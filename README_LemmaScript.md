# pi — Verified with LemmaScript

[![LemmaScript verified](https://img.shields.io/github/actions/workflow/status/midspiral/pi-lemmascript/lemmascript.yml?branch=lemmascript&label=LemmaScript%20verified)](https://github.com/midspiral/pi-lemmascript/actions/workflows/lemmascript.yml)

Fork of **pi** (the [earendil-works](https://pi.dev) agent harness) applying [LemmaScript](https://github.com/midspiral/LemmaScript) to its context-compaction **cut-point selector** — verified with **both backends**: Dafny, and Lean 4 (Velvet/Loom), from the same `//@`-annotated TypeScript. Annotations are added **in-place** — everything goes through `//@` comments; the one exception is a behavior-identical control-flow edit in `truncateTail` (the byte-limit exit moved from a `break` into the loop guard, validated by a 117,900-case differential fuzz against the original). [View as diff](https://github.com/midspiral/pi-lemmascript/compare/main..lemmascript).

When the context window fills, pi compacts history: it picks a cut point and discards everything before it. A provider API rejects a message list whose retained prefix contains an **orphaned `toolResult`** — a tool result with no preceding tool call still in context. So the cut must never land such that the kept suffix *starts with* an orphaned tool result, and never *splits a tool-use/tool-result run*. We prove exactly those properties, in place, for both functions of the selector in [`packages/agent/src/harness/compaction/compaction.ts`](packages/agent/src/harness/compaction/compaction.ts), and in the shipped CLI's own copy [`packages/coding-agent/src/core/compaction/compaction.ts`](packages/coding-agent/src/core/compaction/compaction.ts).

`check.sh dafny` → **8 verified, 0 errors** per compaction file. `check.sh lean` → `lake build` green, **zero `sorry`**: the headline **no-orphan** theorem, the turn-split property, the changelog semver core, and both tool-output truncators also carry machine-checked Lean proofs.

## Coverage

| File | Properties | Dafny | Lean |
|---|---|---|---|
| `agent/.../compaction.ts` | no-orphan cut, in-range, turn-split | ✓ | ✓ |
| `coding-agent/.../core/compaction/compaction.ts` | same (CLI's own copy) | ✓ | generated, not yet proven |
| `coding-agent/.../utils/changelog.ts` | semver ordering trichotomy | ✓ | ✓ |
| `coding-agent/.../core/tools/truncate.ts` | line/byte-limit bounds for head & tail truncation | ✓ | ✓ |
| `coding-agent/.../core/tools/edit-diff.ts`, `ai/.../models.ts` | (see file annotations) | ✓ | — (`//@ backend dafny`) |

## What's Verified

### `findValidCutPoints` — [`compaction.ts:265`](https://github.com/midspiral/pi-lemmascript/blob/lemmascript/packages/agent/src/harness/compaction/compaction.ts#L265)

Scans `entries[startIndex..endIndex)` and returns the indices that are *safe* places to start a retained suffix. Two `//@ ensures`:

- **In range.** Every returned index is in `[startIndex, endIndex)`.
- **No orphan at the cut.** No returned index points at a `message` whose role is `toolResult` — the retained suffix can never *begin* with an orphaned tool result.

The second is the one with teeth: the source `switch` uses C-style fall-through (six roles share one `push`), and only `toolResult` is excluded. Two loop `//@ invariant`s carry both properties.

### `findCutPoint` — [`compaction.ts:341`](https://github.com/midspiral/pi-lemmascript/blob/lemmascript/packages/agent/src/harness/compaction/compaction.ts#L341)

Walks back from the end accumulating an (opaque) token estimate until it reaches `keepRecentTokens`, snaps to the nearest valid cut point, then snaps *backward* over metadata entries. Three `//@ ensures` over the chosen `firstKeptEntryIndex`:

- **The snap can't undo safety.** `firstKeptEntryIndex` is in `[startIndex, endIndex)` and is not a `toolResult` message — even after the backward snap moves the cut earlier past metadata. (The subtle part: proving the snap *breaks on any message*, so it can't slide onto a tool result.)
- **No retained `toolResult` is orphaned.** Every `toolResult` in the kept suffix has its preceding tool-use turn retained too — the cut never splits a tool-use/tool-result run. This holds because the cut lands on a non-`toolResult`, so it can never fall *inside* a run.
- **A split turn names a real boundary.** When the cut falls mid-turn (`isSplitTurn`), the reported `turnStartIndex` is an in-range turn boundary at or before the cut — a `user`/`bashExecution` message or a branch-summary/custom-message entry. Proven via the (verified, non-opaque) `findTurnStartIndex`.

Both carry an honest fallback caveat: when there are no valid cut points at all, the function returns `startIndex` unchanged, and the `ensures` disjoins on `|| firstKeptEntryIndex === startIndex` rather than pretending the degenerate fallback is safe.

### `truncateHead` / `truncateTail` — [`truncate.ts`](packages/coding-agent/src/core/tools/truncate.ts)

The shared tool-output truncators (line limit and byte limit, whichever hits first). Proven on both backends: the output never exceeds the line budget or the total line count, and when truncation was byte-driven (and no partial line was taken) the output is strictly under the line budget. `truncateTail`'s partial-last-line edge case is where Dafny's path-sensitive `break` reasoning and Lean's invariant-at-every-exit discipline diverge — the guard-fold edit noted above makes one loop shape both provers accept.

## Running the verification

Both backends regenerate their artifacts from the annotated TypeScript and check them; the generated files are committed and CI fails if they're stale.

**Dafny** (needs Node ≥ 18 and [Dafny](https://github.com/dafny-lang/dafny) ≥ 4.x, with a LemmaScript clone as a sibling directory):

```sh
git clone https://github.com/midspiral/LemmaScript.git ../LemmaScript
(cd ../LemmaScript/tools && npm ci)
../LemmaScript/tools/check.sh dafny
```

**Lean** (additionally needs [elan](https://github.com/leanprover/elan) and the Loom/Velvet forks as siblings):

```sh
git clone https://github.com/namin/loom.git -b lemma ../loom
git clone https://github.com/namin/velvet.git -b lemma ../velvet
../LemmaScript/tools/check.sh lean   # regenerates *.lean and runs `lake build`
```

Per source file the Lean layout is `foo.types.lean` + `foo.def.lean` (generated) and `foo.proof.lean` (hand-written `prove_correct` tactics); files marked `//@ backend dafny` are skipped on the Lean pass. CI runs both backends ([`lemmascript.yml`](.github/workflows/lemmascript.yml)).

## Trust boundary

These properties hold relative to assumptions made explicit in the annotations — nothing is hidden behind the proof:

- **Type shadows.** The unreachable `@earendil-works/pi-ai` message graph is shadowed down to what the selector reads: `//@ declare-type Role = "user" | "assistant" | "toolResult" | …` and `//@ declare-type AgentMessage { role: Role }`. `SessionTreeEntry` itself auto-resolves; its `custom_message.content` (an unmodelable union) becomes an opaque type, present but uninspectable.
- **Opaque helpers.** `estimateTokens` is `//@ extern` — uninterpreted (Dafny: `function {:axiom}`; Lean: an `opaque` declaration). It reads message fields outside the shadow, so it *must* be opaque; the safety proofs don't depend on its value, only on which entries are messages. `truncate.ts` similarly treats `Buffer.byteLength` and the UTF-8-aware partial-line cut as contracted externs.
- **Valid-input `requires`.** `0 <= startIndex`, `endIndex <= entries.length`, and — for the no-orphan result — an explicit ordering precondition: *within the range, a `toolResult` is always immediately preceded by a message (its tool-use turn).* This is the assumption verification forced into the open; if pi's session tree can ever violate it, the no-orphan guarantee is where that would surface.

## Not (yet) verified

An **approximate-budget bound** (the kept suffix is close to `keepRecentTokens`) is *not* proven. Stating anything about retained tokens needs a recursive token-sum over a range, which can't be expressed as an inline `//@` spec, can't be a post-return-visible ghost local, and would require adding a helper to the production file (breaking in-place). It would need a spec-level ghost-function feature in LemmaScript. The bound also isn't clean — the forward snap can keep slightly *less* than the budget — so it's low value on its own.

The CLI's own compaction copy has its Lean artifacts generated but no `prove_correct` yet; its properties are Dafny-verified, and the proofs would mirror the agent copy's.
