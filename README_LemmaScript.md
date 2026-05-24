# pi — Verified with LemmaScript

Fork of **pi** (the [earendil-works](https://pi.dev) agent harness) applying [LemmaScript](https://github.com/midspiral/LemmaScript)'s Dafny backend to its context-compaction **cut-point selector**. Annotations are added **in-place** — function bodies and signatures are unchanged; everything goes through `//@` comments. [View as diff](https://github.com/midspiral/pi-lemmascript/compare/main..lemmascript).

When the context window fills, pi compacts history: it picks a cut point and discards everything before it. A provider API rejects a message list whose retained prefix contains an **orphaned `toolResult`** — a tool result with no preceding tool call still in context. So the cut must never land such that the kept suffix *starts with* an orphaned tool result, and never *splits a tool-use/tool-result run*. We prove exactly those properties, in place, for both functions of the selector in [`packages/agent/src/harness/compaction/compaction.ts`](https://github.com/midspiral/pi-lemmascript/blob/lemmascript/packages/agent/src/harness/compaction/compaction.ts).

`check.sh dafny` → **4 verified, 0 errors.** The case study drove five LemmaScript additions — string-union `declare-type`, faithful JS-`switch` lowering, an opaque fall-through type for unions that can't be discriminated, per-constructor destructor renaming for field-name collisions, and `//@ extern` signature normalization — see [Notes for LemmaScript](#notes-for-lemmascript).

## What's Verified

### `findValidCutPoints` — [`compaction.ts:265`](https://github.com/midspiral/pi-lemmascript/blob/lemmascript/packages/agent/src/harness/compaction/compaction.ts#L265)

Scans `entries[startIndex..endIndex)` and returns the indices that are *safe* places to start a retained suffix. Two `//@ ensures`:

- **In range.** Every returned index is in `[startIndex, endIndex)`.
- **No orphan at the cut.** No returned index points at a `message` whose role is `toolResult` — the retained suffix can never *begin* with an orphaned tool result.

The second is the one with teeth: the source `switch` uses C-style fall-through (six roles share one `push`), and only `toolResult` is excluded. Two loop `//@ invariant`s carry both properties.

### `findCutPoint` — [`compaction.ts:341`](https://github.com/midspiral/pi-lemmascript/blob/lemmascript/packages/agent/src/harness/compaction/compaction.ts#L341)

Walks back from the end accumulating an (opaque) token estimate until it reaches `keepRecentTokens`, snaps to the nearest valid cut point, then snaps *backward* over metadata entries. Two `//@ ensures` over the chosen `firstKeptEntryIndex`:

- **The snap can't undo safety.** `firstKeptEntryIndex` is in `[startIndex, endIndex)` and is not a `toolResult` message — even after the backward snap moves the cut earlier past metadata. (The subtle part: proving the snap *breaks on any message*, so it can't slide onto a tool result.)
- **No retained `toolResult` is orphaned.** Every `toolResult` in the kept suffix has its preceding tool-use turn retained too — the cut never splits a tool-use/tool-result run. This holds because the cut lands on a non-`toolResult`, so it can never fall *inside* a run.

Both carry an honest fallback caveat: when there are no valid cut points at all, the function returns `startIndex` unchanged, and the `ensures` disjoins on `|| firstKeptEntryIndex === startIndex` rather than pretending the degenerate fallback is safe.

## Trust boundary

These properties hold relative to assumptions made explicit in the annotations — nothing is hidden behind the proof:

- **Type shadows.** The unreachable `@earendil-works/pi-ai` message graph is shadowed down to what the selector reads: `//@ declare-type Role = "user" | "assistant" | "toolResult" | …` and `//@ declare-type AgentMessage { role: Role }`. `SessionTreeEntry` itself auto-resolves; its `custom_message.content` (an unmodelable union) becomes an opaque type, present but uninspectable.
- **Opaque helpers.** `estimateTokens` and `findTurnStartIndex` are `//@ extern` — uninterpreted. `estimateTokens` reads message fields outside the shadow, so it *must* be opaque; the safety proofs don't depend on its value, only on which entries are messages.
- **Valid-input `requires`.** `0 <= startIndex`, `endIndex <= entries.length`, and — for the no-orphan result — an explicit ordering precondition: *within the range, a `toolResult` is always immediately preceded by a message (its tool-use turn).* This is the assumption verification forced into the open; if pi's session tree can ever violate it, the no-orphan guarantee is where that would surface.

## Not (yet) verified

An **approximate-budget bound** (the kept suffix is close to `keepRecentTokens`) is *not* proven. Stating anything about retained tokens needs a recursive token-sum over a range, which can't be expressed as an inline `//@` spec, can't be a post-return-visible ghost local, and would require adding a helper to the production file (breaking in-place). It would need a spec-level ghost-function feature in LemmaScript. The bound also isn't clean — the forward snap can keep slightly *less* than the budget — so it's low value on its own.

## Notes for LemmaScript

This case study drove five additions to the LemmaScript toolchain (all upstream):

- **String-union `declare-type`.** `//@ declare-type Role = "a" | "b"` now lowers to an enum `datatype`, so a shadow can introduce a discriminant enum for a type that's unreachable across an import.
- **Faithful JS-`switch` lowering.** C-style fall-through (stacked `case` labels sharing one body) and `break`-as-switch-exit (a `break` nested in a `{ }` case block) now lower correctly to a Dafny `match` — neither of which `match` has natively.
- **Opaque fall-through type.** A union LemmaScript can't model as a tagged union (no runtime test maps to a tag — e.g. an array element union of unreachable imports) becomes a single opaque `type Opaque_…(==)` rather than invalid raw-union Dafny. Sound by construction: the field is preserved (so distinct values stay distinct — unlike dropping it), and an opaque type has no constructor or tag predicate, so any attempt to *build or test* it fails to lower. Examples: [`opaqueUnion.ts`](https://github.com/midspiral/LemmaScript/blob/main/examples/opaqueUnion.ts).
- **Shared-destructor collision.** Discriminated-union variants that share a field *name* with different types (`label.targetId: string` vs `leaf.targetId: string?`) get per-constructor-unique destructors, satisfying Dafny's rule that a shared destructor has one type. Safe because variant reads lower to positional match bindings. Example: [`sharedDestructorCollision.ts`](https://github.com/midspiral/LemmaScript/blob/main/examples/sharedDestructorCollision.ts).
- **`//@ extern` signature normalization.** Extern signatures now resolve their parameter and return types through the normal type machinery, so a parameter typed by an unreachable import becomes `AgentMessage`, not `import("/abs/path").AgentMessage`.
