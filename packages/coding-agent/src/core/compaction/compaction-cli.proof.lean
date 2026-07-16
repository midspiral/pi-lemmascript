import «compaction-cli.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

-- Bridge lemmas: connect main's `sessionEntryToContextMessages(...).some(...)` /
-- isTurnStartEntry checks to the entry.type-level specs, via the spec axiom.

-- A cut-point entry is never a tool-result: its messages share the entry's role
-- (spec), and a tool-result message is not a cut point.
@[grind] theorem cutpoint_not_toolResult (e : SessionEntry) :
    (sessionEntryToContextMessages e).any Pure.isCutPointMessage = true →
    Pure.isToolResultMessage e = false := by
  have hs := sessionEntryToContextMessages_spec e
  simp only [Pure.isCutPointMessage, Pure.isToolResultMessage, Array.any_eq_true] at *
  grind

-- If main flags the entry a turn start, so does the entry.type-level spec.
@[grind] theorem turnStartEntry_imp_turnStarter (e : SessionEntry) :
    Pure.isTurnStartEntry e = true → Pure.isTurnStarter e = true := by
  have hs := sessionEntryToContextMessages_spec e
  unfold Pure.isTurnStartEntry Pure.isTurnStarter
  cases e <;>
    simp_all only [Pure.isTurnStartMessage, Array.any_eq_true, reduceCtorEq] <;>
    grind

-- No messages ⇒ not a message entry ⇒ not a tool result.
@[grind] theorem emptyCtx_not_toolResult (e : SessionEntry) :
    (sessionEntryToContextMessages e).size = 0 → Pure.isToolResultMessage e = false := by
  have hs := sessionEntryToContextMessages_spec e
  simp only [Pure.isToolResultMessage] at *
  grind

-- Spec predicates (Bool pure mirrors).
prove_correct isToolResultMessage by
  unfold Pure.isToolResultMessage; loom_solve

prove_correct isTurnStarter by
  unfold Pure.isTurnStarter; loom_solve

-- Message/entry classifiers called from the loops; each just returns its pure
-- mirror, so the method spec is needed for the loop proofs to see the result.
prove_correct isCutPointMessage by
  unfold Pure.isCutPointMessage; loom_solve

prove_correct isTurnStartMessage by
  unfold Pure.isTurnStartMessage; loom_solve

-- Its ensures (result ⇒ isTurnStarter) is discharged by the @[grind] bridge lemma.
prove_correct isTurnStartEntry by
  loom_solve

-- Loop selectors. The custom solver unfolds the spec predicates so grind can
-- connect the per-branch role/discriminator facts to isToolResultMessage /
-- isTurnStarter when establishing the loop invariants. main routes turn/cut
-- detection through sessionEntryToContextMessages(...).some(isCutPointMessage /
-- isTurnStartMessage) and isTurnStartEntry, so those are unfolded too; the
-- @[grind] sessionEntryToContextMessages_spec axiom bridges the produced roles
-- back to entry.type.
section LoopProofs
set_option loom.solver "custom"
set_option hygiene false in
macro_rules
| `(tactic|loom_solver) => `(tactic| first
  | omega
  | grind
  | grind [Pure.isToolResultMessage, Pure.isTurnStarter, cutpoint_not_toolResult, turnStartEntry_imp_turnStarter, emptyCtx_not_toolResult, Array.getElem_push, Array.size_push]
  | (simp only [Pure.isToolResultMessage, Pure.isTurnStarter] at *; (split <;> simp_all); done)
  | (simp only [Pure.isToolResultMessage, Pure.isTurnStarter] at *; (split <;> grind); done)
  | (simp_all only [Pure.isToolResultMessage, Pure.isTurnStarter]; grind [cutpoint_not_toolResult, turnStartEntry_imp_turnStarter, emptyCtx_not_toolResult])
  | (simp only [Pure.isToolResultMessage, Pure.isTurnStarter] at *; grind [cutpoint_not_toolResult, turnStartEntry_imp_turnStarter, emptyCtx_not_toolResult, Array.getElem_push, Array.size_push]))

prove_correct findValidCutPoints by
  loom_solve

prove_correct findTurnStartIndex by
  loom_solve

set_option maxHeartbeats 4000000 in
prove_correct findCutPoint by
  loom_solve
  -- ensures_1 (turn-split): the reported turnStartIndex is a real boundary.
  · intro h
    cases x_1 with
    | true => simp at h
    | false =>
      simp only [Bool.not_false, Bool.true_and, decide_eq_true_eq, reduceIte] at h ⊢
      rcases ensures_1_2 with h2 | ⟨ha, hb, hc⟩
      · exact absurd h2 h
      · exact ⟨by omega, by omega, ha, hb, hc⟩
  -- ensures_2 (no-orphan): every retained toolResult keeps its tool-use turn.
  · left
    intro j _hcj hje htr
    have hjne : cutIndex_1 ≠ (↑j : ℤ) := fun he =>
      invariant_14 (by rw [show cutIndex_1.toNat = j from by omega]; exact htr)
    exact ⟨by omega, by omega, require_1 j (by omega) hje htr⟩
end LoopProofs
