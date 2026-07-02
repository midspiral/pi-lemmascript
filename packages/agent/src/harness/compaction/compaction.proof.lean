import «compaction.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

-- Spec predicates (Bool pure mirrors).
prove_correct isToolResultMessage by
  unfold Pure.isToolResultMessage; loom_solve

prove_correct isTurnStarter by
  unfold Pure.isTurnStarter; loom_solve

-- Loop selectors. The custom solver unfolds the spec predicates so grind can
-- connect the per-branch role/discriminator facts to isToolResultMessage /
-- isTurnStarter when establishing the loop invariants.
section LoopProofs
set_option loom.solver "custom"
set_option hygiene false in
macro_rules
| `(tactic|loom_solver) => `(tactic| first
  | omega
  | grind
  | grind [Pure.isToolResultMessage, Pure.isTurnStarter]
  | (simp only [Pure.isToolResultMessage, Pure.isTurnStarter] at *; (split <;> simp_all); done)
  | (simp only [Pure.isToolResultMessage, Pure.isTurnStarter] at *; (split <;> grind); done)
  | (simp_all only [Pure.isToolResultMessage, Pure.isTurnStarter]; grind)
  | (simp only [Pure.isToolResultMessage, Pure.isTurnStarter] at *; grind))

prove_correct findValidCutPoints by
  loom_solve

prove_correct findTurnStartIndex by
  loom_solve

set_option maxHeartbeats 4000000 in
prove_correct findCutPoint by
  loom_solve
  -- ensures_1 (turn-split): the reported turnStartIndex is a real boundary.
  · intro hsplit
    rcases ensures_1_1 with h1 | ⟨hsx, hxc, hts⟩
    · subst h1; simp_all
    · split_ifs with hc
      · simp_all
      · exact ⟨by omega, by omega, by omega, by omega, hts⟩
  -- ensures_2 (no-orphan): every retained toolResult keeps its tool-use turn.
  · left
    intro j _hcj hje htr
    have hjne : cutIndex_1 ≠ (↑j : ℤ) := fun he =>
      invariant_9 (by rw [show cutIndex_1.toNat = j from by omega]; exact htr)
    exact ⟨by omega, by omega, require_1 j (by omega) hje htr⟩
end LoopProofs
