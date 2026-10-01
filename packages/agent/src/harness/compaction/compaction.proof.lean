import «compaction.def»

set_option velvet.semantics.termination "total"

-- Spec predicates (Bool pure mirrors).
prove_correct isToolResultMessage by
  velvet_vcgen [isToolResultMessage] with finish [Pure.isToolResultMessage]

prove_correct isTurnStarter by
  velvet_vcgen [isTurnStarter] with finish [Pure.isTurnStarter]

-- Loop selectors. Unfold the spec predicates so grind can
-- connect the per-branch role/discriminator facts to isToolResultMessage /
-- isTurnStarter when establishing the loop invariants.
section LoopProofs
prove_correct findValidCutPoints by
  velvet_vcgen [findValidCutPoints] with try finish [Pure.isToolResultMessage, Pure.isTurnStarter]

prove_correct findTurnStartIndex by
  velvet_vcgen [findTurnStartIndex] with try finish [Pure.isToolResultMessage, Pure.isTurnStarter]

set_option maxHeartbeats 4000000 in
prove_correct findCutPoint by
  velvet_vcgen [findCutPoint] with
    (expose_names
     first
       (case termination => tactic => omega)
       (finish [Pure.isToolResultMessage, Pure.isTurnStarter])
       (tactic =>
         first
         | omega
         | (left
            intro j hcj hje htr
            have hjne : cutIndex ≠ (↑j : Int) := fun he =>
              invariant_14 (by rw [show cutIndex.toNat = j from by omega]; exact htr)
            exact ⟨by omega, by grind, require_3 j (by grind) hje htr⟩)
         | (intro hsplit
            rcases ensures_1_1 with h1 | ⟨hsx, hxc, hts⟩
            · subst h1; simp_all
            · split_ifs with hc
              · simp_all
              · exact ⟨by omega, by omega, by omega, by omega, hts⟩)
         | (simp only [Pure.isToolResultMessage]
            split <;> simp_all)))
end LoopProofs
