import «compaction-cli.def»

set_option velvet.semantics.termination "total"

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
  velvet_vcgen [isToolResultMessage] with finish [Pure.isToolResultMessage]

prove_correct isTurnStarter by
  velvet_vcgen [isTurnStarter] with finish [Pure.isTurnStarter]

-- Message/entry classifiers called from the loops; each just returns its pure
-- mirror, so the method spec is needed for the loop proofs to see the result.
prove_correct isCutPointMessage by
  velvet_vcgen [isCutPointMessage] with finish [Pure.isCutPointMessage]

prove_correct isTurnStartMessage by
  velvet_vcgen [isTurnStartMessage] with finish [Pure.isTurnStartMessage]

-- Its ensures (result ⇒ isTurnStarter) is discharged by the @[grind] bridge lemma.
prove_correct isTurnStartEntry by
  velvet_vcgen [isTurnStartEntry] with try finish

-- Loop selectors. The custom solver unfolds the spec predicates so grind can
-- connect the per-branch role/discriminator facts to isToolResultMessage /
-- isTurnStarter when establishing the loop invariants. main routes turn/cut
-- detection through sessionEntryToContextMessages(...).some(isCutPointMessage /
-- isTurnStartMessage) and isTurnStartEntry, so those are unfolded too; the
-- @[grind] sessionEntryToContextMessages_spec axiom bridges the produced roles
-- back to entry.type.
section LoopProofs
prove_correct findValidCutPoints by
  velvet_vcgen [findValidCutPoints] with try finish [Pure.isToolResultMessage, Pure.isTurnStarter]

prove_correct findTurnStartIndex by
  velvet_vcgen [findTurnStartIndex] with try finish [Pure.isToolResultMessage, Pure.isTurnStarter]

set_option maxHeartbeats 4000000 in
prove_correct findCutPoint by
  velvet_vcgen -errorOnMissingSpec [findCutPoint] with
    (expose_names
     first
       (case termination => tactic => omega)
       (finish (splits := 0))
       (tactic =>
         first
         -- This nested loop needs a fresh VC generation pass.
         | (solve | velvet_vcgen with finish (splits := 0))
         | omega
         -- Every retained tool result keeps its tool-use entry.
         | (left
            intro j hcj hje htr
            have hjne : cutIndex ≠ (↑j : Int) := fun he =>
              invariant_14 (by rw [show cutIndex.toNat = j from by omega]; exact htr)
            exact ⟨by omega, by grind, require_3 j (by grind) hje htr⟩)
         -- A split turn reports an actual turn boundary.
         | (intro h
            cases a_1 with
            | true => simp at h
            | false =>
              simp only [Bool.not_false, Bool.true_and, decide_eq_true_eq] at h ⊢
              rcases ensures_1_2 with h2 | ⟨ha, hb, hc⟩
              · exact absurd h2 h
              · exact ⟨by omega, by omega, ha, hb, hc⟩)))
end LoopProofs
