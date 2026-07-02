import «truncate.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct truncateHead by
  loom_solve

-- `loom_solve` leaves one goal: `ensures_2 : res.outputLines ≤ res.totalLines`
-- at the post-loop return. Case on the exit mode: in bytes-mode `invariant_4`
-- bounds the output by the line count directly; otherwise `invariant_2` rules
-- out a partial last line, so `invariant_3`'s exact count plus `i ≥ -1` closes it.
prove_correct truncateTail by
  loom_solve
  -- Remaining goals are `ensures_2 : res.outputLines ≤ res.totalLines`, one per
  -- post-loop path. In each, `i_5` packages the loop-exit state as one tuple
  -- equality; project out the returned array so it is identified with the
  -- invariants' `outputLinesArr`, then case on the exit mode: bytes-mode is
  -- bounded by `invariant_4`; otherwise `invariant_2` rules out a partial last
  -- line and `invariant_3`'s exact count plus `i ≥ -1` closes it.
  all_goals
    (have he4 : outputLinesArr = i_4 := congrArg (fun s => s.snd.snd.snd.fst) i_5
     subst he4
     by_cases hb : truncatedBy = "bytes"
     · have h4 := invariant_4 hb
       omega
     · have hlp : ¬ lastLinePartial = true := fun h => hb (invariant_2 h)
       have h3 := invariant_3 hb hlp
       omega)
