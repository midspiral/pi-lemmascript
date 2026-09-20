import «truncate.def»

set_option velvet.semantics.termination "total"

prove_correct truncateHead by
  velvet_vcgen [truncateHead] with try finish
  all_goals expose_names
  all_goals have hbytes := Buffer_byteLength_spec (splitLinesForCounting content)[0]! "utf-8"
  all_goals grind

prove_correct truncateTail by
  velvet_vcgen [truncateTail] with finish
