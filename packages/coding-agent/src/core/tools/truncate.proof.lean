import «truncate.def»

set_option velvet.semantics.termination "total"

prove_correct truncateHead by
  velvet_vcgen [truncateHead] with
    (expose_names
     first
       (finish)
       (have hbytes := Buffer_byteLength_spec (splitLinesForCounting content)[0]! "utf-8"
        try finish))

prove_correct truncateTail by
  velvet_vcgen [truncateTail] with finish
