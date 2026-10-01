import «changelog.def»

set_option velvet.semantics.termination "total"

prove_correct compareVersions by
  velvet_vcgen [compareVersions] with finish [Pure.compareVersions]
