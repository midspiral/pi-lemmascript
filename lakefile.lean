import Lake
open Lake DSL System

require velvet from ".." / "velvet"
require LemmaScript from ".." / "LemmaScript"

package PiLemmaScript where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

@[default_target]
lean_lib Changelog where
  srcDir := "packages/coding-agent/src/utils"
  roots := #[`«changelog.types», `«changelog.def», `«changelog.proof»]

@[default_target]
lean_lib CompactionAgent where
  srcDir := "packages/agent/src/harness/compaction"
  roots := #[`«compaction.types», `«compaction.def», `«compaction.proof»]

-- CLI's own copy of the selector. Same basename (compaction.ts) as the agent
-- copy above, so its Lean modules are re-based to `compaction-cli.*` via
-- `//@ lean-module compaction-cli` to avoid a flat-namespace module collision.
@[default_target]
lean_lib CompactionCLI where
  srcDir := "packages/coding-agent/src/core/compaction"
  roots := #[`«compaction-cli.types», `«compaction-cli.def», `«compaction-cli.proof»]

@[default_target]
lean_lib Truncate where
  srcDir := "packages/coding-agent/src/core/tools"
  roots := #[`«truncate.types», `«truncate.def», `«truncate.proof»]
