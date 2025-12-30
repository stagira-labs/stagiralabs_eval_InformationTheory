import Lake
open Lake DSL

package eval_InformationTheory where
  srcDir := "src"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.17.0"

require VerifiedAgora from git
  "https://github.com/stagiralabs/VerifiedAgora.git" @ "v4.17.0_prod_test"

@[default_target]
lean_lib «Mathlib.InformationTheory» where
  roots := #[`Mathlib.InformationTheory]
  globs := #[.submodules `Mathlib.InformationTheory]
