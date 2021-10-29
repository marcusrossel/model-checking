import Lake
open Lake DSL

package model_checking where
  dependencies := #[
    {
      name := `mathlib
      src := Source.git "https://github.com/leanprover-community/mathlib4.git" "master"
    }
  ]