import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Logic.Basic

import Natural.Core
import Natural.Lsp

open Natural

attribute [natural_name "natural number"] Nat
attribute [natural_name "integer"] Int

syntax (name := set_comp) "{" ident ":" type "|" prop "}" : expr

@[natural_elab set_comp]
def set_comp_elab : NaturalElab
  | `(expr| { $x:ident : $type:type  | $p:prop }) => do
      let type ← of_type type
      (·, #[x], type) <$> `({ ($x:ident) : $type | $(← of_prop p)})
  | _ => Lean.Elab.throwUnsupportedSyntax
