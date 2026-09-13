import Natural.Core
import Natural.Lsp

open Natural

attribute [natural_name "natural number"] Nat
attribute [natural_name "integer"] Int

syntax (name := set_comp) "{" ident ":" type "|" prop "}" : expr

@[natural_elab set_comp]
def set_comp_elab : NaturalElab
  | `(expr| { $x:ident : $t:type  | $p:prop }) => do
      `({ ($x:ident) : $(← of_type t) | $(← of_prop p)})
  | _ => Lean.Elab.throwUnsupportedSyntax
