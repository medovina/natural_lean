import Lean
open Lean

syntax (name := natural_name) "natural_name " str : attr

initialize naturalExt : SimpleScopedEnvExtension (String × Name) (List (String × Name)) ←
  registerSimpleScopedEnvExtension {
    initial := []
    addEntry := fun names (s, name) => (s, name) :: names
  }

initialize registerBuiltinAttribute {
  name := `natural_name
  descr := "Natural name"
  add := fun (decl_name: Name) (stx: Syntax) (kind: AttributeKind) =>
    naturalExt.add ("yo", decl_name) kind
}
