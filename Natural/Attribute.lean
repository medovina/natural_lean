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
    match stx with
      | `(natural_name| natural_name $name:str) =>
          naturalExt.add (name.getString, decl_name) kind
      | _ => throwError "natural_name: unexpected"
}

def lookup_natural (name: String): CoreM (Option Name) := do
  let env ← getEnv
  let map := naturalExt.getState env
  pure (map.lookup name)
