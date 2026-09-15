import Lean
open Lean
open Lean.Elab

namespace Natural

-- natural_name attribute

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

def lookup_natural (name: String): CoreM Name := do
  let env ← getEnv
  let map := naturalExt.getState env
  (map.lookup name).getDM (throwError s!"unknown type: {name}")

-- natural_elab attribute

abbrev NaturalElab := Syntax → CoreM (Term × Array Ident × Term)

unsafe initialize naturalElabAttribute : KeyedDeclsAttribute NaturalElab ←
  mkElabAttribute NaturalElab `builtin_natural_elab `natural_elab
    `Natural `Natural.NaturalElab "expr"

-- tracing

initialize
   forM [`natural, `natural.tree] registerTraceClass
