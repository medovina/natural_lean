import Lean
import Natural.Util

open Lean
open Lean.Elab

namespace Natural

abbrev AssocExtension α := SimpleScopedEnvExtension (String × α) (List (String × α))

def lookup_assoc (ext: AssocExtension α) (name: String): CoreM α := do
  let env ← getEnv
  let map := ext.getState env
  (map.lookup name).getDM (throwError s!"unknown: {name}")

-- natural_name attribute

syntax (name := natural_name) "natural_name " str : attr

initialize name_extension : AssocExtension Name ←
  registerSimpleScopedEnvExtension {
    initial := []
    addEntry | state, (key, val) => (key, val) :: state
  }

initialize registerBuiltinAttribute {
  name := `natural_name
  descr := "Natural name"
  add := fun (decl_name: Name) (stx: Syntax) (kind: AttributeKind) =>
    match stx with
      | `(natural_name| natural_name $name:str) =>
          name_extension.add (name.getString, decl_name) kind
      | _ => throwError "natural_name: unexpected"
}

def lookup_natural_attr : String → CoreM Name := lookup_assoc name_extension

-- natural_op attribute

syntax (name := natural_op) "natural_op " str ident : attr

initialize op_extension : AssocExtension (Name × Name) ←
  registerSimpleScopedEnvExtension {
    initial := []
    addEntry | state, (key, val) => (key, val) :: state
  }

initialize registerBuiltinAttribute {
  name := `natural_op
  descr := "Natural operation"
  add := fun (decl_name: Name) (stx: Syntax) (kind: AttributeKind) =>
    match stx with
      | `(natural_op| natural_op $name:str $id:ident) =>
          op_extension.add (name.getString, (decl_name, id.getId)) kind
      | _ => throwError "natural_name: unexpected"
}

def lookup_op_attr : String → CoreM (Name × Name) := lookup_assoc op_extension

-- other attributes

abbrev NaturalElab := Syntax → CoreM (Term × Array Ident × Term)

unsafe initialize naturalElabAttribute : KeyedDeclsAttribute NaturalElab ←
  mkElabAttribute NaturalElab `builtin_natural_elab `natural_elab
    `Natural `Natural.NaturalElab "expr"

abbrev NaturalResolve := Syntax → TermElabM Term

unsafe initialize naturalResolveAttribute : KeyedDeclsAttribute NaturalResolve ←
  mkElabAttribute NaturalResolve `builtin_natural_resolve `natural_resolve
    `Natural `Natural.NaturalResolve "term"

-- tracing

initialize
   forM [`natural, `natural.tree] registerTraceClass
