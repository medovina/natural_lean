import Lean
import Natural.Util

open Lean
open Lean.Elab

namespace Natural

abbrev AssocExtension α := SimpleScopedEnvExtension (String × α) (List (String × α))

def lookup_assoc {α: Type} [ToString α] (ext: AssocExtension α) (name: String): CoreM (Option α) := do
  let map := ext.getState (← getEnv)
  pure (map.lookup name)

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
  add := fun (decl_name: Name) (stx: Syntax) (attr_kind: AttributeKind) =>
    match stx with
      | `(natural_name| natural_name $name:str) =>
          name_extension.add (name.getString, decl_name) attr_kind
      | _ => throwError "natural_name: unexpected"
}

def lookup_natural_attr (s: String): CoreM Name := do
  (← lookup_assoc name_extension s).getDM (throwError "unknown name")

-- natural_op attribute

syntax (name := natural_op) "natural_op " str ident ident op_kind : attr


initialize op_extension : AssocExtension (Name × Name × Name × OpKind) ←
  registerSimpleScopedEnvExtension {
    initial := []
    addEntry | state, (key, val) => (key, val) :: state
  }

initialize registerBuiltinAttribute {
  name := `natural_op
  descr := "Natural operation"
  add := fun (decl_name: Name) (stx: Syntax) (attr_kind: AttributeKind) =>
    match stx with
      | `(natural_op| natural_op $name:str $ns:ident $id:ident $k:op_kind) =>
          let t := (decl_name, ns.getId, id.getId, of_op_kind k)
          op_extension.add (name.getString, t) attr_kind
      | _ => throwError "natural_name: unexpected"
}

-- other attributes

abbrev NaturalElab := Syntax → CoreM (Term × Array Ident × Term)

unsafe initialize naturalElabAttribute : KeyedDeclsAttribute NaturalElab ←
  mkElabAttribute NaturalElab `builtin_natural_elab `natural_elab
    `Natural `Natural.NaturalElab "expr"

-- tracing

initialize
   forM [`natural, `natural.tree] registerTraceClass
