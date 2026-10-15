import Lean
import Natural.Util

open Lean
open Lean.Elab

namespace Natural

abbrev AssocExtension α := SimpleScopedEnvExtension (String × α) (List (String × α))

def lookup_assoc_in_env (env: Environment) (ext: AssocExtension α) (name: String)
  : Option α :=
  (ext.getState env).lookup name

def lookup_assoc {α: Type} (ext: AssocExtension α) (name: String): CoreM (Option α) := do
  pure $ lookup_assoc_in_env (← getEnv) ext name

-- natural attribute

syntax (name := natural) "natural " category ? str : attr

initialize name_extension : AssocExtension (Category × Name) ←
  registerSimpleScopedEnvExtension {
    initial := []
    addEntry | state, (key, val) => (key, val) :: state
  }

initialize registerBuiltinAttribute {
  name := `natural
  descr := "Natural name"
  add := fun (decl_name: Name) (stx: Syntax) (attr_kind: AttributeKind) =>
    match stx with
      | `(natural| natural $[$cat:category]? $name:str) =>
          let cat := (cat.map of_category).getD Category.noun
          name_extension.add (name.getString, (cat, decl_name)) attr_kind
      | _ => throwError "natural: unexpected"
}

-- natural_op attribute

syntax (name := natural_op) "natural_op " str ident ident op_kind : attr

initialize op_extension : AssocExtension OpInfo ←
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
          let t : OpInfo := {
            name := name.getString, kind := of_op_kind k, cls := .none,
            type := .some decl_name, fname := id.getId, ns := ns.getId }
          op_extension.add (name.getString, t) attr_kind
      | _ => throwError "natural: unexpected"
}

-- other attributes

abbrev NaturalElab := Syntax → CoreM (Term × Array Ident × Term)

unsafe initialize naturalElabAttribute : KeyedDeclsAttribute NaturalElab ←
  mkElabAttribute NaturalElab `builtin_natural_elab `natural_elab
    `Natural `Natural.NaturalElab "expr"

-- tracing

initialize
   forM [`natural, `natural.tree] registerTraceClass
