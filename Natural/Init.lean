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

syntax (name := natural) "natural " category str : attr

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
      | `(natural| natural $cat:category $name:str) =>
          let cat := of_category cat
          name_extension.add (singular name.getString, (cat, decl_name)) attr_kind
      | _ => throwError "natural: unexpected"
}

-- natural_op attribute

syntax (name := natural_op) "natural_op " str str ? ident ident op_kind num: attr

initialize op_extension : AssocExtension OpInfo ←
  registerSimpleScopedEnvExtension {
    initial := []
    addEntry | state, (key, val) => (key, val) :: state
  }

-- If the user declares an operator that acts on types (e.g. "~" in
-- Examples/Cardinality.lean) we can't use an attribute to attach it to
-- the (Type) type, which has no definition.  So we use this dummy instead.
def TypeDummy := Type

initialize registerBuiltinAttribute {
  name := `natural_op
  descr := "Natural operation"
  add := fun (decl_name: Name) (stx: Syntax) (attr_kind: AttributeKind) =>
    match stx with
      | `(natural_op|
            natural_op $name:str $neg:str ? $ns:ident $id:ident $k:op_kind $prec:num) =>
          let type_name := if decl_name == ``TypeDummy then `Type else decl_name
          let t : OpInfo := {
            name := name.getString, neg := neg.map (·.getString), kind := of_op_kind k,
            cls := .none, type := .some type_name, fname := id.getId, ns := ns.getId,
            prec := prec.getNat }
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
