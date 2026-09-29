import Lean
import Natural.Util

open Lean
open Lean.Elab

namespace Natural

-- natural_name, natural_op attributes

syntax (name := natural_name) "natural_name " str : attr
syntax (name := natural_op) "natural_op " str : attr

inductive ExtTag where
  | name
  | op
deriving Inhabited, BEq

instance: ToString ExtTag where
  toString
    | .name => "natural name"
    | .op => "op"

initialize naturalExt : SimpleScopedEnvExtension
      (ExtTag × String × Name) (List ((ExtTag × String) × Name)) ←
  registerSimpleScopedEnvExtension {
    initial := []
    addEntry | state, (tag, s, name) => ((tag, s), name) :: state
  }

initialize registerBuiltinAttribute {
  name := `natural_name
  descr := "Natural name"
  add (decl_name: Name) (stx: Syntax) (kind: AttributeKind) :=
    match stx with
      | `(natural_name| natural_name $name:str) =>
          naturalExt.add (.name, name.getString, decl_name) kind
      | _ => throwError "natural_name: unexpected"
}

initialize registerBuiltinAttribute {
  name := `natural_op
  descr := "operation"
  add (decl_name: Name) (stx: Syntax) (kind: AttributeKind) :=
    match stx with
      | `(natural_op| natural_op $name:str) =>
          naturalExt.add (.op, name.getString, decl_name) kind
      | _ => throwError "natural_op: unexpected"
}

def lookup_tag (tag: ExtTag) (name: String): CoreM Name := do
  let map := naturalExt.getState (← getEnv)
  (map.lookup (tag, name)).getDM (throwError s!"unknown {tag}: {name}")

def lookup_natural_attr := lookup_tag .name
def lookup_op_attr := lookup_tag .op

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
