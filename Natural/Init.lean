module

import Lean
public import Natural.Util

open Lean
open Lean.Elab
open Lean.Parser
open Lean.PrettyPrinter

namespace Natural

public section

abbrev AssocExtension α := SimpleScopedEnvExtension (String × α) (List (String × α))

def lookup_assoc_in_env (env: Environment) (ext: AssocExtension α) (name: String)
  : Option α :=
  (ext.getState env).lookup name

def lookup_assoc {α: Type} (ext: AssocExtension α) (name: String): CoreM (Option α) := do
  pure $ lookup_assoc_in_env (← getEnv) ext name

-- natural attribute

syntax (name := natural) "natural " category str : attr

public initialize name_extension : AssocExtension (Category × Name) ←
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

sdef mixfix_token
  | str
  | ident

def of_mixfix_token : TSyntax `mixfix_token → CoreM MixfixToken
  | `(mixfix_token| $s:str) => pure (.str s.getString)
  | `(mixfix_token| $i:ident) => pure (.ident i.getId)
  | _ => throwError "notation: expected mixfix_token"

-- args: operator name, negated name, namespace, function name, kind, precedence, tokens
syntax (name := natural_op) "natural_op "
  str str ? ident ident op_kind num mixfix_token *: attr

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
      | `(natural_op| natural_op
            $name:str $neg:str ? $ns:ident $id:ident
            $k:op_kind $prec:num $tokens:mixfix_token*) => do
          let type_name := if decl_name == ``TypeDummy then `Type else decl_name
          let t : OpInfo ← pure {
            name := name.getString, neg := neg.map (·.getString), kind := of_op_kind k,
            cls := .none, type := .some type_name, fname := id.getId, ns := ns.getId,
            prec := prec.getNat, tokens := ← tokens.toList.mapM of_mixfix_token }
          op_extension.add (name.getString, t) attr_kind
      | _ => throwError "natural: unexpected"
}

-- other attributes

abbrev NaturalElab := Syntax → CoreM (Term × Array Ident × Term)

unsafe initialize naturalElabAttribute : KeyedDeclsAttribute NaturalElab ←
  mkElabAttribute NaturalElab `builtin_natural_elab `natural_elab
    `Natural `Natural.NaturalElab "expr"

-- name syntax

def singular_name : Ident → Option Ident → String
  | i, none => singular i.getId.toString
  | i, some j => s!"{i.getId.toString} {singular j.getId.toString}"

meta def filter_ident (f : String → Bool) (err: String): Parser :=
  atomic (ident >> checkStackTop (fun stx => stx.isIdOrAtom?.all f) err)

meta def var : Parser := filter_ident (fun s => s.length == 1) "expected var"
meta def non_var : Parser := filter_ident (fun s => s.length > 1) "expected non_var"

@[combinator_formatter var] def var.formatter : Formatter := pure ()
@[combinator_parenthesizer var] def var.parenthesizer : Parenthesizer := pure ()

@[combinator_formatter non_var] def non_var.formatter : Formatter := pure ()
@[combinator_parenthesizer non_var] def non_var.parenthesizer : Parenthesizer := pure ()

-- a simple name such as "integer"
syntax name1 := non_var

def lookup_name1 (env: Environment): Syntax → Option (Category × Name)
  | `(name1| $i:ident) =>
      (lookup_assoc_in_env env name_extension (singular_name i none))
  | _ => none

def check_name1 (c: Category) (env: Environment) (s: Syntax): Bool :=
  (lookup_name1 env s).any (·.1 == c)

-- a compound name such as "natural number"
syntax name2 := non_var non_var

def lookup_name2 (env: Environment) (s: Syntax): Option (Category × Name) :=
  match s with
  | `(name2| $i:ident $j:ident) =>
      lookup_assoc_in_env env name_extension (singular_name i j)
  | _ => none

def check_name2 (c: Category) (env: Environment) (s: Syntax): Bool :=
  (lookup_name2 env s).any (·.1 == c)

-- tracing

initialize
   forM [`natural, `natural.tree] registerTraceClass

end
