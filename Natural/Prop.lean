import Natural.Grammar
import Natural.Init

open Lean
open Lean.Elab
open Lean.Syntax

namespace Natural

syntax "bind" ident+ "," term "," term : term

partial def syntax_free_vars (s: Syntax): List Name := match match_binder s with
  | .some (_bt, xs, _type, t) => (syntax_free_vars t).removeAll xs
  | _ => match s with
    | `(bind $xs:ident*, $_:term, $t:term) =>
        (syntax_free_vars t).removeAll (xs.toList.map TSyntax.getId)
    | _ => match s with
      | .missing => []
      | .node _ _ args => args.toList.flatMap syntax_free_vars |>.eraseDups
      | .ident _ _ _ _ => [s.getId]
      | .atom _ _ => []

def free_vars (t: Term): List Name := syntax_free_vars (t.raw)

def name_to_term (n: Name) : CoreM Term := `($(mkIdent n))

def to_ident: Term → Ident
  | `($n:num) => mkIdent (Name.mkSimple s!"n{n.getNat}")
  | `($i:ident) => i
  | _ => panic! "to_ident: unknown"

def is_fun_type : Term → Bool
  | `(_ → _) => true
  | _ => false

def multi_and : List Term → CoreM Term := foldr1M (fun t a => `($t ∧ $a))

def multi_or : List Term → CoreM Term := foldr1M (fun t a => `($t ∨ $a))

def multi_prod : List Term → CoreM Term := foldr1M (fun t a => `($t * $a))

def at_most (ts: List Term) : CoreM (List Term) :=
  let pair (t: Term) (u: Term) := do
    `(¬($t ∧ $u))
  (all_pairs ts).mapM pair.uncurry

def precisely_one (ts: List Term) : CoreM (List Term) :=
  List.cons <$> multi_or ts <*> at_most ts

partial def result_type : Term → Term
  | `($_t → $u) => result_type u
  | t => t

def of_const : TSyntax `const → CoreM Term
  | `(const| $i:ident) => `($i)
  | `(const| $n:num) => `($n)
  | _ => throwError "unknown const"

partial def of_type : TSyntax `type → CoreM Term
  | `(type| $i:ident) => `($i)
  | `(type| $t:type → $u:type) => do `($(← of_type t) → $(← of_type u))
  | `(type| $t:type × $u:type) => do `($(← of_type t) × $(← of_type u))
  | _ => throwError "unknown multi_specifier"

def of_id_list : TSyntax ``id_list → CoreM (Array Ident)
  | `(id_list| $id:ident $[, $ids:ident $_:comma_ahead]* $[$[,]? and $id2:ident]?) => do
      pure $ #[id] ++ ids ++ id2.toArray
  | _ => throwError "unknown id_list"

def idents_to_nat_type (n1: Ident) (n2: Option Ident) := match n2 with
  | .some n2 => s!"{n1.getId.toString} {singular n2.getId.toString}"
  | .none => singular n1.getId.toString

def of_natural_type (ntype: TSyntax ``natural_type) : CoreM Ident :=
  withRef ntype do match ntype with
    | `(natural_type| $n1:ident $n2:ident ?) => do
        let s := idents_to_nat_type n1 n2
        mkIdentFromRef (← lookup_natural s) (canonical := true)
    | _ => throwError "unknown natural_type"

def of_ids_type : TSyntax `ids_type → CoreM (Array Ident × Term)
  | `(ids_type| $xs:ident,* : $t:type) => do pure (xs.getElems, ← of_type t)
  | `(ids_type| $t:natural_type $ids:id_list) => do
      let type ← of_natural_type t
      let ids ← of_id_list ids
      pure (ids, type)
  | _ => throwError "unknown ids_type"

def of_multi_specifier : TSyntax `multi_specifier → List Term → CoreM (List Term)
  | `(multi_specifier| $_:_at_least) => fun ts => List.singleton <$> multi_or ts
  | `(multi_specifier| $_:_at_most) => at_most
  | `(multi_specifier| $_:_exactly) => precisely_one
  | _ => fun _ => throwError "unknown multi_specifier"

def syntax_atom (t: TSyntax α): String := match t.raw with
  | .node _ _ #[.node _ _ #[a]] => a.getAtomVal
  | _ => panic! "syntax_atom"

def mk_false : Term := mkIdent ``False

def op_map := [("·", "*"), ("~", "≈")]

def map_op (op: String) := (op_map.lookup op).getD op

def of_binary_op (op: TSyntax α): String := map_op (syntax_atom op)

def op_class := [("+", `add, ``Add), ("*", `mul, ``Mul), ("^", `pow, ``Pow),
                 ("<", `lt, ``LT), ("≤", `le, ``LE), ("≈", `Equiv, ``HasEquiv)]

def super_char (s: Syntax) : Char := (s.getArg 0).getAtomVal.front

def super_string (table: List (Char × Char)) (a: TSyntaxArray α) : String :=
  let chars := a.map (fun s => (table.lookup (super_char s)).get!)
  String.ofList chars.toList

partial def of_super_expr : TSyntax `super_expr → CoreM Term
  | `(super_expr| $ds:super_digit*) =>
      pure $ mkNatLit (super_string super_digits ds).toNat!
  | `(super_expr| $cs:super_letter*) =>
      pure $ mkIdent (Name.mkSimple (super_string super_letters cs))
  | `(super_expr| $e:super_expr ⁺ $f:super_expr) => do
      `($(← of_super_expr e) + $(← of_super_expr f))
  | _ => throwError "unknown super_expr"

mutual
  partial def of_expr (expr: TSyntax `expr): CoreM Term := withRef expr do
    match expr with
      | `(expr| $n:num) => pure n
      | `(expr| $i:ident) => pure i
      | `(expr| $e:expr $s:super_expr) => `($(← of_expr e) ^ $(← of_super_expr s))
      | `(expr| $e:expr ^ $f:expr) => `($(← of_expr e) ^ $(← of_expr f))
      | `(expr| $e:expr $f:expr)
      | `(expr| $e:expr · $f:expr)
      | `(expr| $e:expr × $f:expr) => `($(← of_expr e) * $(← of_expr f))
      | `(expr| $e:expr + $f:expr) => `($(← of_expr e) + $(← of_expr f))
      | `(expr| $e:expr ( $f:expr )) => `(app_or_mul $(← of_expr e) $(← of_expr f))
      | `(expr| ( $e:expr )) => of_expr e
      | `(expr| ( $e:expr , $f:expr)) => `( ($(← of_expr e), $(← of_expr f)) )
      | `(expr| $i:ident [ $e:expr ]) => `( (Quotient.mk' $(← of_expr e) : $i) )
      | _ =>
        let elabFns := naturalElabAttribute.getEntries (← getEnv) expr.raw.getKind
        for elabFn in elabFns do
          try
            let (stx, bound, type) ← elabFn.value expr
            return (← `(bind $bound:ident*, $type:term, $stx:term))
          catch ex =>
            match ex with
            | .internal id _ =>
              if id == unsupportedSyntaxExceptionId then continue
              else throw ex
            | _ => throw ex
        throwError "unknown expr"

  partial def of_rel_prop (prop: TSyntax `rel_prop): CoreM Term := withRef prop do
    let rec build : List Term → List String → List Term
      | _, [] => []
      | t :: u :: ts, op :: ops =>
          build_infix t op u :: build (u :: ts) ops
      | _, _ => panic! "of_rel_prop"
    match prop with
      | `(rel_prop| $a:expr $[$ops:rel_op $bs:expr]*) => do
            let ts ← (a :: bs.toList).mapM of_expr
            let ops := ops.toList.map of_binary_op
            multi_and (build ts ops)
      | _ => throwError "unknown rel_prop"

  partial def of_multi_or (prop: TSyntax `multi_or): CoreM Term := withRef prop do
    match prop with
      | `(multi_or| $s:multi_specifier one of $es,* is true) => do
            of_multi_specifier s (← es.getElems.toList.mapM of_rel_prop) >>= multi_and
      | _ => throwError "unknown multi_or"

  partial def of_some_or_no : TSyntax ``some_or_no → CoreM Bool
    | `(some_or_no| some) => pure true
    | `(some_or_no| no) => pure false
    | _ => throwError "unknown some_or_no"

  partial def of_prop (prop: TSyntax `prop): CoreM Term := withRef prop do
    match prop with
      | `(prop| $e:rel_prop) => of_rel_prop e
      | `(prop| $p:prop and $q:prop) => do `($(← of_prop p) ∧ $(← of_prop q))
      | `(prop| $_:_either ? $p:prop or $q:prop) => do `($(← of_prop p) ∨ $(← of_prop q))
      | `(prop| $p:prop implies $q:prop)
      | `(prop| $_:_if $p:prop $[,]? then $q:prop) => do `($(← of_prop p) → $(← of_prop q))
      | `(prop| $p:prop $_:_iff $q:prop) => do `($(← of_prop p) ↔ $(← of_prop q))
      | `(prop| $_:_for_all $ids_type:ids_type , $p:prop)
      | `(prop| $p:prop $_:_for_all $ids_type:ids_type) => do
            let (x, t) ← of_ids_type ids_type
            `(∀ $x* : $t, $(← of_prop p))
      | `(prop| $_:_there $_:_exists $s:some_or_no ? $ids_type:ids_type such that $p:prop) => do
            let (x, t) ← of_ids_type ids_type
            let b ← s.elim (pure true) of_some_or_no
            let t ← `(∃ $[$x:ident]* : $t, $(← of_prop p))
            if b then pure t else `(¬ $t)
      | `(prop| $p:prop $_:_for some $ids_type:ids_type) => do
            let (x, t) ← of_ids_type ids_type
            `(∃ $[$x:ident]* : $t, $(← of_prop p))
      | `(prop| $p:prop , and $q:prop) => do `($(← of_prop p) ∧ $(← of_prop q))
      | `(prop| $_:_either ? $p:prop , or $q:prop) => do `($(← of_prop p) ∨ $(← of_prop q))
      | `(prop| $m:multi_or) => of_multi_or m
      | `(prop| $_:have_contradiction) => pure mk_false
      | stx => throwError s!"unknown prop: {stx}"
end

abbrev LocalEnv := List (Name × Term)    -- maps name to type

def lookup (le: LocalEnv) (n: Name) : CoreM (Option Bool) := do
  match (← resolveGlobalName n (enableLog := false)) with
    | (name, _) :: _ =>
        let env ← getEnv
        match env.find? name with
          | .some cinfo => pure $ .some (cinfo.type.isForall)
          | .none => throwError s!"lookup: can't find {name}"
    | [] => pure $ is_fun_type <$> le.lookup n

mutual
partial def resolve (le: LocalEnv) (s: Syntax) : CoreM (Term × Bool) := match s with
  | `($i:ident) => do
      let n := i.getId
      if n.toString.contains "_@" then pure (⟨s⟩, false) else
      match (← lookup le n) with
        | .some is_fun => pure (⟨s⟩, is_fun)
        | .none =>
          let vars := n.toString.toList.map (fun c => Name.mkSimple c.toString)
          if ← vars.allM (fun x => Option.isSome <$> lookup le x)
          then pure (← multi_prod (← vars.mapM name_to_term), false)
          else throwErrorAt s (
            if vars.length == 1 then s!"undefined: {n}"
            else s!"{n} is neither defined nor an implicit product")
  | `(app_or_mul $t:term $u:term) => do
      let (t, t_is_fun) ← resolve le t
      let u ← resolve1 le u
      pure (← if t_is_fun then `($t $u) else `($t * $u), false)
  | _ => match match_binder s with
    | .some (bt, xs, type, t) => do
        let vars := xs.map (·, type)
        pure $ (← mk_binder bt xs type (← resolve1 (vars ++ le) t), false)
    | .none => match s with
      | `(bind $xs:ident*, $type, $t) =>
          let vars := xs.toList.map (·.getId, type)
          resolve (vars ++ le) t
      | _ => match s with
        | .node info kind args => do
            let args ← args.mapM (resolve1 le)
            pure (⟨.node info kind args⟩, false)
        | _ => pure (⟨s⟩, false)

partial def resolve1 (le: LocalEnv) (s: Syntax) : CoreM Term := (·.1) <$> resolve le s
end

def resolve_term (le: LocalEnv) (t: Term) : CoreM Term :=
  (·.1) <$> resolve le t.raw
