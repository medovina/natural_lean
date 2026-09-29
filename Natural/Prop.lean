import Natural.Grammar
import Natural.Init

open Lean
open Lean.Elab
open Lean.Elab.Term
open Lean.Meta
open Lean.Syntax

namespace Natural

syntax "bind" ident+ "," term "," term : term

partial def syntax_free_vars (s: Syntax): List Name := match match_binder s with
  | .some (_bt, xs, t) => (syntax_free_vars t).removeAll (xs.map (·.1.getId))
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

partial def split_and : Term → List Term
  | `($t ∧ $u) => split_and t ++ split_and u
  | t => [t]

def at_most (ts: List Term) : CoreM (List Term) :=
  let pair (t: Term) (u: Term) := do
    `(¬($t ∧ $u))
  (all_pairs ts).mapM pair.uncurry

def precisely_one (ts: List Term) : CoreM (List Term) :=
  List.cons <$> multi_or ts <*> at_most ts

partial def result_type : Term → Term
  | `($_t → $u) => result_type u
  | t => t

def fmt_term (t: Term) : CoreM Format := do
  let ctx : PPContext := {
    env := (← getEnv), mctx := {}, lctx := {}, opts := (← getOptions),
    currNamespace := (← getCurrNamespace), openDecls := (← getOpenDecls) }
  Lean.ppTerm ctx t

def of_const : TSyntax `const → CoreM Term
  | `(const| $i:ident) => `($i)
  | `(const| $n:num) => `($n)
  | _ => throwError "unknown const"

partial def of_type : TSyntax `type → CoreM Term
  | `(type| $i:ident) => `($i)
  | `(type| Prop) => `(Prop)
  | `(type| $t:type ( $u:type ) ) => do `($(← of_type t) $(← of_type u))
  | `(type| $t:type × $u:type) => do `($(← of_type t) × $(← of_type u))
  | `(type| $t:type → $u:type) => do `($(← of_type t) → $(← of_type u))
  | _ => throwError "unknown multi_specifier"

def of_id_list : TSyntax ``id_list → CoreM (List Ident)
  | `(id_list| $id:ident $[, $ids:ident $_:comma_ahead]* $[$[,]? and $id2:ident]?) => do
      pure $ [id] ++ ids.toList ++ id2.toList
  | _ => throwError "unknown id_list"

def idents_to_nat_type (n1: Ident) (n2: Option Ident) := match n2 with
  | .some n2 => s!"{n1.getId.toString} {singular n2.getId.toString}"
  | .none => singular n1.getId.toString

def of_natural_type (ntype: TSyntax ``natural_type) : CoreM Term :=
  withRef ntype do match ntype with
    | `(natural_type| $n1:ident $n2:ident ?) => do
        let s := idents_to_nat_type n1 n2
        if s == "type" then `(Type) else
        mkIdentFromRef (← lookup_natural_attr s) (canonical := true)
    | _ => throwError "unknown natural_type"

def of_ids_type : TSyntax ``ids_type → CoreM (List Ident × Term)
  | `(ids_type| $xs:ident,* : $t:type) => do
    pure (xs.getElems.toList, ← of_type t)
  | _ => throwError "unknown ids_type"

def of_ids_types : TSyntax `ids_types → CoreM (List (Ident × Term))
  | `(ids_types| $[$ids:ids_type] and*) => do
      ids.toList.flatMapM (fun i => do
        let (xs, type) ← of_ids_type i
        pure $ xs.map (·, type))
  | `(ids_types| $t:natural_type $ids:id_list) => do
      let type ← of_natural_type t
      let xs ← of_id_list ids
      pure $ xs.map (·, type)
  | _ => throwError "unknown ids_types"

def of_multi_specifier : TSyntax `multi_specifier → List Term → CoreM (List Term)
  | `(multi_specifier| $_:_at_least) => fun ts => List.singleton <$> multi_or ts
  | `(multi_specifier| $_:_at_most) => at_most
  | `(multi_specifier| $_:_exactly) => precisely_one
  | _ => fun _ => throwError "unknown multi_specifier"

def syntax_atom (t: TSyntax α): String := match t.raw with
  | .node _ _ #[.node _ _ #[a]] => a.getAtomVal
  | _ => panic! "syntax_atom"

def mk_false : Term := mkIdent ``False

def op_map := [
  ("·", "*"), ("×", "*"), ("~", "≈"),
  ("|", "∣")  -- map vertical bar to division symbol
  ]

def map_op (op: String) := (op_map.lookup op).getD op

def of_binary_op (op: TSyntax α): String := map_op (syntax_atom op)

def op_class := [
  ("+", `add, ``Add), ("*", `mul, ``Mul), ("^", `pow, ``Pow),
  ("∪", `union, ``Union), ("∩", `inter, ``Inter),
  ("<", `lt, ``LT), ("≤", `le, ``LE), ("≈", `Equiv, ``HasEquiv),
  ("∈", `mem, ``Membership), ("⊆", `Subset, `HasSubset),
  ("∣", `dvd, `Dvd) ]

def lookup_op (op: String) : CoreM (Name × Name) :=
  (op_class.lookup op).getDM $ do
    let cl ← lookup_op_attr op
    let fields := Lean.getStructureFieldsFlattened (← getEnv) cl false
    match fields[0]? with
      | .some f => pure (f, cl)
      | .none => throwError "lookup_op: no field"

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

def apply_tf (b: Bool) (t: Term): CoreM Term :=
  if b then pure t else `(¬ $t)

def of_is_tf : TSyntax ``is_tf → CoreM Bool
  | `(is_tf| is true) => pure true
  | `(is_tf| is false) => pure false
  | _ => throwError "unknown is_tf"

def try_elab [Monad m] [MonadExcept Exception m] {α: Type u}
        (fns: List (α → m β)) (expr: α): m (Option β) := match fns with
  | [] => pure none
  | f :: rest =>
      try some <$> f expr
      catch ex =>
        match ex with
        | Lean.Exception.internal id _ =>
          if id == unsupportedSyntaxExceptionId then try_elab rest expr
          else throw ex
        | _ => throw ex

mutual
  partial def of_expr (expr: TSyntax `expr): CoreM Term := withRef expr do
    match expr with
      | `(expr| $n:num) => pure n
      | `(expr| $i:ident) => pure i
      | `(expr| $e:expr $s:super_expr) => `(_super $(← of_expr e) $(← of_super_expr s))
      | `(expr| $e:expr ^ $f:expr) => `($(← of_expr e) ^ $(← of_expr f))
      | `(expr| $e:expr$f:expr)
      | `(expr| $e:expr · $f:expr)
      | `(expr| $e:expr × $f:expr) => `($(← of_expr e) * $(← of_expr f))
      | `(expr| $e:expr ∩ $f:expr) => `($(← of_expr e) ∩ $(← of_expr f))
      | `(expr| $e:expr + $f:expr) => `($(← of_expr e) + $(← of_expr f))
      | `(expr| $e:expr ∪ $f:expr) => `($(← of_expr e) ∪ $(← of_expr f))
      | `(expr| $e:expr ( $f:expr )) => `(_app_or_mul $(← of_expr e) $(← of_expr f))
      | `(expr| ( $e:expr )) => of_expr e
      | `(expr| ( $e:expr , $f:expr)) => `( ($(← of_expr e), $(← of_expr f)) )
      | `(expr| $i:ident [ $e:expr ]) => `($(id_append i `mk_quot) $(← of_expr e))
      | _ =>
        let fns : List NaturalElab :=
          (naturalElabAttribute.getEntries (← getEnv) expr.raw.getKind).map (·.value)
        let (stx, bound, type) ← (← try_elab fns expr).getDM (throwError "unknown expr")
        `(bind $bound:ident*, $type:term, $stx:term)

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
      | `(prop| $e:expr $b:is_tf) => apply_tf (← of_is_tf b) (← of_expr e)
      | `(prop| $e:rel_prop $b:is_tf ?) =>
            apply_tf ((← b.mapM of_is_tf).getD true) (← of_rel_prop e)
      | `(prop| $p:prop and $q:prop) => do `($(← of_prop p) ∧ $(← of_prop q))
      | `(prop| $_:_either ? $p:prop or $q:prop) => do `($(← of_prop p) ∨ $(← of_prop q))
      | `(prop| $p:prop implies $q:prop)
      | `(prop| $_:_if $p:prop $[,]? then $q:prop) => do `($(← of_prop p) → $(← of_prop q))
      | `(prop| $p:prop $_:_iff $q:prop) => do `($(← of_prop p) ↔ $(← of_prop q))
      | `(prop| $_:_for_all $ids_type:ids_types , $p:prop)
      | `(prop| $p:prop $_:_for_all $ids_type:ids_types) => do
            let xs ← of_ids_types ids_type
            `(∀ $(← binders xs)*, $(← of_prop p))
      | `(prop| $_:_there $_:_exists $s:some_or_no ? $ids_type:ids_types such that $p:prop) => do
            let xs ← of_ids_types ids_type
            let b ← s.elim (pure true) of_some_or_no
            let t ← `(∃ $(← ex_binders xs)*, $(← of_prop p))
            apply_tf b t
      | `(prop| $p:prop $_:_for some $ids_type:ids_types) => do
            let xs ← of_ids_types ids_type
            `(∃ $(← ex_binders xs)*, $(← of_prop p))
      | `(prop| $p:prop , and $q:prop) => do `($(← of_prop p) ∧ $(← of_prop q))
      | `(prop| $_:_either ? $p:prop , or $q:prop) => do `($(← of_prop p) ∨ $(← of_prop q))
      | `(prop| $m:multi_or) => of_multi_or m
      | `(prop| $_:have_contradiction) => pure mk_false
      | stx => throwError s!"unknown prop: {stx}"
end

def is_declared (n: Name): MetaM Bool := do
  pure $ (← getLCtx).usesUserName n ||
         (← resolveGlobalName n (enableLog := false)) != []

def global_type (n: Name): CoreM (Option Expr) := do
  match (← resolveGlobalName n (enableLog := false)) with
    | (name, _) :: _ =>
        let env ← getEnv
        .some <$> match env.find? name with
          | .some cinfo => pure cinfo.type
          | .none => throwError s!"lookup: can't find {name}"
    | _ => pure none

def has_supported_type (t: Term) (cl: Name): TermElabM Bool := do
  let e ← elabTerm t none
  let type ← inferType e
  let inst ← mkAppM cl #[type]
  match (← trySynthInstance inst) with
    | .some _ => pure true
    | _ => pure false

def is_numeric (t: Term): TermElabM Bool :=
  match t with
    | `($_:num) => pure true
    | _ => has_supported_type t `Mul

-- Bind a name to a type, allowing implicit parameters in the type, then run f.
def withLocal (name: Name) (type: Term) (f: TermElabM α) : TermElabM α :=
  withAutoBoundImplicit $ do withLocalDecl name .default (← elabType type) (fun _var =>
    withoutAutoBoundImplicit f)

mutual

partial def resolve (s: Syntax) : TermElabM Term := withRef s do
  match s with
    | `($n:num) => pure n
    | `($i:ident) => do
        let n := i.getId
        if n.toString.contains "_@" then pure ⟨s⟩ else
        if (← is_declared n) then pure ⟨s⟩ else
          let vars := n.toString.toList.map (fun c => Name.mkSimple c.toString)
          if ← vars.allM (is_declared ·)
          then pure (← multi_prod (← vars.mapM (name_to_term ·)))
          else throwErrorAt s (
            if vars.length == 1 then s!"undefined: {n}"
            else s!"{n} is neither defined nor an implicit product")
    | `(_app_or_mul $t:term $u:term) => do
        let (t, u) ← mapM_pair resolve (t, u)
        if ← is_numeric t
          then do pure (← `($t * $u))
          else do pure (← `($t $u))
    | `(_super $t:term $u:term) => do
         let t ← resolve t
         let fns : List NaturalResolve :=
            (naturalResolveAttribute.getEntries (← getEnv) `Natural.super).map (·.value)
         -- We pass the resolver the unresolved term u, because it could be a
         -- be a superscript letter representing an operation (e.g. "ᶜ").
         match ← try_elab fns (← `(_super $t $u)) with
          | .some t => pure t
          | .none => `($t ^ $(← resolve u))
    | _ => match match_binder s with
      | .some (bt, vars, t) => do
          let names := map_fst TSyntax.getId vars
          pure $ (← mk_binder bt vars (← resolve_term names t))
      | .none => match s with
        | `(bind $xs:ident*, $type, $t) =>
            let vars := xs.toList.map (·.getId, type)
            -- Also declare the type in the environment, which allows it to be implicit.
            let type_decl := (as_ident type).toList.map (·.getId, ← `(Type))
            resolve_term (vars ++ type_decl) t
        | _ => match s with
          | .node info kind args => do
              let args ← args.mapM resolve
              pure ⟨.node info kind args⟩
          | _ => pure ⟨s⟩

partial def resolve_term (le: LocalEnv) (t: Term) : TermElabM Term := match le with
  | [] => resolve t.raw
  | (name, type) :: rest => withLocal name type (resolve_term rest t)

end
