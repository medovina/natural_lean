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

def of_compound_name : TSyntax ``compound_name → CoreM String
  | `(compound_name| $n1:ident $n2:ident ?) => pure $ match n2 with
    | .some n2 => s!"{n1.getId.toString} {singular n2.getId.toString}"
    | .none => singular n1.getId.toString
  | _ => throwError "unknown compound_name"

def lookup_natural (s: String) : CoreM Ident := do
  mkIdentFromRef (← lookup_natural_attr s) (canonical := true)

def of_natural_type (ntype: TSyntax ``natural_type) : CoreM Term :=
  withRef ntype do match ntype with
    | `(natural_type| $n:compound_name) => do
        let s ← of_compound_name n
        if s == "type" then `(Type) else lookup_natural s
    | _ => throwError "unknown natural_type"

def syntax_atom (t: TSyntax α): String := match t.raw with
  | .node _ _ #[.node _ _ #[a]] => a.getAtomVal
  | _ => panic! "syntax_atom"

def of_ids_type : TSyntax ``ids_type → CoreM (List Ident × BinderOp × Term)
  | `(ids_type| $xs:ident,* $op:binder_op $t:type) => do
    pure (xs.getElems.toList, syntax_atom op, ← of_type t)
  | _ => throwError "unknown ids_type"

def of_multi_specifier : TSyntax `multi_specifier → List Term → CoreM (List Term)
  | `(multi_specifier| $_:_at_least) => fun ts => List.singleton <$> multi_or ts
  | `(multi_specifier| $_:_at_most) => at_most
  | `(multi_specifier| $_:_exactly) => precisely_one
  | _ => fun _ => throwError "unknown multi_specifier"

def mk_false : Term := mkIdent ``False

def op_map := [
  ("·", "*"), ("×", "*"),
  ("~", "≈"), ("∼", "≈"),  -- map both "~" (tilde) and "∼" (tilde operator) to ≈
  ("≁", "≉"),
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

structure OpInfo where
  name: String         -- e.g. "+"
  kind: OpKind
  cls: Option Name     -- type class (if any) associated with op, e.g. `Add
  type: Option Name    -- type (if any) associated with op, e.g. `Set for op "⋃"
  fname: Name          -- function name, e.g. `add
  ns: Name         -- namespace in which op's syntax is defined

def lookup_op_attr (op: String) : CoreM (Option OpInfo) := do
  match ← lookup_assoc op_extension op with
    | .some (typ, ns, fname, kind) =>
        pure $ .some ⟨op, kind, .none, .some typ, fname, ns⟩
    | .none => pure $ .none

def lookup_op (op: String) : CoreM (Option OpInfo) :=
  match op_class.lookup op with
    | .some (fname, cl) =>
        pure $ .some ⟨op, .infix, .some cl, .none, fname, .anonymous⟩
    | .none => lookup_op_attr op

def build_op (kind: OpKind) (op: String) (args: List Term): CoreM Term := do
  let ns := ((← lookup_op_attr op).map (·.ns)).getD .anonymous
  pure $ apply_op ns kind op args

def build_infix (t: Term) (op: String) (u: Term) : CoreM Term :=
  build_op .infix op [t, u]

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

def super_id : TSyntax `super_expr → Option Ident
  | `(super_expr| $c:super_letter) =>
        some $ mkIdent (Name.mkSimple (super_char c).toString)
  | _ => none

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

partial def of_expr (expr: TSyntax `expr): CoreM Term := withRef expr do
  match parse_op_opt expr with
    | .some (kind, op, ts) =>
        build_op kind (map_op op) (← ts.mapM (fun e => of_expr ⟨e⟩))
    | _ => match expr with
      | `(expr| $n:num) => pure n
      | `(expr| $i:ident) => pure i
      | `(expr| $e:expr $s:super_expr) =>
           let (e, se) ← pairM (of_expr e) (of_super_expr s)
           match super_id s with
            | .some id =>  -- could be either exponentiation or postfix op, e.g. Sᶜ
                `(_super $e $se $id)  -- resolve ambiguity later
            | .none => `($e ^ $se)
      | `(expr| $e:expr$f:expr)
      | `(expr| $e:expr ( $f:expr )) => `(_app_or_mul $(← of_expr e) $(← of_expr f))
      | `(expr| ( $e:expr )) => of_expr e
      | `(expr| ( $e:expr , $f:expr)) => `( ($(← of_expr e), $(← of_expr f)) )
      | `(expr| { $es:expr,* }) => do
          let es ← es.getElems.mapM of_expr
          `({ $es:term,* })
      | `(expr| $i:ident [ $e:expr ]) => `($(id_append i `mk_quot) $(← of_expr e))
      | _ =>
        let fns : List NaturalElab :=
          (naturalElabAttribute.getEntries (← getEnv) expr.raw.getKind).map (·.value)
        let (stx, bound, type) ← (← try_elab fns expr).getDM (throwError "unknown expr")
        `(bind $bound:ident*, $type:term, $stx:term)

def of_rel_prop (prop: TSyntax `rel_prop): CoreM Term := withRef prop do
  let rec build : List Term → List String → CoreM (List Term)
    | _, [] => pure []
    | t :: u :: ts, op :: ops =>
        .cons <$> build_infix t op u <*> build (u :: ts) ops
    | _, _ => panic! "of_rel_prop"
  match prop with
    | `(rel_prop| $a:expr $[$ops:rel_op $bs:expr]*) => do
          let ts ← (a :: bs.toList).mapM of_expr
          let ops := ops.toList.map of_binary_op
          multi_and (← build ts ops)
    | _ => throwError "unknown rel_prop"

def of_multi_or (prop: TSyntax `multi_or): CoreM Term := withRef prop do
  match prop with
    | `(multi_or| $s:multi_specifier one of $es,* is true) => do
          of_multi_specifier s (← es.getElems.toList.mapM of_rel_prop) >>= multi_and
    | _ => throwError "unknown multi_or"

def of_some_or_no : TSyntax ``some_or_no → CoreM Bool
  | `(some_or_no| some)
  | `(some_or_no| $_:_a) => pure true
  | `(some_or_no| no) => pure false
  | _ => throwError "unknown some_or_no"

def of_ids_types : TSyntax `ids_types → CoreM IdVars
  | `(ids_types| $[$ids:ids_type] and*) => do
      ids.toList.flatMapM (fun i => do
        let (xs, type) ← of_ids_type i
        pure $ xs.map (·, type))
  | `(ids_types| $t:natural_type $ids:id_list) => do
      let type ← of_natural_type t
      let xs ← of_id_list ids
      pure $ xs.map (·, ":", type)
  | _ => throwError "unknown ids_types"

def of_adjective : TSyntax ``adjective → CoreM Ident
  | `(adjective| $n:compound_name) => do
      lookup_natural (← of_compound_name n)
  | _ => throwError "unexpected adjective"

def of_var_phrase : TSyntax `var_phrase → CoreM (IdVars × Option Term)
  | `(var_phrase| $i:ids_types) => of_ids_types i <&> (·, none)
  | `(var_phrase| $a:adjective function $f:ident : $type:type) => do
      pure ([(f, ":", ← of_type type)],
            some $ ← `($(← of_adjective a) $f))
  | _ => throwError "unknown var_phrase"

def of_relation : TSyntax ``relation → CoreM Ident
  | `(relation| $n:compound_name) => do
      lookup_natural (← of_compound_name n)
  | _ => throwError "unknown relation"

def function_name (s: String) : String := s.replace " " "_"

def of_predicative : TSyntax `predicative → CoreM (Term → CoreM Term)
  | `(predicative| $a:adjective) => do
      let a ← of_adjective a
      pure fun e => `($a $e)
  | `(predicative| a $r:relation of $f:expr) => do
      let r ← of_relation r
      let f ← of_expr f
      pure fun e => `($r $e $f)
  | _ => throwError "unknown predicative"

def of_for_all_ids : TSyntax ``for_all_ids → CoreM (List (Ident × BinderOp × Term))
  | `(for_all_ids| $_:_for_all $ids_type:ids_types ,) => of_ids_types ids_type
  | _ => throwError "unknown for_all_ids"

def check_no_binder_op : α × BinderOp × Term → CoreM (α × Term)
  | (id, ":", t) => pure (id, t)
  | _ => throwError "unexpected binder op"

partial def of_prop (prop: TSyntax `prop): CoreM Term := withRef prop do
  match prop with
    | `(prop| $e:expr $b:is_tf) => apply_tf (← of_is_tf b) (← of_expr e)
    | `(prop| $e:expr is $p:predicative) => do
        (← of_predicative p) (← of_expr e)
    | `(prop| $e:rel_prop $b:is_tf ?) =>
          apply_tf ((← b.mapM of_is_tf).getD true) (← of_rel_prop e)
    | `(prop| $p:prop and $q:prop) => do `($(← of_prop p) ∧ $(← of_prop q))
    | `(prop| $_:_either ? $p:prop or $q:prop) => do `($(← of_prop p) ∨ $(← of_prop q))
    | `(prop| $p:prop implies $q:prop)
    | `(prop| $_:_if $p:prop $[,]? then $q:prop) => do `($(← of_prop p) → $(← of_prop q))
    | `(prop| $p:prop $_:_iff $q:prop) => do `($(← of_prop p) ↔ $(← of_prop q))
    | `(prop| $ids_types:for_all_ids $p:prop) =>
          mk_for_all (← of_for_all_ids ids_types) (← of_prop p)
    | `(prop| $p:prop $_:_for_all $ids_type:ids_types) => do
          mk_for_all (← of_ids_types ids_type) (← of_prop p)
    | `(prop| $_:_there $_:_exists $s:some_or_no ? $vp:var_phrase
              $[such that $p:prop]?) => do
          let (vars, cond) ← of_var_phrase vp
          let t ← mk_exists vars (← opt_and cond (← p.mapM of_prop))
          let b ← s.elim (pure true) of_some_or_no
          apply_tf b t
    | `(prop| $p:prop $_:_for some $ids_type:ids_types) => do
          mk_exists (← of_ids_types ids_type) (← of_prop p)
    | `(prop| $p:prop , and $q:prop) => do `($(← of_prop p) ∧ $(← of_prop q))
    | `(prop| $_:_either ? $p:prop , or $q:prop) => do `($(← of_prop p) ∨ $(← of_prop q))
    | `(prop| $m:multi_or) => of_multi_or m
    | `(prop| $_:have_contradiction) => pure mk_false
    | stx => throwError s!"unknown prop: {stx}"

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

def type_matches_name (type: Expr) (n: Name) :=
  (type.getAppFnArgs).1 == n

def is_type_in_class (type: Expr) (cl: Name): MetaM Bool := do
  let inst ← mkAppM cl #[type]
  match (← trySynthInstance inst) with
    | LOption.some _ => pure true
    | _ => pure false

def elab_to_type (t: Term): TermElabM Expr := do
  let e ← elabTerm t none
  let type ← inferType e
  instantiateMVars type

def has_type_in_class (t: Term) (cl: Name): TermElabM Bool := do
  is_type_in_class (← elab_to_type t) cl

def is_numeric (t: Term): TermElabM Bool :=
  match t with
    | `($_:num) => pure true
    | _ => has_type_in_class t `Mul

def matches_op (kind: OpKind) (t: Term) (info: OpInfo): TermElabM Bool :=
  (kind == info.kind && ·) <$> do
  let type ← elab_to_type t
  pure $ (← info.cls.anyM (fun cl => is_type_in_class type cl)) ||
         info.type.any (fun t => type_matches_name type t)

-- Bind a name to a type, allowing implicit parameters in the type, then run f.
def with_local (name: Name) (type: Term) (f: TermElabM α) : TermElabM α :=
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
        if ← is_numeric t then `($t * $u) else `($t $u)
    | `(_super $t:term $u:term $id:ident) =>
         let t ← resolve t
         let id := id.getId.toString (escape := false)
         if ← (← lookup_op id).anyM (matches_op .postfix t)
           then build_op .postfix id [t]
           else `($t ^ $(← resolve u))
    | _ => match match_binder s with
      | .some (bt, vars, t) => do
          let names := map_fst TSyntax.getId vars
          pure $ (← mk_binder bt vars (← resolve_term1 names t))
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

partial def resolve_term1 (le: Vars) (t: Term)
      : TermElabM Term := match le with
  | [] => resolve t.raw
  | (name, ":", type) :: rest => with_local name type (resolve_term1 rest t)
  | (name, "∈", s) :: rest => do
      let type ← elab_to_type s
      match type.getAppArgs with
        | #[u] => withLocalDecl name .default u (fun _var => resolve_term1 rest t)
        | _ => throwError s!"expected container type: {type}"
  | _ => throwError "resolve_term1: unknown binder op"

partial def resolve_term (le: LocalEnv) (t: Term) : TermElabM Term :=
  resolve_term1 (le.map (fun (x, type) => (x, ":", type))) t

end

partial def resolve_left (s: Syntax): CoreM Term := withRef s do
  match s with
    | `(_app_or_mul $t:term $u:term) => do
       let (t, u) ← mapM_pair resolve_left (t, u)
       `($t $u)
    | _ => match s with
      | .node info kind args => do
          let args ← args.mapM resolve_left
          pure ⟨.node info kind args⟩
      | _ => pure ⟨s⟩
