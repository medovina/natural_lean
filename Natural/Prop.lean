import Natural.Grammar
import Natural.Init

open Lean
open Lean.Elab
open Lean.Elab.Term
open Lean.Meta
open Lean.Syntax

namespace Natural

syntax "bind" ident+ "," term "," term : term

partial def syntax_free_vars (only_free: Bool) : Syntax → List Name :=
  let rec find (s: Syntax) : List Name :=
    let combine (vars: List Name) (t: List Name) :=
      if only_free then t.removeAll vars
      else (vars ++ t).eraseDups
    match match_binder s with
      | .some (_bt, xs, t) => combine (xs.map (·.1.getId)) (find t)
      | _ => match s with
        | `(bind $xs:ident*, $_:term, $t:term) =>
            combine (xs.toList.map TSyntax.getId) (find t)
        | _ => match s with
          | .missing => []
          | .node _ _ args => args.toList.flatMap find |>.eraseDups
          | .ident _ _ _ _ => [s.getId]
          | .atom _ _ => []
  find

def free_vars (t: Term): List Name := syntax_free_vars true (t.raw)

def all_vars (t: Term): List Name := syntax_free_vars false (t.raw)

def to_ident: Term → Ident
  | `($n:num) => mkIdent (Name.mkSimple s!"n{n.getNat}")
  | `($i:ident) => i
  | _ => panic! "to_ident: unknown"

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

def of_id_list : TSyntax ``id_list → CoreM (List Ident)
  | `(id_list| $id:ident $[, $ids:ident $_:comma_ahead]* $[$[,]? and $id2:ident]?) => do
      pure $ [id] ++ ids.toList ++ id2.toList
  | _ => throwError "unknown id_list"

def of_natural_name (stx: Syntax) : CoreM Ident := do
  -- The name we receive here is wrapped in a syntax category such as natural_property,
  -- so we must look below the top-level tag.
  let s := stx[0]

  let (_cat, name) ← match s with
    | `(name1| $_i:ident) => do
        (lookup_name1 (← getEnv) s).getDM (throwError "unknown name1")
    | `(name2| $_i:ident $_j:ident) => do
        (lookup_name2 (← getEnv) s).getDM (throwError "unknown name2")
    | _ => throwError "unknown name"
  mkIdentFromRef name (canonical := true)

partial def of_natural_type (ntype: TSyntax `natural_type) : CoreM Term :=
  withRef ntype do match ntype with
    | `(natural_type| type)
    | `(natural_type| types) => `(Type)
    | `(natural_type| $n:natural_type_name) => of_natural_name n
    | `(natural_type| $n:natural_type_name of $t:natural_type) => do
        `($(← of_natural_name n) $(← of_natural_type t))
    | _ => throwError "unknown natural_type"

-- Retrieve the string constant from syntax matching one of our categories
-- such as 'rel_op' or 'op'.
def syntax_atom (t: TSyntax α): String := match t.raw with
  | .node _ _ #[.atom _ val]
  | .node _ _ #[.node _ _ #[.atom _ val]] => val
  | _ => panic! "syntax_atom"

def of_multi_specifier : TSyntax `multi_specifier → List Term → CoreM (List Term)
  | `(multi_specifier| $_:_at_least) => fun ts => List.singleton <$> multi_or ts
  | `(multi_specifier| $_:_at_most) => at_most
  | `(multi_specifier| $_:_exactly) => precisely_one
  | _ => fun _ => throwError "unknown multi_specifier"

def op_map := [
  ("·", "*"),
  ("−", "-"), -- map minus sign to hyphen
  ("|", "∣")  -- map vertical bar to division symbol
  ]

def map_op (op: String) := (op_map.lookup op).getD op

def of_op (op: TSyntax α): String := map_op (syntax_atom op)

-- A map from infix operators to their associated type classes in Lean.
-- For example, Lean elaborates (x + y) to (Add.add x y).
def infix_op_class := [
  ("+", `add, ``Add), ("-", `sub, ``Sub),
  ("*", `mul, ``Mul), ("/", `div, ``Div), ("%", `mod, ``Mod),
  ("^", `pow, ``Pow),
  ("∪", `union, ``Union), ("∩", `inter, ``Inter),
  ("<", `lt, ``LT), ("≤", `le, ``LE), ("≈", `Equiv, ``HasEquiv),
  ("∈", `mem, ``Membership), ("⊆", `Subset, ``HasSubset), ("⊂", `SSubset, ``HasSSubset),
  ("∣", `dvd, ``Dvd) ]

-- Infix operators that are represented by functions, not type classes.
def extra_infix := [("∘", ``Function.comp), (">", ``GT.gt), ("≥", ``GE.ge)]

def prefix_op_class := [ ("-", `neg, ``Neg) ]

def lookup_op_attr (op: String) : CoreM (Option OpInfo) := lookup_assoc op_extension op

def lookup_op (op: String) (kind: OpKind) : CoreM (Option OpInfo) :=
  let table := match kind with
    | .infix => infix_op_class
    | .prefix => prefix_op_class
    | .postfix
    | .mixfix => []
  match table.lookup op with
    | .some (fname, cl) =>
        pure $ .some ⟨op, .none, kind, .some cl, .none, fname, .anonymous, 0, []⟩
    | .none => lookup_op_attr op

def build_op (kind: OpKind) (op: String) (args: List Term): CoreM Term := do
  let ns := ((← lookup_op_attr op).map (·.ns)).getD .anonymous
  pure $ apply_op ns kind op args

def build_infix (t: Term) (op: String) (u: Term) : CoreM Term :=
  build_op .infix op [t, u]

def fun_to_op (n: Name) : Option String :=
  extra_infix.findSome? (fun (op, name) =>
    if n == name then .some op else .none) <|>
  infix_op_class.findSome? (fun (op, fn, type) =>
    if n == type ++ fn then .some op else .none)

def super_char (s: Syntax) : Char := (s.getArg 0).getAtomVal.front

def super_string (table: List (Char × Char)) (a: TSyntaxArray α) : String :=
  let chars := a.map (fun s => (table.lookup (super_char s)).get!)
  String.ofList chars.toList

def of_some_or_no : TSyntax ``some_or_no → CoreM Bool
  | `(some_or_no| some)
  | `(some_or_no| $_:_a) => pure true
  | `(some_or_no| no) => pure false
  | _ => throwError "unknown some_or_no"

-- expr

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

def elab_expr (expr: Syntax): CoreM Term := do
  let fns : List NaturalElab :=
    (naturalElabAttribute.getEntries (← getEnv) expr.getKind).map (·.value)
  let (stx, bound, type) ← (← try_elab fns expr).getDM (throwError "unknown expr")
  match bound with
    | #[] => pure stx
    | _ => `(bind $bound:ident*, $type:term, $stx:term)

def function_name (s: String) : String := s.replace " " "_"

def check_no_binder_op : α × Option (BinderOp × Term) → CoreM (α × Term)
  | (id, some (":", t)) => pure (id, t)
  | _ => throwError "unexpected binder op"

def apply2 (r : Ident) (e f: Term) : CoreM Term :=
    match fun_to_op r.getId with
      | .some op => build_infix e op f
      | .none => `($r $e $f)

def of_opt_not : TSyntax ``opt_not → CoreM Bool
  | `(opt_not| not) => pure false
  | `(opt_not| ) => pure true
  | _ => throwError "unknown opt_not"

def ungroup : Term → List Term
  | `(_group $t $u) => [t, u]
  | t => [t]

def and_e_t (x y: Term → CoreM Term): Term → CoreM Term :=
  fun e => do mk_and (← x e) (← y e)

def fresh_var : CoreM Ident := mkIdent <$> mkFreshUserName `x

def apply_self (x: Term) (t: Term) : Term :=
  ⟨subst_term x `_self t⟩

mutual

partial def of_if_case : TSyntax `if_case → CoreM (Term × Term)
  | `(if_case| $e:expr if $p:prop |) => pairM (of_expr e) (of_prop1 p)
  | _ => throwError "unknown if_case"

partial def of_expr (expr: TSyntax `expr): CoreM Term := withRef expr do
  match expr with
    | `(expr| $n:num) => pure n
    | `(expr| $i:ident) => pure i
    | `(expr| Prop) => `(Prop)
    | `(expr| $e:expr $s:super_expr) =>
          let (e, se) ← pairM (of_expr e) (of_super_expr s)
          match super_id s with
          | .some id =>  -- could be either exponentiation or postfix op, e.g. Sᶜ
              `(_super $e $se $id)  -- resolve ambiguity later
          | .none => `($e ^ $se)
    | `(expr| $e:expr → $f:expr) => `($(← of_expr e) → $(← of_expr f))
    | `(expr| $e:mixfix_expr) => of_mixfix e
    | `(expr| $e:expr$f:expr)
    | `(expr| $e:expr ( $f:expr )) => `(_app_or_mul $(← of_expr e) $(← of_expr f))
    | `(expr| ( $e:expr )) => of_expr e
    | `(expr| ( $e:expr , $f:expr)) => `( ($(← of_expr e), $(← of_expr f)) )
    | `(expr| { $es:expr,* }) => do
        let es ← es.getElems.mapM of_expr
        `({ $es:term,* })
    | `(expr| { $cs:if_case* $last:expr otherwise }) => do
        let cs ← cs.mapM of_if_case
        let last ← of_expr last
        cs.foldrM (fun (e, p) rest => `(if _ : $p then $e else $rest)) last
    | `(expr| $i:ident [ $e:expr ]) => `($(id_append i `mk_quot) $(← of_expr e))
    | `(expr| some $i:ident : $type:expr such that $p:prop) => do
        let type ← of_expr type
        let p ← of_prop1 p
        `(Classical.choose (show ∃ $i:ident : $type, $p from by default))
    | _ => match parse_op_opt expr with
      | .some (kind, op, ts) =>
          build_op kind (map_op op) (← ts.mapM (fun e => of_expr ⟨e⟩))
      | _ => elab_expr expr

partial def of_type : TSyntax ``type → CoreM Term
  | `(type| $e:expr) => of_expr e >>= (resolve_left ·.raw)
  | _ => throwError "unknown type"

partial def of_simple_type : TSyntax `simple_type → CoreM Term
  | `(simple_type| $i:ident) => `($i)
  | `(simple_type| $t:simple_type × $u:simple_type) => do
      `($(← of_simple_type t) × $(← of_simple_type u))
  | _ => throwError "unknown simple_type"

partial def of_ids_type : TSyntax ``ids_type → CoreM (List Ident × BinderOp × Term)
  | `(ids_type| $xs:ident,* $op:binder_op $t:type) => do
    pure (xs.getElems.toList, syntax_atom op, ← of_type t)
  | _ => throwError "unknown ids_type"

partial def of_rel_prop (prop: TSyntax `rel_prop): CoreM Term := withRef prop do
  let rec build : List Term → List String → CoreM (List Term)
    | _, [] => pure []
    | t :: u :: ts, op :: ops =>
        .cons <$> build_infix t op u <*> build (u :: ts) ops
    | _, _ => panic! "of_rel_prop"
  match prop with
    | `(rel_prop| $a:expr $op:rel_op $b:expr $[$ops:rel_op $cs:expr]*) => do
          let ts ← (a :: b :: cs.toList).mapM of_expr
          let ops := (op :: ops.toList).map of_op
          multi_and (← build ts ops)
    | _ => throwError "unknown rel_prop"

partial def of_mixfix (stx: Syntax): CoreM Term := do
  let kind := stx.getKind
  let ns := ((← lookup_op_attr kind.toString).map (·.ns)).getD .anonymous
  let notation_kind := "term" ++ (String.join $ stx.getArgs.toList.map (fun a =>
    if a.isAtom then a.getAtomVal else "_"))
  let args ← stx.getArgs.mapM (fun a => do
    if a.isAtom then pure a else of_expr ⟨a⟩)
  pure ⟨Syntax.node (stx.getInfo?.get!) (ns ++ .mkSimple notation_kind) args⟩

partial def of_multi_or (prop: TSyntax `multi_or): CoreM Term := withRef prop do
  match prop with
    | `(multi_or| $s:multi_specifier one of $es,* is true) => do
          of_multi_specifier s (← es.getElems.toList.mapM of_rel_prop) >>= multi_and
    | _ => throwError "unknown multi_or"

partial def of_ids_types : TSyntax `ids_types → CoreM IdVars
  | `(ids_types| $[$ids:ids_type] and*) => do
      ids.toList.flatMapM (fun i => do
        let (xs, type) ← of_ids_type i
        pure $ xs.map (·, type))
  | `(ids_types| $t:natural_type $ids:id_list) => do
      let type ← of_natural_type t
      let xs ← of_id_list ids
      pure $ xs.map (·, ":", type)
  | _ => throwError "unknown ids_types"

partial def of_for_all_ids : TSyntax ``for_all_ids → CoreM IdVars
  | `(for_all_ids| $_:_for_all $ids_type:ids_types) => of_ids_types ids_type
  | _ => throwError "unknown for_all_ids"

partial def of_for_all_opt_with : TSyntax ``for_all_opt_with → CoreM (IdVars × Term)
  | `(for_all_opt_with| $f:for_all_ids $[with $p:rel_prop]?) => do
    pure (← of_for_all_ids f, (← p.mapM of_rel_prop).getD mk_true)
  | _ => throwError "unknown for_all_opt_with"

-- natural language

partial def of_adjective : TSyntax ``adjective → CoreM (Term → CoreM Term)
  | `(adjective| only) => pure (fun _x => pure mk_true)
  | `(adjective| $n:natural_property) => do
      let a ← of_natural_name n
      pure fun e => `($a $e)
  | _ => throwError "unknown adjective"

partial def of_comp_adjective_phrase :
      TSyntax ``comp_adjective_phrase → CoreM (Term → CoreM Term)
  | `(comp_adjective_phrase| $c:natural_comparative than $f:expr) => do
        let a ← of_natural_name c
        let f ← of_expr f
        pure fun e => apply2 a e f
  | _ => throwError "unknown comp_adjective_phrase"

partial def of_adjective_phrase : TSyntax `adjective_phrase → CoreM (Term → CoreM Term)
  | `(adjective_phrase| $a:adjective) => of_adjective a
  | `(adjective_phrase| $cp:comp_adjective_phrase) => of_comp_adjective_phrase cp
  | _ => throwError "unknown adjective_phrase"

partial def of_noun_e_e_t : TSyntax ``noun_e_e_t → CoreM Ident
  | `(noun_e_e_t| $n:natural_attribute) => of_natural_name n
  | _ => throwError "unknown noun_e_e_t"

partial def of_nominal_e_e_t :
        TSyntax `nominal_e_e_t → CoreM (Term → Term → CoreM Term)
  | `(nominal_e_e_t| $n:noun_e_e_t) => do
      let n ← of_noun_e_e_t n   -- e.g. "divisor"
      pure fun e f =>
        match ungroup f with
          | [f] => apply2 n e f
          | fs => pure $ Lean.Syntax.mkApp n (e :: fs).toArray
  | `(nominal_e_e_t| $a:adjective $nom:nominal_e_e_t) => do
      let a ← of_adjective a
      let nom ← of_nominal_e_e_t nom
      pure fun e f => do mk_and  (← a e) (← nom e f)
  | _ => throwError "unknown nominal_e_e_t"

partial def of_noun_phrase_e : TSyntax `noun_phrase_e → CoreM Term
  | `(noun_phrase_e| $e:expr) => of_expr e
  | `(noun_phrase_e| $e:expr $_:_and $f:expr) => do
      `(_group $(← of_expr e) $(← of_expr f))
  | `(noun_phrase_e| $_:_the $c:collection) => elab_expr c
  | `(noun_phrase_e| itself) => pure (mkIdent `_self)
  | _ => throwError "unknown noun_phrase"

partial def of_nominal_e_t : TSyntax `nominal_e_t →
        CoreM (Option Term × (Term → CoreM Term))
  | `(nominal_e_t| $t:natural_type) => do
      pure (.some (← of_natural_type t), fun _e => pure mk_true)
  | `(nominal_e_t| $n:nominal_e_e_t of $f:noun_phrase_e) => do
      let n ← of_nominal_e_e_t n
      let f ← of_noun_phrase_e f
      pure (.none, fun e => n e f)
  | `(nominal_e_t| $n:nominal_e_t with $np:noun_phrase_e_et_t) => do
      let (type, n) ← of_nominal_e_t n
      let np ← of_noun_phrase_e_et_t np
      pure (type, fun e => do mk_and (← n e) (← np e (fun _x => pure mk_true)))
  | `(nominal_e_t| $a:adjective $n:nominal_e_t) => do
      let (type, n) ← of_nominal_e_t n
      pure (type, and_e_t (← of_adjective a) n)
  | `(nominal_e_t| $n:nominal_e_t $ap:comp_adjective_phrase) => do
      let (type, n) ← of_nominal_e_t n
      pure (type, and_e_t n (← of_comp_adjective_phrase ap))
  | `(nominal_e_t| $n:nominal_e_t that $vp:verb_phrase) => do
      let (type, n) ← of_nominal_e_t n
      pure (type, and_e_t n (← of_verb_phrase vp))
  | _ => throwError "unknown nominal_e_t"

partial def of_noun_phrase_e_e_t : TSyntax `noun_phrase_e_e_t →
        CoreM ((Term → Term → CoreM Term) × Option Ident)
  | `(noun_phrase_e_e_t| $_:a_or_some $nom:nominal_e_e_t $v:ident ?) =>
      of_nominal_e_e_t nom <&> (·, v)
  | _ => throwError "unknown noun_phrase_e_t"

partial def of_noun_phrase_e_t : TSyntax `noun_phrase_e_t →
        CoreM (Option Term × (Term → CoreM Term))
  | `(noun_phrase_e_t| a $nom:nominal_e_t) => of_nominal_e_t nom
  | _ => throwError "unknown noun_phrase_e_t"

partial def of_noun_phrase_et_t :
        TSyntax ``noun_phrase_et_t → CoreM ((Term → CoreM Term) → CoreM Term)
  | `(noun_phrase_et_t| $_:_every $nom:nominal_e_t) => do
      let (type, nom) ← of_nominal_e_t nom
      pure $ fun p => do
        let x ← fresh_var
        let t ← nom (← `($x))
        let u ← p (← `($x))
        `(∀ $x $[: $type]?, $(← mk_implies t (apply_self x u)))
  | _ => throwError "unknown noun_phrase_et_t"

partial def of_noun_phrase_e_et_t :
        TSyntax `noun_phrase_e_et_t → CoreM (Term → (Term → CoreM Term) → CoreM Term)
  | `(noun_phrase_e_et_t| no $nom:nominal_e_e_t) => do
      let nom ← of_nominal_e_e_t nom
      let x ← fresh_var
      pure $ fun e p => do
        let t ← nom (← `($x)) e
        let u ← p (← `($x))
        `(¬ ∃ $x:ident, $(← mk_implies t u))
  | _ => throwError "unknown noun_phrase_e_et_t"

partial def of_predicative_e : TSyntax `predicative_e → CoreM Term
  | `(predicative_e| $np:noun_phrase_e) => of_noun_phrase_e np
  | _ => throwError "unknown predicative_e"

partial def of_predicative_e_t : TSyntax `predicative_e_t → CoreM (Term → CoreM Term)
  | `(predicative_e_t| $ap:adjective_phrase) => of_adjective_phrase ap
  | `(predicative_e_t| $np:noun_phrase_e_t) =>
        (of_noun_phrase_e_t np) <&> (·.2)
  | _ => throwError "unknown predicative"

partial def of_verb_e_e_t : TSyntax ``verb_e_e_t → CoreM (Term → Term → CoreM Term)
| `(verb_e_e_t| $r:natural_relation) => do
    let r ← of_natural_name r
    pure (apply2 r)
 | _ => throwError "unknown verb"

partial def of_verb_phrase : TSyntax `verb_phrase → CoreM (Term → CoreM Term)
  | `(verb_phrase| has $np:noun_phrase_e_e_t) => do  -- e.g. "has a prime divisor"
      let (np, v) ← of_noun_phrase_e_e_t np
      pure fun e => do
        let x ← v.getDM fresh_var
        let t ← np (← `($x)) e
        `(∃ $x:ident, $t)
  | `(verb_phrase| has $np:noun_phrase_e_et_t) => do  -- e.g. "has no divisor"
      let np ← of_noun_phrase_e_et_t np
      pure $ fun e => np e (fun _x => pure mk_true)
  | `(verb_phrase| is $n:opt_not $p:predicative_e_t) => do  -- e.g. "is even"
        let n ← of_opt_not n
        let p ← of_predicative_e_t p
        pure fun e => p e >>= apply_tf n
  | `(verb_phrase| are $p:predicative_e) => do
      let p ← of_predicative_e p
      pure $ fun (e : Term) =>
        match e, p with
        | `(fun $x:ident => $e), `(fun $y:ident => $p) =>
            let p := subst_term x y.getId p
            `(∀ $x, $(⟨e⟩):term ↔ $(⟨p⟩):term)
        | _, _ => throwError "of_verb_phrase: unexpected"
  | `(verb_phrase| $v:verb_e_e_t $n:noun_phrase_e) => do   -- e.g. "divides x"
      let v ← of_verb_e_e_t v
      let n ← of_noun_phrase_e n
      pure (fun e => v e (apply_self e n))
  | `(verb_phrase| $v:verb_e_e_t $n:noun_phrase_et_t) => do  -- e.g. "divides every integer"
      let v ← of_verb_e_e_t v
      let n ← of_noun_phrase_et_t n
      pure (fun e => n (v e))
  | _ => throwError "unknown verb phrase"

-- prop

partial def of_var_list : TSyntax `var_list → CoreM (IdVars × Option Term)
  | `(var_list| $i:ids_types) => of_ids_types i <&> (·, none)
  | `(var_list| $a:adjective function $f:ident : $type:type) => do
      pure ([(f, ":", ← of_type type)],
            some $ ← (← of_adjective a) f)
  | _ => throwError "unknown var_list"

partial def apply_holds (ids_types: IdVars) : Term → CoreM Term
  | `(_holds _ _) => match ids_types with
      | [(x, _)] => `(_holds _ $x)
      | _ => throwError "multiple variables unexpected"
  | `(_holds $_ $_) => throwError "extra holds clause"
  | t => pure t

partial def of_prop1 (prop: TSyntax `prop): CoreM Term := withRef prop do
  match prop with
    | `(prop| $np:noun_phrase_e $vp:verb_phrase) => do
          let n ← of_noun_phrase_e np
          (← of_verb_phrase vp) n
    | `(prop| $np:noun_phrase_et_t $vp:verb_phrase) => do
          (← of_noun_phrase_et_t np) (← of_verb_phrase vp)
    | `(prop| $e:expr $b:is_tf) => apply_tf (← of_is_tf b) (← of_expr e)
    | `(prop| $e:rel_prop $b:is_tf ?) =>
          apply_tf ((← b.mapM of_is_tf).getD true) (← of_rel_prop e)
    | `(prop| $m:mixfix_prop) => of_mixfix m
    | `(prop| $p:prop $_:_and $q:prop)
    | `(prop| $p:prop , and $q:prop)
    | `(prop| $p:prop and also $q:prop) => do `($(← of_prop1 p) ∧ $(← of_prop1 q))
    | `(prop| $_:_either ? $p:prop or $q:prop) => do `($(← of_prop1 p) ∨ $(← of_prop1 q))
    | `(prop| $p:prop implies $q:prop)
    | `(prop| $_:_if $p:prop $[,]? then $q:prop) => do `($(← of_prop1 p) → $(← of_prop1 q))
    | `(prop| $p:prop $_:_iff $q:prop) => do `($(← of_prop1 p) ↔ $(← of_prop1 q))
    | `(prop| $f:for_all_opt_with $[,]? $p:prop)
    | `(prop| $p:prop $f:for_all_opt_with) => do
          let (ids_types, w) ← of_for_all_opt_with f
          let p ← of_prop1 p >>= apply_holds ids_types
          mk_for_all ids_types (← mk_implies w p)
    | `(prop| $_:_there $_:_exists $s:some_or_no ? $ep:exists_phrase) => do
          let t ← of_exists_phrase ep
          let b ← s.elim (pure true) of_some_or_no
          apply_tf b t
    | `(prop| $p:prop $_:_for some $ids_types:ids_types) => do
          let ids_types ← of_ids_types ids_types
          let p ← of_prop1 p >>= apply_holds ids_types
          mk_exists ids_types p
    | `(prop| $_:_either ? $p:prop , or $q:prop) => do `($(← of_prop1 p) ∨ $(← of_prop1 q))
    | `(prop| $m:multi_or) => of_multi_or m
    | `(prop| $_:have_contradiction) => pure mk_false
    | `(prop| $_:thm_holds) => `(_holds _ _)
    | `(prop| $_:thm_holds for $e:expr) => `(_holds _ $(← of_expr e))
    | `(prop| $_:thm_holds for $x:ident = $e:expr) => `(_holds $x $(← of_expr e))
    | stx => throwError s!"unknown prop: {stx}"

partial def of_exists_phrase (phrase: TSyntax `exists_phrase) : CoreM Term :=
  withRef phrase do match phrase with
    | `(exists_phrase| $vp:var_list $[such that $p:prop]?) => do
        let (vars, cond) ← of_var_list vp
        mk_exists vars (← opt_and cond (← p.mapM of_prop1))
    | `(exists_phrase| $nom:nominal_e_t) => do
        let (type, nom) ← of_nominal_e_t nom
        let x ← fresh_var
        let t ← nom (← `($x))
        `(∃ $x:ident $[: $type]?, $t)
    | _ => throwError "unknown exists_phrase"

end

def nice_names :=
  [`x, `y, `z] ++ ('a' ... 'e').toList.map (Name.mkSimple ·.toString)

-- Rename vars x✝, x✝¹, x✝², ... generated by fresh_var to have
-- nice names x, y, z, a, b, ...
def fix_vars (t: Term): Term :=
  let vars := all_vars t
  let to_map := (all_vars t).filter (fun v =>
    v.hasMacroScopes && v.eraseMacroScopes == `x)
  let names := nice_names.removeAll vars
  let map := to_map.zip names
  ⟨map_vars map t.raw⟩

def of_prop (prop: TSyntax `prop) : CoreM Term :=
  fix_vars <$> of_prop1 prop

def is_declared (n: Name): MetaM Bool := do
  pure $ (← getLCtx).usesUserName n ||
         (← resolveGlobalName n (enableLog := false)) != []

def global_info (n: Name): CoreM (Option ConstantInfo) := do
  match (← resolveGlobalName n (enableLog := false)) with
    | (name, _) :: _ => do
        pure (← getConstInfo name)
    | _ => pure none

def global_type (n: Name): CoreM (Option Expr) :=
  (ConstantInfo.type <$> ·) <$> global_info n

def type_matches_name (type: Expr) (n: Name) :=
  (type.getAppFnArgs).1 == n

def is_type_in_class (type: Expr) (cl: Name): MetaM Bool := do
  if type.isArrow then pure false else
  let inst ← mkAppM cl #[type]
  match (← trySynthInstance inst) with
    | LOption.some _ => pure true
    | _ => pure false

def trap_errors (name: String) (f: TermElabM α) : TermElabM α := do
  if ← MonadLog.hasErrors then
    throwError "trap_errors: preexisting error in {name}"
  let x ← f
  if ← MonadLog.hasErrors then
    throwError s!"trapped error in {name}, aborting"
  pure x

def elab_term (stx: Syntax): TermElabM Expr := trap_errors "elab_term" (elabTerm stx none)

def elab_type (stx: Syntax): TermElabM Expr := trap_errors "elab_type" (elabType stx)

def elab_to_type (t: Term): TermElabM Expr := do
  let e ← elab_term t
  let type ← trap_errors "elab_to_type" (inferType e)
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
  withAutoBoundImplicit $ do
    withLocalDecl name .default (← elab_type type) (fun _var =>
      withoutAutoBoundImplicit f)

-- Bind the given variables with their types, then run f.
def with_vars (le: Vars) (f: TermElabM α) : TermElabM α := match le with
  | [] => f
  | (name, none) :: rest =>
      let type := Lean.mkConst ``Unit  -- just a guess
      withLocalDecl name .default type (fun _var => with_vars rest f)
  | (name, some (":", type)) :: rest => with_local name type (with_vars rest f)
  | (name, some ("∈", s)) :: rest => do
      let type ← elab_to_type s
      match type.getAppArgs with
        | #[u] => withLocalDecl name .default u (fun _var => with_vars rest f)
        | _ => throwError s!"expected container type: {type}"
  | _ => throwError "resolve_term1: unknown binder op"

abbrev LocalEnv := List (Name × Term)    -- maps name to type

-- Infer the type of a term in an environment with the given local variables,
-- whose types may have implicit parameters.
def infer_fun_type (args: LocalEnv) (t: Term): TermElabM Expr := match args with
  | [] => elab_to_type t
  | (x, type) :: rest =>
      withAutoBoundImplicit $ do
        let type ← elab_type type
        let u ← withLocalDecl x .default type (fun _var =>
          withoutAutoBoundImplicit (infer_fun_type rest t))
        mkArrow type u

mutual

-- Resolve ambiguities in a term.  For example, a(b) will become either
-- a product a · b or a function call, depending on the type of a.
partial def resolve (s: Syntax) : TermElabM Term := withRef s do
  match s with
    | `($n:num) => pure n
    | `($i:ident) => do
        let n := i.getId
        if n.toString.contains "_@" then pure ⟨s⟩ else
        if (← is_declared n) then pure ⟨s⟩ else
          let vars := n.toString.toList.map (fun c => Name.mkSimple c.toString)
          if ← vars.allM (is_declared ·) then
              -- We must attach the actual SourceInfo from i (a SourceInfo.original) here.
              -- If we generate synthetic SourceInfo, even with canonical := true, then
              -- sometimes Lean will report that a variable "x" is unused even if we use it
              -- in an implicit product "xy".  (It's unclear whether that is a bug in Lean.)
              let info := i.raw.getInfo?.get!
              let to_ident v : Term := ⟨(mkIdent v).raw.setInfo info⟩
              pure (← multi_prod (vars.map to_ident))
          else throwErrorAt s (
            if vars.length == 1 then s!"undefined: {n}"
            else s!"{n} is neither defined nor an implicit product")
    | `(_app_or_mul $t:term $u:term) => do
        let (t, u) ← mapM_pair resolve (t, u)
        if ← is_numeric t then `($t * $u) else `($t $u)
    | `(_super $t:term $u:term $id:ident) =>
         let t ← resolve t
         let id := id.getId.toString (escape := false)
         if ← (← lookup_op id .postfix).anyM (matches_op .postfix t)
           then build_op .postfix id [t]
           else `($t ^ $(← resolve u))
    | `(_holds $x $e) => `(_holds $x $(← resolve e))
    | `($b:instBinder → $t) =>  -- an instance parameter, e.g. "[Nonempty T] -> ..."
        `($b:instBinder → $(← resolve t))
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

partial def resolve_term1 (le: Vars) (t: Term) : TermElabM Term :=
  with_vars le (resolve t.raw)

partial def resolve_term (le: LocalEnv) (t: Term) : TermElabM Term :=
  resolve_term1 (le.map (fun (x, type) => (x, ":", type))) t

end
