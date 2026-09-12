import Aesop
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Logic.Basic

import Natural.Grammar
import Natural.Init

open Lean
open Lean.Elab.Command
open Lean.Parser.Command
open Lean.Parser.Term
open Lean.Syntax

infix:50 "≮" => fun x y => ¬(x < y)
infix:50 "≯" => fun x y => ¬(x > y)

namespace Natural

attribute [natural_name "natural number"] Nat
attribute [natural_name "integer"] Int

-- Here we reduce the default extent of an Aesop search so that it will succeed or fail
-- more quickly.
def aesop_config : Aesop.Options :=
  { maxRuleApplicationDepth := 10, maxRuleApplications := 50, maxNormIterations := 20 }

macro "default" : tactic =>
  `(tactic| first | trivial | grind | aesop (config := aesop_config) )

macro "default_apply" ts:ident+ : tactic => do
  let aesop_rules ← ts.mapM (fun i => `(Aesop.rule_expr| safe (by rapply $i)))
  `(tactic| first
      | (apply $(ts[0]!); done)
      | (apply_rules [$[$ts:ident],*] ; done)
      | grind [$[$ts:ident],*]
      | aesop (add $aesop_rules,*))

-- English

def singular (s: String) : String :=
  if s.back == 's' then (s.dropEnd 1).toString else s

-- syntax helpers

def parse_infix_opt : Syntax → Option (Syntax × String × Syntax)
  | .node _ _ #[x, .atom _ op, y] => .some (x, op, y)
  | _ => .none

def parse_infix (t: Term): CoreM (Term × String × Term) :=
  match parse_infix_opt t.raw with
    | .some (x, op, y) => pure (⟨x⟩, op, ⟨y⟩)
    | .none => throwError "infix expression expected"

def build_infix (t: Term) (op: String) (u: Term) : Term :=
  let info := match t.raw.getPos?, u.raw.getTailPos? with
    | .some startPos, .some endPos => SourceInfo.synthetic startPos endPos
    | _, _ => SourceInfo.none
  ⟨Syntax.node info (.mkSimple s!"term_{op}_") #[t, mkAtom op, u]⟩

partial def syntax_replace_infix (op: String) (name: Ident) :=
  let rec repl (t: Syntax): Syntax :=
    let recurse (t: Syntax): Syntax := match t with
      | .node i k args => .node i k (args.map repl)
      | t => t
    match parse_infix_opt t with
      | .some (x, op', y) =>
          if op == op' then (mkApp name #[⟨repl x⟩, ⟨repl y⟩]).raw
          else recurse t
      | _ => recurse t
  repl

def replace_infix (op: String) (name: Ident) (t: Term) : Term :=
  ⟨syntax_replace_infix op name t.raw⟩

inductive BinderType
  | all
  | exists
  | set_comp

def match_binder : Syntax → Option (BinderType × List Name × Term × Term)
  | `(∀ $xs:ident* : $type, $t) => .some (.all, xs.toList.map TSyntax.getId, type, t)
  | `(∃ $[$xs:ident]* : $type, $t) => .some (.exists, xs.toList.map TSyntax.getId, type, t)
  | `({($x:ident) : $type | $t}) => .some (.set_comp, [x.getId], type, t)
  | _ => .none

def mk_binder (bt: BinderType) (xs: List Name) (type: Term) (t: Term) : CoreM Term :=
  let xs := xs.toArray.map mkIdent
  match bt with
    | .all => `(∀ $xs* : $type, $t)
    | .exists => `(∃ $[$xs:ident]* : $type, $t)
    | .set_comp => match xs with
        | #[x] => `({($x) : $type | $t})
        | _ => panic! "mk_binder"

partial def syntax_free_vars (s: Syntax): List Name := match match_binder s with
  | .some (_bt, xs, _type, t) => (syntax_free_vars t).removeAll xs
  | _ => match s with
    | .missing => []
    | .node _ _ args => args.toList.flatMap syntax_free_vars |>.eraseDups
    | .ident _ _ _ _ => [s.getId]
    | .atom _ _ => []

def free_vars (t: Term): List Name := syntax_free_vars (t.raw)

-- terms

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

-- translation from natural language

def of_const : TSyntax `const → CoreM Term
  | `(const| $i:ident) => `($i)
  | `(const| $n:num) => `($n)
  | _ => throwError "unknown const"

partial def of_type : TSyntax `type → CoreM Term
  | `(type| $i:ident) => `($i)
  | `(type| $t:type → $u:type) => do `($(← of_type t) → $(← of_type u))
  | _ => throwError "unknown multi_specifier"

def of_id_list : TSyntax ``id_list → CoreM (Array Ident)
  | `(id_list| $id:ident $[, $ids:ident $_:comma_ahead]* $[$[,]? and $id2:ident]?) => do
      pure $ #[id] ++ ids ++ id2.toArray
  | _ => throwError "unknown id_list"

def idents_to_nat_type (n1: Ident) (n2: Option Ident) := match n2 with
  | .some n2 => s!"{n1.getId.toString} {singular n2.getId.toString}"
  | .none => singular n1.getId.toString

def of_natural_type : TSyntax ``natural_type → CoreM Term
  | `(natural_type| $n1:ident $n2:ident ?) => do
      let s := idents_to_nat_type n1 n2
      let type ← lookup_natural s
      match type with
        | .some type => pure (mkIdent type)
        | _ => throwError s!"unknown type: {s}"
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
      | `(expr| { $x:ident : $type:type | $p:prop }) =>
          `({($x) : $(← of_type type) | $(← of_prop p)})
      | _ => throwError "unknown expr"

  partial def of_rel_prop (prop: TSyntax `rel_prop): CoreM Term := withRef prop do
    let rec build : List Term → List String → List Term
      | _, [] => []
      | t :: u :: ts, op :: ops =>
          build_infix t op u :: build (u :: ts) ops
      | _, _ => panic! "of_rel_prop"
    match prop with
      | `(rel_prop| $a:expr $[$ops:rel_op $bs:expr]*) => do
            let ts ← (a :: bs.toList).mapM of_expr
            let ops := ops.toList.map syntax_atom
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

def of_thm_name: TSyntax ``thm_name → CoreM Ident
  | `(thm_name| $i:ident) => pure i
  | _ => throwError s!"unknown thm_name"

inductive Reason where
  | tactic (t: Syntax.Tactic)
  | apply (ns: List Ident)
  | induction

def of_reason: TSyntax `reason → CoreM (Option Reason)
  | `(reason| [ $t:tactic ]) => pure (Reason.tactic t)
  | `(reason| $[$n:thm_name] and*) =>
        .some <$> Reason.apply <$> n.toList.mapM of_thm_name
  | `(reason| induction) => pure Reason.induction
  | `(reason| the inductive hypothesis) => pure .none
  | _ => throwError "unknown reason"

def of_eq_expr_by: TSyntax `eq_expr_by → CoreM (Term × Option Reason)
  | `(eq_expr_by| = $e:expr $[ by $r:reason ]?) =>
        do pure ((← of_expr e), (← r.bindM of_reason))
  | _ => throwError "unknown eq_expr_by"

inductive ETerm where
  | term (t: Term)
  | eq_chain (ts: List Term)

def eterm_free_vars : ETerm → List Name
  | .term t => free_vars t
  | .eq_chain ts => ts.flatMap free_vars

def ex_vars : Term → List (Ident × Term)
  | `(∃ $[$xs:ident]* : $type, $_p) => xs.toList.map (·, type)
  | _ => []

inductive ProofStep where
  | assert (p: ETerm) (reason: List (Option Reason))
  | let (ids: List Name) (type: Term)
  | let_def (id: Name) (e: Term)
  | assume (p: Term)
  | is_some (ids: List Name) (type: Term) (p: Term) (reason: Option Reason)
  | if_otherwise (p: Term) (if_true: List ProofStep) (if_false: List ProofStep) (concl: Term)
  | biconditional (p: Term) (forward: List ProofStep) (q: Term) (reverse: List ProofStep)
  | case (cases: List (Term × List ProofStep)) (concl: Term)
  | group (steps: List ProofStep)
deriving Nonempty

partial def step_mapM [Monad m] (f: Term → m Term) (step: ProofStep) : m ProofStep := do
  let map_steps (steps: List ProofStep) := steps.mapM (step_mapM f)
  match step with
    | .assert (.term t) rs => pure $ .assert (.term (← f t)) rs
    | .assert (.eq_chain ts) rs =>
        pure $ .assert (.eq_chain (← ts.mapM f)) rs
    | .let .. => pure step
    | .let_def id t => pure $ .let_def id (← f t)
    | .assume p => pure $ .assume (← f p)
    | .is_some ids type p r => pure $ .is_some ids type (← f p) r
    | .if_otherwise p ts fs concl =>
        pure $ .if_otherwise (← f p) (← map_steps ts) (← map_steps fs) (← f concl)
    | .biconditional p forward q reverse =>
        pure $ .biconditional (← f p) (← map_steps forward) (← f q) (← map_steps reverse)
    | .case cases concl => do
        pure $ .case (← cases.mapM (fun (t, steps) => do pure $ (← f t, ← map_steps steps)))
                     (← f concl)
    | .group steps => pure $ .group (← map_steps steps)

def step_decl_vars_types : ProofStep → List (Name × Term)
  | .let ids type => ids.map (·, type)
  | .let_def id _ => [(id, mkIdent `Unit)]  -- just a guess
  | .assume p => (ex_vars p).map (map_fst TSyntax.getId)
  | .is_some ids type .. => ids.map (·, type)
  | _ => []

def step_decl_vars (step: ProofStep): List Name := (step_decl_vars_types step).map (·.1)

partial def step_all_decl_vars (step: ProofStep): List Name :=
  let of_steps (steps: List ProofStep) := (steps.flatMap step_all_decl_vars).eraseDups
  match step with
    | .if_otherwise _p t f _q => of_steps (t ++ f)
    | .case cases _ => of_steps (cases.map Prod.snd).flatten
    | .group steps => of_steps steps
    | _ => step_decl_vars step

mutual
partial def step_free_vars : ProofStep → List Name
  | .assert p _ => eterm_free_vars p
  | .let _ _ => []
  | .let_def _ e => free_vars e
  | .assume p => free_vars p
  | .is_some ids _ p _ => (free_vars p).removeAll ids
  | .if_otherwise p t f q
  | .biconditional p t q f => ([p, q].flatMap free_vars ++ [t, f].flatMap all_free_vars).eraseDups
  | .case cases concl =>
      let (ts, steps) := cases.unzip
      (concl :: ts).flatMap free_vars ++ steps.flatMap all_free_vars
  | .group steps => all_free_vars steps

partial def all_free_vars : List ProofStep → List Name
  | [] => []
  | step :: steps =>
      (step_free_vars step ++ all_free_vars steps).removeAll (step_decl_vars step) |>.eraseDups
end

instance: ToString ProofStep where
  toString
    | .assert .. => "assert"
    | .let ids _ => s!"let {ids}"
    | .let_def id _e => s!"let_def {id}"
    | .assume _ => s!"assume"
    | .is_some id .. => s!"is_some {id}"
    | .if_otherwise .. => "if_otherwise"
    | .biconditional .. => "biconditional"
    | .case _ _ => "case"
    | .group _ => "group"

def of_assert_prop: TSyntax `assert_prop → CoreM (ETerm × List (Option Reason))
  | `(assert_prop| $p:prop) =>
        do pure (.term (← of_prop p), [none])
  | `(assert_prop| $e:expr $eb:eq_expr_by $ebs:eq_expr_by*) => do
        let (e1, by1) ← of_eq_expr_by eb
        let (es, bys) := (← ebs.toList.mapM of_eq_expr_by).unzip
        pure (.eq_chain ((← of_expr e) :: e1 :: es), by1 :: bys)
  | _ => throwError "unknown assert_prop"

def assert_step (t: Term) (r: Option Reason): ProofStep :=
  .assert (.term t) [r]

def of_because_prop : TSyntax ``because_prop → CoreM ProofStep
  | `(because_prop| $_:_since $p:prop) => do
       pure $ .assert (.term (← of_prop p)) [none]
  | _ => throwError "unknown because_prop"

def of_which_is_contradiction (stx: TSyntax `which_is_contradiction) : CoreM (List ProofStep) :=
  withRef stx do match stx with
    | `(which_is_contradiction|
            , $[which is]? $[again]? $_:contradicting $i:thm_name $b:because_prop ?) => do
          let because ← b.toList.mapM of_because_prop
          let s := assert_step (← `(False)) (.some (.apply [← of_thm_name i]))
          pure (because ++ [s])
    | _ => throwError "unknown which_is_contradiction"

def mk_step (t: Term) (r: Option Reason): ProofStep := match t with
  | `(∃ $[$xs:ident]* : $type, $p) =>
        .is_some (xs.toList.map TSyntax.getId) type p r
  | _ => assert_step t r

def of_proof_prop: TSyntax `proof_prop → CoreM (List ProofStep)
  | `(proof_prop| $b:because_prop ? $[$_:_by $r:reason]? $[$_:_have]? $p:assert_prop
          $[by $r2:reason]? $w:which_is_contradiction ?) => do
        let because ← b.toList.mapM of_because_prop
        let (e, rs) ← of_assert_prop p
        let s ← match e with
          | .term t => do pure $ mk_step t ((← r.bindM of_reason) <|> (← r2.bindM of_reason))
          | .eq_chain _ => pure (.assert e rs)
        let contra ← w.toList.flatMapM of_which_is_contradiction
        pure (because ++ [s] ++ contra)
  | _ => throwError "unknown proof_prop"

def of_let_step: TSyntax `let_step → CoreM ProofStep
  | `(let_step| $_:_let $xs:ident,* : $type:type) => do
        pure $ .let (xs.getElems.toList.map TSyntax.getId) (← of_type type)
  | `(let_step| $_:_let $xs:id_list be $[a]? $type:natural_type) => do
        pure $ .let ((← of_id_list xs).toList.map TSyntax.getId) (← of_natural_type type)
  | _ => throwError "unknown let_step"

def of_let_or_assume: TSyntax `let_or_assume → CoreM ProofStep
  | `(let_or_assume| $ls:let_step) => of_let_step ls
  | `(let_or_assume| $_:_let $id = $e) =>
        do pure $ .let_def id.getId (← of_expr e)
  | `(let_or_assume| $_:_assume $p:prop) => do pure $ .assume (← of_prop p)
  | _ => throwError "unknown let_or_assume"

def of_proof_if_prop: TSyntax `proof_if_prop → CoreM ProofStep
  | `(proof_if_prop| $_:_if $p:prop $[,]? then $[$qs:proof_prop]/*) => do
        pure $ .group (.assume (← of_prop p) :: (← qs.toList.flatMapM of_proof_prop))
  | _ => throwError "unknown proof_if_prop"

def of_assert_step: TSyntax `assert_step → CoreM (List ProofStep)
  | `(assert_step| $p:proof_if_prop) => .singleton <$> of_proof_if_prop p
  | `(assert_step| $_:will_show $_p:prop) => pure []
  | `(assert_step| $_:and_or_so ? $p:proof_prop) => of_proof_prop p
  | _ => throwError "unknown assert_step"

def of_proof_sentence1: TSyntax `proof_sentence1 → CoreM (List ProofStep)
  | `(proof_sentence1| $ls:let_or_assume /*) =>
        ls.getElems.toList.mapM of_let_or_assume
  | `(proof_sentence1| $s:assert_step /*) =>
        s.getElems.toList.flatMapM of_assert_step
  | _ => throwError "unknown proof_sentence1"

def of_proof_sentence: TSyntax `proof_sentence → CoreM (List ProofStep)
  | `(proof_sentence| $_:clause_intro ? $s:proof_sentence1 .) =>
      of_proof_sentence1 s
  | _ => throwError "unknown proof_sentence"

mutual
partial def of_otherwise_intro: TSyntax `otherwise_intro → CoreM (Term × List ProofStep)
  | `(otherwise_intro| $_:_assume $p:prop . $ts:proof_unit*) => do
      pure (← of_prop p, ← ts.toList.flatMapM of_proof_unit)
  | `(otherwise_intro| $pip:proof_if_prop .) => match pip with
    | `(proof_if_prop| $_:_if $p:prop $[,]? then $[$qs:proof_prop]/*) => do
        pure (← of_prop p, ← qs.toList.flatMapM of_proof_prop)
    | _ => throwError "unknown otherwise_intro"
  | _ => throwError "unknown otherwise_intro"

partial def of_otherwise_unit: TSyntax ``otherwise_unit → CoreM ProofStep
  | `(otherwise_unit| $intro:otherwise_intro $_:_otherwise $fs:proof_unit*
                     $_:_any_case $q:prop .) => do
      let (p, ts) ← of_otherwise_intro intro
      pure $ ProofStep.if_otherwise p ts (← fs.toList.flatMapM of_proof_unit) (← of_prop q)
  | _ => throwError "unknown otherwise_unit"

partial def of_biconditional_unit: TSyntax ``biconditional_unit → CoreM ProofStep
  | `(biconditional_unit| $_:_assume $p:prop . $fs:proof_unit* Conversely $[,]?
                          $_:_assume $q:prop . $rs:proof_unit*) => do
      pure $ ProofStep.biconditional (← of_prop p) (← fs.toList.flatMapM of_proof_unit)
                                     (← of_prop q) (← rs.toList.flatMapM of_proof_unit)
  | _ => throwError "unknown biconditional_unit"

partial def of_proof_unit: TSyntax `proof_unit → CoreM (List ProofStep)
  | `(proof_unit| $o:otherwise_unit) => List.singleton <$> of_otherwise_unit o
  | `(proof_unit| $b:biconditional_unit) => List.singleton <$> of_biconditional_unit b
  | `(proof_unit| $s:proof_sentence) => of_proof_sentence s
  | _ => throwError "unknown proof_unit"
end

def of_case: TSyntax ``case → CoreM (Nat × Term × List ProofStep)
  | `(case| Case $n:num : $p:prop . $ts:proof_unit*) => do
      pure (n.getNat, (← of_prop p), (← ts.toList.flatMapM of_proof_unit))
  | _ => throwError "unknown case"

def of_case_unit: TSyntax `case_unit → CoreM (List ProofStep)
  | `(case_unit| $cs:case* $_:_any_case $p:prop .) => do
      let (nums, cases) ← List.unzip <$> cs.toList.mapM of_case
      match (nums.zipIdx 1).find? (fun (n, i) => n != i) with
        | .some (n, _i) => throwError s!"case number {n} is unexpected"
        | .none => pure [ProofStep.case cases (← of_prop p)]
  | `(case_unit| $u:proof_unit) => of_proof_unit u
  | _ => throwError "unknown case_unit"

structure Block where
  step : ProofStep
  blocks: List Block
deriving Nonempty

partial def show_blocks (blocks: List Block): String :=
  let rec f (indent: String) (blocks: List Block): List String :=
    blocks.flatMap (fun ⟨step, children⟩ =>
      (indent ++ toString step) :: f (indent ++ "    ") children)
  "\n".intercalate (f "" blocks)

def is_assert_false : ProofStep → Bool
  | .assert (.term t) _ => Syntax.getId t == ``False
  | _ => false

partial def infer_blocks (steps: List ProofStep): List Block :=
  let rec infer (vars: List (List Name)) (steps: List ProofStep): List Block × List ProofStep :=
    match steps with
      | [] => ([], [])
      | (step :: rest) =>
          if overlap (step_all_decl_vars step) vars.flatten
             then ([], steps) else
          let in_use := all_free_vars steps
          if (!is_assert_false step && !vars.head?.all (fun vs => vs.any in_use.elem))
            then ([], steps)
            else let (blocks, rest) := match step with
              | .assert .. => ([⟨step, []⟩], rest)
              | .let .. | .let_def .. | .assume _ | .is_some .. =>
                  let vars := if step matches (.assume _) then vars
                    else step_decl_vars step :: vars
                  let (children, rest) := infer vars rest
                  ([⟨step, children⟩], rest)
              | .if_otherwise p ts fs q =>
                  let tb := ⟨.assume p, infer_blocks ts⟩
                  let fb := ⟨.assume (Syntax.mkCApp ``Not #[p]), infer_blocks fs⟩
                  let block := ⟨.if_otherwise p [] [] q, [tb, fb]⟩
                  ([block], rest)
              | .biconditional p fwd q rev =>
                  let fb := ⟨.assume p, infer_blocks fwd⟩
                  let rb := ⟨.assume q, infer_blocks rev⟩
                  let block := ⟨.biconditional p [] q [], [fb, rb]⟩
                  ([block], rest)
              | .case cases concl =>
                  let bs := cases.map (fun (p, steps) => ⟨.assume p, infer_blocks steps⟩)
                  let ts := cases.map (fun (p, _steps) => (p, []))
                  let block := ⟨.case ts concl, bs⟩
                  ([block], rest)
              | .group steps => (infer_blocks steps, rest)
            let (blocks2, rest) := infer vars rest
            (blocks ++ blocks2, rest)
  let (blocks, rest) := infer [] steps
  assert! (rest.isEmpty)
  blocks

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
      | .node info kind args => do
          let args ← args.mapM (resolve1 le)
          pure (⟨.node info kind args⟩, false)
      | _ => pure (⟨s⟩, false)

partial def resolve1 (le: LocalEnv) (s: Syntax) : CoreM Term := (·.1) <$> resolve le s
end

def resolve_term (le: LocalEnv) (t: Term) : CoreM Term :=
  (·.1) <$> resolve le t.raw

partial def resolve_block (le: LocalEnv) : Block → CoreM Block
  | ⟨step, children⟩ => do
      let ivars := match step with
        | .is_some .. => step_decl_vars_types step
        | _ => []
      pure ⟨← step_mapM (resolve_term (ivars ++ le)) step,
            ← children.mapM (resolve_block (step_decl_vars_types step ++ le))⟩

def get_info (t: Term): SourceInfo := t.raw.getInfo?.getD SourceInfo.none

def with_info (t: Term) (source: Term): Term :=
    ⟨t.raw.setInfo (get_info source)⟩

def adjust_info (n: Nat) (s: SourceInfo) :=
  match s.getPos?, s.getTailPos? with
    | .some p, .some q => SourceInfo.synthetic (p.decreaseBy n) q
    | _, _ => SourceInfo.none

-- Hack: Move the start position back 2 bytes to include "= ".
def with_info2 (t: Term) (source: Term): Term :=
    ⟨t.raw.setInfo (adjust_info 2 (get_info source))⟩

def tactic : Option Reason → CoreM Term
  | .some (.tactic t) => `(by { $t })
  | .some (.apply ns) => `(by default_apply $(ns.toArray)*)
  | .some (.induction) => `(by intro x ; induction x <;> default)
  | .none => `(by default)

def produces_let : ProofStep → Bool
  | .let_def .. | .is_some .. => true
  | _ => false

-- Given a list of ids such as [x, y, z], produce an existential
-- binding pattern such as `( ⟨x, ⟨y, ⟨z, _⟩⟩⟩ ).
def ex_pattern : List Ident → CoreM Term
  | [] => `(_)
  | x :: xs => do
      let p ← ex_pattern xs
      `(⟨$x, $p⟩)

def this_term : CoreM Term := `(this)

partial def translate (top: Bool) (parent_ex: List Name) (prev: Term) (concl: Option Term)
      : List Block → CoreM (Term × Term)
  | [] => match concl with
      | .some c => do pure (← `(show $c by default), c)
      | _ => do
        let t ← if top then `(by default) else
          if overlap parent_ex (free_vars prev) then
            let ids := (parent_ex.map Lean.mkIdent).toArray
            `(show ∃ $[$ids:ident]*, $prev by default)
          else this_term
        pure (t, prev)
  | ⟨step, children⟩ :: rest => do
      let ex_decl := match step with
        | .is_some ids .. => ids
        | _ => []
      let unit ← `(())
      let (c, child_concl) ←
        if step matches (.if_otherwise ..) || step matches (.case ..) then pure (unit, unit) else
        translate (top && rest.isEmpty && produces_let step) ex_decl unit none children
      let translate_case (concl: Term) : Block → CoreM Term
        | ⟨.assume p, bs⟩ => do
            let (c, _) ← translate false [] unit (.some concl) bs
            `(fun (_: $p) => $c)
        | _ => panic! "no assume"
      let (decl, prop) ← match step with
        | .assert (.term p) rs => withRef p do
              let b := with_info (← tactic rs[0]!) p
              pure $ (← `(letDecl| : $p:term := $b), p)
        | .assert (.eq_chain ts) reasons => do
            let tactics ← reasons.mapM tactic
            let mk_step t tactic :=
              let b := with_info2 tactic t
              `(calcStep| _ = $t := $b)
            let steps ← (ts.drop 2).zipWithM mk_step (tactics.drop 1)
            let b := with_info2 tactics[0]! ts[1]!
            pure (← `(letDecl| : _ := calc $(ts[0]!) = $(ts[1]!) := $b
                                      $(steps.toArray)*),
                  ← `($(ts.head!) = $(ts.getLast!)))
        | .let ids type =>
            let ids := ids.toArray.map mkIdent
            pure (← `(letDecl| : _ := fun $ids* : $type => $c),
                  ← `(∀ $ids:ident* : $type, _))
        | .let_def id e => do
            let t ← `(let $(mkIdent id) := $e; $c)
            let decl ← `(letDecl| : _ := $t:term)
            pure (decl, child_concl)
        | .assume p =>
            let vars := (ex_vars p).map (·.1)
            let pat ← ex_pattern vars
            pure (← `(letDecl| : _ := fun ($pat:term : $p) => $c),
                  ← `($p → _))
        | .is_some ids type p reason => do
            let b := with_info (← tactic reason) p
            let ids := ids.map mkIdent
            let vars ← if children.isEmpty then this_term else ex_pattern ids
            let a := ids.toArray
            let t ← `(have $vars:term : (∃ $[$a:ident]* : $type, $p) := $b; $c)
            let decl ← `(letDecl| : _ := $t:term)
            pure (decl, child_concl)
        | .if_otherwise _ _ _ q => do
            let ts ← List.toArray <$> children.mapM (translate_case q)
            pure (← `(letDecl| : _ := Classical.byCases $ts*), q)
        | .biconditional p _ q _ => do
            let [fb, rb] := children | panic! "bad biconditional"
            let ts := #[← translate_case q fb, ← translate_case p rb]
            pure (← `(letDecl| : _ := Iff.intro $ts*), ← `(p ↔ q))
        | .case cases concl =>
            let ts ← List.toArray <$> children.mapM (translate_case concl)
            let d ← multi_or (cases.map Prod.fst)
            let f := Lean.mkIdent $ match ts.size with
              | 2 => `Or.elim
              | 3 => `Or.elim3
              | _ => panic! "unimplemented"
            let t ← `($f (show $d by default) $ts*)
            pure (← `(letDecl| : _ := $t), concl)
        | .group _ => panic! "group unexpected"
      let (r, rest_concl) ← translate top parent_ex prop concl rest
      let t := `(have $decl:letDecl; $r)
      let t ←
            if let `(letDecl| : _ := $u) := decl then
              if r == (← this_term) then pure u    -- shorten proof
              else t
            else t
      pure (t, rest_concl)

inductive _Proof where
  | steps (l: List ProofStep)
  | proof_by (r: Option Reason)

def translate_proof (lets: Option ProofStep) (thm: Term): _Proof → CoreM Term
  | .steps steps => do
      let steps ← match lets with
        | .none => pure steps
        | .some (.let ids type) => match steps with
          | .let .. :: _ => pure steps
          | _ =>
            let vars := ids.inter (free_vars thm)
            pure $ .let vars type :: steps
        | _ => throwError "of_proof: unexpected step"
      let blocks := infer_blocks steps
      -- dbg_trace (show_blocks blocks)
      let blocks ← blocks.mapM (resolve_block [])
      Prod.fst <$> translate True [] (← `(())) none blocks
  | .proof_by r => tactic r

def of_proof: TSyntax `proof → CoreM _Proof
  | `(proof| $steps:case_unit*) => do
        pure $ .steps $ List.flatten (← steps.toList.mapM of_case_unit)
  | `(proof| By $r:reason .) => do pure $ .proof_by (← of_reason r)
  | _ => throwError "unknown proof"

def of_label: TSyntax ``label → CoreM Name
  | `(label| $i:ident) => pure i.getId
  | _ => throwError "unknown label"

def of_proof_item: TSyntax ``proof_item → CoreM (Name × _Proof)
  | `(proof_item| $i:label . $p:proof) => do pure (← of_label i, (← of_proof p))
  | _ => throwError "unknown proof_item"

def of_proof_items: TSyntax ``proof_items → CoreM (List (Name × _Proof))
  | `(proof_items| $ps:proof_item*) => ps.toList.mapM of_proof_item
  | _ => throwError "unknown proof_items"

-- statements

def of_constructor: TSyntax ``constructor → CoreM (Term × Term)
  | `(constructor| $c:const : $t:type) => do pure (← of_const c, ← of_type t)
  | _ => throwError "unknown constructor"

def aux_ctor_def (typ:Ident) (t: Term): CoreM Command :=
  let dot (i: Ident) := mkIdent (typ.getId ++ i.getId)
  match t with
    | `($_:num) =>
        `(instance: $(mkIdent ``OfNat) $typ $t where
            $(mkIdent `ofNat):ident := $(dot (to_ident t)))
    | `($i:ident) => `(abbrev $i := $(dot i))
    | _ => throwError "aux_ctor_def: unknown"

def of_type_def : TSyntax ``type_def → CoreM Command
  | `(type_def| The type $i:ident $[( the $n1:ident $n2:ident ?)]?
                is defined inductively with constructors
                $cs:constructor and* .) => do
      let ctors ← cs.getElems.mapM of_constructor
      let mk_def | (n, t) => `(ctor| | $(to_ident n):ident : $t)
      let ctor_defs ← ctors.mapM mk_def
      let ind_decl ← `(inductive $i:ident $ctor_defs:ctor*)
      let aux ← (ctors.map (·.1)).mapM (aux_ctor_def i)
      let att ← n1.mapM (fun n1 =>
        let t := idents_to_nat_type n1 (n2.get!)
        `(attribute [natural_name $(mkStrLit t)] $i:ident)
      )
      let commands := #[ind_decl] ++ aux ++ att.toArray
      pure $ .mk (mkNullNode commands)
  | _ => throwError "unknown definition"

def of_attrib: TSyntax ``attrib → CoreM Ident
  | `(attrib| @ $i:ident) => pure i
  | _ => throwError "unknown attrib"

def of_top_sentence : TSyntax ``top_sentence → CoreM (Term × Option Ident × Option Ident)
  | `(top_sentence| $p:prop . $[ [ $i:thm_name $[ : $a:attrib ]? ] ]?) => do
      pure (← of_prop p, ← i.mapM of_thm_name, ← a.join.mapM of_attrib)
  | _ => throwError "unknown top_sentence"

abbrev Label := Name

structure ThmDecl where
  label: Option Label
  thm: Term
  name: Option Ident
  attr: Option Ident

def of_prop_item : TSyntax ``prop_item → CoreM ThmDecl
  | `(prop_item| $i:label . $s:top_sentence) => do
      let (thm, name, attr) ← of_top_sentence s
      pure ⟨← of_label i, thm, name, attr⟩
  | _ => throwError "unknown prop_item"

def of_binary_op : TSyntax ``binary_op → CoreM String
  | `(binary_op| +) => pure "+"
  | `(binary_op| ·) => pure "·"
  | `(binary_op| ^) => pure "^"
  | `(binary_op| <) => pure "<"
  | `(binary_op| ≤) => pure "≤"
  | _ => throwError "unknown binary_op"

def op_map := [("+", `add, `Add), ("·", `mul, `Mul), ("^", `pow, `Pow),
               ("<", `lt, `LT), ("≤", `le, `LE)]

def parse_def_eq : Term → CoreM (String × Term × Term × Term)
  | `($l = $r)
  | `($l ↔ $r) => do
      let (a, op, b) ← parse_infix l
      pure (op, a, b, r)
  | _ => throwError "equation expected"

def eq_to_alt_expr (op: String) (fname: Ident) (t: Term): CoreM (TSyntax ``matchAltExpr) := do
  let (op', a, b, r) ← parse_def_eq t
  if op == op' then
    `(matchAltExpr| | $a, $b => $(replace_infix op fname r))
  else throwError "wrong infix op"

def as_ident (t: Term): CoreM Ident := match t.raw with
  | .ident _ _ name _ => pure (mkIdent name)
  | _ => throwError "identifier expected"

def generate_def (op: String) (args: List Ident) (type: Ident) (eqs: Array Term)
    : CoreM Command := do
  let (op_name, cl) := (op_map.lookup op).get!
  let fname := mkIdent (type.getId ++ op_name)
  let eqs ← eqs.mapM (resolve_term (args.map (·.getId, type)))
  let d ← match eqs with
    | #[eq] =>  -- direct definition
        let (_op, x, y, r) ← parse_def_eq eq
        let ix ← as_ident x
        let iy ← as_ident y
        `(def $fname ($ix $iy : $type) := $r)
    | _ =>  -- by cases
        let alts ← eqs.mapM (eq_to_alt_expr op fname)
        `(def $fname : $type → $type → $type
            $alts:matchAlt*)

  let instName := Name.mkSimple ("inst" ++ cl.toString ++ type.getId.toString)
  let i ← `(
    @[method_specs]
    instance $(mkIdent instName):ident : $(mkIdent cl) $type where
      $(mkIdent op_name):ident := $fname
  )
  let spec := instName ++ Name.mkSimple (op_name.toString ++ "_spec")
  let a ← `(attribute [grind =] $(mkIdent spec))
  `($d:command
    $i:command
    $a:command)

def of_cases_def : TSyntax ``cases_def → CoreM Command
  | `(cases_def| The binary operation $op:binary_op on $type:ident is defined recursively
                    such that for all $ids_type:ids_type , $items:prop_item*) => do
      let (xs, _type) ← of_ids_type ids_type
      let eqs ← Array.map ThmDecl.thm <$> items.mapM of_prop_item
      generate_def (← of_binary_op op) xs.toList type eqs
  | _ => throwError "unknown cases_def"

def of_direct_def : TSyntax ``direct_def → CoreM Command
  | `(direct_def| $_:_for_all $ids_type:ids_type , $p:prop .) => do
      let (args, type) ← of_ids_type ids_type
      let eq ← of_prop p
      let (op, _, _, _) ← parse_def_eq eq
      match type with
        | `($i:ident) => generate_def op args.toList i #[eq]
        | _ => throwError "simple type expected"
  | _ => throwError "unknown direct_def"

def of_definition : TSyntax `definition → CoreM Command
  | `(definition| $d:type_def) => of_type_def d
  | `(definition| $e:cases_def) => of_cases_def e
  | `(definition| $d:direct_def) => of_direct_def d
  | _ => throwError "unknown definition"

elab d:definition_stmt : command => do
  let c ← match d with
    | `(definition_stmt| Definition . $d) => liftCoreM (of_definition d)
    | _ => throwError "unknown definition_stmt"
  elabCommand c

def match_proofs : List ThmDecl → List (Label × _Proof) → CoreM (List (ThmDecl × Option _Proof))
  | [], [] => pure []
  | decl :: ts, (j, proof) :: ps =>
      if decl.label == j then .cons (decl, .some proof) <$> match_proofs ts ps
      else .cons (decl, .none) <$> match_proofs ts ((j, proof) :: ps)
  | decl :: ts, [] => .cons (decl, .none) <$> match_proofs ts []
  | [], (j, _) :: _ => throwError s!"unmatched proof label: {j}"

def lets_vars (lets: Option ProofStep) : LocalEnv := match lets with
  | .none => []
  | .some (.let ids type) => ids.map (·, type)
  | _ => panic! "lets_vars: unexpected step"

def generalize (lets: Option ProofStep) (t: Term) : CoreM Term := match lets with
  | .none => pure t
  | .some (.let ids type) =>
      let ids := (ids.inter (free_vars t)).toArray.map mkIdent
      if ids == #[] then pure t else `(∀ $ids:ident* : $type, $t)
  | _ => throwError "generalize: unexpected step"

def translate_proofs (lets: Option ProofStep) (thms_proofs: List (ThmDecl × Option _Proof))
    : CoreM (List (ThmDecl × Option Term)) :=
  thms_proofs.mapM (fun (decl, proof) => withRef decl.thm do
    let thm ← resolve_term (lets_vars lets) decl.thm
    pure ({decl with thm := ← generalize lets thm},
          ← proof.mapM (translate_proof lets thm)))

def of_props_proofs (lets: Option ProofStep) (ps: TSyntax `props_proofs) :
        CoreM (List (ThmDecl × Option Term)) :=
  match ps with
    | `(props_proofs| $s:top_sentence $[ Proof . $proof:proof ]?) => do
        let (thm, opt_name, opt_attr) ← of_top_sentence s
        let decl := ThmDecl.mk none thm opt_name opt_attr
        translate_proofs lets [(decl, ← proof.mapM of_proof)]
    | `(props_proofs| $ps:prop_item* $[ Proof . $pis:proof_items ]?) => do
        let label_thms ← ps.toList.mapM of_prop_item
        let label_proofs := (← pis.mapM of_proof_items).getD []
        let thms_proofs ← match_proofs label_thms label_proofs
        translate_proofs lets thms_proofs
    | _ => throwError "unknown prop_or_items"

elab t:_theorem : command => do
  let c : Command ← liftCoreM $ match t with
    | `(_theorem| $_:_thm $name:thm_name ? $_:str ? .
            $[$ls:let_step .]? $ps:props_proofs) => do
        let name ← name.mapM of_thm_name
        let thms_proofs ← of_props_proofs (← ls.mapM of_let_step) ps
        let commands : Array Command ← thms_proofs.toArray.mapM
          (fun (⟨label, thm, thm_name, attr⟩, proof) => withRef thm do
            let proof := proof.getD (← `(by default))
            let name := thm_name <|> name.map (fun name =>
              label.elim name (mkIdent $ name.getId ++ ·))
            let a ← attr.mapM (fun a => `(attributes| @[$a:ident]))
            let command ← match name with
              | Option.some name =>
                  `($a:attributes ? theorem $name : $thm := $proof)
              | Option.none => `(example : $thm := $proof)
            trace[natural.proof] command
            pure command)
        pure $ .mk (mkNullNode commands)
    | _ => throwError "unknown theorem"
  elabCommand c
