import Aesop
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Logic.Basic

import Natural.Attribute
import Natural.Grammar

open Lean
open Lean.Elab.Command
open Lean.Parser.Command
open Lean.Parser.Term
open Lean.Syntax

infix:50 "≮" => fun x y => ¬(x < y)
infix:50 "≯" => fun x y => ¬(x > y)

attribute [natural_name "natural number"] Nat

macro "default" : tactic => `(tactic| first | trivial | grind | aesop )

macro "default_apply" ts:ident+ : tactic => do
  let aesop_rules ← ts.mapM (fun i => `(Aesop.rule_expr| safe (by rapply $i)))
  `(tactic| first | (apply_rules [$[$ts:ident],*] ; done) | grind [$[$ts:ident],*] |
                    aesop (add $aesop_rules,*))

-- English

def singular (s: String) :=
  if s.back == 's' then s.dropEnd 1 else s

-- syntax helpers

def range_info (s: TSyntax α) := match s.raw.getRange? with
    | .some ⟨pos, endPos⟩ => SourceInfo.synthetic pos endPos
    | .none => SourceInfo.none

def set_info_from (s: TSyntax α) (t: TSyntax β): Term :=
  ⟨s.raw.setInfo (range_info t)⟩

def parse_infix_opt : Syntax → Option (Syntax × String × Syntax)
  | .node _ _ #[x, .atom _ op, y] => .some (x, op, y)
  | _ => .none

def parse_infix (t: Term): CoreM (Term × String × Term) :=
  match parse_infix_opt t.raw with
    | .some (x, op, y) => pure (⟨x⟩, op, ⟨y⟩)
    | .none => throwError "infix expression expected"

def build_infix (t: Term) (op: String) (u: Term) : Term :=
  ⟨mkNode (.mkSimple s!"term_{op}_") #[t, mkAtom op, u]⟩

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

partial def syntax_free_vars (s: Syntax): List Name := match s with
  | `(∀ $x:ident* : $_typ, $t) => (syntax_free_vars t).removeAll (x.toList.map TSyntax.getId)
  | `(∃ $[$x:ident]* : $_typ, $t) => (syntax_free_vars t).removeAll (x.toList.map TSyntax.getId)
  | `({($x:ident) : $_typ | $t}) => (syntax_free_vars t).erase (x.getId)
  | _ => match s with
    | .missing => []
    | .node _ _ args => args.toList.flatMap syntax_free_vars |>.eraseDups
    | .ident _ _ _ _ => [s.getId]
    | .atom _ _ => []

def free_vars (t: Term): List Name := syntax_free_vars (t.raw)

-- logical operations on terms

def multi_and : List Term → CoreM Term := foldr1M (fun t a => `($t ∧ $a))

def multi_or : List Term → CoreM Term := foldr1M (fun t a => `($t ∨ $a))

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

def of_id_list : TSyntax `id_list → CoreM (Array Ident)
  | `(id_list| $id:ident $[, $ids:ident]* $[$[,]? and $id2:ident]?) => do
      pure $ #[id] ++ ids ++ id2.toArray
  | _ => throwError "unknown id_list"

def of_natural_type : TSyntax `natural_type → CoreM Term
  | `(natural_type| $n1:ident $n2:ident) => do
      let s := s!"{n1.getId.toString} {singular n2.getId.toString}"
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

mutual
  partial def of_expr (expr: TSyntax `expr): CoreM Term := do
    let t ← match expr with
      | `(expr| $n:num) => `($n)
      | `(expr| $i:ident) => `($i)
      | `(expr| $e:expr $f:expr)
      | `(expr| $e:expr · $f:expr) => `($(← of_expr e) * $(← of_expr f))
      | `(expr| $e:expr + $f:expr) => `($(← of_expr e) + $(← of_expr f))
      | `(expr| $e:expr ( $f:expr )) =>
          let e ← of_expr e
          let f ← of_expr f
          if (e.raw.isOfKind `num) then `($e * $f) else `($e $f)
      | `(expr| ( $e:expr )) => of_expr e
      | `(expr| { $x:ident : $t:ident | $p:prop }) => `({($x) : $t | $(← of_prop p)})
      | _ => throwError "unknown expr"

    -- Avoid copying SourceInfo to identifiers, which produces spurious
    -- "variable not referenced" errors.
    pure (if expr matches `(expr| $_:ident) then t else set_info_from t expr)

  partial def of_rel_prop (prop: TSyntax `rel_prop): CoreM Term := do
    let rec build : List Term → List String → List Term
      | _, [] => []
      | t :: u :: ts, op :: ops =>
          build_infix t op u :: build (u :: ts) ops
      | _, _ => panic! "of_rel_prop"
    let t ← match prop with
      | `(rel_prop| $a:expr $[$ops:rel_op $bs:expr]*) => do
            let ts ← (a :: bs.toList).mapM of_expr
            let ops := ops.toList.map syntax_atom
            multi_and (build ts ops)
      | _ => throwError "unknown rel_prop"
    pure (set_info_from t prop)

  partial def of_multi_or (prop: TSyntax `multi_or): CoreM Term := do
    let t ← match prop with
      | `(multi_or| $s:multi_specifier one of $es,* is true) =>
            of_multi_specifier s (← es.getElems.toList.mapM of_rel_prop) >>= multi_and
      | _ => throwError "unknown multi_or"
    pure (set_info_from t prop)

  partial def of_some_or_no : TSyntax `some_or_no → CoreM Bool
    | `(some_or_no| some) => pure true
    | `(some_or_no| no) => pure false
    | _ => throwError "unknown some_or_no"

  partial def of_prop (prop: TSyntax `prop): CoreM Term := do
    let t ← match prop with
      | `(prop| $e:rel_prop) => of_rel_prop e
      | `(prop| $p:prop and $q:prop) => do `($(← of_prop p) ∧ $(← of_prop q))
      | `(prop| $p:prop or $q:prop) => do `($(← of_prop p) ∨ $(← of_prop q))
      | `(prop| $p:prop implies $q:prop)
      | `(prop| $_:_if $p:prop then $q:prop) => do `($(← of_prop p) → $(← of_prop q))
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
      | `(prop| $_:_either $p:prop , or $q:prop) => do `($(← of_prop p) ∨ $(← of_prop q))
      | `(prop| $m:multi_or) => of_multi_or m
      | `(prop| $_:have_contradiction) => pure mk_false
      | stx => throwError s!"unknown prop: {stx}"
    pure (set_info_from t prop)
end

inductive Reason where
  | tactic (t: Syntax.Tactic)
  | apply (ns: List Name)
  | induction

def of_reason: TSyntax `reason → CoreM (Option Reason)
  | `(reason| [ $t:tactic ]) => pure (Reason.tactic t)
  | `(reason| $[$n:ident] and*) =>
        pure (Reason.apply (n.toList.map TSyntax.getId))
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

def ex_vars : Term → List Ident
  | `(∃ $[$xs:ident]* : $_type:ident, $_p) => xs.toList
  | _ => []

inductive ProofStep where
  | assert (p: ETerm) (reason: List (Option Reason))
  | let (ids: List Name) (type: Term)
  | let_def (id: Name) (e: Term)
  | assume (p: Term)
  | is_some (ids: List Name) (type: Name) (p: Term) (reason: Option Reason)
  | if_otherwise (p: Term) (if_true: List ProofStep) (if_false: List ProofStep) (concl: Term)
  | case (cases: List (Term × List ProofStep)) (concl: Term)
  | group (steps: List ProofStep)
deriving Nonempty

partial def step_decl_vars (step: ProofStep): List Name :=
  let of_steps (steps: List ProofStep) := (steps.flatMap step_decl_vars).eraseDups
  match step with
    | .assert .. => []
    | .let ids _ => ids
    | .let_def id _ => [id]
    | .assume p => ex_vars p |>.map TSyntax.getId
    | .is_some ids .. => ids
    | .if_otherwise _p t f _q => of_steps (t ++ f)
    | .case cases _ => of_steps (cases.map Prod.snd).flatten
    | .group steps => of_steps steps

mutual
partial def step_free_vars : ProofStep → List Name
  | .assert p _ => eterm_free_vars p
  | .let _ _ => []
  | .let_def _ e => free_vars e
  | .assume p => free_vars p
  | .is_some ids _ p _ => (free_vars p).removeAll ids
  | .if_otherwise p t f q => ([p, q].flatMap free_vars ++ [t, f].flatMap all_free_vars).eraseDups
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

def of_because_prop : TSyntax `because_prop → CoreM ProofStep
  | `(because_prop| $_:_since $p:prop) => do
       pure $ .assert (.term (← of_prop p)) [none]
  | _ => throwError "unknown because_prop"

def of_which_is_contradiction: TSyntax `which_is_contradiction → CoreM (List ProofStep)
  | `(which_is_contradiction|
          , $[again]? contradicting $i:ident $b:because_prop ?) => do
        let because ← b.toList.mapM of_because_prop
        let s := assert_step mk_false (.some (.apply [i.getId]))
        pure (because ++ [s])
  | _ => throwError "unknown which_is_contradiction"

def mk_step (t: Term) (r: Option Reason): ProofStep := match t with
  | `(∃ $[$xs:ident]* : $type:ident, $p) =>
        .is_some (xs.toList.map TSyntax.getId) type.getId p r
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

def of_type_suffix: TSyntax `type_suffix → CoreM Term
  | `(type_suffix| : $type:type) => of_type type
  | `(type_suffix| be $type:natural_type) => of_natural_type type
  | _ => throwError "unknown type_suffix"

def of_let_step: TSyntax `let_step → CoreM ProofStep
  | `(let_step| $_:_let $ids:id_list $type:type_suffix) => do
        let ids := (← of_id_list ids).toList.map TSyntax.getId
        pure $ .let ids (← of_type_suffix type)
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
  | `(assert_step| $_:_so ? $p:proof_prop) => of_proof_prop p
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

partial def of_otherwise_unit: TSyntax `otherwise_unit → CoreM ProofStep
  | `(otherwise_unit| $intro:otherwise_intro $_:_otherwise $fs:proof_unit*
                     $_:_any_case $q:prop .) => do
      let (p, ts) ← of_otherwise_intro intro
      pure $ ProofStep.if_otherwise p ts (← fs.toList.flatMapM of_proof_unit) (← of_prop q)
  | _ => throwError "unknown otherwise_unit"

partial def of_proof_unit: TSyntax `proof_unit → CoreM (List ProofStep)
  | `(proof_unit| $o:otherwise_unit) =>
      List.singleton <$> of_otherwise_unit o
  | `(proof_unit| $s:proof_sentence) => of_proof_sentence s
  | _ => throwError "unknown proof_unit"
end

def of_case: TSyntax `case → CoreM (Nat × Term × List ProofStep)
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
          if overlap (step_decl_vars step) vars.flatten
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
  | .some (.apply ns) => `(by default_apply $(ns.toArray.map mkIdent)*)
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

partial def translate (top: Bool) (parent_ex: List Name) (prev: Term) (concl: Option Term)
      : List Block → CoreM (Term × Term)
  | [] => match concl with
      | .some c => do pure (← `(show $c by default), c)
      | _ => do
        let t ← if top then `(by default) else
          if overlap parent_ex (free_vars prev) then
            let ids := (parent_ex.map Lean.mkIdent).toArray
            `(show ∃ $[$ids:ident]*, $prev by default)
          else `(this)
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
      let (f, prop) ← match step with
        | .assert (.term p) rs => do
              let b := with_info (← tactic rs[0]!) p
              pure $ (fun r => `(have: $p := $b; $r), p)
        | .assert (.eq_chain ts) reasons => do
            let tactics ← reasons.mapM tactic
            let mk_step t tactic :=
              let b := with_info2 tactic t
              `(calcStep| _ = $t := $b)
            let steps ← (ts.drop 2).zipWithM mk_step (tactics.drop 1)
            let b := with_info2 tactics[0]! ts[1]!
            pure (fun r => `(have: _ := calc $(ts[0]!) = $(ts[1]!) := $b
                             $(steps.toArray)* ; $r),
                  ← `($(ts.head!) = $(ts.getLast!)))
        | .let ids type =>
            let ids := ids.toArray.map mkIdent
            pure (fun r => `(have: _ := fun $ids* : $type => $c; $r),
                  ← `(∀ $ids:ident* : $type, _))
        | .let_def id e =>
            let t := `(let $(mkIdent id) := $e; $c)
            pure (
              fun r => do
                if rest.isEmpty && concl == none then t
                else `(have: _ := $(← t); $r),
              child_concl)
        | .assume p =>
            let vars := ex_vars p
            let pat ← ex_pattern vars
            pure (fun r => `(have: _ := fun ($pat:term : $p) => $c; $r),
                    ← `($p → _))
        | .is_some ids type p reason => do
            let b := with_info (← tactic reason) p
            let ids := ids.map mkIdent
            let vars ← if children.isEmpty then `(this) else ex_pattern ids
            let a := ids.toArray
            let t := `(have $vars:term : (∃ $[$a:ident]* : $(mkIdent type), $p) := $b; $c)
            pure (
              fun r => do
                if rest.isEmpty && concl == none then t
                else `(have: _ := $(← t); $r),
                child_concl)
        | .if_otherwise _ _ _ q => do
            let ts ← List.toArray <$> children.mapM (translate_case q)
            pure (fun r => `(have: _ := Classical.byCases $ts*; $r), q)
        | .case cases concl =>
            let ts ← List.toArray <$> children.mapM (translate_case concl)
            let d ← multi_or (cases.map Prod.fst)
            let f := Lean.mkIdent $ match ts.size with
              | 2 => `Or.elim
              | 3 => `Or.elim3
              | _ => panic! "unimplemented"
            let t ← `($f (show $d by default) $ts*)
            pure (fun r => `(have: _ := $t; $r),
                  concl)
        | .group _ => panic! "group unexpected"
      let (r, rest_concl) ← translate top parent_ex prop concl rest
      let t ← f r
      pure (t, rest_concl)

inductive Proof where
  | steps (l: List ProofStep)
  | proof_by (r: Option Reason)

def translate_proof (lets: Option ProofStep) (thm: Term): Proof → CoreM Term
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
      Prod.fst <$> translate True [] (← `(())) none blocks
  | .proof_by r => tactic r

def of_proof: TSyntax `proof → CoreM Proof
  | `(proof| $steps:case_unit*) => do
        pure $ .steps $ List.flatten (← steps.toList.mapM of_case_unit)
  | `(proof| By $r:reason .) => do pure $ .proof_by (← of_reason r)
  | _ => throwError "unknown proof"

def of_proof_item: TSyntax `proof_item → CoreM (Name × Proof)
  | `(proof_item| $i:ident . $p:proof) => do pure (i.getId, (← of_proof p))
  | _ => throwError "unknown proof_item"

def of_proof_items: TSyntax `proof_items → CoreM (List (Name × Proof))
  | `(proof_items| $ps:proof_item*) => ps.toList.mapM of_proof_item
  | _ => throwError "unknown proof_items"

-- statements

def of_constructor: TSyntax `constructor → CoreM (Term × Term)
  | `(constructor| $c:const : $t:type) => do pure (← of_const c, ← of_type t)
  | _ => throwError "unknown constructor"

def to_ident: Term → Ident
  | `($n:num) => mkIdent (Name.mkSimple s!"n{n.getNat}")
  | `($i:ident) => i
  | _ => panic! "to_ident: unknown"

def aux_ctor_def (typ:Ident) (t: Term): CoreM Command :=
  let dot (i: Ident) := mkIdent (typ.getId ++ i.getId)
  match t with
    | `($_:num) =>
        `(instance: $(mkIdent ``OfNat) $typ $t where
            $(mkIdent `ofNat):ident := $(dot (to_ident t)))
    | `($i:ident) => `(abbrev $i := $(dot i))
    | _ => throwError "aux_ctor_def: unknown"

def of_type_def : TSyntax `type_def → CoreM Command
  | `(type_def| The type $i:ident is defined inductively
                with constructors $cs:constructor and* .) => do
      let ctors ← cs.getElems.mapM of_constructor
      let mk_def | (n, t) => `(ctor| | $(to_ident n):ident : $t)
      let ctor_defs ← ctors.mapM mk_def
      let ind_decl ← `(inductive $i:ident $ctor_defs:ctor*)
      let aux ← (ctors.map (·.1)).mapM (aux_ctor_def i)
      let commands := #[ind_decl] ++ aux
      pure $ .mk (mkNullNode commands)
  | _ => throwError "unknown definition"

def of_top_sentence : TSyntax `top_sentence → CoreM (Term × Option Name × Option Name)
  | `(top_sentence| $p:prop . $[ [ $i:ident $[ : @ $a:ident ]? ] ]?) => do
      pure (← of_prop p, i.map getId, a.join.map getId)
  | _ => throwError "unknown top_sentence"

abbrev Label := Name

structure ThmDecl where
  label: Option Label
  thm: Term
  name: Option Name
  attr: Option Name

def of_prop_item : TSyntax `prop_item → CoreM ThmDecl
  | `(prop_item| $i:ident . $s:top_sentence) => do
      let (thm, name, attr) ← of_top_sentence s
      pure ⟨i.getId, thm, name, attr⟩
  | _ => throwError "unknown prop_item"

def of_binary_op : TSyntax `binary_op → CoreM String
  | `(binary_op| +) => pure "+"
  | `(binary_op| <) => pure "<"
  | _ => throwError "unknown binary_op"

def op_map := [("+", `add, `Add), ("<", `lt, `LT), ("≤", `le, `LE)]

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

def generate_def (op: String) (_args: Array Ident) (type: Ident) (eqs: Array Term)
    : CoreM Command := do
  let (op_name, cl) := (op_map.lookup op).get!
  let fname := mkIdent (type.getId ++ op_name)
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

def of_cases_def : TSyntax `cases_def → CoreM Command
  | `(cases_def| The binary operation $op:binary_op on $type:ident is defined recursively
                    such that for all $ids_type:ids_type , $items:prop_item*) => do
      let (xs, _type) ← of_ids_type ids_type
      let eqs ← Array.map ThmDecl.thm <$> items.mapM of_prop_item
      generate_def (← of_binary_op op) xs type eqs
  | _ => throwError "unknown cases_def"

def of_direct_def : TSyntax `direct_def → CoreM Command
  | `(direct_def| $_:_for_all $ids_type:ids_type , $p:prop .) => do
      let (args, type) ← of_ids_type ids_type
      let eq ← of_prop p
      let (op, _, _, _) ← parse_def_eq eq
      match type with
        | `($i:ident) => generate_def op args i #[eq]
        | _ => throwError "simple type expected"
  | _ => throwError "unknown direct_def"

def of_definition : TSyntax `definition → CoreM Command
  | `(definition| $d:type_def) => of_type_def d
  | `(definition| $e:cases_def) => of_cases_def e
  | `(definition| $d:direct_def) => of_direct_def d
  | _ => throwError "unknown definition"

elab d:definition_stmt : command => do
  let c ← match d with
    | `(definition_stmt| Definition. $d) => liftCoreM (of_definition d)
    | _ => throwError "unknown definition_stmt"
  elabCommand c

def match_proofs : List ThmDecl → List (Label × Proof) → CoreM (List (ThmDecl × Option Proof))
  | [], [] => pure []
  | decl :: ts, (j, proof) :: ps =>
      if decl.label == j then .cons (decl, .some proof) <$> match_proofs ts ps
      else .cons (decl, .none) <$> match_proofs ts ((j, proof) :: ps)
  | decl :: ts, [] => .cons (decl, .none) <$> match_proofs ts []
  | [], (j, _) :: _ => throwError s!"unmatched proof label: {j}"

def generalize (lets: Option ProofStep) (t: Term) : CoreM Term := match lets with
  | .none => pure t
  | .some (.let ids type) =>
      let ids := (ids.inter (free_vars t)).toArray.map mkIdent
      if ids == #[] then pure t else `(∀ $ids:ident* : $type, $t)
  | _ => throwError "generalize: unexpected step"

def of_props_proofs (lets: Option ProofStep) : TSyntax `props_proofs →
        CoreM (List (ThmDecl × Option Term))
  | `(props_proofs| $s:top_sentence $[ Proof. $proof:proof ]?) => do
      let (thm, opt_name, opt_attr) ← of_top_sentence s
      let proof ← proof.mapM of_proof
      let decl := ThmDecl.mk none (← generalize lets thm) opt_name opt_attr
      pure [ (decl, ← proof.mapM (translate_proof lets thm)) ]
  | `(props_proofs| $ps:prop_item* $[ Proof. $pis:proof_items ]?) => do
      let label_thms ← ps.toList.mapM of_prop_item
      let label_proofs := (← pis.mapM of_proof_items).getD []
      let thms_proofs ← match_proofs label_thms label_proofs
      thms_proofs.mapM (fun (decl, proof) => do
        pure ({decl with thm := ← generalize lets decl.thm},
              ← proof.mapM (translate_proof lets decl.thm)))
  | _ => throwError "unknown prop_or_items"

elab t:_theorem : command => do
  let c : Command ← liftCoreM $ match t with
    | `(_theorem| $_:_thm $name:ident ? $_:str ? .
            $[$ls:let_step .]? $ps:props_proofs) => do
        let name := name.map getId
        let thms_proofs ← of_props_proofs (← ls.mapM of_let_step) ps
        let commands ← thms_proofs.toArray.mapM (fun (⟨label, thm, thm_name, attr⟩, proof) => do
          let proof := proof.getD (← `(by default))
          let name := thm_name <|> name.map (fun name => label.elim name (name ++ ·))
          let a ← attr.mapM (fun a => `(attributes| @[$(mkIdent a):ident]))
          match name with
            | Option.some name =>
                `($a:attributes ? theorem $(mkIdent name) : $thm := $proof)
            | Option.none => `(example : $thm := $proof))
        pure $ .mk (mkNullNode commands)
    | _ => throwError "unknown theorem"
  elabCommand c
