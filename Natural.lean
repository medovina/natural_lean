import Aesop
import Mathlib.Data.Set.Defs

import Natural.Grammar

open Lean

def range_info (s: TSyntax α) := match s.raw.getRange? with
    | .some ⟨pos, endPos⟩ => SourceInfo.synthetic pos endPos
    | .none => SourceInfo.none

def set_info_from (s: TSyntax α) (t: TSyntax β): Term :=
  ⟨s.raw.setInfo (range_info t)⟩

partial def syntax_free_vars (s: Syntax): List Name := match s with
  | `(∀ $x:ident* : $_typ, $t) => (syntax_free_vars t).removeAll (x.toList.map TSyntax.getId)
  | `(Exists (fun $x:ident : $_typ => $t)) => (syntax_free_vars t).erase (x.getId)
  | `({($x:ident) : $_typ | $t}) => (syntax_free_vars t).erase (x.getId)
  | _ => match s with
    | .missing => []
    | .node _ _ args => args.toList.flatMap syntax_free_vars |>.eraseDups
    | .ident _ _ _ _ => [s.getId]
    | .atom _ _ => []

def free_vars (t: Term): List Name := syntax_free_vars (t.raw)

-- expr/prop translation

abbrev TExpr := TSyntax `expr
abbrev TProp := TSyntax `prop

mutual
  partial def of_expr (expr: TExpr): MacroM Term := do
    let t ← match expr with
      | `(expr| $n:num) => `($n)
      | `(expr| $i:ident) => `($i)
      | `(expr| $e:expr + $f:expr) => do `($(← of_expr e) + $(← of_expr f))
      | `(expr| $e:expr ( $f:expr )) => do `($(← of_expr e) $(← of_expr f))
      | `(expr| ( $e:expr )) => of_expr e
      | `(expr| { $x:ident : $t:ident | $p:prop }) => do `({($x) : $t | $(← of_prop p)})
      | _ => Macro.throwError "unknown expr"

    -- Avoid copying SourceInfo to identifiers, which produces spurious
    -- "variable not referenced" errors.
    pure (if expr matches `(expr| $_:ident) then t else set_info_from t expr)

  partial def of_prop (prop: TProp): MacroM Term := do
    let t ← match prop with
      | `(prop| $a:expr = $b:expr) => do `($(← of_expr a) = $(← of_expr b))
      | `(prop| $a:expr ≠ $b:expr) => do `($(← of_expr a) ≠ $(← of_expr b))
      | `(prop| $a:expr ∈ $b:expr) => do `($(← of_expr a) ∈ $(← of_expr b))
      | `(prop| $p:prop or $q:prop) => do `($(← of_prop p) ∨ $(← of_prop q))
      | `(prop| $p:prop implies $q:prop) => do `($(← of_prop p) → $(← of_prop q))
      | `(prop| $_:_for all $x:ident,* : $t:ident, $p:prop)
      | `(prop| $p:prop $_:_for all $x:ident,* : $t:ident) => do
            `(∀ $x* : $t, $(← of_prop p))
      | `(prop| there exists some $x:ident : $t:ident such that $p:prop) => do
          `(Exists (fun $x : $t => $(← of_prop p)))
      | stx => Macro.throwError s!"unknown prop: {stx}"
    pure (set_info_from t prop)
end

inductive Reason where
  | tactic (t: Syntax.Tactic)
  | induction

def of_reason: TSyntax `reason → MacroM Reason
  | `(reason| [ $t:tactic ]) => pure (Reason.tactic t)
  | `(reason| induction) => pure Reason.induction
  | _ => Macro.throwError "unknown reason"

def of_eq_expr_by: TSyntax `eq_expr_by → MacroM (Term × Option Reason)
  | `(eq_expr_by| = $e:expr $[ by $r:reason ]?) =>
        do pure ((← of_expr e), (← r.mapM of_reason))
  | _ => Macro.throwError "unknown eq_expr_by"

inductive ETerm where
  | term (t: Term)
  | eq_chain (ts: List Term)

def eterm_free_vars : ETerm → List Name
  | .term t => free_vars t
  | .eq_chain ts => ts.flatMap free_vars

def of_assert_prop: TSyntax `assert_prop → MacroM (ETerm × List (Option Reason))
  | `(assert_prop| $[ by $r:reason ]? $p:prop) =>
        do pure (.term (← of_prop p), [← r.mapM of_reason])
  | `(assert_prop| $e:expr $eb:eq_expr_by $ebs:eq_expr_by*) => do
        let (e1, by1) ← of_eq_expr_by eb
        let (es, bys) := (← ebs.toList.mapM of_eq_expr_by).unzip
        pure (.eq_chain ((← of_expr e) :: e1 :: es), by1 :: bys)
  | _ => Macro.throwError "unknown assert_prop"

inductive ProofStep where
  | assert (p: ETerm) (reason: List (Option Reason))
  | let (ids: List Name) (type: Name)
  | let_def (id: Name) (e: Term)
  | assume (p: Term)

def step_decl_vars: ProofStep → List Name
  | .assert .. => []
  | .let ids _ => ids
  | .let_def id _ => [id]
  | .assume _ => []

def step_vars : ProofStep → List Name
  | .assert p _ => eterm_free_vars p
  | .let _ _ => []
  | .let_def _ e => free_vars e
  | .assume p => free_vars p

instance: ToString ProofStep where
  toString
    | .assert .. => "assert"
    | .let ids _ => s!"let {ids}"
    | .let_def id _e => s!"let_def {id}"
    | .assume _p => "assume"

def of_proof_step: TSyntax `proof_step → MacroM (List ProofStep)
  | `(proof_step| $p:assert_prop) =>
        do pure [(Function.uncurry .assert) (← of_assert_prop p)]
  | `(proof_step| $_:_assume $p:prop) => do pure [.assume (← of_prop p)]
  | `(proof_step| $_:_let $ids:ident,* : $type) =>
      pure [.let (ids.getElems.toList.map TSyntax.getId) type.getId]
  | `(proof_step| $_:_let $id = $e) => do pure [.let_def id.getId (← of_expr e)]
  | `(proof_step| We have shown that $p:prop) =>
        do pure [.assert (.term (← of_prop p)) [none]]
  | `(proof_step| We must show that $_p:prop) => pure []
  | _ => Macro.throwError "unknown proof step"

def of_proof_step1: TSyntax `proof_step1 → MacroM (List ProofStep)
  | `(proof_step1| $[$i:initial]? $ps:proof_step /* .) =>
        List.flatten <$> ps.getElems.toList.mapM of_proof_step
  | _ => Macro.throwError "unknown proof step 1"

structure Block where
  step : ProofStep
  blocks: List Block

partial def show_blocks (blocks: List Block): String :=
  let rec f (indent: String) (blocks: List Block): List String :=
    blocks.flatMap (fun ⟨step, children⟩ =>
      (indent ++ toString step) :: f (indent ++ "    ") children)
  "\n".intercalate (f "" blocks)

partial def infer_blocks (steps: List ProofStep): List Block :=
  let rec infer (vars: List (List Name)) (steps: List ProofStep): List Block × List ProofStep :=
    match steps with
      | [] => ([], [])
      | (step :: rest) =>
          let in_use := steps.flatMap step_vars
          if vars.head?.all (fun vs => vs.any in_use.elem) then
            let (children, rest1) := match step with
              | .assume _ => infer vars rest
              | _ => match step_decl_vars step with
                | [] => ([], rest)
                | step_vars => infer (step_vars :: vars) rest
            let (blocks, rest2) := infer vars rest1
            (⟨step, children⟩ :: blocks, rest2)
          else ([], steps)
  let (blocks, rest) := infer [] steps
  assert! (rest = [])
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

def tactic : Option Reason → MacroM Term
  | .some (.tactic t) => `(by { $t })
  | .some (.induction) => `(by intro x ; induction x <;> aesop)
  | .none => `(by aesop)

def translate (top: Bool): List Block → MacroM Term
  | [] => if top then `(by aesop) else `(this)
  | ⟨step, children⟩ :: rest => do
      let c ← translate False children
      let r ← translate top rest
      match step with
        | .assert (.term p) rs =>
              let b := with_info (← tactic rs[0]!) p
              `(have: $p := $b; $r)
        | .assert (.eq_chain ts) reasons => do
            let tactics ← reasons.mapM tactic
            let mk_step t tactic :=
              let b := with_info2 tactic t
              `(calcStep| _ = $t := $b)
            let steps ← (ts.drop 2).zipWithM mk_step (tactics.drop 1)
            let b := with_info2 tactics[0]! ts[1]!
            `(have: _ := calc $(ts[0]!) = $(ts[1]!) := $b
                         $(steps.toArray)* ; $r)
        | .let ids type =>
            let ids := ids.toArray.map mkIdent
            `(have: _ := fun $ids* : $(mkIdent type) => $c; $r)
        | .let_def id e =>
            if (rest ≠ []) then
              dbg_trace "error: rest != []"
            `(let $(mkIdent id) := $e; $c)
        | .assume p =>
            `(have: _ := fun (_: $p) => $c; $r)

def of_proof: TSyntax `proof → MacroM Term
  | `(proof| $steps:proof_step1*) => do
      let steps := List.flatten (← steps.toList.mapM of_proof_step1)
      let blocks := infer_blocks steps
      -- dbg_trace (show_blocks blocks)
      translate True blocks
  | `(proof| By induction .) => `(by intro x ; induction x <;> aesop)
  | _ => Macro.throwError "unknown proof"

-- theorem

macro _theorem id:ident "." p:prop "." "Proof." proof:proof : command => do
  `(theorem $id : $(← of_prop p) := $(← of_proof proof))

macro _theorem id:ident "." p:prop "." : command => do
  `(theorem $id : $(← of_prop p) := by aesop)
