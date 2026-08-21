import Aesop
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Logic.Basic

import Natural.Grammar

open Lean

infix:50 "≮" => fun x y => ¬(x < y)
infix:50 "≯" => fun x y => ¬(x > y)

macro "default" : tactic => `(tactic| first | trivial | grind | aesop )

macro "default_apply" t:ident+ : tactic =>
  `(tactic| first | (apply_rules [$[$t:ident],*] ; done) | grind [$[$t:ident],*] | aesop)

def range_info (s: TSyntax α) := match s.raw.getRange? with
    | .some ⟨pos, endPos⟩ => SourceInfo.synthetic pos endPos
    | .none => SourceInfo.none

def set_info_from (s: TSyntax α) (t: TSyntax β): Term :=
  ⟨s.raw.setInfo (range_info t)⟩

def multi_and : List Term → MacroM Term := foldr1M (fun t a => `($t ∧ $a))

def multi_or : List Term → MacroM Term := foldr1M (fun t a => `($t ∨ $a))

def at_most (ts: List Term) : MacroM (List Term) :=
  let pair (t: Term) (u: Term) := do
    `(¬($t ∧ $u))
  (all_pairs ts).mapM pair.uncurry

def precisely_one (ts: List Term) : MacroM (List Term) :=
  List.cons <$> multi_or ts <*> at_most ts

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

-- expr/prop translation

abbrev TExpr := TSyntax `expr
abbrev TProp := TSyntax `prop

def of_multi_specifier : TSyntax `multi_specifier → List Term → MacroM (List Term)
  | `(multi_specifier| $_:_at_least) => fun ts => List.singleton <$> multi_or ts
  | `(multi_specifier| $_:_at_most) => at_most
  | `(multi_specifier| $_:_exactly) => precisely_one
  | _ => fun _ => Macro.throwError "unknown multi_specifier"

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

  partial def of_eq_prop (prop: TSyntax `eq_prop): MacroM Term := do
    let t ← match prop with
      | `(eq_prop| $a:expr = $b:expr) => do `($(← of_expr a) = $(← of_expr b))
      | `(eq_prop| $a:expr ≠ $b:expr) => do `($(← of_expr a) ≠ $(← of_expr b))
      | `(eq_prop| $a:expr < $b:expr) => do `($(← of_expr a) < $(← of_expr b))
      | `(eq_prop| $a:expr ≮ $b:expr) => do `($(← of_expr a) ≮ $(← of_expr b))
      | `(eq_prop| $a:expr ≤ $b:expr) => do `($(← of_expr a) ≤ $(← of_expr b))
      | `(eq_prop| $a:expr > $b:expr) => do `($(← of_expr a) > $(← of_expr b))
      | `(eq_prop| $a:expr ≥ $b:expr) => do `($(← of_expr a) ≥ $(← of_expr b))
      | `(eq_prop| $a:expr ≯ $b:expr) => do `($(← of_expr a) ≯ $(← of_expr b))
      | `(eq_prop| $a:expr ∈ $b:expr) => do `($(← of_expr a) ∈ $(← of_expr b))
      | _ => Macro.throwError "unknown eq_prop"
    pure (set_info_from t prop)

  partial def of_multi_or (prop: TSyntax `multi_or): MacroM Term := do
    let t ← match prop with
      | `(multi_or| $s:multi_specifier one of $es,* is true) =>
            of_multi_specifier s (← es.getElems.toList.mapM of_eq_prop) >>= multi_and
      | _ => Macro.throwError "unknown multi_or"
    pure (set_info_from t prop)

  partial def of_prop (prop: TProp): MacroM Term := do
    let t ← match prop with
      | `(prop| $e:eq_prop) => of_eq_prop e
      | `(prop| $p:prop and $q:prop) => do `($(← of_prop p) ∧ $(← of_prop q))
      | `(prop| $p:prop or $q:prop) => do `($(← of_prop p) ∨ $(← of_prop q))
      | `(prop| $p:prop implies $q:prop)
      | `(prop| if $p:prop then $q:prop) => do `($(← of_prop p) → $(← of_prop q))
      | `(prop| $p:prop $_:_iff $q:prop) => do `($(← of_prop p) ↔ $(← of_prop q))
      | `(prop| $_:_for all $x:ident,* : $t:ident, $p:prop)
      | `(prop| $p:prop $_:_for all $x:ident,* : $t:ident) => do
            `(∀ $x* : $t, $(← of_prop p))
      | `(prop| there $_:_exists $[some]? $x:ident,* : $t:ident such that $p:prop)
      | `(prop| $p:prop $_:_for some $x:ident,* : $t:ident) => do
            `(∃ $[$x:ident]* : $t, $(← of_prop p))
      | `(prop| $_:_either $p:prop , or $q:prop) => do `($(← of_prop p) ∨ $(← of_prop q))
      | `(prop| $m:multi_or) => of_multi_or m
      | stx => Macro.throwError s!"unknown prop: {stx}"
    pure (set_info_from t prop)
end

inductive Reason where
  | tactic (t: Syntax.Tactic)
  | apply (ns: List Name)
  | induction

def of_reason: TSyntax `reason → MacroM (Option Reason)
  | `(reason| [ $t:tactic ]) => pure (Reason.tactic t)
  | `(reason| $[$_:_thm $n:ident] and*) =>
        pure (Reason.apply (n.toList.map TSyntax.getId))
  | `(reason| induction) => pure Reason.induction
  | `(reason| the inductive hypothesis) => pure .none
  | _ => Macro.throwError "unknown reason"

def of_eq_expr_by: TSyntax `eq_expr_by → MacroM (Term × Option Reason)
  | `(eq_expr_by| = $e:expr $[ by $r:reason ]?) =>
        do pure ((← of_expr e), (← r.bindM of_reason))
  | _ => Macro.throwError "unknown eq_expr_by"

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
  | let (ids: List Name) (type: Name)
  | let_def (id: Name) (e: Term)
  | assume (p: Term)
  | is_some (ids: List Name) (type: Name) (p: Term) (reason: Option Reason)
  | group (steps: List ProofStep)
deriving Nonempty

def step_decl_vars: ProofStep → List Name
  | .assert .. => []
  | .let ids _ => ids
  | .let_def id _ => [id]
  | .assume p => ex_vars p |>.map TSyntax.getId
  | .is_some ids .. => ids
  | .group steps => (steps.flatMap step_decl_vars).eraseDups

def step_free_vars : ProofStep → List Name
  | .assert p _ => eterm_free_vars p
  | .let _ _ => []
  | .let_def _ e => free_vars e
  | .assume p => free_vars p
  | .is_some ids _ p _ => (free_vars p).removeAll ids
  | .group steps => (steps.flatMap step_free_vars).eraseDups

instance: ToString ProofStep where
  toString
    | .assert .. => "assert"
    | .let ids _ => s!"let {ids}"
    | .let_def id _e => s!"let_def {id}"
    | .assume _ => s!"assume"
    | .is_some id .. => s!"is_some {id}"
    | .group _ => "group"

def of_assert_prop: TSyntax `assert_prop → MacroM (ETerm × List (Option Reason))
  | `(assert_prop| $p:prop) =>
        do pure (.term (← of_prop p), [none])
  | `(assert_prop| $e:expr $eb:eq_expr_by $ebs:eq_expr_by*) => do
        let (e1, by1) ← of_eq_expr_by eb
        let (es, bys) := (← ebs.toList.mapM of_eq_expr_by).unzip
        pure (.eq_chain ((← of_expr e) :: e1 :: es), by1 :: bys)
  | _ => Macro.throwError "unknown assert_prop"

def mk_false : Term := mkIdent ``False

def assert_step (t: Term) (r: Option Reason): ProofStep :=
  .assert (.term t) [r]

def of_which_is_contradiction: TSyntax `which_is_contradiction → MacroM ProofStep
  | `(which_is_contradiction| , $[again]? contradicting $_:_thm $i:ident) => do
        pure $ assert_step mk_false (.some (.apply [i.getId]))
  | _ => Macro.throwError "unknown which_is_contradiction"

def mk_step (t: Term) (r: Option Reason): ProofStep := match t with
  | `(∃ $[$xs:ident]* : $type:ident, $p) =>
        .is_some (xs.toList.map TSyntax.getId) type.getId p r
  | _ => assert_step t r

def of_proof_prop: TSyntax `proof_prop → MacroM (List ProofStep)
  | `(proof_prop| $[$_:_by $r:reason]? $[$_:_have]? $p:assert_prop
          $[by $r2:reason]? $w:which_is_contradiction ?) => do
        let (e, rs) ← of_assert_prop p
        let s := match e with
          | .term t => do pure $ mk_step t ((← r.bindM of_reason) <|> (← r2.bindM of_reason))
          | .eq_chain _ => pure (.assert e rs)
        List.cons <$> s <*> w.toList.mapM of_which_is_contradiction
  | _ => Macro.throwError "unknown proof_prop"

def of_let_or_assume: TSyntax `let_or_assume → MacroM ProofStep
  | `(let_or_assume| $_:_let $ids:ident,* : $type) =>
        pure $ .let (ids.getElems.toList.map TSyntax.getId) type.getId
  | `(let_or_assume| $_:_let $id = $e) =>
        do pure $ .let_def id.getId (← of_expr e)
  | `(let_or_assume| $_:_assume $p:prop) => do pure $ .assume (← of_prop p)
  | _ => Macro.throwError "unknown let_or_assume"

def of_proof_if_prop: TSyntax `proof_if_prop → MacroM ProofStep
  | `(proof_if_prop| $_:_if $p:prop $[,]? then $[$qs:proof_prop]/*) => do
        pure $ .group (.assume (← of_prop p) :: (← qs.toList.flatMapM of_proof_prop))
  | _ => Macro.throwError "unknown proof_if_prop"

def of_assert_step: TSyntax `assert_step → MacroM (List ProofStep)
  | `(assert_step| $p:proof_if_prop) => .singleton <$> of_proof_if_prop p
  | `(assert_step| $_:will_show $_p:prop) => pure []
  | `(assert_step| $_:_so ? $p:proof_prop) => of_proof_prop p
  | `(assert_step| $_:have_contradiction) => do
        pure $ [assert_step mk_false none]
  | _ => Macro.throwError "unknown assert_step"

def of_proof_sentence1: TSyntax `proof_sentence1 → MacroM (List ProofStep)
  | `(proof_sentence1| $ls:let_or_assume /*) =>
        ls.getElems.toList.mapM of_let_or_assume
  | `(proof_sentence1| $s:assert_step /*) =>
        s.getElems.toList.flatMapM of_assert_step
  | _ => Macro.throwError "unknown proof_sentence1"

def of_proof_sentence: TSyntax `proof_sentence → MacroM (List ProofStep)
  | `(proof_sentence| $_:clause_intro ? $s:proof_sentence1 .) =>
      of_proof_sentence1 s
  | _ => Macro.throwError "unknown proof_sentence"

structure Block where
  step : ProofStep
  blocks: List Block
deriving Nonempty

partial def show_blocks (blocks: List Block): String :=
  let rec f (indent: String) (blocks: List Block): List String :=
    blocks.flatMap (fun ⟨step, children⟩ =>
      (indent ++ toString step) :: f (indent ++ "    ") children)
  "\n".intercalate (f "" blocks)

def all_vars : List ProofStep → List Name
  | [] => []
  | step :: steps =>
      (step_free_vars step ++ all_vars steps).removeAll (step_decl_vars step) |>.eraseDups

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
          let in_use := all_vars steps
          if (!is_assert_false step && !vars.head?.all (fun vs => vs.any in_use.elem))
            then ([], steps)
            else let (blocks, rest) := match step with
              | .assert .. => ([⟨step, []⟩], rest)
              | .group steps =>
                  let rec group_blocks steps : List Block := match steps with
                    | [] => []
                    | steps =>
                        let (blocks, rest) := infer [] steps
                        blocks ++ group_blocks rest
                  (group_blocks steps, rest)
              | _ =>
                  let vars := if step matches (.assume _) then vars
                    else step_decl_vars step :: vars
                  let (children, rest) := infer vars rest
                  ([⟨step, children⟩], rest)
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

def tactic : Option Reason → MacroM Term
  | .some (.tactic t) => `(by { $t })
  | .some (.apply ns) => `(by default_apply $(ns.toArray.map mkIdent)*)
  | .some (.induction) => `(by intro x ; induction x <;> default)
  | .none => `(by default)

def produces_let : ProofStep → Bool
  | .let_def .. | .is_some .. => true
  | _ => false

-- Given a list of ids such as [x, y, z], produce an existential
-- binding pattern such as `( ⟨x, ⟨y, ⟨z, _⟩⟩⟩ ).
def ex_pattern : List Ident → MacroM Term
  | [] => `(_)
  | x :: xs => do
      let p ← ex_pattern xs
      `(⟨$x, $p⟩)

partial def translate (top: Bool) (parent_ex: List Name) (prev: Term) (concl: Option Term)
      : List Block → MacroM (Term × Term)
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
        translate (top && rest.isEmpty && produces_let step) ex_decl unit none children
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
            pure (fun r => `(have: _ := fun $ids* : $(mkIdent type) => $c; $r),
                  ← `(∀ $ids:ident* : $(mkIdent type), _))
        | .let_def id e =>
            let t := `(let $(mkIdent id) := $e; $c)
            pure (
              fun r => do
                if rest.isEmpty then t
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
            let vars ← ex_pattern ids
            let a := ids.toArray
            let t := `(have $vars:term : (∃ $[$a:ident]* : $(mkIdent type), $p) := $b; $c)
            pure (
              fun r => do
                if rest.isEmpty then t
                else `(have: _ := $(← t); $r),
                child_concl)
        | .group _ => panic! "group unexpected"
      let (r, rest_concl) ← translate top parent_ex prop concl rest
      let t ← f r
      pure (t, rest_concl)

def of_proof: TSyntax `proof → MacroM Term
  | `(proof| $steps:proof_sentence*) => do
      let steps := List.flatten (← steps.toList.mapM of_proof_sentence)
      let blocks := infer_blocks steps
      dbg_trace (show_blocks blocks)
      Prod.fst <$> translate True [] (← `(())) none blocks
  | `(proof| By $r:reason .) => tactic =<< of_reason r
  | _ => Macro.throwError "unknown proof"

-- theorem

macro t:_theorem : command => do
  match t with
    | `(_theorem| $_:_thm $id:ident $[ $_:str ]? . $p:prop . $[ Proof. $proof:proof ]?) =>
        let pr ← (proof.map of_proof).getD `(by default)
        `(theorem $id : $(← of_prop p) := $pr)
    | _ => Macro.throwError "unknown theorem"
