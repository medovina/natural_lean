import Aesop

import Natural.Prop

open Lean

namespace Natural

-- Here we reduce the default extent of an Aesop search so that it will succeed or fail
-- more quickly.
def aesop_config : Aesop.Options :=
  { maxRuleApplicationDepth := 10, maxRuleApplications := 50, maxNormIterations := 20,
    terminal := true, warnOnNonterminal := false }

macro "default" : tactic =>
  `(tactic| first | trivial | grind | aesop (config := aesop_config) |
            fail "default tactic could not prove goal")

macro "default_apply" ts:ident+ : tactic => do
  let aesop_rules ← ts.mapM (fun i => `(Aesop.rule_expr| safe (by rapply $i)))
  let t : Ident := ts[0]?.getD (panic! "default_apply")
  `(tactic| first
      | (apply $t; done)
      | (apply_rules [$[$ts:ident],*] ; done)
      | grind [$[$ts:ident],*]
      | aesop (config := aesop_config) (add $aesop_rules,*)
      | fail "default_apply could not prove goal")

-- proof steps

def of_thm_name: TSyntax ``thm_name → CoreM Ident
  | `(thm_name| $i:ident) => pure i
  | _ => throwError s!"unknown thm_name"

def of_reference: TSyntax `reference → CoreM (List Ident)
  | `(reference| $[$n:thm_name] and*) => n.toList.mapM of_thm_name
  | `(reference| $_:assumption_that $_p:prop) => pure []
  | _ => throwError s!"unknown reference"

inductive Reason where
  | tactic (t: Syntax.Tactic)
  | apply (ns: List Ident)
  | induction
  | by_definition_of (i: Ident)

def tactic : Option Reason → CoreM Term
  | .none => `(by default)
  | some r => match r with
    | .apply [] => `(by default)
    | .apply ns => `(by default_apply $(ns.toArray)*)
    | .tactic t => `(by { $t })
    | .induction => `(by intro x ; induction x <;> default)
    | .by_definition_of _ => throwError "can't follow definition"

def of_reason: TSyntax `reason → CoreM (Option Reason)
  | `(reason| [ $t:tactic ]) => pure (Reason.tactic t)
  | `(reason| $r:reference) => .some <$> Reason.apply <$> of_reference r
  | `(reason| induction) => pure Reason.induction
  | `(reason| the inductive hypothesis) => pure .none
  | `(reason| the definition of $i:ident) => pure (.some (.by_definition_of i))
  | _ => throwError "unknown reason"

def of_eq_expr_by1 (t: TSyntax `eq_expr_by): CoreM (String × Term × Term) := match t with
  | `(eq_expr_by| $op:rel_op $e:expr $[ by $r:reason ]?) => do
        let reason ← r.bindM of_reason
        do pure ((of_binary_op op), (← of_expr e), (← tactic reason))
  | _ => throwError "unknown eq_expr_by"

def of_eq_expr_by (t: TSyntax `eq_expr_by): CoreM (String × Term × Term) :=
  withRef t (of_eq_expr_by1 t)

def ex_vars (t: Term) : List (Ident × Term) := match match_binder t with
  | .some (.exists, xs, _) => xs
  | _ => []

inductive ProofStep where
  | assert (p: Term) (reason: Option Reason)
  | assert_chain (ts: List Term) (ops: List String) (tactics: List Term)
  | let (ids: List Name) (type: Term)
  | let_def (id: Name) (e: Term)
  | assume (p: Term)
  | is_some (p: Term) (reason: Option Reason)
  | if_otherwise (p: Term) (if_true: List ProofStep) (if_false: List ProofStep) (concl: Term)
  | biconditional (p: Term) (forward: List ProofStep) (q: Term) (reverse: List ProofStep)
  | case (cases: List (Term × List ProofStep)) (concl: Term)
  | group (steps: List ProofStep)
deriving Nonempty

partial def step_mapM [Monad m] (f: Term → m Term) (step: ProofStep) : m ProofStep := do
  let map_steps (steps: List ProofStep) := steps.mapM (step_mapM f)
  match step with
    | .assert t rs => pure $ .assert (← f t) rs
    | .assert_chain ts ops rs =>
        pure $ .assert_chain (← ts.mapM f) ops rs
    | .let .. => pure step
    | .let_def id t => pure $ .let_def id (← f t)
    | .assume p => pure $ .assume (← f p)
    | .is_some p r => pure $ .is_some (← f p) r
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
  | .assume p => map_fst TSyntax.getId (ex_vars p)
  | .is_some p _reason => map_fst TSyntax.getId (ex_vars p)
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
  | .assert p _ => free_vars p
  | .assert_chain ts _ _ => ts.flatMap free_vars
  | .let _ _ => []
  | .let_def _ e => free_vars e
  | .assume p => free_vars p
  | .is_some p _ => free_vars p
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
    | .assert_chain .. => "assert_chain"
    | .let ids _ => s!"let {ids}"
    | .let_def id _e => s!"let_def {id}"
    | .assume _ => s!"assume"
    | .is_some .. => s!"is_some"
    | .if_otherwise .. => "if_otherwise"
    | .biconditional .. => "biconditional"
    | .case _ _ => "case"
    | .group _ => "group"

def of_begin_chain (t: TSyntax ``begin_chain) : CoreM (Term × String × Term × Term) := withRef t
  do match t with
    | `(begin_chain| $e:expr $eb:eq_expr_by) => do
          pure (← of_expr e, ← of_eq_expr_by1 eb)
    | _ => throwError "unknown begin_chain"

def of_assert_prop: TSyntax `assert_prop → CoreM ProofStep
  | `(assert_prop| $p:prop) =>
        do pure (.assert (← of_prop p) none)
  | `(assert_prop| $bc:begin_chain $ebs:eq_expr_by*) => do
        let (e, op1, e1, by1) ← of_begin_chain bc
        let (ops, es, bys) := unzip3 (← ebs.toList.mapM of_eq_expr_by)
        pure $ .assert_chain (e :: e1 :: es) (op1 :: ops) (by1 :: bys)
  | _ => throwError "unknown assert_prop"

def of_because_prop : TSyntax ``because_prop → CoreM ProofStep
  | `(because_prop| $_:_because $p:prop) => do
       pure $ .assert (← of_prop p) none
  | _ => throwError "unknown because_prop"

def of_which_is_contra (stx: TSyntax `which_is_contra): CoreM ProofStep :=
  let contra r := do
    pure $ .assert (← `(False)) (.some (.apply $ ← r.toList.flatMapM of_reference))
  match stx with
    | `(which_is_contra| $_:which_is a contradiction $[to $r:reference]?) => contra r
    | `(which_is_contra| $_:which_is contradicting $r:reference) => contra (some r)
    | _ => throwError "unknown which_is_contra"

def of_which_is_contradiction (stx: TSyntax ``which_is_contradiction) : CoreM (List ProofStep) :=
  withRef stx do match stx with
    | `(which_is_contradiction| $c:which_is_contra $b:because_prop ?) => do
          let because ← b.toList.mapM of_because_prop
          pure (because ++ [← of_which_is_contra c])
    | _ => throwError "unknown which_is_contradiction"

def mk_step (t: Term) (r: Option Reason): ProofStep := match match_binder t with
  | .some (.exists, _vars, _p) => .is_some t r
  | _ => .assert t r

def of_follows : TSyntax ``_follows → CoreM (Option Reason)
  | `(_follows| $_:_it follows $[by $r:reason]? that) => r.bindM of_reason
  | _ => throwError "unknown follows"

def of_have : TSyntax `_have → CoreM (Option Reason)
  | `(_have| $_:have1) => pure none
  | `(_have| $f:_follows) => of_follows f
  | _ => throwError "unknown have"

def of_proof_prop: TSyntax `proof_prop → CoreM (List ProofStep)
  | `(proof_prop| $[$b:because_prop $[,]?]? $[$_:_by $r1:reason]? $[$h:_have]? $p:assert_prop
          $[by $r2:reason]? $w:which_is_contradiction ?) => do
        let because ← b.toList.mapM of_because_prop
        let step ← of_assert_prop p
        let s ← match step with
          | .assert t _ => do
              let r := (← r1.bindM of_reason) <|> (← h.bindM of_have) <|> (← r2.bindM of_reason)
              pure $ mk_step t r
          | _ => pure step
        let contra ← w.toList.flatMapM of_which_is_contradiction
        pure (because ++ [s] ++ contra)
  | _ => throwError "unknown proof_prop"

def of_let_step: TSyntax `let_step → CoreM ProofStep
  | `(let_step| $_:_let $xs:ident,* : $type:type) => do
        pure $ .let (xs.getElems.toList.map TSyntax.getId) (← of_type type)
  | `(let_step| $_:_let $xs:id_list be $_:_a ? $type:natural_type) => do
        pure $ .let ((← of_id_list xs).map TSyntax.getId) (← of_natural_type type)
  | _ => throwError "unknown let_step"

def of_let_or_assume: TSyntax `let_or_assume → CoreM ProofStep
  | `(let_or_assume| $ls:let_step) => of_let_step ls
  | `(let_or_assume| $_:_let $id = $e) =>
        do pure $ .let_def id.getId (← of_expr e)
  | `(let_or_assume| $_:_let $id = $e for some $vars:ids_types) =>
        match e with
          | `(expr| $_q:ident [ $_:expr ]) => do
              let tac : TSyntax `tactic ←
                `(tactic| (cases $id:ident using Quotient.ind; grind))
              let vars ← of_ids_types vars
              let p ← `(∃ $(← ex_binders vars)*, $id = $(← of_expr e))
              (pure $ ProofStep.is_some p (.some (.tactic tac)))
          | _ => withRef e do throwError "expected quotient projection"
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

partial def show_blocks (blocks: List Block): String := "\n" ++
  let rec f (indent: String) (blocks: List Block): List String :=
    blocks.flatMap (fun ⟨step, children⟩ =>
      (indent ++ toString step) :: f (indent ++ "    ") children)
  "\n".intercalate (f "" blocks)

def is_assert_false : ProofStep → Bool
  | .assert t _ => Syntax.getId t == ``False
  | _ => false

partial def infer_blocks (steps: List ProofStep): List Block :=
  let rec infer (vars: List (List Name)) (let_vars: List (List Name))
                (steps: List ProofStep): List Block × List ProofStep :=
    match steps with
      | [] => ([], [])
      | (step :: rest) =>
          if overlap (step_all_decl_vars step) vars.flatten then ([], steps) else
          let in_use := all_free_vars steps
          let vars_in_use := vars.head?.all (fun vs => vs.any in_use.elem)
          let let_vars_in_use := let_vars.head?.all (fun vs => vs.any in_use.elem)
          if (!is_assert_false step && !vars_in_use && !let_vars_in_use)
            then ([], steps)
            else let (blocks, rest) := match step with
              | .assert .. | .assert_chain .. => ([⟨step, []⟩], rest)
              | .let .. | .let_def .. | .assume _ | .is_some .. =>
                  let vars := if step matches (.assume _)
                    then vars else step_decl_vars step :: vars
                  let let_vars := if step matches (.let ..)
                    then step_decl_vars step :: vars else let_vars
                  let (children, rest) := infer vars let_vars rest
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
            let (blocks2, rest) := infer vars let_vars rest
            (blocks ++ blocks2, rest)
  let (blocks, rest) := infer [] [] steps
  assert! (rest.isEmpty)
  blocks

partial def resolve_block (le: LocalEnv) : Block → CoreM Block
  | ⟨step, children⟩ => do
      let ivars := match step with
        | .is_some .. => step_decl_vars_types step
        | _ => []
      pure ⟨← step_mapM (resolve_term (ivars ++ le)) step,
            ← children.mapM (resolve_block (step_decl_vars_types step ++ le))⟩

def proof_by_multi (names: List Ident) : CoreM Term :=
  tactic (.some (.apply names))

def proof_by (name: Option Ident) : CoreM Term := proof_by_multi name.toList

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

partial def translate (top: Bool) (parent_ex: List (Name × Term)) (prev: Term) (concl: Option Term)
      : List Block → CoreM (Term × Term)
  | [] => match concl with
      | .some c => do pure (← `(show $c by default), c)
      | _ => do
        if top then pure (← `(by default), prev) else
          if overlap (parent_ex.map (·.1)) (free_vars prev) then
            let ids := map_fst Lean.mkIdent parent_ex
            let ex ← `(∃ $(← ex_binders ids)*, $prev)
            pure (← `(show $ex by default), ex)
          else pure (← this_term, prev)
  | ⟨step, children⟩ :: rest => do
      let ex_decl := match step with
        | .is_some .. => step_decl_vars_types step
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
        | .assert p reason => withRef p do
              let b ← tactic reason
              pure $ (← `(letDecl| : $p:term := $b), p)
        | .assert_chain ts ops tactics => do
            let mk_step op t tactic := do
              let eq := build_infix (← `(_)) op t
              `(calcStep| $eq := $tactic)
            let eq1 := build_infix ts[0]! ops[0]! ts[1]!
            let steps ← zipWith3M mk_step (ops.drop 1) (ts.drop 2) (tactics.drop 1)
            pure (← `(letDecl| : _ := calc $eq1 := $(tactics[0]!)
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
        | .is_some p reason => withRef p do
            let vars ← if children.isEmpty then this_term
              else ex_pattern ((ex_vars p).map (·.1))
            let t ← `(have $vars:term : $p := $(← tactic reason); $c)
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
              | 2 => ``Or.elim
              | 3 => ``Or.elim3
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

-- proofs

inductive _Proof where
  | steps (l: List ProofStep)
  | proof_by (r: Option Reason)

def generalize (lets: Option ProofStep) (t: Term) : CoreM Term := match lets with
  | .none => pure t
  | .some (.let ids type) =>
      let ids := (ids.inter (free_vars t)).toArray.map mkIdent
      if ids == #[] then pure t else `(∀ $ids:ident* : $type, $t)
  | _ => throwError "generalize: unexpected step"

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
      trace[natural.tree] show_blocks blocks
      let blocks ← blocks.mapM (resolve_block [])
      Prod.fst <$> translate True [] (← `(())) none blocks
  | .proof_by (.some (.by_definition_of i)) => do
      let env ← getEnv
      let q := i.getId
      let .some info := env.find? q | throwError "type not found"
      let .some val := info.value? | throwError "no value"
      unless val.isAppOf ``Quotient do throwError "not a quotient type"
      let gthm ← generalize lets thm
      let qvars := (bound_vars gthm).filterMap (fun (x, type) => do
        if Syntax.getId type == q then some (mkIdent x) else none)
      if qvars == [] then throwError "no arguments of given type"
      let ind ← qvars.mapM (fun x => `(tactic| cases $x:ident using Quotient.ind))
      `(by
        intros $(qvars.toArray)*
        $(ind.toArray)*
        apply Quotient.sound
        default)
  | .proof_by r => tactic r

def of_proof: TSyntax `proof → CoreM _Proof
  | `(proof| $steps:case_unit*) => do
        pure $ .steps $ List.flatten (← steps.toList.mapM of_case_unit)
  | `(proof| By $r:reason .) => do pure $ .proof_by (← of_reason r)
  | _ => throwError "unknown proof"
