import Lean

import Batteries.Data.List.Basic
open Lean hiding mkStrLit
open Elab Tactic Meta
open Elab.Command
open Lean.Syntax (mkStrLit)

-- pairs

def map_fst (f : α → γ) (pair : Prod α β) := pair.map f id
def map_snd (f : β → γ) (pair : Prod α β) := pair.map id f

def mapM_fst [Monad m] (f : α → m γ) : Prod α β → m (Prod γ β)
  | (x, y) => do pure (← f x, y)

def mapM_snd [Monad m] (f : β → m γ) : Prod α β → m (Prod α γ)
  | (x, y) => do pure (x, ← f y)

-- lists

def overlap [BEq α] (xs: List α) (ys: List α): Bool := xs.inter ys != []

def all_pairs : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ all_pairs xs

def foldr1M [Monad m] [Inhabited α] (f: α → α → m α) (xs: List α) : m α := match xs with
  | [x] => pure x
  | x :: xs => do
      let r ← foldr1M f xs
      f x r
  | _ => panic! "foldr1M"

-- syntax

macro "kdef" name:ident "=" ks:sepBy1(str, "|") : command => do
  let rec mk_or : List (TSyntax `stx) → MacroM (TSyntax `stx)
    | [] => panic! "empty"
    | [x] => pure x
    | x :: xs => do `(stx| $x <|> $(← mk_or xs))

  let mk_stx (s: String) : MacroM (TSyntax `stx) :=
    let i := mkStrLit s
    if s.length == 1 || ["case", "cases", "otherwise", "this", "true", "type"].elem s
      then `(stx| &$i:str) else `(stx| $i:str)

  let seq (ws: List String) : MacroM (TSyntax `stx) := do
    match ← (ws.toArray.mapM mk_stx) with
      | #[ l ] => pure l
      | ls => `(stx| atomic( $[$ls:stx]* ) )

  let items (k: TSyntax `str): MacroM (List (TSyntax `stx)) := do
      let ws := k.getString.splitOn " "
      if ws[0]!.front.isLower then
        pure [← seq ws, ← seq (ws[0]!.capitalize :: ws.drop 1)]
      else pure [← seq ws]

  let all ← ks.getElems.toList.flatMapM items
  let stx ← mk_or all
  `(syntax $name := ($stx:stx))

declare_syntax_cat sdef_decl
syntax "|" (":" num)? stx+ : sdef_decl

def elab_decl (name: Ident) : TSyntax `sdef_decl → CommandElabM Unit
  | `(sdef_decl| | $[: $prec:num]? $[$args:stx]*) => do
      let command ← `(syntax $[: $prec:num]? $[$args:stx]* : $name)
      elabCommand command
  | _ => throwError "unknown sdef_decl"

elab "sdef" name:ident decls:sdef_decl+ : command => do
  elabCommand (← `(declare_syntax_cat $name))
  decls.forM (elab_decl name)

elab "sdef_extend" name:ident decls:sdef_decl+ : command => do
  decls.forM (elab_decl name)

-- tactics

def rapply (goal : MVarId) (e : Expr) : MetaM (List MVarId) := do
  goal.checkNotAssigned `myApply
  goal.withContext do
    let target ← goal.getType
    let type ← inferType e
    let (args, _, conclusion) ← forallMetaTelescopeReducing type
    let extra ← if ← isDefEq target conclusion then do
      goal.assign (mkAppN e args)
      pure []
    else match conclusion.getAppFnArgs with
      | (`Or, #[p, q]) =>
          if ← isDefEq target q then do
            let not_p ← mkFreshExprMVar (Lean.mkNot p) MetavarKind.syntheticOpaque
            goal.assign (← mkAppM `Or.resolve_left #[mkAppN e args, not_p])
            pure [not_p]
          else throwTacticEx `rapply goal "could not resolve"
      | _ => throwTacticEx `rapply goal m!"{e} is not applicable to goal with target {target}"

    let unassigned (var: MVarId) : MetaM Bool := do
      let a ← var.isAssignedOrDelayedAssigned
      pure (! a)
    let newGoals ← ((args ++ extra).map Expr.mvarId!).filterM unassigned
    return newGoals.toList

elab "rapply" e:term : tactic => do
  let e ← Term.elabTerm e none
  Tactic.liftMetaTactic (rapply · e)
