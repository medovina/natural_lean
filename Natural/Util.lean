import Lean

import Batteries.Data.List.Basic
open Lean hiding mkStrLit
open Elab Tactic Meta
open Elab.Command
open Lean.Syntax (mkStrLit)

def overlap [BEq α] (xs: List α) (ys: List α): Bool := xs.inter ys != []

elab "kdef" name:ident "=" ks:sepBy1(str, "|") : command => do
  elabCommand (← `(declare_syntax_cat $name))

  let rec mk_or : List (TSyntax `stx) → CommandElabM (TSyntax `stx)
    | [] => panic! "empty"
    | [x] => pure x
    | x :: xs => do `(stx| $x <|> $(← mk_or xs))

  let seq (ws: List String) : CommandElabM (TSyntax `stx) :=
    match (ws.map mkStrLit).toArray with
      | #[ l ] => `(stx| $l:str)
      | ls => `(stx| atomic( $[$ls:str]* ) )

  let items (k: TSyntax `str): CommandElabM (List (TSyntax `stx)) := do
      let ws := k.getString.splitOn " "
      if ws[0]!.front.isLower then
        pure [← seq ws, ← seq (ws[0]!.capitalize :: ws.drop 1)]
      else pure [← seq ws]

  let all ← ks.getElems.toList.flatMapM items
  let stx ← mk_or all
  let c ← `(syntax ($stx:stx) : $name)
  elabCommand c

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
