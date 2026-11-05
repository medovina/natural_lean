module

import Lean
public meta import Natural.Decl
public import Natural.Grammar

open Lean
open Lean.Elab.Command

namespace Natural

elab t:top : command => do
  try
    -- Open the Classical namespace because elaborating if/then/else expressions
    -- requires propositions to be decidable.  We don't want to make the user
    -- explicitly open Classical for this purpose since these expressions would not
    -- necessarily require the Axiom of Choice in e.g. ZFC set theory.
    pushScope
    elabCommand (← `(open Classical))

    let cs : List Command ← liftTermElabM $ match t with
      | `(top| Notation . $n:notation_decl) => of_notation_decl n
      | `(top| $d:thm_or_def $[Corollary $ts:_theorem]*) => do
          let (commands, names, is_thm) ← of_thm_or_def d
          let commands ← commands.mapM (final_elab_command ·)
          let corrs ← List.map (·.1) <$> ts.toList.mapM (fun c => withRef c.raw do
            if is_thm && names == []
              then throwError "unnamed theorem may not have a corollary"
              else of_theorem names c)
          pure $ commands ++ corrs.flatten
      | _ => throwError "unknown top"
    let c : Command := TSyntax.mk (mkNullNode cs.toArray)
    elabCommand c

    -- We trace only after elaborating because some commands could have syntax
    -- that is defined in previous commands in the same group.
    let ctrace cmd := do
      trace[natural] cmd
      pure ()
    cs.forM ctrace

  finally
    popScope
