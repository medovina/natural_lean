import Lean

open Lean
open Lean.Elab.Command

elab "kdef" name:ident "=" ks:sepBy1(str, "|") : command => do
  elabCommand (← `(declare_syntax_cat $name))

  let rec mk_stx : List (TSyntax `str) → CommandElabM (TSyntax `stx)
    | [] => panic! "no strings"
    | [k] => `(stx| $k:str)
    | k :: ks => do `(stx| $k:str <|> $(← mk_stx ks))
  let all := ks.getElems.toList.flatMap (fun k =>
      let s := k.getString
      if s.front.isLower then [k, Lean.Syntax.mkStrLit (k.getString.capitalize)] else [k])
  let stx ← mk_stx all
  let c ← `(syntax ($stx) : $name)
  elabCommand c
  pure ()

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
