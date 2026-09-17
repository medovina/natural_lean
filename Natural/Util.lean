import Lean
import Batteries.Data.List.Basic

open Lean hiding mkStrLit
open Lean.Parser hiding mkIdent
open Elab Tactic Meta
open Elab.Command
open Lean.Syntax

infix:50 "≮" => fun x y => ¬(x < y)
infix:50 "≯" => fun x y => ¬(x > y)

namespace Natural

-- pairs

def map_fst (f : α → γ) (pair : Prod α β) := pair.map f id
def map_snd (f : β → γ) (pair : Prod α β) := pair.map id f
def map_pair (f : α → β) (pair : Prod α α) := pair.map f f

def mapM_fst [Monad m] (f : α → m γ) : α × β → m (γ × β)
  | (x, y) => do pure (← f x, y)

def mapM_snd [Monad m] (f : β → m γ) : α × β → m (α × γ)
  | (x, y) => do pure (x, ← f y)

def mapM_pair {α : Type u} {β : Type v} [Monad m] (f : α → m β) : α × α → m (β × β)
  | (x, y) => (·,·) <$> f x <*> f y

def pairM [Monad m] (x: m α) (y: m β) := Prod.mk <$> x <*> y

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

-- arrays

-- erase repeated elements, keeping the first element of each run
def _root_.Array.eraseRepsBy {α} (r : α → α → Bool) (as : Array α) : Array α :=
  if h : 0 < as.size then
    let ⟨last, acc⟩ := as.foldl (init := (as[0], #[])) fun ⟨last, acc⟩ a =>
      if r a last then ⟨last, acc⟩ else ⟨a, acc.push last⟩
    acc.push last
  else #[]

-- unicode

-- The Unicode superscript characters '⁰' ... '⁹' are not contiguous!
def super_digits := [('⁰', '0'), ('¹', '1'), ('²', '2'), ('³', '3'), ('⁴', '4'),
                    ('⁵', '5'), ('⁶', '6'), ('⁷', '7'), ('⁸', '8'), ('⁹', '9')]

-- The Unicode superscript characters 'ᵃ' ... 'ᶻ' are also not contiguous!
def super_letters :=
  [('ᵃ', 'a'), ('ᵇ', 'b'), ('ᶜ', 'c'), ('ᵈ', 'd'), ('ᵉ', 'e'), ('ᶠ', 'f'),
   ('ᵍ', 'g'), ('ʰ', 'h'), ('ⁱ', 'i'), ('ʲ', 'j'), ('ᵏ', 'k'), ('ˡ', 'l'),
   ('ᵐ', 'm'), ('ⁿ', 'n'), ('ᵒ', 'o'), ('ᵖ', 'p'), ('𐞥', 'q'), ('ʳ', 'r'),
   ('ˢ', 's'), ('ᵗ', 't'), ('ᵘ', 'u'), ('ᵛ', 'v'), ('ʷ', 'w'), ('ˣ', 'x'),
   ('ʸ', 'y'), ('ᶻ', 'z')]

-- English

def singular (s: String) : String :=
  if s.back == 's' then (s.dropEnd 1).toString else s

-- parsing

-- A parser for numeric literals consisting only of digits.  We need this
-- so that we can parse syntax such as "Let x = 5.", where the built-in parser
-- would parse "5." as a scientific literal, which we don't want.
-- Thanks to Robin Arnez for providing this implementation on the Lean Zulip.
def rawNumLitNoAntiquot : Parser where
  fn c s :=
    let startPos := s.pos
    -- delegate to `numLitFn` for appropriate error messages
    if h : c.atEnd startPos then numLitFn c s else
    if !(c.get' startPos h).isDigit then numLitFn c s else
    let s := takeWhileFn (·.isDigit) c (s.next' c startPos h)
    mkNodeToken numLitKind startPos true c s

attribute [combinator_formatter rawNumLitNoAntiquot] PrettyPrinter.Formatter.numLit.formatter
attribute [combinator_parenthesizer rawNumLitNoAntiquot] PrettyPrinter.Parenthesizer.numLit.parenthesizer

@[run_parser_attribute_hooks]
def nat : Parser :=
  withAntiquot (mkAntiquot "num" numLitKind) rawNumLitNoAntiquot

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

def match_binder : Syntax → Option (BinderType × List Name × Term × Term)
  | `(∀ $xs:ident* : $type, $t) => .some (.all, xs.toList.map TSyntax.getId, type, t)
  | `(∃ $[$xs:ident]* : $type, $t) => .some (.exists, xs.toList.map TSyntax.getId, type, t)
  | _ => .none

def mk_binder (bt: BinderType) (xs: List Name) (type: Term) (t: Term) : CoreM Term :=
  let xs := xs.toArray.map mkIdent
  match bt with
    | .all => `(∀ $xs* : $type, $t)
    | .exists => `(∃ $[$xs:ident]* : $type, $t)

-- syntax builders

def non_keywords :=
  ["because", "case", "cases", "now", "otherwise", "some", "this", "true", "type"]

macro "kdef" name:ident "=" ks:sepBy1(str, "|") : command => do
  let rec mk_or : List (TSyntax `stx) → MacroM (TSyntax `stx)
    | [] => panic! "empty"
    | [x] => pure x
    | x :: xs => do `(stx| $x <|> $(← mk_or xs))

  let mk_stx (s: String) : MacroM (TSyntax `stx) :=
    let i := mkStrLit s
    if s.length == 1 || non_keywords.elem s
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

end Natural

-- from Mathlib
theorem Or.elim3 {c d : Prop} (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
  Or.elim h ha fun h₂ ↦ Or.elim h₂ hb hc
