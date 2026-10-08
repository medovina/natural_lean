import Lean
import Batteries.Data.List.Basic

open Lean hiding mkStrLit
open Lean.Parser hiding mkIdent
open Lean.Parser.Term (bracketedBinder)
open Lean.Syntax
open Elab Tactic Meta
open Elab.Command

infix:50 "≮" => fun x y => ¬(x < y)
infix:50 "≯" => fun x y => ¬(x > y)
infix:50 "≉" => fun x y => ¬(x ≈ y)

-- from Mathlib
theorem Or.elim3 {c d : Prop} (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
  Or.elim h ha fun h₂ ↦ Or.elim h₂ hb hc

-- options

def Option.anyM [Monad m] (f: α → m Bool) (x: Option α) : m Bool :=
  x.toList.anyM f

namespace Natural

-- pairs

def map_fst (f : α → γ) (pairs : List (α × β)) :=
  pairs.map (fun (x, y) => (f x, y))

def map_snd (f : β → γ) (pairs : List (α × β)) :=
  pairs.map (fun (x, y) => (x, f y))

def mapM_fst [Monad m] (f: α → m γ) (pairs : List (α × β)) :=
  pairs.mapM (fun (x, y) => do pure (← f x, y))

def mapM_snd [Monad m] (f: β → m γ) (pairs : List (α × β)) :=
  pairs.mapM (fun (x, y) => do pure (x, ← f y))

def mapM_pair {α : Type u} {β : Type v} [Monad m] (f : α → m β) : α × α → m (β × β)
  | (x, y) => (·,·) <$> f x <*> f y

def pairM [Monad m] (x: m α) (y: m β) := Prod.mk <$> x <*> y

-- lists

def zipWith3M [Applicative m] (f: α → β → γ → m δ) :
  List α → List β → List γ → m (List δ)
  | x :: xs, y :: ys, z :: zs => (· :: ·) <$> f x y z <*> zipWith3M f xs ys zs
  | _, _, _ => pure []

def unzip3 (l: List (α × β × γ)) : (List α × List β × List γ) :=
  let (xs, yzs) := l.unzip
  let (ys, zs) := yzs.unzip
  (xs, ys, zs)

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

def is_super_letter (s: String) :=
  match s.toList with
    | [c] => (super_letters.lookup c).isSome
    | _ => false

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

def as_ident : Term → Option Ident
  | `($i:ident) => .some i
  | _ => .none

def as_ident! (t: Term): Ident := (as_ident t).get!

def as_term (t: TSyntax α): Term := ⟨t.raw⟩

def id_append (id: Ident) (name: Name) := mkIdent (id.getId ++ name)

def opt_and : Option Term → Option Term → CoreM Term
  | none, some p => pure p
  | some p, none => pure p
  | some p, some q => `($p ∧ $q)
  | _, _ => throwError "opt_and: no term"

inductive OpKind
  | infix
  | prefix
  | postfix
deriving BEq, Inhabited

instance: ToString OpKind where
  toString
    | .infix => "infix"
    | .prefix => "prefix"
    | .postfix => "postfix"

syntax op_kind := "infix" <|> "prefix" <|> "postfix"

def of_op_kind : TSyntax ``op_kind → OpKind
  | `(op_kind| infix) => .infix
  | `(op_kind| prefix) => .prefix
  | `(op_kind| postfix) => .postfix
  | _ => panic! "unknown op_kind"

def parse_op_opt : Syntax → Option (OpKind × String × List Syntax)
  | .node _ _ a => match a with
    | #[x, .atom _ op, y] => .some (.infix, op, [x, y])
    | #[.atom _ op, x] => .some (.prefix, op, [x])
    | #[x, .atom _ op] => .some (.postfix, op, [x])
    | _ => .none
  | _ => .none

def parse_op (t: Term): CoreM (String × OpKind × List Term) :=
  match parse_op_opt t.raw with
    | .some (kind, op, args) => pure (op, kind, args.map (⟨·⟩))
    | .none => throwError "infix expression expected"

def sourceInfo (t: Term) := t.raw.getInfo?.getD .none

def apply_op (ns: Name) : OpKind → String → List Term → Term
  | .infix, op, [t, u] =>
    let info := match t.raw.getPos?, u.raw.getTailPos? with
      | .some startPos, .some endPos => SourceInfo.synthetic startPos endPos
      | _, _ => SourceInfo.none
    ⟨Syntax.node info (ns ++ .mkSimple s!"term_{op}_") #[t, mkAtom op, u]⟩
  | .prefix, op, [t] =>
    ⟨Syntax.node (sourceInfo t) (ns ++ .mkSimple s!"term{op}_") #[mkAtom op, t]⟩
  | .postfix, op, [t] =>
    ⟨Syntax.node (sourceInfo t) (ns ++ .mkSimple s!"term_{op}") #[t, mkAtom op]⟩
  | _, _, _ => panic! "apply_op"

partial def syntax_replace_op (op: String) (name: Ident) :=
  let rec repl (t: Syntax): Syntax :=
    let recurse (t: Syntax): Syntax := match t with
      | .node i k args => .node i k (args.map repl)
      | t => t
    match parse_op_opt t with
      | .some (_kind, op', args) =>
          if op == op' then
            let args := args.toArray.map (⟨·⟩)
            (mkApp name args).raw
          else recurse t
      | _ => recurse t
  repl

def replace_op (op: String) (name: Ident) (t: Term) : Term :=
  ⟨syntax_replace_op op name t.raw⟩

def binders (xs: List (Ident × Term)) : CoreM (Array (TSyntax ``bracketedBinder)) :=
  xs.toArray.mapM (fun | (x, t) => `(bracketedBinder| ($x : $t)))

def ex_binders (xs: List (Ident × Term)) : CoreM (Array (TSyntax ``bracketedExplicitBinders)) :=
  xs.toArray.mapM (fun | (x, t) => `(bracketedExplicitBinders| ($x:ident : $t)))

inductive BinderType
  | all
  | exists
deriving BEq

abbrev BinderOp := String

abbrev Vars := List (Name × BinderOp × Term)
abbrev IdVars := List (Ident × BinderOp × Term)

def of_bracketed_binder : TSyntax ``bracketedBinder → Ident × BinderOp × Term
  | `(bracketedBinder| ($x:ident : $t)) => (x, ":", t)
  | _ => panic! "of_bracketed_binder"

def of_bracketed_ex_binder : TSyntax ``bracketedExplicitBinders → Ident × BinderOp × Term
  | `(bracketedExplicitBinders| ($x:ident : $t)) => (x, ":", t)
  | _ => panic! "of_ex_bracketed_binder"

def match_binder (s: Syntax) : Option (BinderType × IdVars × Term) :=
  match s with
    | `(∀ $xs:ident* : $type, $t) =>
        .some (.all, xs.toList.map (·, ":", type), t)
    | `(∀ $xs:bracketedBinder*, $t) =>
        .some (.all, xs.toList.map of_bracketed_binder, t)
    | `(∀ $x:ident ∈ $s, $t) => .some (.all, [(x, "∈", s)], t)
    | `(∃ $[$xs:ident]* : $type, $t) =>
        .some (.exists, xs.toList.map (·, ":", type), t)
    | `(∃ $xs:bracketedExplicitBinders*, $t) =>
        .some (.exists, xs.toList.map of_bracketed_ex_binder, t)
    | `(∃ $x:ident ∈ $s, $t) => .some (.exists, [(x, "∈", s)], t)
    | _ => .none

partial def match_binders (s: Syntax): Option (BinderType × IdVars × Term) :=
  let m := match_binder s
  match m with
    | .none => none
    | .some (b, vars, t) =>
        match match_binders t with
          | .none => m
          | .some (b', vars', t') =>
              if b == b' then .some (b, vars ++ vars', t')
              else m

def mk_for_all (vars: IdVars) (t: Term) : CoreM Term :=
  vars.foldrM (fun
    | (x, ":", t), a => `(∀ $x : $t, $a)
    | (x, "∈", t), a => `(∀ $x:ident ∈ $t, $a)
    | _, _ => throwError "mk_for_all: unknown op") t

def mk_exists (vars: IdVars) (t: Term) : CoreM Term :=
  vars.foldrM (fun
    | (x, ":", t), a => `(∃ $x:ident : $t, $a)
    | (x, "∈", t), a => `(∃ $x:ident ∈ $t, $a)
    | _, _ => throwError "mk_for_all: unknown op") t

def mk_binder (bt: BinderType) (xs: IdVars) (t: Term)
    : CoreM Term :=
  match bt with
    | .all => mk_for_all xs t
    | .exists => mk_exists xs t

def for_all (xs: Vars) (t: Term) : CoreM Term :=
  if xs == [] then pure t else mk_for_all (map_fst mkIdent xs) t

def bound_vars (t: Term): Vars := match match_binders t with
  | .some (_, vars, _) => map_fst (·.getId) vars
  | .none => []

-- syntax builders

def non_keywords :=
  ["because", "case", "cases", "least", "now",
   "otherwise", "some", "this", "true", "type"]

macro "kdef" name:ident "=" ks:sepBy1(str, "|") : command => do
  let rec mk_or : List (TSyntax `stx) → MacroM (TSyntax `stx)
    | [] => panic! "empty"
    | [x] => pure x
    | x :: xs => do `(stx| $x <|> $(← mk_or xs))

  let mk_stx (s: String) : MacroM (TSyntax `stx) :=
    let i := mkStrLit s
    if s.front.isAlpha && (s.length == 1 || non_keywords.elem s)
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
syntax "|" (":" num)? (atomic("(" "priority") ":=" num ")")? stx+ : sdef_decl

def elab_decl (name: Ident) : TSyntax `sdef_decl → CommandElabM Unit
  | `(sdef_decl| | $[: $prec:num]? $[(priority := $prio)]? $[$args:stx]*) => do
      let command ←
        `(syntax $[: $prec:num]? $[(priority := $prio)]? $[$args:stx]* : $name)
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

-- natural language

def singular (s: String) : String :=
  if s.back == 's' then (s.dropEnd 1).toString else s

inductive Category
  | noun
  | verb
  | adjective
deriving Inhabited

syntax category := &"noun" <|> &"verb" <|> &"adjective"

def of_category : TSyntax ``category → Category
  | `(category| noun) => .noun
  | `(category| verb) => .verb
  | `(category| adjective) => .adjective
  | _ => panic! "of_category"

def to_category: Category → CoreM (TSyntax ``category)
  | .noun => `(category| noun)
  | .verb => `(category| verb)
  | .adjective => `(category| adjective)

end Natural
