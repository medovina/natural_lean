import Natural.Util

-- forward declaration
declare_syntax_cat prop

-- expr
sdef expr
  | num
  | ident
  |:65 expr:65 "+" expr:66
  | expr "(" expr ")"
  | "(" expr ")"
  | "{" ident ":" ident "|" prop "}"

-- prop

kdef eq_op = "=" | "≠" | "<" | "≮" | "≤" | ">" | "≯" | "≥" | "∈"

sdef _iff
  | "iff" <|> ("if" "and" "only" "if")

kdef _for = "for"

sdef_extend prop
  |:50 expr:51 eq_op expr:51
  |:35 prop:36 "and" prop:35
  |:30 prop:31 "or" prop:30
  |:25 prop:26 "implies" prop:25
  | "if" prop "then" prop
  | :20 prop:21 _iff prop:21
  | _for "all" ident,+ ":" ident "," prop
  | prop _for "all" ident,+ ":" ident

syntax "there" "exists" "some" Lean.binderIdent ":" ident "such" "that" prop : prop

-- reason

sdef reason
  | "[" tactic "]"
  | ":" ident
  | "induction"

-- assert_prop

sdef eq_expr_by
  | "=" expr ("by" reason)?

sdef assert_prop
  | prop
  | expr eq_expr_by eq_expr_by+

kdef _so = "hence" | "so" | "then" | "thus"

sdef _have
  | "Clearly" <|> ("We" "have" "shown" "that")

sdef proof_prop
  | ("by" reason)? _have ? assert_prop

kdef _let = "let"

sdef _assume
  | ("assume" <|> "suppose") "that"?

sdef let_or_assume
  | _let ident,+ ":" ident
  | _let ident "=" expr
  | _assume prop

kdef _now = "now" | "second"

sdef will_show
  | "We" "must" "show" "that"

sdef assert_step
  | will_show prop
  | _so ? proof_prop

sdef clause_intro
  | ("First" <|> _now) ","?

sdef proof_sentence1
  | sepBy1(let_or_assume, "/", "," ? "and")
  | sepBy1(assert_step, "/", "," _so)

sdef proof_sentence
  | clause_intro ? proof_sentence1 "."

-- proof

sdef proof
  | proof_sentence+
  | "By" "induction" "."

-- theorem

sdef _thm
  | "Lemma" <|> "Theorem"

sdef _theorem
  | _thm ident str ? "." prop "." ("Proof." proof)?
