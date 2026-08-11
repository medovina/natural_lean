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

sdef eq_op
  | ("=" <|> "≠" <|>
     "<" <|> "≮" <|> "≤" <|> ">" <|> "≯" <|> "≥" <|>
     "∈")

sdef _iff
  | ("iff" <|> ("if" "and" "only" "if"))

sdef _for
  | ("for" <|> "For")

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
 | ("by" reason)? prop
 | expr eq_expr_by eq_expr_by+

-- proof_step

sdef _let
  | ("let" <|> "Let")

sdef _assume
  | ("assume" <|> "suppose") "that"?

sdef proof_step
  | assert_prop
  | _assume prop
  | _let ident,+ ":" ident
  | _let ident "=" expr
  | "We" "have" "shown" "that" prop
  | "We" "must" "show" "that" prop

-- proof_step1

sdef initial
  | ("Clearly" <|> "First" <|> "Hence" <|> "Now" <|>
     "Second" <|> "So" <|> "Then" <|> "Thus") ","?

sdef step_sep
  | ","? ("and" <|> "so")

sdef proof_step1
  | initial ? sepBy1(proof_step, "/", step_sep) "."

-- proof

sdef proof
  | proof_step1+
  | "By" "induction" "."

-- theorem

sdef _thm
  | ("Lemma" <|> "Theorem")

sdef _theorem
  | _thm ident str ? "." prop "." ("Proof." proof)?
