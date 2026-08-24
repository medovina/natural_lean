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

sdef eq_prop
  |:50 expr:51 eq_op expr:51

kdef _if = "if"

sdef _iff
  | "iff" <|> ("if" "and" "only" "if")

kdef _for = "for"

kdef _exists = "exist" | "exists" | "is"

kdef _at_least = "at least"
kdef _at_most = "at most"
kdef _exactly = "exactly"

sdef multi_specifier
  | _at_least
  | _at_most
  | _exactly

sdef multi_or
  | multi_specifier "one" "of" eq_prop,+ "is" &"true"

kdef _either = "either"

sdef_extend prop
  | eq_prop
  |:35 prop:36 "and" prop:35
  |:30 prop:31 "or" prop:30
  |:25 prop:26 "implies" prop:25
  | "if" prop "then" prop
  |:20 prop:21 _iff prop:21
  | _for "all" ident,+ ":" ident "," prop
  | prop _for "all" ident,+ ":" ident
  | "there" _exists "some" ? ident,+ ":" ident "such" "that" prop
  | prop _for "some" ident,+ ":" ident
  | _either prop "," "or" prop
  | multi_or

-- reason

sdef _thm
  | "Lemma" <|> "Theorem" <|> ":"

sdef reason
  | "[" tactic "]"
  | sepBy1(_thm ident, "and")
  | "induction"
  | "the" "inductive" "hypothesis"

-- assert_prop

sdef eq_expr_by
  | "=" expr ("by" reason)?

sdef assert_prop
  | prop
  | atomic(expr eq_expr_by eq_expr_by+)

kdef _so = "but" | "hence" | "so" | "that is" | "then" | "therefore" | "thus"

kdef _have =
  "clearly" | "it follows that" |
  "we have shown that" | "we have" | "we know that" | "we must have"

kdef _by = "by"

sdef which_is_contradiction
  | atomic("," "again"? "contradicting") _thm ident

sdef proof_prop
  | (_by reason)? _have ? assert_prop ("by" reason)? which_is_contradiction ?

kdef _let = "let"

kdef _also = "also"

kdef _assume1 = "assume" | "suppose"

sdef _assume
  | _also ? _assume1 "that"?

sdef let_or_assume
  | _let ident,+ ":" ident
  | _let ident "=" expr
  | _assume prop

kdef _now = "now" | "second"

sdef proof_if_prop
  | _if prop ","? "then" sepBy1(proof_prop, "/", "," _so)

kdef will_show =
  "we must show that" | "we will now prove that" | "we will prove that"

kdef _otherwise = "otherwise"

kdef _any_case = "in all cases" | "in any case" | "in either case"

kdef have_contradiction = "this is a contradiction"

sdef assert_step
  | proof_if_prop
  | will_show prop
  | _so ? proof_prop
  | have_contradiction

sdef clause_intro
  | ("First" <|> _now) ","?

sdef and_or_so
  | ("and" _so) <|> _so

sdef proof_sentence1
  | sepBy1(let_or_assume, "/", "," ? "and")
  | sepBy1(assert_step, "/", "," and_or_so)

sdef proof_sentence
  | clause_intro ? proof_sentence1 "."

sdef proof_unit
  | atomic(_assume prop "." proof_unit+ _otherwise) proof_unit+ _any_case prop "."
  | proof_sentence

syntax case := "Case" num ":" prop "." proof_unit+

sdef case_unit
  | case+ _any_case prop "."
  | proof_unit

-- proof

sdef proof
  | case_unit+
  | "By" reason "."

-- theorem

sdef _theorem
  | _thm ident str ? "." prop "." ("Proof." proof)?
