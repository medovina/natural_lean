import Natural.Util

sdef const
  | ident
  | num

sdef type
  | ident
  | type "→" type

sdef ids_type
  | ident,+ ":" type

kdef _at_least = "at least"
kdef _at_most = "at most"
kdef _exactly = "exactly"

sdef multi_specifier
  | _at_least
  | _at_most
  | _exactly

-- forward declaration
declare_syntax_cat prop

-- expr

declare_syntax_cat expr
syntax num : expr
syntax ident : expr
syntax:80 (priority := 1) expr:80 expr:81 : expr
syntax:70 expr:70 "·" expr:71 : expr
syntax:65 expr:65 "+" expr:66 : expr
syntax (priority := 2) expr "(" expr ")" : expr
syntax "(" expr ")" : expr
syntax "{" ident ":" ident "|" prop "}" : expr

-- prop

kdef rel_op = "=" | "≠" | "<" | "≮" | "≤" | ">" | "≯" | "≥" | "∈"

sdef rel_prop
  | expr (rel_op expr)+

kdef _if = "if"

sdef _iff
  | "iff" <|> ("if" "and" "only" "if")

kdef _for = "for"

syntax _for_all := _for "all"

kdef _there = "there"

kdef _exists = "exist" | "exists" | "is"

sdef multi_or
  | multi_specifier "one" "of" rel_prop,+ "is" &"true"

kdef _either = "either"

syntax some_or_no := "some" <|> "no"

kdef _is_have = "this is" | "we have"

syntax have_contradiction := _is_have &"a" "contradiction"

sdef_extend prop
  | atomic(rel_prop)
  |:35 prop:36 "and" prop:35
  |:30 prop:31 "or" prop:30
  |:25 prop:26 "implies" prop:25
  | _if prop "then" prop
  |:20 prop:21 _iff prop:21
  | _for_all ids_type "," prop
  | prop _for_all ids_type
  | _there _exists some_or_no ? ids_type "such" "that" prop
  | prop _for "some" ids_type
  | _either prop "," "or" prop
  | multi_or
  | have_contradiction

-- proof steps

sdef _thm
  | "Lemma" <|> "Theorem"

sdef reason
  | "[" tactic "]"
  | sepBy1(ident, "and")
  | "induction"
  | "the" "inductive" "hypothesis"

sdef eq_expr_by
  | "=" expr ("by" reason)?

declare_syntax_cat assert_prop
syntax (priority := 1) prop : assert_prop
syntax (priority := 2) atomic(expr eq_expr_by eq_expr_by+) : assert_prop

kdef _so = "but" | "hence" | "so" | "that is" | "then" | "therefore" | "thus"

kdef _have =
  "clearly" | "it follows that" |
  "we have shown that" | "we have" | "we know that" | "we must have"

kdef _since = "since"

syntax because_prop := _since prop

kdef _by = "by"

sdef which_is_contradiction
  | atomic("," "again"? "contradicting") ident because_prop ?

sdef proof_prop
  | because_prop ? (_by reason)? _have ? assert_prop
    ("by" reason)? which_is_contradiction ?

kdef _let = "let"

kdef _also = "also"

kdef _assume1 = "assume" | "suppose"

sdef _assume
  | _also ? _assume1 "that"?

syntax let_step := _let ident,+ ":" ident

sdef let_or_assume
  | let_step
  | _let ident "=" expr
  | _assume prop

sdef proof_if_prop
  | _if prop ","? "then" sepBy1(proof_prop, "/", "," _so)

kdef will_show =
  "we must show that" | "we will now prove that" | "we will prove that"

kdef _otherwise = "otherwise"

kdef _any_case = "in all cases" | "in any case" | "in either case"

declare_syntax_cat assert_step
syntax (priority := 1) _so ? proof_prop : assert_step
syntax (priority := 2) proof_if_prop : assert_step
syntax will_show prop : assert_step

sdef clause_intro
  | ("First" <|> "Now" <|> "Second") ","?

sdef and_or_so
  | ("and" _so) <|> _so

sdef proof_sentence1
  | sepBy1(let_or_assume, "/", "," ? "and")
  | sepBy1(assert_step, "/", "," and_or_so)

sdef proof_sentence
  | clause_intro ? proof_sentence1 "."

declare_syntax_cat proof_unit

sdef otherwise_intro
  | _assume prop "." proof_unit+
  | proof_if_prop "."

syntax otherwise_unit :=
  atomic(otherwise_intro _otherwise) proof_unit+ _any_case prop "."

sdef_extend proof_unit
  | otherwise_unit
  | proof_sentence

syntax case := "Case" num ":" prop "." proof_unit+

sdef case_unit
  | case+ _any_case prop "."
  | proof_unit

-- proofs

sdef proof
  | case_unit+
  | "By" reason "."

syntax proof_item := ident "." proof

syntax proof_items := proof_item+

-- definitions

syntax constructor := const ":" type

syntax type_def :=
  "The" &"type" ident "is" "defined" "inductively"
  "with" "constructors" sepBy1(constructor, "and") "."

syntax top_sentence := prop "." ("[" ident (":" "@" ident)? "]")?

syntax prop_item := ident "." top_sentence

kdef binary_op = "+" | "*" | "<"

syntax cases_def :=
  "The" "binary" "operation" binary_op "on" ident
  "is" "defined" "recursively" "such" "that" "for" "all" ids_type ","
  prop_item+

syntax direct_def :=
  _for_all ids_type "," prop "."

sdef definition
  | type_def
  | cases_def
  | direct_def

syntax definition_stmt := "Definition." definition

-- theorems

sdef props_proofs
  | top_sentence ("Proof." proof)?
  | prop_item+ ("Proof." proof_items)?

sdef _theorem
  | _thm ident ? str ? "." (let_step ".")? props_proofs
