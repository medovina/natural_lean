declare_syntax_cat expr
declare_syntax_cat prop

-- expr

syntax num : expr
syntax ident : expr

syntax:65 expr:65 "+" expr:66 : expr

syntax expr "(" expr ")" : expr
syntax "(" expr ")" : expr
syntax "{" ident ":" ident "|" prop "}" : expr

-- prop

declare_syntax_cat eq_op
syntax ("=" <|> "≠" <|>
        "<" <|> "≮" <|> "≤" <|>
        ">" <|> "≯" <|> "≥" <|>
        "∈") : eq_op

syntax:50 expr:51 eq_op expr:51 : prop

syntax:35 prop:36 "and" prop:35 : prop

syntax:30 prop:31 "or" prop:30 : prop

syntax:25 prop:26 "implies" prop:25 : prop

syntax "if" prop "then" prop : prop

declare_syntax_cat _iff
syntax ("iff" <|> ("if" "and" "only" "if")): _iff

syntax:20 prop:21 _iff prop:21 : prop

declare_syntax_cat _for
syntax ("for" <|> "For") : _for

syntax _for "all" ident,+ ":" ident "," prop : prop
syntax prop _for "all" ident,+ ":" ident : prop

syntax "there" "exists" "some" Lean.binderIdent ":" ident "such" "that" prop : prop

-- reason

declare_syntax_cat reason
syntax "[" tactic "]" : reason
syntax ":" ident : reason
syntax "induction" : reason

-- assert_prop

declare_syntax_cat eq_expr_by
syntax "=" expr ("by" reason)? : eq_expr_by

declare_syntax_cat assert_prop
syntax ("by" reason)? prop : assert_prop
syntax expr eq_expr_by eq_expr_by+ : assert_prop

-- proof_step

declare_syntax_cat _let
syntax ("let" <|> "Let") : _let

declare_syntax_cat _assume
syntax ("assume" <|> "suppose") "that"? : _assume

declare_syntax_cat proof_step

syntax assert_prop : proof_step
syntax _assume prop : proof_step
syntax _let ident,+ ":" ident : proof_step
syntax _let ident "=" expr : proof_step
syntax "We" "have" "shown" "that" prop : proof_step
syntax "We" "must" "show" "that" prop : proof_step

-- proof_step1

declare_syntax_cat initial

syntax ("Clearly" <|> "First" <|> "Hence" <|> "Now" <|>
        "Second" <|> "So" <|> "Then" <|> "Thus") ","? : initial

declare_syntax_cat step_sep
syntax ","? ("and" <|> "so") : step_sep

declare_syntax_cat proof_step1

syntax initial ? sepBy1(proof_step, "/", step_sep) "." : proof_step1

-- proof

declare_syntax_cat proof

syntax proof_step1+ : proof
syntax "By" "induction" "." : proof

-- theorem

declare_syntax_cat _thm

syntax ("Lemma" <|> "Theorem") : _thm

declare_syntax_cat _theorem

syntax _thm ident str ? "." prop "." ("Proof." proof)? : _theorem
