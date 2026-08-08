declare_syntax_cat expr
declare_syntax_cat prop

-- expr

syntax num : expr
syntax ident : expr
syntax expr "+" expr : expr
syntax expr "(" expr ")" : expr
syntax "(" expr ")" : expr
syntax "{" ident ":" ident "|" prop "}" : expr

-- prop

declare_syntax_cat _for
syntax ("for" <|> "For") : _for

syntax expr "=" expr : prop
syntax expr "≠" expr : prop
syntax expr "∈" expr : prop
syntax prop ("or" <|> "implies") prop : prop
syntax _for "all" ident,+ ":" ident "," prop : prop
syntax prop _for "all" ident,+ ":" ident : prop
syntax "there" "exists" "some" ident ":" ident "such" "that" prop : prop

-- reason

declare_syntax_cat reason
syntax "[" tactic "]" : reason
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

declare_syntax_cat proof_step

syntax assert_prop : proof_step
syntax "assume" prop : proof_step
syntax _let ident,+ ":" ident : proof_step
syntax _let ident "=" expr : proof_step
syntax "We" "have" "shown" "that" prop : proof_step
syntax "We" "must" "show" "that" prop : proof_step

-- proof_step1

declare_syntax_cat initial

syntax ("First," <|> "Hence" <|> "Now," <|> "Second," <|> "Then" <|> "Thus") : initial

declare_syntax_cat proof_step1

syntax initial ? sepBy1(proof_step, "and") "." : proof_step1

-- proof

declare_syntax_cat proof

syntax proof_step1+ : proof
syntax "By" "induction" "." : proof
