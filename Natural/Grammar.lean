import Lean
import Natural.Init

open Lean
open Lean.Parser
open Lean.Parser.Term (attributes)

namespace Natural

sdef const
  | ident
  | num

syntax super_digit :=
  unicode("⁰", "^0") <|> unicode("¹", "^1") <|> unicode("²", "^2") <|> unicode("³", "^3") <|>
  unicode("⁴", "^4") <|> unicode("⁵", "^5") <|> unicode("⁶", "^6") <|> unicode("⁷", "^7") <|>
  unicode("⁸", "^8") <|> unicode("⁹", "^9")

syntax super_letter :=
  unicode("ᵃ", "^a") <|> unicode("ᵇ", "^b") <|> unicode("ᶜ", "^c") <|> unicode("ᵈ", "^d") <|>
  unicode("ᵉ", "^e") <|> unicode("ᶠ", "^f") <|> unicode("ᵍ", "^g") <|> unicode("ʰ", "^h") <|>
  unicode("ⁱ", "^i") <|> unicode("ʲ", "^j") <|> unicode("ᵏ", "^k") <|> unicode("ˡ", "^l") <|>
  unicode("ᵐ", "^m") <|> unicode("ⁿ", "^n") <|> unicode("ᵒ", "^o") <|> unicode("ᵖ", "^p") <|>
  unicode("𐞥", "^q") <|> unicode("ʳ", "^r") <|> unicode("ˢ", "^s") <|> unicode("ᵗ", "^t") <|>
  unicode("ᵘ", "^u") <|> unicode("ᵛ", "^v") <|> unicode("ʷ", "^w") <|> unicode("ˣ", "^x") <|>
  unicode("ʸ", "^y") <|> unicode("ᶻ", "^z")

syntax comma_ahead := lookahead("," <|> "and")

syntax id_list :=
  ident (atomic("," ident comma_ahead))* (atomic("," ? "and") ident)?

def filter_ident (f : String → Bool) (err: String): Parser :=
  atomic (ident >> checkStackTop (fun stx => stx.isIdOrAtom?.all f) err)

def var : Parser := filter_ident (fun s => s.length == 1) "expected var"
def non_var : Parser := filter_ident (fun s => s.length > 1) "expected non_var"

def singular_name : Ident → Option Ident → String
  | i, none => singular i.getId.toString
  | i, some j => s!"{i.getId.toString} {singular j.getId.toString}"

-- a simple name such as "integer"
syntax name1 := non_var
def mk_name1 : Parser := node ``name1 non_var

def lookup_name1 (env: Environment): Syntax → Option (Category × Name)
  | `(name1| $i:ident) =>
      (lookup_assoc_in_env env name_extension (singular_name i none))
  | _ => none

def check_name1 (c: Category) (env: Environment) (s: Syntax): Bool :=
  (lookup_name1 env s).any (·.1 == c)

def name1_of_cat (c: Category) : Parser :=
  atomic (mk_name1 >> checkStackTopEnv (check_name1 c) "unknown simple name")

-- a compound name such as "natural number"
syntax name2 := non_var non_var
def mk_name2 : Parser := node ``name2 (non_var >> non_var)

def lookup_name2 (env: Environment) (s: Syntax): Option (Category × Name) :=
  match s with
  | `(name2| $i:ident $j:ident) =>
      lookup_assoc_in_env env name_extension (singular_name i j)
  | _ => none

def check_name2 (c: Category) (env: Environment) (s: Syntax): Bool :=
  (lookup_name2 env s).any (·.1 == c)

def name2_of_cat (c: Category) : Parser :=
  atomic (mk_name2 >> checkStackTopEnv (check_name2 c) "unknown compound name")

def name_of_cat (c: Category): Parser := name1_of_cat c <|> name2_of_cat c

def _attribute := name_of_cat Category.attribute
def _property := name_of_cat Category.property
def _property_noun := name_of_cat Category.property_noun
def _comparative := name_of_cat Category.comparative
def _relation := name_of_cat Category.relation
def _type_name := name_of_cat Category.type
def _class := name_of_cat Category.class

syntax natural_attribute := _attribute
syntax natural_property := _property
syntax natural_property_noun := _property_noun
syntax natural_comparative := _comparative
syntax natural_relation := _relation
syntax natural_type_name := _type_name
syntax natural_class := _class

declare_syntax_cat natural_type (behavior := symbol)
syntax &"type" : natural_type
syntax "types" : natural_type
syntax natural_type_name ("of" natural_type)? : natural_type

syntax binder_op := ":" <|> "∈"

kdef _at_least = "at least"
kdef _at_most = "at most"
kdef _exactly = "exactly"

sdef multi_specifier
  | _at_least
  | _at_most
  | _exactly

syntax _a := &"a" <|> "an"

syntax a_or_some := _a <|> &"some"

syntax some_or_no := a_or_some <|> "no"

syntax opt_not := "not" ?

-- expr

sdef super_expr
  | super_digit+
  | super_letter+
  | super_expr "⁺" super_expr

declare_syntax_cat if_case
declare_syntax_cat prop

-- Mixfix notation declarations add syntax rules to these categories.
declare_syntax_cat mixfix_expr
declare_syntax_cat mixfix_prop

declare_syntax_cat expr (behavior := symbol)
syntax nat : expr
syntax id : expr
syntax "Prop" : expr
syntax:90 expr:91 "∘" expr:90 : expr
syntax:80 (name := super) expr:80 super_expr : expr
syntax:80 expr:81 "^" expr:80 : expr
syntax:75 (priority := 1) expr:75 noWs expr:76 : expr
syntax:75 "-" expr:75 : expr
syntax:75 "−" expr:75 : expr
syntax:70 expr:70 "·" expr:71 : expr
syntax:70 expr:70 "×" expr:71 : expr
syntax:70 expr:70 "/" expr:71 : expr
syntax:70 expr:70 "%" expr:71 : expr
syntax:70 expr:70 "∩" expr:71 : expr
syntax:65 expr:65 "+" expr:66 : expr
syntax:65 expr:65 "-" expr:66 : expr
syntax:65 expr:65 "−" expr:66 : expr
syntax:65 expr:65 "∪" expr:66 : expr
syntax:25 expr:26 "→" expr:25 : expr
syntax mixfix_expr : expr
syntax (priority := 2) expr "(" expr ")" : expr
syntax "(" expr ("," expr)? ")" : expr
syntax "{" expr,* "}" : expr  -- set of values
syntax "{" if_case+ expr "otherwise" "}" : expr
syntax id "[" expr "]" : expr  -- quotient type projection
syntax &"some" id ":" expr "such" "that" prop : expr

syntax atomic(expr "if") prop "|" : if_case

syntax type := expr

sdef simple_type
  | id
  | simple_type "×" simple_type

syntax ids_type := atomic(ident,+ binder_op) type

-- relational operators
sdef rel_op
  | "=" | "≠" | "<" | "≮" | "≤" | ">" | "≯" | "≥"
  | "∈" | "∉" | "⊆" | "⊂" | "≈" | "≉"
  | "|" | "∣"    -- vertical bar, division symbol: we accept either
  | "∤"         -- does not divide

-- all built-in operators
sdef op
  | "∘" | "^" | "·" | "×" | "/" | "%" | "∩" | "+" | "-" | "−" | "∪"
  | "<" | "≤" | ">" | "≥" | "∈" | "⊆" | "⊂" | "≈" | "|" | "∣"

sdef rel_prop
  -- We exclude "|" from chaining since that can cause problems when
  -- parsing if/otherwise expressions, which use "|" to separate cases.
  | expr rel_op expr ((! "|") rel_op expr)*

kdef _either = "either"
kdef _if = "if"
kdef _for = "for"
kdef _the = "the"
kdef _there = "there"

sdef _iff
  | "iff" <|> (atomic("if" "and") "only" "if")

kdef _every = "any" | "every"

syntax _for_all := _for ("all" <|> _every)

kdef _exists = "exist" | "exists" | "is"

sdef multi_or
  | multi_specifier "one" "of" rel_prop,+ "is" &"true"

kdef _is_have = "this is" | "we have"

syntax have_contradiction := _is_have &"a" "contradiction"

syntax is_tf := &"is" (&"true" <|> &"false")

sdef ids_types
  | sepBy1(ids_type, "and")
  | natural_type id_list   -- e.g. "natural numbers x, y and z"

syntax for_all_ids := _for_all ids_types

syntax for_all_opt_with := for_all_ids ("with" rel_prop)?

-- natural language

syntax adjective := "only" <|> natural_property  -- type: e → t

syntax comp_adjective_phrase := natural_comparative "than" expr  -- type: e → t

sdef adjective_phrase  -- type: e → t
  | adjective
  | comp_adjective_phrase

-- forward declarations
declare_syntax_cat verb_phrase
declare_syntax_cat noun_phrase_e_et_t

-- e → e → t  (e.g. "divisor", "least element")
syntax noun_e_e_t := natural_attribute

-- e → e → t (e.g. "prime divisor")
sdef nominal_e_e_t
  | noun_e_e_t
  |:50 adjective nominal_e_e_t:50

declare_syntax_cat collection
syntax (name := collection) natural_type_name "of" adjective : collection

syntax _and := atomic("and" (! "also"))

sdef noun_phrase_e
  | expr
  | expr _and expr
  | _the collection  -- e.g. "the set of primes"
  | "itself"

-- e → t (e.g. "positive integer", "divisor of n")
sdef nominal_e_t
  | natural_type
  |:60 atomic(nominal_e_e_t:60 "of") noun_phrase_e
  | nominal_e_t "with" noun_phrase_e_et_t
  |adjective nominal_e_t
  | nominal_e_t comp_adjective_phrase
  | nominal_e_t "that" verb_phrase

-- e → e → t (e.g. "a prime divisor p")
declare_syntax_cat noun_phrase_e_e_t (behavior := symbol)
syntax a_or_some nominal_e_e_t var ? : noun_phrase_e_e_t

-- e → t (e.g. "a positive integer")
declare_syntax_cat noun_phrase_e_t (behavior := symbol)
syntax &"a" nominal_e_t : noun_phrase_e_t

-- (e → t) → t (e.g. "every positive integer")
syntax noun_phrase_et_t := _every nominal_e_t

-- e → (e → t) → t (e.g. "no divisor")
syntax "no" nominal_e_e_t : noun_phrase_e_et_t

sdef predicative_e
  | noun_phrase_e

sdef predicative_e_t
  | adjective_phrase
  | noun_phrase_e_t

syntax verb_e_e_t := natural_relation

-- verb_phrase, type: e → t
syntax "has" noun_phrase_e_e_t : verb_phrase
syntax "has" noun_phrase_e_et_t : verb_phrase
syntax &"is" opt_not predicative_e_t : verb_phrase
syntax "are" predicative_e : verb_phrase
syntax verb_e_e_t noun_phrase_e : verb_phrase
syntax verb_e_e_t noun_phrase_et_t : verb_phrase

-- prop

sdef var_list
  | ids_types
  | adjective "function" ident ":" type

declare_syntax_cat exists_phrase  -- forward declaration

syntax thm_holds :=
  "the" ("assertion" <|> "lemma" <|> "theorem" <|> "result") ("holds" <|> ("is" &"true"))

syntax _unique := &"unique"

sdef_extend prop
  | (priority := 1) noun_phrase_e verb_phrase
  | noun_phrase_et_t verb_phrase
  | (priority := 2) atomic(expr is_tf)
  | atomic(rel_prop) is_tf ?
  | mixfix_prop
  |:35 prop:36 _and prop:35
  |:30 atomic(_either ? prop:31 "or") prop:30
  |:25 prop:26 "implies" prop:25
  | for_all_opt_with "," ? prop
  |:23 prop:23 for_all_opt_with
  |:23 prop:23 _for &"some" ids_types
  |:20 prop:21 _iff prop:21
  |:18 prop:19 atomic("," "and") prop:18
  |:18 prop:19 atomic("and" "also") prop:18
  |:16 atomic(_either ? prop:17 "," "or") prop:16
  | _if prop atomic("," ? "then") prop
  | _there _exists some_or_no ? _unique ? exists_phrase
  | multi_or
  | have_contradiction
  | thm_holds atomic("for" (! &"some") (id "=")? expr)?

syntax var_list ("such" "that" prop)? : exists_phrase
syntax nominal_e_t : exists_phrase

-- proof steps

syntax _thm := "Theorem" <|> "Lemma" <|> "Example"

syntax thm_name := ident

syntax assumption := ("our" <|> "the") "assumption"

sdef reference
  | sepBy1(thm_name, "and")
  | atomic("the" "fact") "that" prop
  | assumption ("that" prop)?

declare_syntax_cat reason (behavior := symbol)
sdef_extend reason
  | "[" tactic "]"
  | (priority := 1) reference
  | atomic(ident ? "induction")
  | "the" "inductive" "hypothesis"
  | (priority := 2) &"definition"
  | "the" &"definition" "of" ident

sdef eq_expr_by
  | rel_op expr ("by" reason)?

syntax begin_chain := expr eq_expr_by

declare_syntax_cat assert_prop
syntax (priority := 1) prop : assert_prop
syntax (priority := 2) atomic(begin_chain eq_expr_by+) : assert_prop

kdef _so =
  "also" | "but" | "consequently" | "hence" | "so" |
  "that is" | "then" | "therefore" | "thus"

kdef have1 =
  "clearly" | "it must be that" | "note that" |
  "observe that" | "this shows that" | "trivially" |
  "we deduce that" | "we have shown that" | "we have" |
  "we know that" | "we must have" | "we see that"

kdef _it = "it"

syntax _follows := _it "follows" ("by" reason)? "that"

kdef similarly = "similarly"

sdef _have
  | have1
  | _follows
  | similarly ","?

kdef _because = "because" | "since"

syntax because_prop := _because prop

kdef _by = "by"

syntax which_is := ("which" "is")? "again"?

sdef which_is_contra
  | atomic(which_is &"a" "contradiction") ("to" reference)?
  | atomic(which_is "contradicting") reference
  | atomic("which" "contradicts") reference

syntax which_is_contradiction :=
  atomic("," which_is_contra) because_prop ?

sdef proof_prop
  | (because_prop "," ?)? (_by reason)? _have ? assert_prop
    ("by" reason)? because_prop ? which_is_contradiction ?

kdef _let = "let"

kdef _also = "also"

kdef _assume1 = "assume" | "suppose"

sdef _assume
  | _also ? _assume1 "that"?

sdef let_step
  | atomic(_let ident,+ ":") type
  | atomic(_let id_list "be") _a ? natural_class ? natural_type

sdef init_step
  | let_step
  | _assume prop

sdef let_or_assume
  | init_step
  | _let ident "=" expr ("for" &"some" ids_types)?

sdef proof_if_prop
  | _if prop ","? "then" sepBy1(proof_prop, "/", "," _so)

kdef will_show =
  "we must show that" | "we will now prove that" | "we will prove that"

kdef _otherwise = "otherwise"

kdef _any_case =
  "in all cases" | "in any case" | "in both cases" | "in either case" | "in every case"

kdef _And = "and"

sdef and_or_so
  | (_And _so) <|> _so

declare_syntax_cat assert_step
syntax (priority := 1) and_or_so ? proof_prop : assert_step
syntax (priority := 2) proof_if_prop : assert_step
syntax will_show prop : assert_step

sdef clause_intro
  | ("First" <|> "Now" <|> "Second") ","?

syntax assertions := sepBy1(assert_step, "/", "," and_or_so)

kdef _define = "define"

sdef proof_sentence1
  | sepBy1(let_or_assume, "/", "," ? "and")
  | atomic(for_all_ids "," _define) expr "=" expr
  | _define expr "=" expr for_all_ids
  | assertions

sdef proof_sentence
  | clause_intro ? proof_sentence1 "."

syntax label := ident

syntax proof_label := label ("-" label)? "."

declare_syntax_cat proof_unit

sdef if_otherwise_intro
  | _assume prop "." proof_unit+
  | proof_if_prop "."

syntax any_case := _any_case prop ("," and_or_so assertions)? "."

syntax if_otherwise_unit :=
  atomic(if_otherwise_intro _otherwise) proof_unit+ any_case ?

syntax biconditional_unit :=
  atomic(_assume prop "." proof_unit+ "Conversely") ","?
  _assume prop "." proof_unit+

sdef_extend proof_unit
  | if_otherwise_unit
  | biconditional_unit
  | (! proof_label) proof_sentence

syntax case := "Case" num ":" prop "." proof_unit+

sdef case_unit
  | case+ _any_case prop "."
  | proof_unit

-- proofs

sdef proof
  | case_unit+
  | "By" reason "."

-- notation

syntax relational := "relational"

syntax op_decl :=
  atomic(str ("(" "negation" ":" str ")")? "is") _a op_kind relational ? "operator"

syntax _propositional := "propositional"

syntax mixfix_decl :=
  mixfix_token+ "is" &"a" _propositional ? "mixfix" "notation"

syntax notation_decl := (op_decl <|> mixfix_decl) "." "[" ident "]"

-- definitions

syntax id_sig := ident atomic("(" var ")")?

syntax constructor := const ":" type

syntax inductive_def :=
  "inductively" "with" "constructors" sepBy1(constructor, "and") "."

syntax justification := "Justification" "." "By" thm_name "."

syntax quotient_def := "as" "the" "quotient" simple_type "/" rel_op "." justification

sdef type_spec
  | "as" type "." -- direct type definition
  | inductive_def
  | quotient_def

syntax defined_term := non_var non_var ?

syntax a_or_the := _a <|> "the"

syntax type_def :=
  "The" &"type" id_sig ("(" a_or_the defined_term ")")?
  "is" "defined" type_spec

syntax attrib := atomic("@" ident) <|> attributes

syntax post_name := ("[" thm_name (":" attrib)? "]")?

syntax top_sentence := "Then"? prop "." post_name

syntax init_sentence := sepBy1(init_step, "/", "," ? "and") "."

syntax init_steps := init_sentence*

syntax _operator := ("unary" <|> "binary") ? ("operation" <|> "operator")

syntax def_if := _iff <|> "if"

sdef def_eq
  | expr "=" expr
  | expr (! "=") rel_op expr def_if prop
  | mixfix_expr "=" expr
  | mixfix_prop def_if prop
  | expr "is" defined_term def_if prop  -- property definition
  | expr "is" _a defined_term "of" id_list def_if prop  -- relation definition

syntax def1 := (for_all_ids ",") ? def_eq "."

sdef defs
  | def1 justification ?
  | (label "." def1)+

declare_syntax_cat direct_def
syntax (priority := 1) (let_step ".")* defs : direct_def
syntax (priority := 2) num (":" type)? "=" expr "." : direct_def

syntax cases_def :=
  "The" _operator op "on" ident
  "is" "defined" "recursively" "such" "that" for_all_ids "," (label "." def_eq ".")+

sdef definition
  | type_def
  | direct_def
  | cases_def

-- theorems

syntax prop_item := label "." init_steps top_sentence

syntax _proof_dot := "Proof" "."

syntax proof_item := proof_label proof

syntax proof_items := proof_item+

sdef props_proofs
  | top_sentence (_proof_dot proof)?
  | prop_item+ (_proof_dot proof_items)?

sdef type_class_ref
  | natural_property  -- e.g. "associative"
  | _a natural_property_noun  -- e.g. "an equivalence relation"

sdef theorem_body
  | init_steps props_proofs
  | atomic("The" _operator) op "is" type_class_ref "on" type "." post_name

syntax _theorem := thm_name ? str ? "." theorem_body

-- declarations

sdef thm_or_def
  | "Definition" "." definition
  | _thm _theorem

sdef top
  | "Notation" "." notation_decl
  | thm_or_def ("Corollary" _theorem)*
