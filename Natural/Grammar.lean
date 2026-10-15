import Lean
import Natural.Init

open Lean
open Lean.Parser

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

declare_syntax_cat type
syntax ident : type
syntax "Prop" : type
syntax type "(" type ")" : type
syntax:70 type:70 "×" type:71 : type
syntax:25 type:26 "→" type:25 : type

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

syntax simple_name_id := non_var

def mk_simple_name_id : Parser := node ``simple_name_id non_var

def lookup_simple_name (env: Environment): Syntax → Option (Category × Name)
  | `(simple_name_id| $i:ident) =>
      (lookup_assoc_in_env env name_extension (singular_name i none))
  | _ => none

def check_simple_name (c: Category) (env: Environment) (s: Syntax): Bool :=
  (lookup_simple_name env s).any (·.1 == c)

def simple_name (c: Category) (syntax_cat: String) : Parser :=
  withAntiquot (mkAntiquot syntax_cat ``simple_name_id) $
  atomic (mk_simple_name_id >> checkStackTopEnv (check_simple_name c) "unknown simple name")

def simple_noun := simple_name Category.noun "simple_noun"
def simple_adjective := simple_name Category.adjective "simple_adjective"
def simple_type := simple_name Category.type "simple_type"

syntax compound_name_ids := non_var non_var

def mk_compound_name_ids : Parser := node ``compound_name_ids (non_var >> non_var)

def lookup_compound_name (env: Environment) (s: Syntax): Option (Category × Name) :=
  match s with
  | `(compound_name_ids| $i:ident $j:ident) =>
      lookup_assoc_in_env env name_extension (singular_name i j)
  | _ => none

def check_compound_name (c: Category) (env: Environment) (s: Syntax): Bool :=
  (lookup_compound_name env s).any (·.1 == c)

def compound_name (c: Category) (syntax_cat: String) : Parser :=
  withAntiquot (mkAntiquot syntax_cat ``compound_name_ids) $
  atomic (mk_compound_name_ids >> checkStackTopEnv (check_compound_name c) "unknown compound name")

def compound_noun := compound_name Category.noun "compound_noun"
def compound_adjective := compound_name Category.adjective "compound_adjective"
def compound_type := compound_name Category.type "compound_type"

syntax natural_noun := simple_noun <|> compound_noun
syntax natural_adjective := simple_adjective <|> compound_adjective
syntax natural_type_name := simple_type <|> compound_type

declare_syntax_cat natural_type (behavior := symbol)
syntax &"type" : natural_type
syntax "types" : natural_type
syntax natural_type_name ("of" natural_type)? : natural_type

syntax binder_op := ":" <|> "∈"

syntax ids_type := atomic(ident,+ binder_op) type

kdef _at_least = "at least"
kdef _at_most = "at most"
kdef _exactly = "exactly"

sdef multi_specifier
  | _at_least
  | _at_most
  | _exactly

-- expr

sdef super_expr
  | super_digit+
  | super_letter+
  | super_expr "⁺" super_expr

declare_syntax_cat expr
syntax nat : expr
syntax ident : expr
syntax:80 (name := super) expr:80 super_expr : expr
syntax:80 expr:81 "^" expr:80 : expr
syntax:75 (priority := 1) expr:75 noWs expr:76 : expr
syntax:75 "-" expr:75 : expr
syntax:75 "−" expr:75 : expr
syntax:70 expr:70 "·" expr:71 : expr
syntax:70 expr:70 "×" expr:71 : expr
syntax:70 expr:70 "∩" expr:71 : expr
syntax:65 expr:65 "+" expr:66 : expr
syntax:65 expr:65 "∪" expr:66 : expr
syntax (priority := 2) expr "(" expr ")" : expr
syntax "(" expr ("," expr)? ")" : expr
syntax "{" expr,* "}" : expr  -- set of values
syntax ident "[" expr "]" : expr  -- quotient type projection

-- prop helpers

sdef rel_op
  | "=" | "≠" | "<" | "≮" | "≤" | ">" | "≯" | "≥"
  | "≁" | "∈" | "∉" | "⊆"
  | "~" | "∼"    -- tilde, tilde operator: we accept either
  | "|" | "∣"    -- vertical bar, division symbol: we accept either
  | "∤"         -- does not divide

kdef binary_op = "+" | "·" | "×" | "^" | "<" | "≤" | "~" | "∼"

sdef rel_prop
  | expr (rel_op expr)+

kdef _if = "if"

sdef _iff
  | "iff" <|> (atomic("if" "and") "only" "if")

kdef _for = "for"

syntax _for_all := _for ("all" <|> "any" <|> "every")

kdef _there = "there"

kdef _exists = "exist" | "exists" | "is"

sdef multi_or
  | multi_specifier "one" "of" rel_prop,+ "is" &"true"

kdef _either = "either"

syntax _a := &"a" <|> "an"

syntax a_or_some := _a <|> &"some"

syntax some_or_no := a_or_some <|> "no"

kdef _is_have = "this is" | "we have"

syntax have_contradiction := _is_have &"a" "contradiction"

syntax is_tf := &"is" (&"true" <|> &"false")

sdef ids_types
  | sepBy1(ids_type, "and")
  | natural_type id_list   -- e.g. "natural numbers x, y and z"

syntax for_all_ids := _for_all ids_types ","

-- natural language

syntax opt_not := "not" ?

syntax adjective := "only" <|> natural_adjective  -- type: e → t

syntax comp_adjective_phrase := adjective "than" expr  -- type: e → t

sdef adjective_phrase  -- type: e → t
  | adjective
  | comp_adjective_phrase

-- forward declarations
declare_syntax_cat verb_phrase
declare_syntax_cat noun_phrase_e_et_t

-- e → e → t  (e.g. "divisor", "least element")
syntax noun_e_e_t := natural_noun

-- e → e → t (e.g. "prime divisor")
sdef nominal_e_e_t
  | noun_e_e_t
  |:50 adjective nominal_e_e_t:50

-- e → t (e.g. "positive integer", "divisor of n")
sdef nominal_e_t
  | natural_type
  |:60 atomic(nominal_e_e_t:60 "of") expr
  | nominal_e_t "with" noun_phrase_e_et_t
  |adjective nominal_e_t
  | nominal_e_t comp_adjective_phrase
  | nominal_e_t "that" verb_phrase

sdef noun_phrase_e
  | expr
  | expr "and" expr
  | "the" nominal_e_t

-- e → e → t (e.g. "a prime divisor p")
declare_syntax_cat noun_phrase_e_e_t (behavior := symbol)
syntax a_or_some nominal_e_e_t var ? : noun_phrase_e_e_t

-- e → t (e.g. "a positive integer")
declare_syntax_cat noun_phrase_e_t (behavior := symbol)
syntax &"a" nominal_e_t : noun_phrase_e_t

-- (e → t) → t (e.g. "every positive integer")
syntax noun_phrase_et_t := "Every" nominal_e_t

-- e → (e → t) → t (e.g. "no divisor")
syntax "no" nominal_e_e_t : noun_phrase_e_et_t

sdef predicative_e
  | noun_phrase_e

sdef predicative_e_t
  | adjective_phrase
  | noun_phrase_e_t

-- verb_phrase, type: e → t
syntax "has" noun_phrase_e_e_t : verb_phrase
syntax "has" noun_phrase_e_et_t : verb_phrase
syntax &"is" opt_not predicative_e_t : verb_phrase
syntax "are" predicative_e : verb_phrase

-- prop

sdef var_list
  | ids_types
  | adjective "function" ident ":" type

declare_syntax_cat exists_phrase  -- forward declaration

sdef prop
  | (priority := 1) atomic(noun_phrase_e verb_phrase)
  | noun_phrase_et_t verb_phrase
  | (priority := 2) atomic(expr is_tf)
  | atomic(rel_prop) is_tf ?
  |:35 prop:36 "and" prop:35
  |:30 atomic(_either ? prop:31 "or") prop:30
  |:25 prop:26 "implies" prop:25
  | for_all_ids prop
  |:23 prop:23 _for_all ids_types
  |:23 prop:23 _for &"some" ids_types
  |:20 prop:21 _iff prop:21
  |:18 prop:19 atomic("," "and") prop:18
  |:16 atomic(_either ? prop:17 "," "or") prop:16
  | _if prop atomic("," ? "then") prop
  | _there _exists some_or_no ? exists_phrase
  | multi_or
  | have_contradiction

syntax var_list ("such" "that" prop)? : exists_phrase
syntax nominal_e_t : exists_phrase

-- proof steps

syntax _thm := "Lemma" <|> "Theorem"

syntax thm_name := ident

syntax assumption := ("our" <|> "the") "assumption"

sdef reference
  | sepBy1(thm_name, "and")
  | atomic("the" "fact") "that" prop
  | assumption ("that" prop)?

declare_syntax_cat reason (behavior := symbol)
syntax "[" tactic "]" : reason
syntax (priority := 1) reference : reason
syntax "induction" : reason
syntax "the" "inductive" "hypothesis" : reason
syntax (priority := 2) &"definition" : reason
syntax "the" &"definition" "of" ident : reason

sdef eq_expr_by
  | rel_op expr ("by" reason)?

syntax begin_chain := expr eq_expr_by

declare_syntax_cat assert_prop
syntax (priority := 1) prop : assert_prop
syntax (priority := 2) atomic(begin_chain eq_expr_by+) : assert_prop

kdef _so =
  "also" | "but" | "hence" | "so" | "that is" | "then" | "therefore" | "thus"

kdef have1 =
  "clearly" | "it must be that" | "observe that" |
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
  | atomic(_let id_list "be") _a ? natural_type

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

kdef _and = "and"

sdef and_or_so
  | (_and _so) <|> _so

declare_syntax_cat assert_step
syntax (priority := 1) and_or_so ? proof_prop : assert_step
syntax (priority := 2) proof_if_prop : assert_step
syntax will_show prop : assert_step

sdef clause_intro
  | ("First" <|> "Now" <|> "Second") ","?

syntax assertions := sepBy1(assert_step, "/", "," and_or_so)

sdef proof_sentence1
  | sepBy1(let_or_assume, "/", "," ? "and")
  | assertions

sdef proof_sentence
  | clause_intro ? proof_sentence1 "."

declare_syntax_cat proof_unit

sdef otherwise_intro
  | _assume prop "." proof_unit+
  | proof_if_prop "."

syntax otherwise_unit :=
  atomic(otherwise_intro _otherwise) proof_unit+
  _any_case prop ("," and_or_so assertions)? "."

syntax biconditional_unit :=
  atomic(_assume prop "." proof_unit+ "Conversely") ","?
  _assume prop "." proof_unit+

sdef_extend proof_unit
  | otherwise_unit
  | biconditional_unit
  | proof_sentence

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

syntax notation_decl :=
  "Notation" "." str "is" _a op_kind relational ? "operator" "." "[" ident "]"

-- definitions

syntax label := ident

syntax id_sig := ident atomic("(" var ")")?

syntax constructor := const ":" type

syntax inductive_def :=
  "inductively" "with" "constructors" sepBy1(constructor, "and") "."

syntax justification := "Justification" "." "By" thm_name "."

syntax quotient_def := "as" "the" "quotient" type "/" rel_op "." justification

sdef type_spec
  | "as" type "." -- direct type definition
  | inductive_def
  | quotient_def

syntax defined_term := non_var non_var ?

syntax a_or_the := _a <|> "the"

syntax type_def :=
  "The" &"type" id_sig ("(" a_or_the defined_term ")")?
  "is" "defined" type_spec

syntax attrib := "@" ident

syntax post_name := ("[" thm_name (":" attrib)? "]")?

syntax top_sentence := "Then"? prop "." post_name

syntax init_sentence := sepBy1(init_step, "/", "," ? "and") "."

syntax init_steps := init_sentence*

syntax _operator := "binary" ? ("operation" <|> "operator")

syntax def_if := _iff <|> "if"

sdef def_eq
  | expr "=" expr
  | expr (! "=") rel_op expr def_if prop
  | expr "is" defined_term def_if prop  -- property definition
  | expr "is" &"a" defined_term "of" expr def_if prop  -- relation definition

syntax def1 := for_all_ids ? def_eq "."

sdef defs
  | def1 justification ?
  | (label "." def1)+

declare_syntax_cat direct_def
syntax (priority := 1) (let_step ".")* defs : direct_def
syntax (priority := 2) num (":" type)? "=" expr "." : direct_def

syntax cases_def :=
  "The" _operator binary_op "on" ident
  "is" "defined" "recursively" "such" "that" for_all_ids (label "." def_eq ".")+

sdef definition
  | type_def
  | direct_def
  | cases_def

-- theorems

syntax prop_item := label "." init_steps top_sentence

syntax _proof_dot := "Proof" "."

syntax proof_item := label ("-" label)? "." proof

syntax proof_items := proof_item+

sdef props_proofs
  | top_sentence (_proof_dot proof)?
  | prop_item+ (_proof_dot proof_items)?

sdef type_class_ref
  | natural_adjective
  | _a natural_noun

sdef theorem_body
  | init_steps props_proofs
  | "The" _operator binary_op "is" type_class_ref "on" type "." post_name

syntax _theorem := thm_name ? str ? "." theorem_body

-- declarations

sdef thm_or_def
  | "Definition" "." definition
  | _thm _theorem

sdef top
  | notation_decl
  | thm_or_def ("Corollary" _theorem)*
