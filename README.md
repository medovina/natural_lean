# Natural Lean

Natural Lean is a library that lets you write Lean definitions, theorems, and proofs in a controlled natural language that looks much like ordinary mathematical English.  To use the library, you can simply write `import Natural` at the top of a Lean source file, then write natural-language mathematics freely in the rest of the file.  If you are using an IDE such as Visual Studio Code, Natural Lean will automatically translate your text into native Lean code, which will be checked for correctness.

The file `examples/nat.lean` in this repository contains a sample development of the natural numbers in Natural Lean.  I recommend looking at it for a first glimpse of the language's capabilities.

Natural Lean is in an __early stage of development__ and is not a practical tool for writing many Lean proofs at this time: the grammar and expressiveness of the language are still extremely limited.  You may nevertheless want to experiment with Natural Lean even in its current state, and your feedback [is welcome](mailto:adam.dingle@mff.cuni.cz).  I am actively developing the library and hope to evolve the controlled natural language to be robust enough for writing large-scale proofs of any nature.

## Getting Natural Lean

In your project's `lakefile.toml` file, write

```
[[require]]
name = "natural"
git = "https://github.com/medovina/natural_lean.git"
rev = "main"
```

## Quick tour

This section gives an informal overview of how to write mathematics in Natural Lean.  (I hope to add a more formal language reference before long.)

At the top of any source file, write

```
import Natural
```

After that, you can mix natural-language mathematics with native Lean code freely in the same file.

### Definitions

A definition begins with the capitalized word `Definition`.  Three kinds of definitions are currently supported.  An _inductive type definition_ defines a new type with one or more constructors:

```
Definition.  The type ℕ is defined inductively with constructors 0 : ℕ and S : ℕ → ℕ.
```

A _definition by cases_ defines a function recursively with one or more cases.  Currently the function must be a binary operator:

```
Definition.  The binary operation + on ℕ is defined recursively such that
  for all x, y : ℕ,

  a.  x + 0 = x.
  b.  x + S(y) = S(x + y).
```

A _direct definition_ defines a function non-recursively, using a single formula.  Currently the function must be a binary operator:

```
Definition.  For all x, y : ℕ, x < y iff there is some z : ℕ such that x + S(z) = y.
```

### Theorems

A natural-language theorem is introduced by the capitalized keyword `Theorem` (as distinguished from lowercase `theorem`, which begins a theorem in native Lean syntax).  Every theorem must have a __name__, which may appear either immediately after the word `Theorem`, or in brackets after the theorem statement.  Thus, these two declarations are equivalent:

```
Theorem ℕ.succ_ne_self.  For all x : ℕ, S(x) ≠ x.

Theorem.  For all x : ℕ, S(x) ≠ x.  [ℕ.succ_ne_self]
```

I generally find the second style to be more readable.

A theorem's name must be a valid Lean identifier and is its actual name in Lean.  Additionally a theorem may optionally have a __long name__, which may be any string and appears in quotes:

```
Theorem "Associativity of Addition".  For all x, y, z: ℕ,

  x + (y + z) = (x + y) + z.  [ℕ.add_assoc]
```

A theorem may or may not be followed by a __proof__.  If a proof is not present, the system will attempt to prove the theorem using the default tactic as described below.  If a proof is present, it appears after the text `Proof.`:

```
Theorem.  For all x : ℕ, x < S(x).  [ℕ.lt_succ]

Proof.  Let x : ℕ.  x + S(0) = S(x).  Therefore x < S(x).
```

The section Proofs below describes the structure of proofs.

#### Theorem groups

Several theorems may appear together in a single __theorem group__:

```
Theorem.  Let x, y, z : ℕ.

  a. x ≤ x.  [ℕ.le_refl]
  b. If x < y and y ≤ z then x < z.  [ℕ.lt_of_lt_of_le]
  c. If x ≤ y and y < z then x < z.  [ℕ.lt_of_le_of_le]

Proof.

  b. Suppose that x < y ≤ z.  We know that y = z or y < z.  If y = z, then x < z.
    If y < z, then x < z by ℕ.lt_trans.

  c. Suppose that x ≤ y and y < z.  We know that x = y or x < y.  If x = y,
    then y < z.  If x < y, then x < z by ℕ.lt_trans.
```

In a theorem group, each theorem must have a __label__, such as "a", "b" or "c" above.  The theorem group may have an associated `Proof` section containing labelled proofs for the theorems in the group.  As in the example above, some theorems in the group might not have proofs.

As visible above, a theorem group may begin with a `Let` declaration that is shared by all theorems in the group.   Any free variables in each theorem's statement will automatically be universally quantified using the type in the `Let` declaration.  Thus, the theorem group above is equivalent to

```
Theorem.

  a. For all x : ℕ, x ≤ x.  [ℕ.le_refl]
  b. For all x, y, z : ℕ, if x < y and y ≤ z then x < z.  [ℕ.lt_of_lt_of_le]
  c. For all x, y, z : ℕ, if x ≤ y and y < z then x < z.  [ℕ.lt_of_le_of_le]

Proof.

  ...
```

### Proofs

A __proof__ consists either of the keyword `By` followed by a __reason__, or a series of __proof steps__.

A reason may be any of the following:

- One or more theorem names, separated by `and`.  Example: `By ℕ.add_assoc and ℕ.succ_ne_self`.
- The keyword `induction`.
- An arbitrary Lean tactic in brackets.  Example: `By [simp +arith]`.

A proof step may be any of the following:

- An __assertion__ states a fact.  It may be preceded by a word such as `So`, `Now`, `Hence` or `Clearly`, and may optionally include a reason introduced by the `by` keyword.  Examples:

    ```
    Clearly 0 ∈ B.
    Hence by induction y ∈ B for all y: ℕ.
    Then x < z by ℕ.lt.
    ```

- A __let declaration__ introduces one or more universally quantified variables of a given type.  Examples:

    ```
    Let x, y, z : ℕ.
    Let a : ℤ.
    ```

- A __let definition__ introduces a variable and gives it a value.  Examples:

    ```
    Let x = 0.
    Let A = { z : ℕ | x + (y + z) = (x + y) + z }.
    ```

- An __assumption__ is expressed using the keyword `assume` or `suppose`.  Example:

    ```
    Assume that v ∈ A.
    Suppose that z = 0 .
    ```
  
  If an assumption does not appear at the beginning of an if/otherwise block, then Natural Lean will infer its scope heuristically.

In addition, the following are __compound steps__ that group proof steps together:

- An __if/then__ block introduces an assumption whose scope is limited to a single sentence.  Example:

   ```
   If z = 0 then x = y, so x ≤ y.
   ```

   This is like

   ```
   Assume that z = 0.  Then x = y.  So x ≤ y.
   ```

   except that the first form above restricts the assumption `z = 0` to be active only through the assertion `x ≤ y`.

- An __if/otherwise__ block allows a proof to consider two mutually exclusive possibilities.  It may have either of these forms:

    ```
    Assume A. (<proof_step>)+  Otherwise (<proof_step>)+  In either case B.

    If A then (<assertion>)+.  Otherwise (<proof_step>)+  In either case B.
    ```

  Here is an if/otherwise block expressed using each of the forms above, which are equivalent:

    ```
    Assume that x < y.  Then there is some w : ℕ such that x + S(w) = y. 
      Otherwise x = y, so x + 0 = y.  In either case there is some z : ℕ such that
      x + z = y.

    If x < y then there is some w : ℕ such that x + S(w) = y.  Otherwise x = y,
      so x + 0 = y.  In either case there is some z : ℕ such that x + z = y.
    ```

- A __cases__ block allows a proof to consider several mutually exclusive possibilities:

  ```
  Case 1: v < y.  Then v + S(z) = y for some z : ℕ.  By ℕ.is_zero_or_succ either z = 0, or z = S(u) for some u : ℕ.  So S(v) < y or S(v) = y.

  Case 2: v = y.  Then S(v) = S(y) = y + S(0).  So y < S(v).

  Case 3: y < v.  Then v = y + S(u) for some u : ℕ.  Hence S(v) = S(y + S(u)) = y + S(S(u)).  Thus y < S(v).

  In all cases S(v) < y or S(v) = y or y < S(v). 
  ```

### Propositions

Each theorem asserts that a certain __proposition__ is true, and every assertion step in a proof also contains a proposition.  A proposition may have any of these forms:

```
<expr> <rel_op> <expr>
<prop> and <prop>
<prop> or <prop>
<prop> implies <prop>
if <prop> then <prop>
<prop> iff <prop>
for all (<var>),+ : <type> , <prop>
<prop> for all (<var>),+ : <type>
there exists (some | no) (<var>),+ : <type> such that <prop>
<prop> for some (<var>),+ : <type>
either <prop> or <prop>
(at least | at most | exactly) one of (<prop>),+ is true
(this is | we have) a contradiction
```

Above `<prop>` is a proposition and `<rel_op>` indicates a relational operator such as `=`, `≠` or `<`.   `<expr>` and `<type>` are expressions or types as described in a following section.

Here are some examples of propositions:

```
x = 0
x + S(y) = S(x + y)
x < y and y < z implies x < z
for all x : ℕ, S(x) ≠ x
z ∈ A for all z: ℕ
there exists some y : ℕ such that x = S(y)
y = S(u) for some u : ℕ
at least one of x < y, x = y, y < x is true
```

#### Operator chains

A proposition may contain __chained relational operators__: for example, `x < y ≤ z = w` has the same meaning as `x < y and y ≤ z and z = w`.  In an assertion, each step in chain may optionally have a reason:

```
z = (x + S(u)) + S(v)
  = x + (S(u) + S(v)) by ℕ.add_assoc
  = x + S(u + S(v)) by ℕ.succ_add.
```

### Expressions

__Expressions__ represent mathematical values.  In Natural Lean an expression has any of the following forms:

```
<num>
<var>
<expr> <expr>      -- multiplication
<expr> <op> <expr>
<expr> ( <expr> )  -- function call or multiplication
( <expr> )
{ <var> : <var> | <prop> }
```

Above, `<op>` is a binary operator.  At the moment Natural Lean includes only the + and · operators, but I will expand this set soon.

Here are some examples of expressions:

```
0
y
x + (y + z)
S(x + y)
{ z : ℕ | x + (y + z) = (x + y) + z }
```

Implicit multiplication is supported: `xy` with no parentheses means `x · y`.  Note that Natural Lean uses the traditional function call syntax `f(x)`, which is different from `f x` as found in native Lean code.  An expression of the form `a(b)` is potentially ambiguous: it may represent either a multiplication or a function call.  At the moment Natural Lean considers such an expression to be a multiplication only if `a` is a numeric constant.

### Tactics

When an assertion does not contain a reason, or when a theorem does not include a proof at all, Natural Lean will attempt to prove the assertion or theorem using a tactic named `default` which tries each of `trivial`, `grind` and `aesop` in turn.  In the future I intent to make the default tactic configurable by any development in Natural Lean, but for the moment it is fixed.

As described above, an assertion or theorem may have a reason indicating one or more named theorems:

```
But x + S(z) ≠ x by ℕ.not_succ_add and ℕ.add_comm.
```

In this situation Natural Lean will invoke the tactic `default_apply` with the given theorem names, e.g. using the Lean code `(by default_apply ℕ.not_succ_add ℕ.add_comm)`.  `default_apply` is a tactic that calls each of `apply_rules`, `grind` and `aesop` in turn, passing the given theorems as arguments.  (I also intend to make this tactic configurable in the future.)

### Hints and tips

Due to a limitation in Lean's parser, in Natural Lean a number may not be directly followed by a period, so an assertion such as `x = 0.` will fail to parse.  Instead, you need to write a space after the number:

```
x = 0 .
```

I hope to implement a workaround to fix this limitation soon.

If you would like to see the Lean code that is generated from any definition or theorem in Natural Lean, write `set_option trace.Elab.command true in` immediately before the definition or theorem.  The Lean code will be visible in the InfoView window in Visual Studio Code.
