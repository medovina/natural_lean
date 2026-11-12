import Natural.Examples.Set
import Natural.Examples.Function
import Natural.Examples.Nat

Notation.  "~" (negation: "≁") is an infix relational operator.  [Type.equiv]

Definition.  Let A and B be types.  A ~ B iff there is a bijective function f : A → B.

Theorem.  Let A and B be types.

  a. A ~ A.  [Type.equinum_refl]
  b. If A ~ B then B ~ A.  [Type.equinum_symm]

Proof.

  a. Define f(x) = x for all x : A.  f is bijective, so A ~ A.

  b. Suppose that A ~ B.  Then there is a bijective function f : A → B.  By Function.inv_iff_bijective f has an inverse g.  By Function.inv_symm f is an inverse of g, so by Function.inv_iff_bijective g is bijective.  So B ~ A.

Definition.  Let T be a type.  T is finite if there is some n : Nat such that T ~ { 1, ..., n }.

Definition.  Let T be a type.  T is infinite if T is not finite.

-- Cantor's Theorem, Wiedijk #63

Theorem.  Let A be a type.  A ≁ Set(A).

Proof.  Suppose that A ~ Set(A). Then there is a bijective function f : A → Set(A). Let D = {a : A | a ∉ f(a)}.  Because f is surjective, there is some d : A such that f(d) = D.  Suppose that d ∈ D. Then by the definition of D we see that d ∉ f(d), so d ∉ D. Otherwise d ∉ D. Then d ∈ f(d), so d ∈ D. In either case we have a contradiction, so A ≁ Set(A).
