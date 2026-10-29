import Natural.Examples.Set
import Natural.Examples.Function
import Natural.Examples.Nat

Notation.  "~" (negation: "≁") is an infix relational operator.  [Set.equiv]

Definition.  Let A : Set(T).  Let B : Set(U).  A ~ B iff there is a bijective function f : A → B.

Theorem.  Let A : Set(T).

  a. A ~ A.

Proof.

  a. Define f(x) = x for all x : A.  f is bijective, so A ~ A.

Definition.  Let A : Set(T).  A is finite if there is some n : Nat such that A ~ { 1, ..., n }.

Definition.  Let A : Set(T).  A is infinite if A is not finite.
