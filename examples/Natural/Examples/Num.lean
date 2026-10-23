import Natural.Examples.Set

-- This file contains definitions/theorems about the Nat and Int types that are
-- built into Lean.

-- Nat

abbrev ℕ := Nat   -- use Lean's built-in natural number type
abbrev S := Nat.succ

-- strong induction principle

theorem strong_induction_on {p : ℕ → Prop} (n : ℕ) (h : ∀ n, (∀ m < n, p m) → p n) : p n
    := Nat.strongRecOn n h

attribute [natural theorem "strong induction"] strong_induction_on

-- least element of a set

Definition.  Let A : Set(ℕ).  Let z : ℕ.  z is a least element of A iff z ∈ A and for all u ∈ A, z ≤ u.

-- Here we prove that ℕ is well ordered using induction on ℕ.  (An alternative proof could use the fact that Nat belongs to the WellFoundedRelation type class.)

Theorem "Well-Ordering Property".  Every nonempty set of natural numbers has a least element.  [ℕ.well_ordered]

Proof.  Let A : Set(ℕ).  Suppose that A is nonempty.  Assume that A has no least element.  Let

    B = { x : ℕ | for all u : ℕ, if u ≤ x then u ∉ A }.

Observe that for all x ∈ B, x ∉ A.

First assume that 0 ∉ B.  Then there is some u : ℕ such that u ≤ 0 and u ∈ A.  We must have u = 0, so 0 ∈ A.  Then 0 is a least element of A, contradicting our assumption.  Hence 0 ∈ B.

Now assume x ∈ B.  Then

    for all u : ℕ, if u ≤ x then u ∉ A.

Assume that S(x) ∈ A.  Suppose that v ∈ A.  If v < S(x) then v ≤ x, so v ∉ A, which is a contradiction.  So v ≮ S(x), so v ≥ S(x).  Thus S(x) is a least element of A.  This is a contradiction, so S(x) ∉ A.

Hence for all u : ℕ, if u ≤ S(x) then u ∉ A. Then S(x) ∈ B.

We have shown that for all x ∈ B, S(x) ∈ B.  Hence by induction x ∈ B for all x : ℕ.  So A is empty, which is a contradiction.

-- divisibility

Lemma.  Let a : ℕ.  a | a.  [ℕ.dvd_rfl: @refl]

-- factorial

Notation.  "!" is a postfix operator.  [ℕ.factorial]

Definition.  The unary operation ! on ℕ is defined recursively such that for all n : ℕ,

  a.  0! = 1.
  b.  (n + 1)! = (n + 1) · n!.

-- Int

abbrev ℤ := Int
