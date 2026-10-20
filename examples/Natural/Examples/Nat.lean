import Natural.Examples.Set

abbrev ℕ := Nat   -- use Lean's built-in natural number type

-- strong induction principle

theorem strong_induction_on {p : ℕ → Prop} (n : ℕ) (h : ∀ n, (∀ m < n, p m) → p n) : p n
    := Nat.strongRecOn n h

attribute [natural theorem "strong induction"] strong_induction_on

-- least element of a set

Definition.  Let A : Set(ℕ).  Let z : ℕ.  z is a least element of A iff z ∈ A and for all u ∈ A, z ≤ u.

-- divisibility

Lemma.  Let a : ℕ.  a | a.  [ℕ.dvd_rfl: @refl]

-- factorial

Notation.  "!" is a postfix operator.  [ℕ.factorial]

Definition.  The unary operation ! on ℕ is defined recursively such that for all n : ℕ,

  a.  0! = 1.
  b.  (n + 1)! = (n + 1) · n!.
