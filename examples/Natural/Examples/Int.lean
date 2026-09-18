import Natural

-- This file defines the integers ℤ as a quotient type based on Nat × Nat.  The integers defined here are independent of Lean's built-in Int type (which in fact is defined as an inductive type, not a quotient).

Definition.  For all n, k, j, i : Nat, (n, j) ~ (k, i) if and only if n + i = k + j.

Theorem.  Let h, i, j, k, m, n : Nat.

  a. (h, i) ~ (h, i).  [ℤ.equiv_refl]
  b. If (h, i) ~ (j, k) then (j, k) ~ (h, i).  [ℤ.equiv_symm]
  c. If (h, i) ~ (j, k) and (j, k) ~ (m, n) then (h, i) ~ (m, n).  [ℤ.equiv_trans]

Corollary.  The operator ~ is an equivalence relation on Nat × Nat.  [ℤ.is_equiv]

-- definition of ℤ as a quotient type

Definition.  The type ℤ is defined as the quotient Nat × Nat / ~.

Justification.  By ℤ.is_equiv.

Definition.  0 : ℤ = ℤ[(0, 0)].

Definition.  1 : ℤ = ℤ[(1, 0)].

-- addition: definition

Lemma.  Let n, j, k, i, n₁, j₁, k₁, i₁ : Nat.  If (n, j) ~ (n₁, j₁) and (k, i) ~ (k₁, i₁) then

  (n + k, j + i) ~ (n₁ + k₁, j₁ + i₁).   [ℤ.add_equiv]

Definition.  For all a, b, c, d : Nat, ℤ[(a, b)] + ℤ[(c, d)] = ℤ[(a + c, b + d)].

Justification.  By ℤ.add_equiv.

-- addition: basic theorems

Theorem.  Let a, b, c : ℤ.

  a. a + b = b + a.
  b. a + (b + c) = (a + b) + c.
  c. a + 0 = a.

Proof.

  a - c. By the definition of ℤ.

-- multiplication: definition

Lemma. Let n, j, k, i, n₁, j₁, k₁, i₁ : Nat.  If (n, j) ~ (n₁, j₁) and (k, i) ~ (k₁, i₁) then

  (n × k + j × i, j × k + n × i) ~ (n₁ × k₁ + j₁ × i₁, j₁ × k₁ + n₁ × i₁).  [ℤ.mul_equiv]

Definition.  For all n, j, k, i : Nat,

  ℤ[(n, j)] × ℤ[(k, i)] = ℤ[(n × k + j × i, j × k + n × i)].

Justification.  By ℤ.mul_equiv.

-- multiplication: basic theorems

Theorem. Let a, b, c : ℤ.

  a. a × b = b × a.
  b. a × (b × c) = (a × b) × c.
  c. a × (b + c) = a × b + a × c.
  d. a × 1 = a.

Proof.

  a - d. By the definition of ℤ.
