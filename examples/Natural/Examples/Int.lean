import Natural

open Lean

Definition.  For all n, k, j, i : Nat, (n, j) ~ (k, i) if and only if n + i = k + j.

Theorem.  Let h, i, j, k, m, n : Nat.

  a. (h, i) ~ (h, i).  [ℤ.equiv_refl]
  b. If (h, i) ~ (j, k) then (j, k) ~ (h, i).  [ℤ.equiv_symm]
  c. If (h, i) ~ (j, k) and (j, k) ~ (m, n) then (h, i) ~ (m, n).  [ℤ.equiv_trans]

Corollary.  The operator ~ is an equivalence relation on Nat × Nat.  [ℤ.is_equiv]

Definition.  The type ℤ is defined as the quotient Nat × Nat / ~.

Justification.  By ℤ.is_equiv.

Theorem.  Let n, j, k, i, n₁, j₁, k₁, i₁ : Nat.  If (n, j) ~ (n₁, j₁) and (k, i) ~ (k₁, i₁) then

  (n + k, j + i) ~ (n₁ + k₁, j₁ + i₁).   [ℤ.add_equiv]

Definition.  For all a, b, c, d : Nat, ℤ[(a, b)] + ℤ[(c, d)] = ℤ[(a + c, b + d)].

Justification.  By ℤ.add_equiv.

Theorem.  For all x, y : ℤ, x + y = y + x.

Proof.  By the definition of ℤ.
