import Natural

-- This file defines the integers ℤ as a quotient type based on Nat × Nat.  The integers defined here are independent of Lean's built-in Int type (which in fact is defined as an inductive type, not a quotient).

Definition.  For all n, k, j, i : Nat, (n, j) ~ (k, i) if and only if n + i = k + j.

Theorem.  Let h, i, j, k, m, n : Nat.

  a. (h, i) ~ (h, i).  [ℤ.equiv_refl]
  b. If (h, i) ~ (j, k) then (j, k) ~ (h, i).  [ℤ.equiv_symm]
  c. If (h, i) ~ (j, k) and (j, k) ~ (m, n) then (h, i) ~ (m, n).  [ℤ.equiv_trans]

Corollary.  The operator ~ is an equivalence relation on Nat × Nat.  [ℤ.is_equiv]

-- definition of ℤ as a quotient type

Definition.  The type ℤ (the integers) is defined as the quotient Nat × Nat / ~.

Justification.  By ℤ.is_equiv.

Definition.  0 = ℤ[(0, 0)].

Definition.  1 = ℤ[(1, 0)].

Lemma.  For all a, b : Nat, ℤ[(a, b)] = 0 if and only if a = b.  [ℤ.eq_zero]

Proof.  Let a, b : Nat.  Suppose that ℤ[(a, b)] = 0.  Then ℤ[(a, b)] = ℤ[(0, 0)], so (a, b) ~ (0, 0), so a + 0 = b + 0, so a = b.  Conversely, suppose that a = b.  Then (a, b) ~ (0, 0), so ℤ[(a, b)] = ℤ[(0, 0)] = 0.

-- addition: definition

Lemma.  Let n, j, k, i, n₁, j₁, k₁, i₁ : Nat.  If (n, j) ~ (n₁, j₁) and (k, i) ~ (k₁, i₁) then

  (n + k, j + i) ~ (n₁ + k₁, j₁ + i₁).   [ℤ.add_equiv]

Definition.  For all a, b, c, d : Nat, ℤ[(a, b)] + ℤ[(c, d)] = ℤ[(a + c, b + d)].

Justification.  By ℤ.add_equiv.

Theorem.  Let a, b, c : ℤ.

  a. a + b = b + a.  [ℤ.add_comm]
  b. a + (b + c) = (a + b) + c.  [ℤ.add_assoc]
  c. a + 0 = a.  [ℤ.add_zero: @simp]
  d. 0 + a = a.  [ℤ.zero_add: @simp]

Proof.

  a - d. By the definition of ℤ.

Corollary.  The operator + is commutative on ℤ.

Corollary.  The operator + is associative on ℤ.

-- negation: definition

Lemma.  Let a, b, a₁, b₁ : Nat.  If (a, b) ~ (a₁, b₁), then

  (b, a) ~ (b₁, a₁).   [ℤ.neg_equiv]

Definition.  For all a, b : Nat, − ℤ[(a, b)] = ℤ[(b, a)].

Justification.  By ℤ.neg_equiv.

Theorem.  Let a, b : ℤ.

  a. a + −a = 0.  [ℤ.add_right_neg: @simp]
  b. a + b = 0 if and only if b = −a.  [ℤ.add_eq_zero_iff_eq_neg']

Proof.

  a. By the definition of ℤ.

  b. Suppose that b = −a.  Then a + b = 0.  Conversely, suppose that a + b = 0.  Then

    b = 0 + b = (a + −a) + b
              = (a + b) + −a
              = 0 + −a
              = −a.

-- multiplication: definition

Lemma. Let n, j, k, i, n₁, j₁, k₁, i₁ : Nat.  If (n, j) ~ (n₁, j₁) and (k, i) ~ (k₁, i₁) then

  (n × k + j × i, j × k + n × i) ~ (n₁ × k₁ + j₁ × i₁, j₁ × k₁ + n₁ × i₁).  [ℤ.mul_equiv]

Definition.  For all n, j, k, i : Nat,

  ℤ[(n, j)] × ℤ[(k, i)] = ℤ[(n × k + j × i, j × k + n × i)].

Justification.  By ℤ.mul_equiv.

-- multiplication: basic theorems

Theorem. Let a, b, c : ℤ.

  a. a × b = b × a.  [ℤ.mul_comm]
  b. a × (b × c) = (a × b) × c.  [ℤ.mul_assoc]
  c. a × (b + c) = a × b + a × c.  [ℤ.mul_add]
  d. (a + b) × c = a × c + b × c.  [ℤ.add_mul]
  e. a × 1 = a.  [ℤ.mul_one: @simp]

Proof.

  a - e. By the definition of ℤ.

Corollary.  The operator × is commutative on ℤ.

Corollary.  The operator × is associative on ℤ.

Theorem.  Let a, b : ℤ.  If a ≠ 0 and b ≠ 0, then a · b ≠ 0.

Proof.  Assume that a ≠ 0 and b ≠ 0.  Let a = ℤ[(n, j)] for some n, j : Nat.  Let b = ℤ[(k, i)] for some k, i : Nat.  It follows by ℤ.eq_zero that n ≠ j and k ≠ i.  Since k ≠ i, either k < i or i < k.

Suppose that i < k.  Then by Nat.exists_eq_add_of_lt k = i + (u + 1) for some u : Nat.  Since n ≠ j, it follows by Nat.mul_right_cancel_iff that n · (u + 1) ≠ j · (u + 1).  Hence

    n · k + j · i = n · (i + (u + 1)) + j · i
                  = n · i + n · (u + 1) + j · i
                  ≠ n · i + j · (u + 1) + j · i.

But

    n · i + j · (u + 1) + j · i = j · (i + (u + 1)) + n · i
                                = j · k + n · i.

Thus n · k + j · i ≠ j · k + n · i.

Otherwise k < i.  Then by Nat.exists_eq_add_of_lt i = k + (u + 1) for some u : Nat.  Since n ≠ j, it follows by Nat.mul_right_cancel_iff that n · (u + 1) ≠ j · (u + 1).  Hence

    n · k + j · i = n · k + j · (k + (u + 1))
                  = n · k + j · k + j · (u + 1)
                  ≠ n · k + j · k + n · (u + 1).

But

    n · k + j · k + n · (u + 1) = n · (k + (u + 1)) + j · k
                                = n · i + j · k.

Thus n · k + j · i ≠ j · k + n · i.

In any case n · k + j · i ≠ j · k + n · i.  So

    a · b = ℤ[(n · k + j · i, j · k + n · i)] ≠ 0 by ℤ.eq_zero.

-- Theorems that hold in ℤ and any ring

Theorem.  Let x, y, z : ℤ.

  a. If x + y = x + z then y = z.  [ℤ.add_left_cancel]
  b. −0 = 0.  [ℤ.neg_zero: @simp]
  c. −(−x) = x.  [ℤ.neg_neg: @simp]
  d. If −x = −y, then x = y.  [ℤ.neg_eq_neg]
  e. −(x + y) = (−x) + (−y).  [ℤ.neg_add]
  f. x + y = x iff y = 0.  [ℤ.left_eq_add: @simp]
  g. x · 0 = 0.  [ℤ.mul_zero: @simp]
  h. 0 · x = 0.  [ℤ.zero_mul: @simp]

Proof.

  a. Assume that x + y = x + z.  Then −x + (x + y) = −x + (x + z), so (−x + x) + y = (−x + x) + z, so 0 + y = 0 + z by ℤ.add_right_neg.  Therefore y = z.

  c. (−x) + x = x + (−x) = 0.  It follows by ℤ.add_eq_zero_iff_eq_neg' that −(−x) = x.

  d. Suppose that −x = −y.  Then −(−x) = −(−y), so by ℤ.neg_neg x = y.

  e. Observe that

    (x + y) + ((−x) + (−y)) = (x + (−x)) + (y + (−y)) = 0 + 0 = 0.

  Then by ℤ.add_eq_zero_iff_eq_neg' −(x + y) = (−x) + (−y).

  f. If x + y = x then x + y = x + 0, so by ℤ.add_left_cancel y = 0.

  g. x · 0 = x · (0 + 0) = x · 0 + x · 0 by ℤ.mul_add, so x · 0 = 0 by ℤ.left_eq_add.

  h. By ℤ.mul_zero and ℤ.mul_comm.
