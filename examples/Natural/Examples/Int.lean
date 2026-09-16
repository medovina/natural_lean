import Natural

Definition.  For all n, k, j, i : Nat, (n, j) ~ (k, i) if and only if n + i = k + j.

Theorem.  Let h, i, j, k, m, n : Nat.

  a. (h, i) ~ (h, i).  [equiv_refl]
  b. If (h, i) ~ (j, k) then (j, k) ~ (h, i).  [equiv_symm]
  c. If (h, i) ~ (j, k) and (j, k) ~ (m, n) then (h, i) ~ (m, n).  [equiv_trans]

Corollary.  The operator ~ is an equivalence relation on Nat × Nat.
