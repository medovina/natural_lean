import Natural

abbrev ℕ := Nat
abbrev S := Nat.succ

Theorem n1_1.  For all x : ℕ, x = 0 or there exists some y : ℕ such that x = S(y).

Proof.  By induction.

Theorem n1_2.  For all x : ℕ, S(x) ≠ x.

Theorem n3_2.  For all x, y, z: ℕ, x + (y + z) = (x + y) + z.

Proof. Let x, y : ℕ.  Let

   A = { z : ℕ | x + (y + z) = (x + y) + z }.

   We must show that A = ℕ.  First, 0 ∈ A.  Second, let z : ℕ and assume z ∈ A.  Then x + (y + z) = (x + y) + z.  Now,

  x + (y + S(z)) = x + (S(y + z))
                 = S(x + (y + z)) by [rfl]
                 = S((x + y) + z)
                 = (x + y) + S(z).

  Thus S(z) ∈ A.  We have shown that z ∈ A implies S(z) ∈ A.  Hence by induction z ∈ A for all z: ℕ.

Lemma n3_3a.  For all x: ℕ, 0 + x = x.
