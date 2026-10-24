import Natural

abbrev ℤ := Int

attribute [grind =] Int.dvd_def

-- congruences

Notation.  a "≡" b "(mod" m ")" is a mixfix notation.  [ℤ.mod_eq]

Definition.  Let a, b, m : ℤ.  a ≡ b (mod m) if m | (a - b).

-- Theorems about congruences.  We follow Rosen, _Elementary Number Theory_, section 4.1.

Theorem.  Let a, b, c, m : ℤ.

  a. a ≡ a (mod m).  [ℤ.mod_eq_refl: @simp]
  b. If a ≡ b (mod m) then b ≡ a (mod m).  [ℤ.mod_eq_symm: @symm]
  c. If a ≡ b (mod m) and b ≡ c (mod m) then a ≡ c (mod m).  [ℤ.mod_eq_trans: @grind]

Proof.

  a. a − a = 0, so m | (a − a).

  b. Suppose that a ≡ b (mod m).  Then m | (a − b), so there is some k : ℤ such that mk = a − b.  This shows that m(−k) = b − a, so m | (b − a).  Consequently b ≡ a (mod m).

  c. Suppose that a ≡ b (mod m) and b ≡ c (mod m).  Then m | (a − b) and m | (b − c).  Hence there exist k, l : ℤ such that mk = a − b and ml = b − c.  Therefore a − c = (a − b) + (b − c) = mk + ml = m(k + l).  It follows that m | (a − c), so a ≡ c (mod m).
