import Natural

abbrev ℤ := Int

attribute [grind =] Int.dvd_def
attribute [grind .] Int.dvd_mul_of_dvd_left
attribute [grind .] Int.dvd_mul_of_dvd_right

-- absolute value

Notation.  "|" x "|" is a mixfix notation.  [ℤ.abs]

Definition.  Let n : ℤ.

  |n| = { n   if n ≥ 0
        | −n  otherwise }.

Example.  |−5| = 5.

-- linear combinations

Definition.  Let a, b, c : ℤ.  c is a linear combination of a and b if there exist m, n : ℤ such that c = ma + nb.

-- congruences

Notation.  a "≡" b "(mod" m ")" is a propositional mixfix notation.  [ℤ.mod_eq]

Definition.  Let a, b, m : ℤ.  a ≡ b (mod m) if m | (a - b).

-- Theorems about congruences.  We follow Rosen, _Elementary Number Theory_, section 4.1.

Theorem.  Let a, b, c, m : ℤ.

  a. a ≡ a (mod m).  [ℤ.mod_eq_refl: @simp]
  b. If a ≡ b (mod m) then b ≡ a (mod m).  [ℤ.mod_eq_symm: @symm]
  c. If a ≡ b (mod m) and b ≡ c (mod m) then a ≡ c (mod m).  [ℤ.mod_eq_trans: @[grind .]]

Proof.

  a. a − a = 0, so m | (a − a).

  b. Suppose that a ≡ b (mod m).  Then m | (a − b), so there is some k : ℤ such that mk = a − b.  This shows that m(−k) = b − a, so m | (b − a).  Consequently b ≡ a (mod m).

  c. Suppose that a ≡ b (mod m) and b ≡ c (mod m).  Then m | (a − b) and m | (b − c).  Hence there exist k, l : ℤ such that mk = a − b and ml = b − c.  Therefore a − c = (a − b) + (b − c) = mk + ml = m(k + l).  It follows that m | (a − c), so a ≡ c (mod m).

Theorem.  Let a, b, c, m : ℤ.  If a ≡ b (mod m) then ac ≡ bc (mod m).  [ℤ.mod_eq_mul_right: @[grind .]]

Proof.  Suppose that a ≡ b (mod m).  Then m | (a − b), so m | c(a − b), so m | (ac − bc), so ac ≡ bc (mod m).

set_option trace.natural true in
Theorem.  Let a, b, c, d, m : ℤ.  Suppose that a ≡ b (mod m) and c ≡ d (mod m).

  a. a + c ≡ b + d (mod m).  [ℤ.mod_eq_add: @[grind .]]
  b. ac ≡ bd (mod m).  [ℤ.mod_eq_mul: @[grind .]]

Proof.

  a. We know that m | (a − b) and m | (c − d).  Hence there exist k, l : ℤ such that mk = a − b and ml = c − d.

  Note that (a + c) − (b + d) = (a − b) + (c − d) = mk + ml = m(k + l).  Hence m | ((a + c) − (b + d)).

  b. We know that m | (a − b) and m | (c − d).  Hence there exist k, l : ℤ such that mk = a − b and ml = c − d.

  Note that ac − bd = ac − bc + bc − bd = c(a − b) + b(c − d) = cmk + bml = m(ck + bl).  Hence m | (ac − bd).
