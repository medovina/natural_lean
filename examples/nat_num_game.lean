import Natural

open Nat (succ)

-- tutorial world

Theorem.  Let a, b, c, q, x, and y be natural numbers.

  a. 37x + q = 37x + q.

  b. If y = x + 7 then 2y = 2(x + 7).

  c. 2 = succ(succ(0)).

  d. a + (b + 0) + (c + 0) = a + b + c.

  e. succ(a) = a + 1.

  f. 2 + 2 = 4.

-- addition world

Theorem.  Let a, b, c, and n be natural numbers.

  a. 0 + n = n.

  b. succ(a) + b = succ(a + b).

  c. a + b = b + a.

  d. (a + b) + c = a + (b + c).

  e. (a + b) + c = (a + c) + b.

-- multiplication world

Theorem.  Let a, b, c, m, and n be natural numbers.

  a. m × 1 = m.

  b. 0 × m = 0.

  c. succ(a) × b = a × b + b.

  d. a × b = b × a.

  e. 1 × m = m.

  f. 2 × m = m + m.

  g. a(b + c) = ab + ac.

  h. (a + b) × c = ac + bc.

  i. (ab)c = a(bc).

-- implication world

Theorem.  Let x, y, and z be natural numbers.

  a. If x + y = 37 and 3x + z = 42 then x + y = 37.

  b. If 0 + x = (0 + y) + 2 then x = y + 2.

  c. If x = 37, and x = 37 implies y = 42, then y = 42.

  d. If x + 1 = 4 then x = 3.

  e. x = 37 implies x = 37.

  f. If x + 1 = y + 1 then x = y.

  g. If x = y and x ≠ y then we have a contradiction.

  h. 0 ≠ 1.

  i. 1 ≠ 0.

  j. 2 + 2 ≠ 5.

-- power world

Theorem.  Let a, b, m, and n be natural numbers.

  a. 0⁰ = 1.

  b. 0 ^ succ(m) = 0.

  c. a¹ = a.

  d. a² = a × a.

  e. aᵐ⁺ⁿ = aᵐ · aⁿ.

  f. (ab)ⁿ = aⁿbⁿ.

  g. (aᵐ)ⁿ = aᵐⁿ.

  h. (a + b)² = a² + b² + 2ab.

Proof.

  f. By Nat.mul_pow.

  g. By Nat.pow_mul.

-- algorithm world

Theorem.  Let a, b, c, d, e, f, g, and h be natural numbers.

  a. a + (b + c) = b + (a + c).

  b. (a + b) + (c + d) = ((a + c) + d) + b.

  c. (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h.

  d. If succ(a) = succ(b) then a = b.

  e. succ(a) ≠ 0.

  f. If a ≠ b then succ(a) ≠ succ(b).

  g. 20 + 20 = 40.

  h. 2 + 2 ≠ 5.

-- advanced addition world

Theorem.  Let a, b, n, x, and y be natural numbers.

  a. If a + n = b + n then a = b.

  b. If n + a = n + b then a = b.

  c. If x + y = y then x = 0.

  d. If x + y = x then y = 0.

  e. If a + b = 0 then a = 0.

  f. If a + b = 0 then b = 0.

-- ≤ world

Theorem.  Let x, y, and z be natural numbers.

  a. x ≤ x.

  b. 0 ≤ x.

  c. x ≤ succ(x).

  d. If x ≤ y and y ≤ z, then x ≤ z.

  e. If x ≤ 0, then x = 0.

  f. If x ≤ y and y ≤ x, then x = y.

  g. If x = 37 or y = 42, then y = 42 or x = 37.

  h. Either x ≤ y or y ≤ x.

  i. If succ(x) ≤ succ(y) then x ≤ y.

  j. If x ≤ 1 then either x = 0 or x = 1.

  k. If x ≤ 2 then x = 0 or x = 1 or x = 2.
