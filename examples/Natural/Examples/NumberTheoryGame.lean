import Natural.Examples.Int

/- This file proves theorems from the Number Theory Game:
    https://adam.math.hhu.de/#/g/k88-b/numbertheorygame

   Actually there aren't any proofs in this file.  Many of these facts are proven
   in Int.lean and then automatically applied here via grind.
-/

-- divisibility club

Theorem.

  a. 3 divides 12.
  b. 1 divides every integer.
  c. Every integer divides itself.
  d. Any integer divides 0.

-- congruences in action

Theorem.  Let a, b, c, d, m : ℤ.

  a. a ≡ a (mod m).
  b. If a ≡ b (mod m) then b ≡ a (mod m).
  c. If a ≡ b (mod m) and b ≡ c (mod m) then a ≡ c (mod m).
  d. If a ≡ b (mod m) and c ≡ d (mod m) then a + c ≡ b + d (mod m).
  e. If a ≡ b (mod m) then a · c ≡ b · c (mod m).
  f. If a ≡ b (mod m) and c ≡ d (mod m) then a · c ≡ b · d (mod m).
