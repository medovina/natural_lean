# Natural Lean: examples

This directory contains a set of files that demonstrate the capabilities of Natural Lean:

### Sets and functions

- `SetBase.lean`: definition of sets
- `Set.lean`: set operations, theorems about sets
- `SetTheoryGame.lean`: theorems from the [Set Theory Game](https://adam.math.hhu.de/#/g/djvelleman/stg4)
- `Function.lean`: basic notions about functions
- `Cardinality.lean`: basic notions about cardinality, including a proof of Cantor's Theorem

### Number systems

- `NatDef.lean`: definition of ℕ as an inductive type, theorems about ℕ
- `Nat.lean`: definition of ℕ as Lean's built-in type `Nat`, theorems about ℕ
- `NatNumGame.lean`: theorems from the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4)
- `IntDef.lean`: definition of ℤ as a quotient type, theorems about ℤ
- `Int.lean`: definition of ℤ as Lean's built-in type `Int`, theorems about ℤ
- `NumberTheoryGame.lean`: theorems from the [Number Theory Game](https://adam.math.hhu.de/#/g/k88-b/numbertheorygame)
- `Prime.lean`: definition of prime numbers, plus a proof of the infinitude of primes

The developments in `NatDef.lean` and `IntDef.lean` loosely follow the excellent textbook  _Number Systems and the Foundations of Analysis_ by Elliott Mendelson (1973).  However in Mendelson 1 is the first natural number and we begin with 0, so a number of our proofs are somewhat different.
