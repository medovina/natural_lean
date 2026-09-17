# Natural Lean: examples

This directory contains a set of files written in Natural Lean to demonstrate its capabilities:

- `Set.lean`: definition of sets (currently this is all native Lean code)
- `Nat.lean`: definition of ℕ as an inductive type, many theorems about ℕ
- `Int.lean`: definition of ℤ as a quotient type, various theorems about ℤ
- `nat_num_game.lean`: theorems from the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4)

The development in `Nat.lean` and `Int.lean` loosely follows the excellent textbook Mendelson, _Number Systems and the Foundations of Analysis_ (1973).  However in Mendelson 1 is the first natural number and we begin with 0, so a number of our proofs are somewhat different.
