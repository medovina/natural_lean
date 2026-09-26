import Natural.Examples.Set

namespace Natural

-- subset world

Theorem.  Let A, B, C : Set(T).

  a. Suppose that x ∈ A.  Then x ∈ A.

  b. Suppose that A ⊆ B.  Suppose that x ∈ A.  Then x ∈ B.

  c. Suppose that A ⊆ B and B ⊆ C.  Suppose that x ∈ A.  Then x ∈ C.

  d. Suppose that A ⊆ B and for all x : T, x ∈ B implies x ∈ C.  Then x ∈ A implies x ∈ C for all x : T.

  e. A ⊆ A.

  f. Suppose that A ⊆ B and B ⊆ C.  Then A ⊆ C.

-- intersection world

Theorem.  Let A, B : Set(T).

  a. Let x : T.  Suppose that x ∈ A and x ∈ B.  Then x ∈ A.

  b. Suppose that x ∈ A ∩ B.  Then x ∈ B.
