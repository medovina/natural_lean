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

Theorem.  Let A, B, C : Set(T).

  a. Let x : T.  Suppose that x ∈ A and x ∈ B.  Then x ∈ A.

  b. Suppose that x ∈ A ∩ B.  Then x ∈ B.

  c. A ∩ B ⊆ A.

  d. Let x : T.  Suppose that x ∈ A and x ∈ B.  Then x ∈ A ∩ B.

  e. Suppose that A ⊆ B and A ⊆ C.  Then A ⊆ B ∩ C.

  f. A ∩ B ⊆ B ∩ A.

  g. A ∩ B = B ∩ A.

  h. (A ∩ B) ∩ C = A ∩ (B ∩ C).

Proof.

  h. Let A, B, C : Set(T). Let x : T.  Suppose that x ∈ (A ∩ B) ∩ C.  Then x ∈ A ∩ (B ∩ C).  Conversely, suppose that x ∈ A ∩ (B ∩ C).  Then x ∈ (A ∩ B) ∩ C.
