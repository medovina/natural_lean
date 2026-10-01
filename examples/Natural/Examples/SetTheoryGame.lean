import Natural.Examples.Set

namespace Natural

-- subset world

Theorem.  Let A, B, C : Set(T).

  a. Suppose that x ∈ A.  Then x ∈ A.

  b. Suppose that A ⊆ B and x ∈ A.  Then x ∈ B.

  c. Suppose that A ⊆ B and B ⊆ C and x ∈ A.  Then x ∈ C.

  d. Suppose that A ⊆ B and for all x : T, x ∈ B implies x ∈ C.  Then x ∈ A implies x ∈ C for all x : T.

  e. A ⊆ A.

  f. Suppose that A ⊆ B and B ⊆ C.  Then A ⊆ C.

-- complement world

Theorem.  Let A, B : Set(T).

  a. Suppose that x ∈ A and x ∉ B.  Then A ⊆ B is false.

  b. Let x : T.  x ∈ Aᶜ if and only if x ∉ A.

  c. Suppose that A ⊆ B.  Then Bᶜ ⊆ Aᶜ.  [Set.compl_subset_compl_if]

  d. (Aᶜ)ᶜ = A.

  e. A ⊆ B if and only if Bᶜ ⊆ Aᶜ.

Proof.

  e. Suppose that A ⊆ B.  Then Bᶜ ⊆ Aᶜ by Set.compl_subset_compl_if.  Conversely, suppose that Bᶜ ⊆ Aᶜ.  Let x : T, and suppose that x ∈ A.  Then x ∉ Aᶜ, so x ∉ Bᶜ, so x ∈ B.

-- intersection world

Theorem.  Let A, B, C : Set(T).

  a. Suppose that x ∈ A and x ∈ B.  Then x ∈ A.

  b. Suppose that x ∈ A ∩ B.  Then x ∈ B.

  c. A ∩ B ⊆ A.

  d. Suppose that x ∈ A and x ∈ B.  Then x ∈ A ∩ B.

  e. Suppose that A ⊆ B and A ⊆ C.  Then A ⊆ B ∩ C.

  f. A ∩ B ⊆ B ∩ A.

  g. A ∩ B = B ∩ A.

  h. (A ∩ B) ∩ C = A ∩ (B ∩ C).

-- union world

Theorem.  Let A, B, C : Set(T).

  a. Suppose that x ∈ A.  Then x ∈ A or x ∈ B.

  b. B ⊆ A ∪ B.

  c. Suppose that A ⊆ C and B ⊆ C.  Then A ∪ B ⊆ C.

  d. A ∪ B ⊆ B ∪ A.

  e. A ∪ B = B ∪ A.

  f. (A ∪ B) ∪ C = A ∪ (B ∪ C).

-- combination world

Theorem.  Let A, B, C : Set(T).

  a. (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ.

  b. (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ.

  c. A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C).

  d. A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).

  e. Suppose that A ∪ C ⊆ B ∪ C and A ∩ C ⊆ B ∩ C. Then A ⊆ B.

Proof.

  e. Suppose that A ∪ C ⊆ B ∪ C and A ∩ C ⊆ B ∩ C. Suppose that x ∈ A.  If x ∈ C then x ∈ A ∩ C, so x ∈ B ∩ C, so x ∈ B.  Otherwise x ∉ C.  Then x ∈ A ∪ C, so x ∈ B ∪ C, so x ∈ B.  In either case x ∈ B.
