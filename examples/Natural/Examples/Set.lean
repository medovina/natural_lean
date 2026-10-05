import Natural.Examples.SetBase

namespace Natural

-- sets: basic definitions

Definition.  Let S : Set(T).

  a. S is empty iff there is no x : T such that x ∈ S.
  b. S is nonempty iff there is some x : T such that x ∈ S.

Definition.  Let A, B : Set(T).  A ⊆ B iff x ∈ A implies x ∈ B for all x : T.

-- set operations

Definition.  Let A, B : Set(T).  A ∪ B = { x : T | x ∈ A or x ∈ B }.

Definition.  Let A, B : Set(T).  A ∩ B = { x : T | x ∈ A and x ∈ B }.

Lemma.  Let A, B : Set(T).  Let x : T.

  a. x ∈ A ∪ B if and only if x ∈ A or x ∈ B.  [Set.mem_union: @simp]
  b. x ∈ A ∩ B if and only if x ∈ A and x ∈ B.  [Set.mem_inter: @simp]

Notation.  "ᶜ" is a postfix operator.  [Set.compl]

Definition.  Let A : Set(T).  Aᶜ = { x : T | x ∉ A }.

-- families of sets

Notation.  "⋃" is a prefix operator.  [Set.sUnion]

Definition.  Let 𝒜 : Set(Set(T)).  ⋃ 𝒜 = { x : T | x ∈ A for some A ∈ 𝒜 }.

Notation.  "⋂" is a prefix operator.  [Set.sInter]

Definition.  Let 𝒜 : Set(Set(T)).  ⋂ 𝒜 = { x : T | x ∈ A for all A ∈ 𝒜 }.

Lemma.  Let 𝒜 : Set(Set(T)).  Let x : T.

  a. x ∈ ⋃ 𝒜 if and only if x ∈ A for some A ∈ 𝒜.  [Set.mem_sUnion: @simp]
  b. x ∈ ⋂ 𝒜 if and only if x ∈ A for all A ∈ 𝒜.  [Set.mem_sInter: @simp]
