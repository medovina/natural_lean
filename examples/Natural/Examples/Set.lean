import Natural.Examples.SetBase

namespace Natural

-- subsets

Definition.  Let A, B : Set(T).  A ⊆ B iff x ∈ A implies x ∈ B for all x : T.

-- set operations

Definition.  Let A, B : Set(T).  A ∪ B = { x : T | x ∈ A or x ∈ B }.

Definition.  Let A, B : Set(T).  A ∩ B = { x : T | x ∈ A and x ∈ B }.

Theorem.  Let A, B : Set(T).  Let x : T.

  a. x ∈ A ∪ B if and only if x ∈ A or x ∈ B.  [Set.mem_union: @simp]

  b. x ∈ A ∩ B if and only if x ∈ A and x ∈ B.  [Set.mem_inter: @simp]

Notation.  "ᶜ" is a postfix operator.  [Set.compl]

Definition.  Let A : Set(T).  Aᶜ = { x : T | x ∉ A }.
