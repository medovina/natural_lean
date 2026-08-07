import Mathlib.Data.Set.Defs
import Aesop

abbrev ℕ := Nat
abbrev S := Nat.succ

example: True := ⟨⟩

axiom t1_0: ∀x: Nat, x = 0 ∨ ∃y:Nat, x = S y

theorem t1_1: ∀x: Nat, x = 0 ∨ ∃y:Nat, x = S y :=
  by intro x; induction x <;> aesop

theorem t1_2: ∀x: Nat, S x != x :=
  by intro x; induction x <;> aesop

theorem t3_2: ∀x y z: Nat, x + (y + z) = (x + y) + z :=
  have: _ := fun x y: Nat =>
    let A := {z : Nat | x + (y + z) = (x + y) + z}
    have: 0 ∈ A := by aesop
    have: _ := fun (z: Nat) =>
      have: _ := fun (_: z ∈ A) =>
        have: x + (y + z) = (x + y) + z := by aesop
        have: _ := calc
          x + (y + S z) = x + S (y + z) := by aesop
                      _ = S (x + (y + z)) := by rfl
                      _ = S ((x + y) + z) := by aesop
                      _ = (x + y) + S z := by aesop
        have: S z ∈ A := by aesop
        have: z ∈ A → S z ∈ A := by aesop
        this
      this
    have: ∀z: Nat, z ∈ A := by intro x; induction x <;> aesop
    this
  this

theorem l3_3a (n: Nat): 0 + n = n + 0 := by aesop
