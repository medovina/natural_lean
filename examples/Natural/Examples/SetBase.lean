import Natural

open Lean
open Lean.Core
open Lean.Parser.Term hiding type
open Lean.Syntax
open Natural

-- Low-level definitions related to sets.  Most of these use native Lean syntax since they can't be expressed in Natural Lean at this time.

-- sets: definition

Definition.  The type Set(T) (a set) is defined as T → Prop.

Definition.  For any S : Set(T) and x : T, x ∈ S iff S(x) is true.

@[ext, grind ext]
theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))

-- Define a coercion from sets to types.

@[coe, reducible] def Elem (s : Set α) : Type u := {x // x ∈ s}

instance : CoeSort (Set α) (Type u) := ⟨Elem⟩

-- Define set comprehension notation.

@[implicit_reducible]
def Set.ofPred {α : Type u} (p : α → Prop) : Set α := p

notation "{" x " : " type " | " body "}" => Set.ofPred (fun x : type => body)

notation "{" x " | " body "}" => Set.ofPred (fun x => body)

@[simp]
theorem mem_ofPred_eq {x : α} {p : α → Prop} : (x ∈ {y : α | p y}) = p x := rfl

grind_pattern mem_ofPred_eq => x ∈ Set.ofPred p

-- Define an elaborator that exposes the set comprehension syntax to Natural Lean.

syntax (name := set_comp) "{" ident ":" type "|" prop "}" : expr

@[natural_elab set_comp]
def set_comp_elab : NaturalElab
  | `(expr| { $x:ident : $type:type  | $p:prop }) => do
      let type ← of_type type
      (·, #[x], type) <$> `({ $x:ident : $type | $(← of_prop p)})
  | _ => Lean.Elab.throwUnsupportedSyntax

-- Define notation for a range of natural numbers.

notation "{" x "," "..." "," y "}" => { n : Nat | x <= n ∧ n <= y }

-- Expose the range syntax to Natural Lean.

syntax (name := range) "{" expr "," "..." "," expr "}" : expr

@[natural_elab range]
def range_elab : NaturalElab
  | `(expr| { $e:expr , ... , $f:expr }) => do
      `({ $(← of_expr e), ..., $(← of_expr f)}) <&> (·, #[], Lean.mkIdent ``Unit)
  | _ => Lean.Elab.throwUnsupportedSyntax

-- Define an elaborator for a set of all values with some property.

@[natural_elab collection]
def set_of_elab : NaturalElab
  | `(collection| set of $a:adjective) => do
      let a ← of_adjective a
      let x := mkIdent `x
      `({ $x:ident | $(← a x)}) <&> (·, #[x], Lean.mkIdent ``Unit)
  | _ => Lean.Elab.throwUnsupportedSyntax

-- Singleton and Insert instances, needed for syntax {a, b, c} to work

def Set.singleton (a : α) : Set α := {b : α | b = a}

instance: Singleton α (Set α) := ⟨Set.singleton⟩

@[simp, grind =]
theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b :=
  Iff.rfl

def Set.insert (a : α) (s : Set α) : Set α := {b : α | b = a ∨ b ∈ s}

instance: Insert α (Set α) := ⟨Set.insert⟩

@[simp, grind =]
theorem mem_insert_iff {x a : α} {s : Set α} : x ∈ insert a s ↔ x = a ∨ x ∈ s :=
  Iff.rfl
