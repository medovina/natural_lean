import Natural

open Lean.Core
open Lean.Parser.Term
open Lean.Syntax

namespace Natural

-- sets: definition

Definition.  The type Set(T) is defined as T → Prop.

Definition.  For any S : Set(T) and x : T, x ∈ S iff S(x) is true.

@[ext, grind ext]
theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x ↦ propext (h x))

-- Define set comprehension notation.  Currently a notation definition is not possible in Natural Lean, so we use native Lean commands here.

@[implicit_reducible]
def Set.ofPred {α : Type u} (p : α → Prop) : Set α := p

notation "{" x " : " type " | " body "}" => Set.ofPred fun x : type => body

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

-- Define notation for a set complement, plus an associated type class.

@[natural_op "ᶜ"]
class Compl (α : Type u) where
  compl : α → α

postfix:1024 "ᶜ" => Compl.compl

-- Define a resolver for set complement syntax.

@[natural_resolve super]
def compl_resolve : NaturalResolve
  | `(_super $t c) => do
      if ← is_numeric t then Lean.Elab.throwUnsupportedSyntax  -- treat as power
      else `($tᶜ)  -- complement
  | _ => Lean.Elab.throwUnsupportedSyntax

-- subsets

Definition.  Let A, B : Set(T).  A ⊆ B iff x ∈ A implies x ∈ B for all x : T.

-- set operations

Definition.  Let A, B : Set(T).  A ∪ B = { x : T | x ∈ A or x ∈ B }.

Definition.  Let A, B : Set(T).  A ∩ B = { x : T | x ∈ A and x ∈ B }.

Definition.  Let A : Set(T).  Aᶜ = { x : T | x ∉ A }.
