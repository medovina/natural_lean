import Natural

namespace Natural

-- sets: definition

Definition.  The type Set(T) is defined as T → Prop.

Definition.  For any S : Set(T) and x : T, x ∈ S iff S(x) is true.

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

-- basic definitions on sets

Definition.  Let T be a type.  Let A, B : Set(T).  A ⊆ B iff x ∈ A implies x ∈ B for all x : T.
