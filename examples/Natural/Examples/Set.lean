import Natural

namespace Natural

def Set (α : Type u) := α → Prop

@[implicit_reducible]
def Mem (s : Set α) (a : α) : Prop := s a

instance : Membership α (Set α) := ⟨Mem⟩

-- set comprehension notation

@[implicit_reducible]
def Set.ofPred {α : Type u} (p : α → Prop) : Set α := p

notation "{" x ":" type "|" body "}" => Set.ofPred fun x : type => body

@[simp]
theorem mem_ofPred_eq {x : α} {p : α → Prop} : (x ∈ {y : α | p y}) = p x := rfl

grind_pattern mem_ofPred_eq => x ∈ Set.ofPred p

-- Natural Lean syntax extension

syntax (name := set_comp) "{" ident ":" type "|" prop "}" : expr

@[natural_elab set_comp]
def set_comp_elab : NaturalElab
  | `(expr| { $x:ident : $type:type  | $p:prop }) => do
      let type ← of_type type
      (·, #[x], type) <$> `({ $x:ident : $type | $(← of_prop p)})
  | _ => Lean.Elab.throwUnsupportedSyntax
