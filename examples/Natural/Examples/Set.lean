import Natural

namespace Natural

-- Definition.  Let A and B be types.  Let f : A → B.  f is injective iff f(x) = f(y) implies x = y for all x, y : A.

def injective (A: Type) (B: Type) (f: A → B) :=
    ∀ x y : A, f x = f y → x = y

-- sets: definition

Definition.  The type Set(α) is defined as α → Prop.

Definition.  For any S : Set(α) and x : α, x ∈ S iff S(x) is true.

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
