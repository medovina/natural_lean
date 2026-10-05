import Natural.Examples.Set
import Natural.Examples.Function

namespace Natural

Definition.  Let A and B be types.  A ~ B iff there is a bijective function f : A → B.

-- Cantor's Theorem, Wiedijk #63

Theorem.  Let A be a type.  A ≁ Set(A).

Proof.  Suppose that A ∼ Set(A). Then there is a bijective function f : A → Set(A). Let D = {a : A | a ∉ f(a)}.  Because f is surjective, there is some d : A such that f(d) = D.  Suppose that d ∈ D. Then by the definition of D we see that d ∉ f(d), so d ∉ D. Otherwise d ∉ D. Then d ∈ f(d), so d ∈ D. In either case we have a contradiction, so A ≁ Set(A).
