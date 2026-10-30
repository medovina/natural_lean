import Natural

Lemma.  Let A, B, C and D be types.  Let f : A → B.  Let g : B → C.  Let h : C → D.

  a. (h ∘ g) ∘ f = h ∘ (g ∘ f).

  b. f ∘ id = f.

  c. id ∘ f = f.

Definition.  Let A and B be types.  Let f : A → B.  Let g : B → A.

  a. g is a right inverse of f if f(g(x)) = x for all x : B.

  b. g is a left inverse of f if g(f(x)) = x for all x : A.

Definition.  Let A and B be types.  Let f : A → B.  Let g : B → A.  g is an inverse of f if g is a right inverse of f and also g is a left inverse of f.

Lemma.  Let A and B be types.  Let f : A → B.  If f has a right inverse and f has a left inverse then f has an inverse.

Proof.  Suppose that f has a right inverse g.  Also suppose that f has a left inverse h.  Then g = h, so g is a left inverse of f.  So f has an inverse.

Definition.  Let A and B be types.  Let f : A → B.

  a. f is injective iff f(x) = f(y) implies x = y for all x, y : A.

  b. f is surjective iff for every b : B, there exists some a : A such that f(a) = b.

Definition.  Let A and B be types.  Let f : A → B.  f is bijective iff f is injective and f is surjective.

Theorem.  Let A and B be nonempty types.  Let f : A → B.

  a. If f is surjective then f has a right inverse.

Proof.

  a. Suppose that f is surjective.  For every b : B, define

    h(b) = some a : A such that f(a) = b.

  Then f(h(b)) = b for all b : B, so f has a right inverse.
