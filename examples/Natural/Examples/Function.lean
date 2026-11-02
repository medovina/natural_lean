import Natural.Examples.Set

-- Basic notions about functions.

-- If α is empty then there exists a function from α to β.
theorem Function.empty_function (h : ¬∃_x : α, True) : ∃_f : (α → β), True :=
  let f (x: α): β := False.elim (show False by solve_by_elim)
  ⟨f, True.intro⟩

Lemma.  Let A, B, C and D be types.  Let f : A → B.  Let g : B → C.  Let h : C → D.

  a. (h ∘ g) ∘ f = h ∘ (g ∘ f).

  b. f ∘ id = f.

  c. id ∘ f = f.

Definition.  Let A and B be types.  Let f : A → B.  Let g : B → A.

  a. g is a right inverse of f if f(g(x)) = x for all x : B.

  b. g is a left inverse of f if g(f(x)) = x for all x : A.

Definition.  Let A and B be types.  Let f : A → B.  Let g : B → A.  g is an inverse of f if g is a right inverse of f and also g is a left inverse of f.

Lemma.  Let A and B be types.  Let f : A → B.

  a. If f has a right inverse and f has a left inverse then f has an inverse.  [Function.inv_of_left_right]

  b. Let g : B → A.  If g is an inverse of f then f is an inverse of g.  [Function.inv_symm]

Proof.

  a. Suppose that f has a right inverse g.  Also suppose that f has a left inverse h.  Then g = h, so g is a left inverse of f.  So f has an inverse.

Definition.  Let A and B be types.  Let f : A → B.

  a. f is injective iff f(x) = f(y) implies x = y for all x, y : A.

  b. f is surjective iff for every b : B, there exists some a : A such that f(a) = b.

Definition.  Let A and B be types.  Let f : A → B.  f is bijective iff f is injective and f is surjective.

Theorem.  Let A and B be types.  Let f : A → B.

  a. f has a right inverse if and only if f is surjective.  [Function.surj_right_inv]
  b. If f is injective and there is some _a : A then f has a left inverse.  [Function.left_inv_if_inj]
  c. If f has a left inverse then f is injective.  [Function.inj_if_left_inv]
  d. f has an inverse if and only if f is bijective.  [Function.inv_iff_bijective]

Proof.

  a. Suppose that f has a right inverse g.  Then f(g(x)) = x for all x : B, so f is surjective.

  Conversely, suppose that f is surjective.  For every b : B, define

    h(b) = some a : A such that f(a) = b.

  Then f(h(b)) = b for all b : B, so f has a right inverse.

  b. Suppose that f is injective.  Suppose there is some a' : A.  For all b : B, define

      h(b) = { the unique x : A such that f(x) = b  if there is some x : A such that f(x) = b
             | a'  otherwise }.

    Let a : A.  Then h(f(a)) = the unique x : A such that f(x) = f(a), so h(f(a)) = a.  So f has a left inverse.

  d. Suppose that f has an inverse g.  Then by part (a) and part (c) f is bijective.

  Conversely, suppose that f is bijective.  Suppose there is some a' : A.  Then f has a right inverse by part (a).  Also f has a left inverse by part (b).  Then by Function.inv_of_left_right f has an inverse.

  Otherwise there is no a' : A.  If there is some b' : B then since f is surjective there is some x : A such that f(x) = b', which is a contradiction.  So there is no b' : B.  Then by empty_function there exists h : B → A.  For all x : B, f(h(x)) = x, so h is a right inverse of f.  Similarly h is a left inverse of f.  So h is a inverse of f.

  In either case f has an inverse.
