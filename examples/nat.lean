import Natural

-- definition of natural numbers

inductive ℕ
  | zero
  | succ (n: ℕ)

instance: OfNat ℕ 0 where
  ofNat := ℕ.zero

abbrev S := ℕ.succ

-- theorems about successor function

Theorem n1_1.  For all x : ℕ, x = 0 or there exists some y : ℕ such that x = S(y).

Proof.  By induction.

Theorem n1_2.  For all x : ℕ, S(x) ≠ x.

Proof.  By induction.

-- addition: definition

@[implicit_reducible]
def ℕ.add : ℕ → ℕ → ℕ
  | x, 0 => x
  | x, ℕ.succ y => ℕ.succ (ℕ.add x y)

instance instAdd_ℕ : Add ℕ where
  add := ℕ.add

-- addition: theorems

Theorem n3_2 "Associativity of Addition".  For all x, y, z: ℕ,

  x + (y + z) = (x + y) + z.

Proof. Let x, y : ℕ.  Let

    A = { z : ℕ | x + (y + z) = (x + y) + z }.

  We must show that A = ℕ.  First, 0 ∈ A.  Second, let z : ℕ and assume z ∈ A.  Then x + (y + z) = (x + y) + z.  Now,

    x + (y + S(z)) = x + (S(y + z))
                   = S(x + (y + z))
                   = S((x + y) + z)
                   = (x + y) + S(z).

  Thus S(z) ∈ A.  We have shown that z ∈ A implies S(z) ∈ A.  Hence by induction z ∈ A for all z: ℕ.

Lemma n3_3a.  For all x : ℕ, 0 + x = x.

Proof.  Let

    A = { x : ℕ | 0 + x = x }.

  Then 0 ∈ A.  Let x : ℕ, and suppose that x ∈ A.  Then

    0 + S(x) = S(0 + x)
             = S(x).

  Hence S(x) ∈ A.  So by induction x ∈ A for all x : ℕ.

Lemma n3_3b.  For all x, y: ℕ, S(x) + y = S(x + y).

Proof.  Let x : ℕ.  Let

    B = { y: ℕ | S(x) + y = S(x + y) }.

  Clearly 0 ∈ B.  Now let y : ℕ and suppose that y ∈ B.  Then

    S(x) + S(y) = S(S(x) + y)
                = S(S(x + y)) by the inductive hypothesis
                = S(x + S(y)).

  So S(y) ∈ B.  Hence by induction y ∈ B for all y: ℕ.

Theorem n3_4 "Commutativity of Addition".  For all x, y : ℕ,

  x + y = y + x.

Proof.  Let y : ℕ.  Let

    C = { x : ℕ | x + y = y + x }.

  We know that

    0 + y = y      by :n3_3a
          = y + 0 .

  So 0 ∈ C.  Now let x : ℕ, and suppose that x ∈ C.  Then

    S(x) + y = S(x + y) by Lemma n3_3b
             = S(y + x)
             = y + S(x).

  So S(x) ∈ C.  Hence by induction x ∈ C for all x : ℕ.

Theorem n3_5 "Cancellation Law for Addition".  For all x, y, z: ℕ,

  x + z = y + z implies x = y.

Proof.  Let x, y : ℕ.  Let

    A = { z : ℕ | x + z = y + z implies x = y }.

  First, x + 0 = y + 0 implies x = y, so 0 ∈ A.

  Second, let z : ℕ and assume z ∈ A.  Then x + z = y + z implies x = y.  Now assume x + S(z) = y + S(z).  Then S(x + z) = S(y + z).  Therefore x + z = y + z.  Hence by the inductive hypothesis x = y.  Thus we have shown that x + S(z) = y + S(z) implies x = y, so S(z) ∈ A.  Therefore z ∈ A implies S(z) ∈ A.  By induction z ∈ A for all z : ℕ.
