import Natural

abbrev ℕ := Nat
abbrev S := Nat.succ

attribute [-simp] Nat.exists_eq_add_one

-- successor

Theorem n1_1.  For all x : ℕ, x = 0 or there exists some y : ℕ such that x = S(y).

Proof.  By induction.

Theorem n1_2.  For all x : ℕ, S(x) ≠ x.

-- addition

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

Lemma n3_3.  For all x, y: ℕ, S(x) + y = S(x + y).

Proof.  Let x : ℕ.  Let

    B = { y: ℕ | S(x) + y = S(x + y) }.

  Clearly 0 ∈ B.  Now let y : ℕ and suppose that y ∈ B.  Then

    S(x) + S(y) = S(S(x) + y)
                = S(S(x + y))
                = S(x + S(y)).

  So S(y) ∈ B.  Hence by induction y ∈ B for all y: ℕ.

Theorem n3_4 "Commutativity of Addition".  For all x, y : ℕ,

  x + y = y + x.

Proof.  Let y : ℕ.  Let

    C = { x : ℕ | x + y = y + x }.

  0 + y = y = y + 0, so 0 ∈ C.  Now let x : ℕ, and suppose that x ∈ C.  Then

    S(x) + y = S(x + y) by :n3_3
             = S(y + x)
             = y + S(x).

  So S(x) ∈ C.  Hence by induction x ∈ C for all x : ℕ.

Theorem n3_5 "Cancellation Law for Addition".  For all x, y, z: ℕ,

  x + z = y + z implies x = y.

Theorem n4_0. For all x, y: Nat, if x ≤ y then there exists some z: Nat such that x + z = y.

Proof.  Let B =

    { y : Nat | for all x : ℕ, if x ≤ y then there exists some z: Nat such that x + z = y }.

Let y = 0 .  Let x : ℕ, and suppose that x ≤ y.  Then we must have x = 0, and so x + 0 = y.  Thus 0 ∈ B.

Now let y : Nat and assume that y ∈ B.  Let x : ℕ, and suppose that x ≤ S(y).  Suppose that x = 0 .  Then x + S(y) = S(y).

Otherwise x ≠ 0 .  Then by :n1_1 there is some x' : Nat such that x = S(x').  Then S(x') ≤ S(y), so x' ≤ y.  So by the inductive hypothesis there is some z : ℕ such that x' + z = y.  Then we have S(x') + z = S(y) by :n3_3, so x + z = S(y).

In either case there is some z : ℕ such that x + z = S(y).  Therefore S(y) ∈ B.

Hence by induction y ∈ B for all y: Nat.
