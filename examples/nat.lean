import Natural

-- definition of natural numbers

Definition.  The type ℕ is defined inductively with constructors 0 : ℕ and S : ℕ → ℕ.

-- theorems about successor function

Theorem n1_1.  For all x : ℕ, x = 0 or there exists some y : ℕ such that x = S(y).

Proof.  By induction.

Theorem n1_2.  For all x : ℕ, S(x) ≠ x.

Proof.  By induction.

-- addition: definition

@[implicit_reducible]
def ℕ.add : ℕ → ℕ → ℕ
  | x, 0 => x
  | x, S y => S (ℕ.add x y)

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

Theorem n3_6.  For all x, y : ℕ, y ≠ S(x) + y.

Proof.  Let x : ℕ.  Let

    A = { y : ℕ | y ≠ S(x) + y }.

  0 ≠ S(x), so 0 ∈ A.  Now let y : ℕ, and assume that y ∈ A.  Then y ≠ S(x) + y.  Hence S(y) ≠ S(S(x) + y).  But S(S(x) + y) = S(x) + S(y).  Hence S(y) ≠ S(x) + S(y), so S(y) ∈ A.  Thus we have shown that for all y : ℕ, y ∈ A implies S(y) ∈ A.  By induction y ∈ A for all y : ℕ.

-- ordering: definition

@[implicit_reducible]
def ℕ.lt (x y: ℕ) := ∃z : ℕ, x + S z = y

@[method_specs]
instance instLT_ℕ : LT ℕ where
  lt := ℕ.lt

attribute [grind =] instLT_ℕ.lt_spec

Theorem n4_1a.  For all x : ℕ, x ≮ x.

Proof.  Let x : ℕ, and suppose that x < x.  Then there is some z : ℕ such that x + S(z) = x.  But x + S(z) ≠ x by :n3_6 and :n3_4.  This is a contradiction.

Theorem n4_1b.  For all x, y, z: ℕ, x < y and y < z implies x < z.

Proof.  Let x, y, z : ℕ.  Suppose that x < y and y < z.  Then there exist some u, v : ℕ such that x + S(u) = y and y + S(v) = z.  Then

    z = (x + S(u)) + S(v)
      = x + (S(u) + S(v)) by :n3_2
      = x + S(u + S(v)) by :n3_3b.

Then x < z by :ℕ.lt.

Theorem n4_1c.  For all x, y : ℕ, exactly one of x < y, x = y, y < x is true.

Proof.  Let x, y : ℕ.  If x < y and x = y then x < x, contradicting :n4_1a.  If x = y and y < x then x < x, again contradicting :n4_1a.  If x < y and y < x then by :n4_1b x < x, contradicting :n4_1a.  So at most one of x < y, x = y, y < x is true.

Let x, y : ℕ.  Let A = { x : ℕ | x < y or x = y or y < x }.  First, by :n1_1 we have either y = 0, or y = S(u) for some u : ℕ.  Hence by :n3_3a either y = 0, or 0 + S(u) = y for some u : ℕ.  So y = 0 or 0 < y.  Thus 0 ∈ A.

Now let v : ℕ, and assume that v ∈ A.  Then v < y or v = y or y < v.

Case 1: v < y.  Then v + S(z) = y for some z : ℕ.  By :n1_1 either z = 0, or z = S(u) for some u : ℕ.  Suppose that z = 0 .  Then v + S(0) = y, that is S(v) = y.  Otherwise z = S(u) for some u : ℕ.  Then

  S(v) + S(u) = v + S(S(u)) by :n3_3b
              = v + S(z) = y.

  So S(v) < y.  In either case S(v) < y or S(v) = y.

Case 2: v = y.  Then S(v) = S(y) = y + S(0).  So y < S(v).

Case 3: y < v.  Then v = y + S(u) for some u : ℕ.  Hence S(v) = S(y + S(u)) = y + S(S(u)).  Thus y < S(v).

In all cases S(v) < y or S(v) = y or y < S(v).  Hence S(v) ∈ A.  We have shown that for all v : ℕ, v ∈ A implies S(v) ∈ A.  By induction x ∈ A for all x : ℕ.  So at least one of x < y, x = y, y < x is true.
