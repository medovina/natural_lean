import Natural

-- definition of natural numbers

Definition.  The type ℕ is defined inductively with constructors 0 : ℕ and S : ℕ → ℕ.

-- theorems about successor function

Theorem.  For all x : ℕ, x = 0 or there exists some y : ℕ such that x = S(y).  [ℕ.is_zero_or_succ]

Proof.  By induction.

Theorem.  For all x : ℕ, S(x) ≠ x.  [ℕ.succ_ne_self]

Proof.  By induction.

-- addition: definition

Definition.  The binary operation + on ℕ is defined recursively such that for all x, y : ℕ,

  a.  x + 0 = x.
  b.  x + S(y) = S(x + y).

-- addition: theorems

Theorem "Associativity of Addition".  For all x, y, z: ℕ,

  x + (y + z) = (x + y) + z.  [ℕ.add_assoc]

Proof. Let x, y : ℕ.  Let

    A = { z : ℕ | x + (y + z) = (x + y) + z }.

  We must show that A = ℕ.  First, 0 ∈ A.  Second, let z : ℕ and assume z ∈ A.  Then x + (y + z) = (x + y) + z.  Now,

    x + (y + S(z)) = x + (S(y + z))
                   = S(x + (y + z))
                   = S((x + y) + z)
                   = (x + y) + S(z).

  Thus S(z) ∈ A.  We have shown that z ∈ A implies S(z) ∈ A.  Hence by induction z ∈ A for all z: ℕ.

Lemma.  Let x, y : ℕ.

  a. 0 + x = x.   [ℕ.zero_add]
  b. S(x) + y = S(x + y).   [ℕ.succ_add]

Proof.

  a. By induction.

  b. Let x : ℕ.  Let

    B = { y: ℕ | S(x) + y = S(x + y) }.

  Clearly 0 ∈ B.  Now let y : ℕ and suppose that y ∈ B.  Then

    S(x) + S(y) = S(S(x) + y)
                = S(S(x + y)) by the inductive hypothesis
                = S(x + S(y)).

  So S(y) ∈ B.  Hence by induction y ∈ B for all y: ℕ.

Theorem "Commutativity of Addition".  For all x, y : ℕ,

  x + y = y + x.  [ℕ.add_comm]

Proof.  Let y : ℕ.  Let

    C = { x : ℕ | x + y = y + x }.

  We know that

    0 + y = y      by ℕ.zero_add
          = y + 0 .

  So 0 ∈ C.  Now let x : ℕ, and suppose that x ∈ C.  Then

    S(x) + y = S(x + y) by ℕ.succ_add
             = S(y + x)
             = y + S(x).

  So S(x) ∈ C.  Hence by induction x ∈ C for all x : ℕ.

Theorem "Cancellation Law for Addition".  For all x, y, z: ℕ,

  x + z = y + z implies x = y.  [ℕ.add_right_cancel]

Proof.  Let x, y : ℕ.  Let

    A = { z : ℕ | x + z = y + z implies x = y }.

  First, x + 0 = y + 0 implies x = y, so 0 ∈ A.

  Second, let z : ℕ and assume z ∈ A.  Then x + z = y + z implies x = y.  Now assume x + S(z) = y + S(z).  Then S(x + z) = S(y + z).  Therefore x + z = y + z.  Hence by the inductive hypothesis x = y.  Thus we have shown that x + S(z) = y + S(z) implies x = y, so S(z) ∈ A.  Therefore z ∈ A implies S(z) ∈ A.  By induction z ∈ A for all z : ℕ.

Theorem.  For all x, y : ℕ, y ≠ S(x) + y.  [ℕ.not_succ_add]

Proof.  Let x : ℕ.  Let

    A = { y : ℕ | y ≠ S(x) + y }.

  0 ≠ S(x), so 0 ∈ A.  Now let y : ℕ, and assume that y ∈ A.  Then y ≠ S(x) + y.  Hence S(y) ≠ S(S(x) + y).  But S(S(x) + y) = S(x) + S(y).  Hence S(y) ≠ S(x) + S(y), so S(y) ∈ A.  Thus we have shown that for all y : ℕ, y ∈ A implies S(y) ∈ A.  By induction y ∈ A for all y : ℕ.

-- ordering: definition

Definition.  For all x, y : ℕ, x < y iff there is some z : ℕ such that x + S(z) = y.

-- ordering: theorems

Theorem.  Let x, y, z : ℕ.

  a. x ≮ x.  [ℕ.lt_irrefl]
  b. x < y and y < z implies x < z.  [ℕ.lt_trans]

Proof.

  a. Suppose that x < x.  Then there is some z : ℕ such that x + S(z) = x.  But x + S(z) ≠ x by ℕ.not_succ_add and ℕ.add_comm.  This is a contradiction.

  b. Suppose that x < y and y < z.  Then there exist some u, v : ℕ such that x + S(u) = y and y + S(v) = z.  Then

    z = (x + S(u)) + S(v)
      = x + (S(u) + S(v)) by ℕ.add_assoc
      = x + S(u + S(v)) by ℕ.succ_add.

Then x < z by ℕ.lt.

Theorem "Trichotomy".  For all x, y : ℕ, exactly one of x < y, x = y, y < x is true.  [ℕ.lt_trichotomy]

Proof.  Let x, y : ℕ.  If x < y and x = y then x < x, contradicting ℕ.lt_irrefl.  If x = y and y < x then x < x, again contradicting ℕ.lt_irrefl.  If x < y and y < x then by ℕ.lt_trans x < x, contradicting ℕ.lt_irrefl.  So at most one of x < y, x = y, y < x is true.

Let x, y : ℕ.  Let A = { x : ℕ | x < y or x = y or y < x }.  First, by ℕ.is_zero_or_succ we have either y = 0, or y = S(u) for some u : ℕ.  Hence by ℕ.zero_add either y = 0, or 0 + S(u) = y for some u : ℕ.  So y = 0 or 0 < y.  Thus 0 ∈ A.

Now let v : ℕ, and assume that v ∈ A.  Then v < y or v = y or y < v.

Case 1: v < y.  Then v + S(z) = y for some z : ℕ.  By ℕ.is_zero_or_succ either z = 0, or z = S(u) for some u : ℕ.  Suppose that z = 0 .  Then v + S(0) = y, that is S(v) = y.  Otherwise z = S(u) for some u : ℕ.  Then

  S(v) + S(u) = v + S(S(u)) by ℕ.succ_add
              = v + S(z) = y.

  So S(v) < y.  In either case S(v) < y or S(v) = y.

Case 2: v = y.  Then S(v) = S(y) = y + S(0).  So y < S(v).

Case 3: y < v.  Then v = y + S(u) for some u : ℕ.  Hence S(v) = S(y + S(u)) = y + S(S(u)).  Thus y < S(v).

In all cases S(v) < y or S(v) = y or y < S(v).  Hence S(v) ∈ A.  We have shown that for all v : ℕ, v ∈ A implies S(v) ∈ A.  By induction x ∈ A for all x : ℕ.  So at least one of x < y, x = y, y < x is true.

Theorem.  Let x : ℕ.

  a. x < S(x).  [ℕ.lt_succ]
  b. There is no y : ℕ such that x < y < S(x).  [ℕ.discrete]

Proof.

  a. x + S(0) = S(x).  Therefore x < S(x).

  b. Assume there is some y : ℕ such that x < y < S(x).  Since x < y there is some z : ℕ such that x + S(z) = y.  By ℕ.is_zero_or_succ either z = 0, or z = S(u) for some u : ℕ.  Suppose that z = 0 .  Then S(x) = x + S(0) = x + S(z) = y, contradicting ℕ.lt_trichotomy since y < S(x).  Otherwise z = S(u) for some u : ℕ.  Then S(x) + S(u) = x + S(S(u)) by ℕ.succ_add = x + S(z) = y.  Thus S(x) < y, contradicting ℕ.lt_trichotomy since y < S(x).  In either case we have a contradiction.

Definition.  For all x, y : ℕ, x ≤ y iff x < y or x = y.

Theorem.  For all x, y : ℕ, x ≤ y iff there is some z : ℕ such that x + z = y.  [ℕ.le_iff_add]

Proof.  Let x, y : ℕ.  Suppose that x ≤ y.  If x < y then there is some w : ℕ such that x + S(w) = y.  Otherwise x = y, so x + 0 = y.  In either case there is some z : ℕ such that x + z = y.

Let x, y : ℕ.  Suppose that there is some z : ℕ such that x + z = y.  If z = 0 then x = y, so x ≤ y.  Otherwise z ≠ 0 .  Then by ℕ.is_zero_or_succ there is some w : ℕ such that z = S(w).  Then x + S(w) = y, so x < y, so x ≤ y.  In either case x ≤ y.

Theorem.  Let x, y, z : ℕ.

  a. x ≤ x.  [ℕ.le_refl]
  b. If x < y and y ≤ z then x < z.  [ℕ.lt_of_lt_of_le]
  c. If x ≤ y and y < z then x < z.  [ℕ.lt_of_le_of_le]

Proof.

  b. Suppose that x < y ≤ z.  We know that y = z or y < z.  If y = z, then x < z.  If y < z, then x < z by ℕ.lt_trans.

  c. Suppose that x ≤ y and y < z.  We know that x = y or x < y.  If x = y, then y < z.  If x < y, then x < z by ℕ.lt_trans.
