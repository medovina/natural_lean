import Natural
import Natural.Examples.Set

-- This file defines the natural numbers inductively and develops their elementary theory including addition, ordering, and multiplication.  It is entirely independent of Lean's built-in Nat type.

-- definition of natural numbers

Definition.  The type ℕ (the natural numbers) is defined inductively with constructors 0 : ℕ and S : ℕ → ℕ.

Definition.  1 : ℕ = S(0).

-- theorems about successor function

Theorem.  For all x : ℕ, x = 0 or there exists some y : ℕ such that x = S(y).  [ℕ.is_zero_or_succ]

Proof.  By induction.

Theorem.  For all x : ℕ, S(x) ≠ x.  [ℕ.succ_ne_self]

Proof.  By induction.

-- addition: definition

Definition.  The binary operation + on ℕ is defined recursively such that for all x, y : ℕ,

  a.  x + 0 = x.
  b.  x + S(y) = S(x + y).

Corollary.  For all x : ℕ, x + 0 = x.  [ℕ.add_zero: @simp]

-- addition: theorems

Theorem.  For all x, y, z: ℕ,

  (x + y) + z = x + (y + z).  [ℕ.add_assoc]

Proof. Let x, y : ℕ.  Let

    A = { z : ℕ | (x + y) + z = x + (y + z) }.

  First, 0 ∈ A.  Second, let z : ℕ and assume z ∈ A.  Then (x + y) + z = x + (y + z).  Now,

    x + (y + S(z)) = x + (S(y + z))
                   = S(x + (y + z))
                   = S((x + y) + z)
                   = (x + y) + S(z).

  Thus S(z) ∈ A.  We have shown that z ∈ A implies S(z) ∈ A.  Hence by induction z ∈ A for all z: ℕ.

Corollary.  The operator + is associative on ℕ.

Lemma.  Let x, y : ℕ.

  a. 0 + x = x.   [ℕ.zero_add: @simp]
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

Theorem.  For all x, y : ℕ,

  x + y = y + x.  [ℕ.add_comm]

Proof.  Let y : ℕ.  Let

    C = { x : ℕ | x + y = y + x }.

  We know that

    0 + y = y
          = y + 0.

  So 0 ∈ C.  Now let x : ℕ, and suppose that x ∈ C.  Then

    S(x) + y = S(x + y) by ℕ.succ_add
             = S(y + x)
             = y + S(x).

  So S(x) ∈ C.  Hence by induction x ∈ C for all x : ℕ.

Corollary.  The operator + is commutative on ℕ.

Theorem "Cancellation Law for Addition".  For all x, y, z: ℕ,

  x + z = y + z implies x = y.  [ℕ.add_right_cancel]

Proof.  Let x, y : ℕ.  Let

    A = { z : ℕ | x + z = y + z implies x = y }.

  First, x + 0 = y + 0 implies x = y, so 0 ∈ A.

  Second, let z : ℕ and assume z ∈ A.  Then x + z = y + z implies x = y.  Now assume x + S(z) = y + S(z).  Then S(x + z) = S(y + z).  Therefore x + z = y + z.  Hence by the inductive hypothesis x = y.  Thus we have shown that x + S(z) = y + S(z) implies x = y, so S(z) ∈ A.  Therefore z ∈ A implies S(z) ∈ A.  By induction z ∈ A for all z : ℕ.

Theorem.  For all x, y, z : ℕ,

  x + z = y + z iff x = y.  [ℕ.add_right_cancel_iff: @simp]

Proof.  By ℕ.add_right_cancel.

Theorem.  For all x, y : ℕ, y ≠ S(x) + y.  [ℕ.not_succ_add]

Proof.  Let x : ℕ.  Let

    A = { y : ℕ | y ≠ S(x) + y }.

  0 ≠ S(x), so 0 ∈ A.  Now let y : ℕ, and assume that y ∈ A.  Then y ≠ S(x) + y.  Hence S(y) ≠ S(S(x) + y).  But S(S(x) + y) = S(x) + S(y).  Hence S(y) ≠ S(x) + S(y), so S(y) ∈ A.  Thus we have shown that y ∈ A implies S(y) ∈ A.  By induction y ∈ A for all y : ℕ.

-- ordering: definition

Definition.  For all x, y : ℕ, x < y iff there is some z : ℕ such that x + S(z) = y.

-- ordering: theorems

Theorem.  Let x, y, z : ℕ.

  a. x ≮ x.  [ℕ.lt_irrefl: @simp]
  b. x < y and y < z implies x < z.  [ℕ.lt_trans]

Proof.

  a. Suppose that x < x.  Then there is some z : ℕ such that x + S(z) = x.  But x + S(z) ≠ x by ℕ.not_succ_add and ℕ.add_comm.  This is a contradiction.

  b. Suppose that x < y and y < z.  Then there exist some u, v : ℕ such that x + S(u) = y and y + S(v) = z.  Then

    z = (x + S(u)) + S(v)
      = x + (S(u) + S(v))
      = x + S(u + S(v)) by ℕ.succ_add.

    Then x < z by ℕ.lt.

Theorem "Trichotomy".  For all x, y : ℕ, exactly one of x < y, x = y, y < x is true.  [ℕ.lt_trichotomy]

Proof.  Let x, y : ℕ.  If x < y and x = y then x < x, contradicting ℕ.lt_irrefl.  If x = y and y < x then x < x, again contradicting ℕ.lt_irrefl.  If x < y and y < x then by ℕ.lt_trans x < x, contradicting ℕ.lt_irrefl.  So at most one of x < y, x = y, y < x is true.

Let x, y : ℕ.  Let A = { x : ℕ | x < y or x = y or y < x }.  First, by ℕ.is_zero_or_succ we have either y = 0, or y = S(u) for some u : ℕ.  Hence either y = 0, or 0 + S(u) = y for some u : ℕ.  So y = 0 or 0 < y.  Thus 0 ∈ A.

Now let v : ℕ, and assume that v ∈ A.  Then v < y or v = y or y < v.

Case 1: v < y.  Then v + S(z) = y for some z : ℕ.  By ℕ.is_zero_or_succ either z = 0, or z = S(u) for some u : ℕ.  Suppose that z = 0.  Then v + S(0) = y, that is S(v) = y.  Otherwise z = S(u) for some u : ℕ.  Then

  S(v) + S(u) = v + S(S(u)) by ℕ.succ_add
              = v + S(z) = y.

  So S(v) < y.  In either case S(v) < y or S(v) = y.

Case 2: v = y.  Then S(v) = S(y) = y + S(0).  So y < S(v).

Case 3: y < v.  Then v = y + S(u) for some u : ℕ.  Hence S(v) = S(y + S(u)) = y + S(S(u)).  Thus y < S(v).

In all cases S(v) < y or S(v) = y or y < S(v).  Hence S(v) ∈ A.  We have shown that v ∈ A implies S(v) ∈ A.  By induction x ∈ A for all x : ℕ.  So at least one of x < y, x = y, y < x is true.

Theorem.  Let x : ℕ.

  a. x < S(x).  [ℕ.lt_succ]
  b. There is no y : ℕ such that x < y < S(x).  [ℕ.discrete]

Proof.

  a. x + S(0) = S(x).  Therefore x < S(x).

  b. Assume there is some y : ℕ such that x < y < S(x).  Since x < y there is some z : ℕ such that x + S(z) = y.  By ℕ.is_zero_or_succ either z = 0, or z = S(u) for some u : ℕ.  Suppose that z = 0.  Then S(x) = x + S(0) = x + S(z) = y, contradicting ℕ.lt_trichotomy since y < S(x).  Otherwise z = S(u) for some u : ℕ.  Then S(x) + S(u) = x + S(S(u)) by ℕ.succ_add = x + S(z) = y.  Thus S(x) < y, contradicting ℕ.lt_trichotomy since y < S(x).  In either case we have a contradiction.

Definition.  For all x, y : ℕ, x ≤ y iff x < y or x = y.

Theorem.  For all x, y : ℕ, x ≤ y iff there is some z : ℕ such that x + z = y.  [ℕ.le_iff_add]

Proof.  Let x, y : ℕ.  Suppose that x ≤ y.  If x < y then there is some w : ℕ such that x + S(w) = y.  Otherwise x = y, so x + 0 = y.  In either case there is some z : ℕ such that x + z = y.

Let x, y : ℕ.  Suppose that there is some z : ℕ such that x + z = y.  If z = 0 then x = y, so x ≤ y.  Otherwise z ≠ 0.  Then by ℕ.is_zero_or_succ there is some w : ℕ such that z = S(w).  Then x + S(w) = y, so x < y, so x ≤ y.  In either case x ≤ y.

Theorem.  Let x, y, z : ℕ.

  a. x ≤ x.  [ℕ.le_refl]
  b. If x < y and y ≤ z then x < z.  [ℕ.lt_of_lt_of_le]
  c. If x ≤ y and y < z then x < z.  [ℕ.lt_of_le_of_lt]
  d. If x ≤ y and y ≤ z then x ≤ z.  [ℕ.le_trans]
  e. x ≤ y or y ≤ x.  [ℕ.le_or_ge]
  f. If x ≤ y and y ≤ x then x = y. [ℕ.le_antisymm]

Proof.

  b - c. By ℕ.lt_trans.
  d. By ℕ.lt_of_lt_of_le.
  e - f. By ℕ.lt_trichotomy.

instance: Std.IsLinearOrder ℕ where
  le_refl := ℕ.le_refl
  le_trans := by (default_apply ℕ.le_trans)
  le_antisymm := by (default_apply ℕ.le_antisymm)
  le_total := ℕ.le_or_ge

instance: Std.LawfulOrderLT ℕ where
  lt_iff := by (default_apply ℕ.lt_trichotomy)

Theorem.  Let x, y, z, u, v : ℕ.

  a. If x ≠ 0 then x > 0.   [ℕ.pos_if_ne_zero]
  b. x ≮ 0.                 [ℕ.not_lt_zero: @simp]
  c. x < x + S(y).          [ℕ.lt_add_of_succ]
  d. If x < y then x + z < y + z.  [ℕ.add_lt_add_right]
  e. If x + z < y + z then x < y.  [ℕ.lt_of_add_lt_add_right]
  f. x + z < y + z iff x < y.  [ℕ.add_lt_add_iff_right: @simp]
  g. x + z ≤ y + z iff x ≤ y.  [ℕ.add_le_add_iff_right: @simp]
  h. If x < y and u < v then x + u < y + v.  [ℕ.add_lt_add_of_lt_of_lt]
  i. If x < y and u ≤ v then x + u < y + v.  [ℕ.add_lt_add_of_lt_of_le]
  j. If x ≤ y and u < v then x + u < y + v.  [ℕ.add_lt_add_of_le_of_lt]
  k. If x ≤ y and u ≤ v then x + u ≤ y + v.  [ℕ.add_le_add_of_le_of_le]

Proof.

  a. Assume that x ≠ 0.  Then by ℕ.is_zero_or_succ there exists some u : ℕ such that x = S(u).  Hence x = 0 + S(u).  Therefore x > 0.

  b. By ℕ.pos_if_ne_zero and ℕ.lt_trichotomy.

  d. Assume that x < y.  Then x + S(w) = y for some w : ℕ.  Hence (x + z) + S(w) = (x + S(w)) + z = y + z.  Then x + z < y + z.

  e. By ℕ.lt_trichotomy and ℕ.add_lt_add_right.
  f. By ℕ.add_lt_add_right and ℕ.lt_of_add_lt_add_right.
  g. By ℕ.add_lt_add_iff_right and ℕ.add_right_cancel.

  h. Suppose that x < y and u < v.  By ℕ.add_lt_add_right x + u < y + u and u + y < v + y, so y + u < y + v.  Hence by ℕ.lt_trans x + u < y + v.

  i - j. By ℕ.add_lt_add_of_lt_of_lt.
  k. By ℕ.add_lt_add_of_le_of_lt and ℕ.add_le_add_iff_right.

Theorem.  Let x, y : ℕ.

  a. x < S(y) if and only if x ≤ y.   [ℕ.le_iff_lt_add_one]
  b. x < y if and only if S(x) ≤ y.   [ℕ.lt_iff_add_one_le]

Proof.

  a. Suppose that x < S(y).  If x > y then y < x < S(y), which is a contradiction to ℕ.discrete.  So by ℕ.lt_trichotomy we have x ≤ y.

  Conversely, suppose that x ≤ y.  If x ≥ S(y) then by ℕ.le_trans we deduce that S(y) ≤ y, which is a contradiction to ℕ.lt_succ and ℕ.lt_trichotomy.  So by ℕ.lt_trichotomy it must be that x < S(y).

  b. Suppose that x < y.  If S(x) > y then x < y < S(x), which is a contradiction to ℕ.discrete.  So by ℕ.lt_trichotomy it must be that S(x) ≤ y.

  Conversely, suppose that S(x) ≤ y.  If x ≥ y then by ℕ.le_trans we deduce that S(x) ≤ x, which is a contradiction to ℕ.lt_succ and ℕ.lt_trichotomy.  So by ℕ.lt_trichotomy it must be that x < y.

-- multiplication: definition

Definition.  The binary operation · on ℕ is defined recursively such that for all x, y : ℕ,

  a. x · 0 = 0.
  b. x · S(y) = (x · y) + x.

Corollary.  For all x : ℕ, x · 0 = 0.   [ℕ.mul_zero: @simp]

-- multiplication: theorems

Theorem.  For all x, y, z : ℕ, (y + z) · x = y · x + z · x.    [ℕ.add_mul]

Proof.  Let y, z : ℕ.  Let

    A = { x : ℕ | (y + z) · x = y · x + z · x }.

  Clearly 0 ∈ A.  Second, Let x : ℕ, and assume that x ∈ A.  Then (y + z) · x = y · x + z · x.  Hence

    (y + z) · S(x) = ((y + z) · x) + (y + z)
                   = (y · x + z · x) + (y + z)  by the inductive hypothesis
                   = (y · x + y) + (z · x + z)
                   = y · S(x) + z · S(x).

  Thus S(x) ∈ A.  We have shown that x ∈ A implies S(x) ∈ A.  By induction x ∈ A for all x : ℕ.

Lemma.  Let x : ℕ.

  a. 0 · x = 0.   [ℕ.zero_mul: @simp]
  b. 1 · x = x.   [ℕ.one_mul: @simp]

Proof.

  a - b. By induction.

Theorem.  For all x, y : ℕ,

    x · y = y · x.  [ℕ.mul_comm]

Proof.  Let x : ℕ.  Let A = { y : ℕ | x · y = y · x }.  Clearly 0 ∈ A.  Now let y : ℕ, and assume that y ∈ A.  Thus x · y = y · x.  Hence

    x · S(y) = (x · y) + x
             = (y · x) + x           by the inductive hypothesis
             = (y · x) + (1 · x)     by ℕ.one_mul
             = (y + 1) · x           by ℕ.add_mul
             = S(y) · x.

Thus S(y) ∈ A.  We have shown that y ∈ A implies S(y) ∈ A.  By induction y ∈ A for all y : ℕ.

Corollary.  The operator · is commutative on ℕ.

Theorem.  For all x, y, z : ℕ, x · (y + z) = x · y + x · z.  [ℕ.mul_add]

Proof.  By ℕ.add_mul and ℕ.mul_comm.

Theorem.  For all x, y, z : ℕ,

    x · (y · z) = (x · y) · z.  [ℕ.mul_assoc]

Proof.  Let x, y : ℕ.  Let

  B = { z : ℕ | x · (y · z) = (x · y) · z }.

Clearly 0 ∈ B.  Let z : ℕ, and suppose that z ∈ B.  Thus x · (y · z) = (x · y) · z.  Hence

    x · (y · S(z)) = x · (y · z + y)
                   = x · (y · z) + x · y   by ℕ.mul_add
                   = (x · y) · z + x · y   by the inductive hypothesis
                   = (x · y) · S(z).

Thus S(z) ∈ B.  We have shown that z ∈ B implies S(z) ∈ B.  By induction z ∈ B for all z : ℕ.

Corollary.  The operator · is associative on ℕ.

Theorem.  Let x, y, z : ℕ.

    a. If x < y and z ≠ 0, then x · z < y · z.  [ℕ.mul_lt_mul_of_pos_right]
    b. If x · z < y · z, then x < y.  [ℕ.lt_of_mul_lt_mul_right]

Proof.

  a. Assume that x < y and z ≠ 0.  Then y = x + S(u) for some u : ℕ.  Hence we have y · z = (x + S(u)) · z = (x · z) + (S(u) · z) by ℕ.add_mul.  Because z ≠ 0, by ℕ.is_zero_or_succ we have z = S(w) for some w : ℕ.  Then

      S(u) · z = S(u) · S(w)
                = S(u) · w + S(u)
                = S(S(u) · w + u).

  So y · z = x · z + S(S(u) · w + u).  It follows that x · z < y · z.

  b. Assume that x · z < y · z.  If z = 0 then x · 0 < y · 0, so 0 < 0, which is a contradiction. Assume x ≮ y.  Then by ℕ.lt_trichotomy either x = y or y < x.  If x = y then x · z = y · z, contradicting the assumption that x · z < y · z.  Otherwise y < x.  Then by ℕ.mul_lt_mul_of_pos_right y · z < x · z, contradicting the assumption that x · z < y · z.  In both cases we have a contradiction.

Theorem "Cancellation Law for Multiplication".  Let x, y, z : ℕ.

    If x · z = y · z and z ≠ 0 then x = y.  [ℕ.mul_right_cancel]

Proof.  Assume that x · z = y · z and z ≠ 0.  Also assume that x ≠ y.  Then by ℕ.lt_trichotomy either x < y or y < x.  If x < y then by ℕ.mul_lt_mul_of_pos_right x · z < y · z, contradicting our assumption that x · z = y · z.  If y < x then by ℕ.mul_lt_mul_of_pos_right y · z < x · z, contradicting our assumption that x · z = y · z.

Theorem.  Let x, y, z, u, v : ℕ.

  a. If x ≤ y, then x · z ≤ y · z.  [ℕ.mul_le_mul_right]
  b. If x · z ≤ y · z and z ≠ 0, then x ≤ y.  [ℕ.le_of_mul_le_mul_right]
  c. If y ≠ 0 then z ≤ y · z.   [ℕ.le_mul_of_pos_left]
  d. If y > 1 and z ≠ 0 then z < y · z.  [ℕ.le_mul_of_gt_one_left]
  e. If x < u and y < v then x · y < u · v.  [ℕ.mul_lt_mul_of_lt_of_lt]
  f. If x < u and y ≤ v and v ≠ 0, then x · y < u · v.  [ℕ.mul_lt_mul_of_lt_of_le]
  g. If x ≤ u and y < v and u ≠ 0, then x · y < u · v.  [ℕ.mul_lt_mul_of_le_of_lt]
  h. If x ≤ u and y ≤ v, then x · y ≤ u · v.

Proof.

  a.  Suppose that x ≤ y.  If z = 0 or x = y then x · z = y · z.  Otherwise z ≠ 0 and x < y, so x · z < y · z by ℕ.mul_lt_mul_of_pos_right.  In either case x · z ≤ y · z.

  b.  Suppose that x · z ≤ y · z and z ≠ 0.  If x · z < y · z, then by ℕ.lt_of_mul_lt_mul_right we have x < y, so x ≤ y.  Otherwise x · z = y · z, so by ℕ.mul_right_cancel we have x = y, so x ≤ y.  In any case x ≤ y.

  c. Suppose that y ≠ 0.  Then y > 0 by ℕ.pos_if_ne_zero, so y ≥ S(0) by ℕ.lt_iff_add_one_le.  Then by ℕ.mul_le_mul_right we know that 1 · z ≤ y · z, so z ≤ y · z.

  d. Suppose that y > 1 and z ≠ 0.  Then by ℕ.mul_lt_mul_of_pos_right 1 · z < y · z, so z < y · z.

  e. Suppose that x < u and y < v.  Then x ≤ u, so by ℕ.mul_le_mul_right we have x · y ≤ u · y.  Because x < u, we know that u ≠ 0.  So by ℕ.mul_lt_mul_of_pos_right we have y · u < v · u, so u · y < u · v.  Then by ℕ.lt_of_le_of_lt it follows that x · y < u · v.

  f. Suppose that x < u and y ≤ v and v ≠ 0.  If y < v, then by ℕ.mul_lt_mul_of_lt_of_lt x · y < u · v.  Otherwise y = v, so by ℕ.mul_lt_mul_of_pos_right x · v < u · v, so x · y < u · v.  In either case x · y < u · v.

  g. Suppose that x ≤ u and y < v and u ≠ 0.  Then by ℕ.mul_lt_mul_of_lt_of_le we know that y · x < v · u.  Then x · y < u · v.

  h. Suppose that x ≤ u and y ≤ v.

  Case 1: x = u.  Then y · x ≤ v · x by ℕ.mul_le_mul_right, so y · x ≤ v · u, so x · y ≤ u · v.

  Case 2: y = v.  Then x · y ≤ u · y by ℕ.mul_le_mul_right, so x · y ≤ u · v.

  Case 3: x ≠ u and y ≠ v.  Then x < u and y < v, so x · y < u · v by ℕ.mul_lt_mul_of_lt_of_lt, so x · y ≤ u · v.

  In every case x · y ≤ u · v.
