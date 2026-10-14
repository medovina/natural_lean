import Natural
import Natural.Examples.Nat

Definition.  Let p : ℕ.  p is prime iff p > 1 and for all x : ℕ, if x | p then x = 1 or x = p.

Lemma.  Every natural number greater than 1 has a prime divisor.

Proof.  Let A = { a : ℕ | a > 1 and a has no prime divisor }.  Assume that A is nonempty.  Then by ℕ.well_ordered A has a least element b.  So b > 1 and b has no prime divisor.

Suppose that b is prime.  But b | b, which contradicts the fact that b has no prime divisor.  Otherwise b is not prime.  Then there is some natural number c such that c | b and c ≠ b and c ≠ 1.  We know that c ≠ 0, so c > 1.  Since c | b and b > 0, it follows by Nat.le_of_dvd that c ≤ b, so c < b.  Hence c ∉ A, so c has some prime divisor d.  Then by Nat.dvd_trans d | b, contradicting the fact that b ∈ A.  In both cases we have a contradiction.  Hence A is empty.
