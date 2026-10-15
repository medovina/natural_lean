import Natural
import Natural.Examples.Nat

Definition.  Let p : ℕ.  p is prime iff p > 1 and the only divisors of p are 1 and p.

Lemma.  Let p : ℕ.  If p > 1 and p is not prime then there is some a : ℕ such that a | p and a ≠ 1 and a ≠ p.  [ℕ.not_prime_has_factor]

Proof.  Suppose that p > 1 and p is not prime.  Suppose that for every a : ℕ, if a | p then a = 1 or a = p.  We know that 1 | p and p | p, so the divisors of p are 1 and p.  Then p is prime, which is a contradiction.

Lemma.  Every natural number greater than 1 has a prime divisor.

Proof.  Let A = { a : ℕ | a > 1 and a has no prime divisor }.  Assume that A is nonempty.  Then by ℕ.well_ordered A has a least element b.  So b > 1 and b has no prime divisor.

Suppose that b is prime.  But b | b, which contradicts the fact that b has no prime divisor.  Otherwise b is not prime.  Then by ℕ.not_prime_has_factor there is some natural number c such that c | b and c ≠ b and c ≠ 1.  We know that c ≠ 0, so c > 1.  Since c | b and b > 0, it follows by Nat.le_of_dvd that c ≤ b, so c < b.  Hence c ∉ A, so c has some prime divisor d.  Then by Nat.dvd_trans d | b, contradicting the fact that b ∈ A.  In both cases we have a contradiction.  Hence A is empty.
