import Natural.Examples.Cardinality
import Natural.Examples.Nat

Definition.  Let p : ℕ.  p is prime if p > 1 and for all k : ℕ, if 1 < k < p then k ∤ p.

Lemma.  Every natural number greater than 1 has a prime divisor.  [ℕ.prime_divisor]

Proof.  Let A = { a : ℕ | if a > 1 then a has a prime divisor }.  Let b : ℕ, and assume that x ∈ A for all x : ℕ with x < b.  If b ≤ 1 then trivially b ∈ A.

Otherwise b > 1.  If b is prime then b has a prime divisor since b | b.  Otherwise b is not prime.  Then there is some natural number c such that c | b and c ≠ b and c ≠ 1.  We know that c ≠ 0, so c > 1.  Since c | b and b > 0, it follows by Nat.le_of_dvd that c ≤ b, so c < b.  By the inductive hypothesis c has some prime divisor d.  Then by Nat.dvd_trans d | b.

In all cases b ∈ A.  By strong induction b ∈ A for all b : ℕ.
