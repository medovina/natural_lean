import Natural.Examples.Cardinality
import Natural.Examples.Num

Definition.  Let p : ℕ.  p is prime if p > 1 and for all k : ℕ, if k | p then k = 1 or k = p.

-- lemma for proving infinitude of primes

Lemma.  Every natural number greater than 1 has a prime divisor.  [ℕ.exists_prime_factor]

Proof.  Let A = { a : ℕ | a > 1 and a has no prime divisor }.  Assume that A is nonempty.  Then by ℕ.well_ordered A has a least element b.  So b > 1 and b has no prime divisor.

Suppose that b is prime.  But b | b, which contradicts the fact that b has no prime divisor.  Otherwise b is not prime.  Then there is some natural number c such that c | b and c ≠ b and c ≠ 1.  We know that c ≠ 0, so c > 1.  Since c | b and b > 0, it follows by Nat.le_of_dvd that c ≤ b, so c < b.  Hence c ∉ A, so c has some prime divisor d.  Then by Nat.dvd_trans d | b, contradicting the fact that b ∈ A.  In both cases we have a contradiction.  Hence A is empty.

-- an alternate proof of the above lemma, using strong induction

Lemma.  Every natural number greater than 1 has a prime divisor.

Proof.  Let A = { a : ℕ | if a > 1 then a has a prime divisor }.  Let b : ℕ, and assume that x ∈ A for all x : ℕ with x < b.  If b ≤ 1 then trivially b ∈ A.

Otherwise b > 1.  If b is prime then b has a prime divisor since b | b.  Otherwise b is not prime.  Then there is some natural number c such that c | b and c ≠ b and c ≠ 1.  We know that c ≠ 0, so c > 1.  Since c | b and b > 0, it follows by Nat.le_of_dvd that c ≤ b, so c < b.  By the inductive hypothesis c has some prime divisor d.  Then by Nat.dvd_trans d | b.

In all cases b ∈ A.  By strong induction b ∈ A for all b : ℕ.

-- infinitude of primes

Theorem.  For all n : ℕ, n! > 0.  [ℕ.factorial_pos]

Proof.  By induction.

Theorem.  For all n : ℕ, k | n! for all k : ℕ with 0 < k ≤ n.  [ℕ.dvd_factorial]

Proof.  Let A = { n : ℕ | k | n! for all k : ℕ with 0 < k ≤ n }.  Clearly 0 ∈ A.  Suppose that n ∈ A.  Let k : ℕ and suppose that 0 < k ≤ n + 1.  If k = n + 1 then by Nat.dvd_mul_right k | (n + 1)!.  Otherwise 0 < k ≤ n, so by the inductive hypothesis k | n!.  In either case k | (n + 1)!, so (n + 1) ∈ A.  By induction n ∈ A for all n : ℕ.

Theorem.  Let n : ℕ.  There exists some p : ℕ such that p > n and p is prime.

Proof.  By ℕ.factorial_pos n! + 1 > 1, so by ℕ.exists_prime_factor there is some p : ℕ such that p is prime and p | (n! + 1).  Suppose that p ≤ n.  We know that p > 0, so by ℕ.dvd_factorial p | n!.  Then by Nat.dvd_sub p | ((n! + 1) - n!), so p | 1, so by Nat.dvd_one p = 1.  This is a contradiction since p is prime.  So p > n and p is prime.

-- linear combinations

Definition.  Let a, b, c : ℤ.  c is a linear combination of a and b if there exist m, n : ℤ such that c = ma + nb.
