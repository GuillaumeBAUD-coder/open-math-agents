import Mathlib

/-!
# A098807: Numbers k such that there exists a prime p for which p - k and p + k are also prime.

Source: https://oeis.org/A098807
Credit: @xor2k

Robert Israel (Mar 16 2026), in the comment section of A098807:
  All terms are even. Dickson's Conjecture implies that all multiples of 6 are terms. An even
  number k not divisible by 3 is a term if and only if k + 3 and 2*k + 3 are primes.

Only the first and the third sentence are formalized here, as one conjunction. The second sentence
(all multiples of 6 are terms, conditionally on Dickson's Conjecture) is a conditional statement on
an open problem and is NOT part of this statement.

Conventions:
* The sequence is stated as a set S of natural numbers (membership predicate), so no offset is
  involved: k is a term iff k ≥ 1 and there is a prime p with p - k and p + k both prime.
* The subtraction p - k is truncated subtraction in ℕ; since a prime is at least 2, primality of
  p - k forces k < p, so it agrees with the integer difference.
* Terms are taken positive (k ≥ 1). The number 0 trivially satisfies the defining condition; both
  formalized sentences are insensitive to whether 0 is counted as a term (0 is even, and 0 is
  divisible by 3, so the equivalence does not concern it).
* Even k is `Even k`, not divisible by 3 is `¬ 3 ∣ k`.

Numerical check: a Python copy of the definition (k ≤ 3000, primes p < 60000) gives
2, 4, 6, 8, 10, 12, 14, 18, 20, 24, 28, 30, 34, 36, 38, 40, 42, 48, 50, 54 for the first 20
elements of S; all terms found are even and the equivalence holds for every even k ≤ 3000 not
divisible by 3. The OEIS DATA field was not available offline for comparison.
-/

namespace OMA.S_oeis_a098807

/-- A098807 as a set: positive k such that some prime p has p - k and p + k both prime. -/
def S : Set ℕ := {k | 1 ≤ k ∧ ∃ p : ℕ, p.Prime ∧ (p - k).Prime ∧ (p + k).Prime}

/-- Israel's comments: all terms are even, and an even k not divisible by 3 is a term iff
k + 3 and 2*k + 3 are primes. -/
theorem main : (∀ k ∈ S, Even k) ∧
    (∀ k : ℕ, Even k → ¬ 3 ∣ k → (k ∈ S ↔ (k + 3).Prime ∧ (2 * k + 3).Prime)) := by
  sorry

end OMA.S_oeis_a098807
