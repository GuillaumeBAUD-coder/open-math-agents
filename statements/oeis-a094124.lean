import Mathlib

/-!
# A094124: First prime in prime(p) - n, where p is prime and n is even.

Source: https://oeis.org/A094124
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture: This sequence, extended to infinity, contains all odd primes.
-/

namespace OMA.S_oeis_a094124

/-- The `k`-th prime (1-indexed, so `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...). -/
noncomputable def nthPrime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- `q` is the first prime of the form `prime(p) - n` (as `p` runs over primes)
for the even number `n`. -/
def isFirstPrimeForEven (n q : ℕ) : Prop :=
  Even n ∧ ∃ p : ℕ, p.Prime ∧ n < nthPrime p ∧ nthPrime p - n = q ∧ q.Prime ∧
    ∀ p' : ℕ, p'.Prime → p' < p → ¬ (n < nthPrime p' ∧ (nthPrime p' - n).Prime)

theorem main :
    ∀ q : ℕ, q.Prime → Odd q → ∃ n : ℕ, isFirstPrimeForEven n q := by
  sorry

end OMA.S_oeis_a094124
