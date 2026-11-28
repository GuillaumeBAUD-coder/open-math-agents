import Mathlib

/-!
# A054271: Difference between prime(n)^2 and the previous prime.

Source: https://oeis.org/A054271
Credit: @<your GitHub handle>

The entry records (Jean-Christophe Hervé, Oct 22 2013): "Contains only even numbers, except the
first term. Even integers of the form 3*k+1 (or equivalently integers of form 6*k+4) never appear
[...]. Conjecture: every other even integer appears in the sequence an infinite number of times."

Conventions (please review):
* `a(n) = prime(n)^2 - precprime(prime(n)^2)`, where `precprime(x)` is the largest prime `< x`
  (formula in the entry). Since `n ↦ prime(n)` is a bijection from the indices onto the primes,
  "the value `m` appears infinitely often" means: there are infinitely many primes `p` with
  `p^2 - precprime(p^2) = m`.
* For `m < p^2`, `p^2 - precprime(p^2) = m` holds iff `p^2 - m` is prime and no prime lies strictly
  between `p^2 - m` and `p^2`. We state it in that form, which avoids defining `precprime`.
* "Every other even integer" is read as: every positive even integer `m` with `m % 6 ≠ 4`
  (0 never appears, since `p^2` is not prime).
-/

namespace OMA.S_oeis_a054271

/-- `m` is the difference between `p^2` and the largest prime below `p^2`. -/
def IsGapBelowSq (p m : ℕ) : Prop :=
  m < p ^ 2 ∧ (p ^ 2 - m).Prime ∧ ∀ r : ℕ, p ^ 2 - m < r → r < p ^ 2 → ¬ r.Prime

/-- Hervé's conjecture in OEIS A054271: every positive even integer `m` not of the form `6k+4`
equals `prime(n)^2 - precprime(prime(n)^2)` for infinitely many `n`. -/
theorem main : ∀ m : ℕ, 0 < m → Even m → m % 6 ≠ 4 →
    {p : ℕ | p.Prime ∧ IsGapBelowSq p m}.Infinite := by
  sorry

end OMA.S_oeis_a054271
