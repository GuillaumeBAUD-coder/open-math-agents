import Mathlib

/-!
# Erdős Problem 431 (Ostmann's conjecture / inverse Goldbach problem)

Source: https://www.erdosproblems.com/431
Credit: @joshuadc11

Are there two infinite sets `A` and `B` of natural numbers such that `A + B` agrees with
the set of prime numbers up to finitely many exceptions?
The source notes that the answer is conjectured to be no (Ostmann's conjecture).

Formalization notes:
- `A + B` is the pointwise sumset in `Set ℕ` (`open scoped Pointwise`).
- Agreeing with the set of primes up to finitely many exceptions is stated as
  `(symmDiff (A + B) {p : ℕ | p.Prime}).Finite`.
- Stated in the conjectured negative form (no such infinite sets `A, B` exist).
-/

namespace OMA.S_erdos_431

open scoped Pointwise

theorem main :
    ¬ ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧
      (symmDiff (A + B) {p : ℕ | p.Prime}).Finite := by
  sorry

end OMA.S_erdos_431
