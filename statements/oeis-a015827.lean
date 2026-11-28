import Mathlib

/-!
# A015827: Numbers k such that phi(k + 9) | sigma(k)

Source: https://oeis.org/A015827

Conjecture (OEIS A015827):
There are infinitely many positive integers `k` such that `φ(k + 9) ∣ σ(k)`.
(In particular, Dickson's conjecture implies this sequence is infinite, as it
includes `6 * A023204`.)

Conventions:
- Offset: `1`; first terms: `3, 5, 7, 10, 15, 21, 24, 30, 31, 33, ...`.
- `φ` is Euler's totient function (`Nat.totient`) and `σ(k)` is the sum of
  positive divisors of `k` (`(Nat.divisors k).sum id`).
-/

namespace OMA.S_oeis_a015827

/-- The set of positive integers `k` such that `φ(k + 9)` divides `σ(k)` (OEIS A015827). -/
def S : Set ℕ :=
  {k : ℕ | 1 ≤ k ∧ Nat.totient (k + 9) ∣ (Nat.divisors k).sum id}

/-- Conjecture: there are infinitely many positive integers `k` with `φ(k + 9) ∣ σ(k)`. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a015827
