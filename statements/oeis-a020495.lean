import Mathlib

/-!
# A020495: Hardy and Littlewood's Conjecture H (numbers neither square nor square + prime)

Source: https://oeis.org/A020495
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

## Problem Statement
Let `A020495` be the set of natural numbers that are neither a square nor the sum of a
square and a prime.

Hardy & Littlewood's Conjecture H:
1. The set `A020495` is finite.
2. As `n → ∞` through non-square integers, the number `r(n)` of representations `n = k^2 + p`
   with `k ∈ ℕ` and `p` prime is asymptotic to
   `(√n / log n) * ∏_{p > 2 prime} (1 - (n / p) / (p - 1))`,
   where `(n / p)` is the Legendre symbol.
-/

namespace OMA.S_oeis_a020495

/-- Numbers that are neither a square nor the sum of a square and a prime. -/
def notSquareOrSquarePlusPrime : Set ℕ :=
  { n : ℕ | ¬ IsSquare n ∧ ∀ k p : ℕ, Nat.Prime p → k ^ 2 + p ≠ n }

/-- Number of representations `n = k^2 + p` with `k : ℕ` and `p` prime. -/
noncomputable def repCount (n : ℕ) : ℕ :=
  Nat.card { kp : ℕ × ℕ // Nat.Prime kp.2 ∧ kp.1 ^ 2 + kp.2 = n }

/-- Partial product over primes `2 < p ≤ N` of `1 - (n / p) / (p - 1)`. -/
noncomputable def partialProduct (n N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p),
    (1 - (jacobiSym (n : ℤ) p : ℝ) / ((p : ℝ) - 1))

/-- The Hardy-Littlewood singular series product `∏_{p > 2 prime} (1 - (n / p) / (p - 1))` is
taken as the limit `S n` of the partial products over `p ≤ N` in increasing order (it converges
only conditionally, so an unordered `tprod` would be a junk value). -/
theorem main :
    notSquareOrSquarePlusPrime.Finite ∧
    ∃ S : ℕ → ℝ,
      (∀ n : ℕ, ¬ IsSquare n →
        Filter.Tendsto (partialProduct n) Filter.atTop (nhds (S n))) ∧
      Filter.Tendsto
        (fun n : ℕ =>
          (repCount n : ℝ) / (Real.sqrt (n : ℝ) / Real.log (n : ℝ) * S n))
        (Filter.atTop ⊓ Filter.principal { n : ℕ | ¬ IsSquare n })
        (nhds 1) := by
  sorry

end OMA.S_oeis_a020495
