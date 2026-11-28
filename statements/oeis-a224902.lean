import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a224902

/-- Sum of divisors `σ(m)`. -/
def sigma (m : ℕ) : ℕ :=
  ∑ d ∈ m.divisors, d

/-- Coefficient weight `w(n) = σ(2 * n^4) - σ(n^4)` in the logarithmic generating function. -/
def w224902 (n : ℕ) : ℕ :=
  sigma (2 * n ^ 4) - sigma (n ^ 4)

/-- Coefficients of `exp(∑_{k ≥ 1} u(k) * x^k / k)` computed recursively via
`a(0) = 1` and `a(n + 1) = (1 / (n + 1)) * ∑_{k = 0}^{n} u(k + 1) * a(n - k)`. -/
def expLogSeq (u : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
    (∑ k ∈ Finset.range (n + 1), u (k + 1) * expLogSeq u (n - k)) / ((n + 1 : ℕ) : ℚ)

/-- OEIS A224902: `n`-th coefficient of `exp(∑_{k ≥ 1} (σ(2*k^4) - σ(k^4)) * x^k / k)`. -/
def a224902 (n : ℕ) : ℚ :=
  expLogSeq (fun k => (w224902 k : ℚ)) n

/-- OEIS A224902 conjecture:
For every `n ≥ 1`, `a(n)` is an integer satisfying `a(n) ≡ 2 (mod 4)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, a224902 n = (m : ℚ) ∧ m % 4 = 2 := by
  sorry

end OMA.S_oeis_a224902
