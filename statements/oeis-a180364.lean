import Mathlib

/-!
# A180364: a(n) = Sum_{k=0..n} C(n,k) C(n+k,k) (2k+1)^2 (Sun's monotonicity conjecture)

Source: https://oeis.org/A180364 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A180364 (offset 0): a(n) = sum_{k=0..n} C(n,k)*C(n+k,k)*(2*k+1)^2; data 1, 19, 205, 1839, ...
(a(1) = 1 + 2*3^2 = 19).

The entry records:

  Conjecture: The sequence a(n+1)/a(n) (n = 0,1,...) is strictly decreasing to the limit
  3+2*sqrt(2), and the sequence a(n+1)^(1/(n+1))/a(n)^(1/n) (n = 1,2,3,..) is strictly
  increasing to the limit 1.

Reading of the source:
* `r n = a(n+1)/a(n)` for `n ≥ 0`, and `s n = a(n+1)^(1/(n+1)) / a(n)^(1/n)` for `n ≥ 1`, as real
  numbers (all terms are positive; the roots are real powers).
* "strictly decreasing to the limit L": `r (n+1) < r n` for every `n ≥ 0`, and `r n → L`.
* "strictly increasing to the limit 1": `s n < s (n+1)` for every `n ≥ 1`, and `s n → 1`.
-/

namespace OMA.S_oeis_a180364

open Filter Topology

/-- A180364(n) = ∑_{k=0}^{n} C(n,k) C(n+k,k) (2k+1)^2. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * (n + k).choose k * (2 * k + 1) ^ 2

/-- `a(n+1)/a(n)`. -/
noncomputable def r (n : ℕ) : ℝ := (a (n + 1) : ℝ) / a n

/-- `a(n+1)^(1/(n+1)) / a(n)^(1/n)`. -/
noncomputable def s (n : ℕ) : ℝ :=
  (a (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1)) / (a n : ℝ) ^ ((1 : ℝ) / n)

/-- Sun's conjecture: `a(n+1)/a(n)` decreases strictly to `3 + 2√2`, and
`a(n+1)^(1/(n+1)) / a(n)^(1/n)` (n ≥ 1) increases strictly to 1. -/
theorem main :
    (∀ n : ℕ, r (n + 1) < r n) ∧ Tendsto r atTop (𝓝 (3 + 2 * Real.sqrt 2)) ∧
      (∀ n : ℕ, 1 ≤ n → s n < s (n + 1)) ∧ Tendsto s atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a180364
