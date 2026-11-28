import Mathlib

/-!
# Erdős Problem 256

Source: https://www.erdosproblems.com/256
Credit: Sudharsan Rajendiran

Let `n ≥ 1` and let `f(n)` be maximal such that for any integers `1 ≤ a_1 ≤ ⋯ ≤ a_n`,
`max_{|z| = 1} |∏_i (1 - z^{a_i})| ≥ f(n)`. Is there a constant `c > 0` such that
`log f(n) ≫ n^c`?

As noted on the problem page, the answer is negative: Belov and Konyagin proved
`log f(n) ≪ (log n)^4`. We state that negative answer: there are no constants `c > 0` and
`C > 0` with `log f(n) ≥ C n^c` for all sufficiently large `n`.

Conventions:
- `f(n)` is the infimum, over all non-decreasing `a : Fin n → ℕ` with every `a i ≥ 1`, of
  `max_{|z| = 1} |∏_i (1 - z^{a i})|`. The largest `f(n)` with the stated property is exactly
  this infimum. The maximum over the unit circle exists (a continuous function on a compact
  set), so it is written as a supremum over `Metric.sphere 0 1`.
- `log f(n) ≫ n^c` means `log f(n) ≥ C · n^c` for some `C > 0` and all large `n`. (Known lower
  bounds give `f(n) > 1` for `n ≥ 1`, so `log f(n)` is the honest logarithm.)
-/

namespace OMA.S_erdos_256

open Filter

/-- `max_{|z| = 1} |∏_i (1 - z^{a i})|`. -/
noncomputable def circleMax {n : ℕ} (a : Fin n → ℕ) : ℝ :=
  sSup ((fun z : ℂ => ‖∏ i, (1 - z ^ (a i))‖) '' Metric.sphere (0 : ℂ) 1)

/-- `f(n)`: the largest lower bound for `circleMax a` over non-decreasing `a` with all
terms at least `1`. -/
noncomputable def f (n : ℕ) : ℝ :=
  sInf {M : ℝ | ∃ a : Fin n → ℕ, Monotone a ∧ (∀ i, 1 ≤ a i) ∧ M = circleMax a}

/-- Erdős Problem 256 has a negative answer: `log f(n)` is not `≫ n^c` for any `c > 0`. -/
theorem main : ¬ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ c ≤ Real.log (f n) := by
  sorry

end OMA.S_erdos_256
