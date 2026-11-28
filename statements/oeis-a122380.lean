import Mathlib

/-!
# A122380: Numbers k such that k^2 > P(k)!, where P(k) is the greatest prime factor of k.

Source: https://oeis.org/A122380
Credit: @luciusacarr

The entry's comments record one conjecture: k^2 < P(k)! for almost all k.

Reading of the source:
* `P(k)` is the greatest prime factor of `k`, written `k.primeFactors.sup id`. For `k = 1` this
  is `0` (OEIS uses `P(1) = 1`); either way `P(1)! = 1` and `1^2 < 1` fails, and a single `k`
  does not affect a density.
* "Almost all k" is read in the standard sense of natural density: the proportion of
  `k ∈ {1, ..., N}` with `k^2 < P(k)!` tends to `1` as `N → ∞`.
-/

namespace OMA.S_oeis_a122380

open Filter Topology

/-- The greatest prime factor of `k` (`0` for `k ≤ 1`). -/
def P (k : ℕ) : ℕ := k.primeFactors.sup id

theorem main :
    Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun k => k ^ 2 < (P k).factorial)).card : ℝ) / N)
      atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a122380
