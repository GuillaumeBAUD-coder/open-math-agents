import Mathlib

/-!
# A211338: numbers k with tau(k) ≡ 2 (mod 3) have density 3*zeta(3)/Pi^2

Source: https://oeis.org/A211338 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A211338 (offset 1): numbers k for which the number of divisors, tau(k), is congruent to 2 modulo
3; data 2, 3, 5, 7, 11, 13, 16, 17, 19, 23, ...

The entry records:

  The numbers of terms not exceeding 10^k, for k = 1, 2, ..., are 4, 37, 368, 3681, 36596, ...
  Conjecture: the asymptotic density of this sequence exists and equals
  3*zeta(3)/Pi^2 = 0.3653814847007... (A346602), so, a(n) ~ k*n with
  k = Pi^2/(3*zeta(3)) = 2.73686555524... .

(The entry also records an older, different conjectured constant, 2.7290077..., from Charles R
Greathouse IV, Apr 13 2012; the data favour the one above, which is the one stated here.)

Reading of the source:
* `tau k` is the number of divisors of `k` (`k.divisors.card`), for `k ≥ 1`.
* "The asymptotic density exists and equals c": the proportion of `k ∈ {1, ..., N}` with
  `tau k ≡ 2 (mod 3)` tends to `c` as `N → ∞`. (This is equivalent to the stated `a(n) ~ n / c`.)
* `zeta(3) = ∑_{n ≥ 1} 1/n^3`, written as a real series.
-/

namespace OMA.S_oeis_a211338

open Filter Topology

/-- The number of `k ≤ N` (with `k ≥ 1`) whose number of divisors is `≡ 2 (mod 3)`. -/
def count (N : ℕ) : ℕ := ((Finset.Icc 1 N).filter (fun k => k.divisors.card % 3 = 2)).card

/-- `ζ(3) = ∑_{n ≥ 1} 1/n^3`. -/
noncomputable def zeta3 : ℝ := ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 3

/-- The conjecture: the density is `3 ζ(3) / π^2`. -/
theorem main :
    Tendsto (fun N : ℕ => (count N : ℝ) / N) atTop (𝓝 (3 * zeta3 / Real.pi ^ 2)) := by
  sorry

end OMA.S_oeis_a211338
