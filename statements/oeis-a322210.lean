import Mathlib

namespace OMA.S_oeis_a322210

/-- Truncated bivariate generating function `P_N(x, y) = ∏_{m=1}^N 1 / (1 - (x^m + y^m))`
over `PowerSeries (PowerSeries ℚ)`, where outer `X` is `x` and inner `X` is `y`. -/
noncomputable def P_trunc (N : ℕ) : PowerSeries (PowerSeries ℚ) :=
  ∏ m ∈ Finset.Icc 1 N,
    Ring.inverse (1 - (PowerSeries.X ^ m + PowerSeries.C (PowerSeries.X ^ m)))

/-- Square table `T(a, b) = [x^a y^b] ∏_{m ≥ 1} 1 / (1 - (x^m + y^m))` of OEIS A322210.
Factors with `m > a + b` contribute only `1` to `[x^a y^b]`, so truncating at `N = a + b` is exact. -/
noncomputable def T_sq (a b : ℕ) : ℚ :=
  PowerSeries.coeff b (PowerSeries.coeff a (P_trunc (a + b)))

/-- Number of ways to form the subsum `k` from a partition `p : Nat.Partition n`
(treating the `r_m = p.parts.count m` copies of part `m` as distinguishable slots,
so choosing `s_m` of the `r_m` copies of `m` contributes `Nat.choose r_m s_m` ways). -/
def subsumWays (n k : ℕ) (p : Nat.Partition n) : ℕ :=
  ∑ s ∈ Fintype.piFinset (fun i : Fin n => Finset.range (p.parts.count (i.1 + 1) + 1)),
    if (∑ i : Fin n, (i.1 + 1) * s i) = k then
      ∏ i : Fin n, (p.parts.count (i.1 + 1)).choose (s i)
    else 0

/-- OEIS A322210 Conjecture 1:
For all integers `0 ≤ k ≤ n`, the triangular table entry `T(n - k, k)` equals the total
number of ways to form the subsum `k` from the partitions of `n`. -/
theorem main :
    ∀ n k : ℕ, k ≤ n →
      T_sq (n - k) k = ((∑ p : Nat.Partition n, subsumWays n k p : ℕ) : ℚ) := by
  sorry

end OMA.S_oeis_a322210
