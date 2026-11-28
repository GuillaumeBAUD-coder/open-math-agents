import Mathlib

/-!
# A053254: Coefficients of the '3rd-order' mock theta function nu(q).

Source: https://oeis.org/A053254
Credit: @<your GitHub handle>

The entry records the conjecture (Peter Bala, Jan 03 2025):
"a(n) = (-1)^n * (A376628(n) + A376628(n+1)), or equivalently, (1 + q * nu(-q))/(1 + q) =
Sum_{n >= 0} q^(n*(n+1))/((1 - q)*(1 - q^3)*...*(1 - q^(2*n-1))), the g.f. of A376628."

Conventions (please review):
* `a(n)` (A053254, offset 0: `1, -1, 2, -2, 2, -3, 4, ...`) is the coefficient of `q^n` in Ramanujan's
  third-order mock theta function
  `nu(q) = Sum_{k >= 0} q^(k(k+1)) / ((1+q)(1+q^3)...(1+q^(2k+1)))`.
* A376628(n) (offset 0: `1, 0, 1, 1, 1, 1, 2, ...`) is the coefficient of `x^n` in
  `Sum_{k >= 0} x^(k(k+1)) / Prod_{j=1..k} (1 - x^(2j-1))`.
* Both are infinite sums of formal power series; each summand is computed in `ℚ⟦X⟧` (the
  denominators have constant coefficient `1`, so `⁻¹` is the true inverse). The `k`-th summand is
  divisible by `X^(k(k+1))`, so the coefficient of `X^m` only receives contributions from
  `k ≤ m`; we define the `m`-th coefficient as the finite sum over `k ∈ {0, ..., m}`.
* We state the first form, `a(n) = (-1)^n (A376628(n) + A376628(n+1))`, for all `n ≥ 0`.
-/

namespace OMA.S_oeis_a053254

open PowerSeries

/-- The `k`-th summand of `nu(q)`: `q^(k(k+1)) / Prod_{j=0..k} (1 + q^(2j+1))`. -/
noncomputable def nuTerm (k : ℕ) : ℚ⟦X⟧ :=
  X ^ (k * (k + 1)) * (∏ j ∈ Finset.range (k + 1), (1 + X ^ (2 * j + 1)))⁻¹

/-- A053254: the coefficient of `q^m` in `nu(q)`. -/
noncomputable def a053254 (m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (m + 1), coeff m (nuTerm k)

/-- The `k`-th summand of the g.f. of A376628: `x^(k(k+1)) / Prod_{j=1..k} (1 - x^(2j-1))`. -/
noncomputable def gTerm (k : ℕ) : ℚ⟦X⟧ :=
  X ^ (k * (k + 1)) * (∏ j ∈ Finset.Icc 1 k, (1 - X ^ (2 * j - 1)))⁻¹

/-- A376628: the coefficient of `x^m` in `Sum_{k >= 0} x^(k(k+1)) / Prod_{j=1..k} (1 - x^(2j-1))`. -/
noncomputable def a376628 (m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (m + 1), coeff m (gTerm k)

/-- Bala's conjecture in OEIS A053254: `a(n) = (-1)^n * (A376628(n) + A376628(n+1))`. -/
theorem main : ∀ n : ℕ, a053254 n = (-1) ^ n * (a376628 n + a376628 (n + 1)) := by
  sorry

end OMA.S_oeis_a053254
