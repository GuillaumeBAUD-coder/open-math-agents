import Mathlib

namespace OMA.S_oeis_a189359

/-- The `m`-th Zagier-Fishburn factor product `∏_{j=1}^m (1 - (1 - X)^j)` over `PowerSeries ℚ`. -/
noncomputable def fishburnProd (m : ℕ) : PowerSeries ℚ :=
  ∏ j ∈ Finset.range m, (1 - (1 - PowerSeries.X) ^ (j + 1))

/-- The shifted Fishburn generating function `∑_{m ≥ 1} ∏_{j=1}^m (1 - (1 - X)^j)`.
Since `1 - (1 - X)^j` has zero constant term for every `j ≥ 1`, the `m`-th product has
zero `n`-th coefficient whenever `m > n`, so the sum truncates at `m = n`. -/
noncomputable def fishburnShiftGF : PowerSeries ℚ :=
  PowerSeries.mk (fun n => ∑ m ∈ Finset.range n, PowerSeries.coeff n (fishburnProd (m + 1)))

/-- The continued fraction recurrence for OEIS A189359:
`Q(k) = 1 + (1 - (1-x)^(2*k+2)) / (1 - (1 - (1-x)^(2*k+3)) / (1 - (1-x)^(2*k+3) + 1/Q(k+1)))`,
expressed in cleared-denominator form over `PowerSeries ℚ` with `Q(k)(0) = 1`. -/
def IsCF189359 (Q : ℕ → PowerSeries ℚ) : Prop :=
  ∀ k : ℕ,
    PowerSeries.coeff 0 (Q k) = 1 ∧
    ∃ D1 D2 : PowerSeries ℚ,
      PowerSeries.coeff 0 D2 = 1 ∧
      PowerSeries.coeff 0 D1 = 1 ∧
      D2 * Q (k + 1) = (1 - (1 - PowerSeries.X) ^ (2 * k + 3)) * Q (k + 1) + 1 ∧
      D1 * D2 = D2 - (1 - (1 - PowerSeries.X) ^ (2 * k + 3)) ∧
      (Q k - 1) * D1 = 1 - (1 - PowerSeries.X) ^ (2 * k + 2)

/-- OEIS A189359 conjecture (d=55):
The generating function `A(x) = (1/(1-x)) * ∑_{m ≥ 1} ∏_{j=1}^m (1 - (1-x)^j)` of
homogeneous games for `n` players (partial sums of Fishburn numbers) equals
`Q(0) * x / (1 - x)`, where `Q(k)` satisfies the continued fraction `IsCF189359`.
Equivalently, `Q 0 * X = fishburnShiftGF`, so any `A` with `(1 - X) * A = Q 0 * X`
satisfies `(1 - X) * A = fishburnShiftGF`. -/
theorem main :
    ∀ (Q : ℕ → PowerSeries ℚ) (A : PowerSeries ℚ),
      IsCF189359 Q →
      (1 - PowerSeries.X) * A = Q 0 * PowerSeries.X →
      (1 - PowerSeries.X) * A = fishburnShiftGF := by
  sorry

end OMA.S_oeis_a189359
