import Mathlib

namespace OMA.S_oeis_a230961

/-- Formal power series `cos(X) = ∑_{m ≥ 0} (-1)^m X^(2m) / (2m)!`. -/
noncomputable def cosPS : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    if n % 2 = 0 then ((-1 : ℚ) ^ (n / 2)) / ((Nat.factorial n : ℕ) : ℚ) else 0

/-- Formal power series `sin(X) = ∑_{m ≥ 0} (-1)^m X^(2m+1) / (2m+1)!`. -/
noncomputable def sinPS : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    if n % 2 = 1 then ((-1 : ℚ) ^ (n / 2)) / ((Nat.factorial n : ℕ) : ℚ) else 0

/-- The continued fraction recurrence for OEIS A230961:
`Q(k) = 2*(4*k+1)*(32*k^2+16*k - X^2 - 6) - X^4*(4*k-1)*(4*k+7)/Q(k+1)`,
expressed in cleared-denominator form over `PowerSeries ℚ` with
`Q(k)(0) = 2*(4*k+1)*(32*k^2+16*k - 6)`. -/
def IsCF230961 (Q : ℕ → PowerSeries ℚ) : Prop :=
  ∀ k : ℕ,
    PowerSeries.coeff 0 (Q k) =
      2 * (4 * (k : ℚ) + 1) * (32 * (k : ℚ) ^ 2 + 16 * (k : ℚ) - 6) ∧
    Q k * Q (k + 1) =
      (PowerSeries.C (2 * (4 * (k : ℚ) + 1)) *
        (PowerSeries.C (32 * (k : ℚ) ^ 2 + 16 * (k : ℚ) - 6) - PowerSeries.X ^ 2)) *
        Q (k + 1) -
      PowerSeries.C ((4 * (k : ℚ) - 1) * (4 * (k : ℚ) + 7)) * PowerSeries.X ^ 4

/-- OEIS A230961 conjecture:
`E.g.f.: (tan(x) + sec(x)) / (1 - 2*x + x^2) = (1 - 12*x / (Q(0) + 6*x + 3*x^2)) / (1 - x)^2`,
where `Q(k)` satisfies `IsCF230961`.
In cleared-denominator form over `PowerSeries ℚ`:
`cos(X) * (Q(0) + 6*X + 3*X^2 - 12*X) = (1 + sin(X)) * (Q(0) + 6*X + 3*X^2)`
(equivalently, if `E` satisfies `(1 - X)^2 * cos(X) * E = 1 + sin(X)`, then
`(1 - X)^2 * (Q(0) + 6*X + 3*X^2) * E = Q(0) - 6*X + 3*X^2`). -/
theorem main :
    ∀ (Q : ℕ → PowerSeries ℚ) (E : PowerSeries ℚ),
      IsCF230961 Q →
      (1 - PowerSeries.X) ^ 2 * cosPS * E = 1 + sinPS →
      (1 - PowerSeries.X) ^ 2 *
        (Q 0 + PowerSeries.C 6 * PowerSeries.X + PowerSeries.C 3 * PowerSeries.X ^ 2) * E =
        Q 0 + PowerSeries.C 6 * PowerSeries.X + PowerSeries.C 3 * PowerSeries.X ^ 2 -
          PowerSeries.C 12 * PowerSeries.X := by
  sorry

end OMA.S_oeis_a230961
