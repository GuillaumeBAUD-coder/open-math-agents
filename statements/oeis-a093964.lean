import Mathlib

namespace OMA.S_oeis_a093964

open PowerSeries BigOperators

/-- OEIS A093964: `a(n) = ∑_{k=1}^n k * k! * C(n, k)` (with `a(0) = 0`). -/
def a093964 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, k * Nat.factorial k * Nat.choose n k

/-- Conjecture on OEIS A093964:
The generating function `A(x) = ∑_{n ≥ 0} a(n) x^n` satisfies `1 + x * A(x) = T(0)`
(equivalently `A(x) = T(0)/x - 1/x`), where the family `T : ℕ → ℚ⟦X⟧` satisfies the
continued-fraction recurrence
`T(k) = 1 - x^2 * (k + 1)^2 / (x^2 * (k + 1)^2 - (1 - 2*(k + 1)*x) * (1 - 2*(k + 2)*x) / T(k + 1))`
(expressed without division as
`(x^2 * (k + 1)^2 * T(k + 1) - (1 - 2*(k + 1)*x) * (1 - 2*(k + 2)*x)) * (T(k) - 1) = - x^2 * (k + 1)^2 * T(k + 1)`
with `T(k)(0) = 1`). -/
theorem main :
    ∀ T : ℕ → PowerSeries ℚ,
      (∀ k, PowerSeries.coeff 0 (T k) = 1) →
      (∀ k,
        (PowerSeries.C (((k + 1 : ℕ) : ℚ) ^ 2) * PowerSeries.X ^ 2 * T (k + 1) -
          (1 - PowerSeries.C (2 * ((k + 1 : ℕ) : ℚ)) * PowerSeries.X) *
          (1 - PowerSeries.C (2 * ((k + 2 : ℕ) : ℚ)) * PowerSeries.X)) * (T k - 1) =
        -(PowerSeries.C (((k + 1 : ℕ) : ℚ) ^ 2) * PowerSeries.X ^ 2 * T (k + 1))) →
      T 0 = 1 + PowerSeries.X * PowerSeries.mk (fun n => (a093964 n : ℚ)) := by
  sorry

end OMA.S_oeis_a093964
