import Mathlib

namespace OMA.S_oeis_a212344

/-- The continued fraction recurrence for OEIS A212344:
`T(k) = 2*x*(2*k+1) + (k+2) - 2*x*(k+2)*(2*k+3)/T(k+1)`,
expressed in cleared-denominator form over `PowerSeries ℚ` with `T(k)(0) = k + 2`. -/
def IsCF212344 (T : ℕ → PowerSeries ℚ) : Prop :=
  ∀ k : ℕ,
    PowerSeries.coeff 0 (T k) = (k : ℚ) + 2 ∧
    T k * T (k + 1) =
      (PowerSeries.C ((k : ℚ) + 2) + PowerSeries.C (2 * (2 * (k : ℚ) + 1)) * PowerSeries.X) *
        T (k + 1) -
      PowerSeries.C (2 * ((k : ℚ) + 2) * (2 * (k : ℚ) + 3)) * PowerSeries.X

/-- OEIS A212344 continued-fraction conjecture:
`5 * (1 - sqrt(1 - 4*x)) / (2*x) = 10 / T(0)`, where
`T(k) = 2*x*(2*k+1) + k+2 - 2*x*(k+2)*(2*k+3)/T(k+1)`.
Formally, for any `T` satisfying `IsCF212344 T` and `A` with `A * T 0 = C 10`,
`A` is the generating function `5 * ∑_n (C(2n, n)/(n+1)) * x^n` and satisfies
`x * A^2 - 5 * A + 25 = 0`. -/
theorem main :
    ∀ (T : ℕ → PowerSeries ℚ) (A : PowerSeries ℚ),
      IsCF212344 T →
      A * T 0 = PowerSeries.C 10 →
      A = PowerSeries.mk (fun n => 5 * (Nat.centralBinom n : ℚ) / ((n : ℚ) + 1)) ∧
      PowerSeries.X * A ^ 2 - PowerSeries.C 5 * A + PowerSeries.C 25 = 0 := by
  sorry

end OMA.S_oeis_a212344
