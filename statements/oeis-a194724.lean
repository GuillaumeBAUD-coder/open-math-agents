import Mathlib

/-!
# A194724: Number of quaternary words either empty or beginning with the first character of the alphabet, that can be built by inserting n doublets into the initially empty word.

Source: https://oeis.org/A194724
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 7, 58, 523, 4966, 48838, 492724, 5068915, ...
The entry gives the generating function
  3/4 + 3/(2*(2+4*sqrt(1-12*x)))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 12*x the series is, in normalised form,
  (1 - 24*x + (1)*sqrt(R)) / (2 - 32*x),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Mar 14 2015) reads
  Conjecture: n*a(n) +2*(-14*n+9)*a(n-1) +96*(2*n-3)*a(n-2)=0
The recurrence fails for n in [2] (small n, where the inhomogeneous part of the differential
equation is felt), so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a194724

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 12 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A194724: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 24 * X + S)
      * (2 - 32 * X : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A194724. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℚ) * a n + (-28 * (n : ℚ) + 18) * a (n - 1) + (192 * (n : ℚ) - 288) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a194724
