import Mathlib

/-!
# A191796: Number of DUU's in all length n left factors of Dyck paths; here U=(1,1) and D=(1,-1).

Source: https://oeis.org/A191796
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 0, 0, 1, 3, 9, 21, 52, ...
The entry gives the generating function
  ((1-3*z^2-z^3)*sqrt(1-4*z^2) -1+5*z^2+z^3-4*z^4)/(2*z*(1-2*z)*sqrt(1-4*z^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (4*x^5 + 12*x^4 - x^3 - 7*x^2 + 1 + (-4*x^4 + x^3 + 5*x^2 - 1)*sqrt(R)) / (16*x^4 - 8*x^3 - 4*x^2 + 2*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: -(n+1)*(2527*n^2+15963*n-146560)*a(n) +(-2527*n^3+68000*n^2-231053*n-293120)*a(n-1) +2*(12635*n^3+906*n^2-429395*n+746484)*a(n-2) +4*(2527*n^3-70527*n^2+316742*n-316524)*a(n-3) -24*(n-5)*(2527*n^2-232*n-28664)*a(n-4)=0
The recurrence fails for n in [4] (small n, where the inhomogeneous part of the differential
equation is felt), so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a191796

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A191796: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((1 - 7 * X ^ 2 - X ^ 3 + 12 * X ^ 4 + 4 * X ^ 5 + (-1 + 5 * X ^ 2 + X ^ 3 - 4 * X ^ 4) * S)
      * (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A191796. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (-2527 * (n : ℚ) ^ 3 - 18490 * (n : ℚ) ^ 2 + 130597 * (n : ℚ) + 146560) * a n
      + (-2527 * (n : ℚ) ^ 3 + 68000 * (n : ℚ) ^ 2 - 231053 * (n : ℚ) - 293120) * a (n - 1)
      + (25270 * (n : ℚ) ^ 3 + 1812 * (n : ℚ) ^ 2 - 858790 * (n : ℚ) + 1492968) * a (n - 2)
      + (10108 * (n : ℚ) ^ 3 - 282108 * (n : ℚ) ^ 2 + 1266968 * (n : ℚ) - 1266096) * a (n - 3)
      + (-60648 * (n : ℚ) ^ 3 + 308808 * (n : ℚ) ^ 2 + 660096 * (n : ℚ) - 3439680) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a191796
