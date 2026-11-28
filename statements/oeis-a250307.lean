import Mathlib

/-!
# A250307: Number of 2-colored Schroeder paths of semilength n in which there are no (2,0)-steps at level 1.

Source: https://oeis.org/A250307
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 3, 10, 37, 152, 690, 3422, 18257, 103144, ...
The entry gives the generating function
  6/(5-14*x+sqrt(1-8*x+4*x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 4*x^2 - 8*x + 1 the series is, in normalised form,
  (5 - 14*x + (-1)*sqrt(R)) / (32*x^2 - 22*x + 4),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Sep 24 2016) reads
  Conjecture: 2*n*a(n) +3*(-9*n+8)*a(n-1) +4*(28*n-39)*a(n-2) +4*(-43*n+81)*a(n-3) +64*(n-3)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a250307

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 8 * X + 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A250307: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((5 - 14 * X - S)
      * (4 - 22 * X + 32 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A250307. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (2 * (n : ℚ)) * a n + (-27 * (n : ℚ) + 24) * a (n - 1) + (112 * (n : ℚ) - 156) * a (n - 2)
      + (-172 * (n : ℚ) + 324) * a (n - 3) + (64 * (n : ℚ) - 192) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a250307
