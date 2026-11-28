import Mathlib

/-!
# A108630: Expansion of g.f. (1+x-sqrt(1-2*x-7*x^2-8*x^3-4*x^4))/(2*(1+x+x^2))

Source: https://oeis.org/A108630
Credit: @xor2k
Sibling of OEIS A108629 (same conjecture wording); statement modelled on the accepted one for that entry.

Formalizes the conjecture of R. J. Mathar (Sep 27 2014) recorded in OEIS A108630:
Conjecture D-finite with recurrence: (n-1)*a(n) = (n-4)*a(n-1) +8*(n-4)*a(n-2) +(17*n-77)*a(n-3)
+(19*n-100)*a(n-4) +12*(n-6)*a(n-5) +4*(n-7)*a(n-6).

Conventions: `a n` is the coefficient of `x^n` in the generating function, computed in `ℚ⟦X⟧`. The
OEIS offset is 1 and the g.f. has constant term 0, so `a 1 = 1, a 2 = 1, a 3 = 2, a 4 = 6, ...` match
the listed data with the same indices. The square root is the binomial series with exponent one half
substituted into the radicand minus one, i.e. the branch with constant coefficient 1; division by
`2*(1+x+x^2)` is multiplication by its power-series inverse. The recurrence is stated for every
`n ≥ 7`, the indices at which all terms `a(n-6), ..., a(n)` lie in the OEIS range `n ≥ 1`.
-/

namespace OMA.S_oeis_a108630

open PowerSeries

/-- The radicand minus its constant term: `-2*x - 7*x^2 - 8*x^3 - 4*x^4`. -/
noncomputable def radicandTail : PowerSeries ℚ :=
  -2 * X - 7 * X ^ 2 - 8 * X ^ 3 - 4 * X ^ 4

/-- `sqrt(1 - 2*x - 7*x^2 - 8*x^3 - 4*x^4)`, the branch with constant coefficient `1`. -/
noncomputable def rootSeries : PowerSeries ℚ :=
  PowerSeries.subst radicandTail (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ))

/-- The generating function `(1+x-sqrt(1-2*x-7*x^2-8*x^3-4*x^4))/(2*(1+x+x^2))`. -/
noncomputable def series : PowerSeries ℚ :=
  (1 + X - rootSeries) * (2 * (1 + X + X ^ 2))⁻¹

/-- `a n` is the coefficient of `x^n`; OEIS lists it from `n = 1` (and `a 0 = 0`). -/
noncomputable def a (n : ℕ) : ℚ := PowerSeries.coeff n series

/-- Mathar's conjectured recurrence, at every `n` for which all indices `n-6, ..., n` are `≥ 1`. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    ((n : ℚ) - 1) * a n =
      ((n : ℚ) - 4) * a (n - 1) + 8 * ((n : ℚ) - 4) * a (n - 2) +
      (17 * (n : ℚ) - 77) * a (n - 3) + (19 * (n : ℚ) - 100) * a (n - 4) +
      12 * ((n : ℚ) - 6) * a (n - 5) + 4 * ((n : ℚ) - 7) * a (n - 6) := by
  sorry

end OMA.S_oeis_a108630
