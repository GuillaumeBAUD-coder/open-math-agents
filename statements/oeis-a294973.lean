import Mathlib

/-!
# A294973: Denominators of the continued fraction convergents to sqrt(7)/2.

Source: https://oeis.org/A294973
Credit: @physbuzz

Conjectures (Colin Barker, Nov 19 2017), from the formula section of the source:
* G.f.: `(1 + 3*x - x^2)*(1 + 32*x^2 + x^4) / ((1 - 16*x^2 + x^4)*(1 + 16*x^2 + x^4))`.
* `a(n) = 254*a(n-4) - a(n-8)` for `n > 7`.

Conventions:
* `a n` is the denominator of the `n`-th convergent of the simple continued fraction of
  `sqrt 7 / 2`, taken from Mathlib's `GenContFract.of`; the offset is 0, so
  `a 0 = 1, a 1 = 3, a 2 = 31, a 3 = 96, ...`, as in the OEIS data.
* The recurrence is written with `n + 8` in place of `n`, so it covers every `n > 7`.
* The generating function is stated as an identity of formal power series over `ℝ`:
  the series of `a` times the denominator equals the numerator.
-/

namespace OMA.S_oeis_a294973

open PowerSeries

/-- A294973: denominators of the continued fraction convergents to `sqrt 7 / 2` (offset 0). -/
noncomputable def a (n : ℕ) : ℝ := (GenContFract.of (Real.sqrt 7 / 2)).dens n

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, a (n + 8) = 254 * a (n + 4) - a n) ∧
    PowerSeries.mk a * ((1 - 16 * X ^ 2 + X ^ 4) * (1 + 16 * X ^ 2 + X ^ 4)) =
      (1 + 3 * X - X ^ 2) * (1 + 32 * X ^ 2 + X ^ 4) := by
  sorry

end OMA.S_oeis_a294973
