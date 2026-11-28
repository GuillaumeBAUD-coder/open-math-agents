import Mathlib

/-!
# A042220: Numerators of continued fraction convergents to sqrt(636).

Source: https://oeis.org/A042220
Credit: @physbuzz

Conjecture (Harvey P. Dale, May 08 2022): the sequence satisfies a linear recurrence with
signature (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7011902, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1),
that is, `a(n) = 7011902 * a(n-12) - a(n-24)`.

Conventions:
* `a n` is the numerator of the `n`-th convergent of the simple continued fraction of
  `sqrt 636`, taken from Mathlib's `GenContFract.of`; the offset is 0, so
  `a 0 = 25, a 1 = 101, a 2 = 126, ...`, as in the OEIS data.
* The recurrence is stated for every index, written with `n + 24` in place of `n`.
-/

namespace OMA.S_oeis_a042220

/-- A042220: numerators of the continued fraction convergents to `sqrt 636` (offset 0). -/
noncomputable def a (n : ℕ) : ℝ := (GenContFract.of (Real.sqrt 636)).nums n

/-- The sequence satisfies the linear recurrence with signature
`(0^11, 7011902, 0^11, -1)`. -/
theorem main : ∀ n : ℕ, a (n + 24) = 7011902 * a (n + 12) - a n := by
  sorry

end OMA.S_oeis_a042220
