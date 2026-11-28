import Mathlib

/-!
# A322008: nearest integers to reciprocals of power-tower integral deficits

Source: https://oeis.org/A322008
Credit: @nskath

M. F. Hasler defined this sequence on 2019-03-01. Colin Barker conjectured
the generating function and recurrence below on 2019-03-07.

The integral and nearest-integer rounding are Mathlib's standard real
interval integral and `round`. Half-integer ties use Mathlib's convention;
the sequence values in fact avoid ties. The generating-function identity
is stated after multiplication by its denominator, whose constant term
is 1, so this is equivalent to the source's rational generating function.
Both conjectures are included, with the recurrence valid for n > 11.
-/

namespace OMA.S_oeis_a322008

noncomputable def a (n : ℕ) : ℤ :=
  round (1 / (1 - ∫ x : ℝ in (0 : ℝ)..1, Real.rpow x (x ^ n)))

noncomputable def generatingSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (a n : ℚ))

noncomputable def numerator : PowerSeries ℚ :=
  2 + PowerSeries.X + 2 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 +
    2 * PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 6 +
    2 * PowerSeries.X ^ 7 + PowerSeries.X ^ 9 + PowerSeries.X ^ 10 -
    PowerSeries.X ^ 11

noncomputable def denominator : PowerSeries ℚ :=
  (1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) *
    (1 + PowerSeries.X ^ 2) * (1 + PowerSeries.X ^ 4)

theorem main :
    denominator * generatingSeries = numerator ∧
    ∀ n : ℕ, 11 < n →
      a n = 2 * a (n - 1) - a (n - 2) + a (n - 8) -
        2 * a (n - 9) + a (n - 10) := by
  sorry

end OMA.S_oeis_a322008
