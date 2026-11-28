import Mathlib

/-!
# OEIS A201814: 6 integers in -n..n with sum zero and as many positives as negatives

Source: https://oeis.org/A201814
Credit: Sudharsan Rajendiran

A201814(n) is the number of arrays of 6 integers in `-n..n` with sum zero and equal numbers of
elements greater than zero and less than zero (offset `1`). Colin Barker conjectured (May 2018) the
g.f. `x(141 + 155x + 730x^2 + 150x^3 + 145x^4 - x^5)/(1 - x)^6` and the order-6 linear recurrence with coefficients from `(1 - x)^6`. We
state the g.f. as an identity of formal power series over `ℚ`, after dividing by `x` (the sequence
starts at `n = 1`): `(∑_(n ≥ 0) a(n+1) x^n) (1 - x)^6 = 141 + 155x + 730x^2 + 150x^3 + 145x^4 - x^5`.

Conventions: an array is `v : Fin 6 → ℤ` with entries in `[-n, n]`; the two counts are the numbers of
indices with `v i > 0` and with `v i < 0`.
-/

namespace OMA.S_oeis_a201814

/-- A201814(n): the number of arrays of 6 integers in `-n..n` with sum zero and equal numbers of
elements greater than zero and less than zero. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 6 => Finset.Icc (-(n : ℤ)) n).filter (fun v => ∑ i, v i = 0 ∧
    (Finset.univ.filter (fun i => 0 < v i)).card = (Finset.univ.filter (fun i => v i < 0)).card)).card

open PowerSeries in
/-- Barker's g.f. `x(141 + 155x + 730x^2 + 150x^3 + 145x^4 - x^5)/(1 - x)^6` for the sequence with offset `1`,
divided by `x`: `∑_(n ≥ 0) a(n+1) x^n · (1 - x)^6 = 141 + 155x + 730x^2 + 150x^3 + 145x^4 - x^5`. -/
theorem main :
    (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 6 = 141 + 155 * X + 730 * X ^ 2 + 150 * X ^ 3 + 145 * X ^ 4 - X ^ 5 := by
  sorry

end OMA.S_oeis_a201814
