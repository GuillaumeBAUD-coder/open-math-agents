import Mathlib

/-!
# OEIS A201815: 7 integers in -n..n with sum zero and as many positives as negatives

Source: https://oeis.org/A201815
Credit: Sudharsan Rajendiran

A201815(n) is the number of arrays of 7 integers in `-n..n` with sum zero and equal numbers of
elements greater than zero and less than zero (offset `1`). Colin Barker conjectured (May 2018) the
g.f. `x(393 + 1787x + 4882x^2 + 1782x^3 + 397x^4 - x^5)/(1 - x)^6` and the order-6 linear recurrence with coefficients from `(1 - x)^6`. We
state the g.f. as an identity of formal power series over `ℚ`, after dividing by `x` (the sequence
starts at `n = 1`): `(∑_(n ≥ 0) a(n+1) x^n) (1 - x)^6 = 393 + 1787x + 4882x^2 + 1782x^3 + 397x^4 - x^5`.

Conventions: an array is `v : Fin 7 → ℤ` with entries in `[-n, n]`; the two counts are the numbers of
indices with `v i > 0` and with `v i < 0`.
-/

namespace OMA.S_oeis_a201815

/-- A201815(n): the number of arrays of 7 integers in `-n..n` with sum zero and equal numbers of
elements greater than zero and less than zero. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 7 => Finset.Icc (-(n : ℤ)) n).filter (fun v => ∑ i, v i = 0 ∧
    (Finset.univ.filter (fun i => 0 < v i)).card = (Finset.univ.filter (fun i => v i < 0)).card)).card

open PowerSeries in
/-- Barker's g.f. `x(393 + 1787x + 4882x^2 + 1782x^3 + 397x^4 - x^5)/(1 - x)^6` for the sequence with offset `1`,
divided by `x`: `∑_(n ≥ 0) a(n+1) x^n · (1 - x)^6 = 393 + 1787x + 4882x^2 + 1782x^3 + 397x^4 - x^5`. -/
theorem main :
    (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 6 = 393 + 1787 * X + 4882 * X ^ 2 + 1782 * X ^ 3 + 397 * X ^ 4 - X ^ 5 := by
  sorry

end OMA.S_oeis_a201815
