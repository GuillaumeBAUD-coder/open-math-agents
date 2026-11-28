import Mathlib

/-!
# OEIS A201813: 5 integers in -n..n with sum zero and as many positives as negatives

Source: https://oeis.org/A201813
Credit: Sudharsan Rajendiran

A201813(n) is the number of arrays of 5 integers in `-n..n` with sum zero and equal numbers of
elements greater than zero and less than zero (offset `1`). Colin Barker conjectured (May 2018) the
g.f. `x(51 + 17x + 53x^2 - x^3)/(1 - x)^4` and the recurrence
`a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) - a(n-4)` for `n > 4`. We state the g.f. as an identity of formal
power series over `ℚ`, after dividing by `x` (the sequence starts at `n = 1`):
`(∑_(n ≥ 0) a(n+1) x^n) (1 - x)^4 = 51 + 17x + 53x^2 - x^3`.

Conventions: an array is `v : Fin 5 → ℤ` with entries in `[-n, n]`; the two counts are the numbers of
indices with `v i > 0` and with `v i < 0`.
-/

namespace OMA.S_oeis_a201813

/-- A201813(n): the number of arrays of 5 integers in `-n..n` with sum zero and equal numbers of
elements greater than zero and less than zero. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 5 => Finset.Icc (-(n : ℤ)) n).filter (fun v => ∑ i, v i = 0 ∧
    (Finset.univ.filter (fun i => 0 < v i)).card = (Finset.univ.filter (fun i => v i < 0)).card)).card

open PowerSeries in
/-- Barker's g.f. `x(51 + 17x + 53x^2 - x^3)/(1 - x)^4` for the sequence with offset `1`,
divided by `x`: `∑_(n ≥ 0) a(n+1) x^n · (1 - x)^4 = 51 + 17x + 53x^2 - x^3`. -/
theorem main :
    (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 4 = 51 + 17 * X + 53 * X ^ 2 - X ^ 3 := by
  sorry

end OMA.S_oeis_a201813
