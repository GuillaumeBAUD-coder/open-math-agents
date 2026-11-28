import Mathlib

/-!
# OEIS A199899: 4 integers in -n..n with sum zero and no two adjacent ones of the same strict sign

Source: https://oeis.org/A199899
Credit: Sudharsan Rajendiran

A199899(n) is the number of arrays `x(0..3)` of 4 integers in `-n..n` with zero sum, and adjacent
elements not both strictly positive and not both strictly negative (offset `1`). Colin Barker
conjectured (Feb 2018) the g.f. `x(3 - x)(5 - 2x + x^2)/(1 - x)^4` and the recurrence
`a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) - a(n-4)` for `n > 4`. We state the g.f. as an identity of formal
power series over `ℚ`, with the denominator multiplied across:
`(∑_(n ≥ 1) a(n) x^n) (1 - x)^4 = x(3 - x)(5 - 2x + x^2)`.
The definition also gives `a(0) = 1` (the zero array), which the g.f. does not describe, so the
coefficient of `x^0` on the left is taken to be `0`.

Conventions: an array is `v : Fin 4 → ℤ` with entries in `[-n, n]`; the condition is required for the
three pairs `(v i, v (i+1))`, `i = 0, 1, 2`.
-/

namespace OMA.S_oeis_a199899

/-- A199899(n): the number of arrays `x(0..3)` of 4 integers in `-n..n` with zero sum and adjacent
elements not both strictly positive and not both strictly negative. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(n : ℤ)) n).filter (fun v => ∑ i, v i = 0 ∧
    ∀ i : Fin 3, ¬ (0 < v i.castSucc ∧ 0 < v i.succ) ∧ ¬ (v i.castSucc < 0 ∧ v i.succ < 0))).card

open PowerSeries in
/-- Barker's g.f. `x(3 - x)(5 - 2x + x^2)/(1 - x)^4` for the sequence with offset `1`; the definition
also gives `a(0) = 1` (the zero array), which the g.f. does not describe, so the coefficient of
`x^0` is taken to be `0`. -/
theorem main :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
      X * (3 - X) * (5 - 2 * X + X ^ 2) := by
  sorry

end OMA.S_oeis_a199899
