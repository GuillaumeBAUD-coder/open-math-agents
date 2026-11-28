import Mathlib

/-!
# OEIS A199531: 4-element zero-sum arrays on -n..n with no two consecutive zeros

Source: https://oeis.org/A199531
Credit: Sudharsan Rajendiran

A199531(n) is the number of arrays `x(0..3)` of 4 integers in `-n..n` with zero sum and no two
consecutive zero elements. Colin Barker conjectured (May 2018) the g.f. `4x(3 + 6x - x^2)/(1 - x)^4`
and the recurrence `a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) - a(n-4)` for `n > 4`. We state the g.f. as an
identity of formal power series over `ℚ` (it implies the recurrence); `a(0) = 0` (the only zero-sum
array over `{0}` is all zeros), matching the factor `x`.

Conventions: an array is `v : Fin 4 → ℤ` with entries in `[-n, n]`; "no two consecutive zeros" is
`∀ i : Fin 3, ¬ (v i.castSucc = 0 ∧ v i.succ = 0)`.
-/

namespace OMA.S_oeis_a199531

/-- A199531(n): the number of arrays `x(0..3)` of 4 integers in `-n..n` with zero sum and no two
consecutive zero elements. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(n : ℤ)) n).filter
    (fun v => ∑ i, v i = 0 ∧ ∀ i : Fin 3, ¬ (v i.castSucc = 0 ∧ v i.succ = 0))).card

open PowerSeries in
theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - X) ^ 4 = 4 * X * (3 + 6 * X - X ^ 2) := by
  sorry

end OMA.S_oeis_a199531
