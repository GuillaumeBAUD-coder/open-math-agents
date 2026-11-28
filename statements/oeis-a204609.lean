import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a204609

/-- Determinant of a `2 × 2` subblock of a `0..1` array. -/
def blockDet (a b c d : Bool) : ℤ :=
  (if a then 1 else 0) * (if d then 1 else 0) - (if b then 1 else 0) * (if c then 1 else 0)

/-- OEIS A204609: Number of `(n + 1) × 2` `0..1` arrays with the determinants of `2 × 2`
subblocks nondecreasing downwards. -/
def A204609 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Bool =>
    ∀ i : Fin (n - 1),
      blockDet (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
        (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1)) ≤
      blockDet (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1))
        (A (⟨i.1 + 2, by omega⟩, 0)) (A (⟨i.1 + 2, by omega⟩, 1)))).card

/-- OEIS A204609 conjectures (Colin Barker, Feb 20 2018):
1. Rational generating function (with `a_0 = A204609 1 = 16`):
   `(1 - X) * (1 - 2 * X - 2 * X^2) * ∑_{n≥0} A204609(n + 1) X^n = 16 - X - 16*X^2 - 8*X^3 - 4*X^4 - X^5`.
2. Binet closed form for all `n > 2`:
   `A204609 (n + 1) = (112 + (193 - 113*√3)*(1 - √3)^n + (1 + √3)^n*(193 + 113*√3)) / 24`. -/
theorem main :
    (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X - 2 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => (A204609 (n + 1) : ℤ)) =
      16 - PowerSeries.X - 16 * PowerSeries.X ^ 2 - 8 * PowerSeries.X ^ 3 -
        4 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5 ∧
    (∀ n : ℕ, 2 < n →
      (A204609 (n + 1) : ℝ) =
        (112 + (193 - 113 * Real.sqrt 3) * (1 - Real.sqrt 3) ^ n +
         (1 + Real.sqrt 3) ^ n * (193 + 113 * Real.sqrt 3)) / 24) := by
  sorry

end OMA.S_oeis_a204609
