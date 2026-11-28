import Mathlib

/-!
# MathOverflow 291544

Source: https://mathoverflow.net/questions/291544
-/

namespace OMA.S_mo_291544

open Matrix

theorem main : ∀ (A : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ),
      (A + x • (Matrix.of fun _ _ : Fin 3 => (1 : ℝ))).det * (A - x • (Matrix.of fun _ _ : Fin 3 => (1 : ℝ))).det ≤ A.det ^ 2 := by
  sorry

end OMA.S_mo_291544
