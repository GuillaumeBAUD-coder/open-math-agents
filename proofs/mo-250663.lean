import OMAStatements.S_mo_250663
import Mathlib

open OMA.S_mo_250663
open Matrix
open scoped Matrix.Norms.L2Operator

lemma mo250663_norm2 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖(![a, b] : Fin 2 → ℝ)‖ = max a b := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_trans ha (le_max_left a b))).2
    intro i; fin_cases i
    · simp [abs_of_nonneg ha]
    · simp [abs_of_nonneg hb]
  · apply max_le
    · have := norm_le_pi_norm (![a, b] : Fin 2 → ℝ) 0
      simpa [abs_of_nonneg ha] using this
    · have := norm_le_pi_norm (![a, b] : Fin 2 → ℝ) 1
      simpa [abs_of_nonneg hb] using this

lemma mo250663_inv (v w : Fin 2 → ℝ) (h : ∀ i, v i * w i = 1) :
    (diagonal v)⁻¹ = diagonal w := by
  apply Matrix.inv_eq_right_inv
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i; exact h i

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_250663.main) := by
  intro h
  have hA : (diagonal ![(2 : ℝ), 2]).PosDef := by
    rw [posDef_diagonal_iff]; intro i; fin_cases i <;> norm_num
  have h1 := h 2 (diagonal ![2, 2]) hA ![1, 3] (by intro i; fin_cases i <;> norm_num)
  have e1 : (diagonal ![(2 : ℝ), 2] + diagonal ![1, 3]) * (1 + diagonal ![1, 3])⁻¹
      = diagonal ![3 / 2, 5 / 4] := by
    rw [diagonal_add, ← diagonal_one, diagonal_add,
      mo250663_inv _ ![1 / 2, 1 / 4] (by intro i; fin_cases i <;> norm_num),
      diagonal_mul_diagonal]
    congr 1
    ext i; fin_cases i <;> norm_num
  have e2 : (diagonal ![(3 : ℝ) / 2, 5 / 4])⁻¹ = diagonal ![2 / 3, 4 / 5] := by
    exact mo250663_inv _ _ (by intro i; fin_cases i <;> norm_num)
  have e3 : (diagonal ![(2 : ℝ), 2])⁻¹ = diagonal ![1 / 2, 1 / 2] := by
    exact mo250663_inv _ _ (by intro i; fin_cases i <;> norm_num)
  unfold condNum at h1
  rw [e1, e2, e3, l2_opNorm_diagonal, l2_opNorm_diagonal, l2_opNorm_diagonal,
    l2_opNorm_diagonal, mo250663_norm2 _ _ (by norm_num) (by norm_num),
    mo250663_norm2 _ _ (by norm_num) (by norm_num),
    mo250663_norm2 _ _ (by norm_num) (by norm_num),
    mo250663_norm2 _ _ (by norm_num) (by norm_num)] at h1
  norm_num at h1
