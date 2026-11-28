import OMAStatements.S_mo_47888
import Mathlib

namespace OMA.D_mo_47888

open OMA.S_mo_47888

/-- A monotone field from the positive part of the scalar projection onto `(0,1,-1)`. -/
noncomputable def field3 (x : Fin 3 → ℤ) (j : Fin 3) : ℝ :=
  max 0 ((x 1 : ℝ) - x 2) * (![0, 1, -1] : Fin 3 → ℝ) j

lemma field3_monotone : fieldMonotone field3 := by
  intro x y
  have hmax : Monotone (max (0 : ℝ)) := fun _ _ h => max_le_max le_rfl h
  have h := (monotone_id.monovary hmax).sub_mul_sub_nonneg
    ((y 1 : ℝ) - y 2) ((x 1 : ℝ) - x 2)
  dsimp only [id] at h
  simp only [Fin.sum_univ_three, field3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  nlinarith only [h]

end OMA.D_mo_47888

open OMA.S_mo_47888 OMA.D_mo_47888 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_47888.main) := by
  intro h
  let p : Fin 3 → ℝ := ![1, 0, 0]
  let q : Fin 3 → ℝ := ![0, 1 / 4, 3 / 4]
  have hp : onSimplex p :=
    ⟨fun j => by fin_cases j <;> norm_num [p], by norm_num [p, Fin.sum_univ_three, Matrix.cons_val_two]⟩
  have hq : onSimplex q :=
    ⟨fun j => by fin_cases j <;> norm_num [q], by norm_num [q, Fin.sum_univ_three, Matrix.cons_val_two]⟩
  have hbad := h 1 3 (by decide) (by decide) field3 field3_monotone p q hp hq
  norm_num [p, q, smooth, average, bump, Fin.sum_univ_three, field3, max_def, Matrix.cons_val_two, Fin.ext_iff] at hbad
