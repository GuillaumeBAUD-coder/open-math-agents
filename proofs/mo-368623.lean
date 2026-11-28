import OMAStatements.S_mo_368623
import Mathlib

/-!
# Weighted involutions with large norm

Swap the first two coordinates with reciprocal positive weights and fix the other two.
This matrix squares to the identity, so its cube equals the original matrix.
Its first row can have arbitrarily large sum, giving the desired strict inequality.
-/

namespace OMA.S_mo_368623

open scoped Matrix.Norms.Operator

/-- Each entry is bounded by its row sum and hence by the operator norm. -/
lemma entry_le (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) : ‖A i j‖ ≤ ‖A‖ := by
  change (‖A i j‖₊ : ℝ) ≤ (‖A‖₊ : ℝ)
  apply NNReal.coe_le_coe.mpr
  rw [Matrix.linfty_opNNNorm_def]
  exact (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ j)).trans
    (Finset.le_sup (f := fun l => ∑ k, ‖A l k‖₊) (Finset.mem_univ i))

end OMA.S_mo_368623

open scoped Matrix.Norms.Operator in
open OMA.S_mo_368623 in
theorem OMA.solution : type_of% @OMA.S_mo_368623.main := by
  intro C hC
  let t := C^3 + 1
  have ht : 0 < t := by dsimp [t]; positivity
  let A : Matrix (Fin 4) (Fin 4) ℝ := !![0,t,0,0; t⁻¹,0,0,0; 0,0,1,0; 0,0,0,1]
  have hsq : A^2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, sq, Matrix.mul_apply, Fin.sum_univ_succ, ht.ne']
  refine ⟨A, ?_, by rw [hsq, norm_one], ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [A, ht.le]
  · rw [pow_succ A 2, hsq, one_mul, norm_one, Real.one_rpow, mul_one, one_div,
      Real.lt_rpow_inv_iff_of_pos hC.le (norm_nonneg A) (by norm_num)]
    have bound := entry_le A 0 1
    change ‖t‖ ≤ ‖A‖ at bound
    rw [Real.norm_eq_abs, abs_of_pos ht] at bound
    norm_num at *
    linarith [show C^3 < t by dsimp [t]; linarith]
