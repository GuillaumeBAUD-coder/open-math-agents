import OMAStatements.S_mo_103880
import Mathlib

namespace OMA.S_mo_103880

open Matrix Finset
open scoped BigOperators Matrix.Norms.Operator NNReal

private theorem row_le_norm {n : ℕ} (A : Mat n) (i : Fin n) :
    rowSize A i ≤ ‖A‖ := by
  rw [linfty_opNorm_def]
  have h := Finset.le_sup (f := fun i : Fin n => ∑ j : Fin n, ‖A i j‖₊) (Finset.mem_univ i)
  have h' := NNReal.coe_le_coe.mpr h
  simpa [rowSize, NNReal.coe_sum, Real.norm_eq_abs] using h'

private theorem norm_le_rows {n : ℕ} (A : Mat n) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ i, rowSize A i ≤ r) : ‖A‖ ≤ r := by
  let R : ℝ≥0 := ⟨r, hr⟩
  rw [linfty_opNorm_def]
  change (↑(_ : ℝ≥0) : ℝ) ≤ (R : ℝ)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  change (↑(∑ j : Fin n, ‖A i j‖₊) : ℝ) ≤ r
  simpa [rowSize, NNReal.coe_sum, Real.norm_eq_abs] using h i

private theorem norm_id_le (n : ℕ) : ‖(1 : Mat n)‖ ≤ 1 := by
  apply norm_le_rows _ _ zero_le_one
  intro i
  unfold rowSize
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem cofactor_criterion (n : ℕ) (A : Mat n) (hA : A.det ≠ 0) :
    dominant A⁻¹ ↔ ∀ i, (∑ j ∈ univ.erase i, |A.adjugate i j|) ≤ |A.adjugate i i| := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  let c : ℝ := ↑(hu.unit⁻¹)
  have hc : 0 < |c| := abs_pos.mpr (Units.ne_zero _)
  have hinv : A⁻¹ = c • A.adjugate := Matrix.nonsing_inv_apply _ hu
  have hmargin (i : Fin n) :
      margin A⁻¹ i = |c| * (|A.adjugate i i| - ∑ j ∈ univ.erase i, |A.adjugate i j|) := by
    rw [margin, hinv]
    simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, ← Finset.mul_sum, mul_sub]
  unfold dominant
  simp only [hmargin, mul_nonneg_iff_of_pos_left hc, sub_nonneg]

/-- The error from the identity controls both parts of the diagonal margin. -/
private theorem margin_from_error {n : ℕ} (G : Mat n) (i : Fin n) :
    1 - rowSize (G - 1) i ≤ margin G i := by
  rw [rowSize, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), margin]
  have hsum : (∑ j ∈ univ.erase i, |(G-1) i j|) = ∑ j ∈ univ.erase i, |G i j| := by
    apply Finset.sum_congr rfl
    intro j hj
    have hij := (Finset.mem_erase.mp hj).1.symm
    simp [Matrix.sub_apply, hij]
  rw [hsum, Matrix.sub_apply, Matrix.one_apply_eq]
  have htri := abs_add_le (1 - G i i) (G i i)
  rw [sub_add_cancel, abs_one, abs_sub_comm] at htri
  linarith

set_option maxHeartbeats 600000 in
private theorem inverse_margin (n : ℕ) (F : Mat n) (r : ℝ) (hr : 0 ≤ r) (hlt : r < 1)
    (h : ∀ i, rowSize F i ≤ r) :
    IsUnit (1-F) ∧
      (∀ i, (1-2*r)/(1-r) ≤ margin (1-F)⁻¹ i) ∧ (r ≤ 1/2 → dominant (1-F)⁻¹) := by
  let G : Mat n := (1-F)⁻¹
  have hF := norm_le_rows F r hr h
  let U := Units.oneSub F (hF.trans_lt hlt)
  have hU : IsUnit (1-F) := ⟨U, Units.val_oneSub _ _⟩
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hprod : (1-F) * G = 1 := Matrix.mul_nonsing_inv _ hdet
  have herror : G - 1 = F * G := by
    rw [Matrix.sub_mul, Matrix.one_mul] at hprod
    abel_nf at hprod ⊢
    rw [← hprod]
    abel
  have hG : ‖G‖ ≤ ‖G-1‖ + 1 := by
    calc
      ‖G‖ = ‖G-1 + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖G-1‖ + ‖(1 : Mat n)‖ := norm_add_le _ _
      _ ≤ _ := by linarith only [norm_id_le n]
  have hbound : ‖G-1‖ ≤ r / (1-r) := by
    have hmul : ‖G-1‖ ≤ r * (‖G-1‖ + 1) := by
      calc
        ‖G-1‖ = ‖F * G‖ := congrArg norm herror
        _ ≤ ‖F‖ * ‖G‖ := norm_mul_le _ _
        _ ≤ _ := mul_le_mul hF hG (norm_nonneg _) hr
    apply (le_div_iff₀ (sub_pos.mpr hlt)).mpr
    linarith
  have hm (i : Fin n) : (1 - 2*r)/(1-r) ≤ margin G i := by
    calc
      _ = 1 - r/(1-r) := by field_simp [sub_ne_zero.mpr (ne_of_gt hlt)]; ring
      _ ≤ 1 - rowSize (G-1) i := sub_le_sub_left ((row_le_norm _ i).trans hbound) _
      _ ≤ _ := margin_from_error G i
  refine ⟨hU, hm, ?_⟩
  intro hhalf i
  exact (div_nonneg (by linarith) (by linarith)).trans (hm i)

private theorem sharp_margin (r : ℝ) (hr : 0 ≤ r) (hlt : r < 1) :
    (∀ i, rowSize (sharp r) i = r) ∧
      IsUnit (1-sharp r) ∧ margin (1-sharp r)⁻¹ 0 = (1-2*r)/(1-r) := by
  have hrs (i : Fin 3) : rowSize (sharp r) i = r := by
    fin_cases i <;> simp [rowSize, sharp, Fin.sum_univ_three, abs_of_nonneg hr]
  have hu := (inverse_margin 3 (sharp r) r hr hlt fun i => (hrs i).le).1
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hden : 0 < 1-r^2 := by
    have := mul_pos (sub_pos.mpr hlt) (show 0 < 1+r by linarith)
    linarith
  let B : Mat 3 := !![1, r/(1-r^2), r^2/(1-r^2);
    0, 1/(1-r^2), r/(1-r^2); 0, r/(1-r^2), 1/(1-r^2)]
  have hB : (1-sharp r) * B = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, sharp, B]
    all_goals field_simp [ne_of_gt hden]; ring
  have hInv : (1-sharp r)⁻¹ = B := by
    calc
      _ = (1-sharp r)⁻¹ * ((1-sharp r) * B) := by rw [hB, Matrix.mul_one]
      _ = B := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  refine ⟨hrs, hu, ?_⟩
  rw [hInv, margin, show (univ : Finset (Fin 3)).erase 0 = {1, 2} by decide]
  have h1 : 0 ≤ r/(1-r^2) := div_nonneg hr hden.le
  have h2 : 0 ≤ r^2/(1-r^2) := div_nonneg (sq_nonneg _) hden.le
  rw [Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)]
  change |(1 : ℝ)| - (|r/(1-r^2)| + |r^2/(1-r^2)|) = _
  rw [abs_one, abs_of_nonneg h1, abs_of_nonneg h2]
  field_simp [ne_of_gt hden, sub_ne_zero.mpr (ne_of_gt hlt)]
  ring

end OMA.S_mo_103880

open OMA.S_mo_103880 in
theorem OMA.solution : type_of% @OMA.S_mo_103880.main :=
  ⟨cofactor_criterion, inverse_margin, sharp_margin⟩