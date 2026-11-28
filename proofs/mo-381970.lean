import OMAStatements.S_mo_381970

/-! Retains @Genbox's cyclic-block counterexample from merged PR25377.
The existing null vector and right inverse supply the determinant conclusions directly. -/

open OMA.S_mo_381970 Matrix

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_381970.main) := by
  intro h
  let σ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  let A (τ : Equiv.Perm (Fin 2)) := cyclicBlockMatrix 3 2 (fun _ => -1) (fun _ => 1) τ
  have hs : σ ≠ 1 := by
    intro he
    have he0 := DFunLike.congr_fun he (0 : Fin 2)
    norm_num [σ] at he0
  have hcard : Fintype.card (Equiv.Perm (Fin 2)) = 2 := by
    norm_num [Fintype.card_perm]
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, σ} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hcard, Ne.symm hs]
  have hperm (i j : Fin 2) : σ.permMatrix ℝ i j = if i = j then 0 else 1 := by
    fin_cases i <;> fin_cases j <;> rfl
  -- The swapped corner joins the two paths into a six-cycle.
  have hzero : (A σ).det = 0 := by
    let v : Fin 3 × Fin 2 → ℝ := fun i =>
      if i.1 = 2 then 0 else if i.2 = 0 then 1 else -1
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v, ?_, ?_⟩
    · exact fun hv => one_ne_zero (congrFun hv ((0, 0) : Fin 3 × Fin 2))
    · funext i
      rcases i with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three,
          Fin.sum_univ_two, A, v, cyclicBlockMatrix, hperm, Matrix.one_apply,
          Pi.zero_apply, Fin.ext_iff] <;> norm_num
  -- With the identity corner, each triangle block has inverse (J - I) / 2.
  have hnonzero : (A 1).det ≠ 0 := by
    let B : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ := fun i j =>
      if i.2 = j.2 ∧ i.1 ≠ j.1 then 1 / 2 else 0
    have hright : A 1 * B = 1 := by
      ext i j
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      rcases i with ⟨i, i'⟩
      rcases j with ⟨j, j'⟩
      fin_cases i <;> fin_cases i' <;> fin_cases j <;> fin_cases j' <;>
        simp only [Fin.sum_univ_three, Fin.sum_univ_two, Fin.ext_iff,
          A, B, cyclicBlockMatrix, Matrix.permMatrix_one, Matrix.one_apply] <;> norm_num <;>
        simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one] <;>
        norm_num
    exact Matrix.det_ne_zero_of_right_inverse hright
  have havg := h 3 2 (by decide) (by decide) (by decide) (fun _ => -1) (fun _ => 1)
  change (∑ τ : Equiv.Perm (Fin 2), (A τ).det) /
    (Fintype.card (Equiv.Perm (Fin 2)) : ℝ) = (A 1).det at havg
  rw [huniv, Finset.sum_insert (by simp [Ne.symm hs]), Finset.sum_singleton, hzero, add_zero,
    hcard] at havg
  apply hnonzero
  norm_num at havg
  linarith