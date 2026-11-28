import OMAStatements.S_oeis_a204240

-- uses note #95524

namespace OMA.S_oeis_a204240

open Matrix PowerSeries
open scoped Matrix BigOperators

private theorem entry_of_le {n : ℕ} {i j : Fin n} (h : i ≤ j) :
    principalMatrix n i j = 3 * ((j.val : ℚ) + 1) - 2 * ((i.val : ℚ) + 1) := by
  have h' : (i.val : ℚ) ≤ j.val := by exact_mod_cast h
  unfold principalMatrix
  exact max_eq_right (by linarith)

private theorem entry_of_ge {n : ℕ} {i j : Fin n} (h : j ≤ i) :
    principalMatrix n i j = 3 * ((i.val : ℚ) + 1) - 2 * ((j.val : ℚ) + 1) := by
  have h' : (j.val : ℚ) ≤ i.val := by exact_mod_cast h
  unfold principalMatrix
  exact max_eq_left (by linarith)

/-- Keep the first row and replace each later row by its first difference. -/
private def difference (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := fun i j =>
  Fin.cases (if j = 0 then 1 else 0)
    (fun k => (if j = k.succ then 1 else 0) - (if j = k.castSucc then 1 else 0)) i

private theorem difference_det (n : ℕ) : (difference n).det = 1 := by
  have h : (difference n).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    revert hij
    refine Fin.cases ?_ (fun k => ?_) i
    · intro h
      simp [difference, (ne_of_lt h).symm]
    · intro h
      have hne : j ≠ k.castSucc := by
        intro e
        rw [e] at h
        have hh : k.val + 1 < k.val := h
        omega
      simp [difference, (ne_of_lt h).symm, hne]
  rw [Matrix.det_of_isLowerTriangular _ h]
  apply Finset.prod_eq_one
  intro i _
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [difference]
  · have hne : k.succ ≠ k.castSucc := by
      intro h
      have hv : k.val + 1 = k.val := congrArg Fin.val h
      omega
    simp [difference, hne]

private theorem row_zero {n : ℕ} (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (j : Fin (n + 1)) : (difference n * N) 0 j = N 0 j := by
  simp [Matrix.mul_apply, difference]

private theorem row_succ {n : ℕ} (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (i : Fin n) (j : Fin (n + 1)) :
    (difference n * N) i.succ j = N i.succ j - N i.castSucc j := by
  simp [Matrix.mul_apply, difference, sub_mul, Finset.sum_sub_distrib]

private theorem col_zero {n : ℕ} (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (i : Fin (n + 1)) : (N * (difference n)ᵀ) i 0 = N i 0 := by
  simp [Matrix.mul_apply, difference]

private theorem col_succ {n : ℕ} (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (i : Fin (n + 1)) (j : Fin n) :
    (N * (difference n)ᵀ) i j.succ = N i j.succ - N i j.castSucc := by
  simp [Matrix.mul_apply, difference, mul_sub, Finset.sum_sub_distrib]

private def splitFirst (n : ℕ) : (Fin 1 ⊕ Fin n) ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl 0) Sum.inr
  left_inv := by
    intro i
    rcases i with i | i
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    · rfl
  right_inv := by
    intro i
    exact Fin.cases rfl (fun _ => rfl) i

private def arrowHead (n : ℕ) : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℚ :=
  Matrix.fromBlocks (Matrix.of fun _ _ => 1) (Matrix.of fun _ _ => 3) (Matrix.of fun _ _ => 3)
    (Matrix.diagonal fun _ => -5)

private theorem difference_congruence (n : ℕ) :
    ((difference n * principalMatrix (n + 1)) * (difference n)ᵀ).submatrix
      (splitFirst n) (splitFirst n) = arrowHead n := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · change ((difference n * principalMatrix (n + 1)) * (difference n)ᵀ) 0 0 = 1
    rw [col_zero, row_zero, entry_of_le le_rfl]
    norm_num
  · change ((difference n * principalMatrix (n + 1)) * (difference n)ᵀ) 0 j.succ = 3
    rw [col_succ, row_zero, row_zero, entry_of_le (Fin.zero_le j.succ),
      entry_of_le (Fin.zero_le j.castSucc)]
    simp only [Fin.val_zero, Nat.cast_zero, Fin.val_succ, Fin.val_castSucc, Nat.cast_add,
      Nat.cast_one]
    ring
  · change ((difference n * principalMatrix (n + 1)) * (difference n)ᵀ) i.succ 0 = 3
    rw [col_zero, row_succ, entry_of_ge (Fin.zero_le i.succ),
      entry_of_ge (Fin.zero_le i.castSucc)]
    simp only [Fin.val_zero, Nat.cast_zero, Fin.val_succ, Fin.val_castSucc, Nat.cast_add,
      Nat.cast_one]
    ring
  · change ((difference n * principalMatrix (n + 1)) * (difference n)ᵀ) i.succ j.succ =
      Matrix.diagonal (fun _ : Fin n => (-5 : ℚ)) i j
    rw [col_succ, row_succ, row_succ]
    rcases lt_trichotomy i j with h | rfl | h
    · have h' : i.val < j.val := h
      rw [entry_of_le (by change i.val + 1 ≤ j.val + 1; omega),
        entry_of_le (by change i.val ≤ j.val + 1; omega),
        entry_of_le (by change i.val + 1 ≤ j.val; omega),
        entry_of_le (by change i.val ≤ j.val; omega), Matrix.diagonal_apply_ne _ h.ne]
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      ring
    · rw [entry_of_le le_rfl, entry_of_le (by change i.val ≤ i.val + 1; omega),
        entry_of_ge (by change i.val ≤ i.val + 1; omega), entry_of_le le_rfl,
        Matrix.diagonal_apply_eq]
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      ring
    · have h' : j.val < i.val := h
      rw [entry_of_ge (by change j.val + 1 ≤ i.val + 1; omega),
        entry_of_ge (by change j.val + 1 ≤ i.val; omega),
        entry_of_ge (by change j.val ≤ i.val + 1; omega),
        entry_of_ge (by change j.val ≤ i.val; omega), Matrix.diagonal_apply_ne _ h.ne']
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      ring

private theorem arrow_det (n : ℕ) :
    (arrowHead n).det = (-5 : ℚ) ^ n * (1 + 9 / 5 * (n : ℚ)) := by
  let D : Matrix (Fin n) (Fin n) ℚ := Matrix.diagonal fun _ => -5
  let E : Matrix (Fin n) (Fin n) ℚ := Matrix.diagonal fun _ => -1 / 5
  let : Invertible D :=
    ⟨E, by simp [D, E, Matrix.diagonal_mul_diagonal],
      by simp [D, E, Matrix.diagonal_mul_diagonal]; funext i; norm_num⟩
  change (Matrix.fromBlocks (Matrix.of fun _ _ => (1 : ℚ)) (Matrix.of fun _ _ => (3 : ℚ))
    (Matrix.of fun _ _ => (3 : ℚ)) D : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℚ).det = _
  rw [Matrix.det_fromBlocks₂₂]
  change D.det * ((Matrix.of fun _ _ => (1 : ℚ)) - (Matrix.of fun _ _ => (3 : ℚ)) *
    E * (Matrix.of fun _ _ => (3 : ℚ)) : Matrix (Fin 1) (Fin 1) ℚ).det = _
  rw [Matrix.det_fin_one, Matrix.sub_apply, Matrix.mul_apply]
  simp [D, E, Matrix.mul_diagonal, Matrix.det_diagonal]
  ring

private theorem det_succ (n : ℕ) :
    a (n + 1) = (-5 : ℚ) ^ n * (1 + 9 / 5 * (n : ℚ)) := by
  have h := congrArg Matrix.det (difference_congruence n)
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, difference_det, one_mul, mul_one, arrow_det] at h
  exact h

private theorem recurrence (n : ℕ) (hn : 3 ≤ n) :
    a n = -10 * a (n - 1) - 25 * a (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = (k + 1) + 1 by omega,
    show k + 3 - 2 = k + 1 by omega, show k + 3 = (k + 2) + 1 by omega,
    det_succ, det_succ, det_succ]
  simp only [pow_succ, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

private theorem coeff_X_mul_shift (F : PowerSeries ℚ) (m : ℕ) :
    coeff m (X * F) = if 1 ≤ m then coeff (m - 1) F else 0 := by
  simpa only [pow_one] using coeff_X_pow_mul' F 1 m

private theorem generatingFunction_cleared :
    (C 5 * X + 1) ^ 2 * generatingFunction = X - C 4 * X ^ 2 := by
  rw [show (C 5 * X + 1 : PowerSeries ℚ) ^ 2 = 1 + C 10 * X + C 25 * X ^ 2 by
    simp only [map_ofNat]
    ring]
  ext n
  simp only [add_mul, mul_assoc, map_add, map_sub, one_mul, coeff_C_mul, coeff_X,
    coeff_X_pow, coeff_X_mul_shift, coeff_X_pow_mul']
  rcases n with _ | n
  · simp [generatingFunction]
  rcases n with _ | n
  · norm_num [generatingFunction, det_succ]
  rcases n with _ | n
  · norm_num [generatingFunction, det_succ]
  · simp (disch := omega) [generatingFunction]
    have h := recurrence (n + 3) (by omega)
    rw [show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega] at h
    linear_combination h

private theorem generatingFunction_formula :
    generatingFunction = -(X * (C 4 * X - 1)) * ((C 5 * X + 1) ^ 2)⁻¹ := by
  let d : PowerSeries ℚ := (C 5 * X + 1) ^ 2
  have hd : constantCoeff d ≠ 0 := by simp [d]
  calc
    generatingFunction = (d * (d⁻¹)) * generatingFunction := by
      rw [PowerSeries.mul_inv_cancel _ hd, one_mul]
    _ = (d * generatingFunction) * d⁻¹ := by ring
    _ = _ := by
      rw [show d * generatingFunction = X - C 4 * X ^ 2 from generatingFunction_cleared]
      change (X - C 4 * X ^ 2) * d⁻¹ = -(X * (C 4 * X - 1)) * d⁻¹
      ring

/-- Both of Colin Barker's A204240 conjectures. -/
theorem complete :
    (∀ n : ℕ, 3 ≤ n → a n = -10 * a (n - 1) - 25 * a (n - 2)) ∧
    generatingFunction = -(X * (C 4 * X - 1)) * ((C 5 * X + 1) ^ 2)⁻¹ := by
  exact ⟨recurrence, generatingFunction_formula⟩

end OMA.S_oeis_a204240


theorem OMA.solution : type_of% @OMA.S_oeis_a204240.main :=
  OMA.S_oeis_a204240.complete

