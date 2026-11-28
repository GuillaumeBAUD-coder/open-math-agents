import OMAStatements.S_mo_254890

open scoped Matrix Matrix.Norms.L2Operator

theorem OMA.solution : type_of% @OMA.S_mo_254890.main := by
  intro n L M _ hMP hnorm
  have hLML : L * M * L = L := hMP.1
  have hE : (1 - L) * (1 - M * L) = 1 - M * L := by
    calc (1 - L) * (1 - M * L)
        = (1 - M * L) - L * (1 - M * L) := by rw [sub_mul, one_mul]
      _ = (1 - M * L) - (L - L * M * L) := by rw [mul_sub, mul_one, ← Matrix.mul_assoc]
      _ = 1 - M * L := by rw [hLML, sub_self, sub_zero]
  have hEnorm : ‖1 - M * L‖ ≤ ‖1 - L‖ * ‖1 - M * L‖ := by
    conv_lhs => rw [← hE]
    exact Matrix.l2_opNorm_mul (1 - L) (1 - M * L)
  have hEnorm0 : ‖1 - M * L‖ = 0 := by
    by_contra h
    have hposE : 0 < ‖1 - M * L‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    nlinarith
  have hML : M * L = 1 := by
    have h0 : 1 - M * L = 0 := norm_eq_zero.mp hEnorm0
    exact (sub_eq_zero.mp h0).symm
  have hM : M = 1 + M * (1 - L) := by
    rw [mul_sub, mul_one, hML]
    abel
  have h1sq : ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ * ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ =
      ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ := by
    simpa [Matrix.conjTranspose_one] using
      (Matrix.l2_opNorm_conjTranspose_mul_self (1 : Matrix (Fin n) (Fin n) ℝ)).symm
  have h1le : ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 1 := by
    by_contra h
    push_neg at h
    nlinarith
  have hMnorm : ‖M‖ ≤ 1 + ‖M‖ * ‖1 - L‖ := by
    calc ‖M‖ = ‖1 + M * (1 - L)‖ := by rw [← hM]
      _ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ + ‖M * (1 - L)‖ := norm_add_le _ _
      _ ≤ 1 + ‖M‖ * ‖1 - L‖ := add_le_add h1le (Matrix.l2_opNorm_mul M (1 - L))
  have hpos : 0 < 1 - ‖1 - L‖ := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith
