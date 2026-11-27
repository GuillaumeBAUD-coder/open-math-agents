import OMAReductions.R_Mills_exists_least_R1

-- Step Mills.exists_least.R1.H2: hypothesis H2 of reduction Mills.exists_least.R1

/-!
Mathlib proves `ψ x - θ x ≤ C √x` for some real `C` (`Chebyshev.psi_sub_theta_le_mul_sqrt`).
Replacing `C` by `max C 1` makes the constant positive.
-/

theorem OMA.solution : OMA.R_Mills_exists_least_R1.H2 := by
  unfold OMA.R_Mills_exists_least_R1.H2
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right C 1), fun x => ?_⟩
  exact le_trans (hC x)
    (mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.sqrt_nonneg x))
