import OMAReductions.R_PartitionParity_subbarao_even_R1

/-! An unbounded lower bound on a counting function forces infinitude. -/

open Filter

theorem OMA.solution : OMA.R_PartitionParity_subbarao_even_R1.H2 := by
  intro S h
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨C, hC⟩ := h.bound
  have hcount (X : ℝ) :
      ({n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S}.ncard : ℝ) ≤ S.ncard := by
    have hs : {n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S} ⊆ S := fun _ hn => hn.2
    exact_mod_cast Set.ncard_le_ncard hs hfin
  have hlarge := Real.tendsto_sqrt_atTop.eventually_gt_atTop (|C| * (S.ncard : ℝ))
  obtain ⟨X, hbound, hgt⟩ := (hC.and hlarge).exists
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg X), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    at hbound
  exact (not_lt_of_ge (hbound.trans
    (mul_le_mul (le_abs_self C) (hcount X) (Nat.cast_nonneg _) (abs_nonneg C)))) hgt
