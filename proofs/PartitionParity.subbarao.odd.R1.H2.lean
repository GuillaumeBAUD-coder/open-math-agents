import OMAReductions.R_PartitionParity_subbarao_odd_R1

-- Step PartitionParity.subbarao.odd.R1.H2
-- Credit: @caa1982

open Filter Asymptotics

theorem OMA.solution : OMA.R_PartitionParity_subbarao_odd_R1.H2 := by
  intro S hO
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨C, hC⟩ := hO.bound
  rw [Filter.eventually_atTop] at hC
  obtain ⟨X₀, hX₀⟩ := hC
  -- Use `Real.log x ≤ x ^ (1 / 4)` for large x, or simply `log X ≤ √(√X) * 4` -> `√X / log X ≥ X^(1/4) / 4`
  have hlog_bound : ∀ X : ℝ, 1 ≤ X → Real.log X ≤ 4 * (Real.sqrt (Real.sqrt X)) := by
    intro X hX
    have hpos : 0 < Real.sqrt (Real.sqrt X) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))
    have h4 : (Real.sqrt (Real.sqrt X)) ^ 4 = X := by
      calc (Real.sqrt (Real.sqrt X)) ^ 4
          = ((Real.sqrt (Real.sqrt X)) ^ 2) ^ 2 := by ring
        _ = (Real.sqrt X) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg X)]
        _ = X := Real.sq_sqrt (by linarith)
    have hlog : Real.log X = 4 * Real.log (Real.sqrt (Real.sqrt X)) := by
      conv_lhs => rw [← h4]
      rw [Real.log_pow]
      push_cast
      rfl
    have hle : Real.log (Real.sqrt (Real.sqrt X)) ≤ Real.sqrt (Real.sqrt X) :=
      le_trans (Real.log_le_sub_one_of_pos hpos) (by linarith)
    linarith
  let M : ℝ := max (max X₀ 2) ((4 * (|C| * (S.ncard : ℝ) + 1)) ^ 4)
  have hM1 : 1 ≤ M := le_trans (by norm_num) (le_trans (le_max_right X₀ 2) (le_max_left _ _))
  have hMX₀ : X₀ ≤ M := le_trans (le_max_left X₀ 2) (le_max_left _ _)
  have hM2 : 2 ≤ M := le_trans (le_max_right X₀ 2) (le_max_left _ _)
  have hbound := hX₀ M hMX₀
  have hlog_pos : 0 < Real.log M := Real.log_pos (by linarith)
  have hsqrt_pos : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by linarith)
  have hss_pos : 0 < Real.sqrt (Real.sqrt M) := Real.sqrt_pos.mpr hsqrt_pos
  have hnorm_l : ‖Real.sqrt M / Real.log M‖ = Real.sqrt M / Real.log M :=
    Real.norm_of_nonneg (div_nonneg (le_of_lt hsqrt_pos) (le_of_lt hlog_pos))
  have hnorm_r : ‖({n : ℕ | (n : ℝ) ≤ M ∧ n ∈ S}.ncard : ℝ)‖ =
      ({n : ℕ | (n : ℝ) ≤ M ∧ n ∈ S}.ncard : ℝ) :=
    Real.norm_of_nonneg (Nat.cast_nonneg _)
  rw [hnorm_l, hnorm_r] at hbound
  have hcard_le : ({n : ℕ | (n : ℝ) ≤ M ∧ n ∈ S}.ncard : ℝ) ≤ (S.ncard : ℝ) := by
    have hsub : {n : ℕ | (n : ℝ) ≤ M ∧ n ∈ S} ⊆ S := fun _ hn => hn.2
    exact_mod_cast Set.ncard_le_ncard hsub hfin
  have hC_le : C * ({n : ℕ | (n : ℝ) ≤ M ∧ n ∈ S}.ncard : ℝ) ≤ |C| * (S.ncard : ℝ) := by
    have h1 : C ≤ |C| := le_abs_self C
    calc C * ({n : ℕ | (n : ℝ) ≤ M ∧ n ∈ S}.ncard : ℝ)
        ≤ |C| * ({n : ℕ | (n : ℝ) ≤ M ∧ n ∈ S}.ncard : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
      _ ≤ |C| * (S.ncard : ℝ) := mul_le_mul_of_nonneg_left hcard_le (abs_nonneg C)
  have hss_ge : 4 * (|C| * (S.ncard : ℝ) + 1) ≤ Real.sqrt (Real.sqrt M) := by
    have hbase : (4 * (|C| * (S.ncard : ℝ) + 1)) ^ 4 ≤ M := le_max_right _ _
    have hnonneg : 0 ≤ 4 * (|C| * (S.ncard : ℝ) + 1) := by positivity
    have hsq1 : (4 * (|C| * (S.ncard : ℝ) + 1)) ^ 2 ≤ Real.sqrt M := by
      rw [← Real.sqrt_sq (sq_nonneg _)]
      apply Real.sqrt_le_sqrt
      linarith [show ((4 * (|C| * (S.ncard : ℝ) + 1)) ^ 2) ^ 2 = (4 * (|C| * (S.ncard : ℝ) + 1)) ^ 4 by ring]
    rw [← Real.sqrt_sq hnonneg]
    exact Real.sqrt_le_sqrt hsq1
  have hlog_le : Real.log M ≤ 4 * Real.sqrt (Real.sqrt M) := hlog_bound M hM1
  have hdiv_ge : Real.sqrt (Real.sqrt M) / 4 ≤ Real.sqrt M / Real.log M := by
    rw [div_le_div_iff₀ (by norm_num) hlog_pos]
    have hsq : Real.sqrt (Real.sqrt M) * Real.sqrt (Real.sqrt M) = Real.sqrt M :=
      Real.mul_self_sqrt (le_of_lt hsqrt_pos)
    nlinarith
  linarith
