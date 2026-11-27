import OMAReductions.R_Erdos933_erdos_933_variants_mahler_R1

/-! Take c(n) = max (log F(n) / log n - 1) 0 + 1 / (n + 1) when F(n) > 0 and c(n) = 1 / (n + 1)
otherwise. For n ≥ 2 the exponent 1 + c(n) is larger than log F(n) / log n, so
F(n) < n^(1 + c(n)) for every such n. And c(n) tends to 0: given delta, eventually
F(n) < n^(1 + delta / 2), which bounds the first term by delta / 2, and 1 / (n + 1) < delta / 2. -/

theorem OMA.solution : OMA.R_Erdos933_erdos_933_variants_mahler_R1.H2 := by
  intro F hF
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℕ → ℝ, ∀ n, m n =
      if 0 < F n then max (Real.log (F n) / Real.log (n : ℝ) - 1) 0 else 0 := ⟨_, fun _ => rfl⟩
  have hm0 : ∀ n, 0 ≤ m n := by
    intro n
    rw [hm n]
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  refine ⟨fun n => m n + 1 / ((n : ℝ) + 1), ?_, ?_⟩
  · rw [Asymptotics.isLittleO_iff]
    intro δ hδ
    have h1 := hF (δ / 2) (by linarith)
    have h2 : ∀ᶠ n : ℕ in Filter.atTop, 1 / ((n : ℝ) + 1) < δ / 2 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (gt_mem_nhds (by linarith))
    filter_upwards [h1, h2, Filter.eventually_ge_atTop 2] with n hn1 hn2 hn3
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hpos : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    have hA : m n ≤ δ / 2 := by
      rw [hm n]
      split_ifs with hF0
      · apply max_le _ (by linarith)
        have h3 : Real.log (F n) < (1 + δ / 2) * Real.log (n : ℝ) := by
          have h4 := Real.log_lt_log hF0 hn1
          rwa [Real.log_rpow (by linarith)] at h4
        rw [sub_le_iff_le_add, div_le_iff₀ hlogn]
        linarith
      · linarith
    have hn0' := hm0 n
    simp only [Pi.one_apply, norm_one, mul_one]
    rw [Real.norm_of_nonneg (by linarith)]
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn3
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    by_cases hF0 : 0 < F n
    · have hle : Real.log (F n) / Real.log (n : ℝ) - 1 ≤ m n := by
        rw [hm n, if_pos hF0]
        exact le_max_left _ _
      have h5 : Real.log (F n) - Real.log (n : ℝ) ≤ m n * Real.log (n : ℝ) := by
        have h6 := mul_le_mul_of_nonneg_right hle hlogn.le
        rwa [sub_mul, div_mul_cancel₀ _ hlogn.ne', one_mul] at h6
      have e : Real.log (n : ℝ) * (1 + (m n + 1 / ((n : ℝ) + 1))) =
          Real.log (n : ℝ) + m n * Real.log (n : ℝ) + Real.log (n : ℝ) * (1 / ((n : ℝ) + 1)) := by
        ring
      have key : Real.log (F n) < Real.log (n : ℝ) * (1 + (m n + 1 / ((n : ℝ) + 1))) := by
        rw [e]
        linarith [mul_pos hlogn hpos]
      calc F n = Real.exp (Real.log (F n)) := (Real.exp_log hF0).symm
        _ < Real.exp (Real.log (n : ℝ) * (1 + (m n + 1 / ((n : ℝ) + 1)))) :=
            Real.exp_lt_exp.2 key
        _ = (n : ℝ) ^ (1 + (m n + 1 / ((n : ℝ) + 1))) := (Real.rpow_def_of_pos hn0 _).symm
    · exact lt_of_le_of_lt (not_lt.1 hF0) (Real.rpow_pos_of_pos hn0 _)
