import OMAReductions.R_Erdos78_erdos_78_variants_little_o_sqrt_R1

/-! At depth one more than the base-16 logarithm, the ratio to the
square root is bounded by a constant times a power of three quarters. -/

open Filter Asymptotics Topology

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_little_o_sqrt_R1.H3 := by
  let f (n : ℕ) : ℝ := 4 * 3 ^ Nat.log 16 n
  refine ⟨f, isLittleO_iff.mpr ?_, Eventually.of_forall ?_⟩
  · intro c hc
    have ht : Tendsto (fun j : ℕ => 4 * (3 / 4 : ℝ) ^ j) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : 0 ≤ (3/4 : ℝ)) (by norm_num : (3/4 : ℝ) < 1)).const_mul 4
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hc))
    filter_upwards [eventually_ge_atTop (16^J)] with n hn
    have hn0 : n ≠ 0 := (lt_of_lt_of_le (pow_pos (by decide) J) hn).ne'
    let j := Nat.log 16 n
    have hj : J ≤ j := (Nat.le_log_iff_pow_le (by norm_num) hn0).mpr hn
    have hpow : (16 : ℝ)^j ≤ n := by exact_mod_cast Nat.pow_log_le_self 16 hn0
    have hs : (4 : ℝ)^j ≤ Real.sqrt n := by
      apply (Real.le_sqrt (by positivity) (by positivity)).mpr
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
      exact hpow
    have hratio := hJ j hj
    rw [div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)] at hratio
    change ‖4 * (3 : ℝ)^j‖ ≤ c * ‖Real.sqrt n‖
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact hratio.le.trans (mul_le_mul_of_nonneg_left hs hc.le)
  · intro n
    refine ⟨Nat.log 16 n + 1, (Nat.lt_pow_succ_log_self (by norm_num) n).le, ?_⟩
    have one : 1 ≤ 3 ^ Nat.log 16 n := Nat.one_le_pow _ _ (by decide)
    have bound : 3 ^ (Nat.log 16 n + 1) + 1 ≤ 4 * 3 ^ Nat.log 16 n := by
      rw [pow_succ]
      omega
    have hf : f n = ((4 * 3 ^ Nat.log 16 n : ℕ) : ℝ) := by simp [f]
    rwa [hf, Nat.ceil_natCast]
