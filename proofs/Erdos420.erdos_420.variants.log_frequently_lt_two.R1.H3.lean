import OMAReductions.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1

/-! # Iterated logarithms: `c log m` is eventually below the Corollary 2 function

With `y = log log log m`, the claim reduces to `9 c y ^ 3 ≤ exp y * log y`.
This follows from `y ^ 4 / 24 ≤ exp y` and `log y ≥ 1` once `y ≥ max 3 (216 c)`. -/

theorem OMA.solution : OMA.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1.H3 := by
  intro c hc
  set Y : ℝ := max 3 (216 * c) with hY
  have hY3 : 3 ≤ Y := le_max_left _ _
  have hYc : 216 * c ≤ Y := le_max_right _ _
  rw [Filter.eventually_atTop]
  refine ⟨⌈Real.exp (Real.exp (Real.exp Y))⌉₊, fun m hm => ?_⟩
  have hm' : Real.exp (Real.exp (Real.exp Y)) ≤ (m : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hm)
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (Real.exp_pos _) hm'
  set L := Real.log (m : ℝ) with hL
  have hL1 : Real.exp (Real.exp Y) ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hmpos]; exact hm'
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL1
  set L2 := Real.log L with hL2
  have hL21 : Real.exp Y ≤ L2 := by
    rw [hL2, Real.le_log_iff_exp_le hLpos]; exact hL1
  have hL2pos : 0 < L2 := lt_of_lt_of_le (Real.exp_pos _) hL21
  set L3 := Real.log L2 with hL3
  have hL31 : Y ≤ L3 := by
    rw [hL3, Real.le_log_iff_exp_le hL2pos]; exact hL21
  have hL3pos : 0 < L3 := by linarith
  set L4 := Real.log L3 with hL4
  have hL41 : 1 ≤ L4 := by
    rw [hL4, Real.le_log_iff_exp_le hL3pos]
    have := Real.exp_one_lt_d9
    linarith
  have hexp : Real.exp L3 = L2 := by rw [hL3, Real.exp_log hL2pos]
  have htay : L3 ^ 4 / 24 ≤ L2 := by
    have := Real.pow_div_factorial_le_exp L3 hL3pos.le 4
    rw [hexp] at this
    simpa [Nat.factorial] using this
  have key : 9 * c * L3 ^ 3 ≤ L2 * L4 := by
    have h1 : 9 * c * L3 ^ 3 ≤ L3 ^ 4 / 24 := by
      have : 0 ≤ L3 ^ 3 := by positivity
      nlinarith
    have h2 : L2 ≤ L2 * L4 := by nlinarith
    linarith
  have hden : 0 < 9 * L3 ^ 3 := by positivity
  rw [le_div_iff₀ hden]
  nlinarith
