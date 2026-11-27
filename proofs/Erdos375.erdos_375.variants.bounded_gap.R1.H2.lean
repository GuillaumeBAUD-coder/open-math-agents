import OMAReductions.R_Erdos375_erdos_375_variants_bounded_gap_R1

-- Step Erdos375.erdos_375.variants.bounded_gap.R1.H2: hypothesis H2 of reduction Erdos375.erdos_375.variants.bounded_gap.R1
-- Credit: @loremcdmx
-- H2 := ∀ c : ℝ, 0 < c → ∀ᶠ k : ℕ in atTop,   ((k + 1).primesBelow.card : ℝ) < c * k

open Filter

theorem OMA.solution : OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1.H2 := by
  intro c hc
  have h1 := Chebyshev.eventually_primeCounting_le (ε := 1) one_pos
  have h1' : ∀ᶠ k : ℕ in atTop, Nat.primeCounting ⌊(k : ℝ)⌋₊ ≤ (Real.log 4 + 1) * (k : ℝ) / Real.log k :=
    tendsto_natCast_atTop_atTop.eventually h1
  have hlog : Tendsto (fun k : ℕ => Real.log k) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2 := hlog.eventually_gt_atTop (2 * (Real.log 4 + 1) / c)
  filter_upwards [h1', h2, eventually_ge_atTop 2] with k hk hl hk2
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hc4 : 0 < Real.log 4 + 1 := by have := Real.log_pos (by norm_num : (1:ℝ) < 4); linarith
  have hl0 : 0 < Real.log k := lt_trans (by positivity) hl
  have hcard : ((k + 1).primesBelow.card : ℝ) = (Nat.primeCounting k : ℝ) := by
    rw [Nat.primesBelow_card_eq_primeCounting']; rfl
  rw [hcard]
  simp only [Nat.floor_natCast] at hk
  have : (Real.log 4 + 1) * k / Real.log k < c * k := by
    rw [div_lt_iff₀ hl0]
    rw [div_lt_iff₀ hc] at hl
    nlinarith [mul_pos hc hkpos, mul_pos hc4 hkpos]
  exact lt_of_le_of_lt hk this
