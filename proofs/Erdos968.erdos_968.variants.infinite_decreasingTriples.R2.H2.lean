import OMAReductions.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R2
import Mathlib

-- Credit: @LordMike

theorem OMA.solution : OMA.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R2.H2 := by
  intro δ hδ
  have hcheb : ∀ᶠ x : ℕ in Filter.atTop,
      ((Nat.primeCounting ⌊(x : ℝ)⌋₊ : ℕ) : ℝ) ≤ (Real.log 4 + 1) * (x : ℝ) / Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Chebyshev.eventually_primeCounting_le one_pos)
  have hlog : ∀ᶠ x : ℕ in Filter.atTop, (Real.log 4 + 1) / δ < Real.log (x : ℝ) := by
    have ht : Filter.Tendsto (fun x : ℕ => Real.log (x : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually_gt_atTop _
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  filter_upwards [hcheb, hlog, Filter.eventually_ge_atTop 2] with x hx2 hx1 hx3
  rw [Nat.floor_natCast] at hx2
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hq : 0 < (Real.log 4 + 1) / δ := by positivity
  have hlpos : 0 < Real.log (x : ℝ) := lt_trans hq hx1
  have hl2 : Real.log 4 + 1 < δ * Real.log (x : ℝ) := by
    have := (div_lt_iff₀ hδ).mp hx1
    linarith [mul_comm δ (Real.log (x : ℝ))]
  calc ((Nat.primeCounting x : ℕ) : ℝ)
      ≤ (Real.log 4 + 1) * (x : ℝ) / Real.log (x : ℝ) := hx2
    _ < δ * (x : ℝ) := by
      rw [div_lt_iff₀ hlpos]
      nlinarith [mul_lt_mul_of_pos_right hl2 hxpos]
