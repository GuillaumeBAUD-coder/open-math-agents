import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1
-- Credit: @bsovocool16
-- H2 := ∀ c η : ℝ, 0 < c → 0 < η →     Summable (fun j : ℕ ↦ Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η)))

open Filter

lemma OMA.one_lt_log_four : 1 < Real.log 4 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

lemma OMA.pointwise (c η : ℝ) (hc : 0 < c) (hη : 0 < η) (j : ℕ) (hj : 2 ≤ j)
    (hL : 2 / c ≤ Real.log (j : ℝ) ^ η) :
    Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η)) ≤ 1 / (j : ℝ) ^ 2 := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (by omega : 1 < j)
  have hLpos : 0 < Real.log (j : ℝ) := Real.log_pos hj1
  have h4 := OMA.one_lt_log_four
  have hM : Real.log (j : ℝ) ≤ Real.log (Real.log ((4 : ℝ) ^ j)) := by
    rw [Real.log_pow]
    apply Real.log_le_log hjpos
    have : (j : ℝ) * 1 ≤ (j : ℝ) * Real.log 4 := by
      apply mul_le_mul_of_nonneg_left h4.le hjpos.le
    simpa using this
  have hpow : Real.log (j : ℝ) ^ (1 + η) ≤ Real.log (Real.log ((4 : ℝ) ^ j)) ^ (1 + η) :=
    Real.rpow_le_rpow hLpos.le hM (by linarith)
  have hsplit : Real.log (j : ℝ) ^ (1 + η) = Real.log (j : ℝ) * Real.log (j : ℝ) ^ η := by
    rw [Real.rpow_add hLpos, Real.rpow_one]
  have hkey : 2 * Real.log (j : ℝ) ≤ c * Real.log (Real.log ((4 : ℝ) ^ j)) ^ (1 + η) := by
    have h1 : 2 ≤ c * Real.log (j : ℝ) ^ η := by
      rw [div_le_iff₀ hc] at hL
      linarith
    have h2 : 2 * Real.log (j : ℝ) ≤ c * (Real.log (j : ℝ) * Real.log (j : ℝ) ^ η) := by
      nlinarith
    rw [← hsplit] at h2
    nlinarith
  have hexp : Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η))
      ≤ Real.exp (-(2 * Real.log (j : ℝ))) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hval : Real.exp (-(2 * Real.log (j : ℝ))) = 1 / (j : ℝ) ^ 2 := by
    rw [Real.exp_neg, mul_comm, Real.exp_mul, Real.exp_log hjpos]
    norm_num
  linarith

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H2 := by
  intro c η hc hη
  have hev : ∀ᶠ j : ℕ in atTop, 2 / c ≤ Real.log (j : ℝ) ^ η := by
    have h1 : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ((tendsto_rpow_atTop hη).comp h1).eventually_ge_atTop _
  have hg : Summable (fun j : ℕ => 1 / (j : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [hev, eventually_ge_atTop 2] with j hj hj2
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact OMA.pointwise c η hc hη j hj2 hj
