import OMAReductions.R_oeis_a099251_R1
import Mathlib

-- Proof of oeis-a099251.R1.H1
-- Evaluates the Catalan beta moments via an explicit antiderivative at j = 0
-- and the substitution t = sin^2 θ plus Wallis's reduction formula for j ≥ 1.
-- Credit: @DPS0340

open Real MeasureTheory intervalIntegral

theorem OMA.solution : OMA.R_oeis_a099251_R1.H1 := by
  -- Define W j = ∫ θ in 0..π/2, sin θ ^ (2 * j)
  let W : ℕ → ℝ := fun j => ∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin θ ^ (2 * j)
  have hW0 : W 0 = Real.pi / 2 := by
    dsimp [W]; simp
  have hW_step : ∀ j : ℕ, W (j + 1) = (2 * (j : ℝ) + 1) / (2 * (j : ℝ) + 2) * W j := by
    intro j
    dsimp [W]
    have h := integral_sin_pow (a := (0 : ℝ)) (b := Real.pi / 2) (n := 2 * j)
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, h]
    simp only [Real.sin_zero, Real.cos_pi_div_two, zero_pow (Nat.succ_ne_zero _),
      zero_mul, mul_zero, sub_self, zero_div, zero_add]
    push_cast; ring
  -- Base integral j = 0 via F(t) = sqrt(t*(1-t)) + (1/2) * arcsin(2*t - 1)
  have hI0 : (∫ t in (0 : ℝ)..1, Real.sqrt ((1 - t) / t)) = Real.pi / 2 := by
    let F : ℝ → ℝ := fun t => Real.sqrt (t * (1 - t)) + (1 / 2 : ℝ) * Real.arcsin (2 * t - 1)
    have hF_cont : ContinuousOn F (Set.Icc 0 1) := by
      apply Continuous.continuousOn
      fun_prop
    have hF_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (Real.sqrt ((1 - t) / t)) t := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have ht1 : t < 1 := ht.2
      have h1mt : 0 < 1 - t := by linarith
      have hprod_pos : 0 < t * (1 - t) := mul_pos ht0 h1mt
      have hsq_pos : 0 < Real.sqrt (t * (1 - t)) := Real.sqrt_pos.mpr hprod_pos
      have hd_poly : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * t) t := by
        have h := (hasDerivAt_id t).mul ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
        exact h.congr_deriv (by simp; ring)
      have hd_sqrt : HasDerivAt (fun x : ℝ => Real.sqrt (x * (1 - x)))
          ((1 - 2 * t) / (2 * Real.sqrt (t * (1 - t)))) t := by
        have h := (Real.hasDerivAt_sqrt hprod_pos.ne').comp t hd_poly
        exact h.congr_deriv (by ring)
      have hd_lin : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 t := by
        have h := ((hasDerivAt_id t).const_mul (2 : ℝ)).sub (hasDerivAt_const t (1 : ℝ))
        exact h.congr_deriv (by simp)
      have hne1 : 2 * t - 1 ≠ -1 := by linarith
      have hne2 : 2 * t - 1 ≠ 1 := by linarith
      have hd_arcsin : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * Real.arcsin (2 * x - 1))
          (1 / Real.sqrt (1 - (2 * t - 1) ^ 2)) t := by
        have h := ((Real.hasDerivAt_arcsin hne1 hne2).comp t hd_lin).const_mul (1 / 2 : ℝ)
        exact h.congr_deriv (by ring)
      have hsq_eq : Real.sqrt (1 - (2 * t - 1) ^ 2) = 2 * Real.sqrt (t * (1 - t)) := by
        have hrew : 1 - (2 * t - 1) ^ 2 = (2 : ℝ) ^ 2 * (t * (1 - t)) := by ring
        rw [hrew, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      have hsum : HasDerivAt F
          ((1 - 2 * t) / (2 * Real.sqrt (t * (1 - t))) + 1 / Real.sqrt (1 - (2 * t - 1) ^ 2)) t :=
        hd_sqrt.add hd_arcsin
      refine hsum.congr_deriv ?_
      rw [hsq_eq, Real.sqrt_div h1mt.le, Real.sqrt_mul ht0.le]
      have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
      have hs1mt : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr h1mt
      field_simp [hst.ne', hs1mt.ne']
      rw [Real.sq_sqrt h1mt.le]
      ring
    have hint : IntervalIntegrable (fun t : ℝ => Real.sqrt ((1 - t) / t)) volume 0 1 := by
      have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (r := -(1 / 2 : ℝ)) (by norm_num)
      have hc : Continuous (fun t : ℝ => Real.sqrt (1 - t)) := by fun_prop
      apply (h.mul_continuousOn hc.continuousOn).congr_uIoo
      intro t ht
      rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      change t ^ (-(1 / 2 : ℝ)) * Real.sqrt (1 - t) = Real.sqrt ((1 - t) / t)
      rw [Real.sqrt_div (by linarith [ht.2]), Real.rpow_neg ht.1.le, ← Real.sqrt_eq_rpow]
      ring
    have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (by norm_num : (0 : ℝ) ≤ 1) hF_cont hF_deriv hint
    rw [heval]
    dsimp [F]
    norm_num
    ring
  -- Express I j = (4^j / (j + 1)) * W j for every j : ℕ
  have hI_eq : ∀ j : ℕ,
      (∫ t in (0 : ℝ)..1, Real.sqrt ((1 - t) / t) * (4 * t) ^ j) =
        (4 : ℝ) ^ j / ((j : ℝ) + 1) * W j := by
    intro j
    cases j with
    | zero =>
      simp [hI0, hW0]
    | succ m =>
      let g : ℝ → ℝ := fun t => (4 : ℝ) ^ (m + 1) * Real.sqrt (t * (1 - t)) * t ^ m
      have hcongr : (∫ t in (0 : ℝ)..1, Real.sqrt ((1 - t) / t) * (4 * t) ^ (m + 1)) =
          ∫ t in (0 : ℝ)..1, g t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        by_cases ht0 : t = 0
        · subst ht0; simp [g]
        · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
          have h1mt : 0 ≤ 1 - t := by linarith [ht.2]
          dsimp [g]
          rw [Real.sqrt_div h1mt, Real.sqrt_mul ht_pos.le, mul_pow]
          have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
          have hsqt : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht_pos.le
          field_simp [hst.ne']
          rw [hsqt, pow_succ]
          ring
      rw [hcongr]
      -- Substitute t = sin^2 θ on [0, π/2]
      let φ : ℝ → ℝ := fun θ => Real.sin θ ^ 2
      let φ' : ℝ → ℝ := fun θ => 2 * Real.sin θ * Real.cos θ
      have hφ_deriv : ∀ θ ∈ Set.uIcc (0 : ℝ) (Real.pi / 2), HasDerivAt φ (φ' θ) θ := by
        intro θ _
        have h := (Real.hasDerivAt_sin θ).pow 2
        exact h.congr_deriv (by dsimp [φ']; ring)
      have hφ'_cont : ContinuousOn φ' (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
        apply Continuous.continuousOn; fun_prop
      have hg_cont : Continuous g := by fun_prop
      have hsub := intervalIntegral.integral_comp_mul_deriv hφ_deriv hφ'_cont hg_cont
      have hφ0 : φ 0 = 0 := by simp [φ]
      have hφ1 : φ (Real.pi / 2) = 1 := by simp [φ]
      rw [hφ0, hφ1] at hsub
      rw [← hsub]
      have htrig : (∫ θ in (0 : ℝ)..Real.pi / 2, (g ∘ φ) θ * φ' θ) =
          ∫ θ in (0 : ℝ)..Real.pi / 2,
            (2 * (4 : ℝ) ^ (m + 1)) * (Real.sin θ ^ (2 * (m + 1)) - Real.sin θ ^ (2 * (m + 2))) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
        have hsin_nn : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
        have hcos_nn : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
        have h1ms : 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
          linarith [Real.sin_sq_add_cos_sq θ]
        have hsq : Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) = Real.sin θ * Real.cos θ := by
          rw [h1ms, ← mul_pow, Real.sqrt_sq (mul_nonneg hsin_nn hcos_nn)]
        dsimp [g, φ, φ']
        rw [hsq]
        have hpow1 : (Real.sin θ ^ 2) ^ m = Real.sin θ ^ (2 * m) := by rw [← pow_mul]
        have hpow2 : Real.sin θ ^ (2 * (m + 1)) = Real.sin θ ^ (2 * m) * Real.sin θ ^ 2 := by
          rw [← pow_add, show 2 * (m + 1) = 2 * m + 2 by ring]
        have hpow3 : Real.sin θ ^ (2 * (m + 2)) = Real.sin θ ^ (2 * m) * Real.sin θ ^ 4 := by
          rw [← pow_add, show 2 * (m + 2) = 2 * m + 4 by ring]
        rw [hpow1, hpow2, hpow3]
        have hcs : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
        calc (4 : ℝ) ^ (m + 1) * (Real.sin θ * Real.cos θ) * Real.sin θ ^ (2 * m) * (2 * Real.sin θ * Real.cos θ)
            = 2 * (4 : ℝ) ^ (m + 1) * Real.sin θ ^ (2 * m) * Real.sin θ ^ 2 * Real.cos θ ^ 2 := by ring
          _ = 2 * (4 : ℝ) ^ (m + 1) * Real.sin θ ^ (2 * m) * Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2) := by rw [hcs]
          _ = 2 * (4 : ℝ) ^ (m + 1) * (Real.sin θ ^ (2 * m) * Real.sin θ ^ 2 -
              Real.sin θ ^ (2 * m) * Real.sin θ ^ 4) := by ring
      rw [htrig, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub]
      · change 2 * (4 : ℝ) ^ (m + 1) * (W (m + 1) - W (m + 2)) = _
        rw [hW_step (m + 1)]
        push_cast
        have hden : (2 * ((m : ℝ) + 1) + 2) ≠ 0 := by positivity
        have hden2 : ((m : ℝ) + 1 + 1) ≠ 0 := by positivity
        field_simp [hden, hden2]
        ring
      · exact (Real.continuous_sin.pow _).intervalIntegrable _ _
      · exact (Real.continuous_sin.pow _).intervalIntegrable _ _
  -- Induction on j using W_{j+1} = (2j+1)/(2j+2) * W_j and Catalan's recurrence
  intro j
  rw [hI_eq j]
  induction j with
  | zero =>
    rw [hW0]
    simp [Real.pi_ne_zero]
  | succ k ih =>
    have hcat_rec : ((k + 2 : ℕ) : ℝ) * (catalan (k + 1) : ℝ) =
        2 * (2 * (k : ℝ) + 1) * (catalan k : ℝ) := by
      have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
      have h2 := succ_mul_catalan_eq_centralBinom k
      have h3 := Nat.succ_mul_centralBinom_succ k
      have hnat : (k + 1) * ((k + 2) * catalan (k + 1)) = (k + 1) * (2 * (2 * k + 1) * catalan k) := by
        calc (k + 1) * ((k + 2) * catalan (k + 1))
            = (k + 1) * (k + 1).centralBinom := by rw [h1]
          _ = 2 * (2 * k + 1) * k.centralBinom := h3
          _ = 2 * (2 * k + 1) * ((k + 1) * catalan k) := by rw [h2]
          _ = (k + 1) * (2 * (2 * k + 1) * catalan k) := by ring
      have hcancel : (k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k :=
        Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) hnat
      exact_mod_cast hcancel
    rw [hW_step k, pow_succ]
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
    have h2k2 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
    have hlhs : 2 / Real.pi * ((4 : ℝ) ^ k * 4 / ((↑(k + 1) : ℝ) + 1) *
        ((2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2) * W k)) =
        (2 * (2 * (k : ℝ) + 1) / ((k : ℝ) + 2)) * (2 / Real.pi * ((4 : ℝ) ^ k / ((k : ℝ) + 1) * W k)) := by
      push_cast
      field_simp [Real.pi_ne_zero, hk1, hk2, h2k2]
      ring
    rw [hlhs, ih]
    push_cast at hcat_rec
    field_simp [hk2]
    linarith
