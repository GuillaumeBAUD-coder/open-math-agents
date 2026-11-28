import OMAStatements.S_mse_3709724

namespace MSE3709724Proof

open OMA.S_mse_3709724

private lemma log_one_add_le {t : ℝ} (ht : -1 < t) :
    Real.log (1 + t) ≤ t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4 + t ^ 5 / 5 := by
  let f : ℝ → ℝ := fun s => s - s ^ 2 / 2 + s ^ 3 / 3 - s ^ 4 / 4 + s ^ 5 / 5 - Real.log (1 + s)
  have hf_deriv : ∀ s : ℝ, -1 < s → HasDerivAt f (s ^ 5 / (1 + s)) s := by
    intro s hs
    have hpos : 1 + s ≠ 0 := by linarith
    have hlog : HasDerivAt (fun s => Real.log (1 + s)) (1 / (1 + s)) s := by
      have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 s := (hasDerivAt_id s).const_add 1
      simpa [div_eq_mul_inv] using h1.log hpos
    have hpoly : HasDerivAt
        (fun s : ℝ => s - s ^ 2 / 2 + s ^ 3 / 3 - s ^ 4 / 4 + s ^ 5 / 5)
        (1 - s + s ^ 2 - s ^ 3 + s ^ 4) s := by
      have d1 : HasDerivAt (fun s : ℝ => s) 1 s := hasDerivAt_id s
      have d2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) s s :=
        ((hasDerivAt_pow 2 s).div_const 2).congr_deriv (by norm_num)
      have d3 : HasDerivAt (fun s : ℝ => s ^ 3 / 3) (s ^ 2) s :=
        ((hasDerivAt_pow 3 s).div_const 3).congr_deriv (by norm_num)
      have d4 : HasDerivAt (fun s : ℝ => s ^ 4 / 4) (s ^ 3) s :=
        ((hasDerivAt_pow 4 s).div_const 4).congr_deriv (by norm_num)
      have d5 : HasDerivAt (fun s : ℝ => s ^ 5 / 5) (s ^ 4) s :=
        ((hasDerivAt_pow 5 s).div_const 5).congr_deriv (by norm_num)
      exact (((d1.sub d2).add d3).sub d4).add d5
    exact (hpoly.sub hlog).congr_deriv (by field_simp [hpos]; ring)
  have hf0 : f 0 = 0 := by simp [f]
  have hge : 0 ≤ f t := by
    by_cases h0 : 0 ≤ t
    · have hmono : MonotoneOn f (Set.Ici 0) := by
        refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
        · exact fun s hs => (hf_deriv s (by linarith [Set.mem_Ici.mp hs])).continuousAt.continuousWithinAt
        · intro s hs
          have hs0 : 0 < s := by simpa [interior_Ici] using hs
          exact (hf_deriv s (by linarith)).differentiableAt.differentiableWithinAt
        · intro s hs
          have hs0 : 0 < s := by simpa [interior_Ici] using hs
          rw [(hf_deriv s (by linarith)).deriv]
          positivity
      rw [← hf0]
      exact hmono (Set.mem_Ici.mpr le_rfl) h0 h0
    · push Not at h0
      have hanti : AntitoneOn f (Set.Ioc (-1) 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Ioc (-1) 0) ?_ ?_ ?_
        · exact fun s hs => (hf_deriv s hs.1).continuousAt.continuousWithinAt
        · intro s hs
          have hsm : s ∈ Set.Ioo (-1 : ℝ) 0 := by simpa [interior_Ioc] using hs
          exact (hf_deriv s hsm.1).differentiableAt.differentiableWithinAt
        · intro s hs
          have hsm : s ∈ Set.Ioo (-1 : ℝ) 0 := by simpa [interior_Ioc] using hs
          rw [(hf_deriv s hsm.1).deriv]
          have hnum : s ^ 5 ≤ 0 := by
            have : s ^ 5 = (s ^ 2) ^ 2 * s := by ring
            rw [this]
            exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hsm.2.le
          exact div_nonpos_of_nonpos_of_nonneg hnum (by linarith [hsm.1])
      rw [← hf0]
      exact hanti ⟨ht, h0.le⟩ ⟨by norm_num, le_rfl⟩ h0.le
  dsimp only [f] at hge
  linarith

private lemma exp_le_quad {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 20) :
    Real.exp y ≤ 1 + y + (11 / 20 : ℝ) * y ^ 2 := by
  have hexp_bound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 20 → Real.exp s ≤ 11 / 10 := by
    intro s hs0 hs1
    have h1 : 1 - s ≤ Real.exp (-s) := by linarith [Real.add_one_le_exp (-s)]
    rw [Real.exp_neg] at h1
    have hpos : 0 < Real.exp s := Real.exp_pos s
    have h2 : (1 - s) * Real.exp s ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h1 hpos.le
      rwa [inv_mul_cancel₀ hpos.ne'] at this
    nlinarith
  let g' : ℝ → ℝ := fun s => 1 + (11 / 10 : ℝ) * s - Real.exp s
  let g : ℝ → ℝ := fun s => 1 + s + (11 / 20 : ℝ) * s ^ 2 - Real.exp s
  have hg'_deriv : ∀ s : ℝ, HasDerivAt g' ((11 / 10 : ℝ) - Real.exp s) s := by
    intro s
    have d1 : HasDerivAt (fun s : ℝ => 1 + (11 / 10 : ℝ) * s) (11 / 10 : ℝ) s := by
      simpa using ((hasDerivAt_id s).const_mul (11 / 10 : ℝ)).const_add 1
    exact d1.sub (Real.hasDerivAt_exp s)
  have hg_deriv : ∀ s : ℝ, HasDerivAt g (g' s) s := by
    intro s
    have d1 : HasDerivAt (fun s : ℝ => 1 + s) 1 s := (hasDerivAt_id s).const_add 1
    have d2 : HasDerivAt (fun s : ℝ => (11 / 20 : ℝ) * s ^ 2) ((11 / 10 : ℝ) * s) s :=
      ((hasDerivAt_pow 2 s).const_mul (11 / 20 : ℝ)).congr_deriv (by norm_num; ring)
    exact (d1.add d2).sub (Real.hasDerivAt_exp s)
  have hg'_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) (1 / 20), 0 ≤ g' s := by
    have hmono : MonotoneOn g' (Set.Icc 0 (1 / 20)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 20)) ?_ ?_ ?_
      · exact fun s _ => (hg'_deriv s).continuousAt.continuousWithinAt
      · exact fun s _ => (hg'_deriv s).differentiableAt.differentiableWithinAt
      · intro s hs
        have hsm : s ∈ Set.Ioo (0 : ℝ) (1 / 20) := by simpa [interior_Icc] using hs
        rw [(hg'_deriv s).deriv]
        linarith [hexp_bound s hsm.1.le hsm.2.le]
    intro s hs
    have h0 : g' 0 = 0 := by simp [g']
    rw [← h0]
    exact hmono ⟨le_rfl, by norm_num⟩ hs hs.1
  have hg_mono : MonotoneOn g (Set.Icc 0 (1 / 20)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 20)) ?_ ?_ ?_
    · exact fun s _ => (hg_deriv s).continuousAt.continuousWithinAt
    · exact fun s _ => (hg_deriv s).differentiableAt.differentiableWithinAt
    · intro s hs
      have hsm : s ∈ Set.Ioo (0 : ℝ) (1 / 20) := by simpa [interior_Icc] using hs
      rw [(hg_deriv s).deriv]
      exact hg'_nonneg s ⟨hsm.1.le, hsm.2.le⟩
  have hg0 : g 0 = 0 := by simp [g]
  have hge : 0 ≤ g y := by
    rw [← hg0]
    exact hg_mono ⟨le_rfl, by norm_num⟩ ⟨hy0, hy1⟩ hy0
  dsimp only [g] at hge
  linarith

private lemma gamma_ratio_five {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x + 5) / Real.Gamma x =
      (x + 2) ^ 5 - 5 * (x + 2) ^ 3 + 4 * (x + 2) := by
  have h0 : x ≠ 0 := by linarith
  have h1 : x + 1 ≠ 0 := by linarith
  have h2 : x + 2 ≠ 0 := by linarith
  have h3 : x + 3 ≠ 0 := by linarith
  have h4 : x + 4 ≠ 0 := by linarith
  have g1 : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one h0
  have g2 : Real.Gamma (x + 2) = (x + 1) * Real.Gamma (x + 1) := by
    convert Real.Gamma_add_one h1 using 2; ring
  have g3 : Real.Gamma (x + 3) = (x + 2) * Real.Gamma (x + 2) := by
    convert Real.Gamma_add_one h2 using 2; ring
  have g4 : Real.Gamma (x + 4) = (x + 3) * Real.Gamma (x + 3) := by
    convert Real.Gamma_add_one h3 using 2; ring
  have g5 : Real.Gamma (x + 5) = (x + 4) * Real.Gamma (x + 4) := by
    convert Real.Gamma_add_one h4 using 2; ring
  have hgp : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  rw [g5, g4, g3, g2, g1]
  field_simp [hgp]
  ring

private lemma diff_ge_one {x : ℝ} (hx : 100 ≤ x) :
    (1 : ℝ) ≤ upper 5 x - Real.Gamma (x + 5) / Real.Gamma x := by
  set u := x + 2
  have hu : 102 ≤ u := by linarith
  have hu_pos : 0 < u := by linarith
  have hW : weightSum 5 x = 5 * u := by
    unfold weightSum
    norm_num
    linarith
  set P := ∏ j ∈ Finset.range 5, (x + (j : ℝ)) ^ (x + (j : ℝ))
  set G := P ^ (1 / weightSum 5 x)
  have hP_eq : P = (u - 2) ^ (u - 2) * (u - 1) ^ (u - 1) * u ^ u *
      (u + 1) ^ (u + 1) * (u + 2) ^ (u + 2) := by
    dsimp only [P]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    have e0 : x + (0 : ℕ) = u - 2 := by simp [u]
    have e1 : x + (1 : ℕ) = u - 1 := by simp [u]; ring
    have e2 : x + (2 : ℕ) = u := by simp [u]
    have e3 : x + (3 : ℕ) = u + 1 := by simp [u]; ring
    have e4 : x + (4 : ℕ) = u + 2 := by simp [u]; ring
    rw [e0, e1, e2, e3, e4]
  have hP_pos : 0 < P := by
    rw [hP_eq]
    have hp1 : 0 < u - 2 := by linarith
    have hp2 : 0 < u - 1 := by linarith
    have hp3 : 0 < u + 1 := by linarith
    have hp4 : 0 < u + 2 := by linarith
    positivity
  have hG_pos : 0 < G := Real.rpow_pos_of_pos hP_pos _
  have hlogG : Real.log G = (1 / (5 * u)) *
      ((u - 2) * Real.log (u - 2) + (u - 1) * Real.log (u - 1) + u * Real.log u +
       (u + 1) * Real.log (u + 1) + (u + 2) * Real.log (u + 2)) := by
    dsimp only [G]
    rw [Real.log_rpow hP_pos, hW, hP_eq]
    have h1 : 0 < (u - 2) ^ (u - 2) := Real.rpow_pos_of_pos (by linarith) _
    have h2 : 0 < (u - 1) ^ (u - 1) := Real.rpow_pos_of_pos (by linarith) _
    have h3 : 0 < u ^ u := Real.rpow_pos_of_pos hu_pos _
    have h4 : 0 < (u + 1) ^ (u + 1) := Real.rpow_pos_of_pos (by linarith) _
    have h5 : 0 < (u + 2) ^ (u + 2) := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.log_mul (by positivity) h5.ne',
      Real.log_mul (by positivity) h4.ne',
      Real.log_mul (by positivity) h3.ne',
      Real.log_mul h1.ne' h2.ne',
      Real.log_rpow (by linarith), Real.log_rpow (by linarith),
      Real.log_rpow hu_pos, Real.log_rpow (by linarith), Real.log_rpow (by linarith)]
  have hterm : ∀ d : ℝ, -2 ≤ d → d ≤ 2 →
      (u + d) * Real.log (u + d) ≤ (u + d) * Real.log u +
        d + d ^ 2 / (2 * u) - d ^ 3 / (6 * u ^ 2) + d ^ 4 / (12 * u ^ 3) -
        d ^ 5 / (20 * u ^ 4) + d ^ 6 / (5 * u ^ 5) := by
    intro d hd1 hd2
    have hdu : -1 < d / u := by
      rw [lt_div_iff₀ hu_pos]
      linarith
    have hsplit : u + d = u * (1 + d / u) := by field_simp [hu_pos.ne']
    have h1d_pos : 0 < 1 + d / u := by linarith
    have hlog := log_one_add_le hdu
    have hlog_eq : Real.log (u + d) = Real.log u + Real.log (1 + d / u) := by
      rw [hsplit, Real.log_mul hu_pos.ne' h1d_pos.ne']
    rw [hlog_eq]
    have hud_nonneg : 0 ≤ u + d := by linarith
    have hmul := mul_le_mul_of_nonneg_left hlog hud_nonneg
    have halg : (u + d) * (d / u - (d / u) ^ 2 / 2 + (d / u) ^ 3 / 3 -
        (d / u) ^ 4 / 4 + (d / u) ^ 5 / 5) =
        d + d ^ 2 / (2 * u) - d ^ 3 / (6 * u ^ 2) + d ^ 4 / (12 * u ^ 3) -
        d ^ 5 / (20 * u ^ 4) + d ^ 6 / (5 * u ^ 5) := by
      field_simp [hu_pos.ne']
      ring
    linarith
  have ht_m2 := hterm (-2) (by norm_num) (by norm_num)
  have ht_m1 := hterm (-1) (by norm_num) (by norm_num)
  have ht_p1 := hterm 1 (by norm_num) (by norm_num)
  have ht_p2 := hterm 2 (by norm_num) (by norm_num)
  have hlogG_le : Real.log G ≤ Real.log u + 1 / u ^ 2 + 3 / (5 * u ^ 4) := by
    have hsum : (u - 2) * Real.log (u - 2) + (u - 1) * Real.log (u - 1) + u * Real.log u +
        (u + 1) * Real.log (u + 1) + (u + 2) * Real.log (u + 2) ≤
        5 * u * Real.log u + 5 / u + 17 / (6 * u ^ 3) + 26 / u ^ 5 := by
      have e1 : u + (-2 : ℝ) = u - 2 := by ring
      have e2 : u + (-1 : ℝ) = u - 1 := by ring
      rw [e1] at ht_m2
      rw [e2] at ht_m1
      have : (5 : ℝ) / u + 17 / (6 * u ^ 3) + 26 / u ^ 5 =
          ((-2) + (-2) ^ 2 / (2 * u) - (-2) ^ 3 / (6 * u ^ 2) + (-2) ^ 4 / (12 * u ^ 3) -
            (-2) ^ 5 / (20 * u ^ 4) + (-2) ^ 6 / (5 * u ^ 5)) +
          ((-1) + (-1) ^ 2 / (2 * u) - (-1) ^ 3 / (6 * u ^ 2) + (-1) ^ 4 / (12 * u ^ 3) -
            (-1) ^ 5 / (20 * u ^ 4) + (-1) ^ 6 / (5 * u ^ 5)) +
          (1 + 1 ^ 2 / (2 * u) - 1 ^ 3 / (6 * u ^ 2) + 1 ^ 4 / (12 * u ^ 3) -
            1 ^ 5 / (20 * u ^ 4) + 1 ^ 6 / (5 * u ^ 5)) +
          (2 + 2 ^ 2 / (2 * u) - 2 ^ 3 / (6 * u ^ 2) + 2 ^ 4 / (12 * u ^ 3) -
            2 ^ 5 / (20 * u ^ 4) + 2 ^ 6 / (5 * u ^ 5)) := by
        field_simp [hu_pos.ne']
        ring
      linarith
    have hdiv := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 1 / (5 * u))
    rw [← hlogG] at hdiv
    have htail : 1 / (5 * u) * (5 * u * Real.log u + 5 / u + 17 / (6 * u ^ 3) + 26 / u ^ 5) ≤
        Real.log u + 1 / u ^ 2 + 3 / (5 * u ^ 4) := by
      have hdiff : Real.log u + 1 / u ^ 2 + 3 / (5 * u ^ 4) -
          1 / (5 * u) * (5 * u * Real.log u + 5 / u + 17 / (6 * u ^ 3) + 26 / u ^ 5) =
          (u ^ 2 - 156) / (30 * u ^ 6) := by
        field_simp [hu_pos.ne']
        ring
      have hnn : 0 ≤ (u ^ 2 - 156) / (30 * u ^ 6) := by
        apply div_nonneg
        · nlinarith
        · positivity
      linarith
    linarith
  set y := 1 / u ^ 2 + 3 / (5 * u ^ 4)
  have hu2 : (10000 : ℝ) ≤ u ^ 2 := by nlinarith only [hu]
  have hu4 : (100000000 : ℝ) ≤ u ^ 4 := by nlinarith only [hu2]
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 / 20 := by
    dsimp only [y]
    have h1 : 1 / u ^ 2 ≤ 1 / (10000 : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith only [hu2]
    have h2 : 3 / (5 * u ^ 4) ≤ 1 / (10000 : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith only [hu4]
    linarith only [h1, h2]
  have hlogG_y : Real.log G ≤ Real.log u + y := by
    dsimp only [y]; linarith only [hlogG_le]
  have hG_le_exp : G ≤ u * Real.exp y := by
    have h1 : Real.exp (Real.log G) ≤ Real.exp (Real.log u + y) :=
      Real.exp_le_exp.mpr hlogG_y
    rwa [Real.exp_log hG_pos, Real.exp_add, Real.exp_log hu_pos] at h1
  have hG_le : G ≤ u + 1 / u + (29 / 25 : ℝ) / u ^ 3 := by
    have hexp := exp_le_quad hy0 hy1
    have h1 : G ≤ u * (1 + y + (11 / 20 : ℝ) * y ^ 2) :=
      le_trans hG_le_exp (mul_le_mul_of_nonneg_left hexp hu_pos.le)
    have h2 : u + 1 / u + (29 / 25 : ℝ) / u ^ 3 - u * (1 + y + (11 / 20 : ℝ) * y ^ 2) =
        (5 * u ^ 4 - 330 * u ^ 2 - 99) / (500 * u ^ 7) := by
      dsimp only [y]
      field_simp [hu_pos.ne']
      ring
    have hnn : 0 ≤ (5 * u ^ 4 - 330 * u ^ 2 - 99) / (500 * u ^ 7) := by
      apply div_nonneg
      · nlinarith only [hu2]
      · positivity
    linarith only [h1, h2, hnn]
  have hbase_le : u - 1 / u - (29 / 25 : ℝ) / u ^ 3 ≤ weightSum 5 x / ((5 : ℕ) / 2 : ℝ) - G := by
    have h2u : weightSum 5 x / ((5 : ℕ) / 2 : ℝ) = 2 * u := by
      rw [hW]; push_cast; ring
    rw [h2u]
    linarith only [hG_le]
  have hbase_pos : 0 ≤ u - 1 / u - (29 / 25 : ℝ) / u ^ 3 := by
    have h1 : 1 / u ≤ 1 := by rw [div_le_one hu_pos]; linarith only [hu]
    have h2 : (29 / 25 : ℝ) / u ^ 3 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith only [hu, hu2]
    linarith only [hu, h1, h2]
  have hup_ge : (u - 1 / u - (29 / 25 : ℝ) / u ^ 3) ^ 5 ≤ upper 5 x := by
    unfold upper
    exact pow_le_pow_left₀ hbase_pos hbase_le 5
  rw [gamma_ratio_five (by linarith only [hx])]
  have hpoly : (u - 1 / u - (29 / 25 : ℝ) / u ^ 3) ^ 5 - (u ^ 5 - 5 * u ^ 3 + 4 * u) ≥ 1 := by
    set a := 1 / u + (29 / 25 : ℝ) / u ^ 3
    have ha_pos : 0 < a := by positivity
    have ha_ge : 1 / u ≤ a := by
      dsimp only [a]; linarith only [show (0 : ℝ) ≤ (29 / 25 : ℝ) / u ^ 3 by positivity]
    have ha_le : a ≤ 2 / u := by
      dsimp only [a]
      have h1 : (29 / 25 : ℝ) / u ^ 3 ≤ 1 / u := by
        rw [div_le_div_iff₀ (by positivity) hu_pos]
        nlinarith only [hu, hu2]
      have h2u : 1 / u + 1 / u = 2 / u := by ring
      linarith only [h1, h2u]
    have h4 : 5 * u ^ 4 * a = 5 * u ^ 3 + (29 / 5 : ℝ) * u := by
      dsimp only [a]
      field_simp [hu_pos.ne']
      ring
    have h3 : 10 * u ≤ 10 * u ^ 3 * a ^ 2 := by
      have hsq : (1 / u) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by positivity) ha_ge 2
      have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 10 * u ^ 3)
      have heq : 10 * u ^ 3 * (1 / u) ^ 2 = 10 * u := by field_simp [hu_pos.ne']
      linarith only [hmul, heq]
    have h2 : 10 * u ^ 2 * a ^ 3 ≤ 1 := by
      have hcu : a ^ 3 ≤ (2 / u) ^ 3 := pow_le_pow_left₀ ha_pos.le ha_le 3
      have hmul := mul_le_mul_of_nonneg_left hcu (by positivity : 0 ≤ 10 * u ^ 2)
      have heq : 10 * u ^ 2 * (2 / u) ^ 3 = 80 / u := by field_simp [hu_pos.ne']; ring
      have h80 : 80 / u ≤ 1 := by rw [div_le_one hu_pos]; linarith only [hu]
      linarith only [hmul, heq, h80]
    have h1 : a ^ 5 ≤ 1 := by
      have hle1 : a ≤ 1 := by
        have : 2 / u ≤ 1 := by rw [div_le_one hu_pos]; linarith only [hu]
        linarith only [ha_le, this]
      exact pow_le_one₀ ha_pos.le hle1
    have h5 : 0 ≤ 5 * u * a ^ 4 := by positivity
    have hexp : (u - 1 / u - (29 / 25 : ℝ) / u ^ 3) ^ 5 =
        u ^ 5 - 5 * u ^ 4 * a + 10 * u ^ 3 * a ^ 2 - 10 * u ^ 2 * a ^ 3 + 5 * u * a ^ 4 - a ^ 5 := by
      dsimp only [a]; ring
    linarith only [hu, h1, h2, h3, h4, h5, hexp]
  linarith only [hup_ge, hpoly]

end MSE3709724Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_3709724.main) := by
  intro h
  have htend := h.2 5 (by norm_num)
  have hev : ∀ᶠ x in Filter.atTop,
      OMA.S_mse_3709724.upper 5 x - Real.Gamma (x + 5) / Real.Gamma x < 1 :=
    htend.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Set.Iio 1))
  rw [Filter.eventually_atTop] at hev
  rcases hev with ⟨M, hM⟩
  have h1 := MSE3709724Proof.diff_ge_one (x := max M 100) (le_max_right M 100)
  have h2 := hM (max M 100) (le_max_left M 100)
  linarith only [h1, h2]
