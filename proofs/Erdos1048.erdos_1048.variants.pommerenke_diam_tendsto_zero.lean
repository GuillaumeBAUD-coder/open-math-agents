import FormalConjectures.ErdosProblems.«1048»

-- Problem: Erdős Problem 1048 — pommerenke diam tendsto zero
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1048.lean:79 (declaration Erdos1048.erdos_1048.variants.pommerenke_diam_tendsto_zero)
-- Credit: @michielkosters (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @Erdos1048.erdos_1048.variants.pommerenke_diam_tendsto_zero := by
  intro r hr ε hε
  set δ : ℝ := min (ε / 6) (r / 2)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ_lt_r : δ < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h2δ : 2 * δ ≤ ε / 3 := by
    have : δ ≤ ε / 6 := min_le_left _ _
    linarith
  have hr_pos : 0 < r := by linarith
  have h1 : ∀ᶠ n : ℕ in Filter.atTop, 3 ≤ n := Filter.eventually_ge_atTop 3
  have h2 : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ r ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hr).eventually_ge_atTop 2
  have h3 : ∀ᶠ n : ℕ in Filter.atTop, ((r - δ) / r) ^ n ≤ 1 / 2 := by
    have hq_nonneg : 0 ≤ (r - δ) / r := div_nonneg (by linarith) hr_pos.le
    have hq_lt_one : (r - δ) / r < 1 := (div_lt_one hr_pos).2 (by linarith)
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one).eventually_le_const (by norm_num)
  have h4 : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ ((r + δ) / r) ^ n := by
    have hq_gt_one : 1 < (r + δ) / r := (one_lt_div hr_pos).2 (by linarith)
    exact (tendsto_pow_atTop_atTop_of_one_lt hq_gt_one).eventually_ge_atTop 2
  have h5 : ∀ᶠ n : ℕ in Filter.atTop, 4 * Real.tan (Real.pi / (n : ℝ)) * (r + δ) ≤ ε / 3 := by
    have ht_div : Filter.Tendsto (fun n : ℕ => Real.pi / (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have ht_tan : Filter.Tendsto (fun n : ℕ => Real.tan (Real.pi / (n : ℝ))) Filter.atTop (nhds 0) := by
      have hsc : ContinuousAt (fun x => Real.sin x / Real.cos x) 0 :=
        Real.continuous_sin.continuousAt.div Real.continuous_cos.continuousAt (by simp)
      have h0 : Real.sin 0 / Real.cos 0 = 0 := by simp
      have ht_sc : Filter.Tendsto (fun n : ℕ => Real.sin (Real.pi / (n : ℝ)) / Real.cos (Real.pi / (n : ℝ)))
          Filter.atTop (nhds 0) := h0 ▸ hsc.tendsto.comp ht_div
      simpa only [Real.tan_eq_sin_div_cos] using ht_sc
    have ht_prod : Filter.Tendsto (fun n : ℕ => 4 * Real.tan (Real.pi / (n : ℝ)) * (r + δ))
        Filter.atTop (nhds 0) := by
      simpa using (ht_tan.const_mul 4).mul_const (r + δ)
    exact ht_prod.eventually_le_const (by linarith)
  filter_upwards [h1, h2, h3, h4, h5] with n hn3 hn_r2 hn_sub hn_add hn_tan
  intro f hf z hz
  have hn_pos : 0 < n := by omega
  have hrn_ge2 : (2 : ℝ) ≤ r ^ n := hn_r2
  have h_eval : ∀ w : ℂ, w ∈ Erdos1043.levelSet f → ‖w ^ n - (r : ℂ) ^ n‖ ≤ 1 := by
    intro w hw
    simpa [Erdos1043.levelSet, hf] using hw
  have h_sub_pow : (r - δ) ^ n ≤ r ^ n - 1 := by
    have h_eq : (r - δ) ^ n = ((r - δ) / r) ^ n * r ^ n := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hr_pos.ne')]
    have h_rn_nonneg : 0 ≤ r ^ n := pow_nonneg hr_pos.le n
    calc (r - δ) ^ n = ((r - δ) / r) ^ n * r ^ n := h_eq
      _ ≤ (1 / 2) * r ^ n := mul_le_mul_of_nonneg_right hn_sub h_rn_nonneg
      _ ≤ r ^ n - 1 := by linarith
  have h_add_pow : r ^ n + 1 ≤ (r + δ) ^ n := by
    have h_eq : (r + δ) ^ n = ((r + δ) / r) ^ n * r ^ n := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hr_pos.ne')]
    have h_rn_nonneg : 0 ≤ r ^ n := pow_nonneg hr_pos.le n
    calc r ^ n + 1 ≤ 2 * r ^ n := by linarith
      _ ≤ ((r + δ) / r) ^ n * r ^ n := mul_le_mul_of_nonneg_right hn_add h_rn_nonneg
      _ = (r + δ) ^ n := h_eq.symm
  have h_norm_bounds : ∀ w : ℂ, w ∈ Erdos1043.levelSet f → r - δ ≤ ‖w‖ ∧ ‖w‖ ≤ r + δ := by
    intro w hw
    have hwn := h_eval w hw
    have hrn_norm : ‖(r : ℂ) ^ n‖ = r ^ n := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hr_pos.le]
    have h_up : ‖w‖ ^ n ≤ (r + δ) ^ n := by
      calc ‖w‖ ^ n = ‖w ^ n‖ := (norm_pow w n).symm
        _ = ‖(w ^ n - (r : ℂ) ^ n) + (r : ℂ) ^ n‖ := by ring_nf
        _ ≤ ‖w ^ n - (r : ℂ) ^ n‖ + ‖(r : ℂ) ^ n‖ := norm_add_le _ _
        _ ≤ 1 + r ^ n := by linarith
        _ ≤ (r + δ) ^ n := by linarith
    have h_lo : (r - δ) ^ n ≤ ‖w‖ ^ n := by
      have h_tri : r ^ n ≤ ‖w ^ n - (r : ℂ) ^ n‖ + ‖w‖ ^ n := by
        calc r ^ n = ‖(r : ℂ) ^ n‖ := hrn_norm.symm
          _ = ‖(r : ℂ) ^ n - w ^ n + w ^ n‖ := by ring_nf
          _ ≤ ‖(r : ℂ) ^ n - w ^ n‖ + ‖w ^ n‖ := norm_add_le _ _
          _ = ‖w ^ n - (r : ℂ) ^ n‖ + ‖w‖ ^ n := by rw [norm_sub_rev, norm_pow]
      linarith
    refine ⟨le_of_pow_le_pow_left₀ hn_pos.ne' (norm_nonneg w) h_lo,
      le_of_pow_le_pow_left₀ hn_pos.ne' (by linarith) h_up⟩
  have h_re_pos : ∀ w : ℂ, w ∈ Erdos1043.levelSet f → 0 < (w ^ n).re := by
    intro w hw
    have hwn := h_eval w hw
    have h_abs_re : |((r : ℂ) ^ n - w ^ n).re| ≤ ‖(r : ℂ) ^ n - w ^ n‖ :=
      Complex.abs_re_le_norm _
    have h_re_eq : ((r : ℂ) ^ n - w ^ n).re = r ^ n - (w ^ n).re := by
      simp [Complex.sub_re, ← Complex.ofReal_pow]
    rw [norm_sub_rev] at h_abs_re
    have : r ^ n - (w ^ n).re ≤ 1 := by
      linarith [le_abs_self ((r : ℂ) ^ n - w ^ n).re]
    linarith
  have hz_norm := h_norm_bounds z hz
  have hz_ne : z ≠ 0 := by
    intro h0
    subst h0
    simp at hz_norm
    linarith
  set θ₀ : ℝ := Real.pi / (n : ℝ)
  have hθ₀_pos : 0 < θ₀ := div_pos Real.pi_pos (Nat.cast_pos.mpr hn_pos)
  have hθ₀_lt : θ₀ < Real.pi / 2 := by
    have hn_cast : (2 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 2 < n)
    exact div_lt_div_of_pos_left Real.pi_pos zero_lt_two hn_cast
  have hcos_pos : 0 < Real.cos θ₀ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ₀_lt⟩
  have htan_pos : 0 < Real.tan θ₀ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ₀_pos hθ₀_lt
  let U₁ : Set ℂ := {w : ℂ | |(w / z).im| < Real.tan θ₀ * (w / z).re}
  let U₂ : Set ℂ := {w : ℂ | Real.tan θ₀ * (w / z).re < |(w / z).im|}
  have hg_cont : Continuous (fun w : ℂ => w / z) := continuous_id.div_const z
  have hU₁_open : IsOpen U₁ := by
    have hc : Continuous (fun w : ℂ => |(w / z).im| - Real.tan θ₀ * (w / z).re) :=
      (Complex.continuous_im.comp hg_cont).abs.sub (continuous_const.mul (Complex.continuous_re.comp hg_cont))
    simpa [U₁, sub_lt_zero] using isOpen_lt hc continuous_zero
  have hU₂_open : IsOpen U₂ := by
    have hc : Continuous (fun w : ℂ => Real.tan θ₀ * (w / z).re - |(w / z).im|) :=
      (continuous_const.mul (Complex.continuous_re.comp hg_cont)).sub (Complex.continuous_im.comp hg_cont).abs
    simpa [U₂, sub_lt_zero] using isOpen_lt hc continuous_zero
  have hU_disj : U₁ ∩ U₂ = ∅ := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1' h2'
    change |(w / z).im| < Real.tan θ₀ * (w / z).re at h1'
    change Real.tan θ₀ * (w / z).re < |(w / z).im| at h2'
    linarith
  have hz_U₁ : z ∈ U₁ := by
    simp [U₁, div_self hz_ne, htan_pos]
  let C := connectedComponentIn (Erdos1043.levelSet f) z
  have hC_sub_level : C ⊆ Erdos1043.levelSet f := connectedComponentIn_subset _ _
  have hlevel_sub_union : Erdos1043.levelSet f ⊆ U₁ ∪ U₂ := by
    intro w hw
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    have hnot1 : ¬ |(w / z).im| < Real.tan θ₀ * (w / z).re := hnot.1
    have hnot2 : ¬ Real.tan θ₀ * (w / z).re < |(w / z).im| := hnot.2
    have h_eq : |(w / z).im| = Real.tan θ₀ * (w / z).re := le_antisymm (not_lt.mp hnot2) (not_lt.mp hnot1)
    set u : ℂ := w / z
    have hw_norm := h_norm_bounds w hw
    have hw_ne : w ≠ 0 := by
      intro h0
      subst h0
      simp at hw_norm
      linarith
    have hu_ne : u ≠ 0 := div_ne_zero hw_ne hz_ne
    have hu_re_nonneg : 0 ≤ u.re := by
      have : 0 ≤ Real.tan θ₀ * u.re := by linarith [abs_nonneg u.im]
      exact (mul_nonneg_iff_of_pos_left htan_pos).mp this
    have hu_re_pos : 0 < u.re := by
      refine lt_of_le_of_ne hu_re_nonneg ?_
      intro h0
      have him0 : u.im = 0 := by
        have : |u.im| = 0 := by rw [h_eq, ← h0, mul_zero]
        exact abs_eq_zero.mp this
      exact hu_ne (Complex.ext h0.symm him0)
    set c : ℝ := u.re / Real.cos θ₀
    have hc_pos : 0 < c := div_pos hu_re_pos hcos_pos
    set θ : ℝ := if 0 ≤ u.im then θ₀ else -θ₀
    have hu_polar : u = (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one,
          sub_self, add_zero]
        by_cases him : 0 ≤ u.im
        · simp [θ, him, c, div_mul_cancel₀ _ hcos_pos.ne']
        · simp [θ, him, c, Real.cos_neg, div_mul_cancel₀ _ hcos_pos.ne']
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          zero_add, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero]
        by_cases him : 0 ≤ u.im
        · have him_eq : u.im = Real.tan θ₀ * u.re := by linarith [abs_of_nonneg him]
          simp only [θ, him, ↓reduceIte, c]
          rw [him_eq, Real.tan_eq_sin_div_cos]
          ring
        · have him_neg : u.im < 0 := lt_of_not_ge him
          have him_eq : u.im = -(Real.tan θ₀ * u.re) := by linarith [abs_of_neg him_neg]
          simp only [θ, him, ↓reduceIte, c, Real.sin_neg]
          rw [him_eq, Real.tan_eq_sin_div_cos]
          ring
    have hu_pow : u ^ n = -((c : ℂ) ^ n) := by
      rw [hu_polar, mul_pow, ← Complex.exp_nat_mul]
      have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
      have hexp : Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) = -1 := by
        by_cases him : 0 ≤ u.im
        · have harg : (n : ℂ) * ((θ : ℂ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
            simp only [θ, him, ↓reduceIte, θ₀, Complex.ofReal_div, Complex.ofReal_natCast]
            field_simp [hn_ne]
          rw [harg, Complex.exp_pi_mul_I]
        · have harg : (n : ℂ) * ((θ : ℂ) * Complex.I) = -((Real.pi : ℂ) * Complex.I) := by
            simp only [θ, him, ↓reduceIte, θ₀, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_natCast]
            field_simp [hn_ne]
          rw [harg, Complex.exp_neg, Complex.exp_pi_mul_I]
          norm_num
      rw [hexp]
      ring
    have hwn_eq : w ^ n = -((c : ℂ) ^ n) * z ^ n := by
      have hw_eq : w = u * z := (div_mul_cancel₀ w hz_ne).symm
      rw [hw_eq, mul_pow, hu_pow]
    have hwn_re : (w ^ n).re = -(c ^ n * (z ^ n).re) := by
      rw [hwn_eq]
      simp [← Complex.ofReal_pow]
    have hre_w := h_re_pos w hw
    have hre_z := h_re_pos z hz
    have hprod_nonneg : 0 ≤ c ^ n * (z ^ n).re := mul_nonneg (pow_nonneg hc_pos.le n) hre_z.le
    linarith
  have hC_conn : IsPreconnected C := isPreconnected_connectedComponentIn
  have hC_sub_U₁ : C ⊆ U₁ := by
    intro w hwC
    have hw_union : w ∈ U₁ ∪ U₂ := hlevel_sub_union (hC_sub_level hwC)
    rcases hw_union with hwU₁ | hwU₂
    · exact hwU₁
    · exfalso
      have hzC : z ∈ C := mem_connectedComponentIn hz
      have hne := hC_conn U₁ U₂ hU₁_open hU₂_open (hC_sub_level.trans hlevel_sub_union)
        ⟨z, hzC, hz_U₁⟩ ⟨w, hwC, hwU₂⟩
      rcases hne with ⟨x, _, hx⟩
      rw [hU_disj] at hx
      exact hx
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_ofReal_iff hε |>.mpr (by linarith : 2 * ε / 3 < ε))
  apply Metric.ediam_le
  intro w₁ hw₁ w₂ hw₂
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  have hw₁_level : w₁ ∈ Erdos1043.levelSet f := hC_sub_level hw₁
  have hw₂_level : w₂ ∈ Erdos1043.levelSet f := hC_sub_level hw₂
  have hw₁_norm := h_norm_bounds w₁ hw₁_level
  have hw₂_norm := h_norm_bounds w₂ hw₂_level
  have hw₁_U₁ : w₁ ∈ U₁ := hC_sub_U₁ hw₁
  have hw₂_U₁ : w₂ ∈ U₁ := hC_sub_U₁ hw₂
  set u₁ : ℂ := w₁ / z
  set u₂ : ℂ := w₂ / z
  have hu₁_im : |u₁.im| < Real.tan θ₀ * u₁.re := hw₁_U₁
  have hu₂_im : |u₂.im| < Real.tan θ₀ * u₂.re := hw₂_U₁
  have hu₁_re_pos : 0 < u₁.re :=
    (mul_pos_iff_of_pos_left htan_pos).mp (lt_of_le_of_lt (abs_nonneg u₁.im) hu₁_im)
  have hu₂_re_pos : 0 < u₂.re :=
    (mul_pos_iff_of_pos_left htan_pos).mp (lt_of_le_of_lt (abs_nonneg u₂.im) hu₂_im)
  have hu₁_re_le : u₁.re ≤ ‖u₁‖ := (le_abs_self u₁.re).trans (Complex.abs_re_le_norm u₁)
  have hu₂_re_le : u₂.re ≤ ‖u₂‖ := (le_abs_self u₂.re).trans (Complex.abs_re_le_norm u₂)
  have hnorm_le : ∀ u : ℂ, 0 < u.re → ‖u‖ - u.re ≤ |u.im| := by
    intro u hu_pos
    have htri : ‖u‖ ≤ ‖(u.re : ℂ)‖ + ‖(u.im : ℂ) * Complex.I‖ := by
      simpa [Complex.re_add_im u] using norm_add_le (u.re : ℂ) ((u.im : ℂ) * Complex.I)
    have hre_n : ‖(u.re : ℂ)‖ = u.re := by
      rw [Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
    have him_n : ‖(u.im : ℂ) * Complex.I‖ = |u.im| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hdiff_u : ‖u₁ - u₂‖ ≤ 2 * Real.tan θ₀ * ‖u₁‖ + 2 * Real.tan θ₀ * ‖u₂‖ + |‖u₁‖ - ‖u₂‖| := by
    have htri : ‖u₁ - u₂‖ ≤ |u₁.re - u₂.re| + |u₁.im - u₂.im| := by
      have h1' : ‖u₁ - u₂‖ ≤ ‖((u₁ - u₂).re : ℂ)‖ + ‖((u₁ - u₂).im : ℂ) * Complex.I‖ := by
        calc ‖u₁ - u₂‖ = ‖((u₁ - u₂).re : ℂ) + ((u₁ - u₂).im : ℂ) * Complex.I‖ := by
              rw [Complex.re_add_im]
          _ ≤ ‖((u₁ - u₂).re : ℂ)‖ + ‖((u₁ - u₂).im : ℂ) * Complex.I‖ := norm_add_le _ _
      have h2' : ‖((u₁ - u₂).re : ℂ)‖ = |u₁.re - u₂.re| := by
        rw [Complex.norm_real, Real.norm_eq_abs, Complex.sub_re]
      have h3' : ‖((u₁ - u₂).im : ℂ) * Complex.I‖ = |u₁.im - u₂.im| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, Complex.sub_im]
      linarith
    have hre_diff : |u₁.re - u₂.re| ≤ |u₁.im| + |‖u₁‖ - ‖u₂‖| + |u₂.im| := by
      have hsplit : u₁.re - u₂.re = (u₁.re - ‖u₁‖) + (‖u₁‖ - ‖u₂‖) + (‖u₂‖ - u₂.re) := by ring
      rw [hsplit]
      have hA : |u₁.re - ‖u₁‖| = ‖u₁‖ - u₁.re := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hu₁_re_le)]
      have hB : |‖u₂‖ - u₂.re| = ‖u₂‖ - u₂.re := abs_of_nonneg (sub_nonneg.mpr hu₂_re_le)
      have h_tri1 := abs_add_le ((u₁.re - ‖u₁‖) + (‖u₁‖ - ‖u₂‖)) (‖u₂‖ - u₂.re)
      have h_tri2 := abs_add_le (u₁.re - ‖u₁‖) (‖u₁‖ - ‖u₂‖)
      linarith [hnorm_le u₁ hu₁_re_pos, hnorm_le u₂ hu₂_re_pos]
    have him_diff : |u₁.im - u₂.im| ≤ |u₁.im| + |u₂.im| := abs_sub u₁.im u₂.im
    have hu₁_bound : |u₁.im| ≤ Real.tan θ₀ * ‖u₁‖ :=
      hu₁_im.le.trans (mul_le_mul_of_nonneg_left hu₁_re_le htan_pos.le)
    have hu₂_bound : |u₂.im| ≤ Real.tan θ₀ * ‖u₂‖ :=
      hu₂_im.le.trans (mul_le_mul_of_nonneg_left hu₂_re_le htan_pos.le)
    linarith
  have hdist_w : dist w₁ w₂ ≤ 4 * Real.tan θ₀ * (r + δ) + 2 * δ := by
    rw [dist_eq_norm]
    have hw_eq : w₁ - w₂ = z * (u₁ - u₂) := by
      simp only [u₁, u₂]
      field_simp [hz_ne]
    rw [hw_eq, norm_mul]
    have hz_u₁ : ‖z‖ * ‖u₁‖ = ‖w₁‖ := by
      simp only [u₁, norm_div]
      exact mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hz_ne)
    have hz_u₂ : ‖z‖ * ‖u₂‖ = ‖w₂‖ := by
      simp only [u₂, norm_div]
      exact mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hz_ne)
    have hz_diff : ‖z‖ * |‖u₁‖ - ‖u₂‖| = |‖w₁‖ - ‖w₂‖| := by
      rw [← abs_of_nonneg (norm_nonneg z), ← abs_mul, mul_sub, hz_u₁, hz_u₂]
    have hnorm_diff_w : |‖w₁‖ - ‖w₂‖| ≤ 2 * δ := by
      rw [abs_le]
      constructor <;> linarith
    have hmul := mul_le_mul_of_nonneg_left hdiff_u (norm_nonneg z)
    have h_alg : ‖z‖ * (2 * Real.tan θ₀ * ‖u₁‖ + 2 * Real.tan θ₀ * ‖u₂‖ + |‖u₁‖ - ‖u₂‖|) =
        2 * Real.tan θ₀ * (‖z‖ * ‖u₁‖) + 2 * Real.tan θ₀ * (‖z‖ * ‖u₂‖) + ‖z‖ * |‖u₁‖ - ‖u₂‖| := by
      ring
    rw [h_alg, hz_u₁, hz_u₂, hz_diff] at hmul
    have hsum_w : 2 * Real.tan θ₀ * ‖w₁‖ + 2 * Real.tan θ₀ * ‖w₂‖ ≤ 4 * Real.tan θ₀ * (r + δ) := by
      have h1' : 2 * Real.tan θ₀ * ‖w₁‖ ≤ 2 * Real.tan θ₀ * (r + δ) :=
        mul_le_mul_of_nonneg_left hw₁_norm.2 (by linarith [htan_pos])
      have h2' : 2 * Real.tan θ₀ * ‖w₂‖ ≤ 2 * Real.tan θ₀ * (r + δ) :=
        mul_le_mul_of_nonneg_left hw₂_norm.2 (by linarith [htan_pos])
      linarith
    linarith
  linarith
