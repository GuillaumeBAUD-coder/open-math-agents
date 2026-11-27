import OMAReductions.R_Erdos499_vanDerWaerden_R1

-- Step Erdos499.vanDerWaerden.R1.H3: hypothesis H3 of reduction Erdos499.vanDerWaerden.R1
-- Credit: @michielkosters
-- H3 := ∀ (d m : ℕ), 1 ≤ d → m ≤ d → ∀ (a : ℝ) (r : Fin m → ℝ) (L D : ℝ), 0 ≤ a → (∀ i, 0 ≤ r i) →     (∀ t : ℝ, 0 < t → L * t ≤ a * ∏ i, (t + r i)) →     HasDerivAt (fun t : ℝ => a * ∏ i, (t + r i)) D 0 →     (((d : ℝ) - 1) / d) ^ (d - 1) * L ≤ D  /-- Weighted AM-GM: for doubly stochastic `M` and positive `x`, `prod x ≤ prod (M x)`. -/

open Finset

private lemma hasDerivAt_finset_prod_add {ι : Type*} [DecidableEq ι] (s : Finset ι) (r : ι → ℝ) :
    HasDerivAt (fun t : ℝ => ∏ i ∈ s, (t + r i)) (∑ i ∈ s, ∏ j ∈ s.erase i, r j) 0 := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact hasDerivAt_const 0 (1 : ℝ)
  | insert a s ha ih =>
    have hprod : (fun t : ℝ => ∏ i ∈ insert a s, (t + r i)) =
        fun t => (t + r a) * ∏ i ∈ s, (t + r i) := by
      ext t; exact Finset.prod_insert ha
    rw [hprod]
    have h1 : HasDerivAt (fun t : ℝ => t + r a) 1 0 := (hasDerivAt_id 0).add_const (r a)
    have hmul := h1.mul ih
    have hderiv_eq : (∑ i ∈ insert a s, ∏ j ∈ (insert a s).erase i, r j) =
        1 * (∏ i ∈ s, (0 + r i)) + (0 + r a) * (∑ i ∈ s, ∏ j ∈ s.erase i, r j) := by
      simp only [zero_add, one_mul]
      rw [Finset.sum_insert ha, Finset.erase_insert ha]
      have hsum : ∑ i ∈ s, ∏ j ∈ (insert a s).erase i, r j =
          r a * ∑ i ∈ s, ∏ j ∈ s.erase i, r j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : a ≠ i := fun h => ha (h ▸ hi)
        have herase : (insert a s).erase i = insert a (s.erase i) := by
          ext x
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨hxne, rfl | hxs⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hxne, hxs⟩
          · rintro (rfl | ⟨hxne, hxs⟩)
            · exact ⟨hne, Or.inl rfl⟩
            · exact ⟨hxne, Or.inr hxs⟩
        rw [herase, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      rw [hsum]
    rw [hderiv_eq]
    exact hmul

private lemma bernoulli_ineq {x : ℝ} (hx : -1 ≤ x) (n : ℕ) :
    1 + (n : ℝ) * x ≤ (1 + x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1x : 0 ≤ 1 + x := by linarith
    have hsq : (0 : ℝ) ≤ (n : ℝ) * x ^ 2 := by positivity
    calc 1 + ((n + 1 : ℕ) : ℝ) * x
        ≤ (1 + (n : ℝ) * x) * (1 + x) := by push_cast; linarith
      _ ≤ (1 + x) ^ n * (1 + x) := mul_le_mul_of_nonneg_right ih h1x
      _ = (1 + x) ^ (n + 1) := by rw [pow_succ]

private lemma one_add_div_pow_step {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 ≤ u) :
    (1 + u / n) ^ n ≤ (1 + u / (n + 1 : ℕ)) ^ (n + 1) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnu_pos : (0 : ℝ) < (n : ℝ) + u := by linarith
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have h1un_pos : (0 : ℝ) < 1 + u / n := by positivity
  set x : ℝ := -u / (((n : ℝ) + 1) * ((n : ℝ) + u))
  have hx : -1 ≤ x := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hbern := bernoulli_ineq hx (n + 1)
  have hL : 1 + ((n + 1 : ℕ) : ℝ) * x = (1 + u / n)⁻¹ := by
    push_cast
    dsimp [x]
    field_simp
    ring
  have hR : 1 + x = (1 + u / ((n + 1 : ℕ) : ℝ)) / (1 + u / n) := by
    push_cast
    dsimp [x]
    field_simp
    ring
  rw [hL, hR, div_pow] at hbern
  have hpow_pos : 0 < (1 + u / n) ^ (n + 1) := pow_pos h1un_pos _
  have hmul := mul_le_mul_of_nonneg_right hbern hpow_pos.le
  rw [div_mul_cancel₀ _ hpow_pos.ne'] at hmul
  have heq : (1 + u / (n : ℝ))⁻¹ * (1 + u / (n : ℝ)) ^ (n + 1) = (1 + u / (n : ℝ)) ^ n := by
    rw [pow_succ]
    field_simp
  linarith

private lemma one_add_div_pow_mono {m d : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d) {u : ℝ} (hu : 0 ≤ u) :
    (1 + u / m) ^ m ≤ (1 + u / d) ^ d := by
  induction d with
  | zero => omega
  | succ d ih =>
    rcases eq_or_lt_of_le hmd with rfl | hlt
    · exact le_rfl
    · have hle : m ≤ d := Nat.lt_succ_iff.mp hlt
      exact (ih hle).trans (one_add_div_pow_step (hm.trans hle) hu)

theorem OMA.solution : OMA.R_Erdos499_vanDerWaerden_R1.H3 := by
  intro d m hd hmd a r L D ha hr hL hD
  have hD_eq : D = a * ∑ i : Fin m, ∏ j ∈ Finset.univ.erase i, r j :=
    hD.unique ((hasDerivAt_finset_prod_add Finset.univ r).const_mul a)
  have hD_nonneg : 0 ≤ D := by
    rw [hD_eq]
    exact mul_nonneg ha (Finset.sum_nonneg fun i _ => Finset.prod_nonneg fun j _ => hr j)
  set c : ℝ := (((d : ℝ) - 1) / d) ^ (d - 1)
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
  have hd_ge_one : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hc_nonneg : 0 ≤ c := pow_nonneg (div_nonneg (by linarith) hd_pos.le) _
  have hc_le_one : c ≤ 1 :=
    pow_le_one₀ (div_nonneg (by linarith) hd_pos.le)
      (div_le_one_of_le₀ (by linarith) hd_pos.le)
  have h_of_L_le_D : L ≤ D → c * L ≤ D := by
    intro hLD
    rcases le_or_gt L 0 with hL0 | hL0
    · exact (mul_nonpos_of_nonneg_of_nonpos hc_nonneg hL0).trans hD_nonneg
    · exact (mul_le_of_le_one_left hL0.le hc_le_one).trans hLD
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp only [zero_mul] at hD_eq
    have hL1 : L * 1 ≤ 0 * ∏ i : Fin m, (1 + r i) := hL 1 zero_lt_one
    rw [mul_one, zero_mul] at hL1
    exact h_of_L_le_D (by linarith)
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · have hD0 : D = 0 := by simp [hD_eq]
    have hL0 : L ≤ 0 := by
      by_contra h
      push Not at h
      have ht : 0 < (a + 1) / L := div_pos (by linarith) h
      have hLt := hL ((a + 1) / L) ht
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at hLt
      rw [mul_div_cancel₀ _ h.ne'] at hLt
      linarith
    exact h_of_L_le_D (by linarith)
  by_cases hd1 : d = 1
  · subst hd1
    have hm1 : m = 1 := by omega
    subst hm1
    have hD_a : D = a := by
      rw [hD_eq]
      simp
    have hL_a : L ≤ a := by
      by_contra h
      push Not at h
      have ht : 0 < (a * r 0 + 1) / (L - a) :=
        div_pos (add_pos_of_nonneg_of_pos (mul_nonneg ha (hr 0)) zero_lt_one) (by linarith)
      have hLt := hL ((a * r 0 + 1) / (L - a)) ht
      simp only [Fin.prod_univ_one] at hLt
      have hsub : (L - a) * ((a * r 0 + 1) / (L - a)) ≤ a * r 0 := by linarith
      rw [mul_div_cancel₀ _ (by linarith)] at hsub
      linarith
    exact h_of_L_le_D (by linarith)
  have hd2 : 2 ≤ d := by omega
  by_cases hr0 : ∃ i : Fin m, r i = 0
  · obtain ⟨i₀, hi₀⟩ := hr0
    have hD_i0 : D = a * ∏ j ∈ Finset.univ.erase i₀, r j := by
      rw [hD_eq]
      congr 1
      refine Finset.sum_eq_single i₀ ?_ (fun h => absurd (Finset.mem_univ i₀) h)
      intro i _ hne
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩) hi₀
    have hL_bound : ∀ t : ℝ, 0 < t → L ≤ a * ∏ j ∈ Finset.univ.erase i₀, (t + r j) := by
      intro t ht
      have hLt := hL t ht
      rw [← Finset.mul_prod_erase Finset.univ (fun i => t + r i) (Finset.mem_univ i₀),
        hi₀, add_zero] at hLt
      have hLt' : L * t ≤ (a * ∏ j ∈ Finset.univ.erase i₀, (t + r j)) * t := by
        linarith
      exact le_of_mul_le_mul_right hLt' ht
    have hcont : Continuous (fun t : ℝ => a * ∏ j ∈ Finset.univ.erase i₀, (t + r j)) :=
      continuous_const.mul (continuous_finsetProd _ fun j _ => continuous_id.add continuous_const)
    have htend : Filter.Tendsto (fun t : ℝ => a * ∏ j ∈ Finset.univ.erase i₀, (t + r j))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds D) := by
      have hg0 : a * ∏ j ∈ Finset.univ.erase i₀, ((0 : ℝ) + r j) = D := by
        simp [hD_i0]
      rw [← hg0]
      exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
        L ≤ a * ∏ j ∈ Finset.univ.erase i₀, (t + r j) :=
      eventually_mem_nhdsWithin.mono fun t ht => hL_bound t ht
    exact h_of_L_le_D (ge_of_tendsto htend hev)
  push Not at hr0
  have hr_pos : ∀ i : Fin m, 0 < r i := fun i => lt_of_le_of_ne (hr i) (Ne.symm (hr0 i))
  set p₀ : ℝ := a * ∏ i : Fin m, r i
  have hp₀_pos : 0 < p₀ := mul_pos ha_pos (Finset.prod_pos fun i _ => hr_pos i)
  have hD_prod : D = p₀ * ∑ i : Fin m, (r i)⁻¹ := by
    rw [hD_eq, Finset.mul_sum]
    dsimp [p₀]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hri := Finset.mul_prod_erase Finset.univ r (Finset.mem_univ i)
    have hri_ne : r i ≠ 0 := (hr_pos i).ne'
    calc a * ∏ j ∈ Finset.univ.erase i, r j
        = a * (r i * ∏ j ∈ Finset.univ.erase i, r j) * (r i)⁻¹ := by
          field_simp
      _ = a * (∏ j : Fin m, r j) * (r i)⁻¹ := by rw [hri]
  have hsum_inv_pos : 0 < ∑ i : Fin m, (r i)⁻¹ :=
    Finset.sum_pos (fun i _ => inv_pos.mpr (hr_pos i)) ⟨⟨0, hm_pos⟩, Finset.mem_univ _⟩
  have hD_pos : 0 < D := by rw [hD_prod]; exact mul_pos hp₀_pos hsum_inv_pos
  have hd_sub_pos : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    linarith
  set u : ℝ := (d : ℝ) / ((d : ℝ) - 1)
  have hu_pos : 0 < u := div_pos hd_pos hd_sub_pos
  set t : ℝ := u * p₀ / D
  have ht_pos : 0 < t := div_pos (mul_pos hu_pos hp₀_pos) hD_pos
  have hsum_t : ∑ i : Fin m, t / r i = u := by
    simp_rw [div_eq_mul_inv, ← Finset.mul_sum]
    have hinv : ∑ i : Fin m, (r i)⁻¹ = D / p₀ := by
      rw [hD_prod, mul_div_cancel_left₀ _ hp₀_pos.ne']
    rw [hinv]
    dsimp [t]
    field_simp
  have hp_eq : a * ∏ i : Fin m, (t + r i) = p₀ * ∏ i : Fin m, (1 + t / r i) := by
    dsimp [p₀]
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have hri_ne : r i ≠ 0 := (hr_pos i).ne'
    field_simp
    ring
  have hgm : ∏ i : Fin m, (1 + t / r i) ≤ (1 + u / m) ^ m := by
    have hw_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin m)), (0 : ℝ) ≤ (m : ℝ)⁻¹ :=
      fun _ _ => by positivity
    have hw_sum : ∑ i ∈ (Finset.univ : Finset (Fin m)), (m : ℝ)⁻¹ = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_inv_cancel₀ (by exact_mod_cast hm_pos.ne')
    have hz_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ 1 + t / r i :=
      fun i _ => add_nonneg zero_le_one (div_nonneg ht_pos.le (hr_pos i).le)
    have hle := Real.geom_mean_le_arith_mean_weighted
      Finset.univ (fun _ => (m : ℝ)⁻¹) (fun i => 1 + t / r i) hw_nonneg hw_sum hz_nonneg
    have hrhs : ∑ i : Fin m, (m : ℝ)⁻¹ * (1 + t / r i) = 1 + u / m := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, hsum_t]
      have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast hm_pos.ne'
      field_simp
    rw [hrhs] at hle
    have hpow := pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hz_nonneg i (Finset.mem_univ i)) _) hle m
    have hlhs : (∏ i : Fin m, (1 + t / r i) ^ (m : ℝ)⁻¹) ^ m = ∏ i : Fin m, (1 + t / r i) := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hpos : 0 ≤ 1 + t / r i := hz_nonneg i (Finset.mem_univ i)
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos, inv_mul_cancel₀ (by exact_mod_cast hm_pos.ne'), Real.rpow_one]
    rwa [hlhs] at hpow
  have hmono : (1 + u / m) ^ m ≤ (1 + u / d) ^ d :=
    one_add_div_pow_mono hm_pos hmd hu_pos.le
  have h1ud : 1 + u / d = u := by
    dsimp [u]
    field_simp
    ring
  have hLt : L * t ≤ p₀ * u ^ d := by
    calc L * t ≤ a * ∏ i : Fin m, (t + r i) := hL t ht_pos
      _ = p₀ * ∏ i : Fin m, (1 + t / r i) := hp_eq
      _ ≤ p₀ * (1 + u / m) ^ m := mul_le_mul_of_nonneg_left hgm hp₀_pos.le
      _ ≤ p₀ * (1 + u / d) ^ d := mul_le_mul_of_nonneg_left hmono hp₀_pos.le
      _ = p₀ * u ^ d := by rw [h1ud]
  have hcu : c * u ^ (d - 1) = 1 := by
    dsimp [c]
    rw [← mul_pow]
    have h1 : (((d : ℝ) - 1) / d) * u = 1 := by
      dsimp [u]
      field_simp
    rw [h1, one_pow]
  have hct_nonneg : 0 ≤ c / t := div_nonneg hc_nonneg ht_pos.le
  calc c * L = (L * t) * (c / t) := by
        have ht_ne : t ≠ 0 := ht_pos.ne'
        field_simp
    _ ≤ (p₀ * u ^ d) * (c / t) := mul_le_mul_of_nonneg_right hLt hct_nonneg
    _ = D := by
        have hd_split : d = (d - 1) + 1 := by omega
        conv_lhs => rw [hd_split, pow_succ]
        have h_alg : p₀ * (u ^ (d - 1) * u) * (c / t) = (c * u ^ (d - 1)) * (p₀ * u / t) := by ring
        rw [h_alg, hcu, one_mul]
        dsimp [t]
        field_simp
