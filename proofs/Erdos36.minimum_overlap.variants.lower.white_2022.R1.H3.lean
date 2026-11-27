import OMAReductions.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1

-- Step Erdos36.minimum_overlap.variants.lower.white_2022.R1.H3
-- Credit: @caa1982

open Filter MeasureTheory Finset

private def cell (n : ℕ) (k : ℤ) : Set ℝ :=
  Set.Ioc (-1 + ((k : ℝ) - 1) / (n : ℝ)) (-1 + (k : ℝ) / (n : ℝ))

private lemma cell_disjoint {n : ℕ} (hn : 0 < n) {j k : ℤ} (hjk : j ≠ k) :
    Disjoint (cell n j) (cell n k) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Set.disjoint_left]
  intro t ht1 ht2
  simp only [cell, Set.mem_Ioc] at ht1 ht2
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · have hle : (j : ℝ) ≤ (k : ℝ) - 1 := by exact_mod_cast (show j ≤ k - 1 by omega)
    have hdiv : (j : ℝ) / (n : ℝ) ≤ ((k : ℝ) - 1) / (n : ℝ) := div_le_div_of_nonneg_right hle hnR.le
    linarith
  · have hle : (k : ℝ) ≤ (j : ℝ) - 1 := by exact_mod_cast (show k ≤ j - 1 by omega)
    have hdiv : (k : ℝ) / (n : ℝ) ≤ ((j : ℝ) - 1) / (n : ℝ) := div_le_div_of_nonneg_right hle hnR.le
    linarith

private lemma cell_subset_Ioc {n : ℕ} (hn : 0 < n) {k : ℤ} (hk : k ∈ Finset.Icc (1 : ℤ) (2 * n)) :
    cell n k ⊆ Set.Ioc (-1 : ℝ) 1 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  simp only [Finset.mem_Icc] at hk
  intro t ht
  simp only [cell, Set.mem_Ioc] at ht ⊢
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
  have hk2 : (k : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hk.2
  have h0 : 0 ≤ ((k : ℝ) - 1) / (n : ℝ) := div_nonneg (by linarith) hnR.le
  have h2 : (k : ℝ) / (n : ℝ) ≤ 2 := (div_le_iff₀ hnR).mpr (by linarith)
  constructor <;> linarith

private lemma exists_cell_of_mem_Ioc {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : y ∈ Set.Ioc (-1 : ℝ) 1) :
    ∃ k ∈ Finset.Icc (1 : ℤ) (2 * n), y ∈ cell n k := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  simp only [Set.mem_Ioc] at hy
  let k : ℤ := ⌈(y + 1) * (n : ℝ)⌉
  have h1 : (y + 1) * (n : ℝ) ≤ (k : ℝ) := Int.le_ceil _
  have h2 : (k : ℝ) - 1 < (y + 1) * (n : ℝ) := by
    have := Int.ceil_lt_add_one ((y + 1) * (n : ℝ))
    linarith
  have hk1 : (1 : ℤ) ≤ k := by
    have hpos : (0 : ℝ) < (y + 1) * (n : ℝ) := mul_pos (by linarith) hnR
    have : (0 : ℤ) < k := Int.ceil_pos.mpr hpos
    omega
  have hk2 : k ≤ 2 * (n : ℤ) := by
    have hle : (y + 1) * (n : ℝ) ≤ ((2 * (n : ℤ) : ℤ) : ℝ) := by
      push_cast
      nlinarith
    exact Int.ceil_le.mpr hle
  refine ⟨k, Finset.mem_Icc.mpr ⟨hk1, hk2⟩, ?_⟩
  simp only [cell, Set.mem_Ioc]
  constructor
  · have : ((k : ℝ) - 1) / (n : ℝ) < y + 1 := (div_lt_iff₀ hnR).mpr h2
    linarith
  · have : y + 1 ≤ (k : ℝ) / (n : ℝ) := (le_div_iff₀ hnR).mpr h1
    linarith

private lemma intervalIntegral_cell_indicator {n : ℕ} (hn : 0 < n) {k : ℤ}
    (hk : k ∈ Finset.Icc (1 : ℤ) (2 * n)) :
    (∫ t in (-1 : ℝ)..1, (cell n k).indicator (fun _ => (1 : ℝ)) t) = 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsub_ioc : cell n k ⊆ Set.Ioc (-1 : ℝ) 1 := cell_subset_Ioc hn hk
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  unfold cell at hsub_ioc ⊢
  rw [MeasureTheory.integral_indicator measurableSet_Ioc, MeasureTheory.setIntegral_const,
    smul_eq_mul, mul_one, Measure.real_def, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left hsub_ioc, Real.volume_Ioc]
  have hsub : (-1 + (k : ℝ) / (n : ℝ)) - (-1 + ((k : ℝ) - 1) / (n : ℝ)) = 1 / (n : ℝ) := by
    field_simp
    ring
  rw [hsub, ENNReal.toReal_ofReal (by positivity)]

private lemma overlap_cell_integral_le {n : ℕ} (hn : 0 < n) (a b : ℤ) (x : ℝ) :
    (∫ t in (-1 : ℝ)..1,
      (cell n a).indicator (fun _ => (1 : ℝ)) t *
        (cell n b).indicator (fun _ => (1 : ℝ)) (x + t)) ≤
    max (0 : ℝ) (1 - |((b - a : ℤ) : ℝ) - (n : ℝ) * x|) / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  let l₁ : ℝ := -1 + ((a : ℝ) - 1) / (n : ℝ)
  let r₁ : ℝ := -1 + (a : ℝ) / (n : ℝ)
  let l₂ : ℝ := -1 + ((b : ℝ) - 1) / (n : ℝ) - x
  let r₂ : ℝ := -1 + (b : ℝ) / (n : ℝ) - x
  have hfun : (fun t : ℝ =>
      (cell n a).indicator (fun _ => (1 : ℝ)) t *
        (cell n b).indicator (fun _ => (1 : ℝ)) (x + t)) =
      (Set.Ioc (max l₁ l₂) (min r₁ r₂)).indicator (fun _ => (1 : ℝ)) := by
    ext t
    by_cases h1 : t ∈ cell n a <;> by_cases h2 : x + t ∈ cell n b
    · have hmem : t ∈ Set.Ioc (max l₁ l₂) (min r₁ r₂) := by
        simp only [cell, Set.mem_Ioc] at h1 h2
        simp only [Set.mem_Ioc, max_lt_iff, le_min_iff, l₁, r₁, l₂, r₂]
        exact ⟨⟨h1.1, by linarith⟩, ⟨h1.2, by linarith⟩⟩
      simp [h1, h2, hmem]
    · have hnot : t ∉ Set.Ioc (max l₁ l₂) (min r₁ r₂) := by
        intro hmem
        simp only [Set.mem_Ioc, max_lt_iff, le_min_iff, l₁, r₁, l₂, r₂] at hmem
        exact h2 ⟨by linarith, by linarith⟩
      simp [h1, h2, hnot]
    · have hnot : t ∉ Set.Ioc (max l₁ l₂) (min r₁ r₂) := by
        intro hmem
        simp only [Set.mem_Ioc, max_lt_iff, le_min_iff, l₁, r₁, l₂, r₂] at hmem
        exact h1 ⟨hmem.1.1, hmem.2.1⟩
      simp [h1, h2, hnot]
    · have hnot : t ∉ Set.Ioc (max l₁ l₂) (min r₁ r₂) := by
        intro hmem
        simp only [Set.mem_Ioc, max_lt_iff, le_min_iff, l₁, r₁, l₂, r₂] at hmem
        exact h1 ⟨hmem.1.1, hmem.2.1⟩
      simp [h1, h2, hnot]
  rw [hfun, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hint : Integrable ((Set.Ioc (max l₁ l₂) (min r₁ r₂)).indicator (fun _ => (1 : ℝ))) volume := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hle_full : (∫ t in Set.Ioc (-1 : ℝ) 1,
        (Set.Ioc (max l₁ l₂) (min r₁ r₂)).indicator (fun _ => (1 : ℝ)) t) ≤
      ∫ t : ℝ, (Set.Ioc (max l₁ l₂) (min r₁ r₂)).indicator (fun _ => (1 : ℝ)) t :=
    MeasureTheory.setIntegral_le_integral hint
      (Filter.Eventually.of_forall fun t => Set.indicator_nonneg (fun _ _ => zero_le_one) t)
  refine hle_full.trans ?_
  rw [MeasureTheory.integral_indicator measurableSet_Ioc, MeasureTheory.setIntegral_const,
    smul_eq_mul, mul_one, Measure.real_def, Real.volume_Ioc]
  by_cases hord : max l₁ l₂ ≤ min r₁ r₂
  · rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hord)]
    have hdiff : min r₁ r₂ - max l₁ l₂ =
        (1 - |((b - a : ℤ) : ℝ) - (n : ℝ) * x|) / (n : ℝ) := by
      have hlen1 : r₁ - l₁ = 1 / (n : ℝ) := by
        dsimp only [r₁, l₁]; field_simp; ring
      have hlen2 : r₂ - l₂ = 1 / (n : ℝ) := by
        dsimp only [r₂, l₂]; field_simp; ring
      have hshift : l₂ - l₁ = (((b - a : ℤ) : ℝ) - (n : ℝ) * x) / (n : ℝ) := by
        dsimp only [l₁, l₂]; push_cast; field_simp; ring
      have hshift_r : r₂ - r₁ = (((b - a : ℤ) : ℝ) - (n : ℝ) * x) / (n : ℝ) := by
        dsimp only [r₁, r₂]; push_cast; field_simp; ring
      rcases le_total (((b - a : ℤ) : ℝ) - (n : ℝ) * x) 0 with hle | hge
      · have hs : l₂ ≤ l₁ := by
          have : l₂ - l₁ ≤ 0 := by rw [hshift]; exact div_nonpos_of_nonpos_of_nonneg hle hnR.le
          linarith
        have hsr : r₂ ≤ r₁ := by
          have : r₂ - r₁ ≤ 0 := by rw [hshift_r]; exact div_nonpos_of_nonpos_of_nonneg hle hnR.le
          linarith
        rw [min_eq_right hsr, max_eq_left hs, abs_of_nonpos hle]
        have : r₂ - l₁ = (r₁ - l₁) + (r₂ - r₁) := by ring
        rw [this, hlen1, hshift_r]
        field_simp
        ring
      · have hs : l₁ ≤ l₂ := by
          have : 0 ≤ l₂ - l₁ := by rw [hshift]; exact div_nonneg hge hnR.le
          linarith
        have hsr : r₁ ≤ r₂ := by
          have : 0 ≤ r₂ - r₁ := by rw [hshift_r]; exact div_nonneg hge hnR.le
          linarith
        rw [min_eq_left hsr, max_eq_right hs, abs_of_nonneg hge]
        have : r₁ - l₂ = (r₁ - l₁) - (l₂ - l₁) := by ring
        rw [this, hlen1, hshift]
        field_simp
    rw [hdiff]
    exact div_le_div_of_nonneg_right (le_max_right _ _) hnR.le
  · push Not at hord
    have hzero : ENNReal.ofReal (min r₁ r₂ - max l₁ l₂) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (by linarith)
    rw [hzero, ENNReal.toReal_zero]
    exact div_nonneg (le_max_left _ _) hnR.le

theorem OMA.solution : OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1.H3 := by
  intro n hn A B hdisj hunion hcard
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hAcard : A.card = n :=
    OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1.card_left hdisj hunion hcard
  have hAsub : ∀ a ∈ A, a ∈ Finset.Icc (1 : ℤ) (2 * n) := by
    intro a ha; rw [← hunion]; exact Finset.mem_union_left B ha
  have hBsub : ∀ b ∈ B, b ∈ Finset.Icc (1 : ℤ) (2 * n) := by
    intro b hb; rw [← hunion]; exact Finset.mem_union_right A hb
  let f : ℝ → ℝ := fun t => ∑ a ∈ A, (cell n a).indicator (fun _ => (1 : ℝ)) t
  have hfm : Measurable f := by
    refine Finset.measurable_sum A fun a _ => ?_
    exact measurable_const.indicator measurableSet_Ioc
  have hf_val : ∀ t : ℝ, (∃ a ∈ A, t ∈ cell n a) → f t = 1 := by
    rintro t ⟨a, ha, hta⟩
    dsimp only [f]
    rw [Finset.sum_eq_single a]
    · simp [hta]
    · intro a' _ hne
      have hnot : t ∉ cell n a' := fun hta' => Set.disjoint_left.mp (cell_disjoint hn hne) hta' hta
      simp [hnot]
    · intro hnot; exact (hnot ha).elim
  have hf_zero : ∀ t : ℝ, (∀ a ∈ A, t ∉ cell n a) → f t = 0 := by
    intro t ht
    dsimp only [f]
    exact Finset.sum_eq_zero fun a ha => Set.indicator_of_notMem (ht a ha) _
  have hf01 : ∀ t : ℝ, 0 ≤ f t ∧ f t ≤ 1 := by
    intro t
    by_cases h : ∃ a ∈ A, t ∈ cell n a
    · rw [hf_val t h]; exact ⟨zero_le_one, le_rfl⟩
    · push Not at h; rw [hf_zero t h]; exact ⟨le_rfl, zero_le_one⟩
  have hfint : (∫ t in (-1 : ℝ)..1, f t) = 1 := by
    dsimp only [f]
    rw [intervalIntegral.integral_finset_sum]
    · have hterm : ∀ a ∈ A, (∫ t in (-1 : ℝ)..1, (cell n a).indicator (fun _ => (1 : ℝ)) t) = 1 / (n : ℝ) :=
        fun a ha => intervalIntegral_cell_indicator hn (hAsub a ha)
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, hAcard, nsmul_eq_mul]
      field_simp
    · intro a _
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr ?_
      refine IntegrableOn.of_bound measure_Ioc_lt_top
        (measurable_const.indicator measurableSet_Ioc).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun t => ?_)
      by_cases h : t ∈ cell n a <;> simp [h]
  refine ⟨f, hfm, hf01, hfint, fun x => ?_⟩
  let g : ℝ → ℝ := fun t => ∑ p ∈ A ×ˢ B,
    (cell n p.1).indicator (fun _ => (1 : ℝ)) t *
      (cell n p.2).indicator (fun _ => (1 : ℝ)) (x + t)
  have hae : (fun t => f t * (Set.Icc (-1 : ℝ) 1).indicator (fun y => 1 - f y) (x + t)) =ᵐ[volume.restrict (Set.Ioc (-1 : ℝ) 1)] g := by
    have hnull : ({-1 - x} : Set ℝ)ᶜ ∈ ae (volume.restrict (Set.Ioc (-1 : ℝ) 1)) := by
      rw [mem_ae_iff, compl_compl, Measure.restrict_apply (measurableSet_singleton _)]
      exact measure_mono_null Set.inter_subset_left (measure_singleton _)
    filter_upwards [hnull] with t ht
    have hne : x + t ≠ -1 := by
      intro heq
      apply ht
      simp only [Set.mem_singleton_iff]
      linarith
    have hBval : (Set.Icc (-1 : ℝ) 1).indicator (fun y => 1 - f y) (x + t) =
        ∑ b ∈ B, (cell n b).indicator (fun _ => (1 : ℝ)) (x + t) := by
      by_cases hy : x + t ∈ Set.Icc (-1 : ℝ) 1
      · rw [Set.indicator_of_mem hy]
        have hy_ioc : x + t ∈ Set.Ioc (-1 : ℝ) 1 := by
          simp only [Set.mem_Icc, Set.mem_Ioc] at hy ⊢
          exact ⟨lt_of_le_of_ne hy.1 hne.symm, hy.2⟩
        obtain ⟨k, hk, htk⟩ := exists_cell_of_mem_Ioc hn hy_ioc
        rw [← hunion, Finset.mem_union] at hk
        rcases hk with hkA | hkB
        · rw [hf_val (x + t) ⟨k, hkA, htk⟩, sub_self]
          symm
          apply Finset.sum_eq_zero
          intro b hb
          have hne_kb : b ≠ k := fun h => Finset.disjoint_left.mp hdisj hkA (h ▸ hb)
          have hnot : x + t ∉ cell n b := fun htb => Set.disjoint_left.mp (cell_disjoint hn hne_kb) htb htk
          simp [hnot]
        · have hnotA : ∀ a ∈ A, x + t ∉ cell n a := by
            intro a ha hta
            have hne_ak : a ≠ k := fun h => Finset.disjoint_left.mp hdisj ha (h ▸ hkB)
            exact Set.disjoint_left.mp (cell_disjoint hn hne_ak) hta htk
          rw [hf_zero (x + t) hnotA, sub_zero]
          symm
          rw [Finset.sum_eq_single k]
          · simp [htk]
          · intro b _ hne_bk
            have hnot : x + t ∉ cell n b := fun htb => Set.disjoint_left.mp (cell_disjoint hn hne_bk) htb htk
            simp [hnot]
          · intro hnot; exact (hnot hkB).elim
      · rw [Set.indicator_of_notMem hy]
        symm
        apply Finset.sum_eq_zero
        intro b hb
        have hnot : x + t ∉ cell n b := fun htb => hy (Set.Ioc_subset_Icc_self (cell_subset_Ioc hn (hBsub b hb) htb))
        simp [hnot]
    rw [hBval]
    dsimp only [f, g]
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have heq_int : (∫ t in (-1 : ℝ)..1, f t * (Set.Icc (-1 : ℝ) 1).indicator (fun y => 1 - f y) (x + t)) =
      ∫ t in (-1 : ℝ)..1, g t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact integral_congr_ae hae
  rw [heq_int]
  dsimp only [g]
  rw [intervalIntegral.integral_finset_sum]
  · calc ∑ p ∈ A ×ˢ B,
          (∫ t in (-1 : ℝ)..1,
            (cell n p.1).indicator (fun _ => (1 : ℝ)) t *
              (cell n p.2).indicator (fun _ => (1 : ℝ)) (x + t))
        ≤ ∑ p ∈ A ×ˢ B, max (0 : ℝ) (1 - |((p.2 - p.1 : ℤ) : ℝ) - (n : ℝ) * x|) / (n : ℝ) :=
          Finset.sum_le_sum fun p _ => overlap_cell_integral_le hn p.1 p.2 x
      _ = (∑ p ∈ A ×ˢ B, max (0 : ℝ) (1 - |((p.2 - p.1 : ℤ) : ℝ) - (n : ℝ) * x|)) / (n : ℝ) := by
          rw [Finset.sum_div]
  · intro p _
    have hm1 : Measurable ((cell n p.1).indicator (fun _ => (1 : ℝ))) :=
      measurable_const.indicator measurableSet_Ioc
    have hm2 : Measurable (fun t : ℝ => (cell n p.2).indicator (fun _ => (1 : ℝ)) (x + t)) :=
      (measurable_const.indicator measurableSet_Ioc).comp (measurable_const.add measurable_id)
    have hbdd : ∀ t : ℝ, ‖(cell n p.1).indicator (fun _ => (1 : ℝ)) t *
        (cell n p.2).indicator (fun _ => (1 : ℝ)) (x + t)‖ ≤ 1 := by
      intro t
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |(cell n p.1).indicator (fun _ => (1 : ℝ)) t| ≤ 1 := by
        by_cases h : t ∈ cell n p.1 <;> simp [h]
      have h2 : |(cell n p.2).indicator (fun _ => (1 : ℝ)) (x + t)| ≤ 1 := by
        by_cases h : x + t ∈ cell n p.2 <;> simp [h]
      nlinarith [abs_nonneg ((cell n p.1).indicator (fun _ => (1 : ℝ)) t),
        abs_nonneg ((cell n p.2).indicator (fun _ => (1 : ℝ)) (x + t))]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      (IntegrableOn.of_bound measure_Ioc_lt_top (hm1.mul hm2).aestronglyMeasurable 1
        (Filter.Eventually.of_forall hbdd))
