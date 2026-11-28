import OMAStatements.S_mo_487278

open MeasureTheory Set Filter OMA.S_mo_487278
open scoped ENNReal Topology

private theorem gap_pos (n : ℕ) : 0 < gap n := by
  unfold gap
  positivity

private theorem gap_le (n : ℕ) : gap n ≤ 1 / 2 := by
  rw [gap, pow_succ]
  have h : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

private theorem low_mem (n : ℕ) : low n ∈ I := by
  have := gap_le n
  have := gap_pos n
  simp only [low, mem_Icc]
  constructor <;> linarith

private theorem low_pos {n : ℕ} (hn : 0 < n) : 0 < low n := by
  unfold low gap
  have h : (1 / 2 : ℝ) ^ n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hn.ne'
  rw [pow_succ]
  linarith

private theorem high_mem (n : ℕ) : high n ∈ I := by
  have := gap_le n
  have := gap_pos n
  simp only [high, mem_Icc]
  constructor <;> linarith

private theorem high_pos (n : ℕ) : 0 < high n := by
  have := gap_pos n
  unfold high
  linarith

private theorem weight_pos (n : ℕ) : 0 < weight n := by
  simpa [weight, ENNReal.ofReal_pos] using div_pos (gap_pos n) (by norm_num : (0 : ℝ) < 2)

private theorem volume_I : volume I = 1 := by simp [I, Real.volume_Icc]

private theorem scaleBranch (A : Set ℝ) {c : ℝ} (hc : 0 < c) :
    oneBranch A c = ENNReal.ofReal c⁻¹ * volume (A ∩ Icc 0 c) := by
  have heq : {t | t ∈ I ∧ c * t ∈ A} =
      (fun t => c * t) ⁻¹' (A ∩ Icc 0 c) := by
    ext t
    have hbound : c * t ≤ c ↔ t ≤ 1 := by
      simpa only [mul_one] using (mul_le_mul_iff_right₀ hc : c * t ≤ c * 1 ↔ t ≤ 1)
    simp only [mem_ofPred_eq, mem_preimage, mem_inter_iff, mem_Icc, I]
    rw [mul_nonneg_iff_of_pos_left hc, hbound]
    tauto
  rw [oneBranch, heq, Real.volume_preimage_mul_left hc.ne',
    abs_of_pos (inv_pos.mpr hc)]

open Classical in
private theorem zeroBranch (A : Set ℝ) :
    oneBranch A 0 = if 0 ∈ A then 1 else 0 := by
  classical
  by_cases h : 0 ∈ A
  · rw [if_pos h, oneBranch]
    simpa only [zero_mul, h, and_true, ofPred_mem_eq] using volume_I
  · simp [oneBranch, h]

private theorem reflect_measurable {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet (reflect A) := (measurable_const.sub measurable_id) hA

private theorem reflect_volume {A : Set ℝ} (hA : MeasurableSet A) :
    volume (reflect A) = volume A := by
  exact (volume.measurePreserving_sub_left 1).measure_preimage hA.nullMeasurableSet

private theorem reflect_icc (a b : ℝ) : reflect (Icc a b) = Icc (1 - b) (1 - a) := by
  ext x
  simp [reflect]

private theorem reflect_inter (A B : Set ℝ) :
    reflect (A ∩ B) = reflect A ∩ reflect B := rfl

private theorem reflect_reflect (A : Set ℝ) : reflect (reflect A) = A := by
  ext x
  simp [reflect]

private theorem reflect_full {A : Set ℝ} (hA : MeasurableSet A) :
    volume (reflect A ∩ I) = volume (A ∩ I) := by
  have hI : reflect I = I := by norm_num [I, reflect_icc]
  calc
    _ = volume (reflect (A ∩ I)) := by rw [reflect_inter, hI]
    _ = _ := reflect_volume (hA.inter measurableSet_Icc)

private theorem reflect_half {A : Set ℝ} (hA : MeasurableSet A) :
    volume (reflect A ∩ Icc 0 (1 / 2)) = volume (A ∩ Icc (1 / 2) 1) := by
  have hh : reflect (Icc (1/2 : ℝ) 1) = Icc 0 (1/2) := by norm_num [reflect_icc]
  rw [← hh, ← reflect_inter]
  exact reflect_volume (hA.inter measurableSet_Icc)

private theorem positive_half {A : Set ℝ} (hA : MeasurableSet A) (hp : 0 < volume (A ∩ I)) :
    0 < volume (A ∩ Icc 0 (1/2)) ∨ 0 < volume (reflect A ∩ Icc 0 (1/2)) := by
  rw [reflect_half hA]
  have heq : A ∩ I = (A ∩ Icc 0 (1/2)) ∪ (A ∩ Icc (1/2) 1) := by
    ext x
    simp only [I, mem_inter_iff, mem_Icc, mem_union]
    constructor
    · rintro ⟨hx, ha, hb⟩
      rcases le_total x (1/2) with h | h
      · exact Or.inl ⟨hx, ha, h⟩
      · exact Or.inr ⟨hx, h, hb⟩
    · rintro (⟨hx, ha, hb⟩ | ⟨hx, ha, hb⟩) <;>
        exact ⟨hx, by linarith, by linarith⟩
  rw [heq] at hp
  by_contra! hn
  have hu := measure_union_le (μ := (volume : Measure ℝ))
    (A ∩ Icc 0 (1/2)) (A ∩ Icc (1/2) 1)
  rw [nonpos_iff_eq_zero.mp hn.1, nonpos_iff_eq_zero.mp hn.2, add_zero] at hu
  exact (not_lt_of_ge hu) hp

private theorem both_le_high (A : Set ℝ) (n : ℕ) :
    bothBranch A n ≤ oneBranch A (high n) := by
  exact measure_mono (fun _ h => ⟨h.1, h.2.2⟩)

private theorem branch_pos {A : Set ℝ} {c : ℝ} (hc : c ∈ I)
    (hp : 0 < oneBranch A c) : 0 < volume (A ∩ I) ∨ 0 ∈ A := by
  have hc' : 0 ≤ c := hc.1
  rcases eq_or_lt_of_le hc' with hzero | hpos
  · right
    by_contra h
    simp [← hzero, zeroBranch, h] at hp
  · left
    rw [scaleBranch A hpos] at hp
    have hm : 0 < volume (A ∩ Icc 0 c) := by
      contrapose! hp
      rw [nonpos_iff_eq_zero.mp hp, mul_zero]
    exact hm.trans_le (measure_mono (inter_subset_inter_right _ (Icc_subset_Icc_right hc.2)))

private theorem both_pos_implies {A : Set ℝ} {n : ℕ}
    (hp : 0 < bothBranch A n) : 0 < volume (A ∩ I) := by
  have hp' := hp.trans_le (both_le_high A n)
  rw [scaleBranch A (high_pos n)] at hp'
  have hm : 0 < volume (A ∩ Icc 0 (high n)) := by
    contrapose! hp'
    rw [nonpos_iff_eq_zero.mp hp', mul_zero]
  exact hm.trans_le (measure_mono (inter_subset_inter_right _
    (Icc_subset_Icc_right (high_mem n).2)))

private theorem eventually_both {A : Set ℝ} (hA : MeasurableSet A)
    (hpos : 0 < volume (A ∩ Icc 0 (1/2))) :
    ∀ᶠ n : ℕ in atTop, 0 < bothBranch A n := by
  have hfin : volume (A ∩ Icc 0 (1/2)) ≠ ∞ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono inter_subset_right)
  obtain ⟨K, hKA, hK, hKpos⟩ :=
    (hA.inter measurableSet_Icc).exists_lt_isCompact_of_ne_top hfin hpos
  have hKfin : volume K ≠ ∞ := hK.measure_lt_top.ne
  obtain ⟨U, hKU, hU, hUmass⟩ :=
    K.exists_isOpen_lt_of_lt (volume K + volume K) (ENNReal.lt_add_right hKfin hKpos.ne')
  obtain ⟨ε, hε, hδ⟩ := hK.exists_thickening_subset_open hU hKU
  let s (n : ℕ) := high n / low n
  have hg : Tendsto gap atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
    change Tendsto (fun n : ℕ => (1/2:ℝ) ^ (n+1)) atTop (𝓝 0)
    simpa only [pow_succ, zero_mul] using h.mul_const (1/2 : ℝ)
  have hs : Tendsto s atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1/2 : ℝ))).add hg
    have h' := (tendsto_const_nhds (x := (1/2 : ℝ))).sub hg
    have hdiv := h.div h' (by norm_num : (1/2 : ℝ) - 0 ≠ 0)
    change Tendsto s atTop (𝓝 (((1/2:ℝ) + 0) / ((1/2:ℝ) - 0))) at hdiv
    simpa using hdiv
  filter_upwards [eventually_gt_atTop (0 : ℕ), (Metric.tendsto_nhds.mp hs) ε hε] with n hn hd
  have hl := low_pos hn
  have hh := high_pos n
  have hsge : 1 ≤ s n := (le_div_iff₀ hl).2 (by
    have := gap_pos n
    unfold low high
    linarith)
  have hsp : 0 < s n := zero_lt_one.trans_le hsge
  let scaled := (fun y : ℝ => (s n)⁻¹ * y) ⁻¹' K
  have hscaledU : scaled ⊆ U := by
    intro y hy
    let x := (s n)⁻¹ * y
    have hx : x ∈ K := hy
    have hyx : y = s n * x := by
      dsimp [x]
      rw [← mul_assoc, mul_inv_cancel₀ hsp.ne', one_mul]
    apply hδ
    refine Metric.mem_thickening_iff.mpr ⟨x, hx, ?_⟩
    have hx1 : |x| ≤ 1 := abs_le.mpr ⟨by linarith [(hKA hx).2.1], by linarith [(hKA hx).2.2]⟩
    rw [hyx, Real.dist_eq, show s n * x - x = (s n - 1) * x by ring, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hx1).trans_lt (by simpa [Real.dist_eq] using hd)
  have hscaledVol : volume K ≤ volume scaled := by
    dsimp [scaled]
    rw [Real.volume_preimage_mul_left (inv_ne_zero hsp.ne'), inv_inv, abs_of_pos hsp]
    calc
      volume K = 1 * volume K := by simp
      _ ≤ ENNReal.ofReal (s n) * volume K := by
        gcongr
        simpa using ENNReal.ofReal_le_ofReal hsge
  have hi : 0 < volume (scaled ∩ K) := by
    by_contra! h
    have hu := measure_union_add_inter (μ := (volume : Measure ℝ)) scaled hK.measurableSet
    rw [nonpos_iff_eq_zero.mp h, add_zero] at hu
    have hle : volume K + volume K ≤ volume U :=
      (add_le_add hscaledVol le_rfl).trans_eq hu.symm |>.trans
        (measure_mono (union_subset hscaledU hKU))
    exact (not_lt_of_ge hle) hUmass
  have hp : 0 < volume ((fun t : ℝ => high n * t) ⁻¹' (scaled ∩ K)) := by
    rw [Real.volume_preimage_mul_left hh.ne']
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero hh.ne'))).ne' hi.ne'
  refine hp.trans_le (measure_mono ?_)
  intro t ht
  have htK : high n * t ∈ K := ht.2
  have htScaled : (s n)⁻¹ * (high n * t) ∈ K := ht.1
  have ho : (s n)⁻¹ * (high n * t) = low n * t := by
    dsimp [s]
    field_simp
  rw [ho] at htScaled
  refine ⟨⟨?_, ?_⟩, (hKA htScaled).1, (hKA htK).1⟩
  · exact (mul_nonneg_iff_of_pos_left hh).mp (hKA htK).2.1
  · apply (mul_le_mul_iff_right₀ hh).mp
    rw [mul_one]
    exact (hKA htK).2.2.trans (by unfold high; linarith [gap_pos n])

private theorem exists_positive (f : ℕ → ℝ≥0∞) (h : 0 < ∑' n, f n) :
    ∃ n, 0 < f n := by
  by_contra! hn
  have hz : (∑' n, f n) = 0 := ENNReal.tsum_eq_zero.mpr (fun n => nonpos_iff_eq_zero.mp (hn n))
  simp [hz] at h

private theorem both_eventually_iff {A : Set ℝ} (hA : MeasurableSet A) :
    0 < volume (A ∩ I) ↔ ∀ᶠ n in atTop, 0 < bothBranch A n + bothBranch (reflect A) n := by
  constructor
  · intro h
    rcases positive_half hA h with hp | hp
    · exact (eventually_both hA hp).mono fun n hn => hn.trans_le le_self_add
    · exact (eventually_both (reflect_measurable hA) hp).mono fun n hn => hn.trans_le le_add_self
  · intro h
    obtain ⟨n, hn⟩ := h.exists
    by_cases hnA : bothBranch A n = 0
    · have hp : 0 < bothBranch (reflect A) n := by
        rwa [hnA, zero_add] at hn
      simpa only [reflect_full hA] using both_pos_implies hp
    · exact both_pos_implies (pos_iff_ne_zero.mpr hnA)

private theorem certain_iff {A : Set ℝ} (hA : MeasurableSet A) :
    0 < certain A ↔ 0 < volume (A ∩ I) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_positive _ h
    have hp : 0 < bothBranch A n + bothBranch (reflect A) n := by
      by_contra! hz
      rw [nonpos_iff_eq_zero.mp hz, mul_zero] at hn
      exact (lt_irrefl _ hn)
    by_cases hnA : bothBranch A n = 0
    · rw [hnA, zero_add] at hp
      simpa only [reflect_full hA] using both_pos_implies hp
    · exact both_pos_implies (pos_iff_ne_zero.mpr hnA)
  · intro h
    obtain ⟨n, hn⟩ := ((both_eventually_iff hA).mp h).exists
    exact (ENNReal.mul_pos (weight_pos n).ne' hn.ne').trans_le (ENNReal.le_tsum n)

private theorem marginal_at (A : Set ℝ) (n : ℕ)
    (h : 0 < oneBranch A (low n) + oneBranch A (high n) +
      oneBranch (reflect A) (low n) + oneBranch (reflect A) (high n)) : 0 < marginal A := by
  have hw : weight n / 2 ≠ 0 := by
    exact (ENNReal.div_pos (weight_pos n).ne' (by simp)).ne'
  exact (ENNReal.mul_pos hw h.ne').trans_le (ENNReal.le_tsum n)

private theorem low_zero : low 0 = 0 := by norm_num [low, gap]
private theorem high_zero : high 0 = 1 := by norm_num [high, gap]

private theorem marginal_iff {A : Set ℝ} (hA : MeasurableSet A) :
    0 < marginal A ↔ 0 < volume (A ∩ I) ∨ 0 ∈ A ∨ 1 ∈ A := by
  constructor
  · intro h
    by_contra! hn
    have hz (c : ℝ) (hc : c ∈ I) : oneBranch A c = 0 := by
      by_contra hb
      rcases branch_pos hc (pos_iff_ne_zero.mpr hb) with hp | hp
      · exact (not_lt_of_ge hn.1) hp
      · exact hn.2.1 hp
    have hzr (c : ℝ) (hc : c ∈ I) : oneBranch (reflect A) c = 0 := by
      by_contra hb
      rcases branch_pos hc (pos_iff_ne_zero.mpr hb) with hp | hp
      · exact (not_lt_of_ge hn.1) (by simpa only [reflect_full hA] using hp)
      · exact hn.2.2 (by simpa [reflect] using hp)
    unfold marginal at h
    simp_rw [hz _ (low_mem _), hz _ (high_mem _), hzr _ (low_mem _), hzr _ (high_mem _),
      add_zero, mul_zero, tsum_zero] at h
    exact lt_irrefl _ h
  · rintro (hp | hp | hp)
    · obtain ⟨n, hn⟩ := ((both_eventually_iff hA).mp hp).exists
      apply marginal_at A n
      refine hn.trans_le ?_
      calc
        bothBranch A n + bothBranch (reflect A) n ≤
            oneBranch A (high n) + oneBranch (reflect A) (high n) :=
          add_le_add (both_le_high A n) (both_le_high (reflect A) n)
        _ ≤ _ := by
          exact add_le_add ((le_add_self.trans le_self_add)) le_rfl
    · apply marginal_at A 0
      have h : oneBranch A (low 0) = 1 := by rw [low_zero, zeroBranch, if_pos hp]
      rw [h]
      positivity
    · apply marginal_at A 0
      have h : oneBranch (reflect A) (low 0) = 1 := by
        rw [low_zero, zeroBranch, if_pos (show 0 ∈ reflect A by simpa [reflect] using hp)]
      rw [h]
      positivity

private theorem reflect_single (a : ℝ) : reflect ({a} : Set ℝ) = {1-a} := by
  ext x
  simp only [reflect, mem_preimage, mem_singleton_iff]
  constructor <;> intro h <;> linarith

private theorem positive_branch_single (a : ℝ) {c : ℝ} (hc : 0 < c) :
    oneBranch {a} c = 0 := by
  rw [scaleBranch _ hc, measure_inter_null_of_null_left _ (measure_singleton a), mul_zero]

private theorem certain_single (a : ℝ) : certain {a} = 0 := by
  unfold certain
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  have hb (x : ℝ) : bothBranch {x} n = 0 := by
    apply nonpos_iff_eq_zero.mp
    simpa only [positive_branch_single x (high_pos n)] using both_le_high ({x} : Set ℝ) n
  rw [reflect_single, hb, hb, add_zero, mul_zero]

private theorem marginal_reflection (A : Set ℝ) : marginal (reflect A) = marginal A := by
  unfold marginal
  simp only [reflect_reflect, add_assoc, add_left_comm, add_comm]

private theorem marginal_zero : marginal ({0} : Set ℝ) = 1/8 := by
  classical
  unfold marginal
  rw [tsum_eq_single 0]
  · rw [reflect_single, sub_zero, low_zero, high_zero, zeroBranch, zeroBranch,
      positive_branch_single _ zero_lt_one, positive_branch_single _ zero_lt_one]
    norm_num [weight, gap, ENNReal.ofReal_div_of_pos]
    rw [div_eq_mul_inv, ← ENNReal.mul_inv (by simp) (by simp)]
    norm_num
  · intro n hn
    rw [reflect_single, positive_branch_single _ (low_pos (Nat.pos_of_ne_zero hn)),
      positive_branch_single _ (low_pos (Nat.pos_of_ne_zero hn)),
      positive_branch_single _ (high_pos n), positive_branch_single _ (high_pos n)]
    simp

private theorem sum_gap : (∑' n, ENNReal.ofReal (gap n)) = 1 := by
  simp_rw [gap, ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2),
    ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_one]
  norm_num [one_div, ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two,
    ENNReal.inv_mul_cancel]

private theorem mass_one : certain univ = 1 ∧ marginal univ = 1 := by
  have hb (c : ℝ) : oneBranch univ c = 1 := by
    simp only [oneBranch, mem_univ, and_true, ofPred_mem_eq, volume_I]
  have hc (n : ℕ) : bothBranch univ n = 1 := by
    simp only [bothBranch, mem_univ, and_true, ofPred_mem_eq, volume_I]
  have ht (n : ℕ) : weight n * (1+1) = ENNReal.ofReal (gap n) := by
    rw [show (1 + 1 : ℝ≥0∞) = 2 by norm_num, ← ENNReal.ofReal_ofNat (n := 2)]
    rw [weight, ← ENNReal.ofReal_mul (div_pos (gap_pos n) (by norm_num : (0 : ℝ) < 2)).le]
    congr 1
    ring
  have ht' (n : ℕ) : weight n / 2 * (1+1+1+1) = ENNReal.ofReal (gap n) := by
    have htwo : (2 : ℝ≥0∞)⁻¹ * (1+1+1+1) = 1+1 := by
      rw [show (1 + 1 + 1 + 1 : ℝ≥0∞) = 2 * 2 by norm_num, ← mul_assoc,
        ENNReal.inv_mul_cancel (by norm_num) (by simp), one_mul]
      norm_num
    rw [div_eq_mul_inv, mul_assoc, htwo, ht]
  have hru : reflect univ = univ := preimage_univ
  constructor
  · simpa only [certain, hru, hc, ht] using sum_gap
  · simpa only [marginal, hru, hb, ht'] using sum_gap

theorem OMA.solution : type_of% @OMA.S_mo_487278.main := by
  refine ⟨mass_one, ⟨marginal_zero, ?_, certain_single 0, certain_single 1⟩, ?_⟩
  · rw [← marginal_zero, ← marginal_reflection ({0} : Set ℝ), reflect_single, sub_zero]
  · exact fun A hA => ⟨certain_iff hA, marginal_iff hA, both_eventually_iff hA⟩
