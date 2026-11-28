import OMAStatements.S_mo_364097

namespace OMA.S_mo_364097_aux

open Set MeasureTheory Metric Filter Topology

private abbrev E (n : ℕ) := OMA.S_mo_364097.E n

private noncomputable def vol {n : ℕ} (K : Set (E n)) : ℝ :=
  OMA.S_mo_364097.vol K

private lemma vol_eq {n : ℕ} (K : Set (E n)) : vol K = volume.real K := rfl

private lemma volume_hyperplane_zero (n : ℕ) (r : ℝ) :
    volume {x : E n | x 0 = r} = 0 := by
  let L : E n →ₗ[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin (n + 1))).toLinearMap
  let v₀ : E n := WithLp.toLp 2 (fun _ : Fin (n + 1) => (1 : ℝ))
  have hv₀ : L v₀ = 1 := rfl
  have hker : LinearMap.ker L ≠ ⊤ := by
    intro h
    have hmem : v₀ ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hv₀] at hmem
    exact one_ne_zero hmem
  have hsub : {x : E n | x 0 = r} =
      (fun x : E n => x + (- (r • v₀))) ⁻¹' (LinearMap.ker L : Set (E n)) := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, SetLike.mem_coe, LinearMap.mem_ker,
      map_add, map_neg, map_smul, smul_eq_mul, L]
    change x 0 = r ↔ x 0 + -(r * L v₀) = 0
    rw [hv₀, mul_one, ← sub_eq_add_neg, sub_eq_zero, eq_comm]
  rw [hsub, measure_preimage_add_right]
  exact Measure.addHaar_submodule volume (LinearMap.ker L) hker

private lemma volume_singleton_zero (n : ℕ) (x : E n) :
    volume ({x} : Set (E n)) = 0 := by
  have hsub : ({x} : Set (E n)) ⊆ {y : E n | y 0 = x 0} := by
    intro y hy
    rw [mem_singleton_iff] at hy
    simp [hy]
  exact measure_mono_null hsub (volume_hyperplane_zero n (x 0))

private lemma volume_finite_zero {n : ℕ} {F : Set (E n)} (hF : F.Finite) :
    volume F = 0 := by
  have hUnion : F = ⋃ x ∈ hF.toFinset, ({x} : Set (E n)) := by
    ext y
    simp
  rw [hUnion, ← le_zero_iff]
  refine (measure_biUnion_finset_le hF.toFinset (fun x => ({x} : Set (E n)))).trans_eq ?_
  simp

private lemma upper_semicont {n : ℕ} {K : Set (E n)} (hK : IsCompact K) (hKne : K.Nonempty) :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ H : Set (E n), IsCompact H → H.Nonempty →
      hausdorffDist K H < δ → vol H < vol K + ε := by
  intro ε hε
  let U : ℕ → Set (E n) := fun k => thickening (1 / (k + 1 : ℝ)) K
  have hU_meas : ∀ k, NullMeasurableSet (U k) volume :=
    fun k => (isOpen_thickening).measurableSet.nullMeasurableSet
  have hU_anti : Antitone U := by
    intro a b hab
    apply thickening_mono
    gcongr
  have hU_fin : ∃ k, volume (U k) ≠ ⊤ :=
    ⟨0, (hK.isBounded.thickening).measure_lt_top.ne⟩
  have hU_inter : (⋂ k : ℕ, U k) = K := by
    have hs₀ : range (fun k : ℕ => 1 / (k + 1 : ℝ)) ⊆ Ioi 0 := by
      rintro _ ⟨k, rfl⟩
      rw [mem_Ioi]
      positivity
    have hs : ∀ η : ℝ, 0 < η → (range (fun k : ℕ => 1 / (k + 1 : ℝ)) ∩ Ioc 0 η).Nonempty := by
      intro η hη
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
      exact ⟨1 / (k + 1 : ℝ), ⟨k, rfl⟩, ⟨by positivity, hk.le⟩⟩
    have hcl := closure_eq_iInter_thickening' K (range (fun k : ℕ => 1 / (k + 1 : ℝ))) hs₀ hs
    rw [hK.isClosed.closure_eq] at hcl
    rw [hcl]
    ext x
    simp [U]
  have htend : Tendsto (fun k => volume (U k)) atTop (𝓝 (volume K)) := by
    rw [← hU_inter]
    exact tendsto_measure_iInter_atTop hU_meas hU_anti hU_fin
  have htend_real : Tendsto (fun k => vol (U k)) atTop (𝓝 (vol K)) := by
    simpa only [vol_eq, Measure.real, Function.comp_def] using
      (ENNReal.tendsto_toReal hK.measure_lt_top.ne).comp htend
  have hevent : ∀ᶠ k in atTop, vol (U k) < vol K + ε :=
    htend_real (Iio_mem_nhds (lt_add_of_pos_right (vol K) hε))
  obtain ⟨k, hk⟩ := hevent.exists
  refine ⟨1 / (k + 1 : ℝ), by positivity, fun H hH hHne hdist => ?_⟩
  have hsub : H ⊆ U k := by
    intro x hx
    have hfin : hausdorffEDist K H ≠ ⊤ :=
      hausdorffEDist_ne_top_of_nonempty_of_bounded hKne hHne hK.isBounded hH.isBounded
    obtain ⟨y, hy, hxy⟩ := exists_dist_lt_of_hausdorffDist_lt' hx hdist hfin
    rw [mem_thickening_iff]
    exact ⟨y, hy, by simpa [dist_comm] using hxy⟩
  have hU_ne_top : volume (U k) ≠ ⊤ :=
    (hK.isBounded.thickening).measure_lt_top.ne
  exact (measureReal_mono hsub hU_ne_top).trans_lt hk

private lemma slice_continuous {n : ℕ} {K : Set (E n)} (hK : IsCompact K) :
    Continuous (fun r : ℝ => vol (K ∩ {x : E n | x 0 ≤ r})) := by
  let S : ℝ → Set (E n) := fun r => K ∩ {x : E n | x 0 ≤ r}
  have hS_compact : ∀ r, IsCompact (S r) := fun r =>
    hK.inter_right (isClosed_le (EuclideanSpace.proj (0 : Fin (n + 1))).continuous continuous_const)
  have hS_meas : ∀ r, NullMeasurableSet (S r) volume := fun r =>
    (hS_compact r).measurableSet.nullMeasurableSet
  have hS_mono : Monotone S := by
    intro a b hab x ⟨hxK, hxa⟩
    exact ⟨hxK, hxa.trans hab⟩
  rw [continuous_iff_continuousAt]
  intro r₀
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · have hUnion : (⋃ r : Iio r₀, S r) = K ∩ {x : E n | x 0 < r₀} := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, Subtype.exists, mem_Iio, S]
      constructor
      · rintro ⟨r, hr, hxK, hxr⟩
        exact ⟨hxK, hxr.trans_lt hr⟩
      · rintro ⟨hxK, hxr⟩
        exact ⟨(x 0 + r₀) / 2, by linarith, hxK, by linarith⟩
    have hVol_eq : volume (K ∩ {x : E n | x 0 < r₀}) = volume (S r₀) := by
      apply le_antisymm
      · exact measure_mono (fun x hx => ⟨hx.1, show x 0 ≤ r₀ from le_of_lt hx.2⟩)
      · have hsub : S r₀ ⊆ (K ∩ {x : E n | x 0 < r₀}) ∪ {x : E n | x 0 = r₀} := by
          rintro x ⟨hxK, hxr⟩
          rcases lt_or_eq_of_le (show x 0 ≤ r₀ from hxr) with hlt | heq
          · exact Or.inl ⟨hxK, hlt⟩
          · exact Or.inr heq
        exact (measure_mono hsub).trans ((measure_union_le _ _).trans_eq (by
          rw [volume_hyperplane_zero n r₀, add_zero]))
    have hfin : volume (S r₀) ≠ ⊤ := (hS_compact r₀).measure_lt_top.ne
    have : (atTop : Filter (Iio r₀)).IsCountablyGenerated := by
      rw [← comap_coe_Iio_nhdsLT r₀ (.of_dense _)]
      infer_instance
    have htend : Tendsto (fun r : Iio r₀ => volume (S r)) atTop (𝓝 (volume (S r₀))) := by
      rw [← hVol_eq, ← hUnion]
      exact tendsto_measure_iUnion_atTop (fun a b hab => hS_mono hab)
    have htend' : Tendsto (fun r => volume (S r)) (𝓝[<] r₀) (𝓝 (volume (S r₀))) := by
      rw [← map_coe_Iio_atTop r₀ (.of_dense _), tendsto_map'_iff]
      exact htend
    simpa only [ContinuousWithinAt, vol_eq, Measure.real, Function.comp_def, S] using
      (ENNReal.tendsto_toReal hfin).comp htend'
  · have hInter : (⋂ r > r₀, S r) = S r₀ := by
      ext x
      simp only [mem_iInter, mem_inter_iff, mem_ofPred_eq, S]
      constructor
      · intro h
        by_cases hxK : x ∈ K
        · refine ⟨hxK, le_of_forall_gt_imp_ge_of_dense fun r hr => (h r hr).2⟩
        · exact False.elim (hxK (h (r₀ + 1) (lt_add_one r₀)).1)
      · rintro ⟨hxK, hxr⟩ r hr
        exact ⟨hxK, hxr.trans hr.le⟩
    have htend : Tendsto (fun r => volume (S r)) (𝓝[>] r₀) (𝓝 (volume (S r₀))) := by
      rw [← hInter]
      exact tendsto_measure_biInter_gt (fun r _ => hS_meas r) (fun i j _ hij => hS_mono hij)
        ⟨r₀ + 1, lt_add_one r₀, (hS_compact (r₀ + 1)).measure_lt_top.ne⟩
    have hfin : volume (S r₀) ≠ ⊤ := (hS_compact r₀).measure_lt_top.ne
    simpa only [ContinuousWithinAt, vol_eq, Measure.real, Function.comp_def, S] using
      (ENNReal.tendsto_toReal hfin).comp htend

private lemma exists_subset_with_vol {n : ℕ} {K : Set (E n)} (hK : IsCompact K)
    {m : ℝ} (hm0 : 0 ≤ m) (hmK : m ≤ vol K) :
    ∃ K' : Set (E n), IsCompact K' ∧ K' ⊆ K ∧ vol K' = m := by
  obtain ⟨R, hRpos, hKR⟩ := hK.isBounded.subset_closedBall_lt (0 : ℝ) (0 : E n)
  let f : ℝ → ℝ := fun r => vol (K ∩ {x : E n | x 0 ≤ r})
  have hf_cont : Continuous f := slice_continuous hK
  have ha : f (-R - 1) = 0 := by
    have h_empty : K ∩ {x : E n | x 0 ≤ -R - 1} = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      intro hxK
      have hdist : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp (hKR hxK)
      have hcoord : ‖x 0‖ ≤ ‖x‖ := PiLp.norm_apply_le x 0
      rw [Real.norm_eq_abs] at hcoord
      linarith [(abs_le.mp (hcoord.trans hdist)).1]
    simp [f, h_empty, vol_eq]
  have hb : f (R + 1) = vol K := by
    have h_eq : K ∩ {x : E n | x 0 ≤ R + 1} = K := by
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
      intro hxK
      have hdist : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp (hKR hxK)
      have hcoord : ‖x 0‖ ≤ ‖x‖ := PiLp.norm_apply_le x 0
      rw [Real.norm_eq_abs] at hcoord
      linarith [(abs_le.mp (hcoord.trans hdist)).2]
    simp [f, h_eq]
  have hab : -R - 1 ≤ R + 1 := by linarith
  have hm_mem : m ∈ Icc (f (-R - 1)) (f (R + 1)) := by
    rw [ha, hb]
    exact ⟨hm0, hmK⟩
  obtain ⟨r, _, hr⟩ := intermediate_value_Icc hab hf_cont.continuousOn hm_mem
  refine ⟨K ∩ {x : E n | x 0 ≤ r}, ?_, inter_subset_left, hr⟩
  exact hK.inter_right (isClosed_le (EuclideanSpace.proj (0 : Fin (n + 1))).continuous continuous_const)

private lemma exact_volumes {n : ℕ} {K : Set (E n)} (hK : IsCompact K) (hKne : K.Nonempty) :
    ∀ m : ℝ, m ∈ Icc 0 (vol K) ↔ ∀ δ : ℝ, 0 < δ → ∃ H : Set (E n),
      IsCompact H ∧ H.Nonempty ∧ hausdorffDist K H < δ ∧ vol H = m := by
  intro m
  constructor
  · rintro ⟨hm0, hmK⟩ δ hδ
    obtain ⟨F, hFK, hFfin, hFcov⟩ := finite_approx_of_totallyBounded hK.totallyBounded (δ / 2) (half_pos hδ)
    have hFne : F.Nonempty := by
      obtain ⟨x₀, hx₀⟩ := hKne
      have hx₀' := hFcov hx₀
      simp only [mem_iUnion, mem_ball, exists_prop] at hx₀'
      obtain ⟨y, hyF, _⟩ := hx₀'
      exact ⟨y, hyF⟩
    obtain ⟨K', hK'c, hK'sub, hK'vol⟩ := exists_subset_with_vol hK hm0 hmK
    refine ⟨F ∪ K', hFfin.isCompact.union hK'c, hFne.mono subset_union_left, ?_, ?_⟩
    · have hle : hausdorffDist K (F ∪ K') ≤ δ / 2 := by
        apply hausdorffDist_le_of_mem_dist (half_pos hδ).le
        · intro x hxK
          have hx' := hFcov hxK
          simp only [mem_iUnion, mem_ball, exists_prop] at hx'
          obtain ⟨y, hyF, hxy⟩ := hx'
          exact ⟨y, Or.inl hyF, hxy.le⟩
        · intro y hy
          have hyK : y ∈ K := by
            rcases hy with hyF | hyK'
            · exact hFK hyF
            · exact hK'sub hyK'
          exact ⟨y, hyK, by simp [(half_pos hδ).le]⟩
      linarith
    · have hFvol : vol F = 0 := by
        simp [vol_eq, Measure.real, volume_finite_zero hFfin]
      apply le_antisymm
      · exact (measureReal_union_le F K').trans (by rw [← vol_eq, ← vol_eq, hFvol, hK'vol, zero_add])
      · have hfin : volume (F ∪ K') ≠ ⊤ := (hFfin.isCompact.union hK'c).measure_lt_top.ne
        rw [← hK'vol]
        exact measureReal_mono subset_union_right hfin
  · intro h
    constructor
    · obtain ⟨H, _, _, _, rfl⟩ := h 1 zero_lt_one
      exact measureReal_nonneg
    · apply le_of_forall_pos_lt_add
      intro ε hε
      obtain ⟨δ, hδpos, hδ⟩ := upper_semicont hK hKne ε hε
      obtain ⟨H, hHc, hHne, hHdist, rfl⟩ := h δ hδpos
      exact hδ H hHc hHne hHdist

private lemma continuous_iff_zero {n : ℕ} {K : Set (E n)} (hK : IsCompact K) (hKne : K.Nonempty) :
    (∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ H : Set (E n), IsCompact H → H.Nonempty →
      hausdorffDist K H < δ → |vol H - vol K| < ε) ↔ vol K = 0 := by
  constructor
  · intro hcont
    by_contra hne
    have hpos : 0 < vol K := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
    obtain ⟨δ, hδpos, hδ⟩ := hcont (vol K / 2) (half_pos hpos)
    have h0mem : (0 : ℝ) ∈ Icc 0 (vol K) := ⟨le_rfl, hpos.le⟩
    obtain ⟨H, hHc, hHne, hHdist, hHvol⟩ := (exact_volumes hK hKne 0).mp h0mem δ hδpos
    have hlt := hδ H hHc hHne hHdist
    rw [hHvol, zero_sub, abs_neg, abs_of_pos hpos] at hlt
    linarith
  · intro hzero ε hε
    obtain ⟨δ, hδpos, hδ⟩ := upper_semicont hK hKne ε hε
    refine ⟨δ, hδpos, fun H hHc hHne hHdist => ?_⟩
    have hlt := hδ H hHc hHne hHdist
    rw [hzero, zero_add] at hlt
    rw [hzero, sub_zero, abs_of_nonneg (by rw [vol_eq]; exact measureReal_nonneg)]
    exact hlt

end OMA.S_mo_364097_aux

theorem OMA.solution : type_of% @OMA.S_mo_364097.main := by
  intro n K hK hKne
  exact ⟨OMA.S_mo_364097_aux.upper_semicont hK hKne,
    OMA.S_mo_364097_aux.exact_volumes hK hKne,
    OMA.S_mo_364097_aux.continuous_iff_zero hK hKne⟩
