import OMAStatements.S_mo_264599

open Cardinal MeasureTheory Set
open scoped ENNReal Pointwise Topology

namespace OMA.Mo264599

private abbrev UnitInterval := Icc (0 : ℝ) 1

private abbrev PositiveCompact :=
  {K : Set ℝ // K ⊆ Icc 0 1 ∧ IsCompact K ∧ 0 < volume K}

private theorem volume_unitInterval : volume (Icc (0 : ℝ) 1) = 1 := by
  simp [Real.volume_Icc]

private theorem card_positiveCompact_set (K : PositiveCompact) : #K.val = 𝔠 := by
  have hfinite : volume K.val ≠ ∞ :=
    ((measure_mono K.property.1).trans_lt (by rw [volume_unitInterval]; exact ENNReal.one_lt_top)).ne
  have hnear := Measure.sub_mem_nhds_zero_of_addHaar_pos_ne_top volume K.val
    K.property.2.1.measurableSet K.property.2.2 hfinite
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hinterval : Ioo (-ε) ε ⊆ K.val - K.val := by
    intro x hx
    apply hball
    simpa [Metric.mem_ball, Real.dist_eq, abs_lt] using hx
  let subPoints : K.val × K.val → ℝ := fun p ↦ (p.1 : ℝ) - p.2
  have hsub : range subPoints = K.val - K.val := by
    ext x
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact Set.mem_sub.mpr ⟨a, a.2, b, b.2, rfl⟩
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sub.mp hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hcard := (mk_le_mk_of_subset hinterval).trans
    (hsub ▸ mk_range_le (f := subPoints))
  simp only [mk_Ioo_real (by linarith : -ε < ε), mk_prod, lift_id] at hcard
  have hinfinite : ℵ₀ ≤ #K.val := by
    by_contra! h
    exact K.property.2.2.ne' ((le_aleph0_iff_set_countable.mp h.le).measure_zero volume)
  rw [mul_eq_self hinfinite] at hcard
  exact le_antisymm (mk_real ▸ mk_set_le _) hcard

private theorem card_positiveCompact_le : #PositiveCompact ≤ 𝔠 := by
  have hmeasurable : #{K : Set ℝ | MeasurableSet K} ≤ 𝔠 := by
    obtain ⟨b, hb, hgen⟩ :=
      (inferInstance : MeasurableSpace.CountablyGenerated ℝ).isCountablyGenerated
    rw [hgen]
    exact MeasurableSpace.cardinal_measurableSet_le_continuum
      ((le_aleph0_iff_set_countable.mpr hb).trans aleph0_lt_continuum.le)
  let f : PositiveCompact → {K : Set ℝ | MeasurableSet K} :=
    fun K ↦ ⟨K.val, K.property.2.1.measurableSet⟩
  have hf : Function.Injective f := fun _ _ h ↦
    Subtype.ext (congrArg (fun K : {K : Set ℝ | MeasurableSet K} ↦ K.val) h)
  exact (mk_le_of_injective hf).trans hmeasurable

/-- A well-order of initial ordinal type lets each step avoid all earlier choices. -/
private theorem exists_injective_mem {ι : Type} (s : ι → Set ℝ) (hs : ∀ i, #ι ≤ #(s i)) :
    ∃ f : ι → ℝ, Function.Injective f ∧ ∀ i, f i ∈ s i := by
  classical
  obtain ⟨order, founded, hord⟩ := exists_ord_eq_type_lt ι
  let := order
  let := founded
  let chooseNext (i : ι) (previous : ∀ j, j < i → ℝ) :=
    fun x ↦ x ∈ s i ∧ x ∉ range (fun j : Iio i ↦ previous j j.2)
  have hexists (i : ι) (previous : ∀ j, j < i → ℝ) : ∃ x, chooseNext i previous x := by
    dsimp [chooseNext]
    by_contra! hn
    have hsubset : s i ⊆ range (fun j : Iio i ↦ previous j j.2) :=
      fun x hx ↦ hn x hx
    exact ((mk_range_le.trans_lt (mk_Iio_lt i hord)).trans_le (hs i)).not_ge
      (mk_le_mk_of_subset hsubset)
  let step (i : ι) (previous : ∀ j, j < i → ℝ) := Classical.choose (hexists i previous)
  let f : ι → ℝ := wellFounded_lt.fix step
  have hf (i : ι) : chooseNext i (fun j _ ↦ f j) (f i) := by
    rw [show f i = step i (fun j _ ↦ f j) from wellFounded_lt.fix_eq step i]
    exact Classical.choose_spec (hexists i (fun j _ ↦ f j))
  have hne (i j : ι) (h : i < j) : f i ≠ f j :=
    fun heq ↦ (hf j).2 ⟨⟨i, h⟩, heq⟩
  refine ⟨f, ?_, fun i ↦ (hf i).1⟩
  intro i j heq
  rcases lt_trichotomy i j with h | h | h
  · exact (hne i j h heq).elim
  · exact h
  · exact (hne j i h heq.symm).elim

private theorem volume_eq_one_of_hits (A : Set ℝ) (hA : A ⊆ Icc 0 1)
    (hhit : ∀ K : PositiveCompact, (A ∩ K.val).Nonempty) :
    volume A = 1 := by
  apply le_antisymm (volume_unitInterval ▸ measure_mono hA)
  by_contra! hsmall
  obtain ⟨T, hAT, hT, hvolT⟩ := exists_measurable_superset volume A
  let B := Icc (0 : ℝ) 1 \ T
  have hB : B ⊆ Icc (0 : ℝ) 1 := sdiff_subset
  have hBfin : volume B ≠ ∞ :=
    ((measure_mono hB).trans_lt (by rw [volume_unitInterval]; exact ENNReal.one_lt_top)).ne
  have hBpos : 0 < volume B := by
    by_contra! hn
    have h := measure_inter_add_sdiff (μ := (volume : Measure ℝ)) (Icc (0 : ℝ) 1) hT
    change volume (Icc (0 : ℝ) 1 ∩ T) + volume B = volume (Icc (0 : ℝ) 1) at h
    rw [le_antisymm hn bot_le, add_zero, volume_unitInterval] at h
    exact hsmall.not_ge (hvolT ▸ h ▸ measure_mono inter_subset_right)
  obtain ⟨K, hKB, hK, hKpos⟩ :=
    (measurableSet_Icc.diff hT).exists_lt_isCompact_of_ne_top hBfin hBpos
  obtain ⟨x, hxA, hxK⟩ := hhit ⟨K, hKB.trans hB, hK, hKpos⟩
  exact (hKB hxK).2 (hAT hxA)

private theorem partition_exists : type_of% @OMA.S_mo_264599.main := by
  classical
  let Index := UnitInterval × PositiveCompact
  have hcard : #Index ≤ 𝔠 := by
    change #(UnitInterval × PositiveCompact) ≤ 𝔠
    simp only [mk_prod, lift_id, mk_Icc_real (by norm_num : (0 : ℝ) < 1)]
    calc
      _ ≤ 𝔠 * 𝔠 := by gcongr; exact card_positiveCompact_le
      _ = 𝔠 := mul_eq_self aleph0_lt_continuum.le
  obtain ⟨pick, hpick, hpick_mem⟩ :=
    exists_injective_mem (fun i : Index ↦ i.2.val) fun i ↦ card_positiveCompact_set i.2 ▸ hcard
  let owner (x : ℝ) : UnitInterval :=
    if h : ∃ i, pick i = x then (Classical.choose h).1 else ⟨0, le_rfl, zero_le_one⟩
  have howner (i : Index) : owner (pick i) = i.1 := by
    have h : ∃ j, pick j = pick i := ⟨i, rfl⟩
    dsimp [owner]
    rw [dif_pos h, hpick (Classical.choose_spec h)]
  let A (i : UnitInterval) : Set ℝ := {x | x ∈ Icc 0 1 ∧ owner x = i}
  refine ⟨A, ?_, ?_, ?_⟩
  · intro i j hij
    exact disjoint_left.mpr fun _ hi hj ↦ hij (hi.2.symm.trans hj.2)
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact hi.1
    · intro hx
      exact mem_iUnion.mpr ⟨owner x, hx, rfl⟩
  · intro i
    refine volume_eq_one_of_hits (A i) (fun _ hx ↦ hx.1) fun K ↦ ?_
    exact ⟨pick (i, K), ⟨K.property.1 (hpick_mem (i, K)), howner (i, K)⟩, hpick_mem (i, K)⟩

end OMA.Mo264599

theorem OMA.solution : type_of% @OMA.S_mo_264599.main := OMA.Mo264599.partition_exists
