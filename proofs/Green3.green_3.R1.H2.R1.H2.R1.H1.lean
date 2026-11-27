import OMAReductions.R_Green3_green_3_R1_H2_R1_H2_R1

/-! Inner approximation by closed geometric cells. Original Lean proof by @Deldor14.
The three-prefix inequality is from Franchi–Gowers–Yip, arXiv:2607.06073, Lemma 2.1. -/

open Set MeasureTheory Finset

private lemma bracket (q : ℝ) (B : ℕ) (x : ℝ) (hx : q^B ≤ x) (hx1 : x < 1) :
    ∃ i < B, q^(i+1) ≤ x ∧ x ≤ q^i := by
  induction B with
  | zero => simp at hx; linarith
  | succ B ih =>
    by_cases h : q^B ≤ x
    · obtain ⟨i,hi,hil,hir⟩ := ih h
      exact ⟨i,by omega,hil,hir⟩
    · exact ⟨B,by omega,hx,(not_le.mp h).le⟩

private lemma geometric_extraction (U : Set ℝ) (hU : IsOpen U) (hu : U ⊆ Icc 0 1)
    (hvol : 1/3 < volume U) (hp : ∀ x ∈ U, ∀ y ∈ U, x*y ∉ U) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ T : Finset ℕ, T.Nonempty ∧
      (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) ∧
      1/3 < (1-q)*(∑ i ∈ T, q^i) := by
  classical
  obtain ⟨K,hKU,hK,hlarge⟩ := hU.measurableSet.exists_lt_isCompact hvol
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_thickening_subset_open hU hKU
  let q := 1 - min (δ/2) (1/2)
  have hw : 0 < min (δ/2) (1/2:ℝ) := lt_min (by positivity) (by norm_num)
  have hq : 0 < q := by dsimp [q]; linarith [min_le_right (δ/2) (1/2:ℝ)]
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hδq : 1-q < δ := by dsimp [q]; linarith [min_le_left (δ/2) (1/2:ℝ)]
  have hpart : U ⊆ Set.Ioo 0 1 := by simpa using interior_maximal hu hU
  have hne : K.Nonempty := by
    by_contra! h
    simp [h] at hlarge
  obtain ⟨x₀,hx₀,hmin⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
  obtain ⟨B,hB⟩ := exists_pow_lt_of_lt_one (hpart (hKU hx₀)).1 hq1
  let C : ℕ → Set ℝ := fun i => Icc (q^(i+1)) (q^i)
  let T := (range B).filter (fun i => C i ⊆ U)
  have hclosed (i : ℕ) (hi : i ∈ T) : C i ⊆ U := (mem_filter.mp hi).2
  have hend (i : ℕ) : q^(i+1) ≤ q^i := pow_le_pow_of_le_one hq.le hq1.le (by omega)
  have hcover : K ⊆ ⋃ i ∈ T, C i := by
    intro x hx
    obtain ⟨i,hi,hil,hir⟩ := bracket q B x (hB.le.trans (hmin hx)) (hpart (hKU hx)).2
    have hsmall : q^i-q^(i+1) < δ := calc
      _ = (1-q)*q^i := by rw [pow_succ]; ring
      _ ≤ (1-q)*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hq.le hq1.le) (by linarith)
      _ < δ := by simpa using hδq
    have hstay : C i ⊆ U := by
      intro y hy
      apply hthick
      apply Metric.mem_thickening_iff.mpr
      refine ⟨x,hx,?_⟩
      obtain ⟨hyl,hyr⟩ := hy
      rw [Real.dist_eq,abs_lt]
      constructor <;> linarith
    exact mem_iUnion₂.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr hi,hstay⟩,hil,hir⟩
  have hmeas (i : ℕ) : volume (C i) = ENNReal.ofReal ((1-q)*q^i) := by
    rw [show C i = Icc (q^(i+1)) (q^i) from rfl,Real.volume_Icc,pow_succ]
    congr 1
    ring
  have hupper : volume K ≤ ENNReal.ofReal ((1-q)*(∑ i ∈ T, q^i)) := calc
    volume K ≤ volume (⋃ i ∈ T, C i) := measure_mono hcover
    _ ≤ ∑ i ∈ T, volume (C i) := measure_biUnion_finset_le _ _
    _ = ∑ i ∈ T, ENNReal.ofReal ((1-q)*q^i) := sum_congr rfl fun i _ => hmeas i
    _ = ENNReal.ofReal (∑ i ∈ T, (1-q)*q^i) := (ENNReal.ofReal_sum_of_nonneg
          (fun i _ => mul_nonneg (sub_nonneg.mpr hq1.le) (pow_nonneg hq.le i))).symm
    _ = _ := by rw [Finset.mul_sum]
  have hbig : (1:ℝ)/3 < (1-q)*(∑ i ∈ T, q^i) := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3)]
    simpa using hlarge.trans_le hupper
  have hT : T.Nonempty := by
    by_contra! h
    simp [h] at hbig
    linarith
  have upper (i : ℕ) (hi : i ∈ T) : q^i ∈ U := hclosed i hi ⟨hend i,le_rfl⟩
  have lower (i : ℕ) (hi : i ∈ T) : q^(i+1) ∈ U := hclosed i hi ⟨le_rfl,hend i⟩
  refine ⟨q,hq,hq1,T,hT,?_,hbig⟩
  intro i hi j hj l hl
  by_contra! hf
  have hcases : l+1=i+j ∨ l=i+j ∨ l=(i+1)+j ∨ l=(i+1)+(j+1) := by omega
  rcases hcases with h | h | h | h
  · exact hp _ (upper i hi) _ (upper j hj) (by rw [← pow_add,←h]; exact lower l hl)
  · exact hp _ (upper i hi) _ (upper j hj) (by rw [← pow_add,←h]; exact upper l hl)
  · exact hp _ (lower i hi) _ (upper j hj) (by rw [← pow_add,←h]; exact upper l hl)
  · exact hp _ (lower i hi) _ (lower j hj) (by rw [← pow_add,←h]; exact upper l hl)

theorem OMA.solution : OMA.R_Green3_green_3_R1_H2_R1_H2_R1.H1 := by
  exact geometric_extraction
