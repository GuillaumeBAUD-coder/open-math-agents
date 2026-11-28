import OMAStatements.S_mo_229756

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise Topology

theorem OMA.solution : type_of% @OMA.S_mo_229756.main := by
  intro G _ _ _ _ _ _ _ μ _ _ H hH hpos hfin
  refine ⟨H.isOpen_of_mem_nhds (g := 1) ?_, ?_⟩
  · exact mem_of_superset (div_mem_nhds_one_of_haar_pos_ne_top μ (H : Set G) hH hpos hfin)
      (div_subset_iff.mpr fun x hx y hy ↦ H.div_mem hx hy)
  obtain ⟨K, hKH, hK, hlarge⟩ :=
    hH.exists_lt_isCompact_of_ne_top hfin (ENNReal.half_lt_self hpos.ne' hfin)
  have hquot : K / K = (H : Set G) := by
    apply Subset.antisymm
    · exact div_subset_iff.mpr fun x hx y hy ↦ H.div_mem (hKH hx) (hKH hy)
    · intro g hg
      have htranslate : g • K ⊆ (H : Set G) := by
        rintro _ ⟨x, hx, rfl⟩
        exact H.mul_mem hg (hKH hx)
      have hmeet : ¬ Disjoint (g • K) K := by
        intro hd
        have hbound := measure_mono (μ := μ) (union_subset htranslate hKH)
        rw [measure_union hd hK.measurableSet, measure_smul] at hbound
        have htooLarge := ENNReal.add_lt_add hlarge hlarge
        rw [ENNReal.add_halves] at htooLarge
        exact htooLarge.not_ge hbound
      obtain ⟨y, hy, hyK⟩ := not_disjoint_iff.mp hmeet
      obtain ⟨x, hxK, rfl⟩ := mem_smul_set.mp hy
      exact mem_div.mpr ⟨g * x, hyK, x, hxK, mul_div_cancel_right _ _⟩
  rw [← hquot, div_eq_mul_inv]
  exact hK.mul hK.inv
