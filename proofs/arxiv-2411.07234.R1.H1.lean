import OMAReductions.R_arxiv_2411_07234_R1

-- Step H1 of reduction arxiv-2411.07234.R1: mixing gives multiple mixing for k < 3.
-- k = 0 and k = 1 follow from invariance of μ; for k = 2, invariance under T^[d r 0] reduces
-- μ (T^{-a} A₀ ∩ T^{-b} A₁) to μ (A₀ ∩ T^{-(b-a)} A₁), and b - a > r tends to infinity.
-- Credit: @GiridhariPradeep (agent: Claude Code)

open MeasureTheory Filter
open scoped Topology BigOperators

theorem OMA.solution : OMA.R_arxiv_2411_07234_R1.H1 := by
  intro X _ μ _ T hT hmix k hk d hd A hA
  interval_cases k
  · have h : ∀ r, μ (⋂ i : Fin 0, (T^[d r i]) ⁻¹' A i) = ∏ i : Fin 0, μ (A i) := by
      intro r
      simp [measure_univ]
    simp only [h]
    exact tendsto_const_nhds
  · have h : ∀ r, μ (⋂ i : Fin 1, (T^[d r i]) ⁻¹' A i) = ∏ i : Fin 1, μ (A i) := by
      intro r
      have hset : (⋂ i : Fin 1, (T^[d r i]) ⁻¹' A i) = (T^[d r 0]) ⁻¹' A 0 := by
        ext x
        simp [Fin.forall_fin_one]
      rw [hset, Fin.prod_univ_one]
      exact (hT.iterate (d r 0)).measure_preimage (hA 0).nullMeasurableSet
    simp only [h]
    exact tendsto_const_nhds
  · -- the gap m r = d r 1 - d r 0 exceeds r
    have hgap : ∀ r, d r 0 + r < d r 1 := fun r => hd r 0 1 (by decide)
    set m : ℕ → ℕ := fun r => d r 1 - d r 0 with hm
    have hmtop : Tendsto m atTop atTop := by
      refine tendsto_atTop_mono (fun r => ?_) tendsto_id
      have := hgap r
      simp only [hm, id]
      omega
    have h : ∀ r, μ (⋂ i : Fin 2, (T^[d r i]) ⁻¹' A i) = μ (A 0 ∩ (T^[m r]) ⁻¹' A 1) := by
      intro r
      have hsplit : d r 1 = m r + d r 0 := by
        have := hgap r
        simp only [hm]
        omega
      have hset : (⋂ i : Fin 2, (T^[d r i]) ⁻¹' A i) =
          (T^[d r 0]) ⁻¹' (A 0 ∩ (T^[m r]) ⁻¹' A 1) := by
        ext x
        simp only [Set.mem_iInter, Fin.forall_fin_two, Set.mem_preimage, Set.mem_inter_iff]
        rw [hsplit, Function.iterate_add_apply]
      rw [hset]
      exact (hT.iterate (d r 0)).measure_preimage
        ((hA 0).inter ((hT.iterate (m r)).measurable (hA 1))).nullMeasurableSet
    simp only [h, Fin.prod_univ_two]
    exact (hmix (A 0) (A 1) (hA 0) (hA 1)).comp hmtop
