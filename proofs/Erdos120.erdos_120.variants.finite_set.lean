import FormalConjectures.ErdosProblems.«120»

/-! # Finite sets admit affine copies inside sets of positive measure -/
-- Credit: @steveDOTdigital

open Set MeasureTheory Filter
open scoped Topology Pointwise ENNReal

theorem OMA.solution : type_of% @Erdos120.erdos_120.variants.finite_set := by
  classical
  intro A h
  rintro ⟨E, hE, hpos, havoid⟩
  obtain ⟨K, hKE, hK, hKpos⟩ := hE.exists_lt_isCompact hpos
  let loss (a x : ℝ) := volume (((a * x) +ᵥ K) \ K)
  have small (x : ℝ) : Tendsto (fun a => loss a x) (𝓝 0) (𝓝 0) := by
    exact (tendsto_measure_vadd_sdiff_isCompact_isClosed (μ := volume) hK hK.isClosed).comp
      (by simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const x)
  have total : Tendsto (fun a => ∑ x ∈ h.toFinset, loss a x) (𝓝 0) (𝓝 0) := by
    simpa using tendsto_finsetSum h.toFinset (fun x _ => small x)
  have nonzero : ∀ᶠ a : ℝ in 𝓝[≠] 0, a ≠ 0 := self_mem_nhdsWithin
  obtain ⟨a, ha, hsum⟩ := (nonzero.and
    ((total.eventually_lt_const hKpos).filter_mono nhdsWithin_le_nhds)).exists
  -- Translating the part of a translated K that misses K back by -a*x
  -- records exactly the failed starting points for x.
  let bad (x : ℝ) : Set ℝ := (-(a * x)) +ᵥ (((a * x) +ᵥ K) \ K)
  have bound : volume (⋃ x ∈ h.toFinset, bad x) < volume K := by
    refine (measure_biUnion_finset_le _ _).trans_lt ?_
    simpa only [bad, measure_vadd, loss] using hsum
  obtain ⟨b, hb, hgood⟩ := Set.not_subset.1 (fun hs => bound.not_ge (measure_mono hs))
  apply havoid a b ha
  rintro _ ⟨x, hx, rfl⟩
  apply hKE
  by_contra hmiss
  apply hgood
  refine Set.mem_iUnion₂.2 ⟨x, h.mem_toFinset.2 hx, a * x + b, ⟨⟨b, hb, rfl⟩, hmiss⟩, ?_⟩
  change -(a * x) + (a * x + b) = b
  simp
