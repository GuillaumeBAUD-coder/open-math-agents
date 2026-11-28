import OMAReductions.R_Kourovka_1_74_kourovka_1_74_variants_tarski_monster_R1
import Mathlib.Topology.Algebra.FilterBasis

/-! The given filter is the identity neighborhood filter of a topological group. -/

open scoped Pointwise Topology

theorem OMA.solution : OMA.R_Kourovka_1_74_kourovka_1_74_variants_tarski_monster_R1.H2 := by
  intro G _ F hone hmul hinv hconj hnondiscrete ⟨U, hU, hproper⟩
  let basis : GroupFilterBasis G :=
    { toFilterBasis := F.asBasis
      one' := fun h => hone _ h
      mul' := by
        intro W hW
        obtain ⟨V, hV, hproduct⟩ := hmul W hW
        refine ⟨V, hV, ?_⟩
        intro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hz
        exact hproduct x hx y hy
      inv' := fun h => ⟨_, hinv _ h, Set.Subset.rfl⟩
      conj' := by
        intro g W hW
        exact ⟨_, hconj g W hW, Set.Subset.rfl⟩ }
  letI : TopologicalSpace G := basis.topology
  have hnhds : 𝓝 (1 : G) = F :=
    basis.nhds_one_eq.trans F.asBasis_filter
  refine ⟨basis.topology, basis.isTopologicalGroup, ?_, ?_⟩
  · intro hdiscrete
    letI : DiscreteTopology G := hdiscrete
    exact hnondiscrete (hnhds.symm.trans (congrFun (nhds_discrete G) 1))
  · have hU' : U ∈ 𝓝 (1 : G) := hnhds.symm ▸ hU
    refine ⟨interior U, isOpen_interior, ⟨1, mem_interior_iff_mem_nhds.mpr hU'⟩, ?_⟩
    intro h
    exact hproper (Set.univ_subset_iff.mp (h ▸ interior_subset))
