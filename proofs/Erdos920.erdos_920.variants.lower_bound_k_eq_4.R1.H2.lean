import OMAReductions.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1
import Mathlib

-- Step Erdos920.erdos_920.variants.lower_bound_k_eq_4.R1.H2: hypothesis H2 of reduction Erdos920.erdos_920.variants.lower_bound_k_eq_4.R1
-- Credit: @ivillar
--
-- Below the infimum defining R(4, m), the Ramsey property fails: some graph on N vertices
-- contains neither K_4 nor (in its complement) K_m.

theorem OMA.solution : OMA.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1.H2 := by
  unfold OMA.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1.H2
  intro m N hN
  unfold SimpleGraph.classicalRamsey SimpleGraph.graphRamsey at hN
  have hnot := Nat.notMem_of_lt_sInf hN
  simp only [Set.mem_setOf_eq, not_forall, not_or] at hnot
  obtain ⟨C, h4, hm⟩ := hnot
  refine ⟨C, ?_, ?_⟩
  · by_contra h
    exact h4 ((SimpleGraph.not_cliqueFree_iff_top_isContained 4).mp h)
  · by_contra h
    rw [not_lt] at h
    have hfree : Cᶜ.CliqueFree m := by
      by_contra h'
      exact hm ((SimpleGraph.not_cliqueFree_iff_top_isContained m).mp h')
    have hfree' : Cᶜ.CliqueFree Cᶜ.cliqueNum := by
      apply hfree.mono
      rw [SimpleGraph.cliqueNum_compl]
      exact h
    obtain ⟨s, hs⟩ := Cᶜ.exists_isNClique_cliqueNum
    exact hfree' s hs
