import OMAReductions.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1

open SimpleGraph

-- Step Erdos920.erdos_920.variants.lower_bound_k_eq_4.R1.H2: hypothesis H2 of reduction Erdos920.erdos_920.variants.lower_bound_k_eq_4.R1
-- Credit: @DeepDuke
-- H2 := ∀ m N : ℕ, N < SimpleGraph.classicalRamsey 4 m →     ∃ G : SimpleGraph (Fin N), G.CliqueFree 4 ∧ G.indepNum < m  /-- `f₄(n)` is at least the chromatic number of any `K₄`-free graph on `n` vertices. -/

theorem OMA.solution : OMA.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1.H2 := by
  intro m N hN
  classical
  have hn : ¬ ∀ G : SimpleGraph (Fin N),
      SimpleGraph.completeGraph (Fin 4) ⊑ G ∨ SimpleGraph.completeGraph (Fin m) ⊑ Gᶜ := by
    intro h
    have hh : SimpleGraph.classicalRamsey 4 m ≤ N := Nat.sInf_le h
    omega
  push Not at hn
  obtain ⟨G,h4,hm⟩ := hn
  have hG : G.CliqueFree 4 := SimpleGraph.cliqueFree_iff.mpr h4
  refine ⟨G,hG,?_⟩
  have hcomp : Gᶜ.CliqueFree m := SimpleGraph.cliqueFree_iff.mpr hm
  have hlt : Gᶜ.cliqueNum < m := by
    by_contra! hle
    obtain ⟨s,hs⟩ := Gᶜ.exists_isNClique_cliqueNum
    exact (SimpleGraph.CliqueFree.mono hle hcomp) s hs
  simpa using hlt

