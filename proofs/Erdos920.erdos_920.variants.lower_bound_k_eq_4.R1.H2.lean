import OMAReductions.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1

/-! The Ramsey witness holds for cliques of any order. The board step uses k = 4. -/

open SimpleGraph


private theorem ramsey_witness (k m N : ℕ) (h : N < classicalRamsey k m) :
    ∃ G : SimpleGraph (Fin N), G.CliqueFree k ∧ G.indepNum < m := by
  classical
  have outside : ¬ ∀ G : SimpleGraph (Fin N),
      (completeGraph (Fin k)).IsContained G ∨ (completeGraph (Fin m)).IsContained Gᶜ := by
    intro allGraphs
    exact (Nat.not_le_of_lt h) (Nat.sInf_le allGraphs)
  push Not at outside
  obtain ⟨G, hk, hm⟩ := outside
  have left : G.CliqueFree k := cliqueFree_iff.mpr hk
  have right : Gᶜ.CliqueFree m := cliqueFree_iff.mpr hm
  refine ⟨G, left, ?_⟩
  by_contra! hlarge
  have hsize : m ≤ Gᶜ.cliqueNum := by simpa only [cliqueNum_compl] using hlarge
  obtain ⟨S, hS⟩ := Gᶜ.exists_isNClique_cliqueNum
  exact right.mono hsize S hS

theorem OMA.solution : OMA.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1.H2 := by
  intro m N hN
  exact ramsey_witness 4 m N hN
