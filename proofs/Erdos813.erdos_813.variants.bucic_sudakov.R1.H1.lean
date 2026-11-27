import OMAReductions.R_Erdos813_erdos_813_variants_bucic_sudakov_R1

-- Step Erdos813.erdos_813.variants.bucic_sudakov.R1.H1: hypothesis H1 of reduction Erdos813.erdos_813.variants.bucic_sudakov.R1

/-!
For `ε ≥ 5/12` the exponent is non-positive, so `n ^ (5/12 - ε) ≤ 1` for `n ≥ 1`. And `h n ≥ 1`
for `n ≥ 1`: the infimum defining `h n` is attained by some graph, and a single vertex is a clique.
-/

theorem OMA.solution : OMA.R_Erdos813_erdos_813_variants_bucic_sudakov_R1.H1 := by
  unfold OMA.R_Erdos813_erdos_813_variants_bucic_sudakov_R1.H1
  intro ε hε
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have hne : {k : ℕ | ∃ G : SimpleGraph (Fin n),
      Erdos813.EverySevenHasTriangle G ∧ G.cliqueNum = k}.Nonempty :=
    ⟨_, ⊤, Erdos813.everySevenHasTriangle_top n, rfl⟩
  obtain ⟨G, _, hG⟩ := Nat.sInf_mem hne
  have h1 : 1 ≤ Erdos813.h n := by
    unfold Erdos813.h
    rw [← hG]
    have hc : G.IsClique (↑({(⟨0, by omega⟩ : Fin n)} : Finset (Fin n))) := by
      rw [Finset.coe_singleton]
      exact SimpleGraph.isClique_singleton _
    have hcard := hc.card_le_cliqueNum
    rw [Finset.card_singleton] at hcard
    exact hcard
  have h2 : (n : ℝ) ^ (5 / 12 - ε : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)
  have h3 : (1 : ℝ) ≤ (Erdos813.h n : ℝ) := by exact_mod_cast h1
  linarith
