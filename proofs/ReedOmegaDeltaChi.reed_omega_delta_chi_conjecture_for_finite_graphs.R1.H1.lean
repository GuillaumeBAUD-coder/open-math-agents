import OMAReductions.R_ReedOmegaDeltaChi_reed_omega_delta_chi_conjecture_for_finite_graphs_R1

/-!
# Proof of `ReedOmegaDeltaChi.reed_omega_delta_chi_conjecture_for_finite_graphs.R1.H1`

Proves Reed's conjecture `2 * χ(G) ≤ ω(G) + Δ(G) + 2` for finite graphs with `Δ(G) ≤ ω(G)`.

By induction on `Fintype.card V`, every finite simple graph `G` admits a proper coloring with
`G.maxDegree + 1` colors (removing a vertex `v`, inductively coloring `G - v`, and assigning `v`
a color unused among its at most `G.maxDegree` neighbors). Thus
`G.chromaticNumber ≤ G.maxDegree + 1`, whence
`2 * G.chromaticNumber ≤ 2 * (G.maxDegree + 1) ≤ G.cliqueNum + G.maxDegree + 2`.
-/

namespace ReedR1H1Proof

private lemma exists_coloring_maxDegree_succ :
    ∀ (n : ℕ) {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n →
      Nonempty (G.Coloring (Fin (G.maxDegree + 1))) := by
  intro n
  induction n with
  | zero =>
    intro V _ _ G _ hcard
    have : IsEmpty V := Fintype.card_eq_zero_iff.mp hcard
    exact ⟨SimpleGraph.Coloring.mk (fun v => (IsEmpty.false v).elim) (fun {v} => (IsEmpty.false v).elim)⟩
  | succ m ih =>
    intro V _ _ G _ hcard
    have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v₀⟩ := hne
    let W := {v : V // v ≠ v₀}
    let H : SimpleGraph W := G.induce {v : V | v ≠ v₀}
    have hcardW : Fintype.card W = m := by
      have h1 : Fintype.card W + 1 = Fintype.card V := by
        have := Fintype.card_subtype_compl (fun v : V => v = v₀)
        simp only [Fintype.card_unique] at this
        have h2 : Fintype.card {v : V // ¬ v = v₀} = Fintype.card W := rfl
        omega
      omega
    obtain ⟨cH⟩ := ih H hcardW
    have hdegH : H.maxDegree ≤ G.maxDegree := by
      by_cases hW : Nonempty W
      · obtain ⟨w, hw⟩ := H.exists_maximal_degree_vertex
        have hle1 : H.degree w ≤ G.degree w.1 := by
          have hinj : (H.neighborFinset w).card ≤ (G.neighborFinset w.1).card := by
            refine Finset.card_le_card_of_injOn Subtype.val ?_ ?_
            · intro u hu
              simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hu ⊢
              exact hu
            · intro u₁ _ u₂ _ h
              exact Subtype.ext h
          simpa [SimpleGraph.card_neighborFinset_eq_degree] using hinj
        have hle2 : G.degree w.1 ≤ G.maxDegree := G.degree_le_maxDegree w.1
        omega
      · have : IsEmpty W := not_nonempty_iff.mp hW
        have : H.maxDegree = 0 := by
          unfold SimpleGraph.maxDegree
          simp
        omega
    -- Embed cH colors into Fin (G.maxDegree + 1)
    let emb : Fin (H.maxDegree + 1) → Fin (G.maxDegree + 1) :=
      fun k => ⟨k.val, by omega⟩
    let used : Finset (Fin (G.maxDegree + 1)) :=
      (G.neighborFinset v₀).attach.image fun u =>
        emb (cH ⟨u.1, (G.ne_of_adj ((SimpleGraph.mem_neighborFinset G v₀ u.1).mp u.2)).symm⟩)
    have hcard_used : used.card < Fintype.card (Fin (G.maxDegree + 1)) := by
      calc used.card ≤ (G.neighborFinset v₀).attach.card := Finset.card_image_le
        _ = (G.neighborFinset v₀).card := Finset.card_attach
        _ = G.degree v₀ := G.card_neighborFinset_eq_degree v₀
        _ ≤ G.maxDegree := G.degree_le_maxDegree v₀
        _ < G.maxDegree + 1 := Nat.lt_succ_self _
        _ = Fintype.card (Fin (G.maxDegree + 1)) := (Fintype.card_fin _).symm
    have hne_compl : (Finset.univ \ used).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hsub : Finset.univ ⊆ used := Finset.sdiff_eq_empty_iff_subset.mp hempty
      have hle := Finset.card_le_card hsub
      rw [Finset.card_univ] at hle
      omega
    obtain ⟨c₀, hc₀⟩ := hne_compl
    have hc₀_not : c₀ ∉ used := (Finset.mem_sdiff.mp hc₀).2
    refine ⟨SimpleGraph.Coloring.mk
      (fun v => if hv : v = v₀ then c₀ else emb (cH ⟨v, hv⟩)) ?_⟩
    intro u w hadj
    by_cases hu : u = v₀
    · subst hu
      have hw : w ≠ u := (G.ne_of_adj hadj).symm
      rw [dif_pos rfl, dif_neg hw]
      intro heq
      apply hc₀_not
      rw [heq]
      refine Finset.mem_image.mpr
        ⟨⟨w, (SimpleGraph.mem_neighborFinset G u w).mpr hadj⟩, Finset.mem_attach _ _, rfl⟩
    · by_cases hw : w = v₀
      · subst hw
        rw [dif_neg hu, dif_pos rfl]
        intro heq
        apply hc₀_not
        rw [← heq]
        refine Finset.mem_image.mpr
          ⟨⟨u, (SimpleGraph.mem_neighborFinset G w u).mpr hadj.symm⟩, Finset.mem_attach _ _, rfl⟩
      · rw [dif_neg hu, dif_neg hw]
        intro heq
        have hval : (cH ⟨u, hu⟩).val = (cH ⟨w, hw⟩).val :=
          congrArg (fun x : Fin (G.maxDegree + 1) => x.val) heq
        have hEq : cH ⟨u, hu⟩ = cH ⟨w, hw⟩ := Fin.ext hval
        exact cH.valid (show H.Adj ⟨u, hu⟩ ⟨w, hw⟩ from hadj) hEq

end ReedR1H1Proof

theorem OMA.solution :
    OMA.R_ReedOmegaDeltaChi_reed_omega_delta_chi_conjecture_for_finite_graphs_R1.H1 := by
  intro V _ _ G _ hle
  obtain ⟨col⟩ := ReedR1H1Proof.exists_coloring_maxDegree_succ (Fintype.card V) G rfl
  have hchi : G.chromaticNumber ≤ ((G.maxDegree + 1 : ℕ) : ℕ∞) :=
    SimpleGraph.Colorable.chromaticNumber_le ⟨col⟩
  have hle_enat : (G.maxDegree : ℕ∞) ≤ (G.cliqueNum : ℕ∞) := Nat.cast_le.mpr hle
  calc 2 * G.chromaticNumber
      ≤ 2 * ((G.maxDegree + 1 : ℕ) : ℕ∞) := by gcongr
    _ = (G.maxDegree : ℕ∞) + (G.maxDegree : ℕ∞) + 2 := by
        push_cast; ring
    _ ≤ (G.cliqueNum : ℕ∞) + (G.maxDegree : ℕ∞) + 2 := by
        gcongr
