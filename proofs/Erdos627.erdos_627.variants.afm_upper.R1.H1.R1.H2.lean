import OMAReductions.R_Erdos627_erdos_627_variants_afm_upper_R1_H1_R1

/-!
Classical Erdős–Szekeres Pascal upper bound and Ramsey vertex bracket for the
clique and independence numbers of a finite graph.
-/

namespace OMA.Erdos627RamseyBracket

open SimpleGraph Combinatorics.Diagonal

private theorem ramsey_choose_succ (s t : ℕ) :
    HasRamseyProperty ((s + t).choose s) (s + 1) (t + 1) := by
  induction s generalizing t with
  | zero =>
    rw [Nat.choose_zero_right]
    exact hasRamseyProperty_one_left (t + 1)
  | succ s ihs =>
    induction t with
    | zero =>
      rw [Nat.add_zero, Nat.choose_self]
      exact hasRamseyProperty_one_right (s + 2)
    | succ t iht =>
      have hs : HasRamseyProperty ((s + (t + 1)).choose s) (s + 1) (t + 2) := ihs (t + 1)
      have hpos : 1 ≤ (s + (t + 1)).choose s := Nat.choose_pos (by omega)
      have hp : ((s + 1) + (t + 1)).choose (s + 1) =
          (s + (t + 1)).choose s + ((s + 1) + t).choose (s + 1) := by
        rw [show (s + 1) + (t + 1) = (s + (t + 1)) + 1 by omega, Nat.choose_succ_succ]
        rw [show s + (t + 1) = (s + 1) + t by omega]
      rw [hp]
      intro m c V hV
      exact HasRamseyProperty.step hs iht hpos c V hV

private theorem indep_of_choose_le
    {n s t : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hclique : G.cliqueNum ≤ s)
    (hn : (s + t).choose s ≤ S.card) :
    ∃ T ⊆ S, T.card = t + 1 ∧ G.IsIndepSet (T : Set (Fin n)) := by
  classical
  let c (e : Finset (Fin n)) : Bool := decide (¬ G.IsClique (e : Set (Fin n)))
  obtain ⟨T, _, hT, hmono⟩ | ⟨T, hTS, hT, hmono⟩ := ramsey_choose_succ s t c S hn
  · have hTc : G.IsClique (T : Set (Fin n)) := by
      intro x hx y hy hxy
      have h := hmono {x, y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
        (by simp [hxy])
      simpa [c, SimpleGraph.isClique_pair, hxy] using h
    have hle := hTc.card_le_cliqueNum
    omega
  · refine ⟨T, hTS, hT, ?_⟩
    intro x hx y hy hxy
    have h := hmono {x, y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
      (by simp [hxy])
    simpa [c, SimpleGraph.isClique_pair, hxy] using h

private lemma choose_mem_ramsey_set (w t : ℕ) :
    (w + t).choose w ∈ {m : ℕ | ∀ H : SimpleGraph (Fin m),
      (completeGraph (Fin (w + 1))).IsContained H ∨
      (completeGraph (Fin (t + 1))).IsContained Hᶜ} := by
  classical
  intro H
  by_cases h : H.cliqueNum ≤ w
  · right
    obtain ⟨T, _, hc, hi⟩ := indep_of_choose_le (t := t) H Finset.univ h (by simp)
    exact (Hᶜ.not_cliqueFree_iff_top_isContained _).mp
      (IsNClique.not_cliqueFree ⟨(H.isClique_compl).mpr hi, hc⟩)
  · left
    obtain ⟨T, hT⟩ := H.exists_isNClique_cliqueNum
    apply (H.not_cliqueFree_iff_top_isContained _).mp
    exact fun hf => hT.not_cliqueFree (CliqueFree.mono (by omega) hf)

private theorem classicalRamsey_le_choose (w t : ℕ) :
    classicalRamsey (w + 1) (t + 1) ≤ (w + t).choose w :=
  Nat.sInf_le (choose_mem_ramsey_set w t)

private theorem indep_of_classicalRamsey_le
    {n w t : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hw : G.cliqueNum ≤ w) (hs : classicalRamsey (w + 1) (t + 1) ≤ S.card) :
    ∃ T ⊆ S, T.card = t + 1 ∧ G.IsIndepSet (T : Set (Fin n)) := by
  classical
  let good := {m : ℕ | ∀ H : SimpleGraph (Fin m),
    (completeGraph (Fin (w + 1))).IsContained H ∨
    (completeGraph (Fin (t + 1))).IsContained Hᶜ}
  have hex : good.Nonempty := ⟨(w + t).choose w, choose_mem_ramsey_set w t⟩
  let R := classicalRamsey (w + 1) (t + 1)
  have hr : R ∈ good := Nat.sInf_mem hex
  let i : Fin R ↪ Fin n := ((Fin.castLEEmb hs).trans S.equivFin.symm.toEmbedding).trans
    (Function.Embedding.subtype (· ∈ S))
  have hi (v : Fin R) : i v ∈ S := (S.equivFin.symm ((Fin.castLEEmb hs) v)).property
  let H := G.comap i
  rcases hr H with h | h
  · have hn := h.not_cliqueFree
    unfold CliqueFree at hn
    obtain ⟨U, hU⟩ := not_forall_not.mp hn
    have hc : G.IsClique ((U.map i : Finset (Fin n)) : Set (Fin n)) := by
      intro a ha b hb hab
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
      exact hU.isClique hx hy (fun e => hab (congrArg i e))
    have hbad := hc.card_le_cliqueNum
    rw [Finset.card_map, hU.card_eq] at hbad
    omega
  · have hn := h.not_cliqueFree
    unfold CliqueFree at hn
    obtain ⟨U, hU⟩ := not_forall_not.mp hn
    refine ⟨U.map i, ?_, by simpa using hU.card_eq, ?_⟩
    · intro a ha
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp ha
      exact hi x
    · intro a ha b hb hab
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
      exact (H.isClique_compl.mp hU.isClique) hx hy (fun e => hab (congrArg i e))

end OMA.Erdos627RamseyBracket

theorem OMA.solution : OMA.R_Erdos627_erdos_627_variants_afm_upper_R1_H1_R1.H2 := by
  intro n G
  refine ⟨?_, OMA.Erdos627RamseyBracket.classicalRamsey_le_choose G.cliqueNum G.indepNum⟩
  by_contra! hle
  obtain ⟨T, _, hcard, hI⟩ := OMA.Erdos627RamseyBracket.indep_of_classicalRamsey_le
    G Finset.univ le_rfl (by simpa using hle)
  have hbad := (G.isClique_compl.mpr hI).card_le_cliqueNum
  rw [SimpleGraph.cliqueNum_compl] at hbad
  omega
