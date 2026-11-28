import OMAReductions.R_TotalColoringConjecture_total_coloring_conjecture_R1

-- Step TotalColoringConjecture.total_coloring_conjecture.R1.H1: hypothesis H1 of reduction TotalColoringConjecture.total_coloring_conjecture.R1
-- Credit: @Raimo33

namespace OMAE_TC
open SimpleGraph

theorem uniq {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.maxDegree ≤ 1) {v a b : V} (ha : G.Adj v a) (hb : G.Adj v b) : a = b := by
  have hd := G.degree_le_maxDegree v
  rw [← card_neighborFinset_eq_degree] at hd
  exact (Finset.card_le_one (s := G.neighborFinset v)).mp (by omega) a (by simpa using ha) b (by simpa using hb)

theorem colorable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.maxDegree ≤ 1) : G.TotalColorable (G.maxDegree + 2) := by
  classical
  let e := Fintype.equivFin V
  let c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2) := Sum.elim
    (fun v => if ∃ w, G.Adj v w ∧ e w < e v then ⟨1, by omega⟩ else ⟨0, by omega⟩)
    (fun _ => ⟨G.maxDegree + 1, by omega⟩)
  refine ⟨c, ?_, ?_, ?_⟩
  · intro u v huv hc
    have hne : e u ≠ e v := fun h' => G.ne_of_adj huv (e.injective h')
    rcases lt_or_gt_of_ne hne with hl | hl
    · have h1 : ∃ w, G.Adj v w ∧ e w < e v := ⟨u, huv.symm, hl⟩
      have h0 : ¬ ∃ w, G.Adj u w ∧ e w < e u := by
        rintro ⟨w, hw, hwl⟩
        have := uniq G h hw huv
        subst this; exact absurd hl (not_lt.mpr hwl.le)
      simp only [c, Sum.elim_inl, h1, h0, if_true, if_false] at hc
      exact absurd (congrArg Fin.val hc) (by simp)
    · have h1 : ∃ w, G.Adj u w ∧ e w < e u := ⟨v, huv, hl⟩
      have h0 : ¬ ∃ w, G.Adj v w ∧ e w < e v := by
        rintro ⟨w, hw, hwl⟩
        have := uniq G h hw huv.symm
        subst this; exact absurd hl (not_lt.mpr hwl.le)
      simp only [c, Sum.elim_inl, h1, h0, if_true, if_false] at hc
      exact absurd (congrArg Fin.val hc) (by simp)
  · rintro ⟨f1, hf1⟩ ⟨f2, hf2⟩ hne ⟨v, hv1, hv2⟩ -
    apply hne
    induction f1 using Sym2.ind with
    | h x y =>
    induction f2 using Sym2.ind with
    | h x' y' =>
    rw [mem_edgeSet] at hf1 hf2
    have k1 : ∃ a, G.Adj v a ∧ s(x, y) = s(v, a) := by
      rcases Sym2.mem_iff.mp hv1 with rfl | rfl
      · exact ⟨y, hf1, rfl⟩
      · exact ⟨x, hf1.symm, Sym2.eq_swap⟩
    have k2 : ∃ a, G.Adj v a ∧ s(x', y') = s(v, a) := by
      rcases Sym2.mem_iff.mp hv2 with rfl | rfl
      · exact ⟨y', hf2, rfl⟩
      · exact ⟨x', hf2.symm, Sym2.eq_swap⟩
    obtain ⟨a, ha, ea⟩ := k1
    obtain ⟨b, hb, eb⟩ := k2
    have := uniq G h ha hb
    subst this
    apply Subtype.ext
    simp only [ea, eb]
  · rintro v ⟨f, hf⟩ hv hc
    have hdeg : 1 ≤ G.maxDegree := by
      induction f using Sym2.ind with
      | h x y =>
      rw [mem_edgeSet] at hf
      have := G.degree_le_maxDegree x
      have : 0 < G.degree x := by
        rw [← card_neighborFinset_eq_degree]; exact Finset.card_pos.mpr ⟨y, by simpa using hf⟩
      omega
    have hv' := congrArg Fin.val hc
    simp only [c, Sum.elim_inl, Sum.elim_inr] at hv'
    by_cases hp : ∃ w, G.Adj v w ∧ e w < e v
    · simp only [hp, if_true] at hv'; omega
    · simp only [hp, if_false] at hv'; omega

end OMAE_TC

theorem OMA.solution : OMA.R_TotalColoringConjecture_total_coloring_conjecture_R1.H1 := by
  intro V _ _ G _ h
  exact Nat.sInf_le (OMAE_TC.colorable G h)
