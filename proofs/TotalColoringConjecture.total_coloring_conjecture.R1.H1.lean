import OMAReductions.R_TotalColoringConjecture_total_coloring_conjecture_R1

-- Step TotalColoringConjecture.total_coloring_conjecture.R1.H1: hypothesis H1 of reduction TotalColoringConjecture.total_coloring_conjecture.R1
-- Credit: @sntntHb

/-!
Graphs of maximum degree `Δ ≤ 1` have a total colouring with `Δ + 2` colours.

Number the vertices by `Fintype.equivFin`. A vertex gets colour `1` if it has a neighbour with a
smaller number and `0` otherwise; every edge gets colour `Δ + 1`.
* Adjacent `u, v` with `u` numbered lower: `v` sees `u`, while the only neighbour of `u` is `v`
  (degree at most 1), so the colours are `0` and `1`.
* Two different edges never share a vertex (that vertex would have two neighbours).
* A vertex on an edge forces `Δ ≥ 1`, so the edge colour `Δ + 1 ≥ 2` differs from `0` and `1`.
-/

namespace OMA.TotalH1

open SimpleGraph

lemma nbr_unique {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.maxDegree ≤ 1) {u v w : V} (hv : G.Adj u v) (hw : G.Adj u w) : v = w := by
  have hc : (G.neighborFinset u).card ≤ 1 := by
    rw [G.card_neighborFinset_eq_degree]; exact (G.degree_le_maxDegree u).trans h
  exact Finset.card_le_one.1 hc v ((G.mem_neighborFinset u v).2 hv) w
    ((G.mem_neighborFinset u w).2 hw)

lemma one_le_of_adj {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V} (hv : G.Adj u v) : 1 ≤ G.maxDegree := by
  have : 0 < G.degree u := by
    rw [← G.card_neighborFinset_eq_degree]
    exact Finset.card_pos.2 ⟨v, (G.mem_neighborFinset u v).2 hv⟩
  exact this.trans_le (G.degree_le_maxDegree u)

theorem colorable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.maxDegree ≤ 1) : G.TotalColorable (G.maxDegree + 2) := by
  classical
  let e := Fintype.equivFin V
  let f : V → ℕ := fun v => if ∃ w, G.Adj v w ∧ e w < e v then 1 else 0
  have hf : ∀ v, f v ≤ 1 := fun v => by simp only [f]; split_ifs <;> omega
  let c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2) := fun x =>
    match x with
    | Sum.inl v => ⟨f v, by have := hf v; omega⟩
    | Sum.inr _ => ⟨G.maxDegree + 1, by omega⟩
  refine ⟨c, ?_, ?_, ?_⟩
  · intro u v huv hc
    have hc' : f u = f v := by simpa [c] using congrArg Fin.val hc
    have hne : e u ≠ e v := fun h' => G.ne_of_adj huv (e.injective h')
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : f v = 1 := by
        simp only [f]; rw [if_pos ⟨u, huv.symm, hlt⟩]
      have h0 : f u = 0 := by
        simp only [f]; rw [if_neg]
        rintro ⟨w, huw, hw⟩
        have := nbr_unique G h huw huv; subst this; exact absurd hw (by omega)
      omega
    · have h1 : f u = 1 := by
        simp only [f]; rw [if_pos ⟨v, huv, hlt⟩]
      have h0 : f v = 0 := by
        simp only [f]; rw [if_neg]
        rintro ⟨w, hvw, hw⟩
        have := nbr_unique G h hvw huv.symm; subst this; exact absurd hw (by omega)
      omega
  · rintro ⟨s, hs⟩ ⟨t, ht⟩ hst ⟨v, hvs, hvt⟩
    exfalso
    apply hst
    induction s using Sym2.ind with
    | _ a b =>
    induction t using Sym2.ind with
    | _ a' b' =>
    rw [Subtype.mk.injEq]
    have hab : G.Adj a b := hs
    have hab' : G.Adj a' b' := ht
    rcases Sym2.mem_iff.1 hvs with rfl | rfl <;> rcases Sym2.mem_iff.1 hvt with rfl | rfl
    · rw [nbr_unique G h hab hab']
    · rw [nbr_unique G h hab hab'.symm, Sym2.eq_swap]
    · rw [nbr_unique G h hab.symm hab', Sym2.eq_swap]
    · rw [nbr_unique G h hab.symm hab'.symm]
  · rintro v ⟨s, hs⟩ hvs hc
    have hc' : f v = G.maxDegree + 1 := by simpa [c] using congrArg Fin.val hc
    have hadj : ∃ w, G.Adj v w := by
      induction s using Sym2.ind with
      | _ a b =>
      have hab : G.Adj a b := hs
      rcases Sym2.mem_iff.1 hvs with rfl | rfl
      · exact ⟨b, hab⟩
      · exact ⟨a, hab.symm⟩
    obtain ⟨w, hw⟩ := hadj
    have := one_le_of_adj G hw
    have := hf v
    omega

end OMA.TotalH1

theorem OMA.solution : OMA.R_TotalColoringConjecture_total_coloring_conjecture_R1.H1 := by
  intro V _ _ G _ h
  exact Nat.sInf_le (OMA.TotalH1.colorable G h)
