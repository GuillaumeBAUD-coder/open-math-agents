import OMAReductions.R_mse_1688329_R1

/-!
Step `mse-1688329.R1.H1`: the Erdos-Gyarfas conjecture for Dirac-dense graphs. If every vertex
has degree at least 3 and at least `n / 2`, the graph has a 4-cycle. Two distinct non-adjacent
vertices `u, w` have their neighbourhoods inside the `n - 2` other vertices, so by
inclusion-exclusion they share two neighbours `x ≠ y`, giving `u x w y u`. Otherwise the graph is
complete, and any vertex with three neighbours spans a 4-cycle with them.
-/

namespace OMA.EGDirac
open OMA.S_mse_1688329 SimpleGraph

variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

lemma four_cycle {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hda : G.Adj d a) (hac : a ≠ c) (hbd : b ≠ d) : HasPowerOfTwoCycle G := by
  refine ⟨a, .cons hab (.cons hbc (.cons hcd (.cons hda .nil))), 2, ?_, rfl⟩
  have hab' := hab.ne; have hbc' := hbc.ne; have hcd' := hcd.ne; have hda' := hda.ne
  rw [Walk.cons_isCycle_iff]
  refine ⟨?_, ?_⟩
  · simp only [Walk.isPath_def, Walk.support_cons, Walk.support_nil, List.nodup_cons,
      List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or]
    exact ⟨⟨hbc', hbd, hab'.symm⟩, ⟨hcd', hac.symm⟩, hda', not_false⟩
  · simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
    tauto

omit [DecidableEq V] in
theorem slice : OMA.R_mse_1688329_R1.H1 := by
  intro V _ _ _ G _ h3 hdir
  by_cases hc : ∃ u w, u ≠ w ∧ ¬ G.Adj u w
  · obtain ⟨u, w, huw, hnadj⟩ := hc
    have hsub : G.neighborFinset u ∪ G.neighborFinset w ⊆ (Finset.univ.erase u).erase w := by
      intro x hx
      simp only [Finset.mem_union, mem_neighborFinset] at hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      rcases hx with h | h
      · exact ⟨fun hxw => hnadj (hxw ▸ h), (G.ne_of_adj h).symm⟩
      · exact ⟨(G.ne_of_adj h).symm, fun hxu => hnadj (hxu ▸ h.symm)⟩
    have hcardU : ((Finset.univ.erase u).erase w).card = Fintype.card V - 2 := by
      rw [Finset.card_erase_of_mem (by simp [huw.symm]), Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ]
      omega
    have key := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset w)
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at key
    have hle := Finset.card_le_card hsub
    have hu := hdir u
    have hw := hdir w
    have hu3 := h3 u
    have h2 : 1 < (G.neighborFinset u ∩ G.neighborFinset w).card := by omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h2
    simp only [Finset.mem_inter, mem_neighborFinset] at hx hy
    exact four_cycle hx.1 hx.2.symm hy.2 hy.1.symm huw hxy
  · push_neg at hc
    obtain ⟨v⟩ := ‹Nonempty V›
    have h3v : 2 < (G.neighborFinset v).card := by
      rw [card_neighborFinset_eq_degree]; exact h3 v
    obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.mp h3v
    rw [mem_neighborFinset] at ha hb hc'
    exact four_cycle ha (hc a b hab) (hc b c hbc) hc'.symm (G.ne_of_adj hb) hac

end OMA.EGDirac

theorem OMA.solution : OMA.R_mse_1688329_R1.H1 :=
  OMA.EGDirac.slice
