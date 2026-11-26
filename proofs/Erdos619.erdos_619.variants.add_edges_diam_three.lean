import FormalConjectures.ErdosProblems.«619»

-- Problem: Erdős Problem 619 — add edges diam three
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/619.lean:88 (declaration Erdos619.erdos_619.variants.add_edges_diam_three)
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: a maximal triangle-free supergraph has diameter at most 2.

open SimpleGraph

namespace OMA

universe u

/-- `H` with the extra edge `uv`. -/
def addEdge {V : Type u} (H : SimpleGraph V) (u v : V) (huv : u ≠ v) : SimpleGraph V where
  Adj x y := H.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)
  symm := ⟨fun x y h => by
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)⟩
  loopless := ⟨fun x h => by
    rcases h with h | h | h
    · exact H.loopless.irrefl x h
    · exact huv (h.1.symm.trans h.2)
    · exact huv (h.2.symm.trans h.1)⟩

theorem addEdge_adj {V : Type u} (H : SimpleGraph V) (u v : V) (huv : u ≠ v) (x y : V) :
    (addEdge H u v huv).Adj x y ↔ H.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := Iff.rfl

/-- If the edge `xy` is the new edge and `z` is adjacent to both in the new graph,
then `z` is a common neighbour in the old graph. -/
theorem common {V : Type u} (H : SimpleGraph V) (u v : V) (huv : u ≠ v) (x y z : V)
    (hxy : (x = u ∧ y = v) ∨ (x = v ∧ y = u))
    (hxz : (addEdge H u v huv).Adj x z) (hyz : (addEdge H u v huv).Adj y z) :
    ∃ w, H.Adj u w ∧ H.Adj w v := by
  have nxz : x ≠ z := (addEdge H u v huv).ne_of_adj hxz
  have nyz : y ≠ z := (addEdge H u v huv).ne_of_adj hyz
  rw [addEdge_adj] at hxz hyz
  have hxz' : H.Adj x z := by
    rcases hxz with h | h | h
    · exact h
    · rcases hxy with h' | h'
      · exact absurd (h'.2.trans h.2.symm) nyz
      · exact absurd (h'.1.symm.trans h.1) huv.symm
    · rcases hxy with h' | h'
      · exact absurd (h'.1.symm.trans h.1) huv
      · exact absurd (h'.2.trans h.2.symm) nyz
  have hyz' : H.Adj y z := by
    rcases hyz with h | h | h
    · exact h
    · rcases hxy with h' | h'
      · exact absurd (h'.2.symm.trans h.1) huv.symm
      · exact absurd (h'.1.trans h.2.symm) nxz
    · rcases hxy with h' | h'
      · exact absurd (h'.1.trans h.2.symm) nxz
      · exact absurd (h'.2.symm.trans h.1) huv
  rcases hxy with h' | h'
  · exact ⟨z, h'.1 ▸ hxz', (h'.2 ▸ hyz').symm⟩
  · exact ⟨z, h'.2 ▸ hyz', (h'.1 ▸ hxz').symm⟩

theorem exists_common {V : Type u} (H : SimpleGraph V) (hH : H.CliqueFree 3)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → K.CliqueFree 3 → K ≤ H)
    (u v : V) (huv : u ≠ v) (hnadj : ¬ H.Adj u v) : ∃ w, H.Adj u w ∧ H.Adj w v := by
  classical
  have hle : H ≤ addEdge H u v huv := fun x y h => Or.inl h
  have hnot : ¬ (addEdge H u v huv).CliqueFree 3 := by
    intro hcf
    have := hmax _ hle hcf
    exact hnadj (this (show (addEdge H u v huv).Adj u v from Or.inr (Or.inl ⟨rfl, rfl⟩)))
  unfold CliqueFree at hnot
  push Not at hnot
  obtain ⟨t, ht⟩ := hnot
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.mp ht
  rcases (addEdge_adj H u v huv a b).mp hab with h1 | h1
  · rcases (addEdge_adj H u v huv a c).mp hac with h2 | h2
    · rcases (addEdge_adj H u v huv b c).mp hbc with h3 | h3
      · exact absurd (is3Clique_triple_iff.mpr ⟨h1, h2, h3⟩) (hH {a, b, c})
      · exact common H u v huv b c a h3 hab.symm hac.symm
    · exact common H u v huv a c b h2 hab hbc.symm
  · exact common H u v huv a b c h1 hac hbc

end OMA

theorem OMA.solution : type_of% @Erdos619.erdos_619.variants.add_edges_diam_three := by
  intro V _ G hG hG'
  classical
  have hfin : {H : SimpleGraph V | G ≤ H ∧ H.CliqueFree 3}.Finite := Set.toFinite _
  obtain ⟨H, hGH, hmax⟩ := hfin.exists_le_maximal (show G ∈ _ from ⟨le_refl G, hG'⟩)
  refine ⟨H, hGH, hmax.1.2, ?_⟩
  rw [ediam_le_iff]
  intro u v
  by_cases huv : u = v
  · subst huv
    rw [edist_self]
    exact bot_le
  by_cases hadj : H.Adj u v
  · rw [edist_eq_one_iff_adj.mpr hadj]
    norm_num
  · obtain ⟨w, h1, h2⟩ := OMA.exists_common H hmax.1.2
      (fun K hHK hK => hmax.2 ⟨hGH.trans hHK, hK⟩ hHK) u v huv hadj
    calc H.edist u v ≤ H.edist u w + H.edist w v := SimpleGraph.edist_triangle
      _ = 1 + 1 := by rw [edist_eq_one_iff_adj.mpr h1, edist_eq_one_iff_adj.mpr h2]
      _ ≤ 3 := by norm_num
