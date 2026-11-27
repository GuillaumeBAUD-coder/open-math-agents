import FormalConjectures.WrittenOnTheWallII.GraphConjecture84

-- Reduction WrittenOnTheWallII.GraphConjecture84.conjecture84.R1 of Written on the Wall II - Conjecture 84
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Split by the minimum degree

The target is the claim for every connected graph with positive minimum degree.
We split on the minimum degree.

* `H1` is the leaf case, minimum degree one. Here the claim reads `2 rad ≤ tree`.
  This case is open. Exhaustive search finds no counterexample up to 12 vertices.
* `H2` is the case of minimum degree at least two. Here `2 rad / δ ≤ rad`, and a
  shortest path between two vertices at distance `diam ≥ rad` induces a tree on
  `diam + 1` vertices. So `H2` has a short proof.
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1

open SimpleGraph

/-- The leaf case: the claim for connected graphs with minimum degree one. -/
def H1 : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α)
    [DecidableRel G.Adj], G.Connected → 0 < G.minDegree → G.minDegree = 1 →
    2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (largestInducedTreeSize G : ℝ)

/-- The case of minimum degree at least two. -/
def H2 : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α)
    [DecidableRel G.Adj], G.Connected → 0 < G.minDegree → 2 ≤ G.minDegree →
    2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (largestInducedTreeSize G : ℝ)

section transfer

variable {V W : Type*} {G : SimpleGraph V} {K : SimpleGraph W}

lemma edist_hom_le (f : G →g K) (u v : V) : K.edist (f u) (f v) ≤ G.edist u v := by
  by_cases h : G.Reachable u v
  · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_edist
    rw [← hp]
    calc K.edist (f u) (f v) ≤ ((p.map f).length : ℕ∞) := SimpleGraph.edist_le _
      _ = (p.length : ℕ∞) := by simp
  · rw [edist_eq_top_of_not_reachable h]
    exact le_top

lemma edist_iso (e : G ≃g K) (u v : V) : K.edist (e u) (e v) = G.edist u v := by
  apply le_antisymm (edist_hom_le e.toHom u v)
  have := edist_hom_le e.symm.toHom (e u) (e v)
  simpa using this

lemma eccent_iso (e : G ≃g K) (u : V) : K.eccent (e u) = G.eccent u := by
  rw [eccent_def, eccent_def]
  simp only
  rw [← e.surjective.iSup_comp]
  simp only [edist_iso]

lemma radius_iso (e : G ≃g K) : K.radius = G.radius := by
  rw [radius_eq_iInf_iSup_edist, radius_eq_iInf_iSup_edist, ← e.surjective.iInf_comp]
  congr 1
  funext u
  rw [← e.surjective.iSup_comp]
  simp only [edist_iso]

lemma tree_iso_le [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] (e : G ≃g K) :
    largestInducedTreeSize K ≤ largestInducedTreeSize G := by
  unfold largestInducedTreeSize
  apply csSup_le'
  rintro n ⟨t, rfl, ht⟩
  let s : Finset V := t.map e.symm.toEquiv.toEmbedding
  have hbij : Set.BijOn e (s : Set V) (t : Set W) := by
    refine ⟨?_, e.injective.injOn, ?_⟩
    · intro x hx
      simp only [s, Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa using hy
    · intro y hy
      refine ⟨e.symm y, ?_, by simp⟩
      simp only [s, Finset.coe_map, Set.mem_image, Finset.mem_coe]
      exact ⟨y, hy, rfl⟩
  have hs : (G.induce (s : Set V)).IsTree := (Iso.induce e hbij).isTree_iff.mpr ht
  have hcard : s.card = t.card := by simp [s]
  have := card_le_largestInducedTreeSize hs
  unfold largestInducedTreeSize at this
  omega

end transfer

theorem main : H1 → H2 → type_of% @WrittenOnTheWallII.GraphConjecture84.conjecture84 := by
  intro h1 h2 α _ _ _ G _ hc hδ
  classical
  let e := Fintype.equivFin α
  let K : SimpleGraph (Fin (Fintype.card α)) := G.map e.toEmbedding
  let i : G ≃g K := SimpleGraph.Iso.map e G
  have : Nontrivial (Fin (Fintype.card α)) :=
    Fin.nontrivial_iff_two_le.mpr Fintype.one_lt_card
  have hc' : K.Connected := i.connected_iff.mp hc
  have hmin : G.minDegree = K.minDegree := i.minDegree_eq
  have hrad : K.radius = G.radius := radius_iso i
  have htree : largestInducedTreeSize K ≤ largestInducedTreeSize G := tree_iso_le i
  have hδ' : 0 < K.minDegree := hmin ▸ hδ
  have key : 2 * (K.radius.toNat : ℝ) / (K.minDegree : ℝ) ≤ (largestInducedTreeSize K : ℝ) := by
    rcases Nat.lt_or_ge K.minDegree 2 with hlt | hge
    · exact h1 _ K hc' hδ' (by omega)
    · exact h2 _ K hc' hδ' hge
  rw [hmin, ← hrad]
  exact key.trans (by exact_mod_cast htree)

end OMA.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1
