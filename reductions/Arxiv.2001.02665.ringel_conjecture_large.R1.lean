import FormalConjectures.Arxiv.«2001.02665».RingelConjecture

-- Reduction Arxiv.2001.02665.ringel_conjecture_large.R1 of Ringel's conjecture for large n
-- Source: R. Montgomery, A. Pokrovskiy, B. Sudakov, A proof of Ringel's Conjecture,
--   Geom. Funct. Anal. 31 (2021), 663-720, arXiv:2001.02665, Theorem 2.1;
--   A. Rosa, On certain valuations of the vertices of a graph, Theory of Graphs (Rome 1966).
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Ringel's conjecture for large `n` from the rainbow tree theorem

The ND-colouring of `K_{2n+1}` on the vertex set `ZMod (2n+1)` colours the edge `xy` by the pair
`{x - y, y - x}` of its two differences (its 'distance'). A copy of a tree `T` is rainbow when no
two of its edges get the same colour. In terms of an embedding `g : V ↪ ZMod (2n+1)` this says:
if `ab` and `cd` are (oriented) edges of `T` with `g a - g b = g c - g d`, then `a = c` and
`b = d`. Such a `g` is exactly a rho-valuation of `T` in the sense of Rosa.

* `H1` (Montgomery-Pokrovskiy-Sudakov, Theorem 2.1 of arXiv:2001.02665): for all sufficiently
  large `n`, the ND-coloured `K_{2n+1}` contains a rainbow copy of every tree with `n` edges.
  This is the only deep input (absorption, the rainbow nibble and concentration inequalities).
* `H2` (Rosa, disjointness): the cyclic shifts `v ↦ g v + i` of a rainbow copy are pairwise
  edge-disjoint. Elementary: a common edge of shifts `i` and `j` gives two oriented edges of `T`
  with the same difference.
* `H3` (Rosa, covering): if `T` has `n` edges, the cyclic shifts of a rainbow copy cover
  `K_{2n+1}`. Elementary counting: the `2n` oriented edges have distinct nonzero differences, so
  every nonzero residue is a difference.

`main` transports the shifts from `ZMod (2n+1)` to `Fin (2n+1)` along `ZMod.finEquiv`.
-/

namespace OMA.R_Arxiv_2001_02665_ringel_conjecture_large_R1

open SimpleGraph

/-- Montgomery-Pokrovskiy-Sudakov: for large `n`, every tree with `n` edges has a rainbow copy
in the ND-coloured `K_{2n+1}`. -/
def H1 : Prop :=
  ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (V : Type) [Finite V] (T : SimpleGraph V),
    T.IsTree → T.edgeSet.ncard = n →
    ∃ g : V ↪ ZMod (2 * n + 1),
      ∀ a b c d, T.Adj a b → T.Adj c d → g a - g b = g c - g d → a = c ∧ b = d

/-- Rosa: the cyclic shifts of a rainbow copy are pairwise edge-disjoint. -/
def H2 : Prop :=
  ∀ (n : ℕ) (V : Type) [Finite V] (T : SimpleGraph V) (g : V ↪ ZMod (2 * n + 1)),
    (∀ a b c d, T.Adj a b → T.Adj c d → g a - g b = g c - g d → a = c ∧ b = d) →
    Pairwise (fun i j : ZMod (2 * n + 1) =>
      Disjoint (T.map (g.trans (Equiv.addRight i).toEmbedding)).edgeSet
        (T.map (g.trans (Equiv.addRight j).toEmbedding)).edgeSet)

/-- Rosa: the cyclic shifts of a rainbow copy of a graph with `n` edges cover `K_{2n+1}`. -/
def H3 : Prop :=
  ∀ (n : ℕ) (V : Type) [Finite V] (T : SimpleGraph V) (g : V ↪ ZMod (2 * n + 1)),
    T.edgeSet.ncard = n →
    (∀ a b c d, T.Adj a b → T.Adj c d → g a - g b = g c - g d → a = c ∧ b = d) →
    ⨆ i : ZMod (2 * n + 1), T.map (g.trans (Equiv.addRight i).toEmbedding) = ⊤

theorem main : H1 → H2 → H3 → type_of% @Arxiv.«2001.02665».ringel_conjecture_large := by
  intro h1 h2 h3
  filter_upwards [h1] with n hn
  intro V _ T hT hcard
  obtain ⟨g, hg⟩ := hn V T hT hcard
  let e : ZMod (2 * n + 1) ≃ Fin (2 * n + 1) := (ZMod.finEquiv (2 * n + 1)).symm.toEquiv
  refine ⟨fun i => (g.trans (Equiv.addRight (e.symm i)).toEmbedding).trans e.toEmbedding, ?_, ?_⟩
  · intro i j hij
    have hne : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    have hd := h2 n V T g hg hne
    have key : ∀ a : V ↪ ZMod (2 * n + 1), (T.map (a.trans e.toEmbedding)).edgeSet =
        e.toEmbedding.sym2Map '' (T.map a).edgeSet := by
      intro a
      rw [← SimpleGraph.edgeSet_map, SimpleGraph.map_map]
      rfl
    show Disjoint (T.map ((g.trans (Equiv.addRight (e.symm i)).toEmbedding).trans
      e.toEmbedding)).edgeSet (T.map ((g.trans (Equiv.addRight (e.symm j)).toEmbedding).trans
      e.toEmbedding)).edgeSet
    rw [key, key]
    exact (Set.disjoint_image_iff (Function.Embedding.injective _)).2 hd
  · have hc := h3 n V T g hcard hg
    ext x y
    simp only [SimpleGraph.iSup_adj, SimpleGraph.top_adj, SimpleGraph.map_adj]
    constructor
    · rintro ⟨i, u, v, huv, rfl, rfl⟩
      exact fun h => huv.ne
        (((g.trans (Equiv.addRight (e.symm i)).toEmbedding).trans e.toEmbedding).injective h)
    · intro hxy
      have hne : e.symm x ≠ e.symm y := fun h => hxy (e.symm.injective h)
      have hadj : (⨆ i : ZMod (2 * n + 1),
          T.map (g.trans (Equiv.addRight i).toEmbedding)).Adj (e.symm x) (e.symm y) := by
        rw [hc]; exact hne
      simp only [SimpleGraph.iSup_adj, SimpleGraph.map_adj] at hadj
      obtain ⟨i, u, v, huv, hu, hv⟩ := hadj
      refine ⟨e i, u, v, huv, ?_, ?_⟩
      · simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
          at hu ⊢
        rw [hu]; simp
      · simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
          at hv ⊢
        rw [hv]; simp

end OMA.R_Arxiv_2001_02665_ringel_conjecture_large_R1
