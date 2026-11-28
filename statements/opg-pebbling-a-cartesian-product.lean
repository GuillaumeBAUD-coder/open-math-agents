import Mathlib

/-!
# Pebbling a cartesian product (Graham's conjecture)

Source: https://www.openproblemgarden.org/op/pebbling_a_cartesian_product

The pebbling number p(G) of a graph G is the smallest integer k so that however k pebbles
are distributed onto the vertices of G, it is possible to move a pebble to any vertex by a
sequence of steps, where in each step we remove two pebbles from one vertex and then place
one on an adjacent vertex. G₁ □ G₂ is the cartesian product.

Conjecture (Graham). p(G₁ □ G₂) ≤ p(G₁) p(G₂).

Conventions:
* G₁, G₂ are finite connected simple graphs (Graham's conjecture as stated by Chung,
  J. Graph Theory 1989, cited on the page, is for connected graphs; for disconnected
  graphs no k works).
* A distribution is `D : V → ℕ`; it has k pebbles when `∑ v, D v = k`.
* A pebbling step `PebbleStep G D D'`: for some edge uv of G with D u ≥ 2,
  D' is D with two pebbles removed from u and one added at v.
* move a pebble to any vertex: for each target r there is a finite sequence of steps
  (`Relation.ReflTransGen`) ending in a distribution with at least one pebble on r.
  The target is fixed before the moves are chosen, as in the definition on the page.
* `pebblingNumber G` is the least k such that every distribution of exactly k pebbles is
  solvable for every target (`sInf` over ℕ). For a finite connected graph this set is
  nonempty (any k ≥ 2^(diameter) · |V| works), so the infimum is a genuine minimum.
* The cartesian product is Mathlib's `G₁ □ G₂` (`SimpleGraph.boxProd`), which is exactly
  the product described on the page.
-/

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

namespace OMA.S_opg_pebbling_a_cartesian_product

/-- One pebbling step: remove two pebbles from `u` and add one at a neighbour `v`. -/
def PebbleStep {V : Type} [DecidableEq V] (G : SimpleGraph V) (D D' : V → ℕ) : Prop :=
  ∃ u v : V, G.Adj u v ∧ 2 ≤ D u ∧
    D' = Function.update (Function.update D u (D u - 2)) v (D v + 1)

/-- Every distribution of exactly `k` pebbles can move a pebble to any chosen vertex. -/
def Solvable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ D : V → ℕ, ∑ v, D v = k → ∀ r : V,
    ∃ D' : V → ℕ, Relation.ReflTransGen (PebbleStep G) D D' ∧ 1 ≤ D' r

/-- The pebbling number p(G). -/
noncomputable def pebblingNumber {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | Solvable G k}

theorem main :
    ∀ (V W : Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      (G₁ : SimpleGraph V) (G₂ : SimpleGraph W),
      G₁.Connected → G₂.Connected →
      pebblingNumber (G₁ □ G₂) ≤ pebblingNumber G₁ * pebblingNumber G₂ := by
  sorry

end OMA.S_opg_pebbling_a_cartesian_product
