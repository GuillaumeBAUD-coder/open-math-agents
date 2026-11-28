import Mathlib

/-!
# Imbalance conjecture

Source: https://en.wikipedia.org/wiki/Imbalance_conjecture
Credit: @joshuadc11

For a finite simple graph `G`, the imbalance of an edge `e = {u, v}` is `|deg(u) - deg(v)|`.
If every edge of `G` has imbalance at least `1` (i.e. no edge connects vertices of equal degree),
then the multiset of all edge imbalances is graphic (i.e. is the degree multiset of some finite
simple graph `H`).

Formalization notes:
- `edgeImbalance G` lifts `fun u v => Nat.dist (G.degree u) (G.degree v)` to `Sym2 V`.
- The imbalance multiset is `G.edgeFinset.val.map (edgeImbalance G)`.
- Being graphic means there exists a simple graph `H` on `Fin G.edgeFinset.card` whose
  multiset of vertex degrees equals the imbalance multiset of `G`.
-/

namespace OMA.S_wp_imbalance_conjecture

/-- The imbalance `|deg(u) - deg(v)|` of an unordered pair `{u, v}` in `G`. -/
def edgeImbalance {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Sym2 V → ℕ :=
  Sym2.lift ⟨fun u v => Nat.dist (G.degree u) (G.degree v),
    fun u v => Nat.dist_comm (G.degree u) (G.degree v)⟩

theorem main :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ u v : V, G.Adj u v → G.degree u ≠ G.degree v) →
      ∃ (H : SimpleGraph (Fin G.edgeFinset.card)) (_ : DecidableRel H.Adj),
        (Finset.univ : Finset (Fin G.edgeFinset.card)).val.map (fun v => H.degree v) =
          G.edgeFinset.val.map (edgeImbalance G) := by
  sorry

end OMA.S_wp_imbalance_conjecture
