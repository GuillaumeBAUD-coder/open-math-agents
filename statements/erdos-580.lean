import Mathlib

/-!
# Erdős Problem 580

Source: https://www.erdosproblems.com/580
Credit: @jeonbik

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_erdos_580

/-- `G` contains `T` as a (not necessarily induced) subgraph: there is an
injective map of the vertices of `T` into the vertices of `G` sending every
edge of `T` to an edge of `G`. -/
def ContainsSubgraph {V W : Type} (G : SimpleGraph V) (T : SimpleGraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ {u v}, T.Adj u v → G.Adj (f u) (f v)

theorem main : ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V),
    Fintype.card V = n →
    2 * (Finset.univ.filter (fun v => 2 * (G.neighborSet v).ncard ≥ n)).card ≥ n →
    ∀ (m : ℕ), 2 * m ≤ n →
    ∀ (W : Type) [Fintype W] (T : SimpleGraph W),
    T.IsTree → Fintype.card W = m → ContainsSubgraph G T := by
  sorry

end OMA.S_erdos_580
