import Mathlib

/-!
# Erdős Problem 62

Source: https://www.erdosproblems.com/62
Credit: @Moti1125

If `G₁, G₂` are two graphs with chromatic number `ℵ₁`, must there exist a graph `G` whose
chromatic number is `4` (or even `ℵ₀`) which is a subgraph of both `G₁` and `G₂`?

We state the affirmative answer to the question with chromatic number `4`.

Conventions:
- Graphs may be infinite, so the chromatic number is the cardinal `chromaticCardinal`: the
  least cardinality of a colour type admitting a proper colouring (as in Formal Conjectures,
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`). Mathlib's
  `chromaticNumber` takes values in `ℕ∞` and cannot express `ℵ₁`.
- "Subgraph" means a not necessarily induced copy: `G.IsContained G₁` (`SimpleGraph.IsContained`,
  an injective graph homomorphism).
- Vertex types live in `Type`.
- The stronger variant "(or even `ℵ₀`)" is not stated. It implies the stated one, because a
  graph of chromatic number `ℵ₀` contains a finite subgraph of chromatic number `4`.
-/

namespace OMA.S_erdos_62

open Cardinal

/-- The chromatic number of a possibly infinite graph, as a cardinal: the least cardinality of a
type of colours admitting a proper colouring. -/
noncomputable def chromaticCardinal {V : Type} (G : SimpleGraph V) : Cardinal.{0} :=
  sInf {κ : Cardinal.{0} | ∃ (C : Type) (_ : Cardinal.mk C = κ), Nonempty (G.Coloring C)}

theorem main :
    ∀ (V₁ V₂ : Type) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
      chromaticCardinal G₁ = ℵ_ 1 → chromaticCardinal G₂ = ℵ_ 1 →
        ∃ (W : Type) (G : SimpleGraph W), chromaticCardinal G = 4 ∧ G.IsContained G₁ ∧ G.IsContained G₂ := by
  sorry

end OMA.S_erdos_62
