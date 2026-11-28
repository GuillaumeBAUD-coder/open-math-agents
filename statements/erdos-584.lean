import Mathlib

/-!
# Erdős Problem 584

Source: https://www.erdosproblems.com/584
Credit: @willperacchio

The cycles witnessing each pair of distinct edges are taken inside the chosen
subgraph, as in Duke, Erdős, and Rödl's short-cycle results. We represent a
subgraph on the ambient vertex set by keeping any unused vertices isolated.
-/

open Filter

namespace OMA.S_erdos_584

def OnCycle {V : Type*} (G : SimpleGraph V) (allowedLength : ℕ → Prop)
    (e f : Sym2 V) : Prop :=
  ∃ (v : V) (p : G.Walk v v),
    p.IsCycle ∧ allowedLength p.length ∧ e ∈ p.edges ∧ f ∈ p.edges

def ShortCycles {V : Type*} (G : SimpleGraph V) (bound : ℕ) : Prop :=
  ∀ e ∈ G.edgeSet, ∀ f ∈ G.edgeSet, e ≠ f →
    OnCycle G (fun length => length ≤ bound) e f

def AdjacentEdgesOnFourCycles {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ e ∈ G.edgeSet, ∀ f ∈ G.edgeSet, e ≠ f →
    (∃ v : V, v ∈ e ∧ v ∈ f) → OnCycle G (fun length => length = 4) e f

/-- Both requested bounds use absolute constants. The density is the edge count divided by
the square of the number of vertices of the ambient graph. -/
theorem main :
    ∃ c₆ c₈ : ℝ, 0 < c₆ ∧ 0 < c₈ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        let δ : ℝ := (G.edgeSet.ncard : ℝ) / (n : ℝ) ^ 2
        (∃ H : SimpleGraph (Fin n), H ≤ G ∧
          c₆ * δ ^ 3 * (n : ℝ) ^ 2 ≤ (H.edgeSet.ncard : ℝ) ∧
          ShortCycles H 6 ∧ AdjacentEdgesOnFourCycles H) ∧
        (∃ H : SimpleGraph (Fin n), H ≤ G ∧
          c₈ * δ ^ 2 * (n : ℝ) ^ 2 ≤ (H.edgeSet.ncard : ℝ) ∧
          ShortCycles H 8) := by
  sorry

end OMA.S_erdos_584
