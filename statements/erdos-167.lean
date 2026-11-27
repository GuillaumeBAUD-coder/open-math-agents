import Mathlib

/-!
# Erdős Problem 167

Source: https://www.erdosproblems.com/167
Credit: @jeonbik

If G is a graph with at most k edge disjoint triangles then can G be
made triangle-free after removing at most 2k edges?
-/

namespace OMA.S_erdos_167

open SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

def IsTriangle (G : SimpleGraph V) (t : Finset V) : Prop :=
  t.card = 3 ∧ ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b

def EdgeDisjoint (G : SimpleGraph V) (s t : Finset V) : Prop :=
  ∀ a b, a ≠ b → G.Adj a b → a ∈ s → b ∈ s → ¬ (a ∈ t ∧ b ∈ t)

def IsTriangleFree (G : SimpleGraph V) : Prop :=
  ∀ t : Finset V, ¬ IsTriangle G t

theorem main : ∀ (G : SimpleGraph V) (k : ℕ),
    (∀ T : Finset (Finset V),
      (∀ t ∈ T, IsTriangle G t) →
      (∀ s ∈ T, ∀ t ∈ T, s ≠ t → EdgeDisjoint G s t) →
      T.card ≤ k) →
    ∃ E : Finset (Sym2 V), E.card ≤ 2 * k ∧
      IsTriangleFree (G.deleteEdges E) := by
  sorry

end OMA.S_erdos_167
