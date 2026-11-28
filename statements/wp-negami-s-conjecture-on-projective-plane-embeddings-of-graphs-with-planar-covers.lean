import Mathlib

namespace OMA.S_wp_negami_s_conjecture_on_projective_plane_embeddings_of_graphs_with_planar_covers

open Set

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Sphere := Metric.sphere (0 : Space) 1

/-- Antipodal identification of points of the sphere. -/
def antipodal : Setoid Sphere where
  r x y := (x : Space) = y ∨ (x : Space) = -(y : Space)
  iseqv := by
    constructor
    · intro x
      exact Or.inl rfl
    · intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, neg_neg])
    · intro x y z h k
      rcases h with h | h <;> rcases k with k | k
      · exact Or.inl (h.trans k)
      · exact Or.inr (h.trans k)
      · exact Or.inr (by rw [h, k])
      · exact Or.inl (by rw [h, k, neg_neg])

abbrev ProjectivePlane := Quotient antipodal
abbrev Interval := Icc (0 : ℝ) 1
def leftEnd : Interval := ⟨0, by norm_num⟩
def rightEnd : Interval := ⟨1, by norm_num⟩

/-- A graph drawing by embedded arcs meeting only at their common endpoints. -/
def Embeds {V X : Type*} [TopologicalSpace X] (G : SimpleGraph V) : Prop :=
  ∃ p : V ↪ X, ∃ arc : G.edgeSet → Interval → X,
    (∀ e,
      Continuous (arc e) ∧ Function.Injective (arc e) ∧
      ({arc e leftEnd, arc e rightEnd} : Set X) = p '' {v : V | v ∈ e.val} ∧
      range (arc e) ∩ range p ⊆ p '' {v : V | v ∈ e.val}) ∧
    ∀ e f, e ≠ f →
      range (arc e) ∩ range (arc f) ⊆ p '' {v : V | v ∈ e.val ∧ v ∈ f.val}

/-- A finite planar graph with a surjective projection bijective on neighbors. -/
def HasFinitePlanarCover {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (W : Type) (_ : Finite W) (H : SimpleGraph W) (p : W → V),
    Embeds (X := EuclideanSpace ℝ (Fin 2)) H ∧ Function.Surjective p ∧
      ∀ w, BijOn p (H.neighborSet w) (G.neighborSet (p w))

/-- Negami's planar cover conjecture. -/
theorem main :
    ∀ (V : Type) [Finite V] (G : SimpleGraph V), G.Connected →
      (HasFinitePlanarCover G ↔ Embeds (X := ProjectivePlane) G) := by
  sorry

end OMA.S_wp_negami_s_conjecture_on_projective_plane_embeddings_of_graphs_with_planar_covers
