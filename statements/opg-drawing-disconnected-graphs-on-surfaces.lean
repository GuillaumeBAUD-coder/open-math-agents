import Mathlib

namespace OMA.S_opg_drawing_disconnected_graphs_on_surfaces

abbrev Plane := EuclideanSpace ℝ (Fin 2)

structure Surface where
  space : TopCat
  hausdorff : T2Space space
  secondCountable : SecondCountableTopology space
  connected : ConnectedSpace space
  charts : ChartedSpace Plane space

/-- Increasing endpoints give one index for each simple undirected edge. -/
abbrev Edge {n : ℕ} (G : SimpleGraph (Fin n)) :=
  { p : Fin n × Fin n // p.1 < p.2 ∧ G.Adj p.1 p.2 }

structure Drawing {n : ℕ} (G : SimpleGraph (Fin n)) (S : TopCat) where
  vertex : Fin n ↪ S
  arc : ∀ e : Edge G, Path (vertex e.1.1) (vertex e.1.2)
  arc_injective : ∀ e, Function.Injective (arc e)
  vertex_on_arc : ∀ v e t, vertex v = arc e t → v = e.1.1 ∨ v = e.1.2

def Drawing.edgeImage {n : ℕ} {G : SimpleGraph (Fin n)} {S : TopCat}
    (D : Drawing G S) (e : Edge G) : Set S :=
  Set.range (D.arc e)

def Drawing.crossings {n : ℕ} {G : SimpleGraph (Fin n)} {S : TopCat}
    (D : Drawing G S) : Set S :=
  {x | x ∉ Set.range D.vertex ∧ ∃ e f : Edge G, e ≠ f ∧
    x ∈ D.edgeImage e ∧ x ∈ D.edgeImage f}

/-- The general-position restrictions from the source. -/
def Drawing.IsProper {n : ℕ} {G : SimpleGraph (Fin n)} {S : TopCat}
    (D : Drawing G S) : Prop :=
  D.crossings.Finite ∧
    ∀ (x : S) (e f : Edge G), x ∉ Set.range D.vertex → e ≠ f →
      x ∈ D.edgeImage e → x ∈ D.edgeImage f →
      Disjoint ({e.1.1, e.1.2} : Set (Fin n)) {f.1.1, f.1.2} ∧
        (∀ y : S, y ∉ Set.range D.vertex →
          y ∈ D.edgeImage e → y ∈ D.edgeImage f → y = x) ∧
        (∀ g : Edge G, x ∈ D.edgeImage g → g = e ∨ g = f) ∧
        ∃ h : OpenPartialHomeomorph S Plane, x ∈ h.source ∧ h x = 0 ∧
          h '' (D.edgeImage e ∩ h.source) = {y ∈ h.target | y 0 = 0} ∧
          h '' (D.edgeImage f ∩ h.source) = {y ∈ h.target | y 1 = 0}

/-- All vertex points and edge arcs belonging to one part of the disjoint union. -/
def Drawing.partImage {n : ℕ} {G : SimpleGraph (Fin n)} {S : TopCat}
    (D : Drawing G S) (part : Fin n → Bool) (side : Bool) : Set S :=
  (D.vertex '' {v | part v = side}) ∪
    {x | ∃ e : Edge G, part e.1.1 = side ∧ x ∈ D.edgeImage e}

/-- In every minimum-crossing drawing of a disjoint union, the two parts are disjoint. -/
theorem main :
    ∀ (S : Surface) (n : ℕ) (G : SimpleGraph (Fin n)) (part : Fin n → Bool),
      (∀ u v, G.Adj u v → part u = part v) →
      ∀ D : Drawing G S.space, D.IsProper →
        (∀ D' : Drawing G S.space, D'.IsProper →
          D.crossings.ncard ≤ D'.crossings.ncard) →
        Disjoint (D.partImage part false) (D.partImage part true) := by
  sorry

end OMA.S_opg_drawing_disconnected_graphs_on_surfaces
