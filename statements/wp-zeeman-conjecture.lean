import Mathlib

namespace OMA.S_wp_zeeman_conjecture

abbrev Complex (n : ℕ) := PreAbstractSimplicialComplex (Fin n)
abbrev Coordinates (n : ℕ) := Fin n → ℝ

/-- Barycentric coordinates with all nonzero entries supported on one face. -/
def realization {n : ℕ} (K : Complex n) : Set (Coordinates n) :=
  {x ∈ stdSimplex ℝ (Fin n) | ∃ s ∈ K.faces, ∀ i, i ∉ s → x i = 0}

def prism {n : ℕ} (K : Complex n) : Set (Coordinates n × ℝ) :=
  realization K ×ˢ Set.Icc 0 1

/-- The face s is free and t is its only strict coface, of codimension one over s. -/
def ElementaryCollapse {n : ℕ} (K L : Complex n) : Prop :=
  ∃ s ∈ K.faces, ∃ t ∈ K.faces, s ⊂ t ∧ t.card = s.card + 1 ∧
    (∀ u ∈ K.faces, s ⊂ u → u = t) ∧ L.faces = K.faces \ {s, t}

/-- Affine on each of finitely many convex polytopes covering the domain. -/
def PiecewiseAffine {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (D : Set E) (f : D → F) : Prop :=
  ∃ (n : ℕ) (vertices : Fin n → Finset E) (piece : Fin n → E →ᵃ[ℝ] F),
    (⋃ i, convexHull ℝ (vertices i : Set E)) = D ∧
      ∀ i (x : D), x.val ∈ convexHull ℝ (vertices i : Set E) → f x = piece i x.val

/-- The polyhedral prism admits a triangulation that collapses to one vertex. -/
theorem main :
    ∀ (n : ℕ) (K : Complex n),
      (∀ s ∈ K.faces, s.card ≤ 3) → (∃ s ∈ K.faces, s.card = 3) →
      ContractibleSpace ↥(realization K) →
      ∃ (m : ℕ) (L P : Complex m) (e : ↥(realization L) ≃ₜ ↥(prism K)) (v : Fin m),
        PiecewiseAffine (realization L) (fun x => (e x).val) ∧
        PiecewiseAffine (prism K) (fun y => (e.symm y).val) ∧
        Relation.ReflTransGen ElementaryCollapse L P ∧ P.faces = {{v}} := by
  sorry

end OMA.S_wp_zeeman_conjecture
