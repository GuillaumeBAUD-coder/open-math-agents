import Mathlib

namespace OMA.S_wp_chern_s_conjecture_affine_geometry

open AlgebraicTopology
open scoped BigOperators

abbrev Model (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The chosen charts cover the space, and each change of coordinates is
locally the restriction of an invertible affine map. -/
def AffineTransitions (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Model n) M] : Prop :=
  ∀ p q : M,
    let e := (chartAt (Model n) p).symm.trans (chartAt (Model n) q)
    ∀ x ∈ e.source,
      ∃ U : Set (Model n), IsOpen U ∧ x ∈ U ∧ U ⊆ e.source ∧
        ∃ a : Model n ≃ᵃ[ℝ] Model n, Set.EqOn e a U

/-- The Euler characteristic from rational singular homology through dimension n. -/
noncomputable def eulerCharacteristic (n : ℕ) (M : Type) [TopologicalSpace M] : ℤ :=
  ∑ i ∈ Finset.range (n + 1),
    let H := ((singularHomologyFunctor (ModuleCat ℚ) i).obj (ModuleCat.of ℚ ℚ)).obj
      (TopCat.of M)
    (-1 : ℤ) ^ i * (Module.finrank ℚ H : ℤ)

/-- Chern's conjecture for closed affine manifolds of positive dimension. -/
theorem main :
    ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      [CompactSpace M] [ConnectedSpace M] [ChartedSpace (Model n) M],
      0 < n → AffineTransitions n M → eulerCharacteristic n M = 0 := by
  sorry

end OMA.S_wp_chern_s_conjecture_affine_geometry
