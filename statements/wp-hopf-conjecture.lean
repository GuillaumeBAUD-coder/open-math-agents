import Mathlib

namespace OMA.S_wp_hopf_conjecture

open Manifold AlgebraicTopology
open scoped Manifold ContDiff BigOperators

abbrev Model (n : ℕ) := EuclideanSpace ℝ (Fin n)

abbrev SmoothMetric (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Model n) M] [IsManifold (𝓡 n) ∞ M] :=
  Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (Model n) (TangentSpace (𝓡 n) (M := M))

/-- Pull the tangent metric back by the inverse of a chart. -/
noncomputable def chartMetric {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Model n) M] [IsManifold (𝓡 n) ∞ M] (g : SmoothMetric n M) (p : M) (x : Model n) :
    Matrix (Fin n) (Fin n) ℝ :=
  let inv := (chartAt (Model n) p).symm
  let D := mfderiv (𝓡 n) (𝓡 n) inv x
  fun i j =>
    g.inner (inv x) (D (EuclideanSpace.single i 1)) (D (EuclideanSpace.single j 1))

noncomputable def coordinateDerivative {n : ℕ} (i : Fin n)
    (f : Model n → ℝ) (x : Model n) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- Christoffel symbols of the Levi-Civita connection in the chart. -/
noncomputable def christoffel {n : ℕ} (g : Model n → Matrix (Fin n) (Fin n) ℝ)
    (x : Model n) (a i j : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ b, ((g x)⁻¹) a b *
    (coordinateDerivative i (fun y => g y j b) x +
      coordinateDerivative j (fun y => g y i b) x -
      coordinateDerivative b (fun y => g y i j) x)

/-- The upper component a of the curvature of the coordinate triple i, j, k. -/
noncomputable def curvature {n : ℕ} (g : Model n → Matrix (Fin n) (Fin n) ℝ)
    (x : Model n) (a i j k : Fin n) : ℝ :=
  coordinateDerivative i (fun y => christoffel g y a j k) x -
    coordinateDerivative j (fun y => christoffel g y a i k) x +
    ∑ b, (christoffel g x a i b * christoffel g x b j k -
      christoffel g x a j b * christoffel g x b i k)

noncomputable def sectionalNumerator {n : ℕ}
    (g : Model n → Matrix (Fin n) (Fin n) ℝ) (x u v : Model n) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, u i * v j * v k * u b * g x a b * curvature g x a i j k

/-- The sectional curvature has the prescribed strict sign on every tangent plane. -/
def SectionalSign {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Model n) M]
    [IsManifold (𝓡 n) ∞ M] (g : SmoothMetric n M) (sgn : ℝ → Prop) : Prop :=
  ∀ p : M, ∀ x ∈ (chartAt (Model n) p).target, ∀ u v : Model n,
    LinearIndependent ℝ (![u, v] : Fin 2 → Model n) →
      sgn (sectionalNumerator (chartMetric g p) x u v)

/-- The Euler characteristic from rational singular homology. -/
noncomputable def eulerCharacteristic (n : ℕ) (M : Type) [TopologicalSpace M] : ℤ :=
  ∑ i ∈ Finset.range (n + 1),
    let H := ((singularHomologyFunctor (ModuleCat ℚ) i).obj (ModuleCat.of ℚ ℚ)).obj
      (TopCat.of M)
    (-1 : ℤ) ^ i * (Module.finrank ℚ H : ℤ)

/-- The positive and negative sectional curvature cases of Hopf's sign conjecture. -/
theorem main :
    ∀ (d : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      [CompactSpace M] [ConnectedSpace M] [ChartedSpace (Model (2 * d)) M]
      [IsManifold (𝓡 (2 * d)) ∞ M],
      0 < d → ∀ g : SmoothMetric (2 * d) M,
        let χ := eulerCharacteristic (2 * d) M
        (SectionalSign g (fun s => 0 < s) → 0 < χ) ∧
          (SectionalSign g (fun s => s < 0) → 0 < (-1 : ℤ) ^ d * χ) := by
  sorry

end OMA.S_wp_hopf_conjecture
