import Mathlib

namespace OMA.S_wp_osserman_conjecture

open Manifold
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

/-- Components of the covariant derivative of the curvature tensor. -/
noncomputable def covariantCurvature {n : ℕ} (g : Model n → Matrix (Fin n) (Fin n) ℝ)
    (x : Model n) (a l i j k : Fin n) : ℝ :=
  coordinateDerivative l (fun y => curvature g y a i j k) x +
    ∑ b, (christoffel g x a l b * curvature g x b i j k -
      christoffel g x b l i * curvature g x a b j k -
      christoffel g x b l j * curvature g x a i b k -
      christoffel g x b l k * curvature g x a i j b)

/-- The endomorphism sending a tangent vector w to R(w, u)u. -/
noncomputable def jacobi {n : ℕ} (g : Model n → Matrix (Fin n) (Fin n) ℝ)
    (x u : Model n) : Matrix (Fin n) (Fin n) ℝ :=
  fun a i => ∑ j, ∑ k, u j * u k * curvature g x a i j k

/-- The Jacobi spectrum is constant on the entire unit tangent bundle. -/
def IsOsserman {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Model n) M]
    [IsManifold (𝓡 n) ∞ M] (g : SmoothMetric n M) : Prop :=
  ∃ P : Polynomial ℝ, ∀ p : M, ∀ x ∈ (chartAt (Model n) p).target, ∀ u : Model n,
    (∑ i, ∑ j, u i * u j * chartMetric g p x i j) = 1 →
      (jacobi (chartMetric g p) x u).charpoly = P

def IsFlat {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Model n) M]
    [IsManifold (𝓡 n) ∞ M] (g : SmoothMetric n M) : Prop :=
  ∀ p : M, ∀ x ∈ (chartAt (Model n) p).target, ∀ a i j k : Fin n,
    curvature (chartMetric g p) x a i j k = 0

/-- In dimension at least two, parallel curvature of strict sectional sign
characterizes metrics locally isometric to rank-one symmetric spaces. -/
def LocallyRankOneSymmetric {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Model n) M] [IsManifold (𝓡 n) ∞ M] (g : SmoothMetric n M) : Prop :=
  (∀ p : M, ∀ x ∈ (chartAt (Model n) p).target, ∀ a l i j k : Fin n,
    covariantCurvature (chartMetric g p) x a l i j k = 0) ∧
  (SectionalSign g (fun s => 0 < s) ∨ SectionalSign g (fun s => s < 0))

theorem main :
    ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      [ConnectedSpace M] [ChartedSpace (Model n) M] [IsManifold (𝓡 n) ∞ M],
      2 ≤ n → ∀ g : SmoothMetric n M, IsOsserman g → IsFlat g ∨ LocallyRankOneSymmetric g := by
  sorry

end OMA.S_wp_osserman_conjecture
