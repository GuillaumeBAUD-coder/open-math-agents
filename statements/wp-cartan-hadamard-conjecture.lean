import Mathlib

namespace OMA.S_wp_cartan_hadamard_conjecture

open MeasureTheory
open scoped BigOperators ContDiff ENNReal

abbrev Vector (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A Riemannian metric in the global coordinates of a Cartan–Hadamard manifold. -/
structure MetricTensor (n : ℕ) where
  tensor : Vector n → Matrix (Fin n) (Fin n) ℝ
  smooth : ∀ i j, ContDiff ℝ ∞ (fun x => tensor x i j)
  posDef : ∀ x, (tensor x).PosDef

noncomputable def coordinateDerivative {n : ℕ} (i : Fin n)
    (f : Vector n → ℝ) (x : Vector n) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

def metricPair {n : ℕ} (g : MetricTensor n) (x u v : Vector n) : ℝ :=
  ∑ i, ∑ j, u i * g.tensor x i j * v j

/-- The coefficient of the upper index a in the Levi-Civita connection. -/
noncomputable def christoffel {n : ℕ} (g : MetricTensor n) (x : Vector n)
    (a i j : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ b,
    ((g.tensor x)⁻¹) a b *
      (coordinateDerivative i (fun y => g.tensor y j b) x +
        coordinateDerivative j (fun y => g.tensor y i b) x -
        coordinateDerivative b (fun y => g.tensor y i j) x)

/-- The upper component a of the curvature applied to the coordinate triple i, j, k. -/
noncomputable def curvature {n : ℕ} (g : MetricTensor n) (x : Vector n)
    (a i j k : Fin n) : ℝ :=
  coordinateDerivative i (fun y => christoffel g y a j k) x -
    coordinateDerivative j (fun y => christoffel g y a i k) x +
    ∑ b, (christoffel g x a i b * christoffel g x b j k -
      christoffel g x a j b * christoffel g x b i k)

/-- The numerator of sectional curvature for the two tangent vectors u and v. -/
noncomputable def sectionalNumerator {n : ℕ} (g : MetricTensor n)
    (x u v : Vector n) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, u i * v j * v k * u b * g.tensor x a b *
    curvature g x a i j k

/-- Every geodesic with given initial position and velocity is defined for all time. -/
def GeodesicallyComplete {n : ℕ} (g : MetricTensor n) : Prop :=
  ∀ x v : Vector n, ∃ γ : ℝ → Vector n,
    ContDiff ℝ ∞ γ ∧ γ 0 = x ∧ deriv γ 0 = v ∧
    ∀ t i, (deriv (deriv γ) t) i =
      -(∑ j, ∑ k, christoffel g (γ t) i j k * (deriv γ t) j * (deriv γ t) k)

noncomputable def volumeDensity {n : ℕ} (g : MetricTensor n) (x : Vector n) : ℝ :=
  Real.sqrt (g.tensor x).det

noncomputable def metricVolume {n : ℕ} (g : MetricTensor n)
    (A : Set (Vector n)) : ℝ≥0∞ :=
  ∫⁻ x in A, ENNReal.ofReal (volumeDensity g x)

/-- Perimeter as the supremum of the volume-weighted divergence of smooth,
compactly supported vector fields of metric norm at most one. -/
noncomputable def perimeter {n : ℕ} (g : MetricTensor n)
    (A : Set (Vector n)) : ℝ≥0∞ :=
  sSup {r | ∃ X : Vector n → Vector n,
    ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧
    (∀ x, metricPair g x (X x) (X x) ≤ 1) ∧
    r = ENNReal.ofReal
      (∫ x in A, ∑ i, coordinateDerivative i (fun y => volumeDensity g y * X y i) x)}

/-- The sharp Euclidean isoperimetric inequality of the Cartan–Hadamard conjecture. -/
theorem main :
    ∀ (n : ℕ) (g : MetricTensor n), 2 ≤ n →
      GeodesicallyComplete g → (∀ x u v, sectionalNumerator g x u v ≤ 0) →
      ∀ A : Set (Vector n), MeasurableSet A → Bornology.IsBounded A →
        0 < metricVolume g A → perimeter g A < ⊤ →
        (n : ℝ≥0∞) ^ n * volume (Metric.ball (0 : Vector n) 1) *
          metricVolume g A ^ (n - 1) ≤ perimeter g A ^ n := by
  sorry

end OMA.S_wp_cartan_hadamard_conjecture
