import OMAReductions.R_Erdos103_erdos_103_variants_two_le_R1

-- Reduction Erdos103.erdos_103.variants.two_le.R1.H2.R1 of step Erdos103.erdos_103.variants.two_le.R1.H2
-- Credit: @chris01-dev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the step.

/-!
Write D(n) for the least diameter of n points of the plane with pairwise distances at least 1.
D is nondecreasing. This file splits the step according to whether D(n) = D(n+1) (n lies on a
plateau of D) or D(n) < D(n+1) (n is the last point of a plateau, a jump of D).

H1 is the plateau case. It is true for all large n, with no tightness assumption, by the
following argument, left as a step. Let B be a separated set of n+1 points whose diameter is at
most that of every separated set of n points. Deleting any single point p of B leaves a
minimiser for n. If these n+1 minimisers were pairwise congruent, then the sum of the squared
distances between the points of B minus p would not depend on p, so the sum g(p) of the squared
distances from p to the points of B would be the same for every p in B. But g(p) is n+1 times
the squared distance from p to the centroid of B, plus a constant. So all n+1 points of B
would lie on one circle centred at the centroid, of radius at most diam B. A circle of radius
r carries at most 8 r + 8 points with pairwise distances at least 1, and diam B is at most
D(n), which is at most 2 sqrt n + 2 (points of the integer grid in a square). For large n this
is a contradiction, so two of the deleted sets are incongruent minimisers.

H2 is the jump case: the step itself, with the extra assumption that every separated set of
n+1 points has diameter strictly larger than D(n). So the only n left are those for which the
minimisers for n are at the same time separated sets of the largest possible cardinality
within their diameter. Small examples of such n with a single minimiser are n = 3 (unit
triangle) and n = 7 (regular hexagon with its centre). H2 is open.
-/

open EuclideanGeometry Filter Finset
open Erdos103

namespace OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1

/-- Plateau case: some separated set of `n+1` points is no wider than every separated set of
`n` points. Then there are two incongruent minimisers for `n`. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop,
    (∃ B ∈ separatedSets (n + 1), ∀ C ∈ separatedSets n,
      Metric.diam (B : Set ℝ²) ≤ Metric.diam (C : Set ℝ²)) →
    ∃ A A' : Finset ℝ², IsMinimiser n A ∧ IsMinimiser n A' ∧ ¬ Congruent A A'

/-- Jump case: the step, restricted to those `n` for which every separated set of `n+1` points
is strictly wider than the minimisers for `n`. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop,
    (∃ A : Finset ℝ², IsMinimiser n A) →
    (∀ A : Finset ℝ², IsMinimiser n A → ∀ p ∈ A,
      ∃ q ∈ A.erase p, dist p q = 1 ∨ dist p q = Metric.diam (A : Set ℝ²)) →
    (∀ A : Finset ℝ², IsMinimiser n A → ∀ B ∈ separatedSets (n + 1),
      Metric.diam (A : Set ℝ²) < Metric.diam (B : Set ℝ²)) →
    ∃ A B : Finset ℝ², IsMinimiser n A ∧ IsMinimiser n B ∧ ¬ Congruent A B

theorem main : H1 → H2 → OMA.R_Erdos103_erdos_103_variants_two_le_R1.H2 := by
  intro k1 k2
  filter_upwards [k1, k2] with n h1 h2 hex htight
  by_cases hp : ∃ B ∈ separatedSets (n + 1), ∀ C ∈ separatedSets n,
      Metric.diam (B : Set ℝ²) ≤ Metric.diam (C : Set ℝ²)
  · exact h1 hp
  · refine h2 hex htight fun A hA B hB => ?_
    by_contra hlt
    refine hp ⟨B, hB, fun C hC => ?_⟩
    exact (not_lt.mp hlt).trans (hA.2 hC)

end OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1
