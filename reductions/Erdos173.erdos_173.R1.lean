import FormalConjectures.ErdosProblems.«173»

/-!
The proof of Erdős 173 transported to the Euclidean plane separates the finite
configuration that rules out a side length from the theorem that a two-colouring
can rule out at most one equilateral side length. See the proof of Erdős Problem
173 at https://github.com/plasma-ai/erdos-173, especially FinalAssembly.lean.
-/

namespace OMA.R_Erdos173_erdos_173_R1

open Affine
open scoped Congruent EuclideanGeometry

/-- A missing triangle forces each of its side lengths to be missing for equilateral triangles. -/
def H1 : Prop :=
  ∀ (c : EuclideanSpace ℝ (Fin 2) → Fin 2)
    (T : Triangle ℝ (EuclideanSpace ℝ (Fin 2))), ¬ Erdos173.HasMonochromaticCopy c T →
    ∀ i j, i ≠ j → ∀ v : Fin 3 → EuclideanSpace ℝ (Fin 2),
    (∀ a b, a ≠ b → dist (v a) (v b) = dist (T.points i) (T.points j)) →
    ¬ ∃ k, ∀ a, c (v a) = k

/-- A two-colouring can avoid equilateral triangles at only one positive side length. -/
def H2 : Prop :=
  ∀ (c : EuclideanSpace ℝ (Fin 2) → Fin 2) (s t : ℝ), 0 < s → 0 < t →
    (∀ v : Fin 3 → EuclideanSpace ℝ (Fin 2), (∀ a b, a ≠ b → dist (v a) (v b) = s) →
      ¬ ∃ k, ∀ a, c (v a) = k) →
    (∀ v : Fin 3 → EuclideanSpace ℝ (Fin 2), (∀ a b, a ≠ b → dist (v a) (v b) = t) →
      ¬ ∃ k, ∀ a, c (v a) = k) →
    s = t

theorem main : H1 → H2 → type_of% @Erdos173.erdos_173 := by
  intro side_missing unique_length c T₁ T₂ h₁ h₂
  refine ⟨1, congruent_iff_dist_eq.mpr fun i j => ?_⟩
  by_cases hij : i = j
  · simp [hij]
  · simp only [Equiv.Perm.coe_one, Function.comp_apply, id]
    exact unique_length c _ _ (dist_pos.mpr (T₁.independent.injective.ne hij))
      (dist_pos.mpr (T₂.independent.injective.ne hij))
      (side_missing c T₁ h₁ i j hij) (side_missing c T₂ h₂ i j hij)

end OMA.R_Erdos173_erdos_173_R1
