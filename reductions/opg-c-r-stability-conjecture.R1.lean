import OMAStatements.S_opg_c_r_stability_conjecture

-- Reduction opg-c-r-stability-conjecture.R1 of opg-c-r-stability-conjecture: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_opg_c_r_stability_conjecture_R1

open OMA.S_opg_c_r_stability_conjecture
open scoped ContDiff Manifold
open Manifold

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ (d e : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
      [Nonempty M] [ChartedSpace (Space d) M] [IsManifold (Model d) ∞ M],
      ∀ (A : AmbientModel d e M) (r : ℕ∞), 1 ≤ r →
        ∀ f : Diffeomorphism d M r, IsStructurallyStable A f → closure (periodic f.equiv) = nonwandering f.equiv

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ (d e : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
      [Nonempty M] [ChartedSpace (Space d) M] [IsManifold (Model d) ∞ M],
      ∀ (A : AmbientModel d e M) (r : ℕ∞), 1 ≤ r →
        ∀ f : Diffeomorphism d M r, IsStructurallyStable A f → UniformlyHyperbolic A f (nonwandering f.equiv)

theorem main : H1 → H2 → type_of% @OMA.S_opg_c_r_stability_conjecture.main := by
  intro h1 h2 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
  exact ⟨h1 x1 x2 x3 x10 x11 x12 x13 x14, h2 x1 x2 x3 x10 x11 x12 x13 x14⟩

end OMA.R_opg_c_r_stability_conjecture_R1
