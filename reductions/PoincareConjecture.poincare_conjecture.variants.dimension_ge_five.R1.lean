import FormalConjectures.Millennium.Poincare
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Homology and the topological generalized Poincaré conjecture in dimensions ≥ 5

A topological `n`-manifold (`n ≥ 5`) of the homotopy type of the `n`-sphere has
nonzero `n`-th singular homology. The top integral homology of a connected
noncompact `n`-manifold vanishes, so the manifold is compact. Simple
connectedness of the `n`-sphere passes across the homotopy equivalence, and
Newman's 1966 topological generalized Poincaré conjecture identifies a compact
simply connected `n`-manifold (`n ≥ 5`) homotopy equivalent to the `n`-sphere
with the `n`-sphere up to homeomorphism. See Hatcher, Algebraic Topology,
Section 3.3, and M. H. A. Newman, The engulfing theorem for topological
manifolds, Ann. of Math. (2) 84 (1966), 555–571.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1

open AlgebraicTopology CategoryTheory Limits
open scoped ContinuousMap

private theorem homotopy_homology_iso (n : ℕ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) :
    Nonempty ((((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)) ≅
      (((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of Y))) := by
  let F := (singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  refine ⟨⟨F.map f, F.map g, ?_, ?_⟩⟩
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨h⟩ := e.left_inv
    have hh : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) := h
    exact hh.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨h⟩ := e.right_inv
    have hh : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of Y)) := h
    exact hh.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n

/-- For `n ≥ 5`, the `n`-sphere has nonzero integral homology in degree `n`. -/
def H1 : Prop :=
  ∀ (n : ℕ), 5 ≤ n →
    ¬ IsZero (((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))

/-- For `n ≥ 5`, the top integral homology of a connected noncompact `n`-manifold vanishes. -/
def H2 : Prop :=
  ∀ (n : ℕ), 5 ≤ n →
    ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [ConnectedSpace M], ¬ CompactSpace M →
      IsZero (((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj
        (TopCat.of M))

/-- For `n ≥ 5`, the `n`-sphere is simply connected. -/
def H3 : Prop :=
  ∀ (n : ℕ), 5 ≤ n →
    SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- Newman's topological generalized Poincaré conjecture in dimensions `n ≥ 5`: a compact
simply connected Hausdorff `n`-manifold homotopy equivalent to the `n`-sphere is
homeomorphic to the `n`-sphere. -/
def H4 : Prop :=
  ∀ (n : ℕ), 5 ≤ n →
    ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
      M ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
      Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

theorem main : H1 → H2 → H3 → H4 →
    type_of% @PoincareConjecture.poincare_conjecture.variants.dimension_ge_five := by
  intro hSphere hVanishing hSC hNewman n hn M _ _ _ e
  have : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := hSC n hn
  have : SimplyConnectedSpace M := e.simplyConnectedSpace
  have : CompactSpace M := by
    by_contra h
    have hZero := hVanishing n hn M h
    obtain ⟨iso⟩ := homotopy_homology_iso n e
    exact hSphere n hn (hZero.of_iso iso.symm)
  exact hNewman n hn M e

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1
