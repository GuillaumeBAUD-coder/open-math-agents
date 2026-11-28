import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_four_R1
import Mathlib

/-!
# A compact-engulfing criterion for recognition of the puncture

A Euclidean chart engulfing a compact set can be shrunk to one with compact
closure. A compact cover then gives a nested cover by open four-cells.
The two remaining inputs are compact engulfing in the four-manifold and
Morton Brown's theorem on monotone unions of open cells (Proc. AMS 12, 1961).
-/
-- Credit: @VestigeClub

open Set Topology Metric CategoryTheory Limits AlgebraicTopology

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_four_R1_H4_R1

/-- The image of a sufficiently large bounded Euclidean ball is a relatively
compact open cell that still contains the specified compact set. -/
private theorem shrink_chart {X : Type} [TopologicalSpace X] [T2Space X]
    (K : Set X) (compactK : IsCompact K)
    (f : EuclideanSpace ℝ (Fin 4) → X) (embedding : IsOpenEmbedding f)
    (inside : K ⊆ range f) :
    ∃ U : Set X, IsOpen U ∧ IsCompact (closure U) ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 4)) ∧ K ⊆ U := by
  let E := EuclideanSpace ℝ (Fin 4)
  have compactPre : IsCompact (f ⁻¹' K) :=
    embedding.isEmbedding.isInducing.isCompact_preimage' compactK inside
  obtain ⟨r,positive,bounded⟩ := compactPre.isBounded.subset_ball_lt 0 (0 : E)
  have disk : E ≃ₜ ball (0 : E) r :=
    (Homeomorph.unitBall (E:=E)).trans
      (OpenPartialHomeomorph.unitBallBall (E:=E) (0 : E) r positive).toHomeomorphSourceTarget
  have compactClosed : IsCompact (f '' closedBall (0 : E) r) :=
    (isCompact_closedBall (0 : E) r).image embedding.continuous
  refine ⟨f '' ball (0 : E) r,embedding.isOpenMap _ isOpen_ball,?_,?_,?_⟩
  · exact compactClosed.of_isClosed_subset isClosed_closure
      (closure_minimal (image_mono ball_subset_closedBall) compactClosed.isClosed)
  · exact ⟨(embedding.isEmbedding.homeomorphImage _).symm.trans disk.symm⟩
  · intro x hx
    obtain ⟨y,rfl⟩ := inside hx
    exact ⟨y,bounded hx,rfl⟩

/-- A countable compact cover and relatively compact engulfings yield a monotone
open cover of the same chart type. -/
private theorem nested_cover {X E : Type} [TopologicalSpace X] [TopologicalSpace E]
    [SigmaCompactSpace X]
    (engulf : ∀ K : Set X, IsCompact K →
      ∃ U : Set X, IsOpen U ∧ IsCompact (closure U) ∧ Nonempty (U ≃ₜ E) ∧ K ⊆ U) :
    ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧ Monotone U ∧
      (⋃ n, U n)=univ ∧ ∀ n, Nonempty (U n ≃ₜ E) := by
  classical
  obtain ⟨K,compactK,covers⟩ := SigmaCompactSpace.exists_compact_covering (X:=X)
  let Chart := {U : Set X // IsOpen U ∧ IsCompact (closure U) ∧ Nonempty (U ≃ₜ E)}
  have existsChart (S : Set X) (hS : IsCompact S) : ∃ U : Chart, S ⊆ U.val := by
    obtain ⟨U,op,cl,homeo,inside⟩ := engulf S hS
    exact ⟨⟨U,op,cl,homeo⟩,inside⟩
  let pick (S : Set X) (hS : IsCompact S) : Chart := (existsChart S hS).choose
  have within (S : Set X) (hS : IsCompact S) : S ⊆ (pick S hS).val :=
    (existsChart S hS).choose_spec
  let advance (n : ℕ) (U : Chart) : Chart :=
    pick (closure U.val ∪ K (n+1)) (U.property.2.1.union (compactK (n+1)))
  let cells : ℕ → Chart := Nat.rec (pick (K 0) (compactK 0)) advance
  have next_set (n : ℕ) : closure (cells n).val ∪ K (n+1) ⊆ (cells (n+1)).val :=
    within _ ((cells n).property.2.1.union (compactK (n+1)))
  have larger (n : ℕ) : (cells n).val ⊆ (cells (n+1)).val :=
    subset_closure.trans (subset_union_left.trans (next_set n))
  have covered (n : ℕ) : K n ⊆ (cells n).val := by
    cases n with
    | zero => exact within (K 0) (compactK 0)
    | succ n => exact subset_union_right.trans (next_set n)
  refine ⟨fun n => (cells n).val,fun n => (cells n).property.1,
    monotone_nat_of_le_succ larger,?_,fun n => (cells n).property.2.2⟩
  apply iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨n,hx⟩ := iUnion_eq_univ_iff.mp covers x
  exact ⟨n,covered n hx⟩

def H1 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [CompactSpace M]
    [SecondCountableTopology M] [SimplyConnectedSpace M],
    IsZero (((singularHomologyFunctor AddCommGrpCat 2).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of M)) → ∃ p : M, ∀ K : Set (↥({p}ᶜ : Set M)), IsCompact K →
        ∃ f : EuclideanSpace ℝ (Fin 4) → ↥({p}ᶜ : Set M), IsOpenEmbedding f ∧ K ⊆ range f

def H2 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] (U : ℕ → Set X),
    (∀ n, IsOpen (U n)) → Monotone U → (⋃ n, U n)=univ →
    (∀ n, Nonempty (U n ≃ₜ EuclideanSpace ℝ (Fin 4))) →
    Nonempty (X ≃ₜ EuclideanSpace ℝ (Fin 4))

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_four_R1.H4 := by
  intro engulf brown M _ _ _ _ _ _ homology
  obtain ⟨p,engulfs⟩ := engulf M homology
  let P := ({p}ᶜ : Set M)
  let _ : LocallyCompactSpace P := isClosed_singleton.isOpen_compl.locallyCompactSpace
  have charts (K : Set P) (compactK : IsCompact K) :
      ∃ U : Set P, IsOpen U ∧ IsCompact (closure U) ∧
        Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 4)) ∧ K ⊆ U := by
    obtain ⟨f,embedding,inside⟩ := engulfs K compactK
    exact shrink_chart K compactK f embedding inside
  obtain ⟨U,op,nested,covers,euclidean⟩ := nested_cover charts
  exact ⟨p,brown P U op nested covers euclidean⟩

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_four_R1_H4_R1
