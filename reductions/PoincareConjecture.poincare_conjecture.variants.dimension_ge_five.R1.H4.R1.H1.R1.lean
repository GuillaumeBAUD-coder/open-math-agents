import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R1
import Mathlib

-- Reduction PoincareConjecture.poincare_conjecture.variants.dimension_ge_five.R1.H4.R1.H1.R1 of step PoincareConjecture.poincare_conjecture.variants.dimension_ge_five.R1.H4.R1.H1
-- Credit: @FarzanAhmedHossain

/-!
Stallings' route to the engulfing step. Puncture the homotopy sphere: the
puncture is a contractible open manifold (homotopy theory, H1) whose ends are
punctured chart balls outside every compact set (proved below as
`punctured_chart_end`). The Euclidean recognition theorem for such manifolds
(H2: Stallings 1962 in the PL category, Luft 1967 and Newman 1966 for
topological manifolds) makes the puncture homeomorphic to Euclidean space, and
the inverse homeomorphism is an open cell engulfing every compact set.

H1 and H2 are copied verbatim from H2 and H3 of the merged reduction
PoincareConjecture.poincare_conjecture.variants.dimension_ge_five.R2 by
@steveDOTdigital, and so is the lemma `punctured_chart_end`, so one proof of each
statement serves both reduction trees.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R1_H1_R1

open Set Metric Topology ContinuousMap
open scoped ContinuousMap Manifold

/-- Deleting a point from a closed homotopy sphere can give a contractible
manifold. This is a homotopy statement about an open manifold. -/
def H1 : Prop := ∀ n : ℕ, 5 ≤ n → ∀ (M : Type) [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M],
  (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) →
  ∃ p : M, ContractibleSpace ↥(({p} : Set M)ᶜ)

/-- Euclidean recognition for a contractible open manifold with punctured-ball
neighbourhoods at infinity. These neighbourhoods are simply connected for n ≥ 3. -/
def H2 : Prop := ∀ n : ℕ, 5 ≤ n → ∀ (X : Type) [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [ContractibleSpace X],
  (∀ K : Set X, IsCompact K → ∃ U : Set X, IsOpen U ∧ IsCompact Uᶜ ∧ Disjoint K U ∧
    ∃ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r ∧ Nonempty (U ≃ₜ ↥(ball c r \ {c}))) →
  Nonempty (X ≃ₜ EuclideanSpace ℝ (Fin n))

theorem punctured_chart_end {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : M)
    (K : Set ↥(({p} : Set M)ᶜ)) (hK : IsCompact K) :
    ∃ U : Set ↥(({p} : Set M)ᶜ), IsOpen U ∧ IsCompact Uᶜ ∧ Disjoint K U ∧
      ∃ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r ∧ Nonempty (U ≃ₜ ↥(ball c r \ {c})) := by
  classical
  let P := ↥(({p} : Set M)ᶜ)
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  let F : Set M := (Subtype.val : P → M) '' K
  have hc : IsCompact F := hK.image continuous_subtype_val
  have hpF : p ∉ F := by
    rintro ⟨x,hx,hxp⟩
    exact x.property (Set.mem_singleton_iff.mpr hxp)
  have hps : p ∈ e.source := mem_chart_source _ _
  have hop := e.isOpen_inter_preimage_symm hc.isClosed.isOpen_compl
  have hm : e p ∈ e.target ∩ e.symm ⁻¹' Fᶜ := ⟨e.map_source hps,by simpa [e.left_inv hps] using hpF⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hop (e p) hm
  let W := e.source ∩ e ⁻¹' ball (e p) r
  let U := (Subtype.val : P → M) ⁻¹' W
  have hW : IsOpen W := e.isOpen_inter_preimage Metric.isOpen_ball
  have hpW : p ∈ W := ⟨hps,Metric.mem_ball_self hr⟩
  refine ⟨U,hW.preimage continuous_subtype_val,?_,?_,e p,r,hr,?_⟩
  · apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have heq : (Subtype.val : P → M) '' Uᶜ = Wᶜ := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact hx
      · intro hy
        have hne : y ≠ p := fun h => hy (h.symm ▸ hpW)
        exact ⟨⟨y,hne⟩,hy,rfl⟩
    rw [heq]
    exact hW.isClosed_compl.isCompact
  · apply Set.disjoint_left.mpr
    intro x hxK hxU
    have hx : (x:M) ∈ W := hxU
    have hout := (hball hx.2).2
    exact (show e.symm (e x) ∉ F from hout) (by rw [e.left_inv hx.1]; exact ⟨x,hxK,rfl⟩)
  · let V := ball (e p) r \ {e p}
    have fu (x : U) : e x.val.val ∈ V := by
      have hx : x.val.val ∈ W := x.property
      refine ⟨hx.2,?_⟩
      intro he
      have hpEq := e.injOn hx.1 hps (Set.mem_singleton_iff.mp he)
      exact x.val.property (Set.mem_singleton_iff.mpr hpEq)
    have bv (y : V) : e.symm y.val ≠ p := by
      intro he
      have htar := (hball y.property.1).1
      apply y.property.2
      exact Set.mem_singleton_iff.mpr ((e.right_inv htar).symm.trans (congrArg e he))
    have bu (y : V) : (⟨e.symm y.val,bv y⟩ : P) ∈ U := by
      have htar := (hball y.property.1).1
      refine ⟨e.map_target htar,?_⟩
      change e (e.symm y.val) ∈ ball (e p) r
      rw [e.right_inv htar]
      exact y.property.1
    refine ⟨{ toFun := fun x => ⟨e x.val.val,fu x⟩
              invFun := fun y => ⟨⟨e.symm y.val,bv y⟩,bu y⟩
              left_inv := fun x => Subtype.ext (Subtype.ext (e.left_inv (show x.val.val ∈ W from x.property).1))
              right_inv := fun y => Subtype.ext (e.right_inv (hball y.property.1).1)
              continuous_toFun := ?_
              continuous_invFun := ?_ }⟩
    · exact (e.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
        fun x => (show x.val.val ∈ W from x.property).1).subtype_mk _
    · exact ((e.continuousOn_symm.comp_continuous continuous_subtype_val
        fun y => (hball y.property.1).1).subtype_mk _).subtype_mk _

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R1.H1 := by
  intro hpuncture hrecognize n hn M _ _ _ _ _ e
  have : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨p, hcontr⟩ := hpuncture n hn M e
  let U : TopologicalSpace.Opens M := ⟨({p} : Set M)ᶜ, isClosed_singleton.isOpen_compl⟩
  have : ContractibleSpace U := hcontr
  obtain ⟨h⟩ := hrecognize n hn U (fun K hK => punctured_chart_end p K hK)
  exact ⟨p, fun K _ => ⟨h.symm, h.symm.isOpenEmbedding, fun x _ => h.symm.surjective x⟩⟩

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R1_H1_R1
