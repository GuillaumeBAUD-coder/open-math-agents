import FormalConjectures.Millennium.Poincare

/-!
The topological conjecture uses a Hausdorff charted space with no second-countability
assumption. Separate compactness of a homotopy 3-sphere from the smoothing theorem
for second-countable topological 3-manifolds. The smooth atlas can replace the
original charts while preserving the given topology.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_implication_R1

open scoped Manifold ContDiff
open PoincareConjecture ContinuousMap

universe u

def H1 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M],
    M ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → CompactSpace M

def H2 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SecondCountableTopology M], ∃ a : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      @IsManifold _ _ _ _ _ _ _ (𝓡 3) ∞ M _ a

lemma assemble : H1 → H2 → SmoothConjectureFor.{u} 3 → ConjectureFor 3 := by
  intro hc hs h M t ht charts he
  have compact := hc M he
  have : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨atlasM, smoothM⟩ := hs M
  let chosenAtlas := atlasM
  let e : ULift.{u} M ≃ₜ M := Homeomorph.ulift
  let liftChart := fun c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)) =>
    e.transOpenPartialHomeomorph c
  let liftedAtlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} M) := {
    atlas := liftChart '' atlasM.atlas
    chartAt := fun x => liftChart (atlasM.chartAt (e x))
    mem_chart_source := fun x => atlasM.mem_chart_source (e x)
    chart_mem_atlas := fun x => ⟨_, atlasM.chart_mem_atlas (e x), rfl⟩ }
  have : IsManifold (𝓡 3) ∞ (ULift.{u} M) := by
    refine { compatible := ?_ }
    rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    have hcd := @HasGroupoid.compatible _ _ M _ chosenAtlas _ smoothM.toHasGroupoid c d hc hd
    change ((e.transOpenPartialHomeomorph c).symm.trans (e.transOpenPartialHomeomorph d)) ∈ _
    rw [Homeomorph.transOpenPartialHomeomorph_eq_trans, Homeomorph.transOpenPartialHomeomorph_eq_trans,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
      ← OpenPartialHomeomorph.trans_assoc e.toOpenPartialHomeomorph.symm,
      ← Homeomorph.symm_toOpenPartialHomeomorph, ← Homeomorph.trans_toOpenPartialHomeomorph]
    simpa using hcd
  obtain ⟨f⟩ := h (ULift.{u} M) (e.toHomotopyEquiv.trans he)
  exact ⟨e.symm.trans f.toHomeomorph⟩

theorem main : H1 → H2 → type_of% @PoincareConjecture.poincare_conjecture.variants.smooth_implication :=
  assemble

end OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_implication_R1
