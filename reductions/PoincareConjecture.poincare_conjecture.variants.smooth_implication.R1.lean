import FormalConjectures.Millennium.Poincare

/-! A homotopy three-sphere is compact by top-dimensional homology.
Compactness makes a Hausdorff locally Euclidean manifold second countable.
Moise's smoothing theorem then provides a compatible smooth atlas. We transfer
the manifold to the universe of the smooth conjecture before applying it. -/

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_implication_R1

open scoped Manifold ContDiff EuclideanGeometry ContinuousMap
open PoincareConjecture

universe u

-- A noncompact connected three-manifold has zero top-dimensional homology,
-- whereas a homotopy three-sphere has the homology of the three-sphere.
def H1 : Prop := ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M],
  (M ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) → CompactSpace M

-- Moise smoothing for compact second-countable Hausdorff three-manifolds.
-- A separate Lean formalization is described in Qin et al., arXiv:2609.33842.
-- The smooth atlas can differ from the initial topological atlas.
def H2 : Prop := ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M]
  [CompactSpace M] [SecondCountableTopology M], ∃ atlas : ChartedSpace (ℝ^3) M,
    letI := atlas
    IsManifold (𝓡 3) ∞ M

-- Pulling the atlas back along a homeomorphism preserves its transition maps.
lemma smooth_pullback {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ℝ^3) M] [IsManifold (𝓡 3) ∞ M] (e : N ≃ₜ M) :
    ∃ c : ChartedSpace (ℝ^3) N, letI := c; IsManifold (𝓡 3) ∞ N := by
  let chart (x : N) := e.transOpenPartialHomeomorph (chartAt (ℝ^3) (e x))
  let c : ChartedSpace (ℝ^3) N := {
    atlas := Set.range chart
    chartAt := chart
    mem_chart_source := fun x => ChartedSpace.mem_chart_source (e x)
    chart_mem_atlas := fun x => ⟨x,rfl⟩ }
  refine ⟨c,?_⟩
  letI := c
  refine { compatible := ?_ }
  intro f g hf hg
  obtain ⟨x,rfl⟩ := hf
  obtain ⟨y,rfl⟩ := hg
  change (chart x).symm.trans (chart y) ∈ _
  have cancel : e.toOpenPartialHomeomorph.symm.trans e.toOpenPartialHomeomorph =
      OpenPartialHomeomorph.refl M := by
    rw [←Homeomorph.symm_toOpenPartialHomeomorph,←Homeomorph.trans_toOpenPartialHomeomorph]
    simp
  dsimp only [chart]
  rw [Homeomorph.transOpenPartialHomeomorph_eq_trans,Homeomorph.transOpenPartialHomeomorph_eq_trans,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,OpenPartialHomeomorph.trans_assoc,
    ←OpenPartialHomeomorph.trans_assoc e.toOpenPartialHomeomorph.symm,cancel,
    OpenPartialHomeomorph.refl_trans]
  exact HasGroupoid.compatible (ChartedSpace.chart_mem_atlas _) (ChartedSpace.chart_mem_atlas _)

lemma apply_smoothing : H1 → H2 → type_of% @PoincareConjecture.poincare_conjecture.variants.smooth_implication.{u} := by
  intro hcompact hsmooth h M top sep charts eqv
  let e : ULift.{u} M ≃ₜ M := Homeomorph.ulift
  letI : CompactSpace M := hcompact M eqv
  letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact (ℝ^3) M
  obtain ⟨atlas,compat⟩ := hsmooth M
  letI : ChartedSpace (ℝ^3) M := atlas
  letI : IsManifold (𝓡 3) ∞ M := compat
  obtain ⟨lifted,liftedCompat⟩ := smooth_pullback e
  letI : ChartedSpace (ℝ^3) (ULift.{u} M) := lifted
  letI : IsManifold (𝓡 3) ∞ (ULift.{u} M) := liftedCompat
  obtain ⟨d⟩ := h (ULift.{u} M) (e.toHomotopyEquiv.trans eqv)
  exact ⟨e.symm.trans d.toHomeomorph⟩

theorem main : H1 → H2 → type_of% @PoincareConjecture.poincare_conjecture.variants.smooth_implication := by
  exact apply_smoothing

end OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_implication_R1
