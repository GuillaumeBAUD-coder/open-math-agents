import OMAStatements.S_mo_33841

open scoped Manifold ContDiff

namespace OMA.R_mo_33841_R1

def H1 : Prop :=
  ∀ (N : Type) [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N],
    ContractibleSpace N → ¬ CompactSpace N →
    Nonempty (Diffeomorph
      ((𝓘(Real, Real)).prod (𝓡 3)) (𝓡 4)
      (Real × N) (EuclideanSpace Real (Fin 4)) ∞)

def H2 : Prop :=
  ∀ (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M],
    Nonempty (M ≃ₜ EuclideanSpace Real (Fin 4)) →
    ∀ (N : Type) [TopologicalSpace N]
      [ChartedSpace (EuclideanSpace Real (Fin 3)) N]
      [IsManifold (𝓡 3) ∞ N],
      Nonempty (Diffeomorph (𝓡 4)
        ((𝓘(Real, Real)).prod (𝓡 3)) M (Real × N) ∞) →
      ContractibleSpace N ∧ ¬ CompactSpace N

theorem main : H1 → H2 → type_of% @OMA.S_mo_33841.main := by
  intro h1 h2 M _ _ _ hHomeo hNotEuclidean N _ _ _ hProduct
  obtain ⟨hContractible, hNoncompact⟩ := h2 M hHomeo N hProduct
  obtain ⟨hStandard⟩ := h1 N hContractible hNoncompact
  exact hNotEuclidean ⟨hProduct.some.trans hStandard⟩

end OMA.R_mo_33841_R1
