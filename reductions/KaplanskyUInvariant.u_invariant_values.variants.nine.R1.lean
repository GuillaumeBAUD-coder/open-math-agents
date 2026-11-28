import FormalConjectures.Paper.KaplanskyUInvariant

namespace OMA.R_KaplanskyUInvariant_u_invariant_values_variants_nine_R1

open QuadraticForm QuadraticMap

-- Field construction from the tower approach described in project note 41659.
-- The fixed nine-form survives each stage. Every ten-form over one stage
-- acquires a nonzero isotropic vector over the next.
def H1 : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : NeZero (2 : F))
    (K : ℕ → Subfield F) (a : Fin 9 → F),
    Monotone K ∧ (∀ z : F, ∃ r, z ∈ K r) ∧ (∀ i, a i ∈ K 0) ∧
    (∀ r (x : Fin 9 → F), (∀ i, x i ∈ K r) →
      weightedSumSquares F a x = 0 → x = 0) ∧
    (∀ r (b : Fin 10 → F), (∀ i, b i ∈ K r) →
      ∃ y : Fin 10 → F, (∀ i, y i ∈ K (r + 1)) ∧
        y ≠ 0 ∧ weightedSumSquares F b y = 0)

-- Restrict an anisotropic form to a coordinate subspace and diagonalize it.
def H2 : Prop :=
  ∀ (F : Type) [Field F] [NeZero (2 : F)] (m n : ℕ),
    m ≤ n → n ∈ anisotropicDims F →
      ∃ b : Fin m → F, (weightedSumSquares F b).Anisotropic

theorem main : H1 → H2 → type_of% @KaplanskyUInvariant.u_invariant_values.variants.nine := by
  classical
  intro tower restrictForm
  obtain ⟨F, instF, instTwo, K, a, hmono, hcover, _, hkeep, hsplit⟩ := tower
  have commonStage {n : ℕ} (v : Fin n → F) : ∃ r, ∀ i, v i ∈ K r := by
    choose stage hstage using fun i => hcover (v i)
    refine ⟨Finset.univ.sup stage, fun i => ?_⟩
    exact hmono (Finset.le_sup (f := stage) (Finset.mem_univ i)) (hstage i)
  refine ⟨F, instF, instTwo, ?_, ?_⟩
  · refine mem_anisotropicDims_iff.mpr ⟨weightedSumSquares F a, ?_⟩
    intro v hv
    obtain ⟨r, hr⟩ := commonStage v
    exact hkeep r v hr hv
  · intro n hn
    by_contra! h
    obtain ⟨b, hb⟩ := restrictForm F 10 n (by omega) hn
    obtain ⟨r, hr⟩ := commonStage b
    obtain ⟨y, _, hy, hz⟩ := hsplit r b hr
    exact hy (hb y hz)

end OMA.R_KaplanskyUInvariant_u_invariant_values_variants_nine_R1
