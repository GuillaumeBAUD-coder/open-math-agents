import FormalConjectures.ErdosProblems.«91»

/-!
# Two nonsimilar optimal configurations on eight points

The lower bound is the eight-point consequence of Erdős and Fishburn's
Theorem 1 in Maximum planar sets that determine k distances (1996).
The witnesses can be sought in the triangular lattice.
-/

namespace OMA.R_Erdos91_erdos_91_variants_eight_R1

open EuclideanGeometry Erdos91

/-- Eight planar points determine at least four distances. -/
def H1 : Prop :=
  ∀ A : Finset ℝ², A.card = 8 → 4 ≤ distinctDistances A

/-- Two nonsimilar eight-point configurations with at most four distances. -/
def H2 : Prop :=
  ∃ A B : Finset ℝ², A.card = 8 ∧ B.card = 8 ∧
    distinctDistances A ≤ 4 ∧ distinctDistances B ≤ 4 ∧ ¬DilationEquivSimilar A B

theorem main : H1 → H2 → type_of% @Erdos91.erdos_91.variants.eight := by
  intro hbound ⟨A, B, hA, hB, hdistA, hdistB, hnonsim⟩ h
  have heA := le_antisymm hdistA (hbound A hA)
  have heB := le_antisymm hdistB (hbound B hB)
  have hmin : minimalDistinctDistances ℝ² 8 = 4 := by
    unfold minimalDistinctDistances
    apply le_antisymm
    · exact Nat.sInf_le ⟨A, hA, heA⟩
    · apply le_csInf
      · exact ⟨4, A, hA, heA⟩
      rintro d ⟨S, hS, hd⟩
      exact hd ▸ hbound S hS
  exact hnonsim (h A B ⟨hA, heA.trans hmin.symm⟩ ⟨hB, heB.trans hmin.symm⟩)

end OMA.R_Erdos91_erdos_91_variants_eight_R1
