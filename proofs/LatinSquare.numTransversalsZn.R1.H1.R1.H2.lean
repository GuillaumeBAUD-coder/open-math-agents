import OMAReductions.R_LatinSquare_numTransversalsZn_R1_H1_R1
import Mathlib

theorem OMA.solution : OMA.R_LatinSquare_numTransversalsZn_R1_H1_R1.H2 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  unfold LatinSquare.z numTransversals
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact {
    toFun := fun σ => ⟨Equiv.ofBijective σ.1 (Finite.injective_iff_bijective.1 σ.2.1),
      Finite.injective_iff_bijective.1 σ.2.2⟩
    invFun := fun σ => ⟨σ.1, σ.1.injective, σ.2.injective⟩
    left_inv := fun σ => rfl
    right_inv := fun σ => by ext; rfl }
