import Mathlib

/-!
# A nowhere-zero point in a linear mapping

Source: https://www.openproblemgarden.org/op/a_nowhere_zero_point_in_a_linear_mapping
Credit: @menelikbaye-digitalmethod
-/

namespace OMA.S_opg_a_nowhere_zero_point_in_a_linear_mapping

universe u

theorem main :
    ∀ (F : Type u) [Field F] [Fintype F], 4 ≤ Fintype.card F →
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) F), IsUnit A →
        ∃ x y : Fin n → F,
          (∀ i, x i ≠ 0) ∧ (∀ i, y i ≠ 0) ∧ A.mulVec x = y := by
  sorry

end OMA.S_opg_a_nowhere_zero_point_in_a_linear_mapping
