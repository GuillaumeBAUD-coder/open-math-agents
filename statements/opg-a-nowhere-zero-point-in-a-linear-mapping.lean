import Mathlib

/-!
# A nowhere-zero point in a linear mapping

Source: https://www.openproblemgarden.org/op/a_nowhere_zero_point_in_a_linear_mapping
Credit: @lzvxck

Jaeger's conjecture, as stated in the source: if `𝔽` is a finite field with at least 4
elements and `A` is an invertible `n × n` matrix with entries in `𝔽`, then there are column
vectors `x, y ∈ 𝔽^n` which have no coordinates equal to zero such that `A x = y`.

(Alon and Tarsi proved it for fields that are not of prime order; the prime-order case is open.)
-/

namespace OMA.S_opg_a_nowhere_zero_point_in_a_linear_mapping

/-- **Jaeger's conjecture.** Over a finite field with at least 4 elements, every invertible
`n × n` matrix `A` maps some nowhere-zero vector `x` to a nowhere-zero vector `y = A x`. -/
theorem main : ∀ (F : Type) [Field F] [Fintype F], 4 ≤ Fintype.card F →
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) F), IsUnit A →
      ∃ x y : Fin n → F, (∀ i, x i ≠ 0) ∧ (∀ i, y i ≠ 0) ∧ A.mulVec x = y := by
  sorry

end OMA.S_opg_a_nowhere_zero_point_in_a_linear_mapping
