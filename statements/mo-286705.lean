import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Fin

namespace OMA.S_mo_286705

/-- Coefficients of the generating polynomial in the question. -/
noncomputable def value (d m n : ℕ) (i : Fin (n+1)) : ℝ :=
  (((1 - Polynomial.X)^i.val *
      (∑ j ∈ Finset.range (d+1), (Polynomial.X : Polynomial ℝ)^j)^(n-i.val)) :
        Polynomial ℝ).coeff m

/-- Since the degree-zero polynomial is 1, orthogonality to the first
two nonconstant polynomials forces every positive weight to lie at the center. -/
theorem main :
    ∀ d n : ℕ, 2 ≤ d → ∀ w : Fin (n+1) → ℝ, (∀ i, 0 ≤ w i) →
      (((∑ i : Fin (n+1), w i * value d 1 n i) = 0 ∧
        (∑ i : Fin (n+1), w i * value d 2 n i) = 0) ↔
          ∀ i, 2*i.val ≠ n → w i = 0) := by
  sorry

end OMA.S_mo_286705
