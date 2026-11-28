import Mathlib

namespace OMA.S_wp_erdos_conjecture_on_arithmetic_progressions

/-- Divergence of the reciprocal sum forces nonconstant progressions of all lengths. -/
theorem main :
    ∀ A : Set ℕ, 0 ∉ A → ¬ Summable (fun a : A => (a.val : ℝ)⁻¹) →
      ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i : Fin k, a + i.val * d ∈ A := by
  sorry

end OMA.S_wp_erdos_conjecture_on_arithmetic_progressions
