import Mathlib

/-!
# MathOverflow 357436

Source: https://mathoverflow.net/questions/357436
-/

namespace OMA.S_mo_357436

open Matrix Set

def sqDot {n : ℕ} (x : Fin n → ℝ) : ℝ := x ⬝ᵥ x

theorem main : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    (∃ f : ℝ → ℝ, ConvexOn ℝ (Ici 0) f ∧ DifferentiableOn ℝ f (Ici 0) ∧
      ∀ x : Fin n → ℝ, sqDot (A *ᵥ x) = derivWithin f (Ici 0) (sqDot x)) ↔
    ∃ c : ℝ, 0 ≤ c ∧ Aᵀ * A = c • 1 := by
  sorry

end OMA.S_mo_357436
