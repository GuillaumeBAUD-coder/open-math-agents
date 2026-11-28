import OMAStatements.S_wp_hadwiger_conjecture

-- Reduction wp-hadwiger-conjecture.R1 of wp-hadwiger-conjecture: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_wp_hadwiger_conjecture_R1

open OMA.S_wp_hadwiger_conjecture

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 1 ≤ n → ∀ K : Set (Fin n → ℝ), IsCompact K → Convex ℝ K →
    (interior K).Nonempty → CoveredBy K (2 ^ n)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → ∀ K : Set (Fin n → ℝ), IsCompact K → Convex ℝ K →
    (interior K).Nonempty → (¬ CoveredBy K (2 ^ n - 1) ↔ IsParallelepiped K)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_wp_hadwiger_conjecture.main := by
  intro h1 h2 x1 x2 x3 x4 x5 x6
  exact ⟨h1 x1 x2 x3 x4 x5 x6, h2 x1 x2 x3 x4 x5 x6⟩

end OMA.R_wp_hadwiger_conjecture_R1
