import Mathlib

/-!
Is 509203 the smallest Riesel number?

Source: https://en.wikipedia.org/wiki/Riesel_number
Credit: @Tchikrazi
-/

namespace OMA.S_wp_is_509_203_the_lowest_riesel_number

/-- Every k · 2ⁿ − 1 is composite for an odd positive Riesel number k. -/
def IsRieselNumber (k : ℕ) : Prop :=
  0 < k ∧ Odd k ∧ ∀ n : ℕ, 1 < k * 2 ^ n - 1 ∧ ¬ Nat.Prime (k * 2 ^ n - 1)

theorem main :
    IsRieselNumber 509203 ∧ ∀ k : ℕ, IsRieselNumber k → 509203 ≤ k := by
  sorry

end OMA.S_wp_is_509_203_the_lowest_riesel_number
