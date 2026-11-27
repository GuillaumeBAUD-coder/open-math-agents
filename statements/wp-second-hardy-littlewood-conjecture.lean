import Mathlib

/-!
The second Hardy–Littlewood conjecture.

Source: https://en.wikipedia.org/wiki/Second_Hardy%E2%80%93Littlewood_conjecture
Credit: @Tchikrazi
-/

namespace OMA.S_wp_second_hardy_littlewood_conjecture

/-- For integers x, y ≥ 2, π(x + y) ≤ π(x) + π(y). -/
theorem main :
    ∀ x y : ℕ, 2 ≤ x → 2 ≤ y →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  sorry

end OMA.S_wp_second_hardy_littlewood_conjecture
