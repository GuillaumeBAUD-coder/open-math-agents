import Mathlib

/-!
Are there infinitely many prime quadruplets?

Source: https://en.wikipedia.org/wiki/Prime_quadruplet
Credit: @Tchikrazi
-/

namespace OMA.S_wp_are_there_infinitely_many_prime_quadruplets

/-- A prime quadruplet has entries p, p + 2, p + 6, and p + 8. -/
def IsPrimeQuadrupletStart (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + 2) ∧ Nat.Prime (p + 6) ∧ Nat.Prime (p + 8)

theorem main : {p : ℕ | IsPrimeQuadrupletStart p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_prime_quadruplets
