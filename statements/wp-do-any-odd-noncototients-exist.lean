import Mathlib

/-!
Do any odd noncototients exist?

Source: https://en.wikipedia.org/wiki/Noncototient
Credit: @Tchikrazi
-/

namespace OMA.S_wp_do_any_odd_noncototients_exist

/-- A positive integer n is a noncototient if no positive m has m − φ(m) = n. -/
def IsNoncototient (n : ℕ) : Prop :=
  0 < n ∧ ¬ ∃ m : ℕ, 0 < m ∧ m - Nat.totient m = n

theorem main : ∃ n : ℕ, Odd n ∧ IsNoncototient n := by
  sorry

end OMA.S_wp_do_any_odd_noncototients_exist
