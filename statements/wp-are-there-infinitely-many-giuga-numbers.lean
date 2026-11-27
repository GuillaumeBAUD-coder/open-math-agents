import Mathlib

/-!
Are there infinitely many Giuga numbers?

Source: https://en.wikipedia.org/wiki/Giuga_number
Credit: @Tchikrazi

A Giuga number is a composite natural number n such that p divides n / p - 1
for every prime divisor p of n.
-/

namespace OMA.S_wp_are_there_infinitely_many_giuga_numbers

def IsGiugaNumber (n : ℕ) : Prop :=
  1 < n ∧ ¬ Nat.Prime n ∧
    ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ n / p - 1

theorem main : {n : ℕ | IsGiugaNumber n}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_giuga_numbers
