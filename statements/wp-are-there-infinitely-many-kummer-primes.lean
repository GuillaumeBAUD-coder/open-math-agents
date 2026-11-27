import Mathlib

/-!
Are there infinitely many prime Kummer numbers?

Source: https://en.wikipedia.org/wiki/Euclid_number#Unsolved_problems
Credit: @Tchikrazi
-/

namespace OMA.S_wp_are_there_infinitely_many_kummer_primes

/-- The product of the first n primes, with the empty product equal to 1. -/
noncomputable def firstPrimesProduct (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

/-- A Kummer prime is prime and equals a primorial minus one. -/
def IsKummerPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ n : ℕ, 1 ≤ n ∧ p = firstPrimesProduct n - 1

theorem main : {p : ℕ | IsKummerPrime p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_kummer_primes
