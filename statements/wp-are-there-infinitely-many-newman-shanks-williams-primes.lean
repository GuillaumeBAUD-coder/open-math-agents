import Mathlib

/-!
Are there infinitely many Newman–Shanks–Williams primes?

Source: https://en.wikipedia.org/wiki/Newman–Shanks–Williams_prime
Credit: @Tchikrazi
-/

namespace OMA.S_wp_are_there_infinitely_many_newman_shanks_williams_primes

/-- The sequence S₀ = S₁ = 1 and Sₙ₊₂ = 2 Sₙ₊₁ + Sₙ. -/
def sequence : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * sequence (n + 1) + sequence n

/-- The prime values of S at odd indices are the NSW primes. -/
def IsNSWPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ m : ℕ, p = sequence (2 * m + 1)

theorem main : {p : ℕ | IsNSWPrime p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_newman_shanks_williams_primes
