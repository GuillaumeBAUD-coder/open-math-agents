import Mathlib

/-!
Are there infinitely many cluster primes?

Source: https://en.wikipedia.org/wiki/Cluster_prime
Credit: @Tchikrazi
-/

namespace OMA.S_wp_are_there_infinitely_many_cluster_primes

/-- A cluster prime is an odd prime p such that every positive even k ≤ p − 3
is the difference of two primes no larger than p. -/
def IsClusterPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ p ≠ 2 ∧
    ∀ k : ℕ, 0 < k → Even k → k ≤ p - 3 →
      ∃ a b : ℕ, Nat.Prime a ∧ Nat.Prime b ∧ a ≤ p ∧ b ≤ p ∧ b ≤ a ∧ a - b = k

theorem main : {p : ℕ | IsClusterPrime p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_cluster_primes
