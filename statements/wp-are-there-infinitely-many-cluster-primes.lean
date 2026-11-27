import Mathlib

/-!
# Are there infinitely many cluster primes?

Source: https://en.wikipedia.org/wiki/cluster_prime
Credit: @caa1982

An odd prime `p` is a cluster prime if every positive even integer `k ≤ p - 3` can be written
as the difference of two primes not exceeding `p`. By convention, `2` is not a cluster prime.
Paul Erdős asked whether there are infinitely many cluster primes.
-/

namespace OMA.S_wp_are_there_infinitely_many_cluster_primes

/-- An odd prime `p` is a cluster prime if every positive even integer `k ≤ p - 3` is the
difference `q₁ - q₂` of two primes `q₁, q₂ ≤ p`. By convention, `2` is excluded. -/
def IsClusterPrime (p : ℕ) : Prop :=
  p.Prime ∧ Odd p ∧
    ∀ k : ℕ, 0 < k → Even k → k ≤ p - 3 →
      ∃ q₁ q₂ : ℕ, q₁.Prime ∧ q₂.Prime ∧ q₁ ≤ p ∧ q₂ ≤ p ∧ q₂ + k = q₁

theorem main : Set.Infinite {p : ℕ | IsClusterPrime p} := by
  sorry

end OMA.S_wp_are_there_infinitely_many_cluster_primes
