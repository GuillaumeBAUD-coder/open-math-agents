import Mathlib

/-!
Are there any Wall–Sun–Sun primes?

Source: https://en.wikipedia.org/wiki/Wall%E2%80%93Sun%E2%80%93Sun_prime
Credit: @Tchikrazi
-/

namespace OMA.S_wp_are_there_any_wall_sun_sun_primes

/-- The Lucas numbers L₀ = 2, L₁ = 1, Lₙ₊₂ = Lₙ₊₁ + Lₙ. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- Equivalent characterization: p is prime and Lₚ ≡ 1 mod p². -/
def IsWallSunSunPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ lucas p % (p ^ 2) = 1

theorem main : ∃ p : ℕ, IsWallSunSunPrime p := by
  sorry

end OMA.S_wp_are_there_any_wall_sun_sun_primes
