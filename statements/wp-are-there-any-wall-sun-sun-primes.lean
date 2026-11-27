import Mathlib

/-!
# Are there any Wall–Sun–Sun primes?

Source: https://en.wikipedia.org/wiki/Wall–Sun–Sun_prime
Credit: @Spenz90

A Wall–Sun–Sun prime is a prime `p` such that `p ^ 2` divides the Fibonacci
number `F_{π(p)}`, where `π(p)` is the Pisano period of `p`. Wikipedia gives
the equivalent characterization used below: for a prime `p`, `p` is a
Wall–Sun–Sun prime if and only if `p ^ 2` divides `F_{p - (5/p)}`, where
`(5/p)` is the Legendre symbol. No Wall–Sun–Sun prime is known; the open
question stated here is whether any exist.
-/

namespace OMA.S_wp_are_there_any_wall_sun_sun_primes

/-- A prime `p` is a Wall–Sun–Sun prime if `p ^ 2` divides the Fibonacci
number `F_{p - (5/p)}`, where `(5/p)` is the Legendre symbol. -/
def IsWallSunSunPrime (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  p ^ 2 ∣ Nat.fib ((p : ℤ) - legendreSym p 5).toNat

/-- The open question: does a Wall–Sun–Sun prime exist? -/
theorem main : ∃ p : ℕ, ∃ hp : p.Prime, IsWallSunSunPrime p hp := by
  sorry

end OMA.S_wp_are_there_any_wall_sun_sun_primes
