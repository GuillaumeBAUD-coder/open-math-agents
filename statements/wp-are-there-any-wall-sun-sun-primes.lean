import Mathlib

/-!
# Are there any Wall–Sun–Sun primes?

Source: https://en.wikipedia.org/wiki/Wall–Sun–Sun_prime
Credit: @John-A-McMahon

Source statement (Wikipedia, *Wall–Sun–Sun prime*): reduce the Fibonacci numbers modulo a prime
`p`; the resulting sequence is periodic, with period the Pisano period `π(p)`, and `p` divides
`F_{π(p)}`. A prime `p` is a Wall–Sun–Sun prime if `p ^ 2` also divides `F_{π(p)}`. The
definition applies to every prime (2 and 5 included). The open question asks whether any
Wall–Sun–Sun prime exists; it is stated here in its positive form. (Wikipedia adds the
conjecture that there are infinitely many; that is not part of this statement.)

`pisanoPeriod m` is the least `n > 0` with `F_n ≡ 0` and `F_{n+1} ≡ 1` modulo `m`, i.e. the
period of `(F_n mod m)`. For every prime `p` this set is nonempty, so the infimum is the period.
-/

namespace OMA.S_wp_are_there_any_wall_sun_sun_primes

/-- The Pisano period: the least positive `n` with `F_n ≡ 0 [MOD m]` and `F_{n+1} ≡ 1 [MOD m]`. -/
noncomputable def pisanoPeriod (m : ℕ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ Nat.fib n ≡ 0 [MOD m] ∧ Nat.fib (n + 1) ≡ 1 [MOD m]}

/-- A Wall–Sun–Sun prime: a prime `p` with `p ^ 2 ∣ F_{π(p)}`. -/
def IsWallSunSunPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ^ 2 ∣ Nat.fib (pisanoPeriod p)

theorem main : ∃ p : ℕ, IsWallSunSunPrime p := by
  sorry

end OMA.S_wp_are_there_any_wall_sun_sun_primes
