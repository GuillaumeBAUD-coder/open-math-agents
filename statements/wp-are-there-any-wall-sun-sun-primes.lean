import Mathlib

/-!
# Are there any Wall–Sun–Sun primes?

Source: https://en.wikipedia.org/wiki/Wall–Sun–Sun_prime
Credit: @caa1982

Let $p$ be a prime. Reducing the Fibonacci numbers $F_n$ modulo $p$ gives a periodic sequence;
its minimal period is the Pisano period $\pi(p)$. Since $F_0 = 0$, $p$ divides $F_{\pi(p)}$.
A prime $p$ such that $p^2$ divides $F_{\pi(p)}$ is called a Wall–Sun–Sun prime (or
Fibonacci–Wieferich prime). Wall–Sun–Sun primes are conjectured to exist (indeed infinitely many),
although none are known.

The Pisano period is stated as the least positive `k` with `F (n + k) ≡ F n (mod p)` for every `n`.
For every `p ≥ 1` such a `k` exists (the sequence of pairs `(F n, F (n+1)) mod p` takes finitely many
values and the recursion can be run backwards), so the infimum below is a genuine minimum and is
positive; it is never the default value `0` of an empty infimum.
-/

namespace OMA.S_wp_are_there_any_wall_sun_sun_primes

/-- The Pisano period $\pi(p)$: the minimal period of the sequence $F_n \bmod p$. -/
noncomputable def pisanoPeriod (p : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ ∀ n : ℕ, Nat.fib (n + k) % p = Nat.fib n % p}

/-- A Wall–Sun–Sun prime: a prime `p` with `p ^ 2 ∣ F_{π(p)}`. -/
def IsWallSunSunPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ^ 2 ∣ Nat.fib (pisanoPeriod p)

/-- Conjecture: there exists a Wall–Sun–Sun prime. -/
theorem main : ∃ p : ℕ, IsWallSunSunPrime p := by
  sorry

end OMA.S_wp_are_there_any_wall_sun_sun_primes
