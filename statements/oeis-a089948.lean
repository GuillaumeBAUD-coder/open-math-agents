import Mathlib

/-!
# A089948: Smallest prime factor of the concatenation of the first n odd primes.

Source: https://oeis.org/A089948
Credit: @darealpandaboi

Conjecture: beyond 3, the concatenation of the first n odd primes is always composite.

Translation notes.
* The odd primes are Nat.nth Nat.Prime k for k >= 1 (3, 5, 7, 11, ...). c n is the decimal
  concatenation of the first n of them: c 1 = 3, c 2 = 35, c 3 = 357, c 4 = 35711.
* Beyond 3 means n >= 2; c n >= 35 there, so composite is stated as not prime. The source says 3
  is the only prime among the first 10000 concatenations.
* This reproduces the listed data: the smallest prime factors of c 1, ..., c 12 are 3, 5, 3, 13,
  3, 23, 3, 11, 7, 13, 3, 137 (checked by computer).
-/

namespace OMA.S_oeis_a089948

/-- The concatenation of the decimal expansions of the first n odd primes. -/
noncomputable def c : ℕ → ℕ
  | 0 => 0
  | n + 1 => c n * 10 ^ (Nat.digits 10 (Nat.nth Nat.Prime (n + 1))).length + Nat.nth Nat.Prime (n + 1)

theorem main : ∀ n : ℕ, 2 ≤ n → ¬ (c n).Prime := by
  sorry

end OMA.S_oeis_a089948
