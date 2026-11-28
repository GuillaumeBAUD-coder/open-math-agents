import Mathlib

/-!
# A216094: a(n+1) = a(n) + |second difference of the primes| + 2 (a(n) ~ prime(n))

Source: https://oeis.org/A216094 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A216094 (offset 1): a(1) = 2; a(n+1) = a(n) + |A036263(n)| + 2, that is
a(n+1) = a(n) + |prime(n+2) - 2*prime(n+1) + prime(n)| + 2; data 2, 5, 7, 11, 15, 19, 23, ...

The entry records:

  The probabilistic primes model.
  Conjecture: a(n) ~ prime(n).

Reading of the source:
* `prime n` is the `n`-th prime with `prime 1 = 2` (`Nat.nth Nat.Prime (n - 1)`); the second
  difference `prime(n+2) - 2 prime(n+1) + prime(n)` is an integer and its absolute value is
  taken (`Int.natAbs`).
* `a 1 = 2`, `a (n+1) = a n + |...| + 2` for `n ≥ 1`; `a 0` is not part of the source and is set
  to 0 (unused).
* `a(n) ~ prime(n)` is asymptotic equivalence (`~[atTop]`) as `n → ∞` over the naturals.
-/

namespace OMA.S_oeis_a216094

open Asymptotics Filter

/-- `prime n`: the `n`-th prime, with `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A216094: `a(1) = 2`, `a(n+1) = a(n) + |prime(n+2) - 2 prime(n+1) + prime(n)| + 2`. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | n + 2 => a (n + 1) +
      ((prime (n + 3) : ℤ) - 2 * prime (n + 2) + prime (n + 1)).natAbs + 2

/-- The conjecture: `a(n) ~ prime(n)`. -/
theorem main : (fun n : ℕ => (a n : ℝ)) ~[atTop] (fun n : ℕ => (prime n : ℝ)) := by
  sorry

end OMA.S_oeis_a216094
