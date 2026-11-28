import Mathlib

/-!
# A180710: a(n) = sigma(2^(n-1) * a(n-1)), a(1) = 1 (sigma(n) divides a(n))

Source: https://oeis.org/A180710 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A180710 (offset 1): a(n) = sigma(2^(n-1)*a(n-1)) for n>1 with a(1)=1;
data 1, 3, 28, 504, 26520, 3090528, ...

The entry records:

  Conjecture: sigma(n) | a(n) for n>=1.

Reading of the source:
* `sigma` is the sum of divisors, Mathlib's `ArithmeticFunction.sigma 1`.
* `a 1 = 1` and `a n = sigma(2^(n-1) * a(n-1))` for `n ≥ 2`. `a 0` is not part of the source; it
  is set to 0 and never used.
* The conjecture: `sigma(n)` divides `a(n)` for every `n ≥ 1`.
-/

namespace OMA.S_oeis_a180710

open ArithmeticFunction

/-- A180710: `a(1) = 1`, `a(n) = σ(2^(n-1) a(n-1))` for `n ≥ 2` (`a(0) = 0`, unused). -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => sigma 1 (2 ^ (n + 1) * a (n + 1))

/-- The conjecture: `σ(n) ∣ a(n)` for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → sigma 1 n ∣ a n := by
  sorry

end OMA.S_oeis_a180710
