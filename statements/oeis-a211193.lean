import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs

namespace OMA.S_oeis_a211193

/-- Coefficients of the formal exponential `exp(f)` for a power series `f` with `f 0 = 0`,
given by `E(0) = 1` and `(n + 1) * E(n + 1) = ∑_{j=0}^n (j + 1) * f(j + 1) * E(n - j)`. -/
def expCoeff (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
    (∑ j : Fin (n + 1), ((j.val + 1 : ℕ) : ℚ) * f (j.val + 1) * expCoeff f (n - j.val)) /
      ((n + 1 : ℕ) : ℚ)

/-- Power series coefficients of `(1 + x) * log(1 + x) = x + ∑_{k ≥ 2} (-1)^k / (k * (k - 1)) * x^k`. -/
def uCoeff : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | n + 2 => (-1 : ℚ) ^ n / (((n + 2 : ℕ) : ℚ) * ((n + 1 : ℕ) : ℚ))

/-- Power series coefficients of `(1 + x)^(1 + x) - 1 = exp((1 + x) * log(1 + x)) - 1`. -/
def gCoeff : ℕ → ℚ
  | 0 => 0
  | n + 1 => expCoeff uCoeff (n + 1)

/-- `a(n)` (OEIS A211193): `n! * [x^n] exp((1 + x)^(1 + x) - 1)`. -/
def a (n : ℕ) : ℚ :=
  (Nat.factorial n : ℚ) * expCoeff gCoeff n

/-- Conjecture (OEIS A211193): for every `n > 1`, `a(n)` is an integer congruent to `1 (mod n)`. -/
theorem main : ∀ n : ℕ, 1 < n → ∃ k : ℤ, a n = ((k * (n : ℤ) + 1 : ℤ) : ℚ) := by
  sorry

end OMA.S_oeis_a211193
