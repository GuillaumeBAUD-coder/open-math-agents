import Mathlib

/-!
# Cousin primes cannot take these forms

Source: https://mathoverflow.net/questions/513625
Credit: Sudharsan Rajendiran

For positive integers `x, y` consider the four forms
`k1 = 12xy - 2x - 2y + 1`, `k2 = 12xy + 2x + 2y + 1`, `k3 = 12xy + 2x - 2y - 1` and
`k4 = 12xy - 2x + 2y - 1`. The question asks whether the odd numbers not of any of these forms,
multiplied by `3`, are exactly the averages of two cousin primes (primes `p` and `p + 4`), that
is, whether for odd `n` the numbers `3n - 2` and `3n + 2` are both prime precisely when `n` is
not of the form `k1`, `k2`, `k3` or `k4`.

We prove this for every odd `n ≥ 3` (for `n = 1` it fails, as `3 · 1 - 2 = 1` is not prime; for
even `n` both `3n ∓ 2` are even). The reason is that `3 k1 - 2 = (6x - 1)(6y - 1)`,
`3 k2 - 2 = (6x + 1)(6y + 1)`, `3 k3 + 2 = (6x - 1)(6y + 1)` and `3 k4 + 2 = (6x + 1)(6y - 1)`.

Conventions:
- `n` is a natural number; since `n ≥ 3`, the truncated subtraction `3 * n - 2` is the true value.
- The four forms are written over `ℤ` with `x, y : ℤ`, `1 ≤ x`, `1 ≤ y`, and compared with the
  cast `(n : ℤ)`.
-/

namespace OMA.S_mo_513625

/-- `n` is of one of the four forms `12xy ∓ 2x ∓ 2y ± 1` from the question, with `x, y ≥ 1`. -/
def IsForm (n : ℕ) : Prop :=
  ∃ x y : ℤ, 1 ≤ x ∧ 1 ≤ y ∧
    ((n : ℤ) = 12 * x * y - 2 * x - 2 * y + 1 ∨ (n : ℤ) = 12 * x * y + 2 * x + 2 * y + 1 ∨
      (n : ℤ) = 12 * x * y + 2 * x - 2 * y - 1 ∨ (n : ℤ) = 12 * x * y - 2 * x + 2 * y - 1)

theorem main : ∀ n : ℕ, Odd n → 3 ≤ n →
    ((3 * n - 2).Prime ∧ (3 * n + 2).Prime ↔ ¬ IsForm n) := by
  sorry

end OMA.S_mo_513625
