import Mathlib

/-!
# OEIS A156849: numbers k with k^2 ≡ 2 (mod 23^2)

Source: https://oeis.org/A156849
Credit: @SudharsanAnimations

The entry conjectured that the sequence satisfies
`a(n) = a(n-1) + a(n-2) - a(n-3)` and `a(n) = 529n/2 - 529/4 - 95(-1)^n/4`, and records that
"the conjecture is correct" (the terms are the numbers `≡ 156` or `373 (mod 529)`). We state both
parts of the proved conjecture.

Conventions: `a n` is the `n`-th number `k` with `k^2 ≡ 2 (mod 23^2)` in increasing order
(`Nat.nth`, offset 1). The closed form is multiplied by 4 to stay in `ℤ`:
`4 a(n) = 1058 n - 529 - 95 (-1)^n`. The recurrence is stated for `n ≥ 4`.
-/

namespace OMA.S_oeis_a156849

/-- The numbers `k` with `k^2 ≡ 2 (mod 23^2)`. -/
def P (k : ℕ) : Prop := k ^ 2 % 23 ^ 2 = 2

/-- `a n` (offset `1`): the `n`-th such number in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = a (n - 1) + a (n - 2) - a (n - 3)) ∧
    (∀ n : ℕ, 1 ≤ n → 4 * (a n : ℤ) = 1058 * n - 529 - 95 * (-1) ^ n) := by
  sorry

end OMA.S_oeis_a156849
