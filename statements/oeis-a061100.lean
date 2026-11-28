import Mathlib

/-!
# OEIS A061100: Squares with digital root 4

Source: https://oeis.org/A061100
Credit: @SudharsanAnimations

Colin Barker (Feb 2013) conjectured the closed form a(n) = (16-72n+81n^2)/4 for n even and
a(n) = (25-90n+81n^2)/4 for n odd (and the rational g.f.
`-x(4x^4+45x^3+64x^2+45x+4)/((x-1)^3(x+1)^2)`); Robert Israel noted it is true because
`x^2 ≡ 4 (mod 9)` iff `x ≡ 2, 7 (mod 9)`. We state the closed form, written as `(9n-4)^2/4` and
`(9n-5)^2/4` (the same numbers) to avoid natural-number subtraction; the g.f. is equivalent.

Conventions: the digital root is defined literally (replace a number by its decimal digit sum
until it is below 10); `a n` is the `n`-th such square in increasing order (`Nat.nth`, offset 1),
and `/` is natural-number division (exact here).
-/

namespace OMA.S_oeis_a061100

/-- The digital root: repeatedly replace a number by the sum of its decimal digits until a
single digit remains. -/
def digitalRoot (m : ℕ) : ℕ :=
  if _h : m < 10 then m else digitalRoot (Nat.digits 10 m).sum
termination_by m
decreasing_by
  rw [Nat.digits_def' (by norm_num) (by omega), List.sum_cons]
  have := Nat.digit_sum_le 10 (m / 10)
  omega

/-- Squares with digital root 4. -/
def P (m : ℕ) : Prop := IsSquare m ∧ digitalRoot m = 4

/-- `a n` (offset `1`): the `n`-th square with digital root 4, in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

theorem main : ∀ n : ℕ, 1 ≤ n →
    (Even n → a n = (9 * n - 4) ^ 2 / 4) ∧ (Odd n → a n = (9 * n - 5) ^ 2 / 4) := by
  sorry

end OMA.S_oeis_a061100
