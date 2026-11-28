import Mathlib

/-!
# OEIS A196279: the order-11 recurrence a(n) = a(n-1) + a(n-10) - a(n-11)

Source: https://oeis.org/A196279
Credit: @SudharsanAnimations

Let `r = (7n) mod 10` and `x = ⌊7n/10⌋` be the last digit and leading part of `7n`; then
`a(n) = (x - 2r)/7`. R. J. Mathar conjectured (Oct 2011) that `a(n) = a(n-1) + a(n-10) - a(n-11)`,
with the corresponding rational g.f.; Charles R Greathouse IV recorded (Jan 2013) that the
conjecture is correct. We state the recurrence for all `n ≥ 11` (the g.f. is equivalent to it given
the initial terms).

Conventions: offset `0`; `x - 2r` is always divisible by 7, and `/` is integer division in `ℤ`.
-/

namespace OMA.S_oeis_a196279

/-- A196279: with `r = (7n) mod 10` the last digit and `x = ⌊7n/10⌋` the leading part of `7n`,
`a(n) = (x - 2r)/7` (an exact division). -/
def a (n : ℕ) : ℤ := (((7 * n / 10 : ℕ) : ℤ) - 2 * ((7 * n % 10 : ℕ) : ℤ)) / 7

theorem main : ∀ n : ℕ, 11 ≤ n → a n = a (n - 1) + a (n - 10) - a (n - 11) := by
  sorry

end OMA.S_oeis_a196279
