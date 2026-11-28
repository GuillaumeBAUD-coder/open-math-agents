import Mathlib

/-!
# OEIS A381005: the Pythagorean triangles are primitive

Source: https://oeis.org/A381005
Credit: @SudharsanAnimations

A381005 lists the short legs of the Pythagorean triangles with `a = 2^(4n) + 2^(2n+1)`,
`b = 2^(4n) - 2^(4n-2) - 2^(2n) - 1`, `c = 2^(4n) + 2^(4n-2) + 2^(2n) + 1` (`n ≥ 1`). It was
conjectured that these Pythagorean triangles are primitive; the entry records that this is true
(Chai Wah Wu, Feb 2025): they come from Euclid's formula with `x = 2^(2n)`, `y = 2^(2n-1) + 1`
coprime and of opposite parity. We state the proved result, together with `a^2 + b^2 = c^2`.

Conventions: primitive means `gcd(a, b, c) = 1`; natural-number subtraction in `b` does not
truncate for `n ≥ 1`.
-/

namespace OMA.S_oeis_a381005

/-- The legs and hypotenuse of the `n`-th triangle of A381005. -/
def a (n : ℕ) : ℕ := 2 ^ (4 * n) + 2 ^ (2 * n + 1)
def b (n : ℕ) : ℕ := 2 ^ (4 * n) - 2 ^ (4 * n - 2) - 2 ^ (2 * n) - 1
def c (n : ℕ) : ℕ := 2 ^ (4 * n) + 2 ^ (4 * n - 2) + 2 ^ (2 * n) + 1

/-- For every `n ≥ 1`, `(a, b, c)` is a Pythagorean triple and it is primitive. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n ^ 2 + b n ^ 2 = c n ^ 2 ∧ Nat.gcd (Nat.gcd (a n) (b n)) (c n) = 1 := by
  sorry

end OMA.S_oeis_a381005
