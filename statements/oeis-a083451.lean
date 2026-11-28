import Mathlib

/-!
# OEIS A083451: n concatenated n times exceeds n^n

Source: https://oeis.org/A083451
Credit: @SudharsanAnimations

`A083451(n) = (n concatenated n times) - n^n`. Amarnath Murthy conjectured that all terms are
positive for `n > 1`; the entry records that this is true (Hauke Worpel): the concatenation has
`n · (number of digits of n)` digits, more than `n^n` has. We state this proved result.

Conventions: "`n` concatenated `k` times" is the number whose decimal representation is that of
`n` repeated `k` times, i.e. `cat n (k + 1) = cat n k · 10^{d} + n` with `d` the number of decimal
digits of `n`; the difference is taken in `ℤ`. Offset `1` (`a(1) = 0`).
-/

namespace OMA.S_oeis_a083451

/-- The number of decimal digits of `n`. -/
def numDigits (n : ℕ) : ℕ := (Nat.digits 10 n).length

/-- `cat n k`: the decimal representation of `n` written `k` times in a row, read in base `10`
(`cat n 0 = 0`, `cat n (k + 1) = cat n k · 10^{numDigits n} + n`). -/
def cat (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cat n k * 10 ^ numDigits n + n

/-- `A083451(n) = (n concatenated n times) - n^n`. -/
def a (n : ℕ) : ℤ := (cat n n : ℤ) - (n : ℤ) ^ n

theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a083451
