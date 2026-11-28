import Mathlib

/-!
# A045575: Nonnegative numbers of the form x^y - y^x, for x,y > 1.

Source: https://oeis.org/A045575
Credit: @bear20252026

The conjecture of Hans Havermann (2023-06-12): for every `d > 11`, the largest
term with exactly `d` decimal digits among the nonnegative numbers of the form
`x ^ y - y ^ x` with `x, y > 1` is `10 ^ d - d ^ 10`.
-/

namespace OMA.S_oeis_a045575

/-- The nonnegative integers of the form `x ^ y - y ^ x` with `x, y > 1`. -/
def terms : Set ℕ :=
  {n | ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ (x : ℤ) ^ y - (y : ℤ) ^ x = (n : ℤ)}

/-- A natural number has exactly `d` decimal digits. -/
def HasDecimalDigits (t d : ℕ) : Prop :=
  10 ^ (d - 1) ≤ t ∧ t < 10 ^ d

/-- For every `d > 11`, `10 ^ d - d ^ 10` is a term with exactly `d` decimal
digits, and no `d`-digit term exceeds it. -/
theorem main :
    ∀ d : ℕ, 11 < d →
      (10 ^ d - d ^ 10) ∈ terms ∧
      HasDecimalDigits (10 ^ d - d ^ 10) d ∧
      ∀ t ∈ terms, HasDecimalDigits t d → t ≤ 10 ^ d - d ^ 10 := by
  sorry

end OMA.S_oeis_a045575
