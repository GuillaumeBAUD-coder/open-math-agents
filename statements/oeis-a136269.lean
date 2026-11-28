import Mathlib

/-!
# A136269: Floor of sum of the first 10^n cube roots.

Source: https://oeis.org/A136269
Credit: @xor2k

Comment in the entry (the sequence is by Cino Hilliard, Mar 19 2008):
  Conjecture: For n = 3k, a(n) = (3/4)*10^(4n/3)+5*10^(n/3-1)-1.
The entry adds: The conjecture is true (see links) - Sela Fried, Oct 02 2024; and the example
  For n = 6, a(6) = (3/4)*10^8 + 5*10^1 - 1 = 75000049.

Conventions:
* Offset 0: a(n) = floor(sum_{i=1..10^n} i^(1/3)), the cube roots being real numbers
  (`Real.rpow` with exponent 1/3), so a(0) = 1.
* The conjecture is stated for n = 3k with k ≥ 1, as an equality in ℚ; with n = 3k the exponents
  are 4n/3 = 4k and n/3 - 1 = k - 1 (natural subtraction, exact for k ≥ 1).
* Range: the comment gives no range for k. For k = 0 the right-hand side is
  3/4 + 5/10 - 1 = 1/4, not an integer, while a(0) = 1, so the formula is meant for k ≥ 1 only
  (5*10^(n/3-1) is an integer exactly then); the case k = 0 is excluded here for that reason.

Numerical check: a Python copy of the definition (50-digit decimal arithmetic) gives
1, 16, 350, 7504, 161593, 3481214, 75000049 for n = 0..6, the DATA of the entry; the formula
gives 7504 for k = 1 and 75000049 for k = 2.
-/

namespace OMA.S_oeis_a136269

/-- A136269 (offset 0): floor of the sum of the cube roots of 1, ..., 10^n. -/
noncomputable def a (n : ℕ) : ℤ :=
  ⌊∑ i ∈ Finset.Icc (1 : ℕ) (10 ^ n), (i : ℝ) ^ ((1 : ℝ) / 3)⌋

/-- The conjecture: for n = 3k, k ≥ 1, a(n) = (3/4)*10^(4n/3) + 5*10^(n/3-1) - 1. -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    (a (3 * k) : ℚ) = 3 / 4 * 10 ^ (4 * k) + 5 * 10 ^ (k - 1) - 1 := by
  sorry

end OMA.S_oeis_a136269
