import Mathlib

/-!
# OEIS A000382: restricted permutations

Source: https://oeis.org/A000382
Credit: @sassmama27
-/

namespace OMA.S_oeis_a000382

/-- The row vector after repeated multiplication by the matrix in the
OEIS entry's Mathematica formula. -/
def rowAfter : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (11, 7, 4, 2)
  | k + 1 =>
    let (a, b, c, d) := rowAfter k
    (2 * a - d, a, b, c)

/-- The published sequence starts at index 4. The zero values below
that index follow the extension used by the Mathematica formula. -/
def sequence (n : ℕ) : ℤ :=
  if n < 4 then 0 else if n = 4 then 6 else (rowAfter (n - 2)).2.2.2

/-- All three predecessor indices are in the published range for n ≥ 7. -/
theorem main (n : ℕ) (hn : 7 ≤ n) :
    sequence n = sequence (n - 1) + sequence (n - 2) + sequence (n - 3) - 2 := by
  sorry

end OMA.S_oeis_a000382
