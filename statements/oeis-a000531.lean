import Mathlib

/-!
# A000531: Maximum number of (2n + 1)-sided cyclic polygons with specified side lengths.

Source: https://oeis.org/A000531
Credit: @thatoneguy006

The conjecture stated here is the one the entry marks as such:

  (Conjecture) a(n)=2^(2*n)*sum_{k=1..n} cos(k*Pi/(2*n+1))^2*n. - L. Edson Jeffery, Jan 21 2012

Reading. The exponent `^2*n` is read as `^(2*n)`: with that reading the right-hand side equals
1, 7, 38, 187, 874, ... (the data), while `(cos(...)^2)*n` already gives 24 at n = 2.

The sequence. The name (the degree of Robbins' area polynomial of cyclic polygons) is not
formalized. The terms are given by the closed form a(n) = ((2n+1)!/(n!)^2 - 4^n)/2 of
Simon Norton (May 14 2001), which is exactly the PARI program of the entry
`a(n)=if(n<1,0,((2*n+1)!/n!^2-4^n)/2)`, with offset 1. It is evaluated in ℚ, where both
divisions are exact, so no truncation is involved.

Norton's informal conjectured definition (counting signings of 0 < a_1 < ... < a_{2n} < 1
with an odd sum) is not stated precisely enough in the source to be formalized, and the
quarter-plane walk interpretation of Arvind Ayyer is stated there as a fact, not as a
conjecture; neither is part of this statement.
-/

namespace OMA.S_oeis_a000531

/-- A000531(n) for n ≥ 1, by the entry's PARI program `((2*n+1)!/n!^2-4^n)/2`. -/
def a (n : ℕ) : ℚ :=
  (((2 * n + 1).factorial : ℚ) / ((n.factorial : ℚ) ^ 2) - 4 ^ n) / 2

/-- Jeffery's conjecture: a(n) = 2^(2n) Σ_{k=1}^{n} cos(kπ/(2n+1))^(2n) for all n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ((a n : ℚ) : ℝ) = 2 ^ (2 * n) *
      ∑ k ∈ Finset.Icc 1 n, Real.cos ((k : ℝ) * Real.pi / (2 * (n : ℝ) + 1)) ^ (2 * n) := by
  sorry

end OMA.S_oeis_a000531
