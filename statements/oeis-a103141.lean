import Mathlib

/-!
# A103141: Riordan array (1/(1-x), x*(1 + x + x^2 + x^3)/(1-x)).

Source: https://oeis.org/A103141
Credit: @xor2k

Werner Schulte (Dec 2018), in the formula section of A103141:
  T(n,k) = Sum_{i=0..n-k} binomial(n-i,k) * (Sum_{j=0..i} binomial(k,j) * binomial(3*k-2*j,i-j) * (-2)^j)
  for 0 <= k <= n (conjectured).

Only this formula, the one marked as conjectured, is formalized; the other formulas of the same
comment (the column g.f., the Dirichlet g.f. and the two further double sums) are not part of
the statement.

Conventions:
* The triangle (offset 0, rows n >= 0, columns 0 <= k <= n) is the Riordan array (d(x), h(x)) with
  d(x) = 1/(1-x) and h(x) = x*(1 + x + x^2 + x^3)/(1-x). By the usual convention its entry in
  row n, column k is the coefficient of x^n in d(x)*h(x)^k; below this is `T n k`, a coefficient
  of a formal power series over ℚ. This agrees with the column g.f. of the entry,
  Sum_{n>=0} T(n+k,k)*x^n = (1+x+x^2+x^3)^k/(1-x)^(k+1).
* The right-hand side is an integer double sum, computed in ℤ and cast to ℚ. The binomials are
  `Nat.choose`. The upper index 3*k-2*j is a truncated natural subtraction; it is negative only
  for 2*j > 3*k, where j > k and the factor binomial(k,j) is 0, so the truncation does not change
  the value of the sum. The indices n-i and i-j are never negative in the ranges of summation.
* The claim is stated for all natural numbers k <= n.

Numerical check: a Python copy of the definition (truncated power series) gives the rows
1; 1, 1; 1, 3, 1; 1, 6, 5, 1; 1, 10, 15, 7, 1; 1, 14, 35, 28, 9, 1; 1, 18, 68, 84, 45, 11, 1;
1, 22, 116, 207, 165, 66, 13, 1 (the OEIS DATA is not available offline; these rows were not
compared with it, only with the column g.f. above), and the formula, with the truncated
subtraction as in Lean, agrees with it for all 0 <= k <= n <= 13.
-/

namespace OMA.S_oeis_a103141

open PowerSeries in
/-- A103141: T(n,k), the coefficient of x^n in (1/(1-x)) * (x*(1+x+x^2+x^3)/(1-x))^k. -/
noncomputable def T (n k : ℕ) : ℚ :=
  coeff n (((1 : ℚ⟦X⟧) - X)⁻¹ * (X * (1 + X + X ^ 2 + X ^ 3) * ((1 : ℚ⟦X⟧) - X)⁻¹) ^ k)

/-- Schulte's conjectured double sum for the entries of A103141. -/
theorem main : ∀ n k : ℕ, k ≤ n →
    T n k = ((∑ i ∈ Finset.range (n - k + 1), (Nat.choose (n - i) k : ℤ) *
      ∑ j ∈ Finset.range (i + 1),
        (Nat.choose k j : ℤ) * (Nat.choose (3 * k - 2 * j) (i - j) : ℤ) * (-2) ^ j : ℤ) : ℚ) := by
  sorry

end OMA.S_oeis_a103141
