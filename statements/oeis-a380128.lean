import Mathlib

/-!
# A380128: Triangle read by rows: Riordan array (1/(C(x)*sqrt(1-4*x)), x/C(x)) where C(x) is g.f. of A000108.

Source: https://oeis.org/A380128
Credit: @xor2k

Werner Schulte (Jan 12 2025, the author of the entry), in the formula section of A380128:
  Conjecture: T(n, k) = Sum_{i=0..n-k} (-1)^i * binomial(2*n - 2*k, n - k - i) * binomial(k + i, i).
(The entry adds: the conjecture is true, see the Fried link. - Sela Fried, Dec 05 2025.)
This is the complete conjecture of the row.

Conventions:
* C(x) = Sum_{i>=0} catalan(i)*x^i is the g.f. of the Catalan numbers A000108 (`catGF`), a formal
  power series over ℚ; 1/C(x) is its inverse as a power series (constant term 1).
* 1/sqrt(1-4*x) denotes the central binomial series B(x) = Sum_{i>=0} binomial(2i,i)*x^i (`cbGF`),
  the power series with constant term 1 and B(x)^2 * (1-4*x) = 1.
* The triangle (offset 0, rows n >= 0, columns 0 <= k <= n) is the Riordan array (g(x), f(x)) with
  g(x) = 1/(C(x)*sqrt(1-4*x)) and f(x) = x/C(x); by the usual convention its entry in row n,
  column k is the coefficient of x^n in g(x)*f(x)^k; below this is `T n k`.
* The formula is stated for all 0 <= k <= n, as an identity in ℚ.

Numerical check: a Python copy of the definition gives the rows 1; 1, 1; 3, 0, 1; 10, 1, -1, 1;
35, 4, 0, -2, 1; 126, 15, 1, 0, -3, 1; 462, 56, 5, 0, 1, -4, 1; ... compared with DATA: identical
for the first 78 terms (rows 0 to 11, all of DATA); the conjectured formula was checked for all
0 <= k <= n < 16.
-/

namespace OMA.S_oeis_a380128

/-- The g.f. of the Catalan numbers A000108, as a power series over ℚ. -/
noncomputable def catGF : PowerSeries ℚ := PowerSeries.mk (fun i => (catalan i : ℚ))

/-- The central binomial series Sum binomial(2i,i) x^i, that is 1/sqrt(1-4x). -/
noncomputable def cbGF : PowerSeries ℚ := PowerSeries.mk (fun i => (Nat.centralBinom i : ℚ))

/-- A380128: T(n,k), the coefficient of x^n in (1/(C(x)*sqrt(1-4x))) * (x/C(x))^k. -/
noncomputable def T (n k : ℕ) : ℚ :=
  PowerSeries.coeff n (catGF⁻¹ * cbGF * (PowerSeries.X * catGF⁻¹) ^ k)

/-- Schulte's conjecture: the explicit alternating binomial sum for T(n,k), 0 <= k <= n. -/
theorem main : ∀ n k : ℕ, k ≤ n → T n k = ∑ i ∈ Finset.range (n - k + 1),
    (-1 : ℚ) ^ i * ((2 * n - 2 * k).choose (n - k - i) : ℚ) * ((k + i).choose i : ℚ) := by
  sorry

end OMA.S_oeis_a380128
