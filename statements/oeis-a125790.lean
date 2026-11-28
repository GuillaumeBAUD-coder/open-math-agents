import Mathlib

/-!
# A125790: Rectangular table where column k equals row sums of matrix power A078121^k, read by antidiagonals.

Source: https://oeis.org/A125790
Credit: @xor2k

Mikhail Kurkov, May 03 2025, in the formula section of A125790:
  Conjecture: g.f. for n-th row is
  (Sum_{i=0..n-1} x^i Sum_{j=0..i} binomial(n+1,j)*T(n,i-j)*(-1)^j)/(1-x)^(n+1) for n > 0.
This is the whole conjecture of the catalogue row (one claim); the later formulas of the entry
(Jan 07 2026, recursions for the columns) are not part of it.

Conventions:
* A125790 (offset 0) is a rectangular table T(n,k), n, k >= 0; its formula line reads:
  T(n,k) = T(n,k-1) + T(n-1,2*k) for n>0, k>0, with T(0,n)=T(n,0)=1 for n>=0. The definition
  below is this recurrence, the same definition as in the statement of A125792 (column 2).
* The table is read by antidiagonals as in the Mathematica program of the entry
  (T[n-k, k] for n >= 0, k = 0..n); `a m` is the m-th term of this reading, offset 0.
* The n-th row is k ↦ T(n,k), k >= 0, and its g.f. is Sum_{k>=0} T(n,k) x^k. The claim is stated
  as an identity of formal power series over ℤ for every n >= 1 (n > 0):
  (Sum_k T(n,k) X^k) * (1 - X)^(n+1) = Sum_{i=0..n-1} X^i * Sum_{j=0..i} binomial(n+1,j)*T(n,i-j)*(-1)^j.

Numerical check: a Python copy of the definition gives 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 10, 9, 4,
1, 1, 36, 35, 16, 5, ... for a(0), a(1), ...; compared with DATA: identical for the first 66 terms
(all terms of the entry). The claim was checked in Python for n <= 8 and all coefficients below 40.
-/

namespace OMA.S_oeis_a125790

/-- The table A125790: T(n,k) = T(n,k-1) + T(n-1,2k) for n, k > 0, T(0,k) = T(n,0) = 1. -/
def T : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | n + 1, k + 1 => T (n + 1) k + T n (2 * (k + 1))

/-- A125790 (offset 0): the table read by antidiagonals, T(d-k,k) for d >= 0, k = 0..d. -/
def a (m : ℕ) : ℕ :=
  let d := (Nat.sqrt (8 * m + 1) - 1) / 2
  let k := m - d * (d + 1) / 2
  T (d - k) k

/-- Kurkov's conjecture: the g.f. of the n-th row, for every n > 0. -/
theorem main : ∀ n : ℕ, 0 < n →
    PowerSeries.mk (fun k => (T n k : ℤ)) * (1 - PowerSeries.X) ^ (n + 1) =
      ∑ i ∈ Finset.range n, PowerSeries.X ^ i *
        ∑ j ∈ Finset.range (i + 1),
          ((n + 1).choose j : PowerSeries ℤ) * (T n (i - j) : PowerSeries ℤ) * (-1) ^ j := by
  sorry

end OMA.S_oeis_a125790
