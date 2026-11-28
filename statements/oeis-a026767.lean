import Mathlib

/-!
# OEIS A026767: Mathar's recurrence for the partial sums of the row sums of the array A026758

Source: https://oeis.org/A026767 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A026767 (Clark Kimberling), offset 0: a(n) = Sum_{i=0..n} Sum_{j=0..n} T(i,j), T given by A026758.
Formula section:
Conjecture: (n+1)*a(n) +(-n-3)*a(n-1) +2*(-5*n+4)*a(n-2) +2*(5*n+3)*a(n-3) +(29*n-83)*a(n-4) +(-29*n+61)*a(n-5) +10*(-2*n+11)*a(n-6) +20*(n-5)*a(n-7)=0. - R. J. Mathar, Jun 30 2013

A026758 (Clark Kimberling): Triangular array T read by rows: T(n,0)=T(n,n)=1 for n >= 0; for n >= 2 and 1 <= k <= n-1, T(n,k) = T(n-1,k-1) + T(n-2,k-1) + T(n-1,k) if n is odd and 1 <= k <= (n-1)/2, else T(n,k) = T(n-1,k-1) + T(n-1,k).

Formalization notes:
* T(n, k) is defined for 0 <= k <= n by the rule of A026758 and is 0 outside the row; the
  definition reproduces the array's data.
* a(n) = the sum of T(i, j) over 0 <= i <= n and 0 <= j <= n for n >= 0, the entry's name and
  offset. The block gives no range for the recurrence, so it is stated for every n >= 7, the
  smallest n for which a(n - 7) is a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 3, 7, 16, 34, 75, ... from n = 0); the proof file
  proves all 29 listed terms as controls.
-/

namespace OMA.S_oeis_a026767

/-- A026758 T(n, k), 0 <= k <= n: T(n, 0) = T(n, n) = 1, and for n >= 2 and 1 <= k <= n - 1,
T(n, k) = T(n-1, k-1) + T(n-2, k-1) + T(n-1, k) if n is odd and k <= (n-1)/2, and
T(n, k) = T(n-1, k-1) + T(n-1, k) otherwise (0 beyond the row). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | n + 2, k =>
    if n + 2 < k then 0
    else if k = 0 ∨ k = n + 2 then 1
    else if n % 2 = 1 ∧ k ≤ (n + 1) / 2 then T (n + 1) (k - 1) + T n (k - 1) + T (n + 1) k
    else T (n + 1) (k - 1) + T (n + 1) k

/-- A026767: a(n) = the sum of T(i, j) over 0 <= i <= n and 0 <= j <= n. -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), T i j

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
      ((n : ℤ) + 1) * (a n : ℤ) + (-(n : ℤ) - 3) * (a (n - 1) : ℤ) + 2 * (-5 * (n : ℤ) + 4) * (a (n - 2) : ℤ) + 2 * (5 * (n : ℤ) + 3) * (a (n - 3) : ℤ) + (29 * (n : ℤ) - 83) * (a (n - 4) : ℤ) + (-29 * (n : ℤ) + 61) * (a (n - 5) : ℤ) + 10 * (-2 * (n : ℤ) + 11) * (a (n - 6) : ℤ) + 20 * ((n : ℤ) - 5) * (a (n - 7) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a026767
