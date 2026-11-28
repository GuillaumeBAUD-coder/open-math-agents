import Mathlib

/-!
# A281260: Triangular array of generalized Narayana numbers T(n,k) = 2*binomial(n+1,k)*binomial(n-2,k-1)/(n+1) for n >= 1 and 0 <= k <= n-1, read by rows.

Source: https://oeis.org/A281260
Credit: @xor2k

Werner Schulte (author of the entry, Jan 18 2017), in the comment section of A281260:
  Conjecture: Sum_{k=1..n-m} binomial(n+1-k,m) * N_m(n,k) * A103365(n+1-m-k)
    = (m+1)^2 * A000007(n-m-1) for n > m >= 0.
This is the only conjecture of the entry and it is stated completely (all m >= 0 and all n > m).

Conventions:
* `N m n k` are the generalized Narayana numbers of the first comment of the entry,
  N_m(n,k) := (m+1)/(n+1)*binomial(n+1,k)*binomial(n-m-1,k-1) for m >= 0, n >= m and
  0 <= k <= n-m, with N_m(n,0) = A000007(n-m). The division is a division in ℚ (the values are
  integers). For k >= 1 (the only case that occurs in the conjecture, where moreover n > m) the
  natural subtractions n - m - 1 and k - 1 are genuine.
* The sequence of the entry is the case m = 1: `T n k = N 1 n k` for n >= 1 and 0 <= k <= n-1,
  read by rows (offset 1).
* `nar n k` is the Narayana triangle A001263, T(n,k) = C(n-1,k-1)*C(n,k-1)/k for 1 <= k <= n, with
  the division in ℚ (the values are integers).
* `c` is A103365 (offset 1): the first column of the matrix inverse of the
  Narayana triangle A001263. The Narayana triangle is lower triangular with diagonal entries 1, so
  the first column c(1), c(2), ... of its inverse is the unique solution of
  Sum_{j=1..N} nar(N,j)*c(j) = [N = 1] for all N >= 1, that is
  c(N) = [N = 1] - Sum_{j=1..N-1} nar(N,j)*c(j). This is the recursion used below, written with
  N + 1 in place of N and j = i + 1; `c 0 = 0` is a junk value that is never used. The values are
  integers; they are kept in ℚ because `nar` is.
* A000007(j) = 0^j is written as `if j = 0 then 1 else 0`; in the statement n > m, so the natural
  subtraction n - m - 1 is genuine, and so are n + 1 - k and n + 1 - m - k for 1 <= k <= n - m.
* The identity is stated in ℚ.

Numerical check (Python copy of the definitions, exact rational arithmetic):
* `T n k` for n = 1..12, k = 0..n-1 gives 1, 0, 2, 0, 2, 3, 0, 2, 8, 4, 0, 2, 15, 20, 5, 0, 2, 24,
  60, 40, 6, 0, 2, 35, 140, 175, 70, 7, ...; compared with DATA of A281260: identical for the
  first 72 terms (all terms of the DATA field).
* `c 1, c 2, ...` gives 1, -1, 2, -7, 39, -321, 3681, -56197, 1102571, -27036487, 810263398,
  -29139230033, 1238451463261, -61408179368043, 3513348386222286, -229724924077987509,
  17023649385410772579, -1419220037471837658603, 132236541042728184852942,
  -13690229149108218523467549; compared with DATA of A103365: identical for the first 20 terms
  (all terms of the DATA field).
* The conjectured identity was checked for all 0 <= m <= 6 and m < n <= 19.
-/

namespace OMA.S_oeis_a281260

/-- Generalized Narayana numbers N_m(n,k) = (m+1)/(n+1)*C(n+1,k)*C(n-m-1,k-1), with
N_m(n,0) = A000007(n-m). -/
def N (m n k : ℕ) : ℚ :=
  if k = 0 then (if n = m then 1 else 0)
  else ((m : ℚ) + 1) / ((n : ℚ) + 1) * (Nat.choose (n + 1) k : ℚ) * (Nat.choose (n - m - 1) (k - 1) : ℚ)

/-- A281260 (offset 1, row n >= 1, 0 <= k <= n-1): the case m = 1,
T(n,k) = 2*C(n+1,k)*C(n-2,k-1)/(n+1). -/
def T (n k : ℕ) : ℚ := N 1 n k

/-- A001263, the Narayana triangle: T(n,k) = C(n-1,k-1)*C(n,k-1)/k for 1 <= k <= n. -/
def nar (n k : ℕ) : ℚ :=
  (Nat.choose (n - 1) (k - 1) : ℚ) * (Nat.choose n (k - 1) : ℚ) / (k : ℚ)

/-- A103365 (offset 1): first column of the matrix inverse of the Narayana triangle,
c(N) = [N = 1] - Sum_{j=1..N-1} nar(N,j)*c(j). -/
def c : ℕ → ℚ
  | 0 => 0
  | n + 1 => (if n = 0 then 1 else 0) - ∑ i : Fin n, nar (n + 1) (i.val + 1) * c (i.val + 1)
decreasing_by exact Nat.succ_lt_succ i.isLt

/-- Schulte's conjecture: Sum_{k=1..n-m} C(n+1-k,m) * N_m(n,k) * A103365(n+1-m-k)
= (m+1)^2 * A000007(n-m-1) for n > m >= 0. -/
theorem main : ∀ m n : ℕ, m < n →
    ∑ k ∈ Finset.Icc 1 (n - m),
        (Nat.choose (n + 1 - k) m : ℚ) * N m n k * c (n + 1 - m - k)
      = ((m : ℚ) + 1) ^ 2 * (if n - m - 1 = 0 then 1 else 0) := by
  sorry

end OMA.S_oeis_a281260
