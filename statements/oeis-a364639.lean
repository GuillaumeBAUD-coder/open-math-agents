import Mathlib

/-!
# A364639: Irregular triangle read by rows: T(n,k) = A237591(n,k) - A237591(n-1,k).

Source: https://oeis.org/A364639
Credit: @xor2k

Omar E. Pol, in the comment section of A364639:
  Conjecture: column k gives 1 together with period A002378(k) repeat Sk, where Sk is the k-th row
  of the triangle A364746.

Conventions:
* A237591 is the irregular triangle with rows n ≥ 1 and columns 1 ≤ k ≤ r(n), where
  r(n) = A003056(n) = floor((sqrt(8n+1)-1)/2), that is, k(k+1)/2 ≤ n. It is taken through the
  formula of that entry, A237591(n,k) = A235791(n,k) - A235791(n,k+1) with
  A235791(n,k) = ceiling((n+1)/k - (k+1)/2) (`c n k`, ceiling of a rational number).
  Entries outside the triangle count as 0 (`A n k`); this matters only for the first term of each
  column of A364639, where row n-1 of A237591 has no column k.
* `T n k` is A364639(n,k) for n ≥ 1, 1 ≤ k ≤ r(n). Column k starts in row A000217(k) = k(k+1)/2.
* A002378(k) = k(k+1). A364746 is the irregular triangle whose row k has k(k+1) terms, in k
  blocks of k+1 terms: the m-th block (1 ≤ m ≤ k) lists k-m zeros, then 1, then m-1 zeros, and
  its last term is -1, except in the k-th block where the last term is 0. `S k j` is the term of
  row k at position j counted from 0 (0 ≤ j < k(k+1)): block index j / (k+1) = m-1 and position
  j % (k+1) inside the block.
* The claim stated is: the first term of column k is 1, and the terms after it are infinitely many
  copies of row k of A364746, i.e. T(k(k+1)/2 + 1 + i, k) = S(k, i mod k(k+1)) for all i ≥ 0.

Numerical check: a Python copy of the definition gives the rows of `A`
  1; 2; 2, 1; 3, 1; 3, 2; 4, 1, 1; 4, 2, 1; 5, 2, 1; 5, 2, 2; 6, 2, 1, 1; ...
and the first 20 terms of `T`, read by rows,
  1, 1, 0, 1, 1, 0, 0, 1, 1, -1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1.
The formula for A237591 and its data are quoted from memory of the entries (no access to the
OEIS when this was written); they agree with the remarks of H. F. W. Hoft in A237591 and A364639
(row sums n, column k of A237591 starts in row k(k+1)/2 with k ones, all terms of A364639 in
{-1, 0, 1}, periodic sections start with k-1 zeros and end with k zeros), checked for k ≤ 8.
The block rule of A364746 is the one of that entry; `S` gives for rows 1, 2, 3, ...
  1, 0, 0, 1, -1, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, -1, 1, 0, 0, 0, ...
and the stated identity was checked in Python for k ≤ 8 and 30 periods.
-/

namespace OMA.S_oeis_a364639

/-- A235791(n,k) = ceiling((n+1)/k - (k+1)/2). -/
def c (n k : ℕ) : ℤ := ⌈((n : ℚ) + 1) / k - ((k : ℚ) + 1) / 2⌉

/-- A237591(n,k) for 1 ≤ k and k(k+1)/2 ≤ n, and 0 outside the triangle. -/
def A (n k : ℕ) : ℤ := if 1 ≤ k ∧ k * (k + 1) ≤ 2 * n then c n k - c n (k + 1) else 0

/-- A364639(n,k) = A237591(n,k) - A237591(n-1,k). -/
def T (n k : ℕ) : ℤ := A n k - A (n - 1) k

/-- A364746, row k, position j counted from 0 (0 ≤ j < k(k+1)). -/
def S (k j : ℕ) : ℤ :=
  if j % (k + 1) + j / (k + 1) + 1 = k then 1
  else if j % (k + 1) = k ∧ j / (k + 1) + 1 < k then -1
  else 0

/-- Pol's conjecture: column k (which starts in row k(k+1)/2) is 1 followed by infinitely many
copies of row k of A364746. -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    T (k * (k + 1) / 2) k = 1 ∧
    ∀ i : ℕ, T (k * (k + 1) / 2 + 1 + i) k = S k (i % (k * (k + 1))) := by
  sorry

end OMA.S_oeis_a364639
