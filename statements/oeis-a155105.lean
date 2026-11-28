import Mathlib

/-!
# A155105: Positive numbers appearing in the third column of A155103.

Source: https://oeis.org/A155105
Credit: @xor2k

Tristan Cam (Oct 02 2024), in the formula section of A155105:
  a(1) = 1, a(n) = a(n-1)*(1+3*2^(n-2)) (conjectured).
  a(n) = Product_{k=1..n-1} 1+3*2^(k-1) = QPochhammer[-3, 2, n-1]. (conjectured).
Both conjectured formulas are stated, as one conjunction. QPochhammer[-3, 2, n-1] is the
Mathematica name of the very product Product_{k=1..n-1} (1+3*2^(k-1)), so that equality only unfolds
a name and is not a separate claim.

Definitions (taken from the entries A155102, A155103, A155105; rows and columns are numbered from 1):
* A155102 is the infinite lower triangular matrix `T`: T(n,k) = 1 if n = k, T(n,k) = -(k+1) if
  n = 2*k, and T(n,k) = 0 otherwise.
* A155103 is the matrix inverse of A155102. `T` is lower triangular with diagonal 1, so its inverse
  is the unique lower triangular matrix `B` with Sum_{k=m..n} T(n,k)*B(k,m) = [n = m] for all
  1 ≤ m ≤ n (the sums are finite because both matrices are lower triangular). As T(n,n) = 1, this
  equation is the same as
    B(n,m) = [n = m] - Sum_{k=m..n-1} T(n,k)*B(k,m),
  which determines B row by row, and this recursion is taken as the definition of `B`. It is
  literally the recursion of the Maple and PARI programs of the entry A155105
  (a[r,c] := -add(a[cp,c]*A155102(r,cp), cp=c..r-1)/A155102(r,r), with a[r,r] = 1 and zeros
  above the diagonal). The inverse of an integer matrix with diagonal 1 has integer entries, so
  `B` is defined with values in ℤ. For n < m the definition gives 0. The index 0 is never used for
  the third column (the sum runs over m ≤ k < n with m = 3).
* A155105 lists the positive numbers of the third column of A155103 in the order of the rows, as
  the programs of the entry print them (they print the entries a[r,3] ≠ 0 for r = 1, 2, 3, ...;
  all entries of that column are ≥ 0, so nonzero and positive select the same entries). With offset 1,
  a(n) is the entry B(r,3) in the n-th row r (in increasing order) with B(r,3) > 0, i.e.
  r = `Nat.nth (fun r => 0 < B r 3) (n - 1)`.

Conventions: the recurrence a(n) = a(n-1)*(1+3*2^(n-2)) is stated for every n ≥ 2 (for n = 1 it
would refer to a(0), which does not exist, offset 1), the product formula for every n ≥ 1; the
product over k = 1..n-1 is `∏ k ∈ Finset.Icc 1 (n - 1)`. All identities are in ℤ.

Numerical check: a Python copy of the definitions gives the triangle T = 1; -2, 1; 0, 0, 1;
0, -3, 0, 1; ... and B = 1; 2, 1; 0, 0, 1; 6, 3, 0, 1; 0, 0, 0, 0, 1; 0, 0, 4, 0, 0, 1; ...
(compared with the DATA of A155102 and A155103: identical for the first 36 terms each, rows 1..8),
and a(1..12) = 1, 4, 28, 364, 9100, 445900, 43252300, 8347693900, 3213862151500,
2471459994503500, 3798634011551879500, 11673202317498925703500 (compared with DATA of A155105:
identical for all 12 terms of the entry); the rows are r = 3, 6, 12, 24, ...
-/

namespace OMA.S_oeis_a155105

/-- A155102: T(n,k) = 1 if n = k, -(k+1) if n = 2*k, else 0. -/
def T (n k : ℕ) : ℤ := if n = k then 1 else if n = 2 * k then -((k : ℤ) + 1) else 0

/-- A155103, the matrix inverse of the lower unitriangular matrix `T`:
B(n,m) = [n = m] - Sum_{m ≤ k < n} T(n,k)*B(k,m). -/
def B (n m : ℕ) : ℤ :=
  (if n = m then 1 else 0) - ∑ k : Fin n, if m ≤ (k : ℕ) then T n k * B k m else 0
termination_by n
decreasing_by exact k.isLt

/-- A155105 (offset 1): the n-th positive entry of the third column of `B`, in the order of the rows. -/
noncomputable def a (n : ℕ) : ℤ := B (Nat.nth (fun r => 0 < B r 3) (n - 1)) 3

/-- Cam's conjectures: the recurrence with a(1) = 1, and the product formula. -/
theorem main :
    (a 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → a n = a (n - 1) * (1 + 3 * 2 ^ (n - 2))) ∧
    (∀ n : ℕ, 1 ≤ n → a n = ∏ k ∈ Finset.Icc 1 (n - 1), ((1 : ℤ) + 3 * 2 ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a155105
