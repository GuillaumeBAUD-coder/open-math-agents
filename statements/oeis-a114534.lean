import Mathlib

/-!
# A114534: a(n) is the permanent of the n X n matrix M defined as follows: if we concatenate the rows of M to form a vector v of length n^2, v_i is the i-th Fibonacci number.

Source: https://oeis.org/A114534
Credit: @xor2k

Comment in the entry (author of the entry: Simone Severini, Feb 15 2006):
  Conjecture: The rank of the matrix M is 2 for every n.
followed in the entry by the remark of Jhixon S. Macías (Sep 02 2026):
  True for n>= 2, see Weston paper.

Conventions:
* The filling starts with F(0) = 0: the entry in row i and column j (both counted from 0) of the
  n X n matrix is F(i*n + j), as in the PARI programs of the entry,
  matrix(n,n,i,j,fibonacci((i-1)*n+j-1)) with i, j counted from 1, and as in the examples of the
  entry (n = 2: [0,1;1,2]; n = 3: [0,1,1;2,3,5;8,13,21]).
* `F n` is this matrix with natural entries, `a n` its permanent (the sequence), and `M n` the same
  matrix with rational entries; the rank is `Matrix.rank` over ℚ.
* Range of n: the entry has offset 2, so its terms are a(2), a(3), ... and 'for every n' is read as
  for every n ≥ 2, the index range of the sequence; this is also the range given by the remark
  'True for n>= 2'. (For n = 1 the matrix is [F(0)] = [0], of rank 0, and for n = 0 it is empty;
  these are not terms of the entry.)

Numerical check: a Python copy of the definition of `a` gives for n = 2, ..., 9
1, 132, 1460808, 6357011889600, 44491520971919463292800, 2082476039060691409777705387034081280,
2712373659248840873249840585282508476815021942277876736,
410721884168854528740774423430429149549703377187068577398353854503625738636800;
compared with DATA: identical for all 8 terms of the entry. (The same definition gives 0 for n = 1.)
-/

namespace OMA.S_oeis_a114534

/-- The n X n matrix filled row by row with the Fibonacci numbers F(0), F(1), ..., F(n^2 - 1). -/
def F (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j => Nat.fib ((i : ℕ) * n + (j : ℕ))

/-- A114534 (offset 2): the permanent of the matrix. -/
def a (n : ℕ) : ℕ := (F n).permanent

/-- The matrix M of the entry, with rational entries. -/
def M (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => (Nat.fib ((i : ℕ) * n + (j : ℕ)) : ℚ)

/-- The rank of M is 2 for every n (n ≥ 2, the offset of the entry). -/
theorem main : ∀ n : ℕ, 2 ≤ n → (M n).rank = 2 := by
  sorry

end OMA.S_oeis_a114534
