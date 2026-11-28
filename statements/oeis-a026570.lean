import Mathlib

/-!
# OEIS A026570: Mathar's recurrence for T(n, n - 1) of the array A026568

Source: https://oeis.org/A026570 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A026570 (Clark Kimberling), offset 1: a(n) = A026568(n,n-1), also a(n) = number of integer strings s(0),...,s(n) counted by A026568 such that s(n)=1.
Formula section:
Conjecture: (n+1)*a(n) -2*n*a(n-1) +(-3*n-1)*a(n-2) +2*(2*n-3)*a(n-3)=0. - R. J. Mathar, Jun 23 2013
If recurrence is correct then a(n) = (A026569(n+1)-A026569(n))/2 = A026585(n+1)/2. - Mark van Hoeij, Nov 29 2024

A026568 (Clark Kimberling): Irregular triangular array T read by rows: T(i,0) = T(i,2i) = 1 for i >= 0; T(i,1) = T(i,2i-1) = [ (i+1)/2 ] for i >= 1; and for i >= 2 and 2 <=j <= i - 2, T(i,j) = T(i-1,j-2) + T(i-1,j-1) + T(i-1,j) if i + j is even, T(i,j) = T(i-1,j-2) + T(i-1,j) if i + j is odd.

Formalization notes:
* T(i, j) is defined for 0 <= j <= 2i by the rule of A026568 and is 0 outside the row. The name
  states the parity recursion for i >= 2 and 2 <= j <= i - 2; the definition applies it for 2 <= j
  <= 2i - 2, the range that the companion array A026584 states (j = 2..2i-2) and that the data
  needs: the name's boundary values fix only j <= 1 and j >= 2i - 1, and row 4 of the data is 1,
  2, 7, 7, 13, 7, 7, 2, 1. With this range the definition reproduces the array's data.
* a(n) = T(n, n - 1) for n >= 1, the entry's offset (natural subtraction below it). The title's
  second description, the number of strings s(0), ..., s(n) counted by A026568 with s(n) = 1, is
  the same number by the comment of A026568; the statement uses the first. The block gives no
  range for the recurrence, so it is stated for every n >= 4, the smallest n for which a(n - 3) is
  a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 1, 4, 7, 20, 43, ... from n = 1); the proof file
  proves all 29 listed terms as controls.
-/

namespace OMA.S_oeis_a026570

/-- A026568 T(i, j), 0 <= j <= 2i: T(i, 0) = T(i, 2i) = 1, T(i, 1) = T(i, 2i - 1) = [(i+1)/2] for
i >= 1, and for 2 <= j <= 2i - 2, T(i, j) = T(i-1, j-2) + T(i-1, j-1) + T(i-1, j) if i + j is even
and T(i, j) = T(i-1, j-2) + T(i-1, j) if i + j is odd (0 beyond the row). -/
def T : ℕ → ℕ → ℕ
  | 0, j => if j = 0 then 1 else 0
  | i + 1, j =>
    if 2 * (i + 1) < j then 0
    else if j = 0 ∨ j = 2 * (i + 1) then 1
    else if j = 1 ∨ j = 2 * (i + 1) - 1 then (i + 2) / 2
    else if (i + 1 + j) % 2 = 0 then T i (j - 2) + T i (j - 1) + T i j
    else T i (j - 2) + T i j

/-- A026570: a(n) = T(n, n - 1). -/
def a (n : ℕ) : ℕ := T n (n - 1)

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
      ((n : ℤ) + 1) * (a n : ℤ) - 2 * (n : ℤ) * (a (n - 1) : ℤ) + (-3 * (n : ℤ) - 1) * (a (n - 2) : ℤ) + 2 * (2 * (n : ℤ) - 3) * (a (n - 3) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a026570
