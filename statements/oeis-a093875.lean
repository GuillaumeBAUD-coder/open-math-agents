import Mathlib

/-!
# A093875: Denominators in Kepler's tree of harmonic fractions.

Source: https://oeis.org/A093875
Credit: @xor2k

Yosu Yurramendi (Jun 22 2016), in the formula section of A093875:
  Conjecture of the comment in detail: a(2n+1) = a(2n), n > 0; a(2n+1) = A071585(n), n >= 0;
  a(2n) = A071585(n), n > 0.
(The comment referred to, by the same author, Jan 09 2016: It appears that A071585 is a
bisection of this sequence, which itself is a bisection of A093873.)

All three claims of the conjecture are stated, as one conjunction.

Conventions:
* Kepler's tree of harmonic fractions (comment of the entry: begin with 1/1 and give every node
  i/j two descendants labeled i/(i+j) and j/(i+j)). The tree is read row by row, left to right,
  with offset 1: the root has index 1 and the fraction at index n has its left child i/(i+j) at
  index 2n and its right child j/(i+j) at index 2n+1, as in the Mathematica program of the
  entry. `kepler n` is the pair (numerator, denominator) at index n as written in the tree, and
  `a n` is its denominator. Index 0 is not part of the sequence (junk value 1/1).
* A071585 (offset 0) is defined by its own name: numerator of the continued fraction expansion
  whose terms are the first-order differences of exponents in the binary representation of 4*n,
  with the exponents of 2 being listed in descending order. Following the comment and the
  Mathematica program of that entry: if 4*n = 2^b_1 + ... + 2^b_k with b_1 > ... > b_k
  (`expo n`), the terms are d_j = b_j - b_(j+1) for j < k and d_k = b_k (`diffs`), the value is
  d_1 + 1/(d_2 + 1/(... + 1/d_k)) as a rational number (`cf`), and A071585(n) is the numerator
  of this rational in lowest terms; A071585(0) = 1 is set separately, as in that entry.
* The first and third claims are stated for every n ≥ 1, the second for every n ≥ 0.

Numerical check: a Python copy of the definitions gives
a(1..20) = 1, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 4, 4, 5, 5, 5, 5, 7, 7, 7
(compared with DATA of A093875: identical for the first 83 terms, all of the DATA) and
A071585(0..19) = 1, 2, 3, 3, 4, 5, 4, 5, 5, 7, 7, 8, 5, 7, 7, 8, 6, 9, 10, 11
(compared with DATA of A071585: identical for the first 77 terms, all of the DATA).
The three claims were checked for all n up to 10^4.
-/

namespace OMA.S_oeis_a093875

/-- The fraction (numerator, denominator) at index n ≥ 1 of Kepler's tree, read row by row:
1/1 at index 1; i/j at index n has children i/(i+j) at index 2n and j/(i+j) at index 2n+1. -/
def kepler : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | 1 => (1, 1)
  | (n + 2) =>
    if (n + 2) % 2 = 0 then
      ((kepler ((n + 2) / 2)).1, (kepler ((n + 2) / 2)).1 + (kepler ((n + 2) / 2)).2)
    else
      ((kepler ((n + 2) / 2)).2, (kepler ((n + 2) / 2)).1 + (kepler ((n + 2) / 2)).2)
decreasing_by all_goals omega

/-- A093875 (offset 1): the denominator of the fraction at index n of Kepler's tree. -/
def a (n : ℕ) : ℕ := (kepler n).2

/-- The exponents b_1 > b_2 > ... > b_k in the binary representation of 4*n, in descending
order. -/
def expo (n : ℕ) : List ℕ := (Nat.bitIndices (4 * n)).reverse

/-- From b_1, ..., b_k to the terms b_1 - b_2, ..., b_(k-1) - b_k, b_k. -/
def diffs : List ℕ → List ℕ
  | [] => []
  | [b] => [b]
  | b :: c :: r => (b - c) :: diffs (c :: r)

/-- The value d_1 + 1/(d_2 + 1/(... + 1/d_k)) of a finite continued fraction. -/
def cf : List ℕ → ℚ
  | [] => 0
  | [d] => d
  | d :: e :: r => d + 1 / cf (e :: r)

/-- A071585 (offset 0): numerator of the continued fraction whose terms are the first-order
differences of the exponents in the binary representation of 4*n; A071585(0) = 1. -/
def A071585 (n : ℕ) : ℕ := if n = 0 then 1 else (cf (diffs (expo n))).num.toNat

/-- Yurramendi's conjecture: a(2n+1) = a(2n) for n > 0; a(2n+1) = A071585(n) for n ≥ 0;
a(2n) = A071585(n) for n > 0. -/
theorem main : (∀ n : ℕ, 0 < n → a (2 * n + 1) = a (2 * n)) ∧
    (∀ n : ℕ, a (2 * n + 1) = A071585 n) ∧
    (∀ n : ℕ, 0 < n → a (2 * n) = A071585 n) := by
  sorry

end OMA.S_oeis_a093875
