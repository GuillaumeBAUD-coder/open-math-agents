import Mathlib

/-!
# A353047: Number of length n words on alphabet {0,1,2} that contain each of the subwords 01, 02, 10, 12, 20, and 21 as (not necessarily contiguous) subwords.

Source: https://oeis.org/A353047

The conjecture formalized here (N. J. A. Sloane, Jun 17 2022, comment in A353047):
* Appears to equal 12 times A222993, except that sequence only has a conjectured formula.

The same remark is recorded in A222993 (N. J. A. Sloane, Jun 17 2022): A353047 is probably equal to
12 times this sequence.

A222993 (R. H. Hardin): Number of n X 2 0..2 arrays with successive rows and columns fitting to
straight lines with nondecreasing slope, with a single point array taken as having zero slope.

Conventions:
* A word of length n on {0,1,2} is a function w : Fin n → Fin 3. A two-letter word xy is a (not
  necessarily contiguous) subword of w when w i = x and w j = y for some positions i < j.
* A353047 has offset 5 (its first term 12 is a(5)); `a n` is defined for every n by the same
  count. A222993 has offset 1 (its first term 9 is the number of 1 X 2 arrays); `b n` is defined
  for every n by the same count.
* An n X 2 array with entries 0..2 is a function A : Fin n → Fin 2 → Fin 3, rows indexed by
  Fin n (top to bottom) and columns by Fin 2 (left to right). The entries of a row or a column of
  length m are the points (1, y_1), ..., (m, y_m), read left to right in a row and top to bottom
  in a column; the slope of the least squares straight line through them is
  (m * Sum x_i*y_i - Sum x_i * Sum y_i) / (m * Sum x_i^2 - (Sum x_i)^2), and, as in the name, a
  single point (m = 1) has slope 0. "Successive rows with nondecreasing slope" means that the slope
  of each row is at most the slope of the next row; "successive columns with nondecreasing slope"
  means that the slope of the left column is at most the slope of the right column.
* The statement: 12 * A222993(n) = A353047(n + 5) for every n >= 1, the alignment of the terms
  (108 = 12 * 9, 600 = 12 * 50, 2664 = 12 * 222, ...).

Numerical check: Python copies of both definitions give a(5..10) = 12, 108, 600, 2664, 10404, 37476
(the DATA of A353047) and b(1..5) = 9, 50, 222, 867, 3123 (the DATA of A222993).
-/

namespace OMA.S_oeis_a353047

/-- The two-letter word xy is a (not necessarily contiguous) subword of w. -/
abbrev HasSubword {n : ℕ} (w : Fin n → Fin 3) (x y : Fin 3) : Prop :=
  ∃ i j : Fin n, i < j ∧ w i = x ∧ w j = y

/-- A353047(n): the number of length n words on {0,1,2} that contain each of 01, 02, 10, 12, 20,
21 as a (not necessarily contiguous) subword. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Fin 3 => ∀ x y : Fin 3, x ≠ y → HasSubword w x y)).card

/-- The slope of the least squares straight line through the points (i + 1, y i), i < m, with a
single point taken as having slope 0. -/
def slope {m : ℕ} (y : Fin m → ℚ) : ℚ :=
  if m = 1 then 0 else
    ((m : ℚ) * ∑ i : Fin m, (((i : ℕ) : ℚ) + 1) * y i -
        (∑ i : Fin m, (((i : ℕ) : ℚ) + 1)) * ∑ i : Fin m, y i) /
      ((m : ℚ) * ∑ i : Fin m, (((i : ℕ) : ℚ) + 1) ^ 2 - (∑ i : Fin m, (((i : ℕ) : ℚ) + 1)) ^ 2)

/-- An n X 2 array with entries 0..2 whose successive rows and successive columns fit straight
lines with nondecreasing slope. -/
abbrev Good {n : ℕ} (A : Fin n → Fin 2 → Fin 3) : Prop :=
  (∀ i j : Fin n, (j : ℕ) = i + 1 →
      slope (fun k => ((A i k : ℕ) : ℚ)) ≤ slope (fun k => ((A j k : ℕ) : ℚ))) ∧
    slope (fun i => ((A i 0 : ℕ) : ℚ)) ≤ slope (fun i => ((A i 1 : ℕ) : ℚ))

/-- A222993(n): the number of n X 2 arrays with entries 0..2 whose successive rows and columns
fit straight lines with nondecreasing slope. -/
def b (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n → Fin 2 → Fin 3 => Good A)).card

/-- Sloane's conjecture: A353047 is 12 times A222993, with the terms aligned as
A353047(n + 5) = 12 * A222993(n) for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a (n + 5) = 12 * b n := by
  sorry

end OMA.S_oeis_a353047
