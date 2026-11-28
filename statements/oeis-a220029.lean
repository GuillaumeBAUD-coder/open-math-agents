import Mathlib

/-!
# OEIS A220029: Hardin's quartic formula and Barker's g.f. and recurrence for the number of n X 5 arrays of minima over horizontal and diagonal neighbours of sorted 0..1 arrays

Source: https://oeis.org/A220029 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with claude-code (model claude-fable-5-2), submitted by @VestigeClub.

Entry: A220029: Number of n X 5 arrays of the minimum value of corresponding elements and their
horizontal or diagonal neighbors in a random, but sorted with lexicographically nondecreasing
rows and nonincreasing columns, 0..1 n X 5 array. (R. H. Hardin, Dec 03 2012; column 5 of
A220032; offset 1; data 5, 12, 30, 61, 111, 187, 297, 450, ...)

The conjectures, as the entry gives them:
* "Empirical: a(n) = (1/24)*n^4 + (5/12)*n^3 + (11/24)*n^2 + (61/12)*n - 4 for n>1." (Hardin)
* Conjectures from Colin Barker, Jul 30 2018:
  "G.f.: x*(5 - 13*x + 20*x^2 - 19*x^3 + 11*x^4 - 3*x^5) / (1 - x)^5."
  "a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>6."

Formalization notes:
* Offset 1, as in the entry. `a 0` (the empty array, counted once) is used nowhere: the formula
  is stated for n > 1, the g.f. has coefficient 0 at x^0, and the recurrence for n > 6 involves
  a(n-5), ..., a(n) with n - 5 ≥ 2.
* A 0..1 n X 5 array is `A : Fin n → Fin 5 → Fin 2`: `A i j` is the entry in row `i` (counted
  from the top) and column `j` (counted from the left), with 0 < 1. All arrays are distinct
  objects (no identification up to symmetry).
* "Sorted with lexicographically nondecreasing rows and nonincreasing columns" (`Sorted`): going
  down, the rows (words read left to right) are nondecreasing in the lexicographic order,
  `Monotone (fun i => toLex (A i))`; going right, the columns (words read top to bottom) are
  nonincreasing in the lexicographic order, `Antitone (fun j => toLex (fun i => A i j))`. `toLex`
  is Mathlib's `Pi.Lex` order: the first position where two words differ decides.
* "Horizontal or diagonal neighbors" (`IsNbr`): at the cell `(i, j)` the cells taken are the
  cell itself, `(i, j + 1)` and `(i, j - 1)` (horizontal), and `(i + 1, j + 1)` and
  `(i - 1, j - 1)` (the two neighbours on the diagonal through the cell that runs from the top
  left to the bottom right), as far as they lie inside the array. The entry's wording does not
  say which diagonal is meant; the data decides it: with this diagonal an exhaustive
  enumeration of the definitions below gives 5, 12, 30, 61, 111, 187, 297 for n = 1..7, the
  entry's terms, and a transfer-automaton count of the same definition gives all 210 terms of
  the entry's b-file, while the other diagonal gives 5, 9, 25, 55, ... and both diagonals
  together give 5, 6, 19, 45, ... (and lexicographically nondecreasing columns give
  5, 17, 75, 346, ...).
* The array of minima of `A` has at each cell the minimum of `A` over these cells (`minNbr`; a
  `Finset.inf` over a set that contains the cell itself). `a n` is the number of distinct arrays
  of minima obtained from the sorted 0..1 n X 5 arrays ("random" = ranging over all of them).
* Hardin's formula is stated in `ℚ` for every n > 1, the range the entry gives (it fails at
  n = 1, where it gives 2 and a(1) = 5).
* The g.f. is the ordinary generating function Sum_{n>=1} a(n) x^n, as an identity of formal
  power series over `ℚ` with the denominator `(1 - x)^5` multiplied out; the coefficient of x^0
  is 0 because the offset is 1.
* The recurrence is stated in `ℤ` for every n > 6, the range the entry gives.
* Controls proved in the proof file from these definitions: a(1), ..., a(6) = 5, 12, 30, 61,
  111, 187.
-/

namespace OMA.S_oeis_a220029

/-- Rows (read left to right) lexicographically nondecreasing from top to bottom, and columns
(read top to bottom) lexicographically nonincreasing from left to right. -/
def Sorted {n : ℕ} (A : Fin n → Fin 5 → Fin 2) : Prop :=
  Monotone (fun i => toLex (A i)) ∧ Antitone (fun j => toLex (fun i => A i j))

/-- `q` is the cell `p` itself, a horizontal neighbour of `p`, or a diagonal neighbour of `p`:
the offset (rows, columns) from `p` to `q` is `(0, 0)`, `(0, 1)`, `(0, -1)`, `(1, 1)` or
`(-1, -1)`. -/
def IsNbr {n : ℕ} (p q : Fin n × Fin 5) : Prop :=
  ((q.1 : ℤ) - p.1, (q.2 : ℤ) - p.2) ∈
    ({(0, 0), (0, 1), (0, -1), (1, 1), (-1, -1)} : Finset (ℤ × ℤ))

/-- The minimum of `A` over the cell `p` and its horizontal and diagonal neighbours that lie
inside the array. -/
noncomputable def minNbr {n : ℕ} (A : Fin n → Fin 5 → Fin 2) (p : Fin n × Fin 5) : Fin 2 := by
  classical
  exact (Finset.univ.filter (fun q => IsNbr p q)).inf (fun q => A q.1 q.2)

/-- A220029(n): the number of distinct arrays of minima `fun i j => minNbr A (i, j)`, where `A`
ranges over the sorted n X 5 arrays with entries in 0..1. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ.filter (fun A : Fin n → Fin 5 → Fin 2 => Sorted A)).image
    (fun A => fun i j => minNbr A (i, j))).card

open PowerSeries in
/-- Hardin's empirical formula `a(n) = n^4/24 + 5 n^3/12 + 11 n^2/24 + 61 n/12 - 4` for `n > 1`,
Barker's generating function `x(5 - 13x + 20x^2 - 19x^3 + 11x^4 - 3x^5)/(1 - x)^5`, and Barker's
recurrence `a(n) = 5a(n-1) - 10a(n-2) + 10a(n-3) - 5a(n-4) + a(n-5)` for `n > 6`. -/
theorem main :
    (∀ n : ℕ, 1 < n →
      (a n : ℚ) = (1 / 24) * (n : ℚ) ^ 4 + (5 / 12) * (n : ℚ) ^ 3 + (11 / 24) * (n : ℚ) ^ 2
        + (61 / 12) * (n : ℚ) - 4) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
        X * (5 - 13 * X + 20 * X ^ 2 - 19 * X ^ 3 + 11 * X ^ 4 - 3 * X ^ 5) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a220029
