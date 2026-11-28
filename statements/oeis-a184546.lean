import Mathlib

/-!
# OEIS A184546: Barker's generating function and recurrence, and Hardin's empirical polynomial

Source: https://oeis.org/A184546 (OEIS Foundation, CC BY-SA 4.0).

Entry (R. H. Hardin, Jan 16 2011), offset 1: Number of (n+2) X 9 binary arrays with each 3 X 3
subblock having rows and columns in lexicographically nondecreasing order. Data: 539, 1513, 3461, 7307, 14767, 28844, ...
The formula section states: Empirical: a(n) = (1/362880)*n^9 + (1/5760)*n^8 + (289/60480)*n^7 + (217/2880)*n^6 + (12949/17280)*n^5 + (28049/5760)*n^4 + (468401/22680)*n^3 + (210319/1440)*n^2 + (145955/504)*n + 77. Conjectures from _Colin Barker_, Apr 14 2018: (Start) G.f.:
x*(539 - 3877*x + 12586*x^2 - 23898*x^3 + 29072*x^4 - 23429*x^5 + 12502*x^6 - 4270*x^7 + 853*x^8 - 77*x^9) / (1 - x)^10. a(n) = 10*a(n-1) - ... + a(n-10) for n>10. (End)

Formalization notes (the reading of the merged statement of the sibling A184540):
* An (n+2) X 9 binary array is a function `A : Fin (n + 2) → Fin 9 → Fin 2`; `A i j` is the entry in
  row `i` (top to bottom) and column `j` (left to right), with entries 0 < 1.
* A 3 X 3 subblock is made of 3 consecutive rows and 3 consecutive columns. The one whose top left
  entry is `A i j` has the entry `A (i + r) (j + c)` in its row `r` and column `c`.
* Rows in lexicographically nondecreasing order: the three rows of the subblock, each read left to
  right as a word, are lexicographically nondecreasing from top to bottom. Columns in
  lexicographically nondecreasing order: the three columns, each read top to bottom, are
  lexicographically nondecreasing from left to right. `LexLE x y` is the lexicographic order on
  words of length 3 over 0 < 1: the first position where the words differ decides.
* `a n` is `Set.ncard` of the set of these arrays, a set of functions between finite types. The
  value for n = 0 (two rows, no subblock) is not a term of the sequence.
* The g.f. is Sum_{n >= 1} a(n) x^n, stated with the denominator (1 - x)^10 cleared, in Z[[x]]
  (it has constant term 1, so this is equivalent). The recurrence is stated in the integers for
  n > 10, and the polynomial in the rationals for every n >= 1, as in the entry.
* `main` is the conjunction of the three formulas.
-/

namespace OMA.S_oeis_a184546

open PowerSeries

/-- `LexLE x y`: the word `x` is lexicographically at most the word `y` (words of length 3 over
0 < 1, compared from position 0). -/
def LexLE (x y : Fin 3 → Fin 2) : Prop :=
  x 0 < y 0 ∨ (x 0 = y 0 ∧ (x 1 < y 1 ∨ (x 1 = y 1 ∧ x 2 ≤ y 2)))

/-- Every 3 X 3 subblock `B` of `A` has its rows, each read left to right, in lexicographically
nondecreasing order from top to bottom, and its columns, each read top to bottom, in
lexicographically nondecreasing order from left to right. -/
def Good {m : ℕ} (A : Fin m → Fin 9 → Fin 2) : Prop :=
  ∀ (i j : ℕ) (hi : i + 2 < m) (hj : j + 2 < 9),
    let B : Fin 3 → Fin 3 → Fin 2 := fun r c =>
      A ⟨i + r, by have := r.isLt; omega⟩ ⟨j + c, by have := c.isLt; omega⟩
    LexLE (B 0) (B 1) ∧ LexLE (B 1) (B 2) ∧
      LexLE (fun r => B r 0) (fun r => B r 1) ∧ LexLE (fun r => B r 1) (fun r => B r 2)

/-- A184546(n): the number of (n+2) X 9 binary arrays all of whose 3 X 3 subblocks have their rows
and columns in lexicographically nondecreasing order. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {A : Fin (n + 2) → Fin 9 → Fin 2 | Good A}

/-- Barker's conjectures (the g.f. and the recurrence) and the empirical polynomial of the entry. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 10 =
      X * (539 - 3877 * X + 12586 * X ^ 2 - 23898 * X ^ 3 + 29072 * X ^ 4 - 23429 * X ^ 5 + 12502 * X ^ 6 - 4270 * X ^ 7 + 853 * X ^ 8 - 77 * X ^ 9) ∧
    (∀ n : ℕ, 10 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10)) ∧
    (∀ n : ℕ, 0 < n → (a n : ℚ) = (1 / 362880 : ℚ) * (n : ℚ) ^ 9 + (1 / 5760 : ℚ) * (n : ℚ) ^ 8 + (289 / 60480 : ℚ) * (n : ℚ) ^ 7 + (217 / 2880 : ℚ) * (n : ℚ) ^ 6 + (12949 / 17280 : ℚ) * (n : ℚ) ^ 5 + (28049 / 5760 : ℚ) * (n : ℚ) ^ 4 + (468401 / 22680 : ℚ) * (n : ℚ) ^ 3 + (210319 / 1440 : ℚ) * (n : ℚ) ^ 2 + (145955 / 504 : ℚ) * (n : ℚ) + (77 : ℚ)) := by
  sorry

end OMA.S_oeis_a184546
