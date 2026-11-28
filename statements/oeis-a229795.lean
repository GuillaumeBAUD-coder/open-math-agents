import Mathlib

/-!
# A229795: Number of 2 X 2 0..n arrays with rows and columns in lexicographically nondecreasing order.

Source: https://oeis.org/A229795
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (offset 1, data 7, 29, 86, 205, 421, 777, 1324, 2121, 3235, 4741, ...)
records in its FORMULA section:

  Conjectures from Colin Barker, Sep 21 2018:
  G.f.: x*(7 - 6*x + 11*x^2 - 5*x^3 + x^4) / (1 - x)^5.
  a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.

Conventions:
* A 2 X 2 array with entries in `0..n` is a function `x : Fin 2 → Fin 2 → Fin (n + 1)`,
  where `x i j` is the entry in row `i` and column `j`.
* Two length-2 vectors `p, q` satisfy `p ≤ q` lexicographically (`lexLE p q`) when
  `p 0 < q 0`, or `p 0 = q 0` and `p 1 ≤ q 1`.
* The rows are in lexicographically nondecreasing order when row 0 is lexicographically at
  most row 1, i.e. `lexLE (fun j => x 0 j) (fun j => x 1 j)`; the columns are in
  lexicographically nondecreasing order when column 0 is lexicographically at most column 1,
  i.e. `lexLE (fun i => x i 0) (fun i => x i 1)`.
* `a n` is the number of such arrays, defined for every `n : ℕ`. The entry has offset `1`;
  the definition gives `a 0 = 1` (the zero array). The g.f. of the entry is
  `Sum_{n>=1} a(n) x^n`, i.e. the power series with coefficients `a n` for `n ≥ 1` and
  constant term `0`.
* The statement is the conjunction of both conjectures: the order-5 linear recurrence for
  `n > 5` (in `ℤ`), and the g.f. identity written without division as
  `(1 - x)^5 * A(x) = x*(7 - 6*x + 11*x^2 - 5*x^3 + x^4)` in `PowerSeries ℤ`, where
  `A(x) = Sum_{n>=1} a(n) x^n`.
-/

namespace OMA.S_oeis_a229795

/-- Lexicographic order on length-2 vectors: `p ≤ q` in lex order. -/
abbrev lexLE {n : ℕ} (p q : Fin 2 → Fin (n + 1)) : Prop :=
  p 0 < q 0 ∨ (p 0 = q 0 ∧ p 1 ≤ q 1)

/-- `a n` = number of 2 X 2 arrays `x` with entries in `0..n` whose rows (row 0, row 1) and
whose columns (column 0, column 1) are in lexicographically nondecreasing order. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 2 → Fin 2 → Fin (n + 1))).filter fun x =>
    lexLE (fun j => x 0 j) (fun j => x 1 j) ∧ lexLE (fun i => x i 0) (fun i => x i 1)).card

/-- Colin Barker's conjectures for A229795: the linear recurrence for `n > 5` and the g.f.
`x*(7 - 6*x + 11*x^2 - 5*x^3 + x^4) / (1 - x)^5` of `Sum_{n>=1} a(n) x^n`. -/
theorem main :
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4)
        + a (n - 5)) ∧
    (1 - PowerSeries.X) ^ 5 * PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) =
      PowerSeries.X * (7 - 6 * PowerSeries.X + 11 * PowerSeries.X ^ 2
        - 5 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4) := by
  sorry

end OMA.S_oeis_a229795
