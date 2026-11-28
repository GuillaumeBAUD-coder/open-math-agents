import Mathlib

/-!
# A266660: Binary representation of the n-th iteration of the Rule 47 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266660
Credit: @alkrssve

Text of the entry: OEIS Foundation and contributors, CC BY-SA 4.0. Read 2026-11-27.

The entry (Robert Price, Jan 02 2016, offset 0) lists, for each n, the middle 2n+1 cells of row n of Rule 47,
started from one ON cell on an all-OFF line, read as a number in base 10: the cells, each 0 or 1, are written as decimal digits.
Its program is CellularAutomaton[47, {{1},0}, ...], then Take the cells -n..n, then FromDigits[...] with its default base 10.
Its formula section has the conjectures stated here:

  Conjectures from Colin Barker, Jan 03 2016 and Apr 18 2019: (Start)
  a(n) = (199*(-1)^n+10^(2*n+1)-(-1)^n*10^(2*n+1)-1)/18 for n>1.
  a(n) = 10001*a(n-2)-10000*a(n-4) for n>5.
  G.f.: (1+110*x-9990*x^2+10990*x^3-100000*x^4+100000*x^5) / ((1-x)*(1+x)*(1-100*x)*(1+100*x)).
  (End)
  Conjecture: a(n) = (10*100^n - 100)/9 for odd n > 1; a(n) = 11 for even n > 1. - Karl V. Keller, Jr., Oct 10 2021

How it is stated:
* Rule numbering is Wolfram's: the new value of a cell is bit 4l + 2c + r of 47, where l, c, r
  are the old values of its left neighbour, the cell itself and its right neighbour.
* The rule acts on every cell of the integer line, so the background changes as well: Rule 47 sends
  three OFF cells to ON and three ON cells to OFF, and the background alternates. This is what the
  entry's program computes.
* a n reads the cells -n..n of row n in base 10 with the leftmost cell most significant:
  cell n - k has weight 10^k for k = 0..2n.
* main is the conjunction of the conjectures, in the entry's order and with its ranges; the last entry
  line gives two conjuncts, one for odd n and one for even n. The first closed form is stated in the
  rationals, the recurrence in the integers because it subtracts.
  The formula for odd n divides by 9 and is stated in the rationals.
  The denominator of the generating function has constant term 1, so A(x) = N(x) / D(x) is stated as
  A * D = N, where A is the formal power series with coefficients a(n) over the integers.
* Check against the entry's data: this definition gives 1, 110, 11, 1111100, 11 for n = 0..4.
-/

namespace OMA.S_oeis_a266660

open PowerSeries

/-- Wolfram's numbering of elementary cellular automata: the new value of a cell is bit
`4l + 2c + r` of the rule number, where `l`, `c`, `r` are the old values of the cell to its left,
the cell itself and the cell to its right. Here the rule number is 47. -/
def rule (l c r : Bool) : Bool := Nat.testBit 47 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Row `n` of Rule 47 on the whole line, started from a single ON cell at position 0. -/
def row : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | n + 1, i => rule (row n (i - 1)) (row n i) (row n (i + 1))

/-- A266660(n): the cells `-n..n` of row `n` read in base 10, leftmost cell first. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * n + 1), if row n ((n : ℤ) - k) then 10 ^ k else 0

theorem main :
    (∀ n : ℕ, 1 < n → (a n : ℚ) = (199 * (-1) ^ n + 10 ^ (2 * n + 1) - (-1) ^ n * 10 ^ (2 * n + 1) - 1) / 18) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 10001 * a (n - 2) - 10000 * a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X)) =
      1 + 110 * X - 9990 * X ^ 2 + 10990 * X ^ 3 - 100000 * X ^ 4 + 100000 * X ^ 5 ∧
    (∀ n : ℕ, 1 < n → Odd n → (a n : ℚ) = (10 * 100 ^ n - 100) / 9) ∧
    (∀ n : ℕ, 1 < n → Even n → a n = 11) := by
  sorry

end OMA.S_oeis_a266660
