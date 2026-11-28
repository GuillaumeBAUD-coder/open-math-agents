import Mathlib

/-!
# OEIS A267359: Barker's conjectures for the rows of Rule 125 read as numbers

Source: https://oeis.org/A267359 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A267359 (Robert Price, Jan 13 2016), offset 0: Binary representation of the n-th iteration of the Rule 125 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 14 2016 and Apr 19 2019: (Start)
a(n) = 10001*a(n-2) - 10000*a(n-4) for n > 8.
G.f.: (1 + 11*x + 1099*x^2 - 8900*x^3 + 108900*x^4 - 10990000*x^5 + 890000*x^6 + 11000000*x^7 - 1000000*x^8) / ((1 - x)*(1 + x)*(1 - 100*x)*(1 + 100*x)).
(End)

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell of Z, as CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* a(n) writes the states of the cells -n..n of stage n as a string of binary digits, leftmost
  first, and reads that string in base 10, as the program does.
* The statement is the conjunction of the conjectures of the formula section listed above.
* Recurrences are stated in the integers. Since the denominator of the generating function has
  constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as A * D = N
  in the formal power series ring over the integers.
* Controls from the entry: the definition gives 1, 11, 11100, 101111, 111110000, 1000111111 for n = 0..5.
-/

namespace OMA.S_oeis_a267359

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 125 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 125 (state t (i - 1)) (state t i) (state t (i + 1))

/-- A267359(n): the cells -n..n of stage n read as base-10 digits, leftmost first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if state n ((k : ℤ) - (n : ℤ)) then 10 ^ (2 * n - k) else 0

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 10001 * a (n - 2) - 10000 * a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X)) =
      (1 + 11 * X + 1099 * X ^ 2 - 8900 * X ^ 3 + 108900 * X ^ 4 - 10990000 * X ^ 5 + 890000 * X ^ 6 + 11000000 * X ^ 7 - 1000000 * X ^ 8 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a267359
