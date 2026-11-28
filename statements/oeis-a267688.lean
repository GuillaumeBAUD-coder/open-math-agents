import Mathlib

/-!
# OEIS A267688: Barker's conjectures for the rows of Rule 199 read as numbers

Source: https://oeis.org/A267688 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A267688 (Robert Price, Jan 19 2016), offset 0: Binary representation of the n-th iteration of the Rule 199 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 19 2016: (Start)
a(n) = 110*a(n-1) - 999*a(n-2) - 110*a(n-3) + 1000*a(n-4) for n > 4.
G.f.: (1 - x^2 + 10*x^3 - 1000*x^4) / ((1-x)*(1+x)*(1-10*x)*(1-100*x)).
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
* Controls from the entry: the definition gives 1, 110, 11100, 1111010, 111110100, 11111101010 for n = 0..5.
-/

namespace OMA.S_oeis_a267688

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 199 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 199 (state t (i - 1)) (state t i) (state t (i + 1))

/-- A267688(n): the cells -n..n of stage n read as base-10 digits, leftmost first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if state n ((k : ℤ) - (n : ℤ)) then 10 ^ (2 * n - k) else 0

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 110 * a (n - 1) - 999 * a (n - 2) - 110 * a (n - 3) + 1000 * a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 - 100 * X)) =
      (1 - X ^ 2 + 10 * X ^ 3 - 1000 * X ^ 4 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a267688
