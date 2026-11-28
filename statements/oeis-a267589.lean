import Mathlib

/-!
# OEIS A267589: Barker's conjectures for the decimal middle column of Rule 169

Source: https://oeis.org/A267589 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A267589 (Robert Price, Jan 18 2016), offset 0: Decimal representation of the middle column of the Rule 169 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 18 2016 and Apr 20 2019: (Start)
a(n) = 3*a(n-1)-2*a(n-2) for n>3.
G.f.: (1-x+x^2-x^3+x^5) / ((1-x)*(1-2*x)).
(End)

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell of Z, as CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* The middle column is the cell at position 0; a(n) writes its states at stages 0..n as a string
  of binary digits, stage 0 first, and reads that string in base 2.
* The statement is the conjunction of the conjectures of the formula section listed above.
* Recurrences are stated in the integers. Since the denominator of the generating function has
  constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as A * D = N
  in the formal power series ring over the integers.
* Controls from the entry: the definition gives 1, 2, 5, 10, 20, 41, 83, 167 for n = 0..7.
-/

namespace OMA.S_oeis_a267589

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 169 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 169 (state t (i - 1)) (state t i) (state t (i + 1))

/-- The middle column: 1 when cell 0 is ON at stage k, 0 when it is OFF. -/
def mid (k : ℕ) : ℕ := if state k 0 then 1 else 0

/-- A267589(n): the middle cells of stages 0..n read as base-2 digits, stage 0 first. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), mid k * 2 ^ (n - k)

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 2)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X)) =
      (1 - X + X ^ 2 - X ^ 3 + X ^ 5 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a267589
