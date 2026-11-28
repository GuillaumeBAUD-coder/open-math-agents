import Mathlib

/-!
# OEIS A267884: Barker's conjectures for the OFF cells of Rule 233

Source: https://oeis.org/A267884 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A267884 (Robert Price, Jan 21 2016), offset 0: Total number of OFF (white) cells after n iterations of the Rule 233 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 24 2016 and Apr 20 2019: (Start)
a(n) = 6 for n>2.
a(n) = a(n-1) for n>3.
G.f.: x*(3+2*x+x^2) / (1-x).
(End)

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell of Z, as CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: as in the entry's program, stage t counts the OFF cells among the cells -t..t, and a(n) is the sum of these counts for t = 0..n.
* The statement is the conjunction of the claims of the formula section listed above.
* Recurrences are stated in the integers. Since the denominator of the generating function has
  constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as A * D = N
  in the formal power series ring over the integers.
* Controls from the entry: the definition gives 0, 3, 5, 6, 6, 6, 6, 6 for n = 0..7.
-/

namespace OMA.S_oeis_a267884

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 233 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 233 (state t (i - 1)) (state t i) (state t (i + 1))

/-- The number of OFF cells of stage t among the cells -t..t. -/
def cells (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1)).filter fun i : ℕ => !state t ((i : ℤ) - (t : ℤ))).card

/-- A267884(n): the total number of OFF cells in stages 0..n. -/
def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), cells t

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 2 < n → a n = 6) ∧
    (∀ n : ℕ, 3 < n → a n = a (n - 1)) ∧
    mk (fun n => (a n : ℤ)) * (1 - X) =
      (X * (3 + 2 * X + X ^ 2) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a267884
