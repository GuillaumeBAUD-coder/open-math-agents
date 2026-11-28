import Mathlib

/-!
# OEIS A267160: Barker's conjectures for the OFF cells of Rule 107

Source: https://oeis.org/A267160 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A267160 (Robert Price, Jan 11 2016), offset 0: Number of OFF (white) cells in the n-th iteration of the Rule 107 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 11 2016 and Apr 19 2019: (Start)
a(n) = a(n-2)+a(n-4)-a(n-6) for n>11.
G.f.: x*(2+2*x+x^3-x^4+x^5-x^6+4*x^7+x^8-x^9-x^10+x^11) / ((1-x)^2*(1+x)^2*(1+x^2)).
(End)

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell of Z, as CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: as in the entry's program, stage n counts the OFF cells among the cells -n..n.
* The statement is the conjunction of the claims of the formula section listed above.
* Recurrences are stated in the integers. Since the denominator of the generating function has
  constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as A * D = N
  in the formal power series ring over the integers.
* Controls from the entry: the definition gives 0, 2, 2, 2, 3, 3, 6, 2, 11, 4, 13, 2 for n = 0..11.
-/

namespace OMA.S_oeis_a267160

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 107 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 107 (state t (i - 1)) (state t i) (state t (i + 1))

/-- The number of OFF cells of stage t among the cells -t..t. -/
def cells (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1)).filter fun i : ℕ => !state t ((i : ℤ) - (t : ℤ))).card

/-- A267160(n): the number of OFF cells of stage n. -/
def a (n : ℕ) : ℕ := cells n

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 11 < n → (a n : ℤ) = a (n - 2) + a (n - 4) - a (n - 6)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2)) =
      (X * (2 + 2 * X + X ^ 3 - X ^ 4 + X ^ 5 - X ^ 6 + 4 * X ^ 7 + X ^ 8 - X ^ 9 - X ^ 10 + X ^ 11) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a267160
