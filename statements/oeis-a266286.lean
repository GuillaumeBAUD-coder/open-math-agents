import Mathlib

/-!
# OEIS A266286: Barker's conjectures for the OFF cells of Rule 13

Source: https://oeis.org/A266286 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A266286 (Robert Price, Dec 26 2015), offset 0: Number of OFF (white) cells in the n-th iteration of the Rule 13 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Dec 28 2015 and Apr 14 2019: (Start)
a(n) = (2*((-1)^n+2)*n-3*(-1)^n+3)/4.
a(n) = 2*a(n-2)-a(n-4) for n>3.
G.f.: x*(2+3*x-x^2) / ((1-x)^2*(1+x)^2).
(End)

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell of Z, as CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: as in the entry's program, stage n counts the OFF cells among the cells -n..n.
* The statement is the conjunction of the claims of the formula section listed above.
* The closed form is multiplied out so that it is stated in the integers.
* Recurrences are stated in the integers. Since the denominator of the generating function has
  constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as A * D = N
  in the formal power series ring over the integers.
* Controls from the entry: the definition gives 0, 2, 3, 3, 6, 4, 9, 5, 12, 6, 15, 7 for n = 0..11.
-/

namespace OMA.S_oeis_a266286

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 13 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 13 (state t (i - 1)) (state t i) (state t (i + 1))

/-- The number of OFF cells of stage t among the cells -t..t. -/
def cells (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1)).filter fun i : ℕ => !state t ((i : ℤ) - (t : ℤ))).card

/-- A266286(n): the number of OFF cells of stage n. -/
def a (n : ℕ) : ℕ := cells n

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 4 * (a n : ℤ) = 2 * ((-1) ^ n + 2) * n - 3 * (-1) ^ n + 3) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 2 * a (n - 2) - a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2) =
      (X * (2 + 3 * X - X ^ 2) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a266286
