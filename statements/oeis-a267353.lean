import Mathlib

/-!
# OEIS A267353: Barker's conjectures for the ON cells of Rule 123

Source: https://oeis.org/A267353 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A267353 (Robert Price, Jan 13 2016), offset 0: Total number of ON (black) cells after n iterations of the Rule 123 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 14 2016: (Start)
a(n) = (n^2+(4-(-1)^n)*n+(-1)^n+1)/2.
a(n) = a(n-1)+2*a(n-2)-2*a(n-3)-a(n-4)+a(n-5) for n>4.
G.f.: (1+2*x+x^2+2*x^3-2*x^4) / ((1-x)^3*(1+x)^2).
(End)

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell of Z, as CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: as in the entry's program, stage t counts the ON cells among the cells -t..t, and a(n) is the sum of these counts for t = 0..n.
* The statement is the conjunction of the claims of the formula section listed above.
* The closed form is multiplied by 2 and stated in the integers.
* Recurrences are stated in the integers. Since the denominator of the generating function has
  constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as A * D = N
  in the formal power series ring over the integers.
* Controls from the entry: the definition gives 1, 3, 6, 12, 15, 25, 28, 42, 45, 63, 66, 88 for n = 0..11.
-/

namespace OMA.S_oeis_a267353

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 123 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 123 (state t (i - 1)) (state t i) (state t (i + 1))

/-- The number of ON cells of stage t among the cells -t..t. -/
def cells (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1)).filter fun i : ℕ => state t ((i : ℤ) - (t : ℤ))).card

/-- A267353(n): the total number of ON cells in stages 0..n. -/
def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), cells t

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 2 * (a n : ℤ) = n ^ 2 + (4 - (-1) ^ n) * n + (-1) ^ n + 1) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) =
      (1 + 2 * X + X ^ 2 + 2 * X ^ 3 - 2 * X ^ 4 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a267353
