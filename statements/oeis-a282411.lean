import Mathlib

/-!
# OEIS A282411: Barker's conjectures for the x-axis, from the left edge to the origin of the 2D Rule 467

Source: https://oeis.org/A282411 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A282411 (Robert Price, Feb 14 2017), offset 0: Binary representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 467, based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Colin Barker, Feb 15 2017: (Start)
a(n) = (1 +(-1)^n) * (10^(1+n)-1)/18 for n>1.
a(n) = 101*a(n-2) - 100*a(n-4) for n>3.
G.f.: (1 + x + 10*x^2 - 101*x^3 + 100*x^5) / ((1 - x)*(1 + x)*(1 - 10*x)*(1 + 10*x)).
(End)

Formalization notes:
* Rule numbering, as in the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}} and
  rule[[10 - #]] of IntegerDigits[code, 2, 10]): the new state of a cell is bit 2s + c of the rule
  number, where c is its old state and s is the number of ON cells among its four orthogonal
  neighbors.
* Initial condition: at stage 0 the cell (0, 0) is ON and every other cell of Z x Z is OFF; each
  stage applies the rule to every cell of Z x Z (the background follows the rule too; the entry's
  program runs on a cyclic grid large enough that the result is the same).
* a(n) writes the states of the cells (x, 0) of stage n, for x = -n, ..., 0 in this order, as a
  string of binary digits and reads that string in base 10 (FromDigits in the entry's program).
* The statement is the conjunction of Barker's recurrence and generating function. The recurrence
  is stated in the integers. Since the denominator of the generating function has constant term 1,
  the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as A * D = N in the formal
  power series ring over the integers.
* Controls: the definition gives 1, 1, 111, 0, 11111, 0, 1111111, 0 for n = 0..7 (the entry's data, checked by direct
  simulation).
-/

namespace OMA.S_oeis_a282411

open PowerSeries

/-- The new state of a cell: bit 2s + c of the rule number. -/
def ca (rule : ℕ) (c : Bool) (s : ℕ) : Bool := Nat.testBit rule (2 * s + c.toNat)

/-- Stage t of Rule 467 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => ca 467 (state t x y)
      ((state t (x - 1) y).toNat + (state t (x + 1) y).toNat +
        (state t x (y - 1)).toNat + (state t x (y + 1)).toNat)

/-- A282411(n): the cells (x, 0) of stage n, x = -n, ..., 0, read as base-10 digits. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (if state n ((k : ℤ) - (n : ℤ)) 0 then 1 else 0) * 10 ^ (n - k)

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 101 * a (n - 2) - 100 * a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) =
      (1 + X + 10 * X ^ 2 - 101 * X ^ 3 + 100 * X ^ 5 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a282411
