import Mathlib

/-!
# OEIS A267442: Mathar's conjecture that the middle column of Rule 129 is A043545

Source: https://oeis.org/A267442 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267442 (Robert Price, Jan 15 2016), offset 0: Middle column of the Rule 129 elementary
cellular automaton starting with a single ON (black) cell.
Formula section:
Conjecture: a(n) = A043545(n), n>0. - R. J. Mathar, Jan 17 2016
Entry A043545, offset 0: (Maximal base-2 digit of n) - (minimal base-2 digit of n).

Formalization notes:
* Rule numbering: Wolfram's code for elementary cellular automata: the new value of cell x is bit
  4l + 2c + r of the rule number, where l, c, r are the old values of the cells x-1, x, x+1.
* Initial condition: at stage 0 the cell 0 is ON and every other cell of Z is OFF; each stage
  applies the rule to every cell, so the background evolves with the rule (Rule 129 turns three
  OFF cells into an ON cell, so its background is ON from stage 1), as Mathematica's
  CellularAutomaton does in the entry's program.
* a(n) is the middle cell (cell 0) of stage n, as 1 for ON and 0 for OFF.
* A043545(n) uses Mathlib's Nat.digits 2 n, the binary digits of n without leading zeros; the
  maximal and minimal digits are List.max? and List.min? of that list (for n > 0 the list is not
  empty, so the default value 0 of getD plays no role).
* Controls from the entry, proved in the proof file: a(0..8) = 1, 0, 1, 0, 1, 1, 1, 0, 1.
-/

namespace OMA.S_oeis_a267442

/-- One step of an elementary cellular automaton in Wolfram's numbering: the new value of cell `x`
is bit `4l + 2c + r` of `rule`, where `l, c, r` are the old values of cells `x-1, x, x+1`. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at `0`. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- A267442(n): the middle cell of row n of Rule 129, as 0 or 1. -/
def a (n : ℕ) : ℕ := if state 129 n 0 then 1 else 0

/-- A043545(n): the maximal binary digit of n minus the minimal one. -/
def A043545 (n : ℕ) : ℕ := ((Nat.digits 2 n).max?).getD 0 - ((Nat.digits 2 n).min?).getD 0

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 0 < n → a n = A043545 n := by
  sorry

end OMA.S_oeis_a267442
