import Mathlib

/-!
# A233637: Number of (n+1) X (1+1) 0..2 arrays with every 2 X 2 subblock having the sum of the squares of the edge differences equal to 2.

Source: https://oeis.org/A233637
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (offset 1, data 24, 90, 324, 1188, 4320, 15768, 57456, ...; author R. H. Hardin, Dec 14 2013)
records in its FORMULA section:

  Empirical: a(n) = 2*a(n-1) + 6*a(n-2).

  Conjectures from Colin Barker, Oct 11 2018:
  G.f.: 6*x*(4 + 7*x) / (1 - 2*x - 6*x^2).

Conventions:
* An array with `n + 1` rows and `2` columns and entries in `0..2` is a function
  `A : Fin (n + 1) → Fin 2 → Fin 3`; `A i` is row `i`, and `A i j` is the entry in row `i`, column `j`.
* The `2 X 2` subblocks are the blocks formed by two consecutive rows `i` and `i + 1`
  (for `i < n`). The edge differences of the block with rows `r` (top) and `s` (bottom) are the
  differences of the entries joined by its four edges: `r 0 - r 1` (top), `s 0 - s 1` (bottom),
  `r 0 - s 0` (left) and `r 1 - s 1` (right). The condition is that the sum of their squares is `2`.
* `a n` counts such arrays with `n + 1` rows. The sequence has offset `1`; the value `a 0`
  (single-row arrays, no subblock) is not part of the entry and plays no role below.
* The statement is the conjunction of the two initial terms `a(1) = 24`, `a(2) = 90` and the
  recurrence `a(n) = 2*a(n-1) + 6*a(n-2)` for `n ≥ 3`; together these are equivalent to the
  conjectured generating function `6*x*(4 + 7*x) / (1 - 2*x - 6*x^2)` (and imply the empirical
  recurrence for every `n` where all indices are at least `1`).
-/

namespace OMA.S_oeis_a233637

/-- The square of the difference of two entries, as an integer. -/
def edgeSq (x y : Fin 3) : ℤ := ((x : ℕ) - (y : ℕ) : ℤ) ^ 2

/-- The `2 X 2` subblock with top row `r` and bottom row `s` has the sum of the squares of its
four edge differences equal to `2`. -/
def BlockOK (r s : Fin 2 → Fin 3) : Prop :=
  edgeSq (r 0) (r 1) + edgeSq (s 0) (s 1) + edgeSq (r 0) (s 0) + edgeSq (r 1) (s 1) = 2

instance : DecidableRel BlockOK := fun r s => by
  unfold BlockOK
  infer_instance

/-- The number of `(n+1) X 2` arrays with entries in `0..2` all of whose `2 X 2` subblocks
satisfy `BlockOK`. -/
def a (n : ℕ) : ℕ :=
  Fintype.card {A : Fin (n + 1) → Fin 2 → Fin 3 //
    ∀ i : Fin n, BlockOK (A i.castSucc) (A i.succ)}

/-- The conjecture of A233637: `a(1) = 24`, `a(2) = 90` and `a(n) = 2*a(n-1) + 6*a(n-2)`
for `n ≥ 3` (equivalently, the generating function is `6*x*(4 + 7*x) / (1 - 2*x - 6*x^2)`). -/
theorem main : a 1 = 24 ∧ a 2 = 90 ∧
    ∀ n : ℕ, 3 ≤ n → a n = 2 * a (n - 1) + 6 * a (n - 2) := by
  sorry

end OMA.S_oeis_a233637
