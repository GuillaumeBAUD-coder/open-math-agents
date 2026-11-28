import Mathlib

/-!
# OEIS A270935: Number of active (ON, black) cells at stage 2^n-1 of the 2D cellular automaton defined by Rule 221

Source: https://oeis.org/A270935
Formalization: @VestigeClub

Entry A270935 (offset 0): Number of active (ON, black) cells at stage 2^n-1 of the two-dimensional
cellular automaton defined by Rule 221, based on the 5-celled von Neumann neighborhood.
Initialized with a single black (ON) cell at stage zero.

Conjectures in the entry (all stated below as one conjunction):
* Conjecture: Rule 253 also generates this sequence. (Lars Blomberg, Jun 06 2016)
* Conjecture: a(n) = 4*4^n - 4*2^n - 4 = A269907(n), n>1. (Lars Blomberg, Jun 06 2016)
* Conjectures from Colin Barker, Jun 07 2016:
  - a(n) = 7*a(n-1) - 14*a(n-2) + 8*a(n-3) for n>4.
  - G.f.: (1 + x + 2*x^2 + 16*x^3 - 32*x^4) / ((1 - x)*(1 - 2*x)*(1 - 4*x)).

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood. The
  next state of a cell at `(i, j)` is bit `c + 2 * s` of `code`, where `c` is its current state
  (`0` or `1`) and `s` is the number of ON cells among its four orthogonal neighbors `(i +- 1, j)`
  and `(i, j +- 1)`.
* Initial condition and evolution: at stage `0`, only `(0, 0)` is ON and every other cell of `ℤ²`
  is OFF. At each stage the rule is applied synchronously to every cell of `ℤ²` (including the
  background).
* Counting convention (offset 0): `onCount code t` counts ON cells in the square `[-t, t]²` after
  `t` steps; `aOf code n = onCount code (2 ^ n - 1)` is the count at stage `2^n - 1`, and
  `a n = aOf 221 n`.
* A269907 is defined as the number of active (ON, black) cells at stage `2^n - 1` of the 2D
  cellular automaton defined by Rule 1 on the 5-celled von Neumann neighborhood, i.e., `aOf 1 n`.
* The closed form and recurrence are stated in `ℤ` so subtraction is exact. The generating
  function is stated in the formal power series ring `ℚ⟦X⟧`, where the denominator has constant
  term `1` and is therefore a unit.
-/

namespace OMA.S_oeis_a270935

open PowerSeries

/-- `cell code t i j` is the state of cell `(i, j)` after `t` steps of the 2D outer totalistic
cellular automaton with Wolfram code `code` on the 5-celled von Neumann neighborhood, starting
from a single ON cell at `(0, 0)` on an all-OFF background. -/
def cell (code : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0 => fun i j => decide (i = 0 ∧ j = 0)
  | t + 1 => fun i j => code.testBit ((cell code t i j).toNat + 2 * ((cell code t (i + 1) j).toNat +
      (cell code t (i - 1) j).toNat + (cell code t i (j + 1)).toNat + (cell code t i (j - 1)).toNat))

/-- The number of ON cells in the square `[-t, t] × [-t, t]` after `t` steps. -/
def onCount (code t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
    if cell code t ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0

/-- The number of ON cells at stage `2^n - 1` for the automaton with Wolfram code `code`. -/
def aOf (code n : ℕ) : ℕ :=
  onCount code (2 ^ n - 1)

/-- A270935(n): the number of ON cells at stage `2^n - 1` for Rule 221. -/
def a (n : ℕ) : ℕ :=
  aOf 221 n

/-- The ordinary generating function `∑_{n ≥ 0} a(n) X^n`. -/
noncomputable def A : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (a n : ℚ)

theorem main :
    (∀ n : ℕ, aOf 253 n = a n) ∧
    (∀ n : ℕ, 1 < n → (a n : ℤ) = 4 * 4 ^ n - 4 * 2 ^ n - 4) ∧
    (∀ n : ℕ, 1 < n → a n = aOf 1 n) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * (a (n - 1) : ℤ) - 14 * (a (n - 2) : ℤ) + 8 * (a (n - 3) : ℤ)) ∧
    A = (1 + X + 2 * X ^ 2 + 16 * X ^ 3 - 32 * X ^ 4) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X))⁻¹ := by
  sorry

end OMA.S_oeis_a270935
