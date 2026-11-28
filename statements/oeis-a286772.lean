import Mathlib

/-!
# OEIS A286772: Decimal representation of the diagonal from the corner to the origin of Rule 221

Source: https://oeis.org/A286772
Conjectures: Colin Barker, May 14 2017.
Formalization: @longling12 (drafted with AI assistance)

Entry A286772 (Robert Price, May 14 2017), offset 0: Decimal representation of the diagonal from
the corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 221, based on the 5-celled von Neumann neighborhood, initialized with a single
black (ON) cell at stage zero.

Formalization notes:
* Outer-totalistic 5-cell von Neumann rule 221 on `ℤ × ℤ`.
* `%N` and all OEIS terms `1, 2, 0, 14, 1, 62, 1, 254, ...` read the diagonal cells
  `(-n, -n), (-n + 1, -n + 1), ..., (0, 0)` in base 2 with the corner most significant (the last
  line of `%t` is a copy-paste x-axis typo).
* The site statement reproduces Barker's four lines verbatim (including omitting parity qualifiers
  on the two closed forms and stating `for n>4` on the recurrence).
-/

namespace OMA.S_oeis_a286772

open PowerSeries

/-- One step of the 2D outer-totalistic cellular automaton with code 221
on the 5-cell von Neumann neighborhood. -/
def step (g : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 221 ((g x y).toNat + 2 *
    ((g (x - 1) y).toNat + (g (x + 1) y).toNat + (g x (y - 1)).toNat + (g x (y + 1)).toNat))

/-- Stage `n` of the automaton on `ℤ × ℤ` started from a single ON cell at `(0, 0)`. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- `A286772(n)`: diagonal cells `(-n, -n)..(0, 0)` at stage `n` interpreted in base 2. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) ((i : ℤ) - n)).toNat * 2 ^ (n - i)

theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      1 + 2 * X - 5 * X ^ 2 + 4 * X ^ 3 + 5 * X ^ 4 - 4 * X ^ 6 ∧
    (∀ n : ℕ, 2 < n → a n = 1) ∧
    (∀ n : ℕ, 2 < n → a n = 2 ^ (n + 1) - 2) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a286772
