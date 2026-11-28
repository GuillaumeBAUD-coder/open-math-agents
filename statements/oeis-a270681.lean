import Mathlib

/-!
# OEIS A270681: Number of active (ON, black) cells in n-th stage of growth of Rule 190

Source: https://oeis.org/A270681
Conjectures: Colin Barker, Mar 21 2016.
Formalization: @longling12 (drafted with AI assistance)

Entry A270681 (Robert Price, Mar 21 2016), offset 0: Number of active (ON, black) cells in n-th
stage of growth of two-dimensional cellular automaton defined by Rule 190, based on the 5-celled
von Neumann neighborhood, initialized with a single black (ON) cell at stage zero.

Formalization notes:
* Outer-totalistic 5-cell von Neumann rule 190 on `ℤ × ℤ`.
* Following `%t`, `a n` counts ON cells in the central `(2n + 1) × (2n + 1)` square `[-n, n]^2`
  at stage `n`, reproducing `1, 5, 12, 24, 32, 52, 60, 88, ...`.
* The first closed form has coefficient `3/2` and is stated over `ℚ`; the parity closed forms,
  recurrence, and cleared-denominator generating function are stated over `ℤ`.
-/

namespace OMA.S_oeis_a270681

open PowerSeries

/-- One step of the 2D outer-totalistic cellular automaton with code 190
on the 5-cell von Neumann neighborhood. -/
def step (g : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 190 ((g x y).toNat + 2 *
    ((g (x - 1) y).toNat + (g (x + 1) y).toNat + (g x (y - 1)).toNat + (g x (y + 1)).toNat))

/-- Stage `n` of the automaton on `ℤ × ℤ` started from a single ON cell at `(0, 0)`. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- `A270681(n)`: number of ON cells in `[-n, n]^2` at stage `n` of Rule 190. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter fun p : ℕ × ℕ =>
    state n ((p.1 : ℤ) - n) ((p.2 : ℤ) - n)).card

theorem main :
    (∀ n : ℕ, 1 < n →
      (a n : ℚ) = (3 : ℚ) / 2 * (-1 + (-1) ^ n) - (-5 + (-1) ^ n) * (n : ℚ) + (n : ℚ) ^ 2) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 0 → a n = n ^ 2 + 4 * n) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 1 → (a n : ℤ) = (n : ℤ) ^ 2 + 6 * n - 3) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) =
      1 + 4 * X + 5 * X ^ 2 + 4 * X ^ 3 - 5 * X ^ 4 - X ^ 6 := by
  sorry

end OMA.S_oeis_a270681
