import Mathlib

/-!
# A270082: First differences of number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by Rule 62, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A270082 (OEIS Foundation, CC BY-SA 4.0).
Conjectures: Colin Barker, Mar 10 2016.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has one ON cell at the origin. The rule updates the whole integer plane
using bit c + 2s, with s the sum of the four orthogonal neighbors and c the center.
The count uses the square [-n,n] by [-n,n] at each stage. The first difference at n subtracts stage n from stage n+1.
The sequence starts at index 0. The ordinary generating function is cross-multiplied in ℤ⟦X⟧.
-/

namespace OMA.S_oeis_a270082

open PowerSeries

def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | n + 1, x, y => Nat.testBit 62 ((state n x y).toNat + 2 *
      ((state n (x - 1) y).toNat + (state n (x + 1) y).toNat +
       (state n x (y - 1)).toNat + (state n x (y + 1)).toNat))

def onCount (n : ℕ) : ℤ :=
  (((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter fun p : ℕ × ℕ =>
    state n ((p.1 : ℤ) - n) ((p.2 : ℤ) - n)).card : ℤ)

def a (n : ℕ) : ℤ := onCount (n + 1) - onCount n

theorem main :
    (∀ n : ℕ, 9 < n → a n = ((a (n - 2) + a (n - 4)) - a (n - 6))) ∧
    (PowerSeries.mk a * ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2)) =
      (4 + 7 * X + 4 * X ^ 2 + 5 * X ^ 3 + 5 * X ^ 5 - 12 * X ^ 6 - X ^ 7 + 4 * X ^ 8 + 4 * X ^ 9 - 4 * X ^ 11 : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a270082
