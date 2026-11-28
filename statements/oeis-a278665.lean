import Mathlib

/-!
# A278665: Binary representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 62, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A278665 (OEIS Foundation, CC BY-SA 4.0).
Conjectures: Colin Barker, Nov 26 2016.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has one ON cell at the origin. The rule updates the whole integer plane
using bit c + 2s, with s the sum of the four orthogonal neighbors and c the center.
The x-axis is read in base 10 with the origin most significant.
The sequence starts at index 0. The ordinary generating function is cross-multiplied in ℤ⟦X⟧.
-/

namespace OMA.S_oeis_a278665

open PowerSeries

def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | n + 1, x, y => Nat.testBit 62 ((state n x y).toNat + 2 *
      ((state n (x - 1) y).toNat + (state n (x + 1) y).toNat +
       (state n x (y - 1)).toNat + (state n x (y + 1)).toNat))

def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), ((state n (j : ℤ) 0).toNat : ℤ) * 10 ^ (n - j)

theorem main :
    (∀ n : ℕ, 7 < n → a n = (((10 * a (n - 1)) + a (n - 4)) - (10 * a (n - 5)))) ∧
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + X ^ 2)) =
      (1 + X - 99 * X ^ 2 - 99 * X ^ 3 - 100 * X ^ 4 + 9900 * X ^ 5 + 10000 * X ^ 6 - 1000000 * X ^ 7 + 1000000 * X ^ 10 : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a278665
