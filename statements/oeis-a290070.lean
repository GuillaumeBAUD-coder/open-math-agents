import Mathlib

/-!
# OEIS A290070

Binary representation of the diagonal from the corner to the origin of the n-th stage of
growth of the two-dimensional cellular automaton defined by Rule 641, based on the 5-celled
von Neumann neighborhood.

Source: https://oeis.org/A290070
Referenced sequence: https://oeis.org/A283504
Conjectures: Colin Barker, Jul 20 2017.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has a single ON cell at the origin. Each cell of the integer plane updates using
rule bit c+2s, where c is its current state and s counts its four orthogonal ON neighbors.
The diagonal runs from corner to origin inclusive. Its first cell is the most significant
digit in base 10. The last line of %t extracts the central row and disagrees with the
published terms. The diagonal follows %N and the published data.
-/

namespace OMA.S_oeis_a290070

open PowerSeries

/-- Synchronous evolution on the integer plane from one ON cell. -/
def state (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t+1, x, y =>
    let s := state r t
    r.testBit ((s x y).toNat + 2 * ((s (x-1) y).toNat + (s (x+1) y).toNat +
      (s x (y-1)).toNat + (s x (y+1)).toNat))

/-- Read the diagonal from corner to origin, most significant digit first. -/
def digits (r n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n+1), ((state r n ((i : ℤ) - n) ((i : ℤ) - n)).toNat : ℤ) * 10 ^ (n-i)

def a (n : ℕ) : ℤ := digits 641 n

/-- A283504 reads the central row of Rule 641 from its left edge to the origin. -/
def A283504 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n+1), ((state 641 n ((i : ℤ)-n) 0).toNat : ℤ) * 10^(n-i)

theorem main :
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X)) =
      1 + 90 * X^3 + 100 * X^4) ∧
    (∀ n : ℕ, 4 < n →
      a n = 10*a (n-1) + a (n-2) - 10*a (n-3) ∧ a n = A283504 n) := by
  sorry

end OMA.S_oeis_a290070
