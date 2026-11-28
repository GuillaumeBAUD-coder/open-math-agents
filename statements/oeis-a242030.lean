import Mathlib

/-!
# A242030: the Collatz variation x -> x/2 + 1 (even), 3x - 1 (odd) always reaches 8

Source: https://oeis.org/A242030 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A242030 (offset 1): irregular triangle read by rows of a variation of the Collatz iteration with
signature (1,1); rows (3, 8), (4, 3, 8), (5, 14, 8), (6, 4, 3, 8), ...

The entry records:

  It is conjectured that the trajectory of this Collatz-like iteration arrives at 8 in a finite
  number of steps for any initial value x, (x>2). The iterative step is divide by 2 and add 1 if
  even, or multiply by 3 and subtract 1 if odd.

Reading of the source:
* The map is `f x = x / 2 + 1` for even `x` and `f x = 3x - 1` for odd `x` (matching the rows:
  3 -> 8, 4 -> 3, 5 -> 14 -> 8, 6 -> 4).
* "arrives at 8 in a finite number of steps for any initial value x > 2": for every `x > 2` some
  iterate `f^[k] x` equals 8.
-/

namespace OMA.S_oeis_a242030

/-- The iteration: halve and add 1 if even, triple and subtract 1 if odd. -/
def f (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 + 1 else 3 * x - 1

/-- Every trajectory starting above 2 reaches 8. -/
theorem main : ∀ x : ℕ, 2 < x → ∃ k : ℕ, f^[k] x = 8 := by
  sorry

end OMA.S_oeis_a242030
