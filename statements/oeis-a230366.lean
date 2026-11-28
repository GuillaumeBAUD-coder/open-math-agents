import Mathlib

/-!
# A230366: a(n) = Sum_{k=1..floor(n/2)} (k^2 mod n) (infinitely many consecutive square pairs)

Source: https://oeis.org/A230366 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A230366 (offset 1): a(n) = Sum_{k=1..floor(n/2)} (k^2 mod n); data
0, 1, 1, 1, 5, 8, 7, 6, 12, 25, ...

The entry records:

  a(26) and a(27) are both squares. Conjecture: the number of n such that a(n) and a(n+1) are
  both squares is infinite.

Reading of the source:
* `a n = ∑_{k=1}^{⌊n/2⌋} (k^2 mod n)` for `n ≥ 1`.
* "squares" are perfect squares of natural numbers (0 = 0^2 included; a(1) = 0).
* "the number of n ... is infinite": the set of `n ≥ 1` such that `a(n)` and `a(n+1)` are both
  squares is infinite.
-/

namespace OMA.S_oeis_a230366

/-- A230366(n) = ∑_{k=1}^{⌊n/2⌋} (k^2 mod n). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 (n / 2), k ^ 2 % n

/-- Infinitely many `n` have `a(n)` and `a(n+1)` both perfect squares. -/
theorem main : {n : ℕ | 1 ≤ n ∧ IsSquare (a n) ∧ IsSquare (a (n + 1))}.Infinite := by
  sorry

end OMA.S_oeis_a230366
