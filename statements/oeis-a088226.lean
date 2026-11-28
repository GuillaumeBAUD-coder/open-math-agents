import Mathlib

/-!
# A088226: a(1)=0, a(2)=0, a(3)=1; for n>3, a(n) = abs(a(n-1) - a(n-2) - a(n-3)).

Source: https://oeis.org/A088226

The conjecture, as written in the OEIS comment by Ralf Stephan (Sep 23 2013):
a(n) is m/2, where m is the smallest even distance from n to a square.

Translation notes for the reviewer.
* The sequence has OEIS offset 1. `a 0 = 0` is a filler value that the theorem never uses.
* A square is `k ^ 2` for a natural number `k` (0, 1, 4, 9, ...).
* The distance from n to a square is `|n - k ^ 2|`. Among the even ones, m is the least.
* `a n = m / 2` is written `m = 2 * a n`, which is the same thing because m is even.
* The statement is kept exactly as the source words it, with the source's indexing.
-/

namespace OMA.S_oeis_a088226

/-- A088226 with OEIS offset 1: `a 1 = 0`, `a 2 = 0`, `a 3 = 1`, and
`a n = |a (n-1) - a (n-2) - a (n-3)|` for `n > 3`. `a 0 = 0` is unused filler. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | n + 4 => |a (n + 3) - a (n + 2) - a (n + 1)|

/-- Ralf Stephan's conjecture: for every `n ≥ 1`, `a n = m / 2`, where `m` is the smallest
even distance from `n` to a square. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ m : ℕ, IsLeast {d : ℕ | Even d ∧ ∃ k : ℕ, (d : ℤ) = |(n : ℤ) - (k : ℤ) ^ 2|} m ∧
      (m : ℤ) = 2 * a n := by
  sorry

end OMA.S_oeis_a088226
