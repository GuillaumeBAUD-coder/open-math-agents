import Mathlib

/-!
# A000079: Powers of 2: a(n) = 2^n.

Source: https://oeis.org/A000079
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a000079

/-- One step of the hailstone sequence. -/
def hailstoneStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The value of the hailstone sequence starting at `n` after `k` steps. -/
def hailstoneAfter : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => hailstoneAfter k (hailstoneStep n)

/-- Powers of two, including `1 = 2^0`, as required for the restatement of the
Collatz conjecture given in the source. -/
def IsPowerOfTwo (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 2 ^ k

theorem main : ∀ n : ℕ, 0 < n → ∃ k : ℕ, IsPowerOfTwo (hailstoneAfter k n) := by
  sorry

end OMA.S_oeis_a000079
