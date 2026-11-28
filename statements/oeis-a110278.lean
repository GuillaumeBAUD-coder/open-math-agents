import Mathlib

/-!
# A110278: Numbers n such that the perfect deficiency of n and n + 1 are both squares

Source: https://oeis.org/A110278

Conjecture (OEIS A110278):
There are infinitely many positive integers `n` such that both `A109883(n)` and
`A109883(n + 1)` are perfect squares, where `A109883(m)` is the perfect deficiency of `m`:
start with `m` and subtract its divisors in increasing order, beginning with `1`, stopping as
soon as the next divisor exceeds the current remainder.

Conventions:
- Offset: `1`; known terms: `1, 4, 5, 16, 37, 256, 65536, 80656, 3459600, 166926400`.
- `A109883(1) = 0` (`1 - 1 = 0`).
- For `m = 18`, the divisors in increasing order are `1, 2, 3, 6, 9, 18`, giving
  `18 → 17 → 15 → 12 → 6`, and `9 > 6` stops, so `A109883(18) = 6`.
- For `m = 50`: `50 → 49 → 47 → 42 → 32 → 7`, and `50 > 7` stops, so `A109883(50) = 7`.
-/

namespace OMA.S_oeis_a110278

/-- Subtract the divisors of a list in order from the remainder `r`, stopping at the first
divisor that exceeds the current remainder. -/
def peel : ℕ → List ℕ → ℕ
  | r, [] => r
  | r, d :: ds => if r < d then r else peel (r - d) ds

/-- Perfect deficiency of `m : ℕ` (OEIS A109883): subtract the divisors of `m` (including `m`)
in increasing order, starting from `1`, until the next divisor exceeds the remainder. -/
def greedyDeficiency (m : ℕ) : ℕ :=
  peel m ((List.range (m + 1)).filter (fun d => decide (1 ≤ d ∧ d ∣ m)))

/-- Predicate stating that `k : ℕ` is a perfect square. -/
def IsNatSquare (k : ℕ) : Prop :=
  ∃ r : ℕ, k = r ^ 2

/-- The set of positive integers `n` whose perfect deficiency and that of `n + 1`
are both squares (OEIS A110278). -/
def S : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ IsNatSquare (greedyDeficiency n) ∧ IsNatSquare (greedyDeficiency (n + 1))}

/-- Conjecture: the sequence A110278 is infinite. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a110278
