import Mathlib

/-!
# A004001: Hofstadter-Conway $10000 sequence.

Source: https://oeis.org/A004001
Credit: @rabdelaal

`a 1 = a 2 = 1`, `a n = a (a (n-1)) + a (n - a (n-1))` for `n >= 3` (OEIS A004001).

OEIS A004001 records the conjecture (Daniel Forgues, 2019): `a(n) = n/2` iff `n` is a
power of two `2^k` with `k >= 1`.

Formalization: `a` is defined by well-founded recursion. For `n >= 3` both recursive
indices `a (n-1)` and `n - a (n-1)` lie in `[1, n-1]`, because `1 <= a m <= m` for every
`m >= 1` (a standard invariant of the recursion); the guard below only makes this visible
to Lean and is always satisfied, so `a` agrees with A004001 for every `n >= 1`
(`a 0 = 0` is a padding value outside the offset). Fix by @sntntHb: the previous
definition did not unfold the recursion and gave `a n = n + 2` for every `n >= 1`.
-/

namespace OMA.S_oeis_a004001

/-- The Hofstadter-Conway `$10000` sequence, offset 1, with padding `a 0 = 0`. -/
def a (n : ℕ) : ℕ :=
  if h0 : n = 0 then 0
  else if h2 : n ≤ 2 then 1
  else
    have : n - 1 < n := by omega
    let p := a (n - 1)
    if h : 0 < p ∧ p < n then
      have : n - p < n := by omega
      a p + a (n - p)
    else 0

/-- `n` is a nontrivial power of two. -/
def IsPowTwo (n : ℕ) : Prop := ∃ k ≥ 1, n = 2 ^ k

/-- The conjecture recorded in OEIS A004001 (Forgues): `a(n) = n/2` iff `n = 2^k, k>=1`
(stated for `n >= 1`). -/
theorem main : ∀ n ≥ 1, a n * 2 = n ↔ IsPowTwo n := by
  sorry

end OMA.S_oeis_a004001
