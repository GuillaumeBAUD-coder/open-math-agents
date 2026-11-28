import Mathlib

/-!
# A007531: when is n^3 - n a factorial?

Source: https://oeis.org/A007531
Credit: @jagraj28

A007531 is `a(n) = n(n-1)(n-2)`. The entry records a conjecture of Ed Pegg Jr: `n^3 - n = k!`
has a solution if and only if `n` is 2, 3, 5 or 9 (when `k` is 3, 4, 5 and 6).

`main` states: the set of natural numbers `n` such that `n^3 - n = k!` for some natural `k` is
`{2, 3, 5, 9}`.

Conventions: `n` and `k` range over the natural numbers; `n^3 - n` is exact in `ℕ` because
`n ≤ n^3`. For `n = 0, 1` the left side is `0`, which is no factorial. A search for `n < 10^6`
finds exactly `n = 2, 3, 5, 9`.
-/

namespace OMA.S_oeis_a007531

/-- Pegg's conjecture in OEIS A007531. -/
theorem main : {n : ℕ | ∃ k : ℕ, n ^ 3 - n = k.factorial} = {2, 3, 5, 9} := by
  sorry

end OMA.S_oeis_a007531
