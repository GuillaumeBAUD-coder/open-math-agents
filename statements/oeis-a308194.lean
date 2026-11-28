import Mathlib

/-!
# OEIS A308194: iterating A063655 from any n ≥ 5 reaches 5

Source: https://oeis.org/A308194
Credit: @SudharsanAnimations

A308194(n) is the number of steps to reach 5 when iterating `x ↦ A063655(x)` from `x = n`, where
A063655(n) is the smallest semiperimeter `b + d` of an integral rectangle of area `b · d = n`. Ali Sada
conjectured that every `n ≥ 5` eventually reaches 5; the entry records that this is easy to show
(composites `> 5` map to smaller numbers, primes `> 5` drop in two steps, and nothing `≥ 5` maps
below 5). We state this proved result.

Conventions: `f n` is the least value of `b + n / b` over the divisors `b` of `n` (for `n ≥ 1` this is
the smallest semiperimeter; the value at `0` is irrelevant). `f^[k]` is the `k`-fold iterate.
-/

namespace OMA.S_oeis_a308194

/-- OEIS A063655: the smallest semiperimeter `b + d` of an integral rectangle with area
`b · d = n`, i.e. the least value of `b + n / b` over the divisors `b` of `n`. -/
noncomputable def f (n : ℕ) : ℕ := sInf ((fun b => b + n / b) '' {b | b ∣ n})

theorem main : ∀ n : ℕ, 5 ≤ n → ∃ k : ℕ, f^[k] n = 5 := by
  sorry

end OMA.S_oeis_a308194
