import Mathlib

/-!
# A177198: a(n+1) = Sum_{p=0..n} (a(p)*a(n-p)+k) + l for n >= 1, a(0)=1, a(1)=7, k=-1, l=1

Source: https://oeis.org/A177198 (conjecture by R. J. Mathar, Nov 27 2011)

`a(n)` (offset 0) is defined by `a(0) = 1`, `a(1) = 7` and, for `n >= 1`,
`a(n+1) = Sum_{p=0..n} (a(p)*a(n-p) + k) + l` with `k = -1`, `l = 1`; below the recursion
is written for `a(n+2)` with `p` ranging over `Fin (n+2)`.

The conjecture, stated for `n >= 5` (where every index is defined):
Conjecture: (n+1)*a(n) +(2-7n)*a(n-1) +9*(3-n)*a(n-2) +9*(7n-22)*a(n-3) +72*(4-n)*a(n-4) +24*(n-5)*a(n-5)=0.
-/

namespace OMA.S_oeis_a177198

open PowerSeries

/-- The sequence A177198. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 7
  | n + 2 => (∑ p : Fin (n + 2), (a p * a (n + 1 - p) + (-1))) + 1
decreasing_by all_goals omega

theorem main : ∀ n : ℕ, 5 ≤ n →
      (((n : ℤ)+1)) * a n +
        ((2-7*(n : ℤ))) * a (n - 1) +
        (9*(3-(n : ℤ))) * a (n - 2) +
        (9*(7*(n : ℤ)-22)) * a (n - 3) +
        (72*(4-(n : ℤ))) * a (n - 4) +
        (24*((n : ℤ)-5)) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a177198
