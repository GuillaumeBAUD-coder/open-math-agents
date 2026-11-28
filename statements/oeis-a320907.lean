import Mathlib

/-!
# Row sums of A320906

Source: https://oeis.org/A320907 and https://oeis.org/A320906

The triangle A320906 is defined for `n ≥ 0` and `0 ≤ k ≤ n` by
`T(n, k) = binomial(2*n - k, k - 1) * hypergeom([2, 2, 1 - k], [1, 2*(1 - k + n)], -1)`.
Since `1 - k` is a nonpositive integer for `k ≥ 1`, the generalized hypergeometric series
terminates after `k` terms (indices `0 ≤ m < k`), and for `k = 0` the prefactor
`binomial(2*n, -1)` is `0`.

We formalize both of Colin Barker's October 28, 2018 conjectures for the row sums
`a(n) = ∑_{k=0..n} T(n, k)`:
1. The order-5 linear recurrence
   `a(n) = 9*a(n-1) - 31*a(n-2) + 50*a(n-3) - 36*a(n-4) + 8*a(n-5)` for `n > 4`.
2. The rational generating function
   `G.f.: x*(1 - x)^2 / ((1 - 2*x)^3*(1 - 3*x + x^2))`,
   written after clearing the denominator (which has constant coefficient 1).
-/

namespace OMA.S_oeis_a320907

/-- Rising factorial `(x)_m = x * (x + 1) * ... * (x + m - 1)`. -/
def rising (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | m + 1 => rising x m * (x + (m : ℚ))

/-- The triangle A320906:
`T(n, k) = binomial(2*n - k, k - 1) * hypergeom([2, 2, 1 - k], [1, 2*(1 - k + n)], -1)`
for `n ≥ 0` and `0 ≤ k ≤ n`. -/
def T (n k : ℕ) : ℚ :=
  if k = 0 then 0
  else
    (Nat.choose (2 * n - k) (k - 1) : ℚ) *
      ∑ m ∈ Finset.range k,
        (rising 2 m * rising 2 m * rising (1 - (k : ℚ)) m) /
          (rising 1 m * rising (2 * (1 - (k : ℚ) + (n : ℚ))) m * (Nat.factorial m : ℚ)) *
          (-1 : ℚ) ^ m

/-- A320907: row sums `a(n) = ∑_{k=0..n} T(n, k)` of A320906. -/
def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), T n k

open PowerSeries

theorem main :
    (∀ n : ℕ,
      a (n + 5) = 9 * a (n + 4) - 31 * a (n + 3) + 50 * a (n + 2) - 36 * a (n + 1) + 8 * a n) ∧
    ((1 - 2 * X) ^ 3 * (1 - 3 * X + X ^ 2) : PowerSeries ℚ) * PowerSeries.mk a =
      (X * (1 - X) ^ 2 : PowerSeries ℚ) := by
  sorry

end OMA.S_oeis_a320907
