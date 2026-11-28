import Mathlib

/-!
# A081672: Expansion of exp(2x) - exp(0) + BesselI_0(2x)

Source: https://oeis.org/A081672
Credit: @sntntHb

The sequence (offset 0: `1, 2, 6, 8, 22, 32, 84, 128, ...`) is the e.g.f. expansion of
`exp(2x) - exp(0) + BesselI_0(2x)`. Since `exp(2x) = Sum 2^n x^n/n!`,
`exp(0) = 1` and `BesselI_0(2x) = Sum_k x^(2k)/(k!)^2`, the coefficient of `x^n/n!` is
`2^n - [n = 0] + [n even] * binomial(n, n/2)`, which we use as the definition
(this matches the entry: for odd `n`, `a(n) = 2^n`; for even `n > 0`, `a(n) = 2^n*(1+n!/(2^n*(n/2)!^2))`).
The entry records the conjecture (R. J. Mathar, Nov 12 2012):
`Conjecture: n*a(n) +2*(1-n)*a(n-1) +4*(1-n)*a(n-2) +8*(n-2)*a(n-3)=0.`

The recurrence involves `a(n-3)`; at `n = 3` it fails (the left side is `-8`, because of the
`- exp(0)` correction at `n = 0`), so it is stated for `n ≥ 4`. The identity is stated over `ℤ`.
-/

namespace OMA.S_oeis_a081672

/-- `a n = 2^n - [n = 0] + [n even] * binomial(n, n/2)` (OEIS A081672). -/
def a (n : ℕ) : ℤ :=
  2 ^ n - (if n = 0 then 1 else 0) + (if Even n then (Nat.choose n (n / 2) : ℤ) else 0)

/-- R. J. Mathar's conjectured recurrence for OEIS A081672 (for `n ≥ 4`). -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (n : ℤ) * a n + 2 * (1 - (n : ℤ)) * a (n - 1) + 4 * (1 - (n : ℤ)) * a (n - 2) +
      8 * ((n : ℤ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a081672
