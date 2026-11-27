import Mathlib

/-!
# A000033: a(n) = A058087(n, n-2).

Source: https://oeis.org/A000033
Credit: @rabdelaal

The entries are the coefficient of `t ^ 2` in `p(t) = Sum_{k=0..n} 2n*C(2n-k, k)*(n-k)!*
(t-1)^k / (2n-k)` (the explicit formula of OEIS A000033).

OEIS A000033 records the conjecture (Mark van Hoeij, 2019) that `a(n) + 2*a(n+p) +
a(n+2p)` is divisible by `p` for any prime `p`.
-/

namespace OMA.S_oeis_a000033

open Polynomial

/-- The polynomial whose `t ^ 2`-coefficient is the OEIS A000033 entry `a n`:
`Sum_{k=0..n} 2n*C(2n-k, k)*(n-k)!*(t-1)^k / (2n-k)`. -/
noncomputable def p (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    (C ((2 * n * Nat.choose (2 * n - k) k * (n - k).factorial : ℚ) / (2 * n - k : ℚ)) *
      (X - C 1) ^ k)

/-- The OEIS A000033 entry `a n`, as the coefficient of `t ^ 2` in `p n`. -/
noncomputable def a (n : ℕ) : ℚ :=
  (p n).coeff 2

/-- The conjecture recorded in OEIS A000033: `a(n) + 2*a(n+p) + a(n+2p)` is divisible by
`p` for any prime `p` (with `n ≥ 1`). -/
theorem main : ∀ (n p : ℕ), 1 ≤ n → Nat.Prime p →
    ∃ m : ℕ, (m : ℚ) = a n + 2 * a (n + p) + a (n + 2 * p) ∧ m % p = 0 := by
  sorry

end OMA.S_oeis_a000033
