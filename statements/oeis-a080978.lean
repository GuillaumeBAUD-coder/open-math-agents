import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a080978

/-- OEIS A006046: `∑_{i=0}^{n-1} 2^(wt(i))`, where `wt(i)` is the binary weight (popcount) of `i`. -/
def a006046 (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 2 ^ (Nat.digits 2 i).sum

/-- OEIS A080978: `a(n) = 2 * A006046(n) + 1`. -/
def a080978 (n : ℕ) : ℕ :=
  2 * a006046 n + 1

/-- OEIS A131136: denominator of the `n`-th exponential Taylor coefficient of
`log((x/2 - 1)/(x - 1)) = log(1 - x/2) - log(1 - x) = ∑_{n ≥ 1} (1 - 2^(-n)) x^n / n`,
whose `n`-th exponential coefficient is `0` for `n = 0` and `(n - 1)! * (1 - 2^(-n))` for `n ≥ 1`. -/
def a131136 (n : ℕ) : ℕ :=
  if n = 0 then 1 else (((n - 1).factorial : ℚ) * (1 - (2 : ℚ)⁻¹ ^ n)).den

/-- OEIS A080978 conjecture (Sean A. Irvine, Jun 25 2022):
`a080978` is the sequence of partial sums of `A131136`. -/
theorem main :
    ∀ n : ℕ, a080978 n = ∑ k ∈ Finset.range (n + 1), a131136 k := by
  sorry

end OMA.S_oeis_a080978
