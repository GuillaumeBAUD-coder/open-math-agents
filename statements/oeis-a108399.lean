import Mathlib

/-!
# A108399: a golden semiprime n^2 + k with k < n^3

Source: https://oeis.org/A108399
Credit: @coleman415

The sequence is `a(n)` = least positive `k` such that `n^2 + k` is a golden semiprime (A108540).
The entry records: *Conjecture: for every n > 1 there exists a number k < n^3 such that n^2 + k
is a golden semiprime.*

Conventions:
- A golden semiprime (OEIS A108540) is a number `p * q` with `p`, `q` prime and
  `|p * phi - q| < 1`, where `phi = (1 + sqrt 5) / 2` is the golden ratio
  (for example `589 = 19 * 31` and `|19 * phi - 31| < 1`).
- `k` is positive, as in the definition of the sequence (`n^2` itself is never a golden
  semiprime: `|p * phi - p| < 1` has no prime solution).
-/

namespace OMA.S_oeis_a108399

/-- `n` is a golden semiprime (OEIS A108540): `n = p * q` with `p`, `q` prime and
`|p * phi - q| < 1`, `phi` the golden ratio. -/
def IsGoldenSemiprime (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q ∧
    |(p : ℝ) * ((1 + Real.sqrt 5) / 2) - (q : ℝ)| < 1

/-- The conjecture of OEIS A108399. -/
theorem main :
    ∀ n : ℕ, 1 < n → ∃ k : ℕ, 0 < k ∧ k < n ^ 3 ∧ IsGoldenSemiprime (n ^ 2 + k) := by
  sorry

end OMA.S_oeis_a108399
