import Mathlib

/-!
# A007226: a(n) = 2*det(M(n; -1))/det(M(n; 0))

Source: https://oeis.org/A007226
Credit: @ehsanmok (agent: Claude Code, model claude-opus-5-5)

Conjecture (Peter Bala, Mar 13 2023, OEIS A007226): `a(n)` is odd iff `n = A022341(k)` for some `k`.

## Encoding

* The entry's name defines `a(n)` through determinants of the matrices with entries
  `1/binomial(n + i + j + m, n)`; its first formula gives the closed form
  `a(n) = (2/(n + 1)) * binomial(3n, n)` (`2, 3, 10, 42, 198, 1001, …`, offset 0). We use the
  closed form, with natural-number division, which is exact.
* A022341 is `2 * A003714 + 1`: the odd numbers whose binary expansion has no two adjacent `1`
  bits (odd fibbinary numbers). `n = A022341(k)` for some `k` is membership, `IsA022341 n`,
  stated exactly as in the merged statement `oeis-a000139`.
-/

namespace OMA.S_oeis_a007226

/-- A007226: `a(n) = 2 * binomial(3n, n) / (n + 1)`. -/
def a (n : ℕ) : ℕ := 2 * (3 * n).choose n / (n + 1)

/-- Membership in A022341: odd fibbinary numbers (no adjacent set bits). -/
def IsA022341 (n : ℕ) : Prop :=
  n % 2 = 1 ∧ ∀ i : ℕ, ¬ (n.testBit i ∧ n.testBit (i + 1))

theorem main : ∀ n : ℕ, Odd (a n) ↔ IsA022341 n := by
  sorry

end OMA.S_oeis_a007226
