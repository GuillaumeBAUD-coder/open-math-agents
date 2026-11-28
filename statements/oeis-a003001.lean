import Mathlib

/-!
# OEIS A003001: reduced numbers of a given multiplicative persistence

Source: https://oeis.org/A003001
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`p10(n)` is the product of the decimal digits of `n`. A number `n` is a class representative
(reduced number) if it is the smallest number with its digit product: `p10(m) = p10(n)` implies
`m ≥ n`. The multiplicative persistence of `n` is the number of applications of `p10` needed to
reach a single digit.

Conjecture (A. H. M. Smeets, OEIS entry): for every multiplicative persistence other than `2`,
the set of class representative numbers with that persistence is finite.

Conventions:
* `p10(0) = 0`, the product of the digits of the one-digit number `0`.
* The persistence of `n` is the least `k` with `p10^[k](n) < 10` (it exists since
  `p10(n) < n` for `n ≥ 10`).
-/

namespace OMA.S_oeis_a003001

/-- The product of the decimal digits of `n` (with `p10(0) = 0`). -/
def p10 (n : ℕ) : ℕ :=
  if n = 0 then 0 else (Nat.digits 10 n).prod

/-- The multiplicative persistence of `n`. -/
noncomputable def persistence (n : ℕ) : ℕ :=
  sInf {k : ℕ | p10^[k] n < 10}

/-- `n` is the smallest number with its digit product. -/
def IsReduced (n : ℕ) : Prop :=
  ∀ m : ℕ, p10 m = p10 n → n ≤ m

/-- For every persistence `p ≠ 2` there are only finitely many reduced numbers of persistence
`p`. -/
theorem main : ∀ p : ℕ, p ≠ 2 → {n : ℕ | IsReduced n ∧ persistence n = p}.Finite := by
  sorry

end OMA.S_oeis_a003001
