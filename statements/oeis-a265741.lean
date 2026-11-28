import Mathlib

/-!
# A265741: Integers in the interval [e*k - 1/k, e*k + 1/k] for some k > 0, where e = 2.71828...

Source: https://oeis.org/A265741
Credit: @xor2k
Sibling of OEIS A265735 (same conjecture wording); statement modelled on the accepted one for that entry.

Conjecture (OEIS A265741): the sequence is infinite.

Conventions: the sequence is the set of integers `m` for which there exists a positive
integer `k` such that `m` lies in the closed interval `[e * k - 1 / k, e * k + 1 / k]`,
where Euler's number `e` is `Real.exp 1`. Thus `k` ranges over positive natural numbers,
encoded by `1 ≤ k`, and the endpoint condition is written as `|e * k - m| ≤ 1 / k`.
The offset of the OEIS sequence is 1. The sequence lists these integers in increasing order
without repetition, so it is infinite exactly when the set of such integers is infinite.
-/

namespace OMA.S_oeis_a265741

/-- `m` is one of the integers lying in `[e * k - 1 / k, e * k + 1 / k]` for some
positive integer `k`. -/
def IsTerm (m : ℤ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ |Real.exp 1 * (k : ℝ) - (m : ℝ)| ≤ 1 / (k : ℝ)

/-- The sequence of integers in `[e * k - 1 / k, e * k + 1 / k]`, for some `k > 0`,
is infinite. -/
theorem main : Set.Infinite {m : ℤ | IsTerm m} := by
  sorry

end OMA.S_oeis_a265741
