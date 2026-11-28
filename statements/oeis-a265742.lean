import Mathlib

/-!
# A265742: Numbers k such that [e*k - 1/k, e*k + 1/k] contains an integer, e = 2.71828...

Source: https://oeis.org/A265742
Credit: @xor2k
Sibling of OEIS A265739 (same conjecture wording); statement modelled on the accepted one for that entry.

Formalizes the OEIS A265742 conjecture (offset 1): the sequence is infinite, i.e. there are
infinitely many positive integers `k` such that the closed interval `[e * k - 1 / k, e * k + 1 / k]`
contains an integer.

Conventions: Euler's number `e` is `Real.exp 1`; `k` ranges over positive natural numbers
(encoded by `1 ≤ k`, as `1 / k` must make sense); an integer `m` lies in the interval exactly
when `|e * k - m| ≤ 1 / k`.
-/

namespace OMA.S_oeis_a265742

/-- Infinitely many positive integers `k` admit an integer within `1 / k` of `e * k`. -/
theorem main :
    Set.Infinite {k : ℕ | 1 ≤ k ∧
      ∃ m : ℤ, |Real.exp 1 * (k : ℝ) - (m : ℝ)| ≤ 1 / (k : ℝ)} := by
  sorry

end OMA.S_oeis_a265742
