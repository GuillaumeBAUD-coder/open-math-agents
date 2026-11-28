import Mathlib

/-!
# A048651: Series identity for Product_{k >= 1} (1 - 1/2^k)

Source: https://oeis.org/A048651
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A048651: Decimal expansion of Product_{k >= 1} (1 - 1/2^k).

Statement:
(Sum_{k>0} (4^k-1)/(Product_{i=1..k} ((4^i-1)*(2*4^i-1))))*2 =
2/7 + 2/(3*7*31) + 2/(3*7*15*31*127) + ... = Product_{k >= 1} (1 - 1/2^k) (conjecture).

Conventions:
- Both the infinite product and infinite series are indexed over `k : ℕ` with `k + 1`
  representing the 1-indexed summation/product index.
-/

namespace OMA.S_oeis_a048651

theorem main :
    ∏' (k : ℕ), (1 - (1 : ℝ) / (2 : ℝ) ^ (k + 1)) =
      2 * ∑' (k : ℕ), ((4 : ℝ) ^ (k + 1) - 1) /
        (∏ i ∈ Finset.Icc 1 (k + 1), (((4 : ℝ) ^ i - 1) * (2 * (4 : ℝ) ^ i - 1))) := by
  sorry

end OMA.S_oeis_a048651
