import Mathlib

/-!
# A054030: Sigma(k)/k for k such that sigma(k) is divisible by k.

Source: https://oeis.org/A054030
Credit: @<your GitHub handle>

The entry records (T. D. Noe, Nov 04 2007): "The graph supports the conjecture that all numbers
except 2 appear only a finite number of times."

Conventions (please review):
* `σ` is `ArithmeticFunction.sigma 1`. The sequence lists `σ(n)/n` for the multiply-perfect numbers
  `n ≥ 1` (A007691, `n ∣ σ(n)`), in increasing order of `n`. So the value `k` appears in the
  sequence exactly once for each positive `n` with `σ(n) = k * n`.
* "Appears only a finite number of times" for `k` means: the set of positive `n` with
  `σ(n) = k * n` is finite. We state this for every natural number `k ≠ 2` (for `k = 0` the set is
  empty, and for `k = 1` it is `{1}`). Nothing is claimed about `k = 2` (the perfect numbers, whose
  infinitude is a separate open problem).
* This is the uniform statement over all `k ≠ 2`; the cases `k = 5` and `k = 6` alone are the
  existing statements `oeis-a046060` and `oeis-a046061`.
-/

namespace OMA.S_oeis_a054030

open ArithmeticFunction

/-- Noe's conjecture in OEIS A054030: every value `k ≠ 2` occurs only finitely often as the
abundancy `σ(n)/n` of a multiply-perfect number `n`. -/
theorem main : ∀ k : ℕ, k ≠ 2 → {n : ℕ | 0 < n ∧ sigma 1 n = k * n}.Finite := by
  sorry

end OMA.S_oeis_a054030
