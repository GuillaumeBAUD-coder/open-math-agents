import Mathlib

/-!
# A conjecture about `8n+6`

Source: https://math.stackexchange.com/questions/2751545 (2018).
Credit: @jagraj28

The post states the claim: for every nonnegative integer `n`, `8n + 6 = a ^ 2 + 2p` for a
nonnegative integer `a` and a prime `p`. The post tests it for `n ≤ 2 · 10 ^ 6`, a comment for
`8n + 6 ≤ 10 ^ 9`; the one answer shows only that `p ≥ 5` in any such representation. It is
inspired by Euler's conjecture about `8n + 3`.

Formalization notes:
* `n` and `a` are natural numbers (nonnegative integers), `p` is a prime natural number.
* A direct search confirms the claim for every `n < 10 ^ 6`.
-/

namespace OMA.S_mse_2751545

/-- Every `8n + 6` is a square plus twice a prime. -/
theorem main : ∀ n : ℕ, ∃ a p : ℕ, p.Prime ∧ 8 * n + 6 = a ^ 2 + 2 * p := by
  sorry

end OMA.S_mse_2751545
