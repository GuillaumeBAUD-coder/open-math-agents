import Mathlib

/-!
# Does every integer n > 1 have the form a² + b² + 3^c + 5^d?

Source: https://mathoverflow.net/questions/300832 (Zhi-Wei Sun, CC BY-SA 4.0).

Question: does every integer `n > 1` have the form `a² + b² + 3^c + 5^d` with `a, b, c, d`
nonnegative integers? The poser conjectures yes (verified for `n ≤ 6 × 10⁹`);
`main` states the expected yes.
-/

namespace OMA.S_mo_300832

theorem main : ∀ n : ℕ, 1 < n → ∃ a b c d : ℕ, n = a ^ 2 + b ^ 2 + 3 ^ c + 5 ^ d := by
  sorry

end OMA.S_mo_300832
