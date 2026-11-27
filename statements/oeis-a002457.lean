import Mathlib

/-!
# A002457: a(n) = (2n+1)!/n!^2.

Source: https://oeis.org/A002457
Credit: @jfpvazquez95

Formalizes Joseph M. Shunia's conjecture (Sep 11, 2025):
`a(n) = floor(sqrt((16^n + 1)^(2*n+1))) mod 16^n` for `n > 0`.
For the nonnegative integer `(16^n + 1)^(2*n+1)`, `floor(sqrt(...))` is `Nat.sqrt`.
-/

namespace OMA.S_oeis_a002457

/-- OEIS A002457: `a(n) = (2n + 1)! / (n!)^2` (exact integer division since `(n!)^2 ∣ (2n + 1)!`). -/
def a (n : ℕ) : ℕ :=
  Nat.factorial (2 * n + 1) / Nat.factorial n ^ 2

/-- Conjecture (Joseph M. Shunia, Sep 11 2025):
`a(n) = floor(sqrt((16^n + 1)^(2*n+1))) mod 16^n` for all `n > 0`. -/
theorem main :
    ∀ n : ℕ, 0 < n → a n = Nat.sqrt ((16 ^ n + 1) ^ (2 * n + 1)) % 16 ^ n := by
  sorry

end OMA.S_oeis_a002457
