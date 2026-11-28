import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Card

namespace OMA.S_oeis_a307864

/-- OEIS A307864: `a n` is the number of natural bases `b < 2 * n + 1` such that
`b ^ n ≡ 1 [MOD 2 * n + 1]`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1)).filter fun b => b ^ n % (2 * n + 1) = 1).card

/-- An odd integer `m = 2 * n + 1` is an absolute Euler pseudoprime (Lehmer / OEIS A033181)
if `m` is composite (`1 < m` and `¬ m.Prime`) and for every `b` coprime to `m`,
`b ^ n ≡ 1 [MOD m]` or `b ^ n ≡ m - 1 [MOD m]` (i.e. `b ^ ((m - 1) / 2) ≡ ±1 (mod m)`). -/
def IsAbsEulerPseudoprime (n : ℕ) : Prop :=
  1 ≤ n ∧ ¬ Nat.Prime (2 * n + 1) ∧
    ∀ b : ℕ, Nat.Coprime b (2 * n + 1) →
      b ^ n ≡ 1 [MOD 2 * n + 1] ∨ b ^ n ≡ 2 * n [MOD 2 * n + 1]

/-- Conjecture on OEIS A307864:
if `2 * n + 1` is an absolute Euler pseudoprime, then `a(n) = φ(2 * n + 1)`. -/
theorem main :
    ∀ n : ℕ, IsAbsEulerPseudoprime n → a n = Nat.totient (2 * n + 1) := by
  sorry

end OMA.S_oeis_a307864
