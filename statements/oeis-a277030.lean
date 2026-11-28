import Mathlib.GroupTheory.Exponent
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Lattice.Nat

namespace OMA.S_oeis_a277030

/-- `a(n)` (OEIS A277030): the smallest `m : ℕ` such that `b ^ φ(n) ≡ b ^ m [ZMOD n]`
for every integer `b`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ b : ℤ, (b : ZMod n) ^ Nat.totient n = (b : ZMod n) ^ m}

/-- Carmichael's lambda function `λ(n)` (OEIS A002322): the exponent of the multiplicative
group `(ZMod n)ˣ` for `n ≥ 1`. -/
noncomputable def carmichael (n : ℕ) : ℕ :=
  Monoid.exponent (ZMod n)ˣ

/-- Conjecture (OEIS A277030): for all `n ≥ 1`, `a(n) = λ(n)` except for `a(1) = 0` and
`a(8) = a(24) = 4`; in particular, `a(n) > λ(n)` holds if and only if `n = 8` or `n = 24`. -/
theorem main :
    a 1 = 0 ∧ a 8 = 4 ∧ a 24 = 4 ∧
    (∀ n : ℕ, 2 ≤ n → n ≠ 8 → n ≠ 24 → a n = carmichael n) ∧
    (∀ n : ℕ, 1 ≤ n → (carmichael n < a n ↔ n = 8 ∨ n = 24)) := by
  sorry

end OMA.S_oeis_a277030
