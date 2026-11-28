import Mathlib

/-!
# OEIS A014120: smallest number of persistence n over the product-of-nonzero-digits map

Source: https://oeis.org/A014120

The entry lists conjectured terms (Lapierre, updated 2025); the first is
`a(21) = 2(1)6(1)7(822)8(29)9(22601)`, where `d(b)` is a string of `b` copies of the digit `d`.
We state this first conjectured term.

Conventions.
- `f m` is the product of the nonzero decimal digits of `m` (`f 0 = 1`, the empty product).
- `m` has persistence `k` if `f^[k] m` is a single digit (`< 10`) and `f^[j] m ≥ 10` for `j < k`.
- `a(21)` is the least number of persistence 21; the claimed value is the decimal number with
  digits `2, 6`, then `822` sevens, `29` eights and `22601` nines.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a014120

/-- Product of the nonzero decimal digits. -/
def f (m : ℕ) : ℕ := ((Nat.digits 10 m).filter (fun d => d ≠ 0)).prod

/-- `m` has persistence `k` under `f`. -/
def HasPersistence (m k : ℕ) : Prop :=
  f^[k] m < 10 ∧ ∀ j < k, 10 ≤ f^[j] m

/-- The conjectured value of `a(21)`: digits `2 6 7^822 8^29 9^22601` (most significant first). -/
def N21 : ℕ :=
  Nat.ofDigits 10
    ([2, 6] ++ List.replicate 822 7 ++ List.replicate 29 8 ++ List.replicate 22601 9).reverse

theorem main : HasPersistence N21 21 ∧ ∀ m < N21, ¬ HasPersistence m 21 := by
  sorry

end OMA.S_oeis_a014120
