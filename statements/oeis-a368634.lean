import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a368634

/-- Sign-negated formal power series `A(-x)` for `A(x) = ∑ a(n) x^n`. -/
noncomputable def negArg (A : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (-1 : ℤ) ^ n * PowerSeries.coeff n A

/-- `IsA368634 A` asserts that `A(x) = ∑_{n≥0} a(n) x^n` is the generating function of
OEIS A368634, uniquely determined by `2 * A(x) = 2 + x * (3 * A(x)^2 - A(-x)^2)`. -/
def IsA368634 (A : PowerSeries ℤ) : Prop :=
  2 * A = 2 + PowerSeries.X * (3 * A ^ 2 - negArg A ^ 2)

/-- Conjecture on OEIS A368634:
`a(n)` is odd iff `n = 2^k - 1` for some `k : ℕ`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA368634 A →
      ∀ n : ℕ, PowerSeries.coeff n A % 2 = 1 ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  sorry

end OMA.S_oeis_a368634
