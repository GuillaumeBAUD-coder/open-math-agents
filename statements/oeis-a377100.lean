import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a377100

/-- Power series substitution `A(x^m)` for `m ≥ 1`. -/
noncomputable def psSubPow (A : PowerSeries ℤ) (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if m ∣ n then PowerSeries.coeff (n / m) A else 0

/-- `IsA377100 A` asserts that `A(x) = ∑_{n≥1} a(n) x^n` is the generating function of
OEIS A377100, satisfying `[x^0] A = 0`, `[x^1] A = 1`, and
`A(x) = A(x^3) / A(x^2) + A(x)^2` (cleared of `A(x^2)`:
`A(x) * A(x^2) = A(x^3) + A(x)^2 * A(x^2)`). -/
def IsA377100 (A : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 A = 0 ∧
  PowerSeries.coeff 1 A = 1 ∧
  A * psSubPow A 2 = psSubPow A 3 + A ^ 2 * psSubPow A 2

/-- Conjecture on OEIS A377100: `a(n) ≡ 1 (mod 3)` for all `n ≥ 1`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA377100 A →
      ∀ n : ℕ, 1 ≤ n → PowerSeries.coeff n A ≡ 1 [ZMOD 3] := by
  sorry

end OMA.S_oeis_a377100
