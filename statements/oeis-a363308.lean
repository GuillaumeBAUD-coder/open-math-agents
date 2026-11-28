import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a363308

/-- Formal power series composition `(F ∘ G)(x) = ∑_{k≥0} [x^k] F * G(x)^k`
(exact whenever `[x^0] G = 0`). -/
noncomputable def psComp (F G : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

/-- `IsCatalan C` asserts that `C(x) = ∑_{n≥0} C_n x^n` is the Catalan generating function,
uniquely determined by `C(x) = 1 + x * C(x)^2`. -/
def IsCatalan (C : PowerSeries ℤ) : Prop :=
  C = 1 + PowerSeries.X * C ^ 2

/-- `IsA363308 A` asserts that `A(x) = C(x * C(x)^3)` where `C` is the Catalan g.f. -/
def IsA363308 (A : PowerSeries ℤ) : Prop :=
  ∃ C : PowerSeries ℤ, IsCatalan C ∧ A = psComp C (PowerSeries.X * C ^ 3)

/-- Conjecture on OEIS A363308:
for all `n : ℕ`, `a(n)` is odd iff `n = 0` or `n` is a power of `2`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA363308 A →
      ∀ n : ℕ, PowerSeries.coeff n A % 2 = 1 ↔ (n = 0 ∨ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a363308
