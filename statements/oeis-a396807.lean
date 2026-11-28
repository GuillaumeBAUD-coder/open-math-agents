import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a396807

/-- Formal power series composition `(F ∘ G)(x) = ∑_{k≥0} [x^k] F * G(x)^k`
(exact whenever `[x^0] G = 0`). -/
noncomputable def psComp (F G : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

/-- `k`-th compositional iterate `A^{[k]}(x)` of a formal power series `A` with `[x^0] A = 0`. -/
noncomputable def psIter (A : PowerSeries ℤ) : ℕ → PowerSeries ℤ
  | 0 => PowerSeries.X
  | k + 1 => psComp A (psIter A k)

/-- `IsA396807 A` asserts that `A(x) = ∑_{n≥1} a(n) x^n` is the generating function of
OEIS A396807, uniquely determined by `[x^0] A = 0` and `A(x) = x + A^{[5]}(x) * A^{[6]}(x)`. -/
def IsA396807 (A : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 A = 0 ∧ A = PowerSeries.X + psIter A 5 * psIter A 6

/-- Conjectures on OEIS A396807:
1. `a(n) ≡ 1 (mod 10)` for all `n ≥ 1`.
2. `[x^n] A^{[k]}(x) ≡ k^(n - 1) (mod 10)` for all `n ≥ 1` and all `k : ℕ`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA396807 A →
      (∀ n : ℕ, 1 ≤ n → PowerSeries.coeff n A ≡ 1 [ZMOD 10]) ∧
      (∀ k n : ℕ, 1 ≤ n → PowerSeries.coeff n (psIter A k) ≡ (k : ℤ) ^ (n - 1) [ZMOD 10]) := by
  sorry

end OMA.S_oeis_a396807
