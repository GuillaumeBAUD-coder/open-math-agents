import Mathlib.Data.Finset.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a372527

/-- Formal power series composition `f(g(X))` for `g(0) = 0`, defined coefficientwise by
`[X^n] f(g(X)) = ∑_{k=0}^n ([X^k] f) * ([X^n] g^k)`. -/
noncomputable def compPS {R : Type*} [CommRing R] (f g : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k f * PowerSeries.coeff n (g ^ k)

open Classical in
/-- Conjecture (Paul D. Hanna; OEIS A372527): For the integer power series `A(X) ∈ ℤ⟦X⟧`
with `A(0) = 0`, `[X^1] A(X) = 1`, and `A(A(X)^2) * (1 - 2 * A(X)) = X * A(X)`,
for every `n ≥ 2`, `a(n) ≡ 2 (mod 4)` if `n = 2^k + 1` for some `k ≥ 0`, and
`a(n) ≡ 0 (mod 4)` otherwise. -/
theorem main :
    ∀ A : PowerSeries ℤ,
      PowerSeries.constantCoeff A = 0 →
      PowerSeries.coeff 1 A = 1 →
      compPS A (A ^ 2) * (1 - 2 * A) = PowerSeries.X * A →
      ∀ n : ℕ, 2 ≤ n →
        ((PowerSeries.coeff n A : ℤ) : ZMod 4) =
          if ∃ k : ℕ, n = 2 ^ k + 1 then 2 else 0 := by
  sorry

end OMA.S_oeis_a372527
