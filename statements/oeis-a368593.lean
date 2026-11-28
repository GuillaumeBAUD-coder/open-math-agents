import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a368593

/-- Substitution `x ↦ -x` on formal power series `A(x) ∈ ℤ[[x]]`. -/
noncomputable def negArg (A : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (-1 : ℤ) ^ n * PowerSeries.coeff n A

/-- Defining functional equation of OEIS A368593:
`A(x) = 1 + x * (A(x)^2 - A(-x)^2) / 2 + x * sqrt((A(x)^4 + A(-x)^4) / 2)`,
expressed integrally via `S(x) = sqrt((A(x)^4 + A(-x)^4) / 2)` with `S(0) = 1`. -/
def IsA368593 (A : PowerSeries ℤ) : Prop :=
  ∃ S : PowerSeries ℤ,
    PowerSeries.coeff 0 S = 1 ∧
    2 * S ^ 2 = A ^ 4 + negArg A ^ 4 ∧
    2 * A = 2 + PowerSeries.X * (A ^ 2 - negArg A ^ 2) + 2 * PowerSeries.X * S

/-- Conjecture on OEIS A368593: `a(n)` is odd if and only if `n = 2^k - 1` for some `k ≥ 0`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA368593 A →
      ∀ n : ℕ, PowerSeries.coeff n A % 2 = 1 ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  sorry

end OMA.S_oeis_a368593
