import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a381364

/-- Positive bilateral summand for `n ≥ 1`:
`(x * A)^n * (A^n + 2*x)^(n - 1) * (x^n + 2*A)^(n - 1)`. -/
noncomputable def termPos (A : PowerSeries ℤ) (n : ℕ) : PowerSeries ℤ :=
  (PowerSeries.X * A) ^ n * (A ^ n + 2 * PowerSeries.X) ^ (1 * n - 1) *
    (PowerSeries.X ^ n + 2 * A) ^ (1 * n - 1)

/-- Negative bilateral summand `-n` (`n ≥ 1`):
`(x * A)^(n^2) / ((1 + 2*x*A^n)^(n + 1) * (1 + 2*x^n*A)^(n + 1))`. -/
noncomputable def termNeg (A : PowerSeries ℤ) (n : ℕ) : PowerSeries ℤ :=
  (PowerSeries.X * A) ^ (1 * n * n) *
    Ring.inverse
      ((1 + 2 * PowerSeries.X * A ^ n) ^ (1 * n + 1) *
        (1 + 2 * PowerSeries.X ^ n * A) ^ (1 * n + 1))

/-- Sum of all nonzero bilateral terms ∑_{n ≥ 1} (termPos A n + termNeg A n). -/
noncomputable def bilateralSum (A : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun k =>
    ∑ n ∈ Finset.Icc 1 k, PowerSeries.coeff k (termPos A n + termNeg A n)

/-- IsSeq A asserts that A(x) = ∑_{n ≥ 0} a(n) x^n satisfies the defining
bilateral power series equation of OEIS A381364 (cleared of (1 + 2x)(1 + 2A)):
A(0) = 1 and (1 + 2x)(1 + 2A) = 3 + 3 * (1 + 2x)(1 + 2A) * ∑_{n ≠ 0} T_n. -/
def IsSeq (A : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 A = 1 ∧
    (1 + 2 * PowerSeries.X) * (1 + 2 * A) =
      3 + 3 * (1 + 2 * PowerSeries.X) * (1 + 2 * A) * bilateralSum A

/-- OEIS A381364 conjecture: for all `n > 0`, `a(n) ≡ 6 (mod 9)`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsSeq A →
      ∀ n : ℕ, 1 ≤ n → PowerSeries.coeff n A ≡ 6 [ZMOD 9] := by
  sorry

end OMA.S_oeis_a381364
