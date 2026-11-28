import OMAStatements.S_oeis_a259269

-- Reduction oeis-a259269.R1 of oeis-a259269: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a259269_R1

open OMA.S_oeis_a259269

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ (A G : PowerSeries ℤ),
      PowerSeries.constantCoeff A = 0 →
      PowerSeries.derivative ℤ A = PowerSeries.C (2 : ℤ) * G →
      PowerSeries.subst (PowerSeries.X - PowerSeries.C (3 : ℤ) * A ^ 2 * G) G = PowerSeries.X →
      ∀ n : ℕ, 1 ≤ n → (PowerSeries.coeff (4 * n - 2) A % 3 = 1 ↔ ∃ k : ℕ, 2 * n - 1 = 3 ^ k)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ (A G : PowerSeries ℤ),
      PowerSeries.constantCoeff A = 0 →
      PowerSeries.derivative ℤ A = PowerSeries.C (2 : ℤ) * G →
      PowerSeries.subst (PowerSeries.X - PowerSeries.C (3 : ℤ) * A ^ 2 * G) G = PowerSeries.X →
      ∀ n : ℕ, 1 ≤ n → (¬ (∃ k : ℕ, 2 * n - 1 = 3 ^ k) → PowerSeries.coeff (4 * n - 2) A % 3 = 0)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a259269.main := by
  intro h1 h2 x1 x2 x3 x4 x5 x6 x7
  exact ⟨h1 x1 x2 x3 x4 x5 x6 x7, h2 x1 x2 x3 x4 x5 x6 x7⟩

end OMA.R_oeis_a259269_R1
