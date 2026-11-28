import OMAStatements.S_oeis_a337758

-- Reduction oeis-a337758.R1 of oeis-a337758: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a337758_R1

open OMA.S_oeis_a337758
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ A : PowerSeries ℤ, IsGeneratingSeries A → ∀ n : ℕ, 0 < n → (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ A : PowerSeries ℤ, IsGeneratingSeries A → ∀ n : ℕ, 0 < n → (coeff n A ≡ 2 [ZMOD 4] ↔
      ∃ i j : ℕ, i < j ∧ n = 2 * (2 ^ i + 2 ^ j))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a337758.main := by
  intro h1 h2 x1 x2 x3 x4
  exact ⟨h1 x1 x2 x3 x4, h2 x1 x2 x3 x4⟩

end OMA.R_oeis_a337758_R1
