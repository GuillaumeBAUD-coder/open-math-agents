import OMAStatements.S_oeis_a250896

-- Reduction oeis-a250896.R1 of oeis-a250896: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a250896_R1

open OMA.S_oeis_a250896

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 9 < n → (a n : ℤ) = 12 * a (n - 1) - 60 * a (n - 2) + 162 * a (n - 3) - 255 * a (n - 4) + 234 * a (n - 5) - 116 * a (n - 6) + 24 * a (n - 7))

/-- Step H2 of the reduction. -/
def H2 : Prop := (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 2 < n → (a n : ℚ) = (-8787 + 3389 * 2 ^ n + 169 * 3 ^ (3 + n) + (14186 - 99 * 2 ^ (4 + n)) * (n : ℚ) + 36 * (145 + 33 * 2 ^ (1 + n)) * (n : ℚ) ^ 2) / 4)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a250896.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a250896_R1
