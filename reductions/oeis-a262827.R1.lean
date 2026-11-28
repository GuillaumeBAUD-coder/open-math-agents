import OMAStatements.S_oeis_a262827

-- Reduction oeis-a262827.R1 of oeis-a262827: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a262827_R1

open OMA.S_oeis_a262827

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 0 < a n

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, (a n = 1 →
      n ∈ ({0, 14, 15, 21, 22, 23, 62, 71, 78, 87, 136, 216, 405, 437, 448, 477, 535, 583, 591,
      623, 671, 696, 885, 950, 1046, 1135, 1206, 1208, 1248, 1317, 2288, 2383, 2543, 3167,
      3717, 3974, 6847, 7918, 8328, 9096, 21935} : Finset ℕ))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a262827.main := by
  intro h1 h2 x1
  exact ⟨h1 x1, h2 x1⟩

end OMA.R_oeis_a262827_R1
