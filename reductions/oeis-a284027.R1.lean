import OMAStatements.S_oeis_a284027

-- Reduction oeis-a284027.R1 of oeis-a284027: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a284027_R1

open OMA.S_oeis_a284027
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 33 ≤ n → (a n : ℚ) = 2 * a (n - 1) - 4 * a (n - 2) + 8 * a (n - 3) + a (n - 8) - 2 * a (n - 9) + 4 * a (n - 10) - 8 * a (n - 11))

/-- Step H2 of the reduction. -/
def H2 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) * (X + 1) * (2 * X - 1) * (X ^ 2 + 1) * (4 * X ^ 2 + 1) * (X ^ 4 + 1) : PowerSeries ℚ) = 1048576 * X ^ 32 + 1310720 * X ^ 30 + 262144 * X ^ 28 + 327680 * X ^ 27 - 65536 * X ^ 26 - 49152 * X ^ 25 - 1118208 * X ^ 24 - 20480 * X ^ 23 - 1324032 * X ^ 22 - 5120 * X ^ 21 - 259072 * X ^ 20 - 327680 * X ^ 19 + 65280 * X ^ 18 + 48384 * X ^ 17 + 3840 * X ^ 16 + 19456 * X ^ 15 - 3328 * X ^ 14 - 256 * X ^ 13 - 256 * X ^ 12 - 976 * X ^ 11 - 64 * X ^ 10 - 252 * X ^ 9 + 64 * X ^ 8 + 49 * X ^ 7 + 5 * X ^ 6 + 5 * X ^ 5 + X ^ 4 + X ^ 3 + 5 * X ^ 2 + X + 1)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a284027.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a284027_R1
