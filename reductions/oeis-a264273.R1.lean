import OMAStatements.S_oeis_a264273

-- Reduction oeis-a264273.R1 of oeis-a264273: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a264273_R1

open OMA.S_oeis_a264273
open PowerSeries in

/-- Step H1 of the reduction. -/
def H1 : Prop := (PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
      (1 - 5 * X) = X * (9 + 3 * X + 16 * X ^ 2))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 2 < n → a n = 256 * 5 ^ (n - 3))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a264273.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a264273_R1
