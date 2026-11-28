import OMAStatements.S_oeis_a019334

-- Reduction oeis-a019334.R1 of oeis-a019334: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a019334_R1

open OMA.S_oeis_a019334

/-- Step H1 of the reduction. -/
def H1 : Prop := Filter.Tendsto
      (fun N : ℕ => (Q N : ℝ) / (artinConstant * (N : ℝ) / Real.log (N : ℝ)))
      Filter.atTop (nhds 1)

/-- Step H2 of the reduction. -/
def H2 : Prop := Filter.Tendsto
      (fun N : ℕ => (Qb N 5 : ℝ) / ((3 / 5 : ℝ) * (Q N : ℝ)))
      Filter.atTop (nhds 1)

/-- Step H3 of the reduction. -/
def H3 : Prop := Filter.Tendsto
      (fun N : ℕ => (Qb N 7 : ℝ) / ((2 / 5 : ℝ) * (Q N : ℝ)))
      Filter.atTop (nhds 1)

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a019334.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a019334_R1
