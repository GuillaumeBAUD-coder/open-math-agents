import OMAStatements.S_oeis_a019335

-- Reduction oeis-a019335.R1 of oeis-a019335: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a019335_R1

open OMA.S_oeis_a019335

/-- Step H1 of the reduction. -/
def H1 : Prop := Filter.Tendsto
        (fun N : ℕ => (qMod5 N 2 : ℝ) / ((20 / 19 : ℝ) * artinConst * (piMod5 N 2 : ℝ)))
        Filter.atTop (nhds 1)

/-- Step H2 of the reduction. -/
def H2 : Prop := Filter.Tendsto
        (fun N : ℕ => (qMod5 N 3 : ℝ) / ((20 / 19 : ℝ) * artinConst * (piMod5 N 3 : ℝ)))
        Filter.atTop (nhds 1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a019335.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a019335_R1
