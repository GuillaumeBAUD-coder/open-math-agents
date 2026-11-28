import OMAReductions.R_Mills_exists_least_R2

-- Step Mills.exists_least.R2.H2: hypothesis H2 of reduction Mills.exists_least.R2
-- Credit: @ivillar. The reduction file itself proves H2 as `dyadicRich`; this step applies it.

/-! Hypothesis H2 of the Mills reduction. -/

open OMA.R_Mills_exists_least_R2 in
theorem OMA.solution : H2 :=
  dyadicRich
