import OMAReductions.R_Mills_exists_least_R2

-- Step Mills.exists_least.R2.H2: hypothesis H2 of reduction Mills.exists_least.R2
-- Credit: @luciusacarr
-- H2 is proved in the reduction file itself (`dyadicRich`, Chebyshev's lower bound).

theorem OMA.solution : OMA.R_Mills_exists_least_R2.H2 :=
  OMA.R_Mills_exists_least_R2.dyadicRich
