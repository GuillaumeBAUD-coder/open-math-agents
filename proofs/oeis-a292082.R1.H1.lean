import OMAReductions.R_oeis_a292082_R1

/-!
# Proof of `oeis-a292082.R1.H1`

Directly applies `OMA.R_oeis_a292082_R1.first_step`, which classifies prime solutions of
`p^2 - 1 = 2 * k^2` via powers of the fundamental Pell solution `3 + 2√2`.
-/

theorem OMA.solution : OMA.R_oeis_a292082_R1.H1 :=
  OMA.R_oeis_a292082_R1.first_step
