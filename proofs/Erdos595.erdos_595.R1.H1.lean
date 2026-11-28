import OMAReductions.R_Erdos595_erdos_595_R1

/-!
# Proof of `Erdos595.erdos_595.R1.H1`

Directly applies `OMA.R_Erdos595_erdos_595_R1.bounded_step`, which proves that every graph of
continuum-bounded edge codegree admits a countable cover by triangle-free graphs.
-/

theorem OMA.solution : OMA.R_Erdos595_erdos_595_R1.H1 :=
  OMA.R_Erdos595_erdos_595_R1.bounded_step
