import OMAReductions.R_Erdos687_erdos_687_parts_iii_R2_H1_R1
import Mathlib

theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R2_H1_R1.H2 := by
  intro w K h
  exact le_csSup ⟨primorial w, fun y hy => (Erdos687.lt_primorial_of_isCoveredByResidues hy).le⟩ h
