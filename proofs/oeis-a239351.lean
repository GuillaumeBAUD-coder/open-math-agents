import OMAStatements.S_oeis_a239351
import Mathlib.Tactic

namespace OMA.P_oeis_a239351

open OMA.S_oeis_a239351

private theorem prove_refutation : ¬ (type_of% @OMA.S_oeis_a239351.main) := by
  intro h
  have hsol : IsA239351Solution (-472715493453327032) (-569936821113563493509) 569936821221962380720 := by
    refine ⟨?_, ?_, ?_⟩ <;> norm_num
  have hcase := h (-472715493453327032) (-569936821113563493509) 569936821221962380720 hsol
  omega

end OMA.P_oeis_a239351

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a239351.main) :=
  OMA.P_oeis_a239351.prove_refutation
