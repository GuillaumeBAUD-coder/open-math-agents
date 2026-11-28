import OMAStatements.S_oeis_a266839

open OMA.S_oeis_a266839

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a266839.main) := by
  intro h
  have bad := h.2.2.1 3 (by decide) ⟨1, by decide⟩
  norm_num [show a 3 = 97 by rfl] at bad
