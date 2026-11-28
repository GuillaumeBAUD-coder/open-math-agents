import OMAStatements.S_oeis_a285666

open OMA.S_oeis_a285666

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a285666.main) := by
  intro h
  have h2 := h 2 (by decide)
  exact (by decide : ¬ ((word 2).length = 2^2 + 2^2)) h2
