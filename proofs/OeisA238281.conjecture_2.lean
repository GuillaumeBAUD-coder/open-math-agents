import FormalConjectures.OEIS.«238281»

theorem OMA.disproof : ¬ (type_of% @OeisA238281.conjecture_2) := by
  intro h
  obtain ⟨k, hk0, hk14, hp, heq⟩ := h 14 (by norm_num) (by norm_num)
  interval_cases k <;> first
    | (exfalso; revert hp; decide +kernel)
    | (exfalso; revert heq; decide +kernel)
