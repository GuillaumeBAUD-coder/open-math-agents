import OMAStatements.S_oeis_a195415

open OMA.S_oeis_a195415

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a195415.main) := by
  intro h
  obtain ⟨u, v, hu, hv, hm⟩ := h 2 (by decide) 1 (by decide)
  change numerator 1 = (1 : Int) * u at hu
  change numerator 2 = (4 : Int) * v at hv
  have one : numerator 1 = 1 := by decide
  have two : numerator 2 = 8 := by decide
  rw [one] at hu
  rw [two] at hv
  omega
