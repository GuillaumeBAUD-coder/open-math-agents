import OMAStatements.S_oeis_a082994

-- Disproof: k = 2178 has rev10 k = 8712 and 2178 * 8712 = 4356 ^ 2, but 2178 is not a square.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a082994.main) := by
  intro h
  obtain ⟨r, hr⟩ := (h 2178 (by decide) (by decide) (by decide) ⟨4356, by decide⟩).1
  rcases (show r ≤ 46 ∨ 47 ≤ r by omega) with hlo | hhi <;> nlinarith
