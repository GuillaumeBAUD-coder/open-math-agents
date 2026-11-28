import OMAStatements.S_oeis_a280606

/-- At stage six, the two sides of the proposed recurrence differ by 100. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a280606.main) := by
  intro h
  have failure : ¬ ((OMA.S_oeis_a280606.a 6 : ℤ) =
      OMA.S_oeis_a280606.a 5 + 100 * OMA.S_oeis_a280606.a 4 - 100 * OMA.S_oeis_a280606.a 3) := by
    decide +kernel
  exact failure (h.2 6 (by decide))
