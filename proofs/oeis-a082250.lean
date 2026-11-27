import OMAStatements.S_oeis_a082250

/-! Two consecutive one-digit blocks refute the divisibility conjecture. -/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a082250.main) := by
  intro claim
  have blocks := claim 3 2 1 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  exact (by decide : ¬ 3 ∣ 34) (blocks.1 (by decide))
