import OMAStatements.S_oeis_a307740

theorem OMA.solution : type_of% @OMA.S_oeis_a307740.main := by
  intro k hk
  exact ⟨hk.1, hk.2.trans (Nat.dvd_lcm_right _ _)⟩
