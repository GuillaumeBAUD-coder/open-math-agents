import OMAStatements.S_mo_334112

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_334112.main) := fun h => by
  obtain ⟨c, hc, h⟩ := h 1 one_pos 1 one_pos le_rfl
  unfold S_mo_334112.expect at h
  obtain ⟨M, hM⟩ := exists_lt_nsmul hc 1
  have := h {0, M + 2} (fun _ => 1 / 2) (by simp) (by simp) (by simp; positivity) (by norm_num)
  simp [min_def] at *
  linarith
