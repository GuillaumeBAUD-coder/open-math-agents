import OMAReductions.R_Arxiv_2001_02665_ringel_conjecture_large_R1

theorem OMA.solution : OMA.R_Arxiv_2001_02665_ringel_conjecture_large_R1.H3 := by
  intro n
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  rw [Nat.mul_comm 2 n, ← Nat.mul_assoc, Nat.mul_div_cancel]
  decide
