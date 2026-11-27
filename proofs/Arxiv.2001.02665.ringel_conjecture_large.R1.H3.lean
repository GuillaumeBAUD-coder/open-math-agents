import OMAReductions.R_Arxiv_2001_02665_ringel_conjecture_large_R1

-- Step Arxiv.2001.02665.ringel_conjecture_large.R1.H3: hypothesis H3 of reduction Arxiv.2001.02665.ringel_conjecture_large.R1

/-!
`choose (2n + 1) 2 = (2n + 1) * (2n) / 2 = (2n + 1) * n`.
-/

theorem OMA.solution : OMA.R_Arxiv_2001_02665_ringel_conjecture_large_R1.H3 := by
  unfold OMA.R_Arxiv_2001_02665_ringel_conjecture_large_R1.H3
  intro n
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  have e : (2 * n + 1) * (2 * n) = 2 * ((2 * n + 1) * n) := by ring
  rw [e, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
