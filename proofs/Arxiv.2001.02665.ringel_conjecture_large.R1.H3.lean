import OMAReductions.R_Arxiv_2001_02665_ringel_conjecture_large_R1

-- Step Arxiv.2001.02665.ringel_conjecture_large.R1.H3: hypothesis H3 of reduction Arxiv.2001.02665.ringel_conjecture_large.R1
-- Credit: @pyaf
-- H3 := ∀ n : ℕ, (2 * n + 1) * n = Nat.choose (2 * n + 1) 2

theorem OMA.solution : OMA.R_Arxiv_2001_02665_ringel_conjecture_large_R1.H3 := by
  intro n
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  calc
    (2 * n + 1) * n = ((2 * n + 1) * n * 2) / 2 := by simp
    _ = (2 * n + 1) * (2 * n) / 2 := by ring_nf

