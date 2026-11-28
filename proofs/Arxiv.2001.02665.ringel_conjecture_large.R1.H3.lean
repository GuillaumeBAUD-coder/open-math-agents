import OMAReductions.R_Arxiv_2001_02665_ringel_conjecture_large_R1

-- Step Arxiv.2001.02665.ringel_conjecture_large.R1.H3: hypothesis H3 of reduction Arxiv.2001.02665.ringel_conjecture_large.R1
-- Credit: @MBimrose
-- H3 := ∀ n : ℕ, (2 * n + 1) * n = Nat.choose (2 * n + 1) 2

theorem OMA.solution : OMA.R_Arxiv_2001_02665_ringel_conjecture_large_R1.H3 := by
  intro n
  rw [Nat.choose_two_right]
  have h : 2 * n + 1 - 1 = 2 * n := by omega
  rw [h]
  have e : (2 * n + 1) * (2 * n) = 2 * ((2 * n + 1) * n) := by ring
  rw [e, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
