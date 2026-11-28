import OMAReductions.R_RingelConjecture_ringel_conjecture_R1

-- Step RingelConjecture.ringel_conjecture.R1.H2: hypothesis H2 of reduction RingelConjecture.ringel_conjecture.R1
-- Credit: @Ezekia1
-- H2 := ∀ n : ℕ, (2 * n + 1) * n = Nat.choose (2 * n + 1) 2
-- Proof: choose (2n+1) 2 = (2n+1) * (2n) / 2 = (2n+1) * n.

theorem OMA.solution : OMA.R_RingelConjecture_ringel_conjecture_R1.H2 := by
  intro n
  rw [Nat.choose_two_right, show 2 * n + 1 - 1 = 2 * n by omega,
    show (2 * n + 1) * (2 * n) = 2 * ((2 * n + 1) * n) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
