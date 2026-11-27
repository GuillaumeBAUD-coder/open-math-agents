import OMAReductions.R_OeisA78729_conjecture_R1

-- Step OeisA78729.conjecture.R1.H1
-- Credit: @caa1982

theorem OMA.solution : OMA.R_OeisA78729_conjecture_R1.H1 := by
  rintro n rfl
  unfold OeisA78729.a
  rw [dif_neg]
  rintro ⟨k, hk, hprime⟩
  have hprod : ∏ i ∈ Finset.range 4, (k + i + 1) + 1 =
      (k ^ 2 + 5 * k + 5) * (k ^ 2 + 5 * k + 5) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    ring
  rw [hprod] at hprime
  exact Nat.not_prime_mul (by nlinarith) (by nlinarith) hprime
