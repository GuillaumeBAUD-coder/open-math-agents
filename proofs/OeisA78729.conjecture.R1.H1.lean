import OMAReductions.R_OeisA78729_conjecture_R1

-- Step OeisA78729.conjecture.R1.H1: hypothesis H1 of reduction OeisA78729.conjecture.R1
-- Credit: @NoahPuckett-IO
-- (k+1)(k+2)(k+3)(k+4) + 1 = (k^2 + 5k + 5)^2 is a square above 1, so never prime: a 4 = 0.

theorem OMA.solution : OMA.R_OeisA78729_conjecture_R1.H1 := by
  intro n hn
  subst hn
  unfold OeisA78729.a
  rw [dif_neg]
  rintro ⟨k, _, hp⟩
  have h : ∏ i ∈ Finset.range 4, (k + i + 1) + 1 = (k ^ 2 + 5 * k + 5) * (k ^ 2 + 5 * k + 5) := by
    simp [Finset.prod_range_succ]
    ring
  rw [h] at hp
  exact Nat.not_prime_mul (by omega) (by omega) hp
