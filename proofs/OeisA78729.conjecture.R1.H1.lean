import OMAReductions.R_OeisA78729_conjecture_R1

-- Step OeisA78729.conjecture.R1.H1: hypothesis H1 of reduction OeisA78729.conjecture.R1
-- Credit: @volskew90
-- H1 := ∀ n : ℕ, n = 4 → OeisA78729.a n = 0

theorem OMA.solution : OMA.R_OeisA78729_conjecture_R1.H1 := by
  intro n hn
  subst hn
  classical
  have hnsq : ¬∃ k, 0 < k ∧ ((∏ i ∈ Finset.range 4, (k + i + 1)) + 1).Prime := by
    rintro ⟨k, hk, hprime⟩
    have hexp : ∏ i ∈ Finset.range 4, (k + i + 1) = (k + 1) * (k + 2) * (k + 3) * (k + 4) := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, Finset.prod_range_succ,
        show (3 : ℕ) = 2 + 1 from rfl, Finset.prod_range_succ,
        show (2 : ℕ) = 1 + 1 from rfl, Finset.prod_range_succ,
        show (1 : ℕ) = 0 + 1 from rfl, Finset.prod_range_succ, Finset.prod_range_zero]
      ring
    have hsq : (∏ i ∈ Finset.range 4, (k + i + 1)) + 1 = (k ^ 2 + 5 * k + 5) ^ 2 := by
      rw [hexp]
      ring
    rw [hsq] at hprime
    have hm : 2 ≤ k ^ 2 + 5 * k + 5 := by nlinarith
    rcases hprime.eq_one_or_self_of_dvd _ (dvd_pow_self _ two_ne_zero) with h1 | h2eq
    · omega
    · nlinarith
  rw [OeisA78729.a, dif_neg hnsq]
