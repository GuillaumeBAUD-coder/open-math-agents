import OMAReductions.R_OeisA78729_conjecture_R1

theorem OMA.solution : OMA.R_OeisA78729_conjecture_R1.H1 := by
  classical
  intro n hn
  subst n
  have hnone : ¬ ∃ k : ℕ, 0 < k ∧ (∏ i ∈ Finset.range 4, (k + i + 1) + 1).Prime := by
    rintro ⟨k, _, hp⟩
    have heq : (∏ i ∈ Finset.range 4, (k + i + 1)) + 1 = (k ^ 2 + 5 * k + 5) ^ 2 := by
      simp only [Finset.prod_range_succ, Finset.prod_range_zero]
      ring
    rw [heq] at hp
    exact Nat.Prime.not_prime_pow (by decide : 2 ≤ 2) hp
  simp only [OeisA78729.a, dif_neg hnone]
