import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

-- Shorter proof: the second and third terms force a common block, then induction
-- keeps all terms in it. This simplifies the original block-separation argument.
-- Choice of block indices follows the approach in PR 3636 by @ishaanzee.

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  intro k hk B hB hfree ⟨a, d, hd, h⟩
  choose! J b hb heq using h
  have gap (i j : ℕ) : i = j ∨ 4 * 4 ^ i ≤ 4 ^ j ∨ 4 * 4 ^ j ≤ 4 ^ i := by
    have step {m n : ℕ} (hm : m < n) : 4 * 4 ^ m ≤ 4 ^ n := by
      simpa only [pow_succ'] using ((show (4 : ℕ) ^ (m + 1) ≤ 4 ^ n from Nat.pow_le_pow_right (by decide) hm))
    rcases lt_trichotomy i j with h | h | h
    · exact Or.inr (Or.inl (step h))
    · exact Or.inl h
    · exact Or.inr (Or.inr (step h))
  have bound (i : ℕ) (hi : i < k) : 4 * 4 ^ J i < a + i * d ∧ a + i * d ≤ 5 * 4 ^ J i := by
    have := Finset.mem_Icc.mp (hB _ (hb i hi))
    have := heq i hi
    omega
  have h0 := bound 0 (by omega)
  have h1 := bound 1 (by omega)
  have h2 := bound 2 (by omega)
  simp only [zero_mul, add_zero, one_mul] at h0 h1
  have j12 : J 1 = J 2 := by
    rcases gap (J 1) (J 2) with hj | hj | hj <;> omega
  rw [← j12] at h2
  have hdP : d < 4 ^ J 1 := by omega
  have j01 : J 0 = J 1 := by
    rcases gap (J 0) (J 1) with hj | hj | hj <;> omega
  have all : ∀ i < k, J i = J 1 := by
    intro i
    induction i with
    | zero => intro _; exact j01
    | succ i ih =>
      intro hi
      have hp := bound i (by omega)
      rw [ih (by omega)] at hp
      have hn := bound (i + 1) hi
      rw [add_mul, one_mul] at hn
      rcases gap (J (i + 1)) (J 1) with hj | hj | hj <;> omega
  apply hfree (J 1)
  refine ⟨b 0, d, hd, fun i hi => ?_⟩
  have hm := hb i hi
  have hE := heq i hi
  have hE0 := heq 0 (by omega)
  simp only [zero_mul, add_zero] at hE0
  rw [all i hi] at hm hE
  rw [j01] at hE0
  rwa [show b 0 + i * d = b i by omega]
