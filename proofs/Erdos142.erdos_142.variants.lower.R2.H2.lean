import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

/-! Recasts the block-separation argument from PR #5265 as linear arithmetic on the block scales. -/

lemma block_power_cases (i j : ℕ) : 4 ^ i = 4 ^ j ∨ 4 * 4 ^ i ≤ 4 ^ j ∨ 4 * 4 ^ j ≤ 4 ^ i := by
  have gap {m n : ℕ} (h : m < n) : 4 * 4 ^ m ≤ 4 ^ n := by
    calc
      _ = 4 ^ (m + 1) := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) h
  rcases lt_trichotomy i j with h | rfl | h
  · exact Or.inr (Or.inl (gap h))
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (gap h))

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  intro k hk B hB hfree ⟨a, d, hd, terms⟩
  choose! index point belongs place using terms
  have bounds (i : ℕ) (hi : i < k) :
      4 * 4 ^ index i < a + i * d ∧ a + i * d ≤ 5 * 4 ^ index i := by
    have := Finset.mem_Icc.mp (hB _ (belongs i hi))
    have := place i hi
    omega
  have first := bounds 0 (by omega)
  have second := bounds 1 (by omega)
  have small : d < 4 ^ index 0 := by
    have := bounds 2 (by omega)
    have := block_power_cases (index 0) (index 1)
    have := block_power_cases (index 1) (index 2)
    omega
  have all : ∀ i < k, 4 ^ index i = 4 ^ index 0 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      have here := bounds i (by omega)
      have there := bounds (i + 1) hi
      have := ih (by omega)
      have := block_power_cases (index (i + 1)) (index 0)
      rw [add_mul, one_mul] at there
      omega
  refine hfree (index 0) ⟨a - 4 * 4 ^ index 0, d, hd, fun i hi => ?_⟩
  have same := all i hi
  have atPoint := place i hi
  have pointEq : a - 4 * 4 ^ index 0 + i * d = point i := by omega
  rw [pointEq, ← Nat.pow_right_injective (by decide : 2 ≤ 4) same]
  exact belongs i hi
