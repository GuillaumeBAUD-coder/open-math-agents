import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

/-- The larger of two distinct block scales is at least four times the smaller. -/
private lemma scaleJump {j l : ℕ} (h : j < l) : 4 * 4 ^ j ≤ 4 ^ l := by
  simpa [pow_succ, mul_comm] using Nat.pow_le_pow_right (by decide : 0 < (4 : ℕ)) h

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  intro k hk B hB hfree ⟨a, d, hd, h⟩
  have bounds {j b : ℕ} (hb : b ∈ B j) : 1 ≤ b ∧ b ≤ 4 ^ j :=
    Finset.mem_Icc.mp (hB j hb)
  obtain ⟨j, b, hb, e⟩ := h 0 (by omega)
  obtain ⟨j₁, b₁, hb₁, e₁⟩ := h 1 (by omega)
  obtain ⟨j₂, b₂, hb₂, e₂⟩ := h 2 (by omega)
  have b0 := bounds hb
  have b1 := bounds hb₁
  have b2 := bounds hb₂
  simp only [zero_mul, add_zero, one_mul, two_mul] at e e₁ e₂
  -- A positive-step triple cannot cross to a different block at its second term.
  have same : j₁ = j := by
    rcases lt_trichotomy j₁ j with hlt | rfl | hgt
    · have := scaleJump hlt
      omega
    · rfl
    · have := scaleJump hgt
      rcases lt_trichotomy j₁ j₂ with hlt | rfl | hgt
      · have := scaleJump hlt
        omega
      · omega
      · have := scaleJump hgt
        omega
  subst j₁
  have close : d < 4 ^ j := by omega
  -- The whole progression stays in the first block, with explicit witnesses from that block.
  have stay : ∀ i < k, ∃ t ∈ B j, a + i * d = 4 * 4 ^ j + t := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨b, hb, by simpa using e⟩
    | succ i ih =>
      intro hi
      obtain ⟨t, ht, et⟩ := ih (by omega)
      obtain ⟨l, u, hu, eu⟩ := h (i + 1) hi
      have bt := bounds ht
      have bu := bounds hu
      rw [add_mul, one_mul] at eu
      rcases lt_trichotomy l j with hlt | rfl | hgt
      · have := scaleJump hlt
        omega
      · exact ⟨u, hu, by simpa [add_mul, add_assoc] using eu⟩
      · have := scaleJump hgt
        omega
  refine hfree j ⟨a - 4 * 4 ^ j, d, hd, fun i hi => ?_⟩
  obtain ⟨t, ht, et⟩ := stay i hi
  rwa [show a - 4 * 4 ^ j + i * d = t by omega]
