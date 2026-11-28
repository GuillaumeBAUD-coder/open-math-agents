import OMAReductions.R_mo_342377_R1

-- Step mo-342377.R1.H2: hypothesis H2 of reduction mo-342377.R1
-- Credit: @Genbox
-- H2 := ∀ a c : ℕ, 2 ≤ a → 2 ≤ c → (a - 1) * (a + 2) ≠ Nat.ascFactorial c 4

theorem OMA.solution : OMA.R_mo_342377_R1.H2 := by
  intro a c ha hc h
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  have e : Nat.ascFactorial c 4 = c * (c + 1) * (c + 2) * (c + 3) := by
    simp [Nat.ascFactorial_succ, Nat.ascFactorial_zero]; ring
  rw [e] at h
  simp only [Nat.add_sub_cancel] at h
  have ht : (c * (c + 1) * (c + 2) * (c + 3)) = (c*c+3*c) * (c*c+3*c+2) := by ring
  rw [ht] at h
  generalize c*c+3*c = t at h
  have h10 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; nlinarith
    · exact h0
  rcases lt_trichotomy k t with h1 | h1 | h1
  · have : k + 1 ≤ t := h1
    nlinarith [Nat.mul_le_mul this this]
  · subst h1; nlinarith
  · have : t + 1 ≤ k := h1
    nlinarith [Nat.mul_le_mul this this]
