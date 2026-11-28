import OMAReductions.R_mo_342377_R1

-- Step mo-342377.R1.H2: hypothesis H2 of reduction mo-342377.R1
-- Credit: @sovrana

theorem asc4 (c : ℕ) : Nat.ascFactorial c 4 = c * (c + 1) * (c + 2) * (c + 3) := by
  simp [Nat.ascFactorial_succ]
  ring

theorem sol : ∀ a c : ℕ, 2 ≤ a → 2 ≤ c → (a - 1) * (a + 2) ≠ Nat.ascFactorial c 4 := by
  intro a c ha hc h
  rw [asc4] at h
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  have h' : (b + 1) * (b + 4) = c * (c + 1) * (c + 2) * (c + 3) := by
    simpa [show b + 2 - 1 = b + 1 by omega, show b + 2 + 2 = b + 4 by omega] using h
  have key : (b + 1) * (b + 4) + 1 = (c ^ 2 + 3 * c + 1) ^ 2 := by
    rw [h']; ring_nf
  have h1 : b + 2 < c ^ 2 + 3 * c + 1 := by
    by_contra hh
    push Not at hh
    have := Nat.pow_le_pow_left hh 2
    nlinarith
  have h2 : c ^ 2 + 3 * c + 1 < b + 3 := by
    by_contra hh
    push Not at hh
    have := Nat.pow_le_pow_left hh 2
    nlinarith
  omega

theorem OMA.solution : OMA.R_mo_342377_R1.H2 := sol
