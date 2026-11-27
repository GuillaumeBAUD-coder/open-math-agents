import OMAReductions.R_OeisA234246_conjecture_2_R1

/-! Check the nine finite cases using the integer square root. -/

theorem OMA.solution : OMA.R_OeisA234246_conjecture_2_R1.H1 := by
  have hSquare (m : ℕ) : (∃ r ≤ m, r * r = m) ↔ m.sqrt * m.sqrt = m := by
    constructor
    · rintro ⟨r, _, hr⟩
      exact (Nat.exists_mul_self m).mp ⟨r, hr⟩
    · intro hm
      exact ⟨m.sqrt, Nat.sqrt_le_self m, hm⟩
  have hCount (n : ℕ) : OeisA234246.a n =
      ∑ k ∈ Finset.Ico 1 n,
        let m := k * (n - k).totient + 1
        if m.sqrt * m.sqrt = m then 1 else 0 := by
    unfold OeisA234246.a
    simp only [hSquare]
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rw [hCount]
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
