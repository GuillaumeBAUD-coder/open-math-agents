import OMAReductions.R_OeisA1146_conjecture_R1

-- Step OeisA1146.conjecture.R1.H1: hypothesis H1 of reduction OeisA1146.conjecture.R1
-- Credit: @luciusacarr

/-! `(2^m)^4 - 1 = 2^(4m) - 1` divides `2^(2^m) - 1` iff `4m ∣ 2^m`, iff `m = 2^t` with `t ≥ 2`. -/

private theorem four_mul_dvd_iff (m : ℕ) : 4 * m ∣ 2 ^ m ↔ ∃ t : ℕ, 2 ≤ t ∧ m = 2 ^ t := by
  constructor
  · intro h
    obtain ⟨t, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.dvd.trans (Dvd.intro_left 4 rfl) h)
    have h4 : 4 * 2 ^ t = 2 ^ (t + 2) := by rw [pow_add]; ring
    rw [h4, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at h
    refine ⟨t, ?_, rfl⟩
    by_contra hlt
    interval_cases t <;> simp at h
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
    have h4 : 4 * 2 ^ (s + 2) = 2 ^ (s + 4) := by rw [pow_add, pow_add]; ring
    rw [h4, Nat.pow_dvd_pow_iff_le_right (by norm_num)]
    have hs : s < 2 ^ s := Nat.lt_two_pow_self
    have he : 2 ^ (s + 2) = 4 * 2 ^ s := by rw [pow_add]; ring
    omega

theorem OMA.solution : OMA.R_OeisA1146_conjecture_R1.H1 := by
  intro m
  rw [← pow_mul, OMA.Hasler.mersenneIff, mul_comm m 4]
  exact four_mul_dvd_iff m
