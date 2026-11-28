import OMAStatements.S_oeis_a016789
theorem OMA.solution : type_of% @OMA.S_oeis_a016789.main := by
  intro y
  unfold OMA.S_oeis_a016789.a
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨9 * (n : ℤ) ^ 3 + 18 * n ^ 2 + 12 * n + 2, by push_cast; ring⟩
  · rintro ⟨k, hk⟩
    refine ⟨y / 3, ?_⟩
    have h := congrArg (· % 3) hk
    simp only [pow_succ, pow_zero, one_mul, Int.mul_emod (y : ℤ), Int.add_mul_emod_self_left] at h
    rcases (by omega : (y : ℤ) % 3 = 0 ∨ (y : ℤ) % 3 = 1 ∨ (y : ℤ) % 3 = 2) with h' | h' | h' <;>
      simp [h', Int.mul_emod] at h <;> omega
