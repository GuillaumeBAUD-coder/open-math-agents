import OMAReductions.R_Erdos386_erdos_386_variants_two_R1

/-! The square discriminant criterion for triangular numbers.
The odd square root of 8 * P + 1 is 2 * t + 1, so P = (t + 1).choose 2.
Credit: @rgoldman73-dev. -/
theorem OMA.solution : OMA.R_Erdos386_erdos_386_variants_two_R1.H1 := by
  intro P hP hSquare
  obtain ⟨k, hk⟩ := hSquare
  have hOdd : Odd (k * k) := by
    rw [← hk]
    exact ⟨4 * P, by omega⟩
  obtain ⟨t, ht⟩ := (Nat.odd_mul.mp hOdd).1
  rw [ht] at hk
  have hProduct : (t + 1) * t = P * 2 := by nlinarith [hk]
  have ht3 : 3 ≤ t := by
    by_contra! h
    interval_cases t <;> omega
  refine ⟨t + 1, by omega, ?_, ?_⟩
  · rw [Nat.choose_two_right, Nat.add_sub_cancel, hProduct, Nat.mul_div_cancel] <;> norm_num
  · nlinarith [hProduct]
