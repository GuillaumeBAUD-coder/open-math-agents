import OMAReductions.R_Erdos727_erdos_727_variants_k_2_R1

theorem OMA.solution : OMA.R_Erdos727_erdos_727_variants_k_2_R1.H1 := by
  intro n
  have h := Nat.add_choose_mul_factorial_mul_factorial n n
  rw [← Nat.two_mul, Nat.mul_assoc, ← Nat.pow_two] at h
  rw [← h, Nat.factorial_succ, Nat.factorial_succ]
  convert Nat.mul_dvd_mul_iff_right (Nat.pow_pos (n := 2) (Nat.factorial_pos n)) using 2; ring
