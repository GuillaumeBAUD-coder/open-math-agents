import OMAReductions.R_Erdos727_erdos_727_variants_k_2_R1

theorem OMA.solution : OMA.R_Erdos727_erdos_727_variants_k_2_R1.H1 := by
  intro n
  have hf : (n + 2).factorial = ((n + 1) * (n + 2)) * n.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    ac_rfl
  have hb : (2 * n).factorial = (2 * n).choose n * n.factorial ^ 2 := by
    have h := Nat.add_choose_mul_factorial_mul_factorial n n
    simpa only [Nat.two_mul, Nat.pow_two, Nat.mul_assoc] using h.symm
  rw [hf, hb, Nat.mul_pow]
  exact Nat.mul_dvd_mul_iff_right (Nat.pow_pos (Nat.factorial_pos n))
