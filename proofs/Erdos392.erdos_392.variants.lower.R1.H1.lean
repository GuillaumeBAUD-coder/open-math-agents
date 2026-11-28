import OMAReductions.R_Erdos392_erdos_392_variants_lower_R1

open Real

theorem OMA.solution : OMA.R_Erdos392_erdos_392_variants_lower_R1.H1 := by
  intro n hn t a h hb
  have := log_le_log (by positivity) (((div_le_iff₀ (by positivity)).1 (pow_div_factorial_le_exp (x := n) (by positivity) n)).trans (mul_le_mul_of_nonneg_left (Nat.cast_le.2 (h ▸ Finset.prod_le_pow_card .univ a n fun i _ => hb i)) (by positivity)))
  simp [log_mul, (by positivity : (n:ℝ) ≠ 0)] at this
  rw [sub_le_comm, le_div_iff₀ (log_pos (by norm_cast))]
  linarith
