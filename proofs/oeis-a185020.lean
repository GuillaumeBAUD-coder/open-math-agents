import OMAStatements.S_oeis_a185020

open OMA.S_oeis_a185020 in
theorem OMA.solution : type_of% @OMA.S_oeis_a185020.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have r (j : ℕ) : ((j:ℤ)+2) * catalan (j+1) = 2*(2*j+1) * catalan j := by
    have := Nat.succ_mul_centralBinom_succ j
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at this
    exact_mod_cast Nat.eq_of_mul_eq_mul_left j.succ_pos (by ring_nf at this ⊢; linarith)
  have r1 := r (k+1)
  simp [a, s, add_assoc] at r1 ⊢
  linear_combination (k+2:ℤ)*(2*(2*s (k+1)+2*s k)+2*s (k+1))*r1 + 4*(2*k+3:ℤ)*s (k+1)*r k
