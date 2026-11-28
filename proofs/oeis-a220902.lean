import OMAStatements.S_oeis_a220902

theorem OMA.solution : type_of% @OMA.S_oeis_a220902.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have r (j : ℕ) : ((j : ℤ) + 2) * catalan (j + 1) = 2 * (2 * j + 1) * catalan j := by
    have := Nat.succ_mul_centralBinom_succ j
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at this
    exact_mod_cast Nat.eq_of_mul_eq_mul_left j.succ_pos (by ring_nf at this ⊢; linarith)
  have r4 := r (k+4)
  have r3 := r (k+3)
  have r2 := r (k+2)
  have r1 := r (k+1)
  simp [OMA.S_oeis_a220902.a, add_assoc] at r1 r2 r3 r4 ⊢
  linear_combination r4 - 2*r3 + 3*r2 - 2*r1 + r k
