import OMAStatements.S_oeis_a099976

open OMA.S_oeis_a099976 in
theorem OMA.solution : type_of% @OMA.S_oeis_a099976.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h (j : ℕ) : ((j:ℤ)+1) * (j+1).centralBinom = 2*(2*j+1)*j.centralBinom :=
    mod_cast Nat.succ_mul_centralBinom_succ j
  have e j : a j = (2*j+1).centralBinom := by rw [a, Nat.centralBinom]; ring_nf
  have h1 := h (2*k+1)
  have h2 := h (2*k+2)
  simp [e, mul_add, add_assoc] at h1 h2 ⊢
  linear_combination (k+1:ℤ) * h2 + (4*k+5:ℤ) * h1
