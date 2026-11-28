import OMAStatements.S_oeis_a112703

theorem OMA.solution : type_of% @OMA.S_oeis_a112703.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h1 := succ_mul_catalan_eq_centralBinom (k+2)
  have h2 := succ_mul_catalan_eq_centralBinom (k+1)
  have h3 := (k+1).succ_mul_centralBinom_succ
  zify at h1 h2 h3
  simp [OMA.S_oeis_a112703.a, Finset.sum_range_succ, add_assoc] at h1 h2 h3 ⊢
  exact mul_left_cancel₀ (by positivity : (k:ℤ)+2 ≠ 0)
    (by linear_combination 9^(k+2) * ((k+2)*h1 + h3 - 2*(2*k+3)*h2))
