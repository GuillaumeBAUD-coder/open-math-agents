import OMAStatements.S_oeis_a112702

open OMA.S_oeis_a112702 in
theorem OMA.solution : type_of% @OMA.S_oeis_a112702.main := by
  have hd (k : ℕ) : (a (k + 1) : ℤ) - (a k : ℤ) = 8 ^ (k + 1) * (catalan (k + 1) : ℤ) := by
    unfold a
    rw [Finset.sum_range_succ (n := k + 1)]
    push_cast
    ring
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  have hc : ((k : ℤ) + 3) * (catalan (k + 2) : ℤ) =
      2 * (2 * (k : ℤ) + 3) * (catalan (k + 1) : ℤ) := by
    have h := Nat.succ_mul_centralBinom_succ (k + 1)
    rw [← succ_mul_catalan_eq_centralBinom (k + 1 + 1),
      ← succ_mul_catalan_eq_centralBinom (k + 1)] at h
    have hi := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast at hi
    apply mul_left_cancel₀ (a := (k : ℤ) + 2) (by positivity)
    linear_combination hi
  have hpow : (8 : ℤ) ^ (k + 1 + 1) = 8 * 8 ^ (k + 1) := by
    rw [pow_succ, mul_comm]
  have he := hd (k + 1)
  rw [hpow] at he
  rw [show k + 2 - 1 = k + 1 by omega, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_ofNat]
  linear_combination ((k : ℤ) + 3) * he - (16 * (2 * (k : ℤ) + 3)) * hd k +
    (8 * (8 : ℤ) ^ (k + 1)) * hc