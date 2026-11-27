import OMAStatements.S_oeis_a134347

theorem OMA.solution : type_of% @OMA.S_oeis_a134347.main := by
  have key : ∀ (x : ℤ) (k m : ℕ),
      ∑ j ∈ Finset.range (k + m + 1), (-1 : ℤ) ^ (k + m - j) * ((k + m).choose j : ℤ) *
        ((j.choose k : ℤ) * x ^ j) = ((k + m).choose k : ℤ) * x ^ k * (x - 1) ^ m := by
    intro x k m
    rw [show k + m + 1 = k + (m + 1) by ring, Finset.sum_range_add]
    have h0 : ∑ j ∈ Finset.range k, (-1 : ℤ) ^ (k + m - j) * ((k + m).choose j : ℤ) *
        ((j.choose k : ℤ) * x ^ j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_range] at hj
      simp [Nat.choose_eq_zero_of_lt hj]
    rw [h0, zero_add, sub_eq_add_neg, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hc : (k + m).choose (k + i) * (k + i).choose k = (k + m).choose k * m.choose i := by
      have hcm : (k + m).choose (k + i) * (k + i).choose k =
          (k + m).choose k * (k + m - k).choose (k + i - k) := by
        first
          | exact Nat.choose_mul (by omega)
          | exact Nat.choose_mul (by omega) (by omega)
      rw [hcm, show k + m - k = m by omega,
        show k + i - k = i by omega]
    have hc2 : ((k + m).choose (k + i) : ℤ) * ((k + i).choose k : ℤ) =
        ((k + m).choose k : ℤ) * (m.choose i : ℤ) := by exact_mod_cast hc
    rw [show k + m - (k + i) = m - i by omega]
    calc _ = ((k + m).choose (k + i) : ℤ) * ((k + i).choose k : ℤ) * ((-1) ^ (m - i) * x ^ (k + i)) := by
          ring
      _ = _ := by rw [hc2, pow_add]; ring
  intro n k hkn
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  unfold OMA.S_oeis_a134347.T OMA.S_oeis_a134347.A134346
  have e : ∀ j ∈ Finset.range (k + m + 1), (-1 : ℤ) ^ (k + m - j) * ((k + m).choose j : ℤ) *
      ((2 ^ (j + 1) - 1) * (j.choose k : ℤ)) =
      2 * ((-1 : ℤ) ^ (k + m - j) * ((k + m).choose j : ℤ) * ((j.choose k : ℤ) * 2 ^ j)) -
      (-1 : ℤ) ^ (k + m - j) * ((k + m).choose j : ℤ) * ((j.choose k : ℤ) * 1 ^ j) := by
    intro j _
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum, key 2 k m, key 1 k m]
  rcases m with _ | m
  · simp
    ring
  · rw [if_pos (by omega)]
    simp
    ring
