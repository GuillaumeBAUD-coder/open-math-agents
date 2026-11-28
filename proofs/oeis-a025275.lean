import OMAStatements.S_oeis_a025275

-- Problem: A025275, Mathar's recurrence (known result, proof via the g.f. equation A^2 - A = -x + x^2 - x^3 + 2x^4).
-- Credit: @katiem08
open PowerSeries

namespace OMAa025275

lemma key (A E : ℚ⟦X⟧) (h : A ^ 2 = A + E) :
    (1 + 4 * E) * d⁄dX ℚ A - 2 * d⁄dX ℚ E * A + d⁄dX ℚ E = 0 := by
  have hD : 2 * A * d⁄dX ℚ A = d⁄dX ℚ A + d⁄dX ℚ E := by
    have h2 := congrArg (d⁄dX ℚ) h
    rw [map_add, pow_two, Derivation.leibniz, smul_eq_mul] at h2
    linear_combination h2
  linear_combination (-4 * d⁄dX ℚ A) * h + (2 * A - 1) * hD

noncomputable def E : ℚ⟦X⟧ := -X ^ 1 + X ^ 2 - X ^ 3 + C (2:ℚ) * X ^ 4

lemma dE : d⁄dX ℚ E = -1 + C (2:ℚ) * X ^ 1 - C (3:ℚ) * X ^ 2 + C (8:ℚ) * X ^ 3 := by
  ext k
  rw [coeff_derivative]
  simp only [E, map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow, coeff_one]
  rcases Nat.lt_or_ge k 4 with hk | hk
  · interval_cases k <;> norm_num
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp

noncomputable def ser (a : ℕ → ℚ) : ℚ⟦X⟧ := mk fun n => if n = 0 then 0 else a n

lemma coeff_E (m : ℕ) (hm : 5 ≤ m) : coeff m E = 0 := by
  simp only [E, map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

lemma sq_eq (a : ℕ → ℚ) (h1 : a 1 = 1) (h2 : a 2 = 0) (h3 : a 3 = 1) (h4 : a 4 = 0)
    (hr : ∀ n : ℕ, 5 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k)) :
    ser a ^ 2 = ser a + E := by
  ext m
  rw [pow_two, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (ser a) * coeff j (ser a)),
    map_add]
  simp only [ser, coeff_mk]
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m <;>
      (simp [Finset.sum_range_succ, E, coeff_X_pow, coeff_X, h1, h2, h3, h4]; try norm_num)
  · rw [coeff_E m hm, add_zero, if_neg (by omega), hr m hm]
    symm
    apply Finset.sum_subset_zero_on_sdiff
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_range]
      omega
    · intro k hk
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc] at hk
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · simp [h0]
      · have : m - k = 0 := by omega
        simp [this]
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      rw [if_neg (by omega), if_neg (by omega)]

theorem target (a : ℕ → ℚ) (h1 : a 1 = 1) (h2 : a 2 = 0) (h3 : a 3 = 1) (h4 : a 4 = 0)
    (hr : ∀ n : ℕ, 5 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k))
    (n : ℕ) (hn : 5 ≤ n) :
      ((n : ℚ)) * a n + (6 - 4 * (n : ℚ)) * a (n - 1) +
        (-12 + 4 * (n : ℚ)) * a (n - 2) + (18 - 4 * (n : ℚ)) * a (n - 3) +
        (-48 + 8 * (n : ℚ)) * a (n - 4) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have hk0 := key (ser a) E (sq_eq a h1 h2 h3 h4 hr)
  rw [show (4:ℚ⟦X⟧) = C (4:ℚ) from (map_ofNat C 4).symm,
    show (2:ℚ⟦X⟧) = C (2:ℚ) from (map_ofNat C 2).symm, dE] at hk0
  have hk := congrArg (coeff (m + 4)) hk0
  simp only [E, mul_add, add_mul, sub_mul, mul_sub, neg_mul, mul_neg, one_mul, mul_one, map_add, map_sub,
    map_neg, map_zero, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_one, coeff_X_pow,
    coeff_derivative, ser, coeff_mk] at hk
  simp at hk
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
  rw [show m + 4 + 1 = m + 5 by omega, show m + 3 + 1 = m + 4 by omega,
    show m + 2 + 1 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega] at hk
  push_cast
  linear_combination hk

end OMAa025275

theorem OMA.solution : type_of% @OMA.S_oeis_a025275.main := by
  intro a h1 h2 h3 h4 hr n hn
  exact OMAa025275.target a h1 h2 h3 h4 hr n hn
