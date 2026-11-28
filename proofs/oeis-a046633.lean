import OMAStatements.S_oeis_a046633
import Mathlib

open OMA.S_oeis_a046633 PowerSeries

lemma OMA.dv (n : ℕ) : (5 ^ (n + 2) + 2 * b n) % 31 = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> decide
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have := ih k (by omega)
      have hb : b (k + 3) = b k := by simp only [b, show (k + 3) % 3 = k % 3 by omega]
      rw [hb, show k + 3 + 2 = (k + 2) + 3 by ring, pow_add]
      omega

lemma OMA.cl (n : ℕ) : (a n : ℤ) * 31 = 5 ^ (n + 2) + 2 * (b n : ℤ) := by
  have := OMA.dv n
  simp only [a]
  have h : 31 ∣ 5 ^ (n + 2) + 2 * b n := Nat.dvd_of_mod_eq_zero this
  exact_mod_cast Nat.div_mul_cancel h

lemma OMA.rec (m : ℕ) : (a (m + 4) : ℤ) = 5 * a (m + 3) + a (m + 1) - 5 * a m := by
  have h4 := OMA.cl (m + 4); have h3 := OMA.cl (m + 3); have h1 := OMA.cl (m + 1); have h0 := OMA.cl m
  have hb : b (m + 4) = b (m + 1) := by simp only [b, show (m + 4) % 3 = (m + 1) % 3 by omega]
  have hb' : b (m + 3) = b m := by simp only [b, show (m + 3) % 3 = m % 3 by omega]
  rw [hb] at h4; rw [hb'] at h3
  apply mul_right_cancel₀ (show (31 : ℤ) ≠ 0 by norm_num)
  rw [show m + 4 + 2 = m + 2 + 4 by ring, show m + 3 + 2 = m + 2 + 3 by ring,
    show m + 1 + 2 = m + 2 + 1 by ring] at *
  linear_combination h4 - 5 * h3 - h1 + 5 * h0

theorem OMA.solution : type_of% @OMA.S_oeis_a046633.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 3 = m + 1 by omega,
      show m + 4 - 4 = m by omega]
    exact OMA.rec m
  · simp only [denominator, generating, numerator]
    have e : (X - 1) * (C 5 * X - 1) * (1 + X + X ^ 2 : PowerSeries ℚ) =
        1 - C 5 * X ^ 1 - X ^ 3 + C 5 * X ^ 4 := by
      simp only [map_ofNat]; ring
    have r : (1 - C 4 * X ^ 2 - C 5 * X ^ 3 : PowerSeries ℚ) =
        C 1 * X ^ 0 - C 4 * X ^ 2 - C 5 * X ^ 3 := by simp
    rw [e, r]
    ext n
    simp only [sub_mul, add_mul, one_mul, map_sub, map_add, coeff_mk]
    rw [mul_assoc, mul_assoc, coeff_C_mul, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul',
      coeff_X_pow_mul']
    simp only [coeff_C_mul, coeff_X_pow, coeff_mk]
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> norm_num [a, b]
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      simp only [if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 2 by omega),
        if_neg (show n ≠ 3 by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 3 = k + 1 by omega,
        show k + 4 - 4 = k by omega]
      have := OMA.rec k
      have h' : ((a (k + 4) : ℤ) : ℚ) = 5 * ((a (k + 3) : ℤ) : ℚ) + ((a (k + 1) : ℤ) : ℚ) -
          5 * ((a k : ℤ) : ℚ) := by exact_mod_cast this
      push_cast at h'
      linear_combination h'
