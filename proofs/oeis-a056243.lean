import OMAStatements.S_oeis_a056243
import Mathlib

namespace OMA.P056243

open OMA.S_oeis_a056243 Polynomial

lemma a_eq (m : ℕ) : a (m + 3) = ∑ j ∈ Finset.range (m + 1),
    (-1 : ℤ) ^ (m - j) * (m.choose j : ℤ) * ((m + 2 + 2 * j).choose (m + 2) : ℤ) := by
  unfold a T
  rw [if_neg (by omega)]
  have e : m + 3 - 2 = m + 1 := by omega
  rw [e]
  apply Finset.sum_congr rfl
  intro j hj
  have e1 : m + 1 - 1 - j = m - j := by omega
  have e2 : m + 1 - 1 = m := by omega
  have e3 : m + 3 + 2 * j - 1 = m + 2 + 2 * j := by omega
  have e4 : (m + 2 + 2 * j).choose (2 * j) = (m + 2 + 2 * j).choose (m + 2) :=
    (Nat.choose_symm_add (a := m + 2) (b := 2 * j)).symm
  rw [e1, e2, e3, e4]

lemma poly_id (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1),
        C ((-1 : ℤ) ^ (m - j) * (m.choose j : ℤ)) * (X + C (1 : ℤ)) ^ (m + 2 + 2 * j)
      = (X + C (1 : ℤ)) ^ (m + 2) * (X + C (2 : ℤ)) ^ m * X ^ m := by
  have h := add_pow ((X + C (1 : ℤ)) ^ 2) (C (-1 : ℤ)) m
  have e : (X + C (1 : ℤ)) ^ 2 + C (-1 : ℤ) = (X + C (2 : ℤ)) * X := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [e, mul_pow] at h
  rw [mul_assoc, h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_add, pow_mul]
  simp only [map_mul, map_pow, map_natCast, map_neg, map_one]
  ring

lemma coeffA (k : ℕ) :
    ((X + C (1 : ℤ)) ^ (k + 4) * (X + C (2 : ℤ)) ^ (k + 2)).coeff 2
      = 2 ^ (k + 2) * (((k + 4).choose 2 : ℕ) : ℤ) + ((k : ℤ) + 4) * (2 ^ (k + 1) * ((k : ℤ) + 2))
        + 2 ^ k * (((k + 2).choose 2 : ℕ) : ℤ) := by
  rw [coeff_mul]
  simp only [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_cons,
    Finset.sum_map, Finset.sum_singleton, Function.Embedding.coe_prodMap,
    Function.Embedding.coeFn_mk, Prod.map, Function.Embedding.refl_apply, coeff_X_add_C_pow]
  simp
  ring

lemma S_eq (m : ℕ) : a (m + 3)
    = ((X + C (1 : ℤ)) ^ (m + 2) * (X + C (2 : ℤ)) ^ m).coeff 2 := by
  rw [a_eq]
  have h := congrArg (fun q : ℤ[X] => q.coeff (2 + m)) (poly_id m)
  simp only [finset_sum_coeff, coeff_C_mul, coeff_X_add_C_pow, coeff_mul_X_pow, one_pow, one_mul]
    at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show 2 + m = m + 2 from by ring]

lemma E (m : ℕ) : 8 * a (m + 3) = 2 ^ m * (9 * (m : ℤ) ^ 2 + 19 * (m : ℤ) + 8) := by
  rcases m with _ | _ | k
  · decide
  · decide
  · rw [S_eq, show k + 1 + 1 + 2 = k + 4 from by ring, show k + 1 + 1 = k + 2 from by ring, coeffA]
    have c1 : (2 : ℤ) * (((k + 4).choose 2 : ℕ) : ℤ) = ((k : ℤ) + 4) * ((k : ℤ) + 3) := by
      have h := Nat.choose_two_right (k + 4)
      have h2 : 2 * (k + 4).choose 2 = (k + 4) * (k + 3) := by
        rw [h]
        exact Nat.mul_div_cancel' (by
          have := Nat.even_mul_succ_self (k + 3)
          rw [mul_comm] at this
          exact this.two_dvd)
      exact_mod_cast h2
    have c2 : (2 : ℤ) * (((k + 2).choose 2 : ℕ) : ℤ) = ((k : ℤ) + 2) * ((k : ℤ) + 1) := by
      have h := Nat.choose_two_right (k + 2)
      have h2 : 2 * (k + 2).choose 2 = (k + 2) * (k + 1) := by
        rw [h]
        exact Nat.mul_div_cancel' (by
          have := Nat.even_mul_succ_self (k + 1)
          rw [mul_comm] at this
          exact this.two_dvd)
      exact_mod_cast h2
    push_cast
    linear_combination (4 * 2 ^ (k + 2) : ℤ) * c1 + (4 * 2 ^ k : ℤ) * c2

lemma v0 : a 0 = 0 := by decide

lemma v1 : a 1 = 0 := by decide

lemma v2 : a 2 = 0 := by decide

lemma v3 : a 3 = 1 := by decide

lemma v4 : a 4 = 9 := by decide

lemma v5 : a 5 = 41 := by decide

lemma rec (m : ℕ) : a (m + 6) = 6 * a (m + 5) - 12 * a (m + 4) + 8 * a (m + 3) := by
  have h0 := E m
  have h1 := E (m + 1)
  have h2 := E (m + 2)
  have h3 := E (m + 3)
  rw [show m + 1 + 3 = m + 4 from by ring] at h1
  rw [show m + 2 + 3 = m + 5 from by ring] at h2
  rw [show m + 3 + 3 = m + 6 from by ring] at h3
  push_cast at h1 h2 h3
  have h8 : (8 : ℤ) * (a (m + 6) - (6 * a (m + 5) - 12 * a (m + 4) + 8 * a (m + 3))) = 0 := by
    linear_combination h3 - 6 * h2 + 12 * h1 - 8 * h0
  have := mul_eq_zero.1 h8
  rcases this with h | h
  · norm_num at h
  · linarith

lemma closed (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℚ) = (2 : ℚ) ^ ((n : ℤ) - 6) * (32 - 35 * (n : ℚ) + 9 * (n : ℚ) ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := E m
  have hq : (8 : ℚ) * (a (m + 3) : ℚ) = 2 ^ m * (9 * (m : ℚ) ^ 2 + 19 * (m : ℚ) + 8) := by
    exact_mod_cast h
  have hz : (2 : ℚ) ^ (((m + 3 : ℕ) : ℤ) - 6) = 2 ^ m / 8 := by
    rw [show (((m + 3 : ℕ) : ℤ) - 6) = (m : ℤ) - 3 from by push_cast; ring,
      zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
    norm_num
  rw [hz]
  push_cast
  linear_combination (1 / 8 : ℚ) * hq

end OMA.P056243

theorem OMA.solution : type_of% @OMA.S_oeis_a056243.main := by
  refine ⟨OMA.P056243.closed, ?_⟩
  have key : PowerSeries.mk OMA.S_oeis_a056243.a
      - PowerSeries.C (6 : ℤ) * (PowerSeries.mk OMA.S_oeis_a056243.a * PowerSeries.X ^ 1)
      + PowerSeries.C (12 : ℤ) * (PowerSeries.mk OMA.S_oeis_a056243.a * PowerSeries.X ^ 2)
      - PowerSeries.C (8 : ℤ) * (PowerSeries.mk OMA.S_oeis_a056243.a * PowerSeries.X ^ 3)
      - (PowerSeries.X ^ 3 * PowerSeries.C (1 : ℤ) + PowerSeries.X ^ 4 * PowerSeries.C (3 : ℤ)
        - PowerSeries.X ^ 5 * PowerSeries.C (1 : ℤ)) = 0 := by
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow, map_zero]
    rcases Nat.lt_or_ge n 6 with hlt | hge
    · interval_cases n <;> norm_num [OMA.P056243.v0, OMA.P056243.v1, OMA.P056243.v2,
        OMA.P056243.v3, OMA.P056243.v4, OMA.P056243.v5]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      have h := OMA.P056243.rec m
      have z3 : ¬ (m + 6 = 3) := by omega
      have z4 : ¬ (m + 6 = 4) := by omega
      have z5 : ¬ (m + 6 = 5) := by omega
      have w1 : 1 ≤ m + 6 := by omega
      have w2 : 2 ≤ m + 6 := by omega
      have w3 : 3 ≤ m + 6 := by omega
      have e1 : m + 6 - 1 = m + 5 := by omega
      have e2 : m + 6 - 2 = m + 4 := by omega
      have e3 : m + 6 - 3 = m + 3 := by omega
      simp only [z3, z4, z5, w1, w2, w3, e1, e2, e3, if_true, if_false, zero_mul, mul_zero,
        add_zero, sub_zero]
      linear_combination h
  simp only [map_ofNat, map_one] at key
  linear_combination key
