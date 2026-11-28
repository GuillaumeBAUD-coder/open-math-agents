import OMAStatements.S_oeis_a290745
import Mathlib

namespace OMA.S_oeis_a290745
open PowerSeries

lemma ch2 (k : ℕ) : ((k.choose 2 : ℕ) : ℤ) * 2 = (k : ℤ) * ((k : ℤ) - 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linarith

lemma a_shift (m : ℕ) : a (m + 10) = a m + 9 * (m : ℤ) + 45 := by
  obtain ⟨q, p, hp, rfl⟩ : ∃ q p : ℕ, p < 10 ∧ m = 10 * q + p := ⟨m / 10, m % 10, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 10).symm⟩
  have e1 : (10 * q + p + 10) % 10 = p := by omega
  have e2 : (10 * q + p + 10) / 10 = q + 1 := by omega
  have e3 : (10 * q + p) % 10 = p := by omega
  have e4 : (10 * q + p) / 10 = q := by omega
  unfold a
  rw [e1, e2, e3, e4]
  have h11 := ch2 (10 * q + p + 10 + 1)
  have h1 := ch2 (10 * q + p + 1)
  have h2 := ch2 (q + 1 + 1)
  have h3 := ch2 (q + 1 + 2)
  have h4 := ch2 (q + 1)
  have h5 := ch2 (q + 2)
  push_cast at *
  have c2 : ((q + 1 + 2).choose 2 : ℤ) = (q + 1 + 1).choose 2 + (q + 2) := by nlinarith
  have c1 : ((q + 1 + 1).choose 2 : ℤ) = (q + 1).choose 2 + (q + 1) := by nlinarith
  have c0 : ((q + 2).choose 2 : ℤ) = (q + 1 + 1).choose 2 := by norm_num
  have hpz : (p : ℤ) < 10 := by exact_mod_cast hp
  have : (((10 * q + p + 10 + 1).choose 2 : ℕ) : ℤ) = ((10 * q + p + 1).choose 2 : ℕ) + (10 * (10 * q + p) + 55) := by nlinarith
  push_cast
  rw [this]
  nlinarith

lemma b_eq (n : ℕ) (h : 1 ≤ n) : b n = a n := by simp [b]; omega

lemma poly_eq : ((1 - X) ^ 3 * (1 + X) * (1 - X + X ^ 2 - X ^ 3 + X ^ 4) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) : ℚ⟦X⟧)
    = 1 - 2 * X + X ^ 2 - X ^ 10 + 2 * X ^ 11 - X ^ 12 := by ring

lemma coeff_lhs (n : ℕ) : coeff n (PowerSeries.mk (fun n => (b n : ℚ)) * (1 - 2 * X + X ^ 2 - X ^ 10 + 2 * X ^ 11 - X ^ 12 : ℚ⟦X⟧))
    = (b n : ℚ) - 2 * (if 1 ≤ n then (b (n-1) : ℚ) else 0) + (if 2 ≤ n then (b (n-2) : ℚ) else 0)
      - (if 10 ≤ n then (b (n-10) : ℚ) else 0) + 2 * (if 11 ≤ n then (b (n-11) : ℚ) else 0)
      - (if 12 ≤ n then (b (n-12) : ℚ) else 0) := by
  have e : (1 - 2 * X + X ^ 2 - X ^ 10 + 2 * X ^ 11 - X ^ 12 : ℚ⟦X⟧)
      = 1 - C (2:ℚ) * X ^ 1 + X ^ 2 - X ^ 10 + C (2:ℚ) * X ^ 11 - X ^ 12 := by
    rw [show (C (2:ℚ)) = (2:ℚ⟦X⟧) from map_ofNat C 2]; ring
  rw [e]
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, ← mul_assoc, coeff_mul_X_pow', mul_comm _ (C (2:ℚ)),
    coeff_C_mul]
  simp [coeff_mul_C]

lemma coeff_rhs (n : ℕ) : coeff (n+1) (X * (10 - 9 * X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 8 + X ^ 9 - 10 * X ^ 10 + 10 * X ^ 11 : ℚ⟦X⟧))
    = 10 * (if n = 0 then 1 else 0) - 9 * (if n = 1 then 1 else 0) + (if n = 2 then 1 else 0) + (if n = 3 then 1 else 0)
      + (if n = 4 then 1 else 0) + (if n = 5 then 1 else 0) + (if n = 6 then 1 else 0) + (if n = 7 then 1 else 0)
      + (if n = 8 then 1 else 0) + (if n = 9 then 1 else 0) - 10 * (if n = 10 then 1 else 0) + 10 * (if n = 11 then 1 else 0) := by
  have e : (10 - 9 * X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 8 + X ^ 9 - 10 * X ^ 10 + 10 * X ^ 11 : ℚ⟦X⟧)
      = C (10:ℚ) * X ^ 0 - C (9:ℚ) * X ^ 1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 8 + X ^ 9 - C (10:ℚ) * X ^ 10 + C (10:ℚ) * X ^ 11 := by
    rw [show (C (10:ℚ)) = (10:ℚ⟦X⟧) from map_ofNat C 10, show (C (9:ℚ)) = (9:ℚ⟦X⟧) from map_ofNat C 9]; ring
  rw [e, coeff_succ_X_mul]
  simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow]

lemma main_aux (n : ℕ) : coeff n (PowerSeries.mk (fun n => (b n : ℚ)) * (1 - 2 * X + X ^ 2 - X ^ 10 + 2 * X ^ 11 - X ^ 12 : ℚ⟦X⟧))
    = coeff n (X * (10 - 9 * X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 8 + X ^ 9 - 10 * X ^ 10 + 10 * X ^ 11 : ℚ⟦X⟧)) := by
  rw [coeff_lhs]
  rcases n with _ | n
  · simp [b]
  · rw [coeff_rhs]
    by_cases h : n + 1 ≤ 12
    · have : n ≤ 11 := by omega
      interval_cases n <;> simp [b, a] <;> norm_num [Nat.choose]
    · have h13 : 13 ≤ n + 1 := by omega
      have hn : ∀ k, k ≤ 11 → ¬ (n = k) := fun k hk => by omega
      simp only [if_neg (hn 0 (by norm_num)), if_neg (hn 1 (by norm_num)), if_neg (hn 2 (by norm_num)),
        if_neg (hn 3 (by norm_num)), if_neg (hn 4 (by norm_num)), if_neg (hn 5 (by norm_num)),
        if_neg (hn 6 (by norm_num)), if_neg (hn 7 (by norm_num)), if_neg (hn 8 (by norm_num)),
        if_neg (hn 9 (by norm_num)), if_neg (hn 10 (by norm_num)), if_neg (hn 11 (by norm_num))]
      have s0 := a_shift (n + 1 - 10)
      have s1 := a_shift (n + 1 - 11)
      have s2 := a_shift (n + 1 - 12)
      rw [show n + 1 - 10 + 10 = n + 1 by omega] at s0
      rw [show n + 1 - 11 + 10 = n + 1 - 1 by omega] at s1
      rw [show n + 1 - 12 + 10 = n + 1 - 2 by omega] at s2
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      rw [b_eq _ (by omega), b_eq _ (by omega), b_eq _ (by omega), b_eq _ (by omega), b_eq _ (by omega), b_eq _ (by omega)]
      have c0 : ((n + 1 - 10 : ℕ) : ℤ) = (n : ℤ) - 9 := by omega
      have c1 : ((n + 1 - 11 : ℕ) : ℤ) = (n : ℤ) - 10 := by omega
      have c2 : ((n + 1 - 12 : ℕ) : ℤ) = (n : ℤ) - 11 := by omega
      rw [c0] at s0
      rw [c1] at s1
      rw [c2] at s2
      have key : (a (n+1) : ℤ) - 2 * a (n+1-1) + a (n+1-2) - a (n+1-10) + 2 * a (n+1-11) - a (n+1-12) = 0 := by linarith
      have key' : ((a (n+1) : ℤ) : ℚ) - 2 * (a (n+1-1) : ℤ) + (a (n+1-2) : ℤ) - (a (n+1-10) : ℤ) + 2 * (a (n+1-11) : ℤ) - (a (n+1-12) : ℤ) = 0 := by
        exact_mod_cast key
      linarith

end OMA.S_oeis_a290745

theorem OMA.solution : type_of% @OMA.S_oeis_a290745.main := by
  show PowerSeries.mk (fun n => (OMA.S_oeis_a290745.b n : ℚ)) * _ = _
  rw [OMA.S_oeis_a290745.poly_eq]
  ext n
  exact OMA.S_oeis_a290745.main_aux n
