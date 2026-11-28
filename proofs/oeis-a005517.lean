import OMAStatements.S_oeis_a005517

open PowerSeries OMA.S_oeis_a005517

private lemma A005517_recur (k : ℕ) :
    A005517 (k + 6) = 5 * A005517 (k + 3) := by
  unfold A005517
  have hne0a : k + 6 ≠ 0 := by omega
  have hne1a : k + 6 ≠ 1 := by omega
  have hne2a : k + 6 ≠ 2 := by omega
  have hne0b : k + 3 ≠ 0 := by omega
  have hne1b : k + 3 ≠ 1 := by omega
  have hne2b : k + 3 ≠ 2 := by omega
  simp only [hne0a, hne1a, hne2a, hne0b, hne1b, hne2b, ↓reduceIte]
  rw [show (k + 6) % 3 = (k + 3) % 3 by omega]
  split_ifs with h0 h1
  · rw [show (k + 6 - 3) / 3 = (k + 3 - 3) / 3 + 1 by omega, pow_succ']
    ring
  · rw [show (k + 6 - 1) / 3 = (k + 3 - 1) / 3 + 1 by omega, pow_succ']
  · rw [show (k + 6 - 5) / 3 = (k + 3 - 5) / 3 + 1 by omega, pow_succ']
    ring

private lemma coeff_lhs_split (m : ℕ) :
    coeff m ((mk fun n => (A005517 (n + 1) : ℚ)) * (1 - 5 * (X : PowerSeries ℚ) ^ 3)) =
      (A005517 (m + 1) : ℚ) - 5 * coeff m ((mk fun n => (A005517 (n + 1) : ℚ)) * (X : PowerSeries ℚ) ^ 3) := by
  set p : PowerSeries ℚ := mk fun n => (A005517 (n + 1) : ℚ)
  have hC5 : (5 : PowerSeries ℚ) = C (5 : ℚ) := (map_ofNat (C : ℚ →+* PowerSeries ℚ) 5).symm
  have hmul : p * (1 - 5 * (X : PowerSeries ℚ) ^ 3) = p - C (5 : ℚ) * (p * (X : PowerSeries ℚ) ^ 3) := by
    rw [mul_sub, mul_one, hC5]
    ring
  rw [hmul, map_sub, coeff_C_mul, coeff_mk]

private lemma coeff_lhs_lt {m : ℕ} (hm : m < 3) :
    coeff m ((mk fun n => (A005517 (n + 1) : ℚ)) * (1 - 5 * (X : PowerSeries ℚ) ^ 3)) =
      (A005517 (m + 1) : ℚ) := by
  rw [coeff_lhs_split]
  have hzero : coeff m ((mk fun n => (A005517 (n + 1) : ℚ)) * (X : PowerSeries ℚ) ^ 3) = 0 := by
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx' : x.1 + x.2 = m := by simpa using hx
    have hx2 : x.2 ≠ 3 := by omega
    rw [coeff_X_pow]
    simp only [hx2, ↓reduceIte, mul_zero]
  rw [hzero, mul_zero, sub_zero]

private lemma coeff_lhs_ge (d : ℕ) :
    coeff (d + 3) ((mk fun n => (A005517 (n + 1) : ℚ)) * (1 - 5 * (X : PowerSeries ℚ) ^ 3)) =
      (A005517 (d + 4) : ℚ) - 5 * (A005517 (d + 1) : ℚ) := by
  rw [coeff_lhs_split, coeff_mul_X_pow, coeff_mk]

private lemma coeff_rhs_eq (m : ℕ) :
    coeff m (1 + 2 * (X : PowerSeries ℚ) + 3 * (X : PowerSeries ℚ) ^ 2 - (X : PowerSeries ℚ) ^ 4) =
      (if m = 0 then (1 : ℚ) else 0) + (if m = 1 then (2 : ℚ) else 0) +
        (if m = 2 then (3 : ℚ) else 0) - (if m = 4 then (1 : ℚ) else 0) := by
  have hC2 : (2 : PowerSeries ℚ) = C (2 : ℚ) := by
    rw [← Nat.cast_ofNat, ← map_natCast (C (R := ℚ)), Nat.cast_ofNat]
  have hC3 : (3 : PowerSeries ℚ) = C (3 : ℚ) := by
    rw [← Nat.cast_ofNat, ← map_natCast (C (R := ℚ)), Nat.cast_ofNat]
  rw [map_sub, map_add, map_add, coeff_one, hC2, coeff_C_mul, coeff_X, hC3, coeff_C_mul,
    coeff_X_pow, coeff_X_pow]
  split_ifs <;> norm_num

theorem OMA.solution : type_of% @OMA.S_oeis_a005517.main := by
  ext m
  have h1 : A005517 1 = 1 := by simp [A005517]
  have h2 : A005517 2 = 2 := by simp [A005517]
  have h3 : A005517 3 = 3 := by simp [A005517]
  have h4 : A005517 4 = 5 := by simp [A005517]
  have h5 : A005517 5 = 9 := by simp [A005517]
  rcases m with _ | _ | _ | _ | _ | k
  · rw [coeff_lhs_lt (by omega), coeff_rhs_eq]
    norm_num [h1]
  · rw [coeff_lhs_lt (by omega), coeff_rhs_eq]
    norm_num [h2]
  · rw [coeff_lhs_lt (by omega), coeff_rhs_eq]
    norm_num [h3]
  · change coeff (0 + 3) _ = coeff 3 _
    rw [coeff_lhs_ge 0, coeff_rhs_eq]
    norm_num [h4, h1]
  · change coeff (1 + 3) _ = coeff 4 _
    rw [coeff_lhs_ge 1, coeff_rhs_eq]
    norm_num [h5, h2]
  · rw [show k + 5 = (k + 2) + 3 by omega, coeff_lhs_ge (k + 2), coeff_rhs_eq]
    have hr := A005517_recur k
    have hq : (A005517 (k + 6) : ℚ) = 5 * (A005517 (k + 3) : ℚ) := by exact_mod_cast hr
    rw [show k + 2 + 4 = k + 6 by omega, show k + 2 + 1 = k + 3 by omega, hq, sub_self]
    have hne0 : k + 5 ≠ 0 := by omega
    have hne1 : k + 5 ≠ 1 := by omega
    have hne2 : k + 5 ≠ 2 := by omega
    have hne4 : k + 5 ≠ 4 := by omega
    simp only [hne0, hne1, hne2, hne4, ↓reduceIte]
    norm_num
