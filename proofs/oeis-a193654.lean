import OMAStatements.S_oeis_a193654
import Mathlib

namespace OMA.S_oeis_a193654

lemma r_cast (j : ℕ) : (r j : ℤ) = if j = 0 then 1 else 2 ^ (j - 1) := by
  unfold r; split_ifs <;> simp

lemma S0 (n : ℕ) : ∑ j ∈ Finset.range (n + 1), (r j : ℤ) = 2 ^ n := by
  induction n with
  | zero => simp [r]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, r_cast]; simp; ring

lemma S1 (n : ℕ) : ∑ j ∈ Finset.range (n + 1), (j : ℤ) * (r j : ℤ) = ((n : ℤ) - 1) * 2 ^ n + 1 := by
  induction n with
  | zero => simp [r]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, r_cast]; simp; ring

lemma SU (n : ℕ) : 3 * ∑ j ∈ Finset.range (n + 1), ((j % 2 : ℕ) : ℤ) * (r j : ℤ) + 1 = 4 ^ ((n + 1) / 2) := by
  induction n with
  | zero => simp [r]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, add_right_comm, ih, r_cast]
    rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
    · have e1 : (2 * t + 1 + 1) / 2 = t + 1 := by omega
      have e2 : (2 * t + 1) / 2 = t := by omega
      have e3 : (2 * t + 1) % 2 = 1 := by omega
      rw [e1, e2, e3]
      simp
      have h4 : (2:ℤ) ^ (2 * t) = 4 ^ t := by rw [pow_mul]; norm_num
      rw [h4]; ring
    · have e1 : (2 * t + 1 + 1 + 1) / 2 = t + 1 := by omega
      have e2 : (2 * t + 1 + 1) / 2 = t + 1 := by omega
      have e3 : (2 * t + 1 + 1) % 2 = 0 := by omega
      rw [e1, e2, e3]; simp

lemma two_a (n : ℕ) : 2 * (a n : ℤ) =
    ((n : ℤ) + 1) * (2 * n + 2) * 2 ^ n - ((n : ℤ) + 1) * (((n : ℤ) - 1) * 2 ^ n + 1) -
      (if n % 2 = 0 then ∑ j ∈ Finset.range (n + 1), ((j % 2 : ℕ) : ℤ) * (r j : ℤ) else 0) := by
  have h1 : (a n : ℤ) = ∑ j ∈ Finset.range (n + 1), (((n + 1) * (2 * n + 2 - j) / 2 : ℕ) : ℤ) * (r j : ℤ) := by
    unfold a
    simp only [Nat.cast_sum, Nat.cast_mul]
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < n + 1 := Finset.mem_range.mp hj
    have : n + 1 - 1 - j = n - j := by omega
    rw [this]
    have e : p n (n - j) = (n + 1) * (2 * n + 2 - j) / 2 := by
      unfold p
      have e : n + (n - j) + 2 = 2 * n + 2 - j := by omega
      rw [e]
    have e2 : n - (n - j) = j := by omega
    rw [e, e2]
  have h2 : ∀ j ∈ Finset.range (n + 1), 2 * ((((n + 1) * (2 * n + 2 - j) / 2 : ℕ) : ℤ) * (r j : ℤ)) =
      (((n : ℤ) + 1) * (2 * n + 2) - ((n : ℤ) + 1) * j - (if n % 2 = 0 then ((j % 2 : ℕ) : ℤ) else 0)) * (r j : ℤ) := by
    intro j hj
    have hj' : j < n + 1 := Finset.mem_range.mp hj
    have hdm := Nat.div_add_mod ((n + 1) * (2 * n + 2 - j)) 2
    have hsum : (n + 1) * (2 * n + 2 - j) + (n + 1) * j = 2 * ((n + 1) * (n + 1)) := by
      have : 2 * n + 2 - j + j = 2 * n + 2 := by omega
      calc (n + 1) * (2 * n + 2 - j) + (n + 1) * j = (n + 1) * (2 * n + 2 - j + j) := by ring
        _ = _ := by rw [this]; ring
    have hmod : ((n + 1) * (2 * n + 2 - j)) % 2 = ((n + 1) * j) % 2 := by omega
    have hmod2 : ((n + 1) * j) % 2 = if n % 2 = 0 then j % 2 else 0 := by
      rw [Nat.mul_mod]
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · simp [h, Nat.add_mod]
      · simp [h, Nat.add_mod]
    have hz : (((n + 1) * (2 * n + 2 - j) : ℕ) : ℤ) = ((n : ℤ) + 1) * (2 * n + 2 - j) := by
      push_cast [Nat.cast_sub (show j ≤ 2 * n + 2 by omega)]; ring
    have key : 2 * ((((n + 1) * (2 * n + 2 - j) / 2 : ℕ)) : ℤ) =
        ((n : ℤ) + 1) * (2 * n + 2 - j) - (if n % 2 = 0 then ((j % 2 : ℕ) : ℤ) else 0) := by
      have h3 : (((n + 1) * (2 * n + 2 - j) % 2 : ℕ) : ℤ) = (if n % 2 = 0 then ((j % 2 : ℕ) : ℤ) else 0) := by
        rw [hmod, hmod2]; split_ifs <;> simp
      have h4 : (2 * ((n + 1) * (2 * n + 2 - j) / 2 : ℕ) : ℤ) + (((n + 1) * (2 * n + 2 - j) % 2 : ℕ) : ℤ) = (((n + 1) * (2 * n + 2 - j) : ℕ) : ℤ) := by
        exact_mod_cast hdm
      rw [hz, h3] at h4
      linarith
    rw [← mul_assoc, key]; ring
  rw [h1, Finset.mul_sum, Finset.sum_congr rfl h2]
  by_cases h : n % 2 = 0
  · simp only [if_pos h, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rw [S0, S1]; ring
  · simp only [if_neg h, sub_zero, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rw [S0, S1]; ring


lemma six_even (s : ℕ) : 6 * (a (2 * s) : ℤ) =
    3 * ((2 * (s : ℤ) + 1) * (4 * s + 2) * 4 ^ s - (2 * (s : ℤ) + 1) * ((2 * (s : ℤ) - 1) * 4 ^ s + 1)) - (4 ^ s - 1) := by
  have h := two_a (2 * s)
  have hu := SU (2 * s)
  have e1 : (2 * s + 1) / 2 = s := by omega
  rw [e1] at hu
  have h2 : (2:ℤ) ^ (2 * s) = 4 ^ s := by rw [pow_mul]; norm_num
  rw [if_pos (by omega), h2] at h
  have hc : ((2 * s : ℕ) : ℤ) = 2 * s := by push_cast; ring
  rw [hc] at h
  linarith

lemma six_odd (s : ℕ) : 6 * (a (2 * s + 1) : ℤ) =
    3 * ((2 * (s : ℤ) + 2) * (4 * s + 4) * (2 * 4 ^ s) - (2 * (s : ℤ) + 2) * ((2 * (s : ℤ)) * (2 * 4 ^ s) + 1)) := by
  have h := two_a (2 * s + 1)
  have h2 : (2:ℤ) ^ (2 * s + 1) = 2 * 4 ^ s := by rw [pow_succ, pow_mul]; norm_num; ring
  rw [if_neg (by omega), h2] at h
  push_cast at h
  linarith

lemma rec_even (u : ℕ) : -1 * (a (2 * (u + 3) + 1) : ℤ) + 5 * a (2 * (u + 3)) - 3 * a (2 * (u + 2) + 1) - 21 * a (2 * (u + 2))
    + 36 * a (2 * (u + 1) + 1) + 0 * a (2 * (u + 1)) - 32 * a (2 * u + 1) + 16 * a (2 * u) = 0 := by
  have h0 := six_odd (u + 3)
  have h1 := six_even (u + 3)
  have h2 := six_odd (u + 2)
  have h3 := six_even (u + 2)
  have h4 := six_odd (u + 1)
  have h5 := six_even (u + 1)
  have h6 := six_odd u
  have h7 := six_even u
  push_cast at *
  have : 6 * (-1 * (a (2 * (u + 3) + 1) : ℤ) + 5 * a (2 * (u + 3)) - 3 * a (2 * (u + 2) + 1) - 21 * a (2 * (u + 2))
    + 36 * a (2 * (u + 1) + 1) + 0 * a (2 * (u + 1)) - 32 * a (2 * u + 1) + 16 * a (2 * u)) = 0 := by
    linear_combination (-1) * h0 + 5 * h1 - 3 * h2 - 21 * h3 + 36 * h4 + 0 * h5 - 32 * h6 + 16 * h7
  omega

lemma rec_odd (u : ℕ) : -1 * (a (2 * (u + 4)) : ℤ) + 5 * a (2 * (u + 3) + 1) - 3 * a (2 * (u + 3)) - 21 * a (2 * (u + 2) + 1)
    + 36 * a (2 * (u + 2)) + 0 * a (2 * (u + 1) + 1) - 32 * a (2 * (u + 1)) + 16 * a (2 * u + 1) = 0 := by
  have h0 := six_even (u + 4)
  have h1 := six_odd (u + 3)
  have h2 := six_even (u + 3)
  have h3 := six_odd (u + 2)
  have h4 := six_even (u + 2)
  have h5 := six_odd (u + 1)
  have h6 := six_even (u + 1)
  have h7 := six_odd u
  push_cast at *
  have : 6 * (-1 * (a (2 * (u + 4)) : ℤ) + 5 * a (2 * (u + 3) + 1) - 3 * a (2 * (u + 3)) - 21 * a (2 * (u + 2) + 1)
    + 36 * a (2 * (u + 2)) + 0 * a (2 * (u + 1) + 1) - 32 * a (2 * (u + 1)) + 16 * a (2 * u + 1)) = 0 := by
    linear_combination (-1) * h0 + 5 * h1 - 3 * h2 - 21 * h3 + 36 * h4 + 0 * h5 - 32 * h6 + 16 * h7
  omega

lemma rec (m : ℕ) : -1 * (a (m + 7) : ℤ) + 5 * a (m + 6) - 3 * a (m + 5) - 21 * a (m + 4) + 36 * a (m + 3)
    + 0 * a (m + 2) - 32 * a (m + 1) + 16 * a m = 0 := by
  rcases Nat.even_or_odd' m with ⟨u, rfl | rfl⟩
  · have := rec_even u
    have e : ∀ x y : ℕ, x = y → (a x : ℤ) = a y := fun x y h => by rw [h]
    rw [e (2 * u + 7) (2 * (u + 3) + 1) (by ring), e (2 * u + 6) (2 * (u + 3)) (by ring),
      e (2 * u + 5) (2 * (u + 2) + 1) (by ring), e (2 * u + 4) (2 * (u + 2)) (by ring),
      e (2 * u + 3) (2 * (u + 1) + 1) (by ring), e (2 * u + 2) (2 * (u + 1)) (by ring),
      e (2 * u + 1) (2 * u + 1) rfl]
    exact this
  · have := rec_odd u
    have e : ∀ x y : ℕ, x = y → (a x : ℤ) = a y := fun x y h => by rw [h]
    rw [e (2 * u + 1 + 7) (2 * (u + 4)) (by ring), e (2 * u + 1 + 6) (2 * (u + 3) + 1) (by ring),
      e (2 * u + 1 + 5) (2 * (u + 3)) (by ring), e (2 * u + 1 + 4) (2 * (u + 2) + 1) (by ring),
      e (2 * u + 1 + 3) (2 * (u + 2)) (by ring), e (2 * u + 1 + 2) (2 * (u + 1) + 1) (by ring),
      e (2 * u + 1 + 1) (2 * (u + 1)) (by ring)]
    exact this

lemma a0 : a 0 = 1 := by decide +kernel
lemma a1 : a 1 = 7 := by decide +kernel
lemma a2 : a 2 = 28 := by decide +kernel
lemma a3 : a 3 = 94 := by decide +kernel
lemma a4 : a 4 = 275 := by decide +kernel
lemma a5 : a 5 = 765 := by decide +kernel
lemma a6 : a 6 = 2002 := by decide +kernel

theorem sol : PowerSeries.mk (fun n => (a n : ℚ)) *
    ((1 + PowerSeries.X) * (2 * PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 2 *
      (2 * PowerSeries.X - 1) ^ 3) =
    -1 - 2 * PowerSeries.X + 4 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 -
      8 * PowerSeries.X ^ 5 := by
  open PowerSeries in
  have hX : (PowerSeries.mk fun n => (a n : ℚ)) * ((1 + X) * (2 * X + 1) * (X - 1) ^ 2 * (2 * X - 1) ^ 3) =
      C (-1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 0) + C (5 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
      + C (-3 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) + C (-21 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
      + C (36 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4) + C (-32 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 6)
      + C (16 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 7) := by
    simp only [map_neg, map_ofNat, map_one]
    ring
  have hR : (-1 - 2 * X + 4 * X ^ 2 + 4 * X ^ 3 - 8 * X ^ 5 : PowerSeries ℚ) =
      C (-1 : ℚ) * X ^ 0 + C (-2 : ℚ) * X ^ 1 + C (4 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 3 + C (-8 : ℚ) * X ^ 5 := by
    simp only [map_neg, map_ofNat, map_one]
    ring
  rw [hX, hR]
  open PowerSeries in
  ext k
  open PowerSeries in
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  rcases k with _ | _ | _ | _ | _ | _ | _ | m
  · simp [a0, coeff_X_pow, coeff_one]
  · simp [a0, a1, coeff_X_pow, coeff_one]; norm_num
  · simp [a0, a1, a2, coeff_X_pow, coeff_one]; norm_num
  · simp [a0, a1, a2, a3, coeff_X_pow, coeff_one]; norm_num
  · simp [a0, a1, a2, a3, a4, coeff_X_pow, coeff_one]; norm_num
  · simp [a0, a1, a2, a3, a4, a5, coeff_X_pow, coeff_one]; norm_num
  · simp [a0, a1, a2, a3, a4, a5, a6, coeff_X_pow, coeff_one]; norm_num
  · have h := rec m
    have hq : (-1 : ℚ) * (a (m + 7) : ℚ) + 5 * a (m + 6) - 3 * a (m + 5) - 21 * a (m + 4) + 36 * a (m + 3)
      + 0 * a (m + 2) - 32 * a (m + 1) + 16 * a m = 0 := by exact_mod_cast h
    simp [coeff_X_pow]
    have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 = m + 7 := by ring
    have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 = m + 6 := by ring
    rw [e7, e6]
    linarith

end OMA.S_oeis_a193654
theorem OMA.solution : type_of% @OMA.S_oeis_a193654.main := OMA.S_oeis_a193654.sol
