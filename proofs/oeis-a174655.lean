import OMAStatements.S_oeis_a174655
import Mathlib

namespace OMA.S_oeis_a174655

open Finset

lemma tail_closed (n : ℕ) : 2 * tail n = 21 + 16 * (n : ℤ) + 4 * (n : ℤ) ^ 2 - (-1 : ℤ) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [tail]
    | 1, _ => simp [tail]
    | 2, _ => simp [tail]
    | 3, _ => simp [tail]
    | m + 4, ih =>
      have h3 := ih (m + 3) (by omega)
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      have e : tail (m + 4) = 2 * tail (m + 3) - 2 * tail (m + 1) + tail m := rfl
      rw [e]
      push_cast at *
      have s3 : (-1 : ℤ) ^ (m + 3) = -(-1) ^ m := by ring
      have s1 : (-1 : ℤ) ^ (m + 1) = -(-1) ^ m := by ring
      have s4 : (-1 : ℤ) ^ (m + 4) = (-1) ^ m := by ring
      rw [s4]
      rw [s3] at h3
      rw [s1] at h1
      linear_combination 2 * h3 - 2 * h1 + h0

lemma a_succ (n : ℕ) : a (n + 1) = a n + b (n + 1) := by
  simp [a, Finset.sum_range_succ]

lemma a_closed (n : ℕ) : 12 * a (n + 2) =
    3 * (-9 + (-1 : ℤ) ^ (n + 2)) + 34 * ((n + 2 : ℕ) : ℤ) - 12 * ((n + 2 : ℕ) : ℤ) ^ 2
      + 8 * ((n + 2 : ℕ) : ℤ) ^ 3 := by
  induction n with
  | zero => simp [a, b, Finset.sum_range_succ]
  | succ k ih =>
    rw [a_succ (k + 2)]
    have hb : b (k + 3) = tail k := rfl
    have ht := tail_closed k
    rw [hb]
    push_cast at *
    have s : (-1 : ℤ) ^ (k + 1 + 2) = -(-1) ^ (k + 2) := by ring
    have s2 : (-1 : ℤ) ^ (k + 2) = (-1) ^ k := by ring
    rw [s, s2] at *
    linear_combination ih + 6 * ht


open PowerSeries in
set_option maxHeartbeats 2000000 in
lemma gf_part : ((X - 1) ^ 4 * (X + 1) * PowerSeries.mk a : ℤ⟦X⟧) = X * (X ^ 5 - X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 + 2 * X + 1) := by
  have h : ((X - 1) ^ 4 * (X + 1) * PowerSeries.mk a : ℤ⟦X⟧) =
      X ^ 5 * PowerSeries.mk a - C 3 * (X ^ 4 * PowerSeries.mk a) + C 2 * (X ^ 3 * PowerSeries.mk a) + C 2 * (X ^ 2 * PowerSeries.mk a)
        - C 3 * (X * PowerSeries.mk a) + PowerSeries.mk a := by
    have e3 : (C 3 : ℤ⟦X⟧) = 3 := by simp
    have e2 : (C 2 : ℤ⟦X⟧) = 2 := by simp
    rw [e3, e2]; ring
  rw [h]
  have hR : (X * (X ^ 5 - X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 + 2 * X + 1) : ℤ⟦X⟧) =
      X ^ 6 - X ^ 5 + C 3 * X ^ 4 + C 2 * X ^ 3 + C 2 * X ^ 2 + X := by
    have e3 : (C 3 : ℤ⟦X⟧) = 3 := by simp
    have e2 : (C 2 : ℤ⟦X⟧) = 2 := by simp
    rw [e3, e2]; ring
  rw [hR]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_X, PowerSeries.coeff_mk]
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp [a, b, tail, Finset.sum_range_succ]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have h5 : ¬ (m + 7 = 6) := by omega
    have h6 : ¬ (m + 7 = 5) := by omega
    have h7 : ¬ (m + 7 = 4) := by omega
    have h8 : ¬ (m + 7 = 3) := by omega
    have h9 : ¬ (m + 7 = 2) := by omega
    have h10 : ¬ (m + 7 = 1) := by omega
    simp only [if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10,
      show 5 ≤ m + 7 from by omega, show 4 ≤ m + 7 from by omega, show 3 ≤ m + 7 from by omega,
      show 2 ≤ m + 7 from by omega, show 1 ≤ m + 7 from by omega, if_true]
    have e5 : m + 7 - 5 = m + 2 := by omega
    have e4 : m + 7 - 4 = m + 3 := by omega
    have e3 : m + 7 - 3 = m + 4 := by omega
    have e2 : m + 7 - 2 = m + 5 := by omega
    have e1 : m + 7 - 1 = m + 6 := by omega
    have c0 := a_closed (m + 5)
    have c1 := a_closed (m + 4)
    have c2 := a_closed (m + 3)
    have c3 := a_closed (m + 2)
    have c4 := a_closed (m + 1)
    have c5 := a_closed m
    have ex : (PowerSeries.coeff (m + 7)) (X * PowerSeries.mk a : ℤ⟦X⟧) = a (m + 6) := by
      have := PowerSeries.coeff_succ_X_mul (m + 6) (PowerSeries.mk a : ℤ⟦X⟧)
      simpa using this
    rw [e5, e4, e3, e2, ex]
    have hs : ((-1 : ℤ) ^ m) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]; simp
    simp only [pow_add] at c0 c1 c2 c3 c4 c5
    push_cast at c0 c1 c2 c3 c4 c5
    have key : (12 : ℤ) * (a (m + 2) - 3 * a (m + 3) + 2 * a (m + 4) + 2 * a (m + 5)
        - 3 * a (m + 6) + a (m + 7)) = 12 * 0 := by
      linear_combination c5 - 3 * c4 + 2 * c3 + 2 * c2 - 3 * c1 + c0
    have := mul_left_cancel₀ (by norm_num : (12 : ℤ) ≠ 0) key
    simpa using this

end OMA.S_oeis_a174655

theorem OMA.solution : type_of% @OMA.S_oeis_a174655.main := by
  refine ⟨?_, OMA.S_oeis_a174655.gf_part⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact OMA.S_oeis_a174655.a_closed m
