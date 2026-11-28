import OMAStatements.S_oeis_a024219
import Mathlib

namespace A024219
open OMA.S_oeis_a024219

lemma floor_val (n : ℕ) (hn : 1 ≤ n) (z : ℤ) (c : ℚ) (hc : c = 2 ∨ c = 4)
    (hz : 4 * (z : ℚ) = 3 * (n : ℚ) ^ 2 + n - c) : a n = z := by
  unfold a
  have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℚ) < 4 * (3 * (n : ℚ) + 2) := by positivity
  have hz' : (z : ℚ) = (3 * (n : ℚ) ^ 2 + n - c) / 4 := by linarith
  rw [Int.floor_eq_iff, le_div_iff₀ hpos, div_lt_iff₀ hpos, hz']
  rcases hc with rfl | rfl
  · constructor <;> nlinarith
  · constructor <;> nlinarith

def cc (n : ℕ) : ℤ := if n % 4 < 2 then 4 else 2

lemma cc_rec (m : ℕ) :
    cc (m + 6) - 3 * cc (m + 5) + 4 * cc (m + 4) - 4 * cc (m + 3) + 3 * cc (m + 2) -
      cc (m + 1) = 0 := by
  unfold cc
  split_ifs <;> omega

lemma four_a (n : ℕ) (hn : 1 ≤ n) : 4 * a n = 3 * (n : ℤ) ^ 2 + n - cc n := by
  unfold cc
  obtain ⟨k, hk⟩ : ∃ k, n = 4 * k + n % 4 := ⟨n / 4, by omega⟩
  have hr : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize n % 4 = r at hk hr
  interval_cases r
  · have h := floor_val n hn (12 * (k : ℤ) ^ 2 + k - 1) 4 (Or.inr rfl)
      (by rw [hk]; push_cast; ring)
    rw [h, hk]
    push_cast
    ring
  · have h := floor_val n hn (12 * (k : ℤ) ^ 2 + 7 * k) 4 (Or.inr rfl)
      (by rw [hk]; push_cast; ring)
    rw [h, hk]
    push_cast
    ring
  · have h := floor_val n hn (12 * (k : ℤ) ^ 2 + 13 * k + 3) 2 (Or.inl rfl)
      (by rw [hk]; push_cast; ring)
    rw [h, hk]
    push_cast
    ring
  · have h := floor_val n hn (12 * (k : ℤ) ^ 2 + 19 * k + 7) 2 (Or.inl rfl)
      (by rw [hk]; push_cast; ring)
    rw [h, hk]
    push_cast
    ring

lemma rec_shift (m : ℕ) :
    a (m + 6) - 3 * a (m + 5) + 4 * a (m + 4) - 4 * a (m + 3) + 3 * a (m + 2) - a (m + 1) = 0 := by
  have h0 := four_a (m + 6) (by omega)
  have h1 := four_a (m + 5) (by omega)
  have h2 := four_a (m + 4) (by omega)
  have h3 := four_a (m + 3) (by omega)
  have h4 := four_a (m + 2) (by omega)
  have h5 := four_a (m + 1) (by omega)
  have hc := cc_rec m
  push_cast at h0 h1 h2 h3 h4 h5
  linarith

lemma a0 : a 0 = 0 := by
  unfold a
  norm_num

lemma a1 : a 1 = 0 := floor_val 1 (by norm_num) 0 4 (Or.inr rfl) (by norm_num)
lemma a2 : a 2 = 3 := floor_val 2 (by norm_num) 3 2 (Or.inl rfl) (by norm_num)
lemma a3 : a 3 = 7 := floor_val 3 (by norm_num) 7 2 (Or.inl rfl) (by norm_num)
lemma a4 : a 4 = 12 := floor_val 4 (by norm_num) 12 4 (Or.inr rfl) (by norm_num)
lemma a5 : a 5 = 19 := floor_val 5 (by norm_num) 19 4 (Or.inr rfl) (by norm_num)

lemma coeff_F_mul_X (k n : ℕ) :
    PowerSeries.coeff n (F * PowerSeries.X ^ k) = if k ≤ n then a (n - k) else 0 := by
  simp only [PowerSeries.coeff_mul_X_pow', F, PowerSeries.coeff_mk]

lemma coeff_lhs (n : ℕ) :
    PowerSeries.coeff n ((1 + PowerSeries.X ^ 2) * (1 - PowerSeries.X) ^ 3 * F) =
      a n - 3 * (if 1 ≤ n then a (n - 1) else 0) + 4 * (if 2 ≤ n then a (n - 2) else 0) -
        4 * (if 3 ≤ n then a (n - 3) else 0) + 3 * (if 4 ≤ n then a (n - 4) else 0) -
        (if 5 ≤ n then a (n - 5) else 0) := by
  have expand : (1 + PowerSeries.X ^ 2) * (1 - PowerSeries.X) ^ 3 * F =
      F - PowerSeries.C 3 * (F * PowerSeries.X ^ 1) + PowerSeries.C 4 * (F * PowerSeries.X ^ 2) -
        PowerSeries.C 4 * (F * PowerSeries.X ^ 3) + PowerSeries.C 3 * (F * PowerSeries.X ^ 4) -
        F * PowerSeries.X ^ 5 := by
    simp only [map_ofNat, pow_one]
    ring
  rw [expand]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_F_mul_X]
  simp only [F, PowerSeries.coeff_mk]

lemma coeff_rhs (n : ℕ) :
    PowerSeries.coeff n ((3 : PowerSeries ℤ) * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 +
        3 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5) =
      3 * (if n = 2 then 1 else 0) - 2 * (if n = 3 then 1 else 0) +
        3 * (if n = 4 then 1 else 0) - (if n = 5 then 1 else 0) := by
  have expand : ((3 : PowerSeries ℤ) * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 +
        3 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5) =
      PowerSeries.C 3 * PowerSeries.X ^ 2 - PowerSeries.C 2 * PowerSeries.X ^ 3 +
        PowerSeries.C 3 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5 := by
    simp only [map_ofNat]
  rw [expand]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

end A024219

theorem OMA.solution : type_of% @OMA.S_oeis_a024219.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    have e1 : m + 6 - 1 = m + 5 := by omega
    have e2 : m + 6 - 2 = m + 4 := by omega
    have e3 : m + 6 - 3 = m + 3 := by omega
    have e4 : m + 6 - 4 = m + 2 := by omega
    have e5 : m + 6 - 5 = m + 1 := by omega
    rw [e1, e2, e3, e4, e5]
    exact A024219.rec_shift m
  · apply PowerSeries.ext
    intro n
    rw [A024219.coeff_lhs, A024219.coeff_rhs]
    by_cases hn : 6 ≤ n
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      have e1 : m + 6 - 1 = m + 5 := by omega
      have e2 : m + 6 - 2 = m + 4 := by omega
      have e3 : m + 6 - 3 = m + 3 := by omega
      have e4 : m + 6 - 4 = m + 2 := by omega
      have e5 : m + 6 - 5 = m + 1 := by omega
      have h := A024219.rec_shift m
      have c1 : 1 ≤ m + 6 := by omega
      have c2 : 2 ≤ m + 6 := by omega
      have c3 : 3 ≤ m + 6 := by omega
      have c4 : 4 ≤ m + 6 := by omega
      have c5 : 5 ≤ m + 6 := by omega
      have d2 : ¬ (m + 6 = 2) := by omega
      have d3 : ¬ (m + 6 = 3) := by omega
      have d4 : ¬ (m + 6 = 4) := by omega
      have d5 : ¬ (m + 6 = 5) := by omega
      rw [if_pos c1, if_pos c2, if_pos c3, if_pos c4, if_pos c5, if_neg d2, if_neg d3,
        if_neg d4, if_neg d5, e1, e2, e3, e4, e5]
      linarith
    · have hn' : n < 6 := by omega
      interval_cases n <;>
        norm_num [A024219.a0, A024219.a1, A024219.a2, A024219.a3, A024219.a4, A024219.a5]
