import OMAStatements.S_oeis_a152260
import Mathlib

open OMA.S_oeis_a152260 PowerSeries Finset

namespace P152260

lemma s2_zero_right (n : ℕ) : stirling2 (n + 1) 0 = 0 := rfl

lemma s2_succ (n k : ℕ) : stirling2 (n + 1) (k + 1) = (k + 1) * stirling2 n (k + 1) + stirling2 n k := rfl

lemma s2_gt : ∀ n k : ℕ, n < k → stirling2 n k = 0
  | 0, k + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [s2_succ, s2_gt n (k + 1) (by omega), s2_gt n k (by omega)]
    simp

lemma s2_n0 (n : ℕ) (hn : 1 ≤ n) : stirling2 n 0 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

lemma chj (j k : ℕ) : j.choose k * j = k * j.choose k + (k + 1) * j.choose (k + 1) := by
  have h := Nat.choose_succ_right_eq j k
  by_cases hk : k ≤ j
  · rw [mul_comm (k + 1), h]
    calc j.choose k * j = j.choose k * (k + (j - k)) := by rw [Nat.add_sub_cancel' hk]
      _ = _ := by ring
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    ring

lemma stir (n j : ℕ) : j ^ n = ∑ k ∈ range (n + 1), stirling2 n k * k.factorial * j.choose k := by
  induction n with
  | zero => simp [stirling2]
  | succ n ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    have e1 : ∀ k ∈ range (n + 1), stirling2 n k * k.factorial * j.choose k * j =
        stirling2 n k * k.factorial * k * j.choose k + stirling2 n k * (k + 1).factorial * j.choose (k + 1) := by
      intro k _
      rw [mul_assoc, chj, Nat.factorial_succ]
      ring
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun k => stirling2 (n + 1) k * k.factorial * j.choose k), s2_zero_right]
    simp only [s2_succ, zero_mul, add_zero]
    have e2 : ∀ k ∈ range (n + 1), ((k + 1) * stirling2 n (k + 1) + stirling2 n k) * (k + 1).factorial * j.choose (k + 1)
        = stirling2 n (k + 1) * (k + 1).factorial * (k + 1) * j.choose (k + 1) +
          stirling2 n k * (k + 1).factorial * j.choose (k + 1) := by
      intro k _; ring
    rw [Finset.sum_congr rfl e2, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_range_succ (fun k => stirling2 n (k + 1) * (k + 1).factorial * (k + 1) * j.choose (k + 1)),
      s2_gt n (n + 1) (by omega), Finset.sum_range_succ' (fun k => stirling2 n k * k.factorial * k * j.choose k)]
    simp

lemma chB (n k j : ℕ) (hn : 1 ≤ n) : (n + j - 1).choose j * j.choose k =
    (n - 1 + k).choose k * (if k ≤ j then (n - 1 + k + (j - k)).choose (n - 1 + k) else 0) := by
  by_cases hkj : k ≤ j
  · rw [if_pos hkj]
    obtain ⟨i, rfl⟩ : ∃ i, j = k + i := ⟨j - k, by omega⟩
    rw [Nat.choose_mul (show k ≤ k + i by omega), show n + (k + i) - 1 = n - 1 + k + i by omega,
      show k + i - k = i by omega, show n - 1 + k + i - k = n - 1 + i by omega]
    have h2 := Nat.choose_mul (n := n - 1 + k + i) (k := n - 1 + k) (s := k) (by omega)
    rw [show n - 1 + k + i - k = n - 1 + i by omega, show n - 1 + k - k = n - 1 by omega] at h2
    rw [mul_comm ((n - 1 + k).choose k), h2, Nat.choose_symm_add (a := n - 1) (b := i)]
  · rw [if_neg hkj, Nat.choose_eq_zero_of_lt (show j < k by omega)]
    simp

lemma serB (n k : ℕ) (hn : 1 ≤ n) :
    (PowerSeries.mk fun j => (((n + j - 1).choose j * j.choose k : ℕ) : ℚ)) =
      C (((n - 1 + k).choose k : ℕ) : ℚ) * (X ^ k * PowerSeries.mk fun i => (((n - 1 + k + i).choose (n - 1 + k) : ℕ) : ℚ)) := by
  ext j
  rw [coeff_mk, coeff_C_mul, coeff_X_pow_mul', chB n k j hn]
  split_ifs with h
  · rw [coeff_mk]; push_cast; ring
  · simp

lemma prodB (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    (1 - X : ℚ⟦X⟧) ^ (2 * n) * (PowerSeries.mk fun j => (((n + j - 1).choose j * j.choose k : ℕ) : ℚ)) =
      C (((n - 1 + k).choose k : ℕ) : ℚ) * (X ^ k * (1 - X) ^ (n - k)) := by
  rw [serB n k hn, show 2 * n = (n - k) + (n - 1 + k + 1) by omega, pow_add]
  have h1 := mk_add_choose_mul_one_sub_pow_eq_one (S := ℚ) (d := n - 1 + k)
  have h1' : (PowerSeries.mk fun i => (((n - 1 + k + i).choose (n - 1 + k) : ℕ) : ℚ)) * (1 - X) ^ (n - 1 + k + 1) = 1 := h1
  calc _ = C (((n - 1 + k).choose k : ℕ) : ℚ) * (X ^ k * (1 - X) ^ (n - k)) *
        ((PowerSeries.mk fun i => (((n - 1 + k + i).choose (n - 1 + k) : ℕ) : ℚ)) * (1 - X) ^ (n - 1 + k + 1)) := by ring
    _ = _ := by rw [h1', mul_one]

lemma coeff_osp (r i : ℕ) : coeff i ((1 - X : ℚ⟦X⟧) ^ r) = (-1) ^ i * (r.choose i : ℚ) := by
  rw [show (1 - X : ℚ⟦X⟧) = -X + 1 by ring, add_pow]
  have e : ∀ j ∈ range (r + 1), (-X : ℚ⟦X⟧) ^ j * 1 ^ (r - j) * (r.choose j : ℚ⟦X⟧) =
      C ((-1) ^ j * (r.choose j : ℚ)) * X ^ j := by
    intro j _
    rw [one_pow, mul_one, neg_pow, map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [Finset.sum_congr rfl e, map_sum]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range] at h
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

end P152260

open P152260 in
theorem OMA.solution : type_of% @OMA.S_oeis_a152260.main := by
  intro n m hn hm1 hmn
  have hser : (PowerSeries.mk fun j => (Nat.choose (n + j - 1) j : ℚ) * (j : ℚ) ^ n) =
      ∑ k ∈ range (n + 1), C ((stirling2 n k * k.factorial : ℕ) : ℚ) *
        PowerSeries.mk fun j => (((n + j - 1).choose j * j.choose k : ℕ) : ℚ) := by
    ext j
    rw [coeff_mk, map_sum]
    simp only [coeff_C_mul, coeff_mk]
    rw [show ((j : ℚ)) ^ n = ((j ^ n : ℕ) : ℚ) by push_cast; rfl, stir n j]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  unfold a152260 a152260Series
  rw [hser, mul_assoc, Finset.mul_sum]
  have e : ∀ k ∈ range (n + 1), (1 - X : ℚ⟦X⟧) ^ (2 * n) * (C ((stirling2 n k * k.factorial : ℕ) : ℚ) *
        PowerSeries.mk fun j => (((n + j - 1).choose j * j.choose k : ℕ) : ℚ)) =
      C ((stirling2 n k * k.factorial : ℕ) : ℚ) * (C (((n - 1 + k).choose k : ℕ) : ℚ) * (X ^ k * (1 - X) ^ (n - k))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [mul_left_comm, prodB n k hn (by omega)]
  rw [Finset.sum_congr rfl e, coeff_C_mul, map_sum]
  simp only [coeff_C_mul, coeff_X_pow_mul', coeff_osp]
  rw [Finset.mul_sum]
  rw [← Finset.sum_subset (s₁ := Icc 1 m) (s₂ := range (n + 1))]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    rw [if_pos hk.2]
    have hcb : ((n + k).choose k : ℚ) * n = ((n + k : ℕ) : ℚ) * ((n - 1 + k).choose k : ℚ) := by
      have := Nat.choose_mul_succ_eq (n - 1 + k) k
      rw [show n - 1 + k + 1 = n + k by omega, show n + k - k = n by omega] at this
      exact_mod_cast (by rw [← this]; ring : (n + k).choose k * n = (n + k) * (n - 1 + k).choose k)
    have hn0 : (n : ℚ) ≠ 0 := by positivity
    have hnk : ((n + k : ℕ) : ℚ) ≠ 0 := by positivity
    have : ((n + k).choose k : ℚ) = ((n + k : ℕ) : ℚ) * ((n - 1 + k).choose k : ℚ) / n := by
      field_simp; linarith [hcb]
    rw [this]
    push_cast
    field_simp
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    omega
  · intro k _ hk
    rw [Finset.mem_Icc] at hk
    by_cases h0 : k = 0
    · subst h0
      rw [s2_n0 n hn]
      simp
    · rw [if_neg (by omega)]
      simp
