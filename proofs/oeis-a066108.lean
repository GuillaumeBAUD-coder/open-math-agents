import OMAStatements.S_oeis_a066108
import Mathlib

open OMA.S_oeis_a066108 PowerSeries Finset

namespace P066108

lemma vanish (m q : ℕ) (hq : m + 1 ≤ q) :
    ∑ j ∈ range (m + 2), (-1 : ℚ) ^ j * ((m + 1).choose j : ℚ) * ((q - j : ℕ) : ℚ) ^ m = 0 := by
  have h := congr_fun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℚ) (Nat.lt_succ_self m)) ((q : ℚ) - (m + 1))
  rw [fwdDiff_iter_eq_sum_shift] at h
  simp only [Pi.zero_apply] at h
  rw [← h]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Nat.succ_eq_add_one, Finset.mem_range] at hj ⊢
  rw [zsmul_eq_mul, nsmul_eq_mul, mul_one, show m + 1 + 1 - 1 - j = m + 1 - j by omega,
    Nat.choose_symm (by omega), show m + 1 - (m + 1 - j) = j by omega]
  push_cast
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

lemma Dq (m q : ℕ) (hm : 1 ≤ m) :
    ∑ j ∈ range (m + 2), (-1 : ℚ) ^ j * ((m + 1).choose j : ℚ) *
      (if j ≤ q then ((q - j : ℕ) : ℚ) ^ m else 0) = if 1 ≤ q ∧ q ≤ m then eulerian m q else 0 := by
  by_cases hq : m + 1 ≤ q
  · rw [if_neg (by omega), ← vanish m q hq]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [if_pos (by omega)]
  · rw [← Finset.sum_range_add_sum_Ico _ (show q + 1 ≤ m + 2 by omega)]
    rw [Finset.sum_eq_zero (s := Ico (q + 1) (m + 2)) (fun j hj => by
      rw [Finset.mem_Ico] at hj; rw [if_neg (by omega), mul_zero]), add_zero]
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0
      rw [if_neg (by omega)]
      simp [zero_pow (show m ≠ 0 by omega)]
    · rw [if_pos (by omega), eulerian]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [if_pos (by omega)]
      ring

def g (m : ℕ) : ℕ → ℚ := fun n => if m ∣ n then (n : ℚ) ^ m else 0

lemma binom (m : ℕ) : ((1 : PowerSeries ℚ) - X ^ m) ^ (m + 1) =
    ∑ j ∈ range (m + 2), C ((-1 : ℚ) ^ j * ((m + 1).choose j : ℚ)) * X ^ (j * m) := by
  rw [show (1 : PowerSeries ℚ) - X ^ m = -X ^ m + 1 by ring, add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [one_pow, mul_one, map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [neg_pow, ← pow_mul, mul_comm m j]
  ring

lemma cL (f : ℕ → ℚ) (c : ℚ) (k N : ℕ) :
    coeff N (mk f * (C c * X ^ k)) = if k ≤ N then f (N - k) * c else 0 := by
  rw [← mul_assoc, coeff_mul_X_pow', coeff_mul_C, coeff_mk]

lemma cR (a e : ℚ) (k N : ℕ) : coeff N (C a * (C e * X ^ k)) = a * (if N = k then e else 0) := by
  rw [coeff_C_mul, coeff_C_mul_X_pow]

lemma T (m : ℕ) (hm : 1 ≤ m) : a066108Term m = mk (g m) := by
  unfold a066108Term
  symm
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp [zero_pow (show m ≠ 0 by omega)])]
  rw [binom, Finset.mul_sum, Finset.mul_sum]
  ext N
  simp only [map_sum, cL, cR]
  rw [← Finset.mul_sum]
  by_cases hd : m ∣ N
  · obtain ⟨q, rfl⟩ := hd
    have e1 : ∀ k ∈ Icc 1 m, (if m * q = k * m then eulerian m k else 0) = if q = k then eulerian m k else 0 := by
      intro k _
      have : m * q = k * m ↔ q = k := by
        rw [mul_comm k m]; exact Nat.mul_right_inj (by omega)
      simp only [this]
    rw [Finset.sum_congr rfl e1, Finset.sum_ite_eq]
    have e2 : ∀ j ∈ range (m + 2), (if j * m ≤ m * q then g m (m * q - j * m) * ((-1 : ℚ) ^ j * ((m + 1).choose j : ℚ)) else 0)
        = (m : ℚ) ^ m * ((-1 : ℚ) ^ j * ((m + 1).choose j : ℚ) * (if j ≤ q then ((q - j : ℕ) : ℚ) ^ m else 0)) := by
      intro j _
      by_cases hj : j ≤ q
      · rw [if_pos (by rw [mul_comm m q]; exact Nat.mul_le_mul_right m hj), if_pos hj, g,
          if_pos ⟨q - j, by rw [Nat.mul_sub, mul_comm j m]⟩,
          show m * q - j * m = m * (q - j) by rw [Nat.mul_sub, mul_comm j m]]
        push_cast
        ring
      · rw [if_neg (by rw [mul_comm m q]; intro h; exact hj (Nat.le_of_mul_le_mul_right h (by omega))),
          if_neg hj]
        ring
    rw [Finset.sum_congr rfl e2, ← Finset.mul_sum, Dq m q hm]
    simp only [Finset.mem_Icc]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero (s := Icc 1 m), mul_zero]
    · intro k _
      rw [if_neg]
      rintro rfl
      exact hd ⟨k, by ring⟩
    · intro j _
      by_cases h1 : j * m ≤ N
      · rw [if_pos h1, g, if_neg, zero_mul]
        intro h2
        apply hd
        have : m ∣ N - j * m + j * m := Nat.dvd_add h2 ⟨j, by ring⟩
        rwa [Nat.sub_add_cancel h1] at this
      · rw [if_neg h1]

end P066108

open P066108 in
theorem OMA.solution : type_of% @OMA.S_oeis_a066108.main := by
  intro n M hnM
  rw [map_sum]
  have e : ∀ m ∈ Icc 1 M, coeff n (a066108Term m) = if m ∣ n then (n : ℚ) ^ m else 0 := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [T m hm.1, coeff_mk, g]
  rw [Finset.sum_congr rfl e, ← Finset.sum_filter]
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    rw [a066108, if_pos rfl, Nat.cast_zero]
    refine Finset.sum_eq_zero fun m hm => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    simp [zero_pow (show m ≠ 0 by omega)]
  · have hs : (Icc 1 M).filter (· ∣ n) = n.divisors := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨_, hd⟩; exact ⟨hd, by omega⟩
      · rintro ⟨hd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd h0, (Nat.le_of_dvd h0 hd).trans hnM⟩, hd⟩
    rw [hs, a066108, if_neg (by omega)]
    push_cast
    rfl
