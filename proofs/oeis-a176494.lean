import OMAStatements.S_oeis_a176494
import Mathlib

namespace OMA.S_oeis_a176494

lemma per_aux (q : ℤ) (P r : ℕ) (hP : q ∣ (2:ℤ) ^ P - 1) (hr : q ∣ (2:ℤ) ^ r - 7629217) (j : ℕ) :
    q ∣ (2:ℤ) ^ (P * j + r) - 7629217 := by
  have h1 : q ∣ ((2:ℤ) ^ P) ^ j - 1 := by
    have := sub_dvd_pow_sub_pow ((2:ℤ) ^ P) 1 j
    rw [one_pow] at this
    exact dvd_trans hP this
  have h2 : (2:ℤ) ^ (P * j + r) - 7629217 = (((2:ℤ) ^ P) ^ j - 1) * 2 ^ r + ((2:ℤ) ^ r - 7629217) := by
    rw [pow_add, pow_mul]; ring
  rw [h2]
  exact dvd_add (dvd_mul_of_dvd_left h1 _) hr

lemma cover (m : ℕ) : ∃ q : ℕ, q ∈ [3, 5, 7, 13, 17, 241] ∧ (q : ℤ) ∣ (2:ℤ) ^ m - 7629217 := by
  have hD : m % 2 = 0 ∨ m % 4 = 1 ∨ m % 3 = 0 ∨ m % 12 = 7 ∨ m % 8 = 3 ∨ m % 24 = 23 := by omega
  rcases hD with h | h | h | h | h | h
  · refine ⟨3, by simp, ?_⟩
    have := per_aux 3 2 0 (by norm_num) (by norm_num) (m / 2)
    have e : m = 2 * (m / 2) + 0 := by omega
    rw [e]; simpa using this
  · refine ⟨5, by simp, ?_⟩
    have := per_aux 5 4 1 (by norm_num) (by norm_num) (m / 4)
    have e : m = 4 * (m / 4) + 1 := by omega
    rw [e]; simpa using this
  · refine ⟨7, by simp, ?_⟩
    have := per_aux 7 3 0 (by norm_num) (by norm_num) (m / 3)
    have e : m = 3 * (m / 3) + 0 := by omega
    rw [e]; simpa using this
  · refine ⟨13, by simp, ?_⟩
    have := per_aux 13 12 7 (by norm_num) (by norm_num) (m / 12)
    have e : m = 12 * (m / 12) + 7 := by omega
    rw [e]; simpa using this
  · refine ⟨17, by simp, ?_⟩
    have := per_aux 17 8 3 (by norm_num) (by norm_num) (m / 8)
    have e : m = 8 * (m / 8) + 3 := by omega
    rw [e]; simpa using this
  · refine ⟨241, by simp, ?_⟩
    have := per_aux 241 24 23 (by norm_num) (by norm_num) (m / 24)
    have e : m = 24 * (m / 24) + 23 := by omega
    rw [e]; simpa using this

end OMA.S_oeis_a176494

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a176494.main) := by
  intro h
  obtain ⟨m, hm, hp⟩ := h 7629217 (by norm_num) ⟨3814608, by norm_num⟩
  obtain ⟨q, hq, hd⟩ := OMA.S_oeis_a176494.cover m
  have hd' : q ∣ Int.natAbs ((2:ℤ) ^ m - (7629217 : ℕ)) := by
    rw [← Int.natCast_dvd]; simpa using hd
  have hq1 : 1 < q := by simp at hq; omega
  rcases hp.eq_one_or_self_of_dvd q hd' with h1 | h1
  · omega
  · have hq241 : q ≤ 241 := by simp at hq; omega
    have hle : Int.natAbs ((2:ℤ) ^ m - (7629217 : ℕ)) ≤ 241 := by omega
    have h3 : -241 ≤ (2:ℤ) ^ m - (7629217 : ℕ) ∧ (2:ℤ) ^ m - (7629217 : ℕ) ≤ 241 := by omega
    rcases Nat.lt_or_ge m 23 with h4 | h4
    · have : (2:ℤ) ^ m ≤ 2 ^ 22 := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at this h3
      omega
    · have : (2:ℤ) ^ 23 ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) h4
      norm_num at this h3
      omega
