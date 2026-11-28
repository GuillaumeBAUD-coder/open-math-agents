import OMAStatements.S_oeis_a007384
import Mathlib

namespace A007384Proof

open OMA.S_oeis_a007384

lemma c_rec (n : ℕ) : c (n + 5) = c (n + 3) + c n := by
  rw [c]

lemma b_step (n : ℕ) : b (n + 4) = 2 * b (n + 2) - b n := by
  simp only [b]
  split_ifs <;> omega

lemma b_rec (m : ℕ) :
    b (m + 9) = 3 * b (m + 7) - 3 * b (m + 5) + b (m + 4) + b (m + 3) - 2 * b (m + 2) + b m := by
  have s1 := b_step (m + 5)
  have s2 := b_step (m + 3)
  have s3 := b_step m
  simp only [Nat.add_assoc, Nat.reduceAdd] at s1 s2 s3
  linarith

lemma rec9 (m : ℕ) :
    a (m + 9) = 3 * a (m + 7) - 3 * a (m + 5) + a (m + 4) + a (m + 3) - 2 * a (m + 2) + a m := by
  have hb := b_rec m
  have r1 := c_rec (m + 10)
  have r2 := c_rec (m + 8)
  have r3 := c_rec (m + 6)
  simp only [a]
  simp only [Nat.add_assoc, Nat.reduceAdd] at r1 r2 r3 ⊢
  linarith

lemma a_0 : a 0 = 0 := by simp [a, b, c]
lemma a_1 : a 1 = 0 := by simp [a, b, c]
lemma a_2 : a 2 = 0 := by simp [a, b, c]
lemma a_3 : a 3 = 0 := by simp [a, b, c]
lemma a_4 : a 4 = 0 := by simp [a, b, c]
lemma a_5 : a 5 = 1 := by simp [a, b, c]
lemma a_6 : a 6 = 0 := by simp [a, b, c]
lemma a_7 : a 7 = 3 := by simp [a, b, c]
lemma a_8 : a 8 = 0 := by simp [a, b, c]

end A007384Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a007384.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    have hr := A007384Proof.rec9 (m + 1)
    have e2 : m + 10 - 2 = m + 8 := by omega
    have e4 : m + 10 - 4 = m + 6 := by omega
    have e5 : m + 10 - 5 = m + 5 := by omega
    have e6 : m + 10 - 6 = m + 4 := by omega
    have e7 : m + 10 - 7 = m + 3 := by omega
    have e9 : m + 10 - 9 = m + 1 := by omega
    rw [e2, e4, e5, e6, e7, e9]
    simp only [Nat.add_assoc, Nat.reduceAdd] at hr
    linarith
  · have hD : ((PowerSeries.X ^ 5 + PowerSeries.X ^ 2 - 1) * (PowerSeries.X - 1) ^ 2
          * (1 + PowerSeries.X) ^ 2 : PowerSeries ℤ)
        = -1 + PowerSeries.X ^ 2 + PowerSeries.X ^ 2 + PowerSeries.X ^ 2 - PowerSeries.X ^ 4
          - PowerSeries.X ^ 4 - PowerSeries.X ^ 4 + PowerSeries.X ^ 5 + PowerSeries.X ^ 6
          - PowerSeries.X ^ 7 - PowerSeries.X ^ 7 + PowerSeries.X ^ 9 := by
      ring
    rw [hD]
    ext n
    simp only [mul_add, mul_sub, mul_neg, mul_one, map_add, map_sub, map_neg,
      PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8
        ∨ 9 ≤ n) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    · simp [A007384Proof.a_0]
    · simp [A007384Proof.a_1]
    · simp [A007384Proof.a_0, A007384Proof.a_2]
    · simp [A007384Proof.a_1, A007384Proof.a_3]
    · simp [A007384Proof.a_0, A007384Proof.a_2, A007384Proof.a_4]
    · simp [A007384Proof.a_0, A007384Proof.a_1, A007384Proof.a_3, A007384Proof.a_5]
    · simp [A007384Proof.a_0, A007384Proof.a_1, A007384Proof.a_2, A007384Proof.a_4,
        A007384Proof.a_6]
    · simp [A007384Proof.a_0, A007384Proof.a_1, A007384Proof.a_2, A007384Proof.a_3,
        A007384Proof.a_5, A007384Proof.a_7]
    · simp [A007384Proof.a_1, A007384Proof.a_2, A007384Proof.a_3, A007384Proof.a_4,
        A007384Proof.a_6, A007384Proof.a_8]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      have hr := A007384Proof.rec9 m
      have e2 : m + 9 - 2 = m + 7 := by omega
      have e4 : m + 9 - 4 = m + 5 := by omega
      have e5 : m + 9 - 5 = m + 4 := by omega
      have e6 : m + 9 - 6 = m + 3 := by omega
      have e7 : m + 9 - 7 = m + 2 := by omega
      have e9 : m + 9 - 9 = m := by omega
      have c2 : 2 ≤ m + 9 := by omega
      have c4 : 4 ≤ m + 9 := by omega
      have c5 : 5 ≤ m + 9 := by omega
      have c6 : 6 ≤ m + 9 := by omega
      have c7 : 7 ≤ m + 9 := by omega
      have c9 : 9 ≤ m + 9 := by omega
      have z5 : ¬ m + 9 = 5 := by omega
      simp only [if_pos c2, if_pos c4, if_pos c5, if_pos c6, if_pos c7, if_pos c9, if_neg z5,
        e2, e4, e5, e6, e7, e9]
      rw [hr]
      ring
