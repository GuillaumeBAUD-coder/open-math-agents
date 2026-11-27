import OMAStatements.S_oeis_a329178
import Mathlib

namespace A329178Proof

open PowerSeries OMA.S_oeis_a329178

lemma P_rec (n : ℕ) : padovan (n + 3) = padovan (n + 1) + padovan n := by
  rw [padovan]

lemma a_zero : a 0 = 1 := by
  unfold a
  simp [padovan]

lemma a_succ (n : ℕ) : a (n + 1) = a n + padovan (n + 6) * padovan (n + 8) := by
  unfold a
  rw [Finset.sum_range_succ]

lemma a_one : a 1 = 3 := by rw [a_succ, a_zero]; simp [padovan]
lemma a_two : a 2 = 5 := by rw [a_succ, a_one]; simp [padovan]
lemma a_three : a 3 = 11 := by rw [a_succ, a_two]; simp [padovan]
lemma a_four : a 4 = 19 := by rw [a_succ, a_three]; simp [padovan]
lemma a_five : a 5 = 34 := by rw [a_succ, a_four]; simp [padovan]
lemma a_six : a 6 = 62 := by rw [a_succ, a_five]; simp [padovan]

lemma rec7 (m : ℕ) :
    a (m + 7) = 2 * a (m + 6) - 2 * a (m + 3) + 2 * a (m + 2) - 2 * a (m + 1) + a m := by
  have h1 := a_succ m
  have h2 := a_succ (m + 1)
  have h3 := a_succ (m + 2)
  have h4 := a_succ (m + 3)
  have h5 := a_succ (m + 4)
  have h6 := a_succ (m + 5)
  have h7 := a_succ (m + 6)
  have p9 := P_rec (m + 6)
  have p10 := P_rec (m + 7)
  have p11 := P_rec (m + 8)
  have p12 := P_rec (m + 9)
  have p13 := P_rec (m + 10)
  have p14 := P_rec (m + 11)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h2 h3 h4 h5 h6 h7 p9 p10 p11 p12 p13 p14
  rw [h7, h6, h5, h4, h3, h2, h1]
  rw [p14, p13, p12, p11, p10, p9]
  ring

end A329178Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a329178.main := by
  constructor
  · show ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X + PowerSeries.X ^ 2 - PowerSeries.X ^ 3)
        * (1 + PowerSeries.X - PowerSeries.X ^ 3) : PowerSeries ℤ) *
          PowerSeries.mk OMA.S_oeis_a329178.a =
        1 + PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 - PowerSeries.X ^ 4
    rw [mul_comm]
    have hD : ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X + PowerSeries.X ^ 2 - PowerSeries.X ^ 3)
        * (1 + PowerSeries.X - PowerSeries.X ^ 3) : PowerSeries ℤ)
        = 1 - PowerSeries.X ^ 1 - PowerSeries.X ^ 1 + PowerSeries.X ^ 4 + PowerSeries.X ^ 4
          - PowerSeries.X ^ 5 - PowerSeries.X ^ 5 + PowerSeries.X ^ 6 + PowerSeries.X ^ 6
          - PowerSeries.X ^ 7 := by
      ring
    rw [hD]
    ext n
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ 7 ≤ n)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    · simp [A329178Proof.a_zero]
    · simp [A329178Proof.a_zero, A329178Proof.a_one]
    · simp [A329178Proof.a_one, A329178Proof.a_two]
    · simp [A329178Proof.a_two, A329178Proof.a_three]
    · simp [A329178Proof.a_zero, A329178Proof.a_three, A329178Proof.a_four]
    · simp [A329178Proof.a_zero, A329178Proof.a_one, A329178Proof.a_four, A329178Proof.a_five]
    · simp [A329178Proof.a_zero, A329178Proof.a_one, A329178Proof.a_two, A329178Proof.a_five,
        A329178Proof.a_six]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
      have hr := A329178Proof.rec7 m
      have e1 : m + 7 - 1 = m + 6 := by omega
      have e4 : m + 7 - 4 = m + 3 := by omega
      have e5 : m + 7 - 5 = m + 2 := by omega
      have e6 : m + 7 - 6 = m + 1 := by omega
      have e7 : m + 7 - 7 = m := by omega
      have c1 : 1 ≤ m + 7 := by omega
      have c4 : 4 ≤ m + 7 := by omega
      have c5 : 5 ≤ m + 7 := by omega
      have c6 : 6 ≤ m + 7 := by omega
      have c7 : 7 ≤ m + 7 := by omega
      have z0 : ¬ m + 7 = 0 := by omega
      have z1 : ¬ m + 7 = 1 := by omega
      have z2 : ¬ m + 7 = 2 := by omega
      have z3 : ¬ m + 7 = 3 := by omega
      have z4 : ¬ m + 7 = 4 := by omega
      simp only [if_pos c1, if_pos c4, if_pos c5, if_pos c6, if_pos c7,
        if_neg z0, if_neg z1, if_neg z2, if_neg z3, if_neg z4, e1, e4, e5, e6, e7]
      rw [hr]
      ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have hr := A329178Proof.rec7 m
    have e1 : m + 7 - 1 = m + 6 := by omega
    have e4 : m + 7 - 4 = m + 3 := by omega
    have e5 : m + 7 - 5 = m + 2 := by omega
    have e6 : m + 7 - 6 = m + 1 := by omega
    have e7 : m + 7 - 7 = m := by omega
    rw [e1, e4, e5, e6, e7]
    exact hr
