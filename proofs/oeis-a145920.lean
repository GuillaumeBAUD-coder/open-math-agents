import OMAStatements.S_oeis_a145920
import Mathlib

namespace A145920Proof

open OMA.S_oeis_a145920

def P (t : ℚ) : ℚ := (27 * t ^ 4 - 18 * t ^ 3 - 3 * t ^ 2 + 2 * t) / 8

lemma a_even (j : ℕ) : a (2 * j) = P j := by
  have h1 : 2 * j / 2 = j := by omega
  have h2 : (-1 : ℚ) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
  simp only [a, x, P, h1, h2, mul_one]

lemma a_odd (j : ℕ) : a (2 * j + 1) = P (-(j : ℚ)) := by
  have h1 : (2 * j + 1) / 2 = j := by omega
  have h2 : (-1 : ℚ) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  simp only [a, x, P, h1, h2]
  ring

lemma rec9 (m : ℕ) :
    a (m + 9) = a (m + 8) + 4 * a (m + 7) - 4 * a (m + 6) - 6 * a (m + 5) + 6 * a (m + 4)
      + 4 * a (m + 3) - 4 * a (m + 2) - a (m + 1) + a m := by
  rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
  · -- even m
    have e9 : 2 * j + 9 = 2 * (j + 4) + 1 := by ring
    have e8 : 2 * j + 8 = 2 * (j + 4) := by ring
    have e7 : 2 * j + 7 = 2 * (j + 3) + 1 := by ring
    have e6 : 2 * j + 6 = 2 * (j + 3) := by ring
    have e5 : 2 * j + 5 = 2 * (j + 2) + 1 := by ring
    have e4 : 2 * j + 4 = 2 * (j + 2) := by ring
    have e3 : 2 * j + 3 = 2 * (j + 1) + 1 := by ring
    have e2 : 2 * j + 2 = 2 * (j + 1) := by ring
    rw [e9, e8, e7, e6, e5, e4, e3, e2]
    simp only [a_odd, a_even, P]
    push_cast
    ring
  · -- odd m
    have e9 : 2 * j + 1 + 9 = 2 * (j + 5) := by ring
    have e8 : 2 * j + 1 + 8 = 2 * (j + 4) + 1 := by ring
    have e7 : 2 * j + 1 + 7 = 2 * (j + 4) := by ring
    have e6 : 2 * j + 1 + 6 = 2 * (j + 3) + 1 := by ring
    have e5 : 2 * j + 1 + 5 = 2 * (j + 3) := by ring
    have e4 : 2 * j + 1 + 4 = 2 * (j + 2) + 1 := by ring
    have e3 : 2 * j + 1 + 3 = 2 * (j + 2) := by ring
    have e2 : 2 * j + 1 + 2 = 2 * (j + 1) + 1 := by ring
    have e1 : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
    rw [e9, e8, e7, e6, e5, e4, e3, e2, e1]
    simp only [a_odd, a_even, P]
    push_cast
    ring

lemma a_0 : a 0 = 0 := by norm_num [a, x]
lemma a_1 : a 1 = 0 := by norm_num [a, x]
lemma a_2 : a 2 = 1 := by norm_num [a, x]
lemma a_3 : a 3 = 5 := by norm_num [a, x]
lemma a_4 : a 4 = 35 := by norm_num [a, x]
lemma a_5 : a 5 = 70 := by norm_num [a, x]
lemma a_6 : a 6 = 210 := by norm_num [a, x]
lemma a_7 : a 7 = 330 := by norm_num [a, x]
lemma a_8 : a 8 = 715 := by norm_num [a, x]

end A145920Proof

open PowerSeries OMA.S_oeis_a145920 in
theorem OMA.solution : type_of% @OMA.S_oeis_a145920.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    have hr := A145920Proof.rec9 (m + 1)
    have i1 : m + 10 - 1 = m + 9 := by omega
    have i2 : m + 10 - 2 = m + 8 := by omega
    have i3 : m + 10 - 3 = m + 7 := by omega
    have i4 : m + 10 - 4 = m + 6 := by omega
    have i5 : m + 10 - 5 = m + 5 := by omega
    have i6 : m + 10 - 6 = m + 4 := by omega
    have i7 : m + 10 - 7 = m + 3 := by omega
    have i8 : m + 10 - 8 = m + 2 := by omega
    have i9 : m + 10 - 9 = m + 1 := by omega
    rw [i1, i2, i3, i4, i5, i6, i7, i8, i9]
    simp only [Nat.add_assoc, Nat.reduceAdd] at hr
    linarith
  · have hD : (((1 + X) ^ 4 * (1 - X) ^ 5) : PowerSeries ℚ) = C (1) + C (-1) * X ^ 1 + C (-4) * X ^ 2 + C (4) * X ^ 3 + C (6) * X ^ 4 + C (-6) * X ^ 5 + C (-4) * X ^ 6 + C (4) * X ^ 7 + C (1) * X ^ 8 + C (-1) * X ^ 9 := by
      simp only [map_neg, map_ofNat, map_one]; ring
    have hN : ((X ^ 2 * (1 + 4 * X + 26 * X ^ 2 + 19 * X ^ 3 + 26 * X ^ 4 + 4 * X ^ 5 + X ^ 6)) : PowerSeries ℚ) = C (1) * X ^ 2 + C (4) * X ^ 3 + C (26) * X ^ 4 + C (19) * X ^ 5 + C (26) * X ^ 6 + C (4) * X ^ 7 + C (1) * X ^ 8 := by
      simp only [map_neg, map_ofNat, map_one]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, ← mul_assoc, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_C,
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ 9 ≤ n) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    · norm_num [A145920Proof.a_0]
    · norm_num [A145920Proof.a_0, A145920Proof.a_1]
    · norm_num [A145920Proof.a_0, A145920Proof.a_1, A145920Proof.a_2]
    · norm_num [A145920Proof.a_0, A145920Proof.a_1, A145920Proof.a_2, A145920Proof.a_3]
    · norm_num [A145920Proof.a_0, A145920Proof.a_1, A145920Proof.a_2, A145920Proof.a_3, A145920Proof.a_4]
    · norm_num [A145920Proof.a_0, A145920Proof.a_1, A145920Proof.a_2, A145920Proof.a_3, A145920Proof.a_4, A145920Proof.a_5]
    · norm_num [A145920Proof.a_0, A145920Proof.a_1, A145920Proof.a_2, A145920Proof.a_3, A145920Proof.a_4, A145920Proof.a_5, A145920Proof.a_6]
    · norm_num [A145920Proof.a_0, A145920Proof.a_1, A145920Proof.a_2, A145920Proof.a_3, A145920Proof.a_4, A145920Proof.a_5, A145920Proof.a_6, A145920Proof.a_7]
    · norm_num [A145920Proof.a_0, A145920Proof.a_1, A145920Proof.a_2, A145920Proof.a_3, A145920Proof.a_4, A145920Proof.a_5, A145920Proof.a_6, A145920Proof.a_7, A145920Proof.a_8]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      have hr := A145920Proof.rec9 m
      have c1 : 1 ≤ m + 9 := by omega
      have e1 : m + 9 - 1 = m + 8 := by omega
      have c2 : 2 ≤ m + 9 := by omega
      have e2 : m + 9 - 2 = m + 7 := by omega
      have c3 : 3 ≤ m + 9 := by omega
      have e3 : m + 9 - 3 = m + 6 := by omega
      have c4 : 4 ≤ m + 9 := by omega
      have e4 : m + 9 - 4 = m + 5 := by omega
      have c5 : 5 ≤ m + 9 := by omega
      have e5 : m + 9 - 5 = m + 4 := by omega
      have c6 : 6 ≤ m + 9 := by omega
      have e6 : m + 9 - 6 = m + 3 := by omega
      have c7 : 7 ≤ m + 9 := by omega
      have e7 : m + 9 - 7 = m + 2 := by omega
      have c8 : 8 ≤ m + 9 := by omega
      have e8 : m + 9 - 8 = m + 1 := by omega
      have c9 : 9 ≤ m + 9 := by omega
      have e9 : m + 9 - 9 = m := by omega
      have z1 : ¬ (m + 1 = 0) := by omega
      have z2 : ¬ (m + 2 = 0) := by omega
      have z3 : ¬ (m + 3 = 0) := by omega
      have z4 : ¬ (m + 4 = 0) := by omega
      have z5 : ¬ (m + 5 = 0) := by omega
      have z6 : ¬ (m + 6 = 0) := by omega
      have z7 : ¬ (m + 7 = 0) := by omega
      simp only [if_pos c1, if_pos c2, if_pos c3, if_pos c4, if_pos c5, if_pos c6, if_pos c7, if_pos c8, if_pos c9, e1, e2, e3, e4, e5, e6, e7, e8, e9, if_neg z1, if_neg z2, if_neg z3, if_neg z4, if_neg z5, if_neg z6, if_neg z7]
      rw [hr]
      ring
