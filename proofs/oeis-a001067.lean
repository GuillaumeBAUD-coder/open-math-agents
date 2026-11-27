import OMAStatements.S_oeis_a001067
import Mathlib

/-!
# Disproof of Ramanujan's claim recorded in OEIS A001067

The claim fails at n = 10: B(20)/20 = -174611/6600 in lowest terms, and
174611 = 283 * 617 is composite. This is the known counterexample (see OEIS
A001067 / A119766). The Bernoulli numbers up to B(20) are computed from
Mathlib's recursive definition, one index at a time.
-/

namespace OMA.P_oeis_a001067

open Finset

lemma b0 : bernoulli' 0 = 1 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

lemma b1 : bernoulli' 1 = 1 / 2 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, b0]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

lemma b2 : bernoulli' 2 = 1 / 6 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, b0, b1]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

lemma b3 : bernoulli' 3 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

lemma b4 : bernoulli' 4 = -1 / 30 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, b0, b1, b2, b3]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

lemma b5 : bernoulli' 5 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

lemma b6 : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, b0, b1, b2, b3, b4, b5]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

lemma b7 : bernoulli' 7 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

lemma b8 : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, b0, b1, b2, b3, b4, b5, b6, b7]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

lemma b9 : bernoulli' 9 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

lemma b10 : bernoulli' 10 = 5 / 66 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

lemma b11 : bernoulli' 11 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

lemma b12 : bernoulli' 12 = -691 / 2730 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

lemma b13 : bernoulli' 13 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

lemma b14 : bernoulli' 14 = 7 / 6 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

lemma b15 : bernoulli' 15 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

lemma b16 : bernoulli' 16 = -3617 / 510 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

lemma b17 : bernoulli' 17 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

lemma b18 : bernoulli' 18 = 43867 / 798 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

lemma b19 : bernoulli' 19 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

lemma b20 : bernoulli' 20 = -174611 / 330 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

lemma num_eq : ((-174611 / 330 : ℚ) / (2 * ((10 : ℕ) : ℚ))).num = -174611 := by
  have e : (-174611 / 330 : ℚ) / (2 * ((10 : ℕ) : ℚ)) = ((-174611 : ℤ) : ℚ) / ((6600 : ℤ) : ℚ) := by
    norm_num
  rw [e, Rat.num_div_eq_of_coprime (by norm_num) (by norm_num)]

end OMA.P_oeis_a001067

open OMA.P_oeis_a001067 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a001067.main) := by
  intro h
  have h10 := h 10 (by norm_num)
  unfold OMA.S_oeis_a001067.absNumerator at h10
  rw [show 2 * 10 = 20 from rfl, bernoulli_eq_bernoulli'_of_ne_one (by norm_num), b20, num_eq] at h10
  norm_num at h10
