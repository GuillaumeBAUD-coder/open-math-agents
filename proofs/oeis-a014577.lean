import OMAStatements.S_oeis_a014577
import Mathlib

namespace OMA.A014577Proof

open OMA.S_oeis_a014577

lemma a_eq (n : ℕ) : a n = if n % 4 = 0 then 1 else if n % 4 = 2 then 0 else a (n / 2) := by
  rw [a]

lemma a_odd (m : ℕ) : a (2 * m + 1) = a m := by
  rw [a_eq]
  have h1 : (2 * m + 1) % 4 ≠ 0 := by omega
  have h2 : (2 * m + 1) % 4 ≠ 2 := by omega
  have h3 : (2 * m + 1) / 2 = m := by omega
  simp [h1, h2, h3]

lemma a_form (v m : ℕ) : a (2 ^ v * (2 * m + 1) - 1) = if m % 2 = 0 then 1 else 0 := by
  induction v with
  | zero =>
    simp only [pow_zero, one_mul, Nat.add_sub_cancel]
    rw [a_eq]
    rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩ <;> subst hr
    · have : (2 * (r + r)) % 4 = 0 := by omega
      simp [this]; omega
    · have h2 : (2 * (2 * r + 1)) % 4 = 2 := by omega
      simp [h2]
  | succ v ih =>
    have hp : 0 < 2 ^ v * (2 * m + 1) := by positivity
    have : 2 ^ (v + 1) * (2 * m + 1) - 1 = 2 * (2 ^ v * (2 * m + 1) - 1) + 1 := by
      rw [pow_succ, mul_comm (2 ^ v) 2, mul_assoc]; omega
    rw [this, a_odd, ih]

lemma a_pow (k : ℕ) : a (2 ^ k - 1) = 1 := by
  have := a_form k 0
  simpa using this

lemma a_flip (k : ℕ) : a (2 ^ (k + 1) + (2 ^ k - 1)) = 0 := by
  have := a_form k 1
  have e : 2 ^ k * (2 * 1 + 1) - 1 = 2 ^ (k + 1) + (2 ^ k - 1) := by
    have : 0 < 2 ^ k := by positivity
    rw [pow_succ]; omega
  rw [e] at this
  simpa using this

lemma a_shift (k j : ℕ) (hj : j + 1 < 2 ^ (k + 1)) (hne : j + 1 ≠ 2 ^ k) :
    a (2 ^ (k + 1) + j) = a j := by
  obtain ⟨v, o, ho, he⟩ := Nat.exists_eq_two_pow_mul_odd (n := j + 1) (by omega)
  obtain ⟨m, rfl⟩ := ho
  have hv : v < k := by
    by_contra hvk
    push Not at hvk
    rcases Nat.lt_or_ge k v with h | h
    · have : 2 ^ (k + 1) ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) h
      have : 2 ^ v ≤ 2 ^ v * (2 * m + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    · have hk : v = k := le_antisymm h hvk
      subst hk
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp at he; omega
      · have : 2 ^ (v + 1) ≤ 2 ^ v * (2 * m + 1) := by
          rw [pow_succ]; exact Nat.mul_le_mul_left _ (by omega)
        omega
  obtain ⟨w, rfl⟩ : ∃ w, k = v + 1 + w := ⟨k - v - 1, by omega⟩
  have hj' : j = 2 ^ v * (2 * m + 1) - 1 := by omega
  have e : 2 ^ (v + 1 + w + 1) + j = 2 ^ v * (2 * (m + 2 * 2 ^ w) + 1) - 1 := by
    have hp : 0 < 2 ^ v * (2 * m + 1) := by positivity
    have : 2 ^ (v + 1 + w + 1) = 2 ^ v * (4 * 2 ^ w) := by
      rw [show v + 1 + w + 1 = v + (w + 2) by omega, pow_add, pow_add]; ring
    rw [this]
    have : 2 ^ v * (2 * (m + 2 * 2 ^ w) + 1) = 2 ^ v * (4 * 2 ^ w) + 2 ^ v * (2 * m + 1) := by
      ring
    omega
  rw [e, hj', a_form, a_form]
  have : (m + 2 * 2 ^ w) % 2 = m % 2 := by omega
  rw [this]

lemma dir_succ (k : ℕ) : dir (k + 1) = dir k * (if a k = 1 then -I else I) := rfl

lemma I_mul_I : I * I = -1 := by decide

/-- Main doubling lemma. -/
lemma key (k : ℕ) :
    dir (2 ^ (k + 1) - 1) = I ∧
      ∀ j < 2 ^ (k + 1), dir (2 ^ (k + 1) + j) = (if j < 2 ^ k then -1 else 1) * dir j := by
  induction k with
  | zero =>
    refine ⟨by decide +kernel, ?_⟩
    intro j hj
    interval_cases j <;> decide +kernel
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hpos : 0 < 2 ^ (k + 1) := by positivity
    have h1 : dir (2 ^ (k + 1 + 1) - 1) = I := by
      have e : 2 ^ (k + 1 + 1) - 1 = 2 ^ (k + 1) + (2 ^ (k + 1) - 1) := by
        rw [pow_succ 2 (k + 1)]; omega
      rw [e, ih2 _ (by omega)]
      have : ¬ (2 ^ (k + 1) - 1 < 2 ^ k) := by rw [pow_succ]; omega
      rw [if_neg this, one_mul, ih1]
    have h0 : dir (2 ^ (k + 1 + 1)) = 1 := by
      have e : 2 ^ (k + 1 + 1) = (2 ^ (k + 1 + 1) - 1) + 1 := by
        have : 0 < 2 ^ (k + 1 + 1) := by positivity
        omega
      rw [e, dir_succ, a_pow, h1]
      simp only [if_true]
      rw [mul_neg, I_mul_I, neg_neg]
    refine ⟨h1, ?_⟩
    intro j hj
    induction j with
    | zero =>
      simp only [add_zero, h0, hpos, if_true]
      decide
    | succ j ihj =>
      have ihj := ihj (by omega)
      rw [← add_assoc, dir_succ, dir_succ, ihj]
      by_cases hc : j + 1 = 2 ^ (k + 1)
      · have hjv : j = 2 ^ (k + 1) - 1 := by omega
        have hf : a (2 ^ (k + 1 + 1) + j) = 0 := by rw [hjv]; exact a_flip (k + 1)
        have hjlt : j < 2 ^ (k + 1) := by omega
        have hj1 : ¬ (j + 1 < 2 ^ (k + 1)) := by omega
        rw [hf, if_pos hjlt, if_neg hj1, hjv, a_pow]
        simp
      · rw [a_shift (k + 1) j (by omega) hc]
        have : (j < 2 ^ (k + 1)) ↔ (j + 1 < 2 ^ (k + 1)) := by omega
        by_cases hl : j < 2 ^ (k + 1)
        · rw [if_pos hl, if_pos (this.mp hl)]; ring
        · rw [if_neg hl, if_neg (fun h => hl (this.mpr h))]; ring

theorem main_proof :
    row 0 = [-1] ∧
    row 1 = [-1, I] ∧
    row 2 = [-1, I, 1, I] ∧
    row 3 = [-1, I, 1, I, 1, -I, 1, I] ∧
    row 4 = [-1, I, 1, I, 1, -I, 1, I, 1, -I, -1, -I, 1, -I, 1, I] ∧
    ∀ n, 1 ≤ n →
      row (n + 1) = row n ++ ((row n).take (2 ^ (n - 1))).map (fun z => -z) ++
        (row n).drop (2 ^ (n - 1)) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hk := (key k).2
  unfold row
  have hsplit : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
  rw [pow_succ 2 (k + 1), mul_two, List.range_add, List.map_append, List.append_assoc]
  congr 1
  rw [hsplit, List.range_add]
  simp only [List.map_append, List.map_map]
  rw [List.take_left' (by simp), List.drop_left' (by simp)]
  simp only [List.map_map]
  congr 1
  · apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    simp only [Function.comp]
    rw [← hsplit, hk j (by omega), if_pos hj, neg_one_mul]
  · apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    simp only [Function.comp]
    rw [← add_assoc, ← hsplit, add_assoc, hk (2 ^ k + j) (by omega)]
    rw [if_neg (by omega), one_mul]

end OMA.A014577Proof

open OMA.A014577Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a014577.main := main_proof
