import OMAStatements.S_oeis_a098664
import Mathlib

namespace A098664Proof

open OMA.S_oeis_a098664

lemma a_even (j : ℕ) :
    a (2 * j) = ((2 * j).factorial : ℚ) * ((2 : ℚ) ^ (2 * j) / ((j.factorial : ℚ) ^ 2)) := by
  have he : Even (2 * j) := ⟨j, by ring⟩
  have ho : ¬ Odd (2 * j) := by rw [Nat.not_odd_iff_even]; exact he
  have d : 2 * j / 2 = j := by omega
  simp only [a, i0, i1, if_pos he, if_neg ho, d]
  ring

lemma a_odd (j : ℕ) :
    a (2 * j + 1) = ((2 * j + 1).factorial : ℚ) *
      ((2 : ℚ) ^ (2 * j + 1) / ((j.factorial : ℚ) * ((j + 1).factorial : ℚ)) / 2) := by
  have ho : Odd (2 * j + 1) := ⟨j, rfl⟩
  have he : ¬ Even (2 * j + 1) := by rw [Nat.not_even_iff_odd]; exact ho
  have d1 : (2 * j + 1 - 1) / 2 = j := by omega
  have d2 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
  simp only [a, i0, i1, if_neg he, if_pos ho, d1, d2]
  ring

lemma big_odd (j : ℕ) :
    (((2 * j + 3 : ℕ) : ℚ) + 1) * a (2 * j + 3) + 8 * (((2 * j + 3 : ℕ) : ℚ) - 1) * a (2 * j + 2)
      - 16 * ((2 * j + 3 : ℕ) : ℚ) * a (2 * j + 1)
      + 128 * (2 - ((2 * j + 3 : ℕ) : ℚ)) * a (2 * j) = 0 := by
  have e3 : 2 * j + 3 = 2 * (j + 1) + 1 := by ring
  have e2 : 2 * j + 2 = 2 * (j + 1) := by ring
  rw [e3, e2, a_odd (j + 1), a_even (j + 1), a_odd j, a_even j]
  have f0 : (j.factorial : ℚ) ≠ 0 := by positivity
  have F0 : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.mul_add, Nat.reduceMul]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma big_even (j : ℕ) :
    (((2 * j + 4 : ℕ) : ℚ) + 1) * a (2 * j + 4) + 8 * (((2 * j + 4 : ℕ) : ℚ) - 1) * a (2 * j + 3)
      - 16 * ((2 * j + 4 : ℕ) : ℚ) * a (2 * j + 2)
      + 128 * (2 - ((2 * j + 4 : ℕ) : ℚ)) * a (2 * j + 1) = 0 := by
  have e4 : 2 * j + 4 = 2 * (j + 2) := by ring
  have e3 : 2 * j + 3 = 2 * (j + 1) + 1 := by ring
  have e2 : 2 * j + 2 = 2 * (j + 1) := by ring
  rw [e4, e3, e2, a_even (j + 2), a_odd (j + 1), a_even (j + 1), a_odd j]
  have f0 : (j.factorial : ℚ) ≠ 0 := by positivity
  have F0 : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.mul_add, Nat.reduceMul]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

end A098664Proof

open OMA.S_oeis_a098664 in
theorem OMA.solution : type_of% @OMA.S_oeis_a098664.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have i1' : m + 3 - 1 = m + 2 := by omega
  have i2' : m + 3 - 2 = m + 1 := by omega
  have i3' : m + 3 - 3 = m := by omega
  rw [i1', i2', i3']
  rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
  · have h := A098664Proof.big_odd j
    push_cast at h ⊢
    linarith
  · have h := A098664Proof.big_even j
    have e4 : 2 * j + 1 + 3 = 2 * j + 4 := by ring
    have e3 : 2 * j + 1 + 2 = 2 * j + 3 := by ring
    have e2 : 2 * j + 1 + 1 = 2 * j + 2 := by ring
    rw [e4, e3, e2]
    push_cast at h ⊢
    linarith
