import OMAStatements.S_oeis_a086845
import Mathlib

namespace A086845
open OMA.S_oeis_a086845

lemma b_zero : A087808 0 = 0 := by
  rw [A087808]

lemma b_odd (m : ℕ) : A087808 (2 * m + 1) = A087808 m + 1 := by
  rw [A087808]
  have h1 : ¬ (2 * m + 1) % 2 = 0 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [if_neg h1, h2]

lemma b_even (m : ℕ) : A087808 (2 * m) = 2 * A087808 m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    rw [Nat.mul_zero, b_zero]
  · obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    have e : 2 * (i + 1) = (2 * i + 1) + 1 := by ring
    rw [e, A087808]
    have h1 : (2 * i + 1 + 1) % 2 = 0 := by omega
    have h2 : (2 * i + 1 + 1) / 2 = i + 1 := by omega
    rw [if_pos h1, h2]

lemma S_even (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), A087808 k = 3 * ∑ k ∈ Finset.range m, A087808 k + m := by
  induction m with
  | zero => simp
  | succ i ih =>
    have e : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, b_odd, b_even,
      Finset.sum_range_succ]
    ring

lemma a_step (n : ℕ) : a (n + 2) = a ((n + 2) / 2) + 2 * a ((n + 3) / 2) + (n + 2) / 2 := by
  rw [a]

lemma a_zero : a 0 = 0 := by
  rw [a]

lemma a_one : a 1 = 0 := by
  rw [a]

lemma all (n : ℕ) : a n = ∑ k ∈ Finset.range n, A087808 k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · rw [a_zero]
        simp
      · rw [a_one]
        simp [b_zero]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      rw [a_step]
      rcases Nat.even_or_odd' (k + 2) with ⟨m, hm | hm⟩
      · have e1 : (k + 2) / 2 = m := by omega
        have e2 : (k + 3) / 2 = m := by omega
        rw [e1, e2, ih m (by omega), hm, S_even]
        ring
      · have e1 : (k + 2) / 2 = m := by omega
        have e2 : (k + 3) / 2 = m + 1 := by omega
        rw [e1, e2, ih m (by omega), ih (m + 1) (by omega), hm,
          Finset.sum_range_succ _ (2 * m), S_even, b_even, Finset.sum_range_succ]
        ring

end A086845

theorem OMA.solution : type_of% @OMA.S_oeis_a086845.main := by
  intro n _
  exact A086845.all n
