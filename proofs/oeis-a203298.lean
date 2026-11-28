import OMAStatements.S_oeis_a203298
import Mathlib

namespace A203298

open OMA.S_oeis_a203298

def T (n : ℕ) : ℕ := ∑ i ∈ Finset.Ico 1 (n + 1), t i

lemma T_zero : T 0 = 0 := by
  simp [T]

lemma T_succ (n : ℕ) : T (n + 1) = T n + t (n + 1) := by
  unfold T
  rw [Finset.sum_Ico_succ_top (by omega)]

lemma a_zero : a 0 = 0 := by
  simp [a]

lemma a_succ (n : ℕ) : a (n + 1) = a n + T n * t (n + 1) := by
  unfold a T
  rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_mul]

lemma evenForm (m : ℕ) : T (2 * m) = m ^ 2 + 2 * m ∧
    6 * ((a (2 * m) : ℕ) : ℤ) = 3 * (m : ℤ) ^ 4 + 10 * (m : ℤ) ^ 3 + 6 * (m : ℤ) ^ 2 - 7 * (m : ℤ) := by
  induction m with
  | zero => exact ⟨by simp [T_zero], by simp [a_zero]⟩
  | succ k ih =>
    obtain ⟨hT, hA⟩ := ih
    have t1 : t (2 * k + 1) = k + 1 := by
      unfold t
      omega
    have t2 : t (2 * k + 1 + 1) = k + 2 := by
      unfold t
      omega
    have hT1 : T (2 * k + 1) = k ^ 2 + 3 * k + 1 := by
      rw [T_succ, hT, t1]
      ring
    have hA1 : a (2 * k + 1) = a (2 * k) + (k ^ 2 + 2 * k) * (k + 1) := by
      rw [a_succ, hT, t1]
    have hT2 : T (2 * k + 1 + 1) = (k + 1) ^ 2 + 2 * (k + 1) := by
      rw [T_succ, hT1, t2]
      ring
    have hA2 : a (2 * k + 1 + 1) = a (2 * k + 1) + (k ^ 2 + 3 * k + 1) * (k + 2) := by
      rw [a_succ, hT1, t2]
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    refine ⟨hT2, ?_⟩
    rw [hA2, hA1]
    push_cast
    linear_combination hA

lemma oddForm (m : ℕ) : 6 * ((a (2 * m + 1) : ℕ) : ℤ) = 3 * (m : ℤ) ^ 4 + 16 * (m : ℤ) ^ 3 + 24 * (m : ℤ) ^ 2 + 5 * (m : ℤ) := by
  obtain ⟨hT, hA⟩ := evenForm m
  have t1 : t (2 * m + 1) = m + 1 := by
    unfold t
    omega
  rw [a_succ, hT, t1]
  push_cast
  linear_combination hA

set_option maxHeartbeats 1000000 in
lemma recE (m : ℕ) : ((OMA.S_oeis_a203298.a (2 * m + 10) : ℕ) : ℤ) = 2 * ((OMA.S_oeis_a203298.a (2 * m + 9) : ℕ) : ℤ) + 2 * ((OMA.S_oeis_a203298.a (2 * m + 8) : ℕ) : ℤ) - 6 * ((OMA.S_oeis_a203298.a (2 * m + 7) : ℕ) : ℤ) + 6 * ((OMA.S_oeis_a203298.a (2 * m + 5) : ℕ) : ℤ)
    - 2 * ((OMA.S_oeis_a203298.a (2 * m + 4) : ℕ) : ℤ) - 2 * ((OMA.S_oeis_a203298.a (2 * m + 3) : ℕ) : ℤ) + ((OMA.S_oeis_a203298.a (2 * m + 2) : ℕ) : ℤ) := by
  have h0 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 10) : ℕ) : ℤ) = 3 * ((m : ℤ) + 5) ^ 4 + 10 * ((m : ℤ) + 5) ^ 3 + 6 * ((m : ℤ) + 5) ^ 2 - 7 * ((m : ℤ) + 5) := by
    have h := (evenForm (m + 5)).2
    rw [show 2 * (m + 5) = 2 * m + 10 by ring] at h
    push_cast at h
    linear_combination h
  have h1 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 9) : ℕ) : ℤ) = 3 * ((m : ℤ) + 4) ^ 4 + 16 * ((m : ℤ) + 4) ^ 3 + 24 * ((m : ℤ) + 4) ^ 2 + 5 * ((m : ℤ) + 4) := by
    have h := oddForm (m + 4)
    rw [show 2 * (m + 4) + 1 = 2 * m + 9 by ring] at h
    push_cast at h
    linear_combination h
  have h2 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 8) : ℕ) : ℤ) = 3 * ((m : ℤ) + 4) ^ 4 + 10 * ((m : ℤ) + 4) ^ 3 + 6 * ((m : ℤ) + 4) ^ 2 - 7 * ((m : ℤ) + 4) := by
    have h := (evenForm (m + 4)).2
    rw [show 2 * (m + 4) = 2 * m + 8 by ring] at h
    push_cast at h
    linear_combination h
  have h3 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 7) : ℕ) : ℤ) = 3 * ((m : ℤ) + 3) ^ 4 + 16 * ((m : ℤ) + 3) ^ 3 + 24 * ((m : ℤ) + 3) ^ 2 + 5 * ((m : ℤ) + 3) := by
    have h := oddForm (m + 3)
    rw [show 2 * (m + 3) + 1 = 2 * m + 7 by ring] at h
    push_cast at h
    linear_combination h
  have h5 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 5) : ℕ) : ℤ) = 3 * ((m : ℤ) + 2) ^ 4 + 16 * ((m : ℤ) + 2) ^ 3 + 24 * ((m : ℤ) + 2) ^ 2 + 5 * ((m : ℤ) + 2) := by
    have h := oddForm (m + 2)
    rw [show 2 * (m + 2) + 1 = 2 * m + 5 by ring] at h
    push_cast at h
    linear_combination h
  have h6 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 4) : ℕ) : ℤ) = 3 * ((m : ℤ) + 2) ^ 4 + 10 * ((m : ℤ) + 2) ^ 3 + 6 * ((m : ℤ) + 2) ^ 2 - 7 * ((m : ℤ) + 2) := by
    have h := (evenForm (m + 2)).2
    rw [show 2 * (m + 2) = 2 * m + 4 by ring] at h
    push_cast at h
    linear_combination h
  have h7 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 3) : ℕ) : ℤ) = 3 * ((m : ℤ) + 1) ^ 4 + 16 * ((m : ℤ) + 1) ^ 3 + 24 * ((m : ℤ) + 1) ^ 2 + 5 * ((m : ℤ) + 1) := by
    have h := oddForm (m + 1)
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring] at h
    push_cast at h
    linear_combination h
  have h8 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 2) : ℕ) : ℤ) = 3 * ((m : ℤ) + 1) ^ 4 + 10 * ((m : ℤ) + 1) ^ 3 + 6 * ((m : ℤ) + 1) ^ 2 - 7 * ((m : ℤ) + 1) := by
    have h := (evenForm (m + 1)).2
    rw [show 2 * (m + 1) = 2 * m + 2 by ring] at h
    push_cast at h
    linear_combination h
  linarith

set_option maxHeartbeats 1000000 in
lemma recO (m : ℕ) : ((OMA.S_oeis_a203298.a (2 * m + 11) : ℕ) : ℤ) = 2 * ((OMA.S_oeis_a203298.a (2 * m + 10) : ℕ) : ℤ) + 2 * ((OMA.S_oeis_a203298.a (2 * m + 9) : ℕ) : ℤ) - 6 * ((OMA.S_oeis_a203298.a (2 * m + 8) : ℕ) : ℤ) + 6 * ((OMA.S_oeis_a203298.a (2 * m + 6) : ℕ) : ℤ)
    - 2 * ((OMA.S_oeis_a203298.a (2 * m + 5) : ℕ) : ℤ) - 2 * ((OMA.S_oeis_a203298.a (2 * m + 4) : ℕ) : ℤ) + ((OMA.S_oeis_a203298.a (2 * m + 3) : ℕ) : ℤ) := by
  have h0 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 11) : ℕ) : ℤ) = 3 * ((m : ℤ) + 5) ^ 4 + 16 * ((m : ℤ) + 5) ^ 3 + 24 * ((m : ℤ) + 5) ^ 2 + 5 * ((m : ℤ) + 5) := by
    have h := oddForm (m + 5)
    rw [show 2 * (m + 5) + 1 = 2 * m + 11 by ring] at h
    push_cast at h
    linear_combination h
  have h1 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 10) : ℕ) : ℤ) = 3 * ((m : ℤ) + 5) ^ 4 + 10 * ((m : ℤ) + 5) ^ 3 + 6 * ((m : ℤ) + 5) ^ 2 - 7 * ((m : ℤ) + 5) := by
    have h := (evenForm (m + 5)).2
    rw [show 2 * (m + 5) = 2 * m + 10 by ring] at h
    push_cast at h
    linear_combination h
  have h2 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 9) : ℕ) : ℤ) = 3 * ((m : ℤ) + 4) ^ 4 + 16 * ((m : ℤ) + 4) ^ 3 + 24 * ((m : ℤ) + 4) ^ 2 + 5 * ((m : ℤ) + 4) := by
    have h := oddForm (m + 4)
    rw [show 2 * (m + 4) + 1 = 2 * m + 9 by ring] at h
    push_cast at h
    linear_combination h
  have h3 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 8) : ℕ) : ℤ) = 3 * ((m : ℤ) + 4) ^ 4 + 10 * ((m : ℤ) + 4) ^ 3 + 6 * ((m : ℤ) + 4) ^ 2 - 7 * ((m : ℤ) + 4) := by
    have h := (evenForm (m + 4)).2
    rw [show 2 * (m + 4) = 2 * m + 8 by ring] at h
    push_cast at h
    linear_combination h
  have h5 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 6) : ℕ) : ℤ) = 3 * ((m : ℤ) + 3) ^ 4 + 10 * ((m : ℤ) + 3) ^ 3 + 6 * ((m : ℤ) + 3) ^ 2 - 7 * ((m : ℤ) + 3) := by
    have h := (evenForm (m + 3)).2
    rw [show 2 * (m + 3) = 2 * m + 6 by ring] at h
    push_cast at h
    linear_combination h
  have h6 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 5) : ℕ) : ℤ) = 3 * ((m : ℤ) + 2) ^ 4 + 16 * ((m : ℤ) + 2) ^ 3 + 24 * ((m : ℤ) + 2) ^ 2 + 5 * ((m : ℤ) + 2) := by
    have h := oddForm (m + 2)
    rw [show 2 * (m + 2) + 1 = 2 * m + 5 by ring] at h
    push_cast at h
    linear_combination h
  have h7 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 4) : ℕ) : ℤ) = 3 * ((m : ℤ) + 2) ^ 4 + 10 * ((m : ℤ) + 2) ^ 3 + 6 * ((m : ℤ) + 2) ^ 2 - 7 * ((m : ℤ) + 2) := by
    have h := (evenForm (m + 2)).2
    rw [show 2 * (m + 2) = 2 * m + 4 by ring] at h
    push_cast at h
    linear_combination h
  have h8 : 6 * ((OMA.S_oeis_a203298.a (2 * m + 3) : ℕ) : ℤ) = 3 * ((m : ℤ) + 1) ^ 4 + 16 * ((m : ℤ) + 1) ^ 3 + 24 * ((m : ℤ) + 1) ^ 2 + 5 * ((m : ℤ) + 1) := by
    have h := oddForm (m + 1)
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring] at h
    push_cast at h
    linear_combination h
  linarith

end A203298

theorem OMA.solution : type_of% @OMA.S_oeis_a203298.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n _ he
    obtain ⟨m, rfl⟩ := he
    rw [← two_mul]
    have h := (A203298.evenForm m).2
    have hq : (6 : ℚ) * ((OMA.S_oeis_a203298.a (2 * m) : ℕ) : ℚ) =
        3 * (m : ℚ) ^ 4 + 10 * (m : ℚ) ^ 3 + 6 * (m : ℚ) ^ 2 - 7 * (m : ℚ) := by
      exact_mod_cast h
    rw [eq_div_iff (by norm_num)]
    push_cast
    linear_combination 32 * hq
  · intro n _ ho
    obtain ⟨m, rfl⟩ := ho
    have h := A203298.oddForm m
    have hq : (6 : ℚ) * ((OMA.S_oeis_a203298.a (2 * m + 1) : ℕ) : ℚ) =
        3 * (m : ℚ) ^ 4 + 16 * (m : ℚ) ^ 3 + 24 * (m : ℚ) ^ 2 + 5 * (m : ℚ) := by
      exact_mod_cast h
    rw [eq_div_iff (by norm_num)]
    push_cast
    linear_combination 32 * hq
  · intro n hn
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 10 ∨ n = 2 * m + 11 := ⟨(n - 10) / 2, by omega⟩
    rcases hm with rfl | rfl
    · rw [show 2 * m + 10 - 1 = 2 * m + 9 by omega, show 2 * m + 10 - 2 = 2 * m + 8 by omega,
        show 2 * m + 10 - 3 = 2 * m + 7 by omega, show 2 * m + 10 - 5 = 2 * m + 5 by omega,
        show 2 * m + 10 - 6 = 2 * m + 4 by omega, show 2 * m + 10 - 7 = 2 * m + 3 by omega,
        show 2 * m + 10 - 8 = 2 * m + 2 by omega]
      exact A203298.recE m
    · rw [show 2 * m + 11 - 1 = 2 * m + 10 by omega, show 2 * m + 11 - 2 = 2 * m + 9 by omega,
        show 2 * m + 11 - 3 = 2 * m + 8 by omega, show 2 * m + 11 - 5 = 2 * m + 6 by omega,
        show 2 * m + 11 - 6 = 2 * m + 5 by omega, show 2 * m + 11 - 7 = 2 * m + 4 by omega,
        show 2 * m + 11 - 8 = 2 * m + 3 by omega]
      exact A203298.recO m
