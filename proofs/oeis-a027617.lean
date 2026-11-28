import OMAStatements.S_oeis_a027617
import Mathlib

namespace OMA.S_oeis_a027617

noncomputable def T (m : ℕ) : ℚ := 1 - ∑ k ∈ Finset.range (m + 1), (-1 : ℚ) ^ k / (3 ^ k * (k.factorial : ℚ))

lemma S_eq (k : ℕ) : S k = 3 ^ k * (k.factorial : ℚ) * T k := by
  induction k with
  | zero => simp [S, T]
  | succ k ih =>
    have hT : T (k + 1) = T k - (-1 : ℚ) ^ (k + 1) / (3 ^ (k + 1) * ((k + 1).factorial : ℚ)) := by
      unfold T
      rw [Finset.sum_range_succ _ (k + 1)]
      ring
    rw [S, ih, hT, Nat.factorial_succ]
    push_cast
    have h3 : (3 : ℚ) ^ (k + 1) ≠ 0 := by positivity
    have hf : ((k.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    ring

lemma S_pos (k : ℕ) : 1 ≤ S (k + 1) := by
  induction k with
  | zero => simp [S]
  | succ k ih =>
    rw [S]
    have : (-1 : ℚ) ^ (k + 1 + 1) ≤ 1 := by
      rcases neg_one_pow_eq_or ℚ (k + 1 + 1) with h | h <;> rw [h] <;> norm_num
    have hk : (1 : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    push_cast at *
    nlinarith

lemma a_eq (n : ℕ) : a n = (n.factorial : ℚ) * T (n / 3) := by
  unfold a T; rfl

end OMA.S_oeis_a027617

theorem OMA.solution : type_of% @OMA.S_oeis_a027617.main := by
  refine ⟨?_, ?_⟩
  · intro n hn h3
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [OMA.S_oeis_a027617.a_eq, OMA.S_oeis_a027617.a_eq, Nat.factorial_succ]
    have : (m + 1) / 3 = m / 3 := by omega
    rw [this]; push_cast; ring
  · intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have e1 : 3 * (m + 2) - 1 = 3 * m + 5 := by omega
    have e2 : m + 2 - 1 = m + 1 := by omega
    rw [e1, e2, OMA.S_oeis_a027617.a_eq, OMA.S_oeis_a027617.a_eq]
    have d1 : 3 * (m + 2) / 3 = m + 2 := by omega
    have d2 : (3 * m + 5) / 3 = m + 1 := by omega
    rw [d1, d2]
    have hS := OMA.S_oeis_a027617.S_eq
    have hp := OMA.S_oeis_a027617.S_pos m
    have hTne : OMA.S_oeis_a027617.T (m + 1) ≠ 0 := by
      intro h
      have := hS (m + 1)
      rw [h] at this; rw [this] at hp; simp at hp; linarith
    rw [hS (m + 2), hS (m + 1)]
    have e3 : 3 * (m + 2) = (3 * m + 5) + 1 := by omega
    rw [e3, Nat.factorial_succ]
    have h3 : (3 : ℚ) ^ (m + 1) ≠ 0 := by positivity
    have hf : (((m + 1).factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
    push_cast
    rw [Nat.factorial_succ (m + 1)]
    push_cast
    ring
