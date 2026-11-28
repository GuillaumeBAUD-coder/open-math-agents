import OMAStatements.S_oeis_a027617
import Mathlib

open OMA.S_oeis_a027617

namespace P027617

noncomputable def s (k : ℕ) : ℚ := ∑ j ∈ Finset.range (k + 1), (-1 : ℚ) ^ j / (3 ^ j * (j.factorial : ℚ))

theorem Sform : ∀ k, S k = 3 ^ k * (k.factorial : ℚ) * (1 - s k) := by
  intro k
  induction k with
  | zero => simp [S, s]
  | succ k ih =>
    rw [S, ih]
    simp only [s]
    rw [Finset.sum_range_succ _ (k + 1), Nat.factorial_succ]
    push_cast
    have h1 : (3 : ℚ) ^ (k + 1) ≠ 0 := by positivity
    have h2 : (k.factorial : ℚ) ≠ 0 := by positivity
    field_simp
    ring

theorem Spos : ∀ k, 1 ≤ k → 1 ≤ S k := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp [S]
    · have := ih h
      rw [S]
      have hp : (-1 : ℚ) ^ (k + 1) ≤ 1 := by
        rcases neg_one_pow_eq_or ℚ (k + 1) with h' | h' <;> rw [h'] <;> norm_num
      have : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast h
      nlinarith

theorem a_eq (n : ℕ) : a n = (n.factorial : ℚ) * (1 - s (n / 3)) := rfl

end P027617

theorem OMA.solution : type_of% @OMA.S_oeis_a027617.main := by
  constructor
  · intro n hn h3
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [P027617.a_eq, P027617.a_eq, show m + 1 - 1 = m by omega, show (m + 1) / 3 = m / 3 by omega,
      Nat.factorial_succ]
    push_cast
    ring
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hS := P027617.Spos (j + 2 - 1) (by omega)
    rw [show j + 2 - 1 = j + 1 by omega] at hS ⊢
    rw [P027617.a_eq, P027617.a_eq, show 3 * (j + 2) - 1 = 3 * j + 5 by omega,
      show 3 * (j + 2) / 3 = j + 2 by omega, show (3 * j + 5) / 3 = j + 1 by omega,
      P027617.Sform, P027617.Sform]
    rw [P027617.Sform] at hS
    have hne : (1 - P027617.s (j + 1)) ≠ 0 := by
      intro h; rw [h, mul_zero] at hS; norm_num at hS
    rw [show 3 * (j + 2) = (3 * j + 5) + 1 by ring, Nat.factorial_succ,
      show j + 2 = (j + 1) + 1 by ring, Nat.factorial_succ (j + 1)]
    push_cast
    have h1 : ((j + 1).factorial : ℚ) ≠ 0 := by positivity
    field_simp
    ring
