import OMAStatements.S_oeis_a005251
import Mathlib

open OMA.S_oeis_a005251

lemma OMA.key (n : ℕ) :
    (a (n + 1) + (-1) ^ n * b n = 2 * c (n + 1) ∧
      a (n + 2) + (-1) ^ (n + 1) * b (n + 1) = 2 * c (n + 2) ∧
      a (n + 3) + (-1) ^ (n + 2) * b (n + 2) = 2 * c (n + 3)) ∧
    (1 ≤ (-1) ^ n * b n ∧ (-1) ^ n * b n ≤ (-1) ^ (n + 1) * b (n + 1) ∧
      (-1) ^ (n + 1) * b (n + 1) ≤ (-1) ^ (n + 2) * b (n + 2)) := by
  induction n with
  | zero => decide
  | succ m ih =>
    obtain ⟨⟨h1, h2, h3⟩, ⟨g1, g2, g3⟩⟩ := ih
    have ea : a (m + 1 + 3) = 2 * a (m + 3) - a (m + 2) + a (m + 1) := rfl
    have eb : b (m + 1 + 2) = -2 * b (m + 2) - b (m + 1) - b m := rfl
    have ec : c (m + 1 + 3) = 2 * c (m + 3) - c (m + 2) + c (m + 1) := rfl
    have p1 : ((-1 : ℤ)) ^ (m + 1 + 2) = -(-1) ^ (m + 2) := by ring
    have p2 : ((-1 : ℤ)) ^ (m + 2) = -(-1) ^ (m + 1) := by ring
    have p3 : ((-1 : ℤ)) ^ (m + 1) = -(-1) ^ m := by ring
    refine ⟨⟨h2, h3, ?_⟩, ⟨by linarith, g3, ?_⟩⟩
    · rw [ea, ec, eb, p1, p2, p3]
      rw [p2, p3] at h3
      rw [p3] at h2
      linear_combination 2 * h3 - h2 + h1
    · rw [show m + 1 + 1 = m + 2 by ring, eb, p1, p2, p3]
      rw [p2, p3] at g3
      rw [p3] at g2
      nlinarith [g1, g2, g3]

theorem OMA.solution : type_of% @OMA.S_oeis_a005251.main := by
  intro n
  obtain ⟨⟨h, -, -⟩, ⟨g, -, -⟩⟩ := OMA.key n
  have : |b n| = (-1) ^ n * b n := by
    rcases neg_one_pow_eq_or ℤ n with e | e <;> rw [e] at g ⊢
    · simp only [one_mul] at g ⊢; exact abs_of_nonneg (by linarith)
    · rw [abs_of_nonpos (by linarith)]; ring
  rw [this]; exact h
