import OMAStatements.S_oeis_a185020
import Mathlib

lemma OMA.cr (k : ℕ) : ((k + 2 : ℕ) : ℤ) * (catalan (k + 1) : ℤ) = 2 * (2 * k + 1) * (catalan k : ℤ) := by
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  have e : ((k + 1 : ℕ) : ℤ) * (((k + 2 : ℕ) : ℤ) * (catalan (k + 1) : ℤ)) =
      ((k + 1 : ℕ) : ℤ) * (2 * (2 * k + 1) * (catalan k : ℤ)) := by
    have : ((k + 1 : ℕ) : ℤ) * ((k + 1).centralBinom : ℤ) =
        2 * (2 * k + 1) * (k.centralBinom : ℤ) := by exact_mod_cast h3
    rw [← h1, ← h2] at this
    push_cast at this ⊢
    linear_combination this
  exact mul_left_cancel₀ (by positivity) e

theorem OMA.solution : type_of% @OMA.S_oeis_a185020.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  simp only [OMA.S_oeis_a185020.a]
  have r1 := OMA.cr (m + 1)
  have r0 := OMA.cr m
  have s3 : OMA.S_oeis_a185020.s (m + 2 + 1) =
      2 * OMA.S_oeis_a185020.s (m + 1 + 1) + 2 * OMA.S_oeis_a185020.s (m + 1) := by
    rw [show m + 2 + 1 = (m + 1) + 2 by ring]; rfl
  push_cast at r1 r0 ⊢
  rw [show m + 1 + 1 = m + 2 by ring] at r1 s3
  linear_combination ((m : ℤ) + 2) * OMA.S_oeis_a185020.s (m + 2 + 1) * r1 +
    ((m : ℤ) + 2) * (2 * (2 * ((m : ℤ) + 1) + 1)) * (catalan (m + 1) : ℤ) * s3 +
    4 * (2 * (m : ℤ) + 3) * OMA.S_oeis_a185020.s (m + 1) * r0
