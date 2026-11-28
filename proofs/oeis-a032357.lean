import OMAStatements.S_oeis_a032357
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

lemma OMA.st (n : ℕ) : OMA.S_oeis_a032357.a (n + 1) = (catalan (n + 1) : ℤ) - OMA.S_oeis_a032357.a n := by
  simp only [OMA.S_oeis_a032357.a]
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul]
  have : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + 1 - k) * (catalan k : ℤ) =
      -∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (catalan k : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
    ring
  rw [this]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a032357.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have s2 := OMA.st (m + 1)
  have s1 := OMA.st m
  have r1 := OMA.cr (m + 1)
  push_cast at r1 ⊢
  rw [show m + 1 + 1 = m + 2 by ring] at s2 r1
  linear_combination ((m : ℤ) + 2 + 1) * s2 - 2 * (2 * ((m : ℤ) + 2) - 1) * s1 + r1
