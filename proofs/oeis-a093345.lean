import OMAStatements.S_oeis_a093345
import Mathlib

open Finset

theorem OMA.solution : type_of% @OMA.S_oeis_a093345.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  simp only [OMA.S_oeis_a093345.a]
  set E : ℕ → ℚ := fun i => ∑ j ∈ range i, 1 / (j.factorial : ℚ) with hE
  set H : ℕ → ℚ := fun n => ∑ i ∈ Icc 1 n, (1 / (i : ℚ)) * E i with hH
  have hH1 : ∀ k, H (k + 1) = H k + (1 / ((k + 1 : ℕ) : ℚ)) * E (k + 1) := by
    intro k; simp only [hH]; rw [Finset.sum_Icc_succ_top (by omega)]
  have hE1 : ∀ k, E (k + 1) = E k + 1 / (k.factorial : ℚ) := by
    intro k; simp only [hE]; rw [Finset.sum_range_succ]
  show ((m + 3).factorial : ℚ) * (1 + H (m + 3)) - 2 * ((m + 3 : ℕ) : ℚ) *
      (((m + 2).factorial : ℚ) * (1 + H (m + 2))) + (((m + 3 : ℕ) : ℚ) ^ 2 - 2) *
      (((m + 1).factorial : ℚ) * (1 + H (m + 1))) - (((m + 3 : ℕ) : ℚ) - 2) ^ 2 *
      ((m.factorial : ℚ) * (1 + H m)) = 0
  rw [show m + 3 = (m + 2) + 1 by ring, hH1 (m + 2), show m + 2 = (m + 1) + 1 by ring, hH1 (m + 1),
    hH1 m, hE1 (m + 1 + 1), hE1 (m + 1), Nat.factorial_succ (m + 1 + 1), Nat.factorial_succ (m + 1),
    Nat.factorial_succ m]
  have : (m.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
