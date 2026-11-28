import OMAStatements.S_oeis_a121696
import Mathlib

open OMA.S_oeis_a121696 in
theorem OMA.solution : type_of% @OMA.S_oeis_a121696.main := by
  have hs : ∀ m : ℕ, a (m + 2) + a (m + 1) = ((m + 1).factorial : ℤ) * ↑((m + 3) / 2) := by
    intro m
    induction m with
    | zero => simp [a]
    | succ m ih =>
      rw [show m + 1 + 2 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring,
        show m + 1 + 3 = m + 4 by ring]
      rw [show a (m + 3) = a (m + 1) + ((m : ℤ) + 3) * (m + 1).factorial * ↑((m + 2) / 2) from rfl]
      rw [show (m + 4) / 2 = (m + 2) / 2 + 1 by omega, Nat.factorial_succ (m + 1)]
      have hq : (m + 3) / 2 + (m + 2) / 2 = m + 2 := by omega
      generalize (m + 3) / 2 = r at *
      generalize (m + 2) / 2 = q at *
      have hq' : (r : ℤ) + q = (m : ℤ) + 2 := by exact_mod_cast hq
      push_cast
      linear_combination ih + ((m + 1).factorial : ℤ) * hq'
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega]
  rw [show a (m + 4) = a (m + 2) + ((m : ℤ) + 1 + 3) * (m + 2).factorial * ↑((m + 3) / 2) from rfl,
    Nat.factorial_succ (m + 1)]
  have h := hs m
  generalize (m + 3) / 2 = r at *
  push_cast
  linear_combination (-((m : ℤ) + 4) * ((m : ℤ) + 2)) * h
