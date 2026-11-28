import OMAStatements.S_oeis_a092634
import Mathlib

lemma OMA.cl (n : ℕ) : OMA.S_oeis_a092634.a (n + 1) = 3 - ((n + 2).factorial : ℤ) := by
  induction n with
  | zero => decide
  | succ m ih =>
    simp only [OMA.S_oeis_a092634.a] at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega)]
    have : ((m + 1 + 2).factorial : ℤ) = (m + 3) * ((m + 2).factorial : ℤ) := by
      rw [show m + 1 + 2 = (m + 2) + 1 by ring, Nat.factorial_succ]; push_cast; ring
    rw [this]
    push_cast
    linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a092634.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 + 1 := ⟨n - 5, by omega⟩
  rw [show m + 4 + 1 - 1 = m + 3 + 1 by omega, show m + 4 + 1 - 2 = m + 2 + 1 by omega,
    show m + 4 + 1 - 3 = m + 1 + 1 by omega, OMA.cl, OMA.cl, OMA.cl, OMA.cl]
  simp only [show m + 4 + 2 = m + 5 + 1 by ring, show m + 3 + 2 = m + 4 + 1 by ring,
    show m + 2 + 2 = m + 3 + 1 by ring, show m + 1 + 2 = m + 2 + 1 by ring,
    show m + 5 = m + 4 + 1 by ring, show m + 4 = m + 3 + 1 by ring, Nat.factorial_succ]
  push_cast
  ring
