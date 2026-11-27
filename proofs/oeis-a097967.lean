import OMAStatements.S_oeis_a097967
import Mathlib

-- Problem: oeis-a097967
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P097967
open OMA.S_oeis_a097967

lemma shift (f : ℕ → ℤ) (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

def P (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, (n.descFactorial (k + 1) : ℤ)

lemma P_succ (n : ℕ) : P (n + 1) = ((n : ℤ) + 1) * (P n + 1) := by
  unfold P
  have : ∀ k ∈ Finset.range (n + 1), (((n + 1).descFactorial (k + 1) : ℕ) : ℤ)
      = ((n : ℤ) + 1) * ((n.descFactorial k : ℕ) : ℤ) := by
    intro k _
    rw [Nat.succ_descFactorial_succ]; push_cast; ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_range_succ']
  simp [add_comm]

lemma Q_eq (n : ℕ) : ∑ k ∈ Finset.range n, ((n.choose (k + 1) : ℕ) : ℤ) = 2 ^ n - 1 := by
  have h := Nat.sum_range_choose n
  rw [Finset.sum_range_succ'] at h
  have h' : ((∑ k ∈ Finset.range n, n.choose (k + 1) + n.choose 0 : ℕ) : ℤ) = ((2 ^ n : ℕ) : ℤ) := by
    rw [h]
  push_cast at h'
  simp at h'
  linarith

lemma a_eq (n : ℕ) : a n = P n + 2 ^ n - 1 := by
  unfold a
  rw [shift, Finset.sum_add_distrib, Q_eq]
  unfold P
  ring

theorem sol : type_of% @OMA.S_oeis_a097967.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega]
  simp only [a_eq, show m + 5 = (m + 4) + 1 by ring, show m + 4 = (m + 3) + 1 by ring,
    show m + 3 = (m + 2) + 1 by ring, show m + 2 = (m + 1) + 1 by ring, P_succ, pow_succ]
  push_cast
  ring

end OMA.P097967

theorem OMA.solution : type_of% @OMA.S_oeis_a097967.main := OMA.P097967.sol
