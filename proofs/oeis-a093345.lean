import OMAStatements.S_oeis_a093345
import Mathlib

-- Problem: oeis-a093345
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P093345
open OMA.S_oeis_a093345

def E (i : ℕ) : ℚ := ∑ j ∈ Finset.range i, 1 / (j.factorial : ℚ)
def T (n : ℕ) : ℚ := 1 + ∑ i ∈ Finset.Icc 1 n, (1 / (i : ℚ)) * E i

lemma a_eq (n : ℕ) : a n = (n.factorial : ℚ) * T n := rfl

lemma E_succ (i : ℕ) : E (i + 1) = E i + 1 / (i.factorial : ℚ) := by
  unfold E; rw [Finset.sum_range_succ]

lemma T_succ (n : ℕ) : T (n + 1) = T n + (1 / ((n + 1 : ℕ) : ℚ)) * E (n + 1) := by
  unfold T; rw [Finset.sum_Icc_succ_top (by omega)]; ring

theorem sol : type_of% @OMA.S_oeis_a093345.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = (m + 1) + 1 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega, show m + 3 = ((m + 1) + 1) + 1 by omega]
  rw [a_eq, a_eq, a_eq, a_eq]
  simp only [T_succ, E_succ]
  rw [Nat.factorial_succ (m + 1 + 1), Nat.factorial_succ (m + 1), Nat.factorial_succ m]
  have h : (m.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end OMA.P093345

theorem OMA.solution : type_of% @OMA.S_oeis_a093345.main := OMA.P093345.sol
