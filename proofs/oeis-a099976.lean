import OMAStatements.S_oeis_a099976
import Mathlib

namespace A099976
open OMA.S_oeis_a099976

lemma a_eq (n : ℕ) : a n = (2 * n + 1).centralBinom := by
  unfold a
  rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (2 * n + 1) = 4 * n + 2 by ring]

lemma cb_step (k : ℕ) :
    ((k : ℤ) + 1) * ((k + 1).centralBinom : ℤ) = 2 * (2 * (k : ℤ) + 1) * (k.centralBinom : ℤ) := by
  have h := Nat.succ_mul_centralBinom_succ k
  have h' : (((k + 1) * (k + 1).centralBinom : ℕ) : ℤ) = ((2 * (2 * k + 1) * k.centralBinom : ℕ) : ℤ) := by
    rw [h]
  push_cast at h'
  exact h'

end A099976

theorem OMA.solution : type_of% @OMA.S_oeis_a099976.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega, A099976.a_eq, A099976.a_eq,
    show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by ring]
  have h1 := A099976.cb_step (2 * m + 2)
  have h2 := A099976.cb_step (2 * m + 1)
  rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring] at h2
  push_cast at h1 h2 ⊢
  linear_combination ((m : ℤ) + 1) * h1 + (4 * (m : ℤ) + 5) * h2
