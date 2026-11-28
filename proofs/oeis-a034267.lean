import OMAStatements.S_oeis_a034267
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: C(2n,n+1)=centralBinom(n)*n/(n+1) and (n+1)centralBinom(n+1)=2(2n+1)centralBinom(n); then field_simp and ring. No computer search.

namespace OMA.A034267Proof

open OMA.S_oeis_a034267
-- C(2n, n+1) * (n+1) = centralBinom n * n
theorem c_eq (n : ℕ) : ((2 * n).choose (n + 1) : ℚ) = (n.centralBinom : ℚ) * n / (n + 1) := by
  have h := Nat.choose_succ_right_eq (2 * n) n
  rw [show 2 * n - n = n by omega] at h
  rw [eq_div_iff (by positivity), Nat.centralBinom]
  exact_mod_cast h

theorem cb (n : ℕ) : ((n + 1).centralBinom : ℚ) = 2 * (2 * n + 1) * n.centralBinom / (n + 1) := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [eq_div_iff (by positivity)]
  have h' : ((n + 1 : ℕ) : ℚ) * ((n + 1).centralBinom : ℚ) = 2 * (2 * n + 1) * n.centralBinom := by exact_mod_cast h
  push_cast at h'; linarith

theorem mainP : ∀ n : ℕ, 2 ≤ n → -(((n : ℚ) + 2) * (11 * (n : ℚ) - 7)) * a n + 2 * (23 * (n : ℚ) ^ 2 + 44 * (n : ℚ) + 30) * a (n - 1) - 4 * ((n : ℚ) + 5) * (2 * (n : ℚ) - 3) * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  simp only [a, c_eq]
  rw [cb (m + 1), cb m]
  push_cast
  field_simp
  ring

end OMA.A034267Proof

open OMA.A034267Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a034267.main := mainP
