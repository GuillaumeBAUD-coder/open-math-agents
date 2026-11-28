import OMAStatements.S_oeis_a112700
import Mathlib

-- Problem: oeis-a112700
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof sketch: write c(k) = 6^k * catalan k, so a(n) = a(n-1) + c(n). Substituting
-- a(n) = a(n-2) + c(n-1) + c(n) and a(n-1) = a(n-2) + c(n-1), the a(n-2) terms cancel and the
-- recurrence reduces to (n+1) c(n) = 12 (2n-1) c(n-1), i.e. (n+1) C(n) = 2 (2n-1) C(n-1),
-- which follows from (n+1) C(n) = centralBinom n and the central binomial recurrence.

namespace OMA.Sol_a112700
open OMA.S_oeis_a112700

lemma catalan_step (m : ℕ) :
    ((m : ℤ) + 3) * (catalan (m + 2) : ℤ) = 2 * (2 * (m : ℤ) + 3) * (catalan (m + 1) : ℤ) := by
  have e1 := succ_mul_catalan_eq_centralBinom (m + 2)
  have e2 := succ_mul_catalan_eq_centralBinom (m + 1)
  have e3 := Nat.succ_mul_centralBinom_succ (m + 1)
  have key : (m + 2) * ((m + 3) * catalan (m + 2)) = (m + 2) * (2 * (2 * m + 3) * catalan (m + 1)) := by
    have : (m + 2 + 1) * catalan (m + 2) = Nat.centralBinom (m + 2) := e1
    have h4 : (m + 1 + 1) * catalan (m + 1) = Nat.centralBinom (m + 1) := e2
    calc (m + 2) * ((m + 3) * catalan (m + 2)) = (m + 1 + 1) * Nat.centralBinom (m + 1 + 1) := by
          rw [← this]
      _ = 2 * (2 * (m + 1) + 1) * Nat.centralBinom (m + 1) := e3
      _ = (m + 2) * (2 * (2 * m + 3) * catalan (m + 1)) := by rw [← h4]; ring
  have := Nat.eq_of_mul_eq_mul_left (by omega) key
  exact_mod_cast this

end OMA.Sol_a112700

open OMA.S_oeis_a112700 in
theorem OMA.solution : type_of% @OMA.S_oeis_a112700.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 2 - 2 = m := by omega
  rw [h1, h2]
  have s1 : (a (m + 1) : ℤ) = a m + 6 ^ (m + 1) * catalan (m + 1) := by
    simp only [a, Finset.sum_range_succ (n := m + 1)]; push_cast; ring
  have s2 : (a (m + 2) : ℤ) = a (m + 1) + 6 ^ (m + 2) * catalan (m + 2) := by
    simp only [a, Finset.sum_range_succ (n := m + 2)]; push_cast; ring
  have k := OMA.Sol_a112700.catalan_step m
  rw [s2, s1]
  push_cast
  linear_combination (6 : ℤ) ^ (m + 2) * k
