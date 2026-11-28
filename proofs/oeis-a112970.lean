import OMAStatements.S_oeis_a112970
import Mathlib

-- Problem: oeis-a112970

namespace OMA.P112970
open OMA.S_oeis_a112970

theorem a0 : a 0 = 1 := by simp [a]
theorem a1 : a 1 = 1 := by simp [a]
theorem a2 : a 2 = 1 := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, a]
  simp [a1]

theorem a_odd' (k : ℕ) : a (2 * k + 1) = a k := by
  cases k with
  | zero => rw [show 2 * 0 + 1 = 1 from rfl, a0, a1]
  | succ j =>
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, a, if_pos (by omega)]
    congr 1
    omega

theorem a_odd (k : ℕ) (_hk : True) : a (2 * k + 1) = a k := a_odd' k

theorem a_even (k : ℕ) (hk : 2 ≤ k) : a (2 * k) = a k + a (k - 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show 2 * (j + 1) = (2 * j) + 2 by ring, a, if_neg (by omega)]
  have e1 : (2 * j + 2) / 2 = j + 1 := by omega
  rw [e1, if_pos hk]

theorem pc : ∀ n : ℕ, a (2 ^ n - 1) = 1 := by
  intro n
  induction n with
  | zero => exact a0
  | succ n ih =>
    cases n with
    | zero => exact a1
    | succ m =>
      have hp : 2 ≤ 2 ^ (m + 1) := by
        have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        rw [pow_succ]; omega
      rw [show 2 ^ (m + 1 + 1) - 1 = 2 * (2 ^ (m + 1) - 1) + 1 by rw [pow_succ 2 (m + 1)]; omega,
        a_odd _ trivial]
      exact ih

theorem pd : ∀ n : ℕ, a (3 * 2 ^ n - 1) = 1 := by
  intro n
  induction n with
  | zero => exact a2
  | succ n ih =>
    have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [show 3 * 2 ^ (n + 1) - 1 = 2 * (3 * 2 ^ n - 1) + 1 by rw [pow_succ]; omega,
      a_odd _ trivial]
    exact ih

theorem pu : ∀ n : ℕ, a (2 ^ (n + 1) - 2) = (n + 2) / 2 ∧ a (2 ^ (n + 2) - 2) = (n + 3) / 2 := by
  intro n
  induction n with
  | zero => exact ⟨a0, a2⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have e1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    have e2 : 2 ^ (n + 2) = 4 * 2 ^ n := by rw [pow_succ, e1]; ring
    have e3 : 2 ^ (n + 1 + 2) = 8 * 2 ^ n := by rw [pow_succ, e2]; ring
    rw [show 2 ^ (n + 1 + 2) - 2 = 2 * (2 ^ (n + 2) - 1) by omega, a_even _ (by omega), pc,
      show 2 ^ (n + 2) - 1 - 2 = 2 * (2 ^ (n + 1) - 2) + 1 by omega, a_odd _ trivial, h1]
    omega

theorem pa : ∀ n : ℕ, a (2 ^ n) = n ^ 2 / 4 + 1 ∧ a (2 ^ (n + 1)) = (n + 1) ^ 2 / 4 + 1 := by
  intro n
  induction n with
  | zero => exact ⟨a1, a2⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have e1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    rw [show 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) by rw [pow_succ]; ring, a_even _ (by omega), h2,
      (pu n).1]
    rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
    · have s1 : (2 * j + 1) ^ 2 = 4 * (j ^ 2 + j) + 1 := by ring
      have s2 : (2 * j + 1 + 1) ^ 2 = 4 * (j ^ 2 + 2 * j + 1) := by ring
      rw [s1, s2]
      omega
    · have s1 : (2 * j + 1 + 1) ^ 2 = 4 * (j ^ 2 + 2 * j + 1) := by ring
      have s2 : (2 * j + 1 + 1 + 1) ^ 2 = 4 * (j ^ 2 + 3 * j + 2) + 1 := by ring
      rw [s1, s2]
      omega

end OMA.P112970

theorem OMA.solution : type_of% @OMA.S_oeis_a112970.main := by
  intro n
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  refine ⟨(OMA.P112970.pa n).1, ?_, OMA.P112970.pc n, OMA.P112970.pd n⟩
  rw [show 2 ^ (n + 1) + 1 = 2 * 2 ^ n + 1 by rw [pow_succ]; ring, OMA.P112970.a_odd _ trivial]
  exact (OMA.P112970.pa n).1
