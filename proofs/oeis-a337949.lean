import OMAStatements.S_oeis_a337949
import Mathlib

namespace OMA.P_oeis_a337949

open OMA.S_oeis_a337949

theorem two_pow_mod (m : ℕ) : 2 ^ m % 3 = 1 + m % 2 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    have : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
    interval_cases h : m % 2 <;> omega

theorem case1 (k : ℕ) : a (2 * k + 1) % 3 = 0 := by
  have e1 : (2 * k + 1) * (2 * k + 1 - 1) / 2 = (2 * k + 1) * k := by
    rw [show 2 * k + 1 - 1 = 2 * k by omega, show (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) by ring]
    omega
  have e2 : (2 * k + 1) * (2 * k + 1 + 1) / 2 = (2 * k + 1) * (k + 1) := by
    rw [show (2 * k + 1) * (2 * k + 1 + 1) = 2 * ((2 * k + 1) * (k + 1)) by ring]
    omega
  unfold a
  rw [if_neg (by omega), e1, e2, Nat.add_mod, two_pow_mod, two_pow_mod, Nat.mul_mod,
    Nat.mul_mod (2 * k + 1)]
  have : (2 * k + 1) % 2 = 1 := by omega
  rw [this]
  have : k % 2 < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases h : k % 2 <;> omega

theorem case2 (k : ℕ) : a (4 * k + 2) % 3 = 1 := by
  have e1 : (4 * k + 2) * (4 * k + 2 - 1) / 2 = (2 * k + 1) * (4 * k + 1) := by
    rw [show 4 * k + 2 - 1 = 4 * k + 1 by omega,
      show (4 * k + 2) * (4 * k + 1) = 2 * ((2 * k + 1) * (4 * k + 1)) by ring]
    omega
  have e2 : (4 * k + 2) * (4 * k + 2 + 1) / 2 = (2 * k + 1) * (4 * k + 3) := by
    rw [show (4 * k + 2) * (4 * k + 2 + 1) = 2 * ((2 * k + 1) * (4 * k + 3)) by ring]
    omega
  unfold a
  rw [if_neg (by omega), e1, e2, Nat.add_mod, two_pow_mod, two_pow_mod, Nat.mul_mod,
    Nat.mul_mod (2 * k + 1)]
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (4 * k + 1) % 2 = 1 := by omega
  have h3 : (4 * k + 3) % 2 = 1 := by omega
  rw [h1, h2, h3]

theorem case3 (k : ℕ) : a (4 * k + 4) % 3 = 2 := by
  have e1 : (4 * k + 4) * (4 * k + 4 - 1) / 2 = (2 * k + 2) * (4 * k + 3) := by
    rw [show 4 * k + 4 - 1 = 4 * k + 3 by omega,
      show (4 * k + 4) * (4 * k + 3) = 2 * ((2 * k + 2) * (4 * k + 3)) by ring]
    omega
  have e2 : (4 * k + 4) * (4 * k + 4 + 1) / 2 = (2 * k + 2) * (4 * k + 5) := by
    rw [show (4 * k + 4) * (4 * k + 4 + 1) = 2 * ((2 * k + 2) * (4 * k + 5)) by ring]
    omega
  unfold a
  rw [if_neg (by omega), e1, e2, Nat.add_mod, two_pow_mod, two_pow_mod, Nat.mul_mod,
    Nat.mul_mod (2 * k + 2)]
  have h1 : (2 * k + 2) % 2 = 0 := by omega
  rw [h1]
  simp

end OMA.P_oeis_a337949

theorem OMA.solution : type_of% @OMA.S_oeis_a337949.main := by
  intro n
  exact ⟨OMA.P_oeis_a337949.case1 n, OMA.P_oeis_a337949.case2 n, OMA.P_oeis_a337949.case3 n⟩
