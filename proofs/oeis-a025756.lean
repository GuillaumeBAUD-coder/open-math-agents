import OMAStatements.S_oeis_a025756
import Mathlib

namespace A025756Aux
open OMA.S_oeis_a025756

lemma choose_step (r : ℚ) (k : ℕ) :
    ((k + 1 : ℕ) : ℚ) * Ring.choose r (k + 1) = (r - k) * Ring.choose r k := by
  have h := Ring.choose_smul_choose r (Nat.le_add_right k 1)
  rw [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right,
    nsmul_eq_mul] at h
  rw [h]; ring

lemma term_step (r : ℚ) (k : ℕ) :
    ((k + 1 : ℕ) : ℚ) * term r (k + 1) = -9 * (r - k) * term r k := by
  unfold term
  have h := choose_step r k
  rw [pow_succ]
  linear_combination (-9 : ℚ) ^ k * (-9) * h

lemma a_step (k : ℕ) : a (k + 1) = a k + d (k + 1) / 3 := by
  unfold a
  rw [Finset.sum_range_succ _ (k + 1)]; ring
end A025756Aux

open OMA.S_oeis_a025756 A025756Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a025756.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  have E1a := term_step (2 / 3) (m + 1)
  have E2a := term_step (2 / 3) (m + 2)
  have E1b := term_step (1 / 3) (m + 1)
  have E2b := term_step (1 / 3) (m + 2)
  rw [a_step (m + 2), a_step (m + 1), a_step m]
  unfold d
  push_cast at E1a E2a E1b E2b ⊢
  linear_combination (1 / 3 : ℚ) * (((m : ℚ) + 2) * E2a + (-9) * (2 / 3 + (m : ℚ)) * E1a) +
    (-2 / 3 : ℚ) * (((m : ℚ) + 2) * E2b + (-9) * (1 / 3 + (m : ℚ)) * E1b)
