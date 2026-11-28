import OMAStatements.S_oeis_a329725
import Mathlib

open OMA.S_oeis_a329725

namespace OMA.P_oeis_a329725

lemma p_ten (n : ℕ) (hn : 0 < n) : p (10 * n) = p n := by
  unfold p
  rw [Nat.digits_def' (by norm_num) (by omega)]
  simp [Nat.mul_mod_right, Nat.mul_div_cancel_left n (by norm_num : 0 < 10)]

lemma p_ten_one (n : ℕ) : p (10 * n + 1) = p n := by
  unfold p
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (10 * n + 1) % 10 = 1 := by omega
  have h2 : (10 * n + 1) / 10 = n := by omega
  simp [h1, h2]

end OMA.P_oeis_a329725

open OMA.P_oeis_a329725 in
theorem OMA.solution : type_of% @OMA.S_oeis_a329725.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : 10 * (m + 1) + 1 = (10 * m + 9) + 2 := by ring
  have e2 : 10 * (m + 1) - 1 = 10 * m + 9 := by omega
  have e3 : a (10 * m + 9 + 1) = ((10 * m + 10 : ℕ) : ℤ) - p (10 * (m + 1)) - a (10 * m + 9) := by
    rw [show 10 * m + 9 + 1 = (10 * m + 8) + 2 by ring, a]
    rw [show 10 * m + 8 + 2 = 10 * (m + 1) by ring, show 10 * m + 8 + 1 = 10 * m + 9 by ring]
  rw [e1, e2, a, e3, show 10 * m + 9 + 2 = 10 * (m + 1) + 1 by ring, p_ten_one, p_ten _ (by omega)]
  push_cast; ring

