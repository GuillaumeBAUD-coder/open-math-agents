import OMAStatements.S_oeis_a029795
import Mathlib

namespace OMA.A029795Proof

open OMA.S_oeis_a029795

theorem digits_mul_pow (d j : ℕ) (hd : 0 < d) (hd10 : d < 10) :
    Nat.digits 10 (d * 10 ^ j) = List.replicate j 0 ++ [d] := by
  induction j with
  | zero => simp [Nat.digits_of_lt 10 d hd.ne' hd10]
  | succ j ih =>
    have hpos : 0 < d * 10 ^ (j + 1) := by positivity
    rw [Nat.digits_def' (by norm_num) hpos]
    have h1 : d * 10 ^ (j + 1) % 10 = 0 := by
      rw [pow_succ, ← mul_assoc]; exact Nat.mul_mod_left _ _
    have h2 : d * 10 ^ (j + 1) / 10 = d * 10 ^ j := by
      rw [pow_succ, ← mul_assoc]; exact Nat.mul_div_cancel _ (by norm_num)
    rw [h1, h2, ih, List.replicate_succ, List.cons_append]

theorem P_pow (j : ℕ) : P (10 ^ (j + 1)) := by
  unfold P
  have e1 := digits_mul_pow 1 (j + 1) (by norm_num) (by norm_num)
  have e2 := digits_mul_pow 1 (3 * j + 3) (by norm_num) (by norm_num)
  rw [one_mul] at e1 e2
  rw [← pow_mul, show (j + 1) * 3 = 3 * j + 3 by ring, e1, e2]
  ext x
  simp only [List.mem_toFinset, List.mem_append, List.mem_replicate, List.mem_singleton]
  constructor <;> rintro (⟨_, h⟩ | h) <;> first | (left; exact ⟨by omega, h⟩) | (right; exact h)

theorem not_P (j : ℕ) : ¬ P (2 * 10 ^ j) := by
  unfold P
  intro h
  have e1 := digits_mul_pow 2 j (by norm_num) (by norm_num)
  have e2 := digits_mul_pow 8 (3 * j) (by norm_num) (by norm_num)
  have hc : (2 * 10 ^ j) ^ 3 = 8 * 10 ^ (3 * j) := by ring
  rw [hc, e1, e2] at h
  have h2 : (2 : ℕ) ∈ (List.replicate j 0 ++ [2]).toFinset := by simp
  rw [h] at h2
  simp [List.mem_replicate] at h2

theorem P_infinite : {k : ℕ | P k}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun j : ℕ => 10 ^ (j + 1))
  · intro i j hij
    simp only at hij
    have h := Nat.pow_right_injective (by norm_num : 2 ≤ 10) hij
    omega
  · intro j; exact P_pow j

end OMA.A029795Proof

open OMA.A029795Proof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a029795.main) := by
  rintro ⟨m, N, h⟩
  set j := m + N with hj
  have hlt : j < 10 ^ j := Nat.lt_pow_self (by norm_num)
  set k := 2 * 10 ^ j with hk
  have hn : N ≤ k - m := by omega
  have h1 : 1 ≤ k - m := by omega
  have e := h (k - m) hn
  have hmem : OMA.S_oeis_a029795.P (Nat.nth OMA.S_oeis_a029795.P (k - m - 1)) := Nat.nth_mem_of_infinite P_infinite _
  unfold OMA.S_oeis_a029795.a at e
  rw [e, show m + (k - m) = k by omega] at hmem
  exact not_P j hmem
