import OMAStatements.S_oeis_a004171
import Mathlib

open OMA.S_oeis_a004171 in
theorem OMA.solution : type_of% @OMA.S_oeis_a004171.main := by
  intro x n t _ ht h
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  refine ⟨t, Nat.lt_succ_self t, ?_⟩
  rw [collatzOrbit, Function.iterate_succ_apply'] at h
  rw [collatzOrbit]
  generalize collatzStep^[t] x = y at h ⊢
  unfold collatzStep at h
  split_ifs at h with he
  · exact ⟨2 * n + 2, by rw [pow_succ]; omega⟩
  · exfalso
    have h3 : 2 ^ (2 * n + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul]
      norm_num [Nat.mul_mod, Nat.pow_mod]
    omega
