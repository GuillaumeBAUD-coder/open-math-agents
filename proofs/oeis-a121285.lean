import OMAStatements.S_oeis_a121285
import Mathlib

open OMA.S_oeis_a121285 in
theorem OMA.solution : type_of% @OMA.S_oeis_a121285.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k <;> rcases i with _ | j <;> first
  | (norm_num [a, Nat.choose]; done)
  | (simp (disch := omega) [a, mul_add, add_assoc, show ∀ c, (2*j+c)/2 = j+c/2 by omega,
       Nat.cast_choose ℚ, show ∀ m c, m ≤ c → 2*j+c-(j+m) = j+(c-m) by omega,
       show ∀ c, 2*j+c-j = j+c by omega, show 2*j-j = j by omega, Nat.factorial_succ, pow_succ]
     field_simp
     ring)
