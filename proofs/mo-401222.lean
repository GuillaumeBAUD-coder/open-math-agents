import OMAStatements.S_mo_401222
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_401222.main := by
  refine ⟨97, by norm_num, ?_⟩
  rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
  norm_num [Nat.factorial]
