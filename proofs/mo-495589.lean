import OMAStatements.S_mo_495589
import Mathlib

open OMA.S_mo_495589

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_495589.main) := by
  intro h
  have hf : firstFailure 0 5 3 := by
    refine ⟨by decide, by decide +kernel, ?_⟩
    intro j hj hj'
    have hcases : j = 1 ∨ j = 2 := by omega
    rcases hcases with rfl | rfl <;> decide +kernel
  have hr := ((h.1 0 5).1).mp hf
  exact (by decide : ¬ ((0 % 2 = 1 ∧ (5 % 3 = 1 ∨ 5 % 3 = 2)) ∨
    (0 % 2 = 0 ∧ 5 % 3 = 1))) hr