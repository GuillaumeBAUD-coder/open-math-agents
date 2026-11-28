import OMAStatements.S_mo_185536
import Mathlib

open OMA.S_mo_185536

theorem OMA.solution : type_of% @OMA.S_mo_185536.main := by
  intro A _ x y hx hy hne heq
  apply hne
  have h := congrArg CFC.log heq
  rwa [CFC.log_exp x hx, CFC.log_exp y hy] at h
