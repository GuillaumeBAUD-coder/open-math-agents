import OMAStatements.S_mo_185536
import Mathlib


theorem OMA.solution : type_of% @OMA.S_mo_185536.main := by
  intro A _ x y hx hy hne h
  apply hne
  have h1 : CFC.log (NormedSpace.exp x) = x := CFC.log_exp x hx
  have h2 : CFC.log (NormedSpace.exp y) = y := CFC.log_exp y hy
  rw [← h1, ← h2, h]
