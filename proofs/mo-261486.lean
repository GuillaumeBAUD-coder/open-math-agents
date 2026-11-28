import OMAStatements.S_mo_261486
import Mathlib

/-!
MathOverflow 261486: `11^3` divides `d(136) = 136^135 - 135^135`, so `v_11(d(136)) ≥ 3`.
-/

open OMA.S_mo_261486

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_261486.main) := by
  intro h
  refine h 136 (by norm_num) 11 (by norm_num) ?_
  unfold d
  decide
