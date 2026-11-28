import OMAStatements.S_oeis_a025755
import Mathlib

open OMA.S_oeis_a025755 in
theorem OMA.solution : type_of% @OMA.S_oeis_a025755.main := by
  rintro (_ | _ | m) h
  any_goals omega
  simp [a, Nat.factorial_succ, ascPochhammer_succ_eval]
  field_simp
  ring
