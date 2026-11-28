import OMAStatements.S_oeis_a081739
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a081739.main := by
  intro n _
  have h : (2 : ℚ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  unfold OMA.S_oeis_a081739.a OMA.S_oeis_a081739.b
  field_simp
  ring
