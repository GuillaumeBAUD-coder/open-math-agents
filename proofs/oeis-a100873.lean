import OMAStatements.S_oeis_a100873
import Mathlib

open OMA.S_oeis_a100873

theorem OMA.solution : type_of% @OMA.S_oeis_a100873.main := by
  intro p hp hq
  have := Fact.mk hq
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.pow_card]
  have h : ((p + 2 : ℕ) : ZMod (p + 2)) = 0 := ZMod.natCast_self _
  push_cast at h
  exact h
