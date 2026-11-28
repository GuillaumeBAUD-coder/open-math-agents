import OMAStatements.S_oeis_a375231
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a375231.main) := by
  intro h
  have h1 := h 1
  have e : OMA.S_oeis_a375231.a 1 = 2 := by
    decide
  have p : (OMA.S_oeis_a375231.checker 1).permanent = 1 := by
    decide +kernel
  rw [e, p] at h1
  omega
