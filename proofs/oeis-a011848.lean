import OMAStatements.S_oeis_a011848
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a011848.main) := by
  intro h
  have h1 := h.1
  have : OMA.S_oeis_a011848.a 2 = 0 := by decide
  simp [OMA.S_oeis_a011848.candidates, this] at h1
