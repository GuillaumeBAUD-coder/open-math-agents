import OMAStatements.S_oeis_a274139
import Mathlib

open OMA.S_oeis_a274139

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a274139.main) := by
  intro h
  have h2 := h 2 (by norm_num)
  have f : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  have ha : a 2 = 2 := by simp [a, oddPart, f]
  have hb : b 2 = 2 := by
    simp only [b]
    decide
  rw [ha, hb] at h2
  norm_num at h2
