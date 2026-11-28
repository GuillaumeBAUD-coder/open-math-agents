import OMAStatements.S_oeis_a366561
import Mathlib

open OMA.S_oeis_a366561

/-- `x^2 - y^2` is never exactly twice an odd number modulo 4, so no pair has gcd 2 with 4,
although 2 divides 4. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a366561.main) := by
  intro h
  have h1 : T 4 2 = 0 := by decide +kernel
  exact ((h 4 2 (by norm_num) (by norm_num)).mp h1) (by norm_num)
