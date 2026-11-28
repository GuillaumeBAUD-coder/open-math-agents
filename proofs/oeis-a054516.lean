import OMAStatements.S_oeis_a054516
import Mathlib

open OMA.S_oeis_a054516

theorem OMA.solution : type_of% @OMA.S_oeis_a054516.main := by
  intro k
  dsimp
  have h0 : fromThree (k + 1) =
      -((k : ℤ) + 1) * fromThree k + ((k : ℤ) + 1) * ((k : ℤ) + 2) := rfl
  have h1 : fromThree (k + 2) =
      -(((k + 1 : ℕ) : ℤ) + 1) * fromThree (k + 1) +
        (((k + 1 : ℕ) : ℤ) + 1) * (((k + 1 : ℕ) : ℤ) + 2) := rfl
  push_cast at h1
  linear_combination (-((k : ℤ) + 1)) * h1 + ((k : ℤ) + 3) * h0
