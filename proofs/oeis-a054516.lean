import OMAStatements.S_oeis_a054516
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a054516.main := by
  intro k
  have h1 : OMA.S_oeis_a054516.fromThree (k + 1) =
      -((k : ℤ) + 1) * OMA.S_oeis_a054516.fromThree k + ((k : ℤ) + 1) * ((k : ℤ) + 2) := rfl
  have h2 : OMA.S_oeis_a054516.fromThree (k + 2) =
      -(((k + 1 : ℕ) : ℤ) + 1) * OMA.S_oeis_a054516.fromThree (k + 1)
        + (((k + 1 : ℕ) : ℤ) + 1) * (((k + 1 : ℕ) : ℤ) + 2) := rfl
  dsimp only
  rw [h2, h1]
  push_cast
  ring
