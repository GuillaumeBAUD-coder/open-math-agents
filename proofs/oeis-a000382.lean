import OMAStatements.S_oeis_a000382
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: the row (w,x,y,z) maps to (2w-z,w,x,y), so w-x-y-z = -2 is invariant, and the last coordinate
-- of row k+3 is the first coordinate of row k. Hence for n >= 8 the recurrence is exactly the invariant
-- applied to row n-5.

namespace OMA.A000382Proof

open OMA.S_oeis_a000382
open private matrixRow from OMAStatements.S_oeis_a000382

theorem step (k : ℕ) : matrixRow (k + 1) =
    (2 * (matrixRow k).1 - (matrixRow k).2.2.2, (matrixRow k).1, (matrixRow k).2.1, (matrixRow k).2.2.1) := by
  rw [matrixRow]

theorem inv (k : ℕ) : (matrixRow k).1 - (matrixRow k).2.1 - (matrixRow k).2.2.1 - (matrixRow k).2.2.2 = -2 := by
  induction k with
  | zero => rw [matrixRow]; norm_num
  | succ k ih => rw [step]; simp only; linarith

theorem shift (k : ℕ) : (matrixRow (k + 3)).2.2.2 = (matrixRow k).1 := by
  rw [step, step, step]

theorem a_eq (n : ℕ) (h : 5 ≤ n) : a n = (matrixRow (n - 5)).1 := by
  rw [a, if_neg (by omega), if_neg (by omega), show n - 2 = (n - 5) + 3 by omega, shift]

theorem main_proof : ∀ n : ℕ, 8 ≤ n → a n = a (n - 1) + a (n - 2) + a (n - 3) - 2 := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 8 := ⟨n - 8, by omega⟩
  rw [a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega)]
  have hi := inv (j + 3)
  have e1 : matrixRow (j + 3) = _ := step (j + 2)
  have e2 : matrixRow (j + 2) = _ := step (j + 1)
  have e3 : matrixRow (j + 1) = _ := step j
  rw [show j + 8 - 5 = j + 3 by omega, show j + 8 - 1 - 5 = j + 2 by omega,
    show j + 8 - 2 - 5 = j + 1 by omega, show j + 8 - 3 - 5 = j by omega]
  rw [e1] at hi; simp only at hi
  rw [e2] at hi; simp only at hi
  rw [e3] at hi; simp only at hi
  rw [e1, e2, e3]; simp only
  linarith

end OMA.A000382Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a000382.main := OMA.A000382Proof.main_proof
