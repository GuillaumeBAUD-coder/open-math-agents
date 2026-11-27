import OMAStatements.S_oeis_a056158
import Mathlib

-- Problem: A056158: Equivalent of the Kurepa hypothesis for left factorial.
-- Upstream: formal-conjectures :0 (declaration OMA.S_oeis_a056158.main)
-- Credit: @Mapika (the owner of the agent is credited as the solver)

/-!
Proof of R. J. Mathar's four-term recurrence for A056158.

Writing `f = fromThree`, the definition gives `f (j+1) = -(j+1) f j - 2 (j+3)`. Unfolding
`f (k+3)`, `f (k+2)` and `f (k+1)` down to `f k` turns Mathar's expression with `n = k + 6` into a
polynomial identity in `k` and `f k`.
-/

open OMA.S_oeis_a056158

theorem OMA.solution : type_of% @OMA.S_oeis_a056158.main := by
  intro k
  have h3 : fromThree (k + 3) = -(((k + 2 : ℕ) : ℤ) + 1) * fromThree (k + 2) -
      2 * (((k + 2 : ℕ) : ℤ) + 3) := rfl
  have h2 : fromThree (k + 2) = -(((k + 1 : ℕ) : ℤ) + 1) * fromThree (k + 1) -
      2 * (((k + 1 : ℕ) : ℤ) + 3) := rfl
  have h1 : fromThree (k + 1) = -((k : ℤ) + 1) * fromThree k - 2 * ((k : ℤ) + 3) := rfl
  show fromThree (k + 3) + (((k : ℤ) + 6) - 5) * fromThree (k + 2) +
      (-2 * ((k : ℤ) + 6) + 9) * fromThree (k + 1) + (((k : ℤ) + 6) - 5) * fromThree k = 0
  rw [h3, h2, h1]
  push_cast
  ring
