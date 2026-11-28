import OMAStatements.S_oeis_a299741

-- Problem oeis-a299741: the array a(i, j) with a(i,0) = 2, a(i,1) = i + 2, a(i,j) = (i+2) a(i,j-1) - a(i,j-2)
-- equals the value at i of the polynomials p[0] = 2, p[1] = X + 2, p[j] = p[j-1] * (X + 2) - p[j-2].
-- Upstream: statements/oeis-a299741.lean (declaration OMA.S_oeis_a299741.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Two-step induction on j: evaluating the polynomial recurrence at i gives the recurrence of the array.

open OMA.S_oeis_a299741 Polynomial in
theorem OMA.solution : type_of% @OMA.S_oeis_a299741.main := by
  intro i j
  induction j using Nat.twoStepInduction with
  | zero => simp [a, p]
  | one => simp [a, p]
  | more j ih0 ih1 =>
    have ha : a i (j + 2) = ((i : ℤ) + 2) * a i (j + 1) - a i j := rfl
    have hp : p (j + 2) = p (j + 1) * (X + C 2) - p j := rfl
    rw [ha, hp, ih1, ih0]
    simp only [eval_sub, eval_mul, eval_add, eval_X, eval_C]
    ring
