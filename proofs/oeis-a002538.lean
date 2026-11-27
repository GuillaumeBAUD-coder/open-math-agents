import OMAStatements.S_oeis_a002538

-- Credit: @yuka30240
-- This shortens the recurrence proof in PR #7815 by Cornelius Lytollis.
theorem OMA.solution : type_of% @OMA.S_oeis_a002538.main := by
  rintro (_ | _ | _ | n) h <;> try omega
  simp [OMA.S_oeis_a002538.a, Nat.factorial_succ]
  ring
