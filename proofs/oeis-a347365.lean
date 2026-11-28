import OMAStatements.S_oeis_a347365

-- Problem oeis-a347365: with a(n) = n * (2 - (-1)^n), a(6n+1)/3 = 6n+1 and a(6n+5)/3 = 6n+5.
-- Upstream: statements/oeis-a347365.lean (declaration OMA.S_oeis_a347365.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Both indices are odd, so (-1)^index = -1 and a(index) = 3 * index; dividing by 3 gives the index back.

theorem OMA.solution : type_of% @OMA.S_oeis_a347365.main := by
  intro n
  have h1 : (-1 : ℤ) ^ (6 * n + 1) = -1 := Odd.neg_one_pow ⟨3 * n, by ring⟩
  have h5 : (-1 : ℤ) ^ (6 * n + 5) = -1 := Odd.neg_one_pow ⟨3 * n + 2, by ring⟩
  unfold OMA.S_oeis_a347365.a
  rw [h1, h5]
  push_cast
  constructor <;> omega
