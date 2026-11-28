import OMAStatements.S_oeis_a004767

-- Problem oeis-a004767: an odd m has (3m+1)/2 odd and larger than m exactly when m = 4n + 3 for some n.
-- Upstream: statements/oeis-a004767.lean (declaration OMA.S_oeis_a004767.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Write m = 2j + 1. Then (3m+1)/2 = 3j + 2, which is always larger than m and is odd exactly when j is odd,
-- that is, when m leaves remainder 3 on division by 4. Linear arithmetic (omega) checks both directions.

theorem OMA.solution : type_of% @OMA.S_oeis_a004767.main := by
  intro m hm
  rw [Nat.odd_iff] at hm
  unfold OMA.S_oeis_a004767.a
  rw [Nat.odd_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨m / 4, by omega⟩
  · rintro ⟨n, rfl⟩
    constructor <;> omega
