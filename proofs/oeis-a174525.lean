import OMAStatements.S_oeis_a174525

-- Problem oeis-a174525: every odd square N > 1 is a term: there are a, b in [1, N) with a N + b and b N + a
-- two different squares.
-- Upstream: statements/oeis-a174525.lean (declaration OMA.S_oeis_a174525.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: write N = (2j + 1)^2 with j >= 1 and take a = j^2, b = 4j^2 + 2j + 1. Then
--   a N + b = (2j^2 + j + 1)^2   and   b N + a = (4j^2 + 3j + 1)^2,
-- and the two squares differ because 2j^2 + j + 1 < 4j^2 + 3j + 1.

open OMA.S_oeis_a174525

theorem OMA.solution : type_of% @OMA.S_oeis_a174525.main := by
  intro N hsq hodd hne
  obtain ⟨r, rfl⟩ := hsq
  obtain ⟨j, rfl⟩ := (Nat.odd_mul.mp hodd).1
  have hj : 1 ≤ j := by
    by_contra h
    have h0 : j = 0 := by omega
    subst h0
    simp at hne
  have hj2 : 1 ≤ j ^ 2 := Nat.one_le_pow 2 j hj
  have e1 : j ^ 2 * ((2 * j + 1) * (2 * j + 1)) + (4 * j ^ 2 + 2 * j + 1)
      = (2 * j ^ 2 + j + 1) ^ 2 := by ring
  have e2 : (4 * j ^ 2 + 2 * j + 1) * ((2 * j + 1) * (2 * j + 1)) + j ^ 2
      = (4 * j ^ 2 + 3 * j + 1) ^ 2 := by ring
  refine ⟨j ^ 2, 4 * j ^ 2 + 2 * j + 1, hj2, by nlinarith, by omega, by nlinarith,
    ⟨2 * j ^ 2 + j + 1, by ring⟩, ⟨4 * j ^ 2 + 3 * j + 1, by ring⟩, ?_⟩
  rw [e1, e2]
  exact Nat.ne_of_lt (Nat.pow_lt_pow_left (by omega) (by norm_num))
