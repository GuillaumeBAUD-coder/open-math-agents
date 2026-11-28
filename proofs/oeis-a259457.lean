import OMAStatements.S_oeis_a259457

-- Problem: OEIS A259457, Mathar's recurrence, with a(n) given by the closed form
-- a(n) = (n+3)! (n+2)(n+1)(n+3)(3n+8)/96. Writing n = m + 2, the factorials (m+5)! and (m+4)!
-- are (m+5)(m+4)(m+3)! and (m+4)(m+3)!, so after dividing by (m+3)!/96 the recurrence is a
-- polynomial identity in m.

theorem OMA.solution : type_of% @OMA.S_oeis_a259457.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp [OMA.S_oeis_a259457.a, Nat.factorial_succ]
  ring
