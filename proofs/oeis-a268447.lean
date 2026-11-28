import OMAStatements.S_oeis_a268447

-- Problem oeis-a268447 (OEIS A268447): the recurrence
--   -(n+10)*(n-8)*a(n) + 2*n*(2*n+1)*a(n-1) = 0   for n >= 9,
-- where a(n) = 18*(2n+1)! / ((n-8)! * (n+10)!).
-- Upstream: statements/oeis-a268447.lean (declaration OMA.S_oeis_a268447.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Direct computation. Write n = m + 9. Then
--   a(n)   = 18*(2m+19)! / ((m+1)! * (m+19)!),
--   a(n-1) = 18*(2m+17)! / (m! * (m+18)!),
-- and (2m+19)! = (2m+19)*(2m+18)*(2m+17)!, (m+1)! = (m+1)*m!, (m+19)! = (m+19)*(m+18)!,
-- so (n+10)*(n-8)*a(n) = 2*n*(2*n+1)*a(n-1).

theorem OMA.solution : type_of% @OMA.S_oeis_a268447.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  have hm1 : (m : ℚ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero m
  have hm19 : (m : ℚ) + 19 ≠ 0 := by
    have h0 : (0 : ℚ) ≤ (m : ℚ) := Nat.cast_nonneg m
    intro h
    linarith
  have e0 : m + 9 - 1 = m + 8 := by omega
  have e1 : 2 * (m + 9) + 1 = 2 * m + 19 := by ring
  have e2 : m + 9 - 8 = m + 1 := by omega
  have e3 : m + 9 + 10 = m + 19 := by ring
  have e4 : 2 * (m + 8) + 1 = 2 * m + 17 := by ring
  have e5 : m + 8 - 8 = m := by omega
  have e6 : m + 8 + 10 = m + 18 := by ring
  have g1 : (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
  have g2 : (m + 19).factorial = (m + 19) * (m + 18).factorial := Nat.factorial_succ (m + 18)
  have g3 : (2 * m + 19).factorial = (2 * m + 19) * ((2 * m + 18) * (2 * m + 17).factorial) := by
    rw [Nat.factorial_succ (2 * m + 18), Nat.factorial_succ (2 * m + 17)]
  have hA : (m.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hB : ((m + 18).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 18))
  rw [e0]
  unfold OMA.S_oeis_a268447.a
  rw [e1, e2, e3, e4, e5, e6, g1, g2, g3]
  push_cast
  clear e0 e1 e2 e3 e4 e5 e6 g1 g2 g3 hn
  generalize (m.factorial : ℚ) = A at hA ⊢
  generalize ((m + 18).factorial : ℚ) = B at hB ⊢
  generalize ((2 * m + 17).factorial : ℚ) = C
  field_simp
  ring
