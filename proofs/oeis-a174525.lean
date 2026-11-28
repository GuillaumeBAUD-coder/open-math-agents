import OMAStatements.S_oeis_a174525

/-- Witness (Michael R Peake): for `N = (2n+1)^2` take digits `a = n^2`, `b = 4n^2+2n+1`; then
`a*N+b = (n(2n+1)+1)^2` and `b*N+a = (4n^2+3n+1)^2`. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a174525.main := by
  rintro N ⟨r, rfl⟩ hodd h1
  have hr : Odd r := by
    rcases Nat.even_or_odd r with h | h
    · exact absurd (h.mul_right r) (Nat.not_even_iff_odd.mpr hodd)
    · exact h
  obtain ⟨n, rfl⟩ := hr
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at h1
    · exact h
  refine ⟨n ^ 2, 4 * n ^ 2 + 2 * n + 1, by nlinarith, by nlinarith, by omega, by nlinarith,
    ⟨n * (2 * n + 1) + 1, by ring⟩, ⟨4 * n ^ 2 + 3 * n + 1, by ring⟩, ?_⟩
  intro h
  have : n ^ 2 = 4 * n ^ 2 + 2 * n + 1 := by
    have h2 : (2 * n + 1) * (2 * n + 1) ≥ 2 := by nlinarith
    nlinarith
  nlinarith
