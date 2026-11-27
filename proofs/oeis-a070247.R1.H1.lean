import OMAReductions.R_oeis_a070247_R1

-- The proper divisors below are recorded in OEIS A102050.
-- Only divisibility and the two strict bounds are needed.
lemma OMA.composite_of_remainder {n : ℕ} (d : ℕ)
    (h₁ : 1 < d) (h₂ : d < n) (h₃ : n % d = 0) : ¬ Nat.Prime n := by
  intro hp
  exact (Nat.prime_def_lt'.mp hp).2 d h₁ h₂ (Nat.dvd_of_mod_eq_zero h₃)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem OMA.solution : OMA.R_oeis_a070247_R1.H1 := by
  intro k hk hk'
  have hk_cases : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
      k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 := by omega
  rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact OMA.composite_of_remainder 73 (by decide) (by decide) (by decide)
  · exact OMA.composite_of_remainder 17 (by decide) (by decide) (by decide)
  · exact OMA.composite_of_remainder 353 (by decide) (by decide) (by decide)
  · exact OMA.composite_of_remainder 19841 (by decide) (by decide) (by decide)
  · exact OMA.composite_of_remainder 1265011073 (by decide) (by decide) (by decide)
  · exact OMA.composite_of_remainder 257 (by decide) (by decide) (by decide)
  · exact OMA.composite_of_remainder 10753 (by decide) (by decide) (by decide)
  · exact OMA.composite_of_remainder 1514497 (by decide) (by decide) (by decide)
  · exact OMA.composite_of_remainder 1856104284667693057 (by decide) (by decide) (by decide)
  · exact OMA.composite_of_remainder 106907803649 (by decide) (by decide) (by decide)
  · exact OMA.composite_of_remainder 458924033 (by decide) (by decide) (by decide)
  · exact OMA.composite_of_remainder 3635898263938497962802538435084289
      (by decide) (by decide) (by decide)
  · exact OMA.composite_of_remainder 1702047085242613845984907230501142529
      (by decide) (by decide) (by decide)
