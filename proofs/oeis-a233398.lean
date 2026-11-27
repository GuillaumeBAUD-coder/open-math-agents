import OMAStatements.S_oeis_a233398

-- Problem: oeis-a233398
-- Credit: @anmolspace
-- Proof: if x = 3k then x^x = 3^x * k^x, so 3^x divides x^x and x^x % 3^x = 0.

theorem OMA.solution : type_of% @OMA.S_oeis_a233398.main := by
  intro x ⟨k, hk⟩
  subst hk
  unfold OMA.S_oeis_a233398.a
  apply Nat.mod_eq_zero_of_dvd
  rw [mul_pow]
  exact Dvd.intro _ rfl
