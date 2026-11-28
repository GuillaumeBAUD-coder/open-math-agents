import OMAStatements.S_oeis_a242560

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: k = n works since n divides (2n)!. For 0 < k < n we have n < 2n - k ≤ 2n, so 2n - k
-- divides (2n)! and (2n)! - k ≡ -k, which is not 0 mod 2n - k because 0 < k < 2n - k.

open OMA.S_oeis_a242560

theorem OMA.solution : type_of% @OMA.S_oeis_a242560.main := by
  intro n hn
  refine ⟨⟨by omega, by omega, ?_⟩, ?_⟩
  · have hd : (n : ℤ) ∣ ((2 * n).factorial : ℤ) := by
      exact_mod_cast Nat.dvd_factorial (by omega) (by omega)
    have : ((2 * n : ℕ) : ℤ) - n = n := by push_cast; ring
    rw [this]
    exact Int.emod_eq_zero_of_dvd (dvd_sub hd (dvd_refl _))
  · intro k hk
    by_contra hlt
    push Not at hlt
    obtain ⟨hk0, -, hmod⟩ := hk
    have hd : ((2 * n - k : ℕ) : ℤ) ∣ ((2 * n).factorial : ℤ) := by
      exact_mod_cast Nat.dvd_factorial (by omega) (by omega)
    have hc : ((2 * n : ℕ) : ℤ) - k = ((2 * n - k : ℕ) : ℤ) := by push_cast [Nat.cast_sub (show k ≤ 2 * n by omega)]; ring
    rw [hc] at hmod
    have h2 : ((2 * n - k : ℕ) : ℤ) ∣ (k : ℤ) := by
      have h3 := Int.dvd_of_emod_eq_zero hmod
      have := dvd_sub hd h3
      simpa using this
    have h4 : (2 * n - k : ℕ) ∣ k := by exact_mod_cast h2
    have := Nat.le_of_dvd hk0 h4
    omega
