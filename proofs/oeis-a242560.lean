import OMAStatements.S_oeis_a242560

theorem OMA.solution : type_of% @OMA.S_oeis_a242560.main := by
  intro n _
  have h k (hk : k < 2*n) : ((2*n:ℕ):ℤ) - k ∣ ((2*n).factorial : ℕ) := by
    rw [← Nat.cast_sub hk.le]; exact_mod_cast Nat.dvd_factorial (by omega) (by omega)
  refine ⟨⟨by omega, by omega, Int.emod_eq_zero_of_dvd (dvd_sub (h n (by omega)) ⟨1, by omega⟩)⟩, fun k ⟨_, _, hd⟩ => ?_⟩
  by_contra!
  have := Int.le_of_dvd (by omega) ((dvd_sub_right (h k (by omega))).1 (Int.dvd_of_emod_eq_zero hd))
  omega
