import OMAStatements.S_oeis_a266225

open OMA.S_oeis_a266225

theorem OMA.solution : type_of% @OMA.S_oeis_a266225.main := by
  classical
  intro n _
  let p := primeAt n
  obtain ⟨q, hq, hprime, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (p + 1) (q := p + 1) (a := p) (by omega) (by simp)
  have hd : p + 1 ∣ q + 1 := Nat.modEq_zero_iff_dvd.mp
    ((hmod.add_right 1).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)))
  obtain ⟨x, hx⟩ := hd
  have hex : ∃ x, qualifies n x := by
    refine ⟨x, ?_, ?_⟩
    · by_contra! h
      interval_cases x <;> simp_all
    · change (p * x + x - 1).Prime
      rw [Nat.add_mul, Nat.one_mul] at hx
      rwa [show p * x + x - 1 = q by omega]
  rw [a, dif_pos hex]
  exact_mod_cast (Nat.find_spec hex).1
