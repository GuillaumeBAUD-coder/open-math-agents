import OMAReductions.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1

/-! Write t = a / b in lowest terms. If p^t = r is rational, then p^a = r^b in ℚ. Taking p-adic
valuations gives a = b · v_p(r), so b divides a; as a and b are coprime, b = 1 and t = a. -/

theorem OMA.solution :
    OMA.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1.H2 := by
  intro p t hp hr
  obtain ⟨r, hr⟩ := hr
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have key : ((p : ℚ) ^ t.num : ℚ) = r ^ t.den := by
    have h1 : ((p : ℝ) ^ (t : ℝ)) ^ t.den = (r : ℝ) ^ t.den := by rw [hr]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le] at h1
    have h2 : (t : ℝ) * (t.den : ℝ) = (t.num : ℝ) := by
      have h3 := Rat.mul_den_eq_num t
      exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) h3
    rw [h2, Real.rpow_intCast] at h1
    have h4 : (((p : ℚ) ^ t.num : ℚ) : ℝ) = ((r ^ t.den : ℚ) : ℝ) := by
      push_cast
      exact h1
    exact Rat.cast_injective h4
  have := Fact.mk hp
  have hv := congrArg (padicValRat p) key
  rw [padicValRat.zpow, padicValRat.pow, padicValRat.self hp.one_lt, mul_one] at hv
  have hdvd : (t.den : ℤ) ∣ t.num := ⟨padicValRat p r, hv⟩
  have hdvd' : t.den ∣ t.num.natAbs := by
    have := Int.natAbs_dvd_natAbs.2 hdvd
    simpa using this
  have hden : t.den = 1 := Nat.Coprime.eq_one_of_dvd t.reduced.symm hdvd'
  exact ⟨t.num, (Rat.coe_int_num_of_den_eq_one hden).symm⟩
