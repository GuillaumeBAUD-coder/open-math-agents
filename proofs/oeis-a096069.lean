import OMAStatements.S_oeis_a096069

-- Problem: A096069: Smallest prime ending in prime(n) and == 1 (mod prime(n)), or 0 if no such prime exists.
-- Upstream: statements/oeis-a096069.lean (declaration OMA.S_oeis_a096069.main)
-- Credit: @anthill24 (the owner of the agent is credited as the solver)

theorem OMA.solution : type_of% @OMA.S_oeis_a096069.main := by
  intro p hp hp2 hp5
  set m := 10 ^ (Nat.digits 10 p).length with hm_def
  have h10_cop : (10 : ℕ).Coprime p := by
    have h2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    have h5 : ¬ p ∣ 5 := fun h => hp5 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
    have h10 : ¬ p ∣ 10 := by
      intro h
      rcases hp.dvd_mul.mp (show p ∣ 2 * 5 from h) with h' | h'
      · exact h2 h'
      · exact h5 h'
    exact (hp.coprime_iff_not_dvd.mpr h10).symm
  have hm_cop : m.Coprime p := h10_cop.pow_left _
  obtain ⟨r, hr_m, hr_p⟩ := Nat.chineseRemainder hm_cop p 1
  have hr_cop_m : r.Coprime m := by
    have : r.gcd m = p.gcd m := hr_m.gcd_eq
    rw [Nat.Coprime, this]
    exact hm_cop.symm
  have hr_cop_p : r.Coprime p := by
    have : r.gcd p = (1 : ℕ).gcd p := hr_p.gcd_eq
    rw [Nat.Coprime, this]
    exact Nat.gcd_one_left p
  have hr_cop_mp : r.Coprime (m * p) := hr_cop_m.mul_right hr_cop_p
  have hmp_ne : m * p ≠ 0 := mul_ne_zero (pow_ne_zero _ (by decide)) hp.ne_zero
  obtain ⟨q, -, hq_prime, hq_mod⟩ := Nat.forall_exists_prime_gt_and_modEq 0 hmp_ne hr_cop_mp
  refine ⟨q, hq_prime, ?_, ?_⟩
  · exact (hq_mod.of_mul_right p).trans hr_m
  · exact (hq_mod.of_mul_left m).trans hr_p
