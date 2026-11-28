import OMAStatements.S_oeis_a025527

-- Problem: A025527: a(n) = n!/lcm{1,2,...,n} = (n-1)!/lcm{C(n-1,0), C(n-1,1), ..., C(n-1,n-1)}.
-- Upstream: formal-conjectures statements/oeis-a025527.lean:0 (declaration OMA.S_oeis_a025527.main)
-- Credit: @Mingjaam (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Thanks to @vubui for the verified quotient lemma in the problem notes.

private theorem quotient_totient_eq (d n : ℕ) (hd : 0 < d) (hdn : d ∣ n)
    (hs : n.primeFactors = d.primeFactors) : n / d = n.totient / d.totient := by
  obtain ⟨k, rfl⟩ := hdn
  have ht : (d * k).totient = d.totient * k := by
    exact_mod_cast (show ((d * k).totient : ℚ) = (d.totient : ℚ) * k by
      rw [Nat.totient_eq_mul_prod_factors (d * k), Nat.totient_eq_mul_prod_factors d, hs,
        Nat.cast_mul]
      ring)
  rw [ht, Nat.mul_div_cancel_left k hd, Nat.mul_div_cancel_left k (Nat.totient_pos.mpr hd)]

open OMA.S_oeis_a025527

private theorem all_indices (m : ℕ) : m.factorial / L m = m.factorial.totient / (L m).totient := by
  have hd : L m ∣ m.factorial := Finset.lcm_dvd fun k hk =>
    Nat.dvd_factorial (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
  have hpos : 0 < L m := Nat.pos_of_dvd_of_pos hd (Nat.factorial_pos m)
  apply quotient_totient_eq _ _ hpos hd
  apply Finset.Subset.antisymm _ (Nat.primeFactors_mono hd (Nat.factorial_ne_zero m))
  intro q hq
  obtain ⟨hp, hdiv, _⟩ := Nat.mem_primeFactors.mp hq
  exact hp.mem_primeFactors (Finset.dvd_lcm (f := id)
    (Finset.mem_Icc.mpr ⟨hp.pos, hp.dvd_factorial.mp hdiv⟩)) hpos.ne'

theorem OMA.solution : type_of% @OMA.S_oeis_a025527.main := by
  intro p _
  exact all_indices (p - 1)
