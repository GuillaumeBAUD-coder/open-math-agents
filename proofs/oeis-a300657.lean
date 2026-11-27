import OMAStatements.S_oeis_a300657

theorem OMA.solution : type_of% @OMA.S_oeis_a300657.main := by
  intro n hn
  have hsplit : OMA.S_oeis_a300657.a n =
      (∑ d ∈ n.properDivisors, ArithmeticFunction.sigma 1 d % d) + OMA.S_oeis_a300657.b n := by
    unfold OMA.S_oeis_a300657.a OMA.S_oeis_a300657.b
    rw [← Nat.cons_self_properDivisors (by omega), Finset.sum_cons, add_comm]
  rw [hsplit]
  constructor
  · intro h
    have h0 : (∑ d ∈ n.properDivisors, ArithmeticFunction.sigma 1 d % d) = 0 := by omega
    rw [Finset.sum_eq_zero_iff] at h0
    by_contra hc
    push Not at hc
    have hn2 : n ≠ 1 := hc.1
    have hp : (Nat.minFac n).Prime := Nat.minFac_prime hn2
    have hlt : Nat.minFac n < n := by
      exact (Nat.not_prime_iff_minFac_lt (by omega)).1 hc.2
    have hmem : Nat.minFac n ∈ n.properDivisors := by
      rw [Nat.mem_properDivisors]
      exact ⟨Nat.minFac_dvd n, hlt⟩
    have := h0 _ hmem
    rw [ArithmeticFunction.sigma_one_apply, hp.sum_divisors] at this
    have h2 := hp.two_le
    rw [Nat.add_mod_left] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega
  · rintro (rfl | hp)
    · simp
    · rw [hp.properDivisors]
      simp
