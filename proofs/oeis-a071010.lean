import OMAStatements.S_oeis_a071010

lemma geom_mod4 (q t : ℕ) (hq : q % 4 = 3) : 4 ∣ ∑ k ∈ Finset.range (2 * t + 2), q ^ k := by
  induction t with
  | zero =>
    simp [Finset.sum_range_succ]
    omega
  | succ t ih =>
    have h1 : 2 * (t + 1) + 2 = (2 * t + 2) + 1 + 1 := by ring
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ]
    have : q ^ (2 * t + 2) + q ^ (2 * t + 2 + 1) = q ^ (2 * t + 2) * (q + 1) := by ring
    rw [add_assoc, this]
    apply dvd_add ih
    apply Dvd.dvd.mul_left
    omega

open ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a071010.main := by
  intro n hn
  rw [Nat.eq_sq_add_sq_iff] at hn
  push Not at hn
  obtain ⟨q, hqmem, hq3, hodd⟩ := hn
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  have hn0 : n ≠ 0 := (Nat.mem_primeFactors.1 hqmem).2.2
  have : Fact q.Prime := ⟨hqp⟩
  set e := padicValNat q n with he
  have hdvd : q ^ e ∣ n := pow_padicValNat_dvd
  obtain ⟨m, hm⟩ := hdvd
  have hqm : ¬ q ∣ m := by
    intro h
    apply pow_succ_padicValNat_not_dvd (p := q) hn0
    rw [← he, hm, pow_succ]
    exact Nat.mul_dvd_mul_left _ h
  have hcop : Nat.Coprime (q ^ e) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hqp).2 hqm)
  rw [hm, isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_apply_prime_pow hqp]
  apply Dvd.dvd.mul_right
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨t, ht⟩ := hodd
  rw [ht, show 2 * t + 1 + 1 = 2 * t + 2 by ring]
  exact geom_mod4 q t hq3
