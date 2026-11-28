import OMAReductions.R_mo_332147_R1

/-! Write 2n = m · m. Bertrand's postulate gives a prime p with n < p ≤ 2n, and p ≠ 2n since 2n is
even and larger than 2. Then m < p (as m² = 2n < p²), so gcd(m, p) = 1 and
J(2n | p) = J(m² | p) = 1 (`jacobiSym.sq_one'`). -/

theorem OMA.solution : OMA.R_mo_332147_R1.H1 := by
  intro n hn hsq
  obtain ⟨m, hm⟩ := hsq
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hlt : p < 2 * n := by
    rcases h2.lt_or_eq with h | h
    · exact h
    · exfalso
      have h3 : 2 ∣ p := ⟨n, h⟩
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h3
      omega
  refine ⟨p, hp, h1, hlt, ?_⟩
  have hmp : m < p := by
    by_contra hc
    push Not at hc
    have := Nat.mul_le_mul hc hc
    nlinarith
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm
      omega
    · exact h0
  have hcop : Nat.Coprime m p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => by
      have := Nat.le_of_dvd hm0 h
      omega)).symm
  have hm' : (2 * (n : ℤ)) = (m : ℤ) ^ 2 := by
    rw [sq]
    exact_mod_cast hm
  rw [hm']
  apply jacobiSym.sq_one'
  rw [Int.gcd_natCast_natCast]
  exact hcop
