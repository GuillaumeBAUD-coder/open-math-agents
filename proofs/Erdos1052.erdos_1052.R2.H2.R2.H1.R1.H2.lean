import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R2_H1_R1


namespace E1052Aux

lemma two_pow_dvd_u (a c : ℕ) (hc : Odd c) (ha : 1 ≤ a) :
    2^a+1 ∣ ∏ p ∈ (2^a*c).primeFactors, (1+p^(2^a*c).factorization p) := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have h2 : 2 ∈ (2^a*c).primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨Nat.prime_two, dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _, by positivity⟩
  have hf : (2^a*c).factorization 2 = a := by
    rw [Nat.factorization_mul (by positivity) hc0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
    · rw [Nat.factorization_eq_zero_of_not_dvd]
      · simp
      · exact fun h => (Nat.not_even_iff_odd.mpr hc) (even_iff_two_dvd.mpr h)
  have := Finset.dvd_prod_of_mem (fun p => 1+p^(2^a*c).factorization p) h2
  simp only [hf] at this
  rwa [add_comm] at this

lemma not_in_S_dvd (c a : ℕ) (S : Finset ℕ) (hc : Odd c) (ha : 1 ≤ a)
    (hS : ∀ p ∈ S, p.Prime ∧ ¬p ∣ 2^a*c)
    (heq : (∏ p ∈ (2^a*c).primeFactors, (1+p^(2^a*c).factorization p))*(∏ p ∈ S, (1+p))
      = (2*(2^a*c))*(∏ p ∈ S, p))
    (x : ℕ) (hx : x.Prime) (hxd : x ∣ 2^a+1) (hxS : x ∉ S) : x ≤ c := by
  have hc0 : 0 < c := by rcases hc with ⟨k, rfl⟩; omega
  have hodd : ¬ x ∣ 2 := by
    intro h
    have : x = 2 := (Nat.prime_dvd_prime_iff_eq hx Nat.prime_two).mp h
    subst this
    have : 2 ∣ 1 := by
      have h2 : 2 ∣ 2^a := dvd_pow_self 2 (by omega)
      exact (Nat.dvd_add_right h2).mp hxd
    omega
  have hdu := (hxd.trans (two_pow_dvd_u a c hc ha)).trans (dvd_mul_right _ (∏ p ∈ S, (1+p)))
  rw [heq] at hdu
  rcases (Nat.Prime.dvd_mul hx).mp hdu with h | h
  · rcases (Nat.Prime.dvd_mul hx).mp h with h | h
    · exact absurd h hodd
    · rcases (Nat.Prime.dvd_mul hx).mp h with h | h
      · exact absurd (hx.dvd_of_dvd_pow h) hodd
      · exact Nat.le_of_dvd hc0 h
  · obtain ⟨q, hq, hxq⟩ := (Prime.dvd_finsetProd_iff hx.prime _).mp h
    have : x = q := (Nat.prime_dvd_prime_iff_eq hx (hS q hq).1).mp hxq
    subst this
    exact absurd hq hxS

end E1052Aux

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H1_R1.H2 := by
  intro c hc hpow a S b u ha hcard hsub hS heq p r hp hr hpr hnot
  have key := E1052Aux.not_in_S_dvd c a S hc (by omega) hS heq
  have hpd : p ∣ 2^a+1 := (dvd_mul_right p r).trans hpr
  have hrd : r ∣ 2^a+1 := (dvd_mul_left r p).trans hpr
  by_cases hpS : p ∈ S
  · by_cases hrS : r ∈ S
    · exfalso
      have hpr' : p = r := by
        by_contra hne
        exact hnot ⟨hpS, hrS, hne⟩
      subst hpr'
      have h1 : p*p ∣ (2*b)*(∏ q ∈ S, q) := by
        rw [← heq]
        exact (hpr.trans (E1052Aux.two_pow_dvd_u a c hc (by omega))).trans (dvd_mul_right _ _)
      rw [← Finset.mul_prod_erase S (fun q => q) hpS, mul_left_comm] at h1
      have h2 : p ∣ (2*b)*(∏ q ∈ S.erase p, q) := Nat.dvd_of_mul_dvd_mul_left hp.pos h1
      rcases (Nat.Prime.dvd_mul hp).mp h2 with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
          subst this
          have h2 : 2 ∣ 2^a := dvd_pow_self 2 (by omega)
          have : 2 ∣ 1 := (Nat.dvd_add_right h2).mp hpd
          omega
        · exact (hS p hpS).2 h
      · obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
        have : p = q := (Nat.prime_dvd_prime_iff_eq hp (hS q (Finset.mem_of_mem_erase hq)).1).mp hpq
        subst this
        exact (Finset.ne_of_mem_erase hq) rfl
    · exact (min_le_right p r).trans (key r hr hrd hrS)
  · exact (min_le_left p r).trans (key p hp hpd hpS)
