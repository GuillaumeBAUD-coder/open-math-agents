import OMAReductions.R_SolitaryNumber_is_ten_solitary_R1_H3_R1
import Mathlib
-- Credit: @LordMike

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

theorem OMA.solution : OMA.R_SolitaryNumber_is_ten_solitary_R1_H3_R1.H1 := by
  have geom : ∀ p k : ℕ, 0 < p → (p - 1) * (∑ i ∈ Finset.range (k + 1), p ^ i) + 1 = p ^ (k + 1) := by
    intro p k hp
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, pow_succ (n + 1) (k + 1)]
      nlinarith [ih]
  intro m hodd hsq hcard heq
  have hm0 : m ≠ 0 := by rintro rfl; simp at hodd
  have h5 : 5 ∣ m := by
    have : 5 ∣ 18 * m := ⟨σ 1 m * 2, by linarith⟩
    rcases (Nat.Prime.dvd_mul Nat.prime_five).mp this with h | h
    · omega
    · exact h
  have he1 : 1 ≤ m.factorization 5 := Nat.prime_five.factorization_pos_of_dvd hm0 h5
  have he2 : Even (m.factorization 5) := by
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact hm0 hr
    have := congrArg (fun n => n.factorization 5) hr
    simp only [Nat.factorization_mul hr0 hr0, Finsupp.add_apply] at this
    exact ⟨_, this⟩
  obtain ⟨e, he⟩ : ∃ e, e = m.factorization 5 := ⟨_, rfl⟩
  rw [← he] at he1 he2
  obtain ⟨m', hm'⟩ : ∃ m', m' = m / 5 ^ m.factorization 5 := ⟨_, rfl⟩
  have hdec : 5 ^ e * m' = m := by
    rw [he, hm']; exact Nat.ordProj_mul_ordCompl_eq_self m 5
  have hcop : Nat.Coprime (5 ^ e) m' := by
    have := Nat.coprime_ordCompl Nat.prime_five hm0
    rw [← hm'] at this
    exact this.pow_left e
  have hcop5 : Nat.Coprime 5 m' := by
    have := Nat.coprime_ordCompl Nat.prime_five hm0
    rwa [← hm'] at this
  have hm'0 : m' ≠ 0 := by rintro rfl; simp at hdec; exact hm0 hdec.symm
  have hσ : σ 1 m = (∑ i ∈ Finset.range (e + 1), 5 ^ i) * σ 1 m' := by
    rw [← hdec, isMultiplicative_sigma.map_mul_of_coprime hcop,
      sigma_one_apply_prime_pow Nat.prime_five]
  have hg := geom 5 e (by norm_num)
  norm_num at hg
  generalize hS : (∑ i ∈ Finset.range (e + 1), 5 ^ i) = S at hσ hg
  rw [hσ, ← hdec] at heq
  have hpos : 0 < 5 ^ e := by positivity
  have hdvd : ∀ r, r.Prime → r ∣ m' → r = 5 → False := by
    intro r hr hrd h; subst h
    exact absurd (Nat.Prime.coprime_iff_not_dvd hr |>.mp hcop5) (by simpa using hrd)
  -- unique prime factor of m'
  have huniq : m'.primeFactors.card ≤ 1 := by
    have hsub : m'.primeFactors ⊆ m.primeFactors.erase 5 := by
      intro r hr
      rw [Finset.mem_erase, Nat.mem_primeFactors]
      rw [Nat.mem_primeFactors] at hr
      refine ⟨fun h => hdvd r hr.1 hr.2.1 h, hr.1, ?_, hm0⟩
      exact hr.2.1.trans ⟨5 ^ e, by rw [← hdec]; ring⟩
    have h5m : 5 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_five, h5, hm0⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem h5m] at this
    omega
  rw [Finset.card_le_one] at huniq
  have hSpos : 1 < S := by
    have : 2 ≤ 5 ^ e := by
      calc 2 ≤ 5 := by norm_num
        _ = 5 ^ 1 := by norm_num
        _ ≤ 5 ^ e := Nat.pow_le_pow_right (by norm_num) he1
    have h4 : 5 ^ (e + 1) = 5 * 5 ^ e := by ring
    omega
  by_cases hm1 : m' = 1
  · subst hm1
    simp at heq
    have h4 : 5 ^ (e + 1) = 5 * 5 ^ e := by ring
    omega
  · obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hm1
    have hqu : ∀ {d : ℕ}, d.Prime → d ∣ m' → d = q := by
      intro d hd hdd
      exact huniq d (Nat.mem_primeFactors.mpr ⟨hd, hdd, hm'0⟩) q
        (Nat.mem_primeFactors.mpr ⟨hq, hqd, hm'0⟩)
    have hmq := Nat.eq_prime_pow_of_unique_prime_dvd hm'0 hqu
    obtain ⟨f, hmq⟩ : ∃ f, m' = q ^ f := ⟨_, hmq⟩
    subst hmq
    have hq5 : q ≠ 5 := by
      intro h; subst h
      exact hdvd 5 hq hqd rfl
    have hf1 : f ≠ 0 := by
      rintro rfl
      simp at hqd
      exact hq.one_lt.ne' hqd
    have hq2 : q ≠ 2 := by
      intro h; subst h
      have h2 : 2 ∣ m := by
        rw [← hdec]; exact Dvd.dvd.mul_left (dvd_pow_self 2 hf1) _
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨c, hc⟩ := h2
      omega
    rw [sigma_one_apply_prime_pow hq] at heq
    have hgq := geom q f hq.pos
    generalize (∑ i ∈ Finset.range (f + 1), q ^ i) = T at heq hgq
    have hP : 0 < 5 ^ e := hpos
    have hQ : 0 < q ^ f := pow_pos hq.pos f
    have h54 : 5 ^ (e + 1) = 5 * 5 ^ e := by ring
    have hmod5 : ¬ 5 ∣ S := by
      intro h
      have h5' : 5 ∣ 5 ^ (e + 1) := dvd_pow_self 5 (by omega)
      omega
    by_cases hq3 : q = 3
    · subst hq3
      have hmod3 : ¬ 3 ∣ S := by
        obtain ⟨j, hj⟩ := he2
        have : 5 ^ (e + 1) % 3 = 2 := by
          rw [show e + 1 = 2 * j + 1 by omega, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
          norm_num
        omega
      have h2 : S * T * 5 = 9 * (5 ^ e * 3 ^ f) := by
        have : 2 * (S * T * 5) = 2 * (9 * (5 ^ e * 3 ^ f)) := by linarith
        omega
      have hd : S ∣ 9 * (5 ^ e * 3 ^ f) := Dvd.intro (T * 5) (by rw [← h2]; ring)
      have hS3 : Nat.Coprime S 3 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hmod3).symm
      have hS5 : Nat.Coprime S 5 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hmod5).symm
      have hS9 : Nat.Coprime S 9 := by
        have := Nat.Coprime.pow_right 2 hS3
        simpa using this
      have hc : Nat.Coprime S (9 * (5 ^ e * 3 ^ f)) :=
        Nat.Coprime.mul_right hS9 (Nat.Coprime.mul_right (hS5.pow_right e) (hS3.pow_right f))
      have := Nat.Coprime.eq_one_of_dvd hc hd
      omega
    · have h7 : 7 ≤ q := by
        by_contra h
        push Not at h
        have := hq.two_le
        interval_cases q <;> first | omega | exact absurd hq (by norm_num)
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h7
      have hr : 7 + r - 1 = r + 6 := by omega
      rw [hr] at hgq
      have hpw : (7 + r) ^ (f + 1) = (7 + r) * (7 + r) ^ f := by ring
      rw [hpw] at hgq
      generalize 5 ^ e = P at *
      generalize (7 + r) ^ f = Q at *
      have h2 : S * T * 5 = 9 * (P * Q) := by
        have : 2 * (S * T * 5) = 2 * (9 * (P * Q)) := by linarith
        omega
      have hA : 4 * S < 5 * P := by omega
      have hB : 6 * T < 7 * Q := by
        by_contra hcon
        push Not at hcon
        nlinarith [Nat.mul_le_mul_left (r + 6) hcon]
      have h3 := Nat.mul_lt_mul'' hA hB
      have hPQ : 0 < P * Q := Nat.mul_pos hP hQ
      nlinarith
