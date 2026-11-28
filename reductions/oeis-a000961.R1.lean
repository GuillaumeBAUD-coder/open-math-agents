import OMAStatements.S_oeis_a000961

-- Reduction oeis-a000961.R1 of A000961: Powers of primes. Alternatively, 1 and the prime powers (p^k, p prime, k >= 1).
-- Credit: @notswizz
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Write S(m) for the sum of k^phi(m) over k < m. Proved here: the forward direction in full (1 and every prime power
-- satisfy S(m) = phi(m) mod m), and the converse for every even m and every m with exactly two distinct prime
-- factors. Key lemma (crit): if q^b exactly divides m, then S(m) = m - m/q mod q^b. So the congruence forces
-- q | r - phi(r) for every prime q | m, where r = m/q^b. For q = 2 this fails because r is odd and phi(r) is even.
-- When r = p^e, r - phi(r) = p^(e-1), which q does not divide.
-- Remaining: odd m with at least three distinct prime factors, H1 squarefree (where the condition reads
-- m | sum_q m/q + phi(m), Giuga-type) and H2 non-squarefree. A search found no such m below 2*10^8.

namespace OMA.R_oeis_a000961_R1

open Nat

theorem mult_count (m q : ℕ) (hq : 0 < q) (hqm : q ∣ m) :
    ((Finset.range m).filter (fun k => q ∣ k)).card = m / q := by
  obtain ⟨t, rfl⟩ := hqm
  rw [Nat.mul_div_cancel_left t hq]
  have : (Finset.range (q*t)).filter (fun k => q ∣ k) = (Finset.range t).image (fun j => q * j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, j, rfl⟩
      exact ⟨j, by nlinarith, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨by nlinarith, dvd_mul_right q j⟩
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa [hq.ne'] using h)]
  simp

theorem nonmult_count (m q : ℕ) (hq : 0 < q) (hqm : q ∣ m) :
    ((Finset.range m).filter (fun k => ¬ q ∣ k)).card = m - m / q := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range m) (fun k => q ∣ k)
  rw [mult_count m q hq hqm, Finset.card_range] at h
  omega

theorem term_local (m q b k : ℕ) (hq : q.Prime) (hb : 1 ≤ b) (hbm : q ^ b ∣ m) (hm : 0 < m) :
    ((k ^ φ m : ℕ) : ZMod (q ^ b)) = if ¬ q ∣ k then 1 else 0 := by
  have hdvd : φ (q ^ b) ∣ φ m := Nat.totient_dvd_of_dvd hbm
  have htot : φ (q ^ b) = q ^ (b - 1) * (q - 1) := Nat.totient_prime_pow hq (by omega)
  by_cases hk : q ∣ k
  · rw [if_neg (not_not.mpr hk)]
    rw [ZMod.natCast_eq_zero_iff]
    have hpos : 0 < φ m := Nat.totient_pos.mpr hm
    have hle : φ (q ^ b) ≤ φ m := Nat.le_of_dvd hpos hdvd
    have hb2 : b ≤ q ^ (b - 1) := by
      have : b - 1 < 2 ^ (b - 1) := Nat.lt_two_pow_self
      have : 2 ^ (b-1) ≤ q ^ (b-1) := Nat.pow_le_pow_left hq.two_le _
      omega
    have hq1 : 1 ≤ q - 1 := by have := hq.two_le; omega
    have hbphi : b ≤ φ m := by
      calc b ≤ q ^ (b-1) := hb2
        _ ≤ q ^ (b-1) * (q - 1) := Nat.le_mul_of_pos_right _ hq1
        _ = φ (q ^ b) := htot.symm
        _ ≤ φ m := hle
    exact dvd_trans (pow_dvd_pow_of_dvd hk b) (pow_dvd_pow k hbphi)

  · rw [if_pos hk]
    have hc : k.Coprime (q ^ b) := Nat.Coprime.pow_right _ ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hk))
    obtain ⟨e, he⟩ := hdvd
    rw [he, pow_mul]
    have h1 := Nat.ModEq.pow_totient hc
    have h2 : (k ^ φ (q ^ b)) ^ e ≡ 1 ^ e [MOD q ^ b] := Nat.ModEq.pow e h1
    rw [one_pow] at h2
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
    simpa using this

theorem sum_local (m q b : ℕ) (hq : q.Prime) (hb : 1 ≤ b) (hbm : q ^ b ∣ m) (hm : 0 < m) :
    ((∑ k ∈ Finset.range m, k ^ φ m : ℕ) : ZMod (q ^ b)) = ((m - m / q : ℕ) : ZMod (q ^ b)) := by
  rw [Nat.cast_sum, Finset.sum_congr rfl (fun k _ => term_local m q b k hq hb hbm hm), Finset.sum_boole,
    nonmult_count m q hq.pos (dvd_trans (dvd_pow_self q (by omega)) hbm)]

-- local criterion
theorem crit (m q : ℕ) (hq : q.Prime) (hqm : q ∣ m) (hm : 0 < m)
    (h : (∑ k ∈ Finset.range m, k ^ φ m) % m = φ m % m) :
    (q : ℤ) ∣ (φ (m / q ^ m.factorization q) : ℤ) - (m / q ^ m.factorization q : ℕ) := by
  set b := m.factorization q with hbdef
  set r := m / q ^ b with hr
  have hb : 1 ≤ b := (hq.dvd_iff_one_le_factorization hm.ne').mp hqm
  have hmr : q ^ b * r = m := Nat.ordProj_mul_ordCompl_eq_self m q
  have hbm : q ^ b ∣ m := ⟨r, hmr.symm⟩
  have hcop : (q ^ b).Coprime r := Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hq hm.ne')
  have e1 := sum_local m q b hq hb hbm hm
  have e2 : ((∑ k ∈ Finset.range m, k ^ φ m : ℕ) : ZMod (q ^ b)) = ((φ m : ℕ) : ZMod (q ^ b)) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact Nat.ModEq.of_dvd hbm h
  rw [e1, ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd] at e2
  -- e2 : (q^b : ℤ) ∣ φ m - (m - m/q)
  have hmq : m / q = q ^ (b - 1) * r := by
    rw [← hmr]
    have : q ^ b = q * q ^ (b-1) := by rw [← pow_succ']; congr 1; omega
    rw [this, mul_assoc, Nat.mul_div_cancel_left _ hq.pos]
  have hphi : φ m = q ^ (b - 1) * (q - 1) * φ r := by
    rw [← hmr, Nat.totient_mul hcop, Nat.totient_prime_pow hq (by omega)]
  have hle : m / q ≤ m := Nat.div_le_self m q
  rw [hphi, Nat.cast_sub hle, hmq, ← hmr] at e2
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hqb : (q:ℤ) ^ b = (q:ℤ) ^ (b-1) * q := by rw [← pow_succ]; congr 1; omega
  push_cast [Nat.cast_sub hq1] at e2
  have e3 : ((q:ℤ) ^ (b-1) * q) ∣ (q:ℤ) ^ (b-1) * (((q:ℤ) - 1) * ((φ r : ℤ) - r)) := by
    rw [← hqb]
    have : (q:ℤ) ^ (b-1) * (((q:ℤ) - 1) * ((φ r : ℤ) - r)) =
      (q:ℤ) ^ (b - 1) * ((q:ℤ) - 1) * (φ r : ℤ) - ((q:ℤ) ^ b * r - (q:ℤ) ^ (b - 1) * r) := by
      rw [hqb]; ring
    rw [this]; exact e2
  have hne : (q:ℤ) ^ (b-1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne_zero)
  have e4 := (mul_dvd_mul_iff_left hne).mp e3
  have e5 : (q:ℤ) ∣ (q:ℤ) * ((φ r : ℤ) - r) := dvd_mul_right _ _
  have : ((φ r : ℤ) - r) = (q:ℤ) * ((φ r : ℤ) - r) - ((q:ℤ) - 1) * ((φ r : ℤ) - r) := by ring
  rw [this]; exact dvd_sub e5 e4

theorem ppow_fail (q p e : ℕ) (hq : q.Prime) (hp : p.Prime) (hpq : p ≠ q) (he : 1 ≤ e) :
    ¬ (q : ℤ) ∣ (φ (p ^ e) : ℤ) - (p ^ e : ℕ) := by
  rw [Nat.totient_prime_pow hp (by omega)]
  have : ((p ^ (e-1) * (p - 1) : ℕ) : ℤ) - ((p ^ e : ℕ) : ℤ) = - ((p ^ (e-1) : ℕ) : ℤ) := by
    have hp1 : 1 ≤ p := hp.one_lt.le
    have : p ^ e = p ^ (e-1) * p := by rw [← pow_succ]; congr 1; omega
    rw [this]; push_cast [Nat.cast_sub hp1]; ring
  rw [this, dvd_neg, Int.natCast_dvd_natCast]
  intro h
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)).symm

theorem fwd (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) :
    (∑ k ∈ Finset.range (p^a), k ^ φ (p^a)) % (p^a) = φ (p^a) % (p^a) := by
  have hm : 0 < p ^ a := pow_pos hp.pos a
  have e := sum_local (p^a) p a hp ha dvd_rfl hm
  rw [← ZMod.natCast_eq_natCast_iff']
  rw [e]
  congr 1
  rw [Nat.totient_prime_pow hp (by omega)]
  have : p ^ a = p ^ (a-1) * p := by rw [← pow_succ]; congr 1; omega
  rw [this, Nat.mul_div_cancel _ hp.pos, Nat.mul_sub_one]

theorem dvd_compl (m q p : ℕ) (hm : m ≠ 0) (hq : q.Prime) (hp : p.Prime) (hpq : p ≠ q) (hpm : p ∣ m) :
    p ∣ m / q ^ m.factorization q := by
  have hmr := Nat.ordProj_mul_ordCompl_eq_self m q
  have hc : p.Coprime (q ^ m.factorization q) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hq).mpr hpq)
  rw [← hmr] at hpm
  exact hc.dvd_of_dvd_mul_left hpm

def H1 : Prop := ∀ m : ℕ, Odd m → Squarefree m → 3 ≤ m.primeFactors.card →
  (∑ k ∈ Finset.range m, k ^ Nat.totient m) % m ≠ Nat.totient m % m

def H2 : Prop := ∀ m : ℕ, Odd m → ¬ Squarefree m → 3 ≤ m.primeFactors.card →
  (∑ k ∈ Finset.range m, k ^ Nat.totient m) % m ≠ Nat.totient m % m

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000961.main := by
  intro h1 h2 m hm
  have hm0 : m ≠ 0 := hm.ne'
  constructor
  · rintro (rfl | hpp)
    · simp
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
      exact fwd p k hp hk
  · intro h
    by_contra hn
    simp only [OMA.S_oeis_a000961.InA000961, not_or] at hn
    obtain ⟨hn1, hnp⟩ := hn
    have hc1 : m.primeFactors.card ≠ 1 := fun hc => hnp (isPrimePow_iff_card_primeFactors_eq_one.mpr hc)
    have hc0 : m.primeFactors.card ≠ 0 := by
      intro hc
      rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hc) with h' | h' <;> omega
    by_cases he : 2 ∣ m
    · have hcr := crit m 2 Nat.prime_two he hm h
      obtain ⟨p, hpm, hp2⟩ := Finset.exists_mem_ne (s := m.primeFactors) (by omega) 2
      have hp := Nat.prime_of_mem_primeFactors hpm
      have hpr := dvd_compl m 2 p hm0 Nat.prime_two hp hp2 (Nat.dvd_of_mem_primeFactors hpm)
      set r := m / 2 ^ m.factorization 2 with hr
      have hr0 : r ≠ 0 := (Nat.ordCompl_pos 2 hm0).ne'
      have hrodd : ¬ 2 ∣ r := Nat.not_dvd_ordCompl Nat.prime_two hm0
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hr3 : 2 < r := by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hpr; omega
      obtain ⟨t, ht⟩ := Nat.totient_even hr3
      apply hrodd
      have : (2:ℤ) ∣ (r : ℤ) := by
        have h2 : (2:ℤ) ∣ (φ r : ℤ) := ⟨t, by rw [ht]; push_cast; ring⟩
        have := dvd_sub h2 (by exact_mod_cast hcr : (2:ℤ) ∣ (φ r : ℤ) - (r : ℤ))
        simpa using this
      exact_mod_cast this
    · have hodd : Odd m := Nat.odd_iff.mpr (by omega)
      by_cases hc2 : m.primeFactors.card = 2
      · obtain ⟨p, q, hpq, hpq1⟩ := Finset.card_eq_two.mp hc2
        have hp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hpq1]; simp)
        have hq : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hpq1]; simp)
        have hqm : q ∣ m := Nat.dvd_of_mem_primeFactors (by rw [hpq1]; simp)
        have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors (by rw [hpq1]; simp)
        have hcr := crit m q hq hqm hm h
        have hpr := dvd_compl m q p hm0 hq hp hpq hpm
        set r := m / q ^ m.factorization q with hr
        have hr0 : r ≠ 0 := (Nat.ordCompl_pos q hm0).ne'
        have hqr : ¬ q ∣ r := Nat.not_dvd_ordCompl hq hm0
        have hrm : r ∣ m := Nat.ordCompl_dvd m q
        have hrp : r = p ^ r.primeFactorsList.length := by
          apply Nat.eq_prime_pow_of_unique_prime_dvd hr0
          intro d hd hdr
          have : d ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hd, dvd_trans hdr hrm, hm0⟩
          rw [hpq1] at this
          rcases Finset.mem_insert.mp this with h' | h'
          · exact h'
          · rw [Finset.mem_singleton] at h'; subst h'; exact absurd hdr hqr
        have he1 : 1 ≤ r.primeFactorsList.length := by
          rcases Nat.eq_zero_or_pos r.primeFactorsList.length with h0 | h0
          · rw [h0, pow_zero] at hrp; rw [hrp] at hpr; exact absurd (Nat.le_of_dvd one_pos hpr) (by have := hp.two_le; omega)
          · exact h0
        rw [hrp] at hcr
        exact ppow_fail q p _ hq hp hpq he1 hcr
      · by_cases hsq : Squarefree m
        · exact h1 m hodd hsq (by omega) h
        · exact h2 m hodd hsq (by omega) h

end OMA.R_oeis_a000961_R1
