import OMAReductions.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1

/-!
# Proof of `ColossallyAbundantNumber.alaoglu_erdos_prime_powers_rational_conjecture.R1.H2`

If `p` is prime, `t : ℚ`, and `(p : ℝ) ^ (t : ℝ) = r` for some `r : ℚ`, then `t` is an integer:
reducing to `0 ≤ t` by negation if necessary, write `t = a / b` in lowest terms and `r = u / v`
with `u, v > 0`. Raising to the `b`-th power gives `p ^ a * v ^ b = u ^ b` in `ℕ`; comparing
`Nat.factorization` at `p` yields `b ∣ a`, so `b = 1` by coprimality and `t = t.num`.
-/

namespace OMA.P_ColAbundant_H2

private lemma rat_pow_eq_int_of_nonneg {p : ℕ} {t : ℚ} (hp : p.Prime) (ht : 0 ≤ t)
    {r : ℚ} (hr : (p : ℝ) ^ (t : ℝ) = (r : ℝ)) : ∃ k : ℤ, t = k := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hr_pos_R : (0 : ℝ) < (r : ℝ) := by
    rw [← hr]
    exact Real.rpow_pos_of_pos hp_pos _
  have hr_pos : (0 : ℚ) < r := by exact_mod_cast hr_pos_R
  set a : ℕ := t.num.natAbs
  set b : ℕ := t.den
  have hb_pos : 0 < b := t.den_pos
  have ht_num_nonneg : 0 ≤ t.num := Rat.num_nonneg.mpr ht
  have ha_eq : (a : ℤ) = t.num := Int.natAbs_of_nonneg ht_num_nonneg
  have ht_eq_div : (t : ℝ) = (a : ℝ) / (b : ℝ) := by
    have h1 : (t : ℚ) = (t.num : ℚ) / (t.den : ℚ) := (Rat.num_div_den t).symm
    have h2 : (t : ℝ) = ((t.num : ℚ) / (t.den : ℚ) : ℚ) := congrArg ((↑) : ℚ → ℝ) h1
    rw [h2, ← ha_eq]
    push_cast
    rfl
  have hpow_R : (p : ℝ) ^ a = (r : ℝ) ^ b := by
    have hbR : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb_pos.ne'
    calc (p : ℝ) ^ a
        = (p : ℝ) ^ (a : ℝ) := (Real.rpow_natCast (p : ℝ) a).symm
      _ = (p : ℝ) ^ (((a : ℝ) / (b : ℝ)) * (b : ℝ)) := by congr 1; field_simp [hbR]
      _ = ((p : ℝ) ^ ((a : ℝ) / (b : ℝ))) ^ (b : ℝ) := Real.rpow_mul hp_pos.le _ _
      _ = ((p : ℝ) ^ (t : ℝ)) ^ b := by rw [← ht_eq_div, Real.rpow_natCast]
      _ = (r : ℝ) ^ b := by rw [hr]
  have hpow_Q : (p : ℚ) ^ a = r ^ b := by exact_mod_cast hpow_R
  set u : ℕ := r.num.natAbs
  set v : ℕ := r.den
  have hv_pos : 0 < v := r.den_pos
  have hr_num_pos : 0 < r.num := Rat.num_pos.mpr hr_pos
  have hu_eq : (u : ℤ) = r.num := Int.natAbs_of_nonneg hr_num_pos.le
  have hu_pos : 0 < u := by omega
  have hr_div : r = (u : ℚ) / (v : ℚ) := by
    rw [← Rat.num_div_den r, ← hu_eq]
    push_cast
    rfl
  have hnat_Q : ((p ^ a * v ^ b : ℕ) : ℚ) = ((u ^ b : ℕ) : ℚ) := by
    rw [hr_div, div_pow] at hpow_Q
    have hvQ : (v : ℚ) ^ b ≠ 0 := pow_ne_zero b (Nat.cast_ne_zero.mpr hv_pos.ne')
    have hmul := congrArg (· * (v : ℚ) ^ b) hpow_Q
    simp only [div_mul_cancel₀ _ hvQ] at hmul
    push_cast
    exact hmul
  have hnat : p ^ a * v ^ b = u ^ b := by exact_mod_cast hnat_Q
  have hfac := congrArg (fun n => Nat.factorization n p) hnat
  have hpa_ne : p ^ a ≠ 0 := pow_ne_zero a hp.ne_zero
  have hvb_ne : v ^ b ≠ 0 := pow_ne_zero b hv_pos.ne'
  rw [Nat.factorization_mul hpa_ne hvb_ne, Finsupp.add_apply,
    Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow,
    Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    smul_eq_mul, smul_eq_mul, smul_eq_mul,
    hp.factorization_self, mul_one] at hfac
  have hb_dvd_a : b ∣ a := by
    have : b * (u.factorization p - v.factorization p) = a := by
      have hle : v.factorization p ≤ u.factorization p := by
        by_contra hlt
        have hgt : u.factorization p < v.factorization p := not_le.mp hlt
        have : b * u.factorization p < b * v.factorization p := Nat.mul_lt_mul_of_pos_left hgt hb_pos
        omega
      rw [Nat.mul_sub_left_distrib]
      omega
    exact ⟨u.factorization p - v.factorization p, this.symm⟩
  have hb_eq_one : b = 1 :=
    Nat.dvd_one.mp (t.reduced.gcd_eq_one ▸ Nat.dvd_gcd hb_dvd_a dvd_rfl)
  refine ⟨t.num, ?_⟩
  calc t = (t.num : ℚ) / (b : ℚ) := (Rat.num_div_den t).symm
    _ = (t.num : ℚ) := by rw [hb_eq_one]; simp

theorem h2_proof :
    OMA.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1.H2 := by
  intro p t hp ⟨r, hr⟩
  by_cases ht : 0 ≤ t
  · exact rat_pow_eq_int_of_nonneg hp ht hr
  · have htneg : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hrinv : (p : ℝ) ^ ((-t : ℚ) : ℝ) = ((r⁻¹ : ℚ) : ℝ) := by
      push_cast
      rw [Real.rpow_neg hp_pos.le, hr]
    obtain ⟨k, hk⟩ := rat_pow_eq_int_of_nonneg hp htneg hrinv
    refine ⟨-k, ?_⟩
    have : -t = (k : ℚ) := hk
    push_cast
    linarith

end OMA.P_ColAbundant_H2

theorem OMA.solution :
    OMA.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1.H2 :=
  OMA.P_ColAbundant_H2.h2_proof
