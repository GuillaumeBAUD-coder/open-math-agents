import OMAReductions.R_oeis_a265402_R1

/-!
Proof of `OMA.R_oeis_a265402_R1.H2`.
Let n be composite with n dividing every C(2n,2k), 1 <= k <= n-1, and let p be a prime factor of n.
If p = 2, then 6 C(2n,4) = n (n-1) (2n-1) (2n-3), so C(2n,4)/n would be (odd)/6: impossible.
For odd p write 2n = p^v t with p not dividing t. If v >= 2, take k = p^(v-1): from
k C(2n,2k) = n C(2n-1,2k-1) we get p | C(2n-1,2k-1), contradicting Lucas, because the lowest v
base-p digits of 2n-1 and of 2k-1 are all p-1 except the last digit 1 of 2k-1.
If v = 1, Lucas gives C(pt,pm) = C(t,m) mod p, so p | C(t,m) for every even m in (0,t).
With t = pa + r, the case r >= 2 fails at m = 2, and for r = 1 the conditions force
p | C(a,b) for all 0 < b < a, so a is a power of p and 2n = p + p^s with s >= 2.
-/

namespace OMAProof.A265402H2

open Nat

/-- One step of Lucas's theorem with explicit last digits. -/
lemma luc {p : ℕ} (hp : p.Prime) (a r b s : ℕ) (hr : r < p) (hs : s < p) :
    choose (p * a + r) (p * b + s) ≡ choose r s * choose a b [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (p * a + r) (p * b + s) p _
  have e1 : (p * a + r) % p = r := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have e2 : (p * b + s) % p = s := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
  have e3 : (p * a + r) / p = a := by
    rw [Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hr, add_zero]
  have e4 : (p * b + s) / p = b := by
    rw [Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hs, add_zero]
  rwa [e1, e2, e3, e4] at h

lemma dvd_iff_of_modEq {p a b : ℕ} (h : a ≡ b [MOD p]) : p ∣ a ↔ p ∣ b :=
  h.dvd_iff dvd_rfl

/-- Below the prime, binomial coefficients are prime to it. -/
lemma not_dvd_choose_lt {p r k : ℕ} (hp : p.Prime) (hr : r < p) (hk : k ≤ r) :
    ¬ p ∣ choose r k := by
  intro h
  have h1 := Nat.choose_mul_factorial_mul_factorial hk
  have h2 : p ∣ r ! := by
    rw [← h1]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _
  exact absurd ((hp.dvd_factorial).mp h2) (by omega)

/-- If p divides all inner binomial coefficients of a, then a is a power of p. -/
lemma pow_of_dvd_choose {p : ℕ} (hp : p.Prime) :
    ∀ a : ℕ, 1 ≤ a → (∀ b, 0 < b → b < a → p ∣ choose a b) → ∃ j, a = p ^ j := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha hdiv
    by_cases hap : a < p
    · by_cases ha1 : a = 1
      · exact ⟨0, by simp [ha1]⟩
      · exfalso
        have := hdiv 1 one_pos (by omega)
        rw [Nat.choose_one_right] at this
        exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    · have hp1 := hp.two_le
      set c := a / p with hc
      set d := a % p with hd
      have hdec : p * c + d = a := Nat.div_add_mod a p
      have hdp : d < p := Nat.mod_lt _ hp.pos
      have hc1 : 1 ≤ c := (Nat.le_div_iff_mul_le hp.pos).mpr (by omega)
      by_cases hd0 : d = 0
      · have hca : c < a := by
          have : p * c = a := by omega
          nlinarith
        have hcdiv : ∀ b, 0 < b → b < c → p ∣ choose c b := by
          intro b hb hbc
          have hb' : 0 < p * b := Nat.mul_pos hp.pos hb
          have hbc' : p * b < a := by
            have := Nat.mul_lt_mul_of_pos_left hbc hp.pos
            omega
          have h := hdiv (p * b) hb' hbc'
          have hl := luc hp c 0 b 0 hp.pos hp.pos
          rw [Nat.choose_self, one_mul, add_zero, add_zero] at hl
          rw [← hdec, hd0, add_zero] at h
          exact (dvd_iff_of_modEq hl).mp h
        obtain ⟨j, hj⟩ := ih c hca hc1 hcdiv
        exact ⟨j + 1, by rw [← hdec, hd0, add_zero, hj, pow_succ, mul_comm]⟩
      · exfalso
        have hb : 0 < p * c := Nat.mul_pos hp.pos hc1
        have hba : p * c < a := by omega
        have h := hdiv (p * c) hb hba
        have hl := luc hp c d c 0 hdp hp.pos
        rw [Nat.choose_zero_right, one_mul, Nat.choose_self, add_zero, hdec] at hl
        have := (dvd_iff_of_modEq hl).mp h
        exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- The core digit analysis in the case v = 1. -/
lemma core {p t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpt : ¬ p ∣ t) (ht2 : t ≠ 2)
    (hte : Even t) (ht0 : t ≠ 0)
    (hdiv : ∀ m, Even m → 0 < m → m < t → p ∣ choose t m) : ∃ j, 1 ≤ j ∧ t = 1 + p ^ j := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set a := t / p with ha
  set r := t % p with hr
  have hdec : p * a + r = t := Nat.div_add_mod t p
  have hrp : r < p := Nat.mod_lt _ hp.pos
  have hr0 : r ≠ 0 := fun h => hpt (Nat.dvd_of_mod_eq_zero h)
  have ht4 : 4 ≤ t := by
    obtain ⟨u, hu⟩ := hte
    omega
  by_cases hr1 : r = 1
  · have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · rw [h] at hdec
        omega
      · exact h
    have hall : ∀ b, 0 < b → b < a → p ∣ choose a b := by
      intro b hb hba
      have hpb : p * b < p * a := Nat.mul_lt_mul_of_pos_left hba hp.pos
      rcases Nat.even_or_odd b with hbe | hbo
      · have hm : Even (p * b) := hbe.mul_left p
        have h := hdiv (p * b) hm (Nat.mul_pos hp.pos hb) (by omega)
        have hl := luc hp a 1 b 0 (by omega) hp.pos
        rw [Nat.choose_zero_right, one_mul, add_zero] at hl
        rw [← hdec, hr1] at h
        exact (dvd_iff_of_modEq hl).mp h
      · have hm : Even (p * b + 1) := (hpodd.mul hbo).add_one
        have h := hdiv (p * b + 1) hm (by omega) (by omega)
        have hl := luc hp a 1 b 1 (by omega) (by omega)
        rw [Nat.choose_self, one_mul] at hl
        rw [← hdec, hr1] at h
        exact (dvd_iff_of_modEq hl).mp h
    obtain ⟨j, hj⟩ := pow_of_dvd_choose hp a ha1 hall
    refine ⟨j + 1, by omega, ?_⟩
    rw [← hdec, hr1, hj, pow_succ]
    ring
  · exfalso
    have h := hdiv 2 even_two (by omega) (by omega)
    have hl := luc hp a r 0 2 hrp (by omega)
    rw [mul_zero, zero_add, Nat.choose_zero_right, mul_one, hdec] at hl
    exact not_dvd_choose_lt hp hrp (by omega) ((dvd_iff_of_modEq hl).mp h)

/-- Lucas with all lower digits equal to p - 1. -/
lemma low_digits {p t : ℕ} (hp : p.Prime) (ht : 1 ≤ t) :
    ∀ j, ¬ p ∣ choose (p ^ (j + 1) * t - 1) (2 * p ^ j - 1) := by
  intro j
  induction j with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, mul_one]
    rw [show 2 - 1 = 1 by rfl, Nat.choose_one_right]
    intro h
    have h1 : p ∣ p * t := dvd_mul_right p t
    have hpt : 1 ≤ p * t := Nat.mul_pos hp.pos ht
    have h2 : p ∣ p * t - (p * t - 1) := Nat.dvd_sub h1 h
    rw [show p * t - (p * t - 1) = 1 by omega] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  | succ j ih =>
    intro h
    have hX : 1 ≤ p ^ (j + 1) * t := Nat.mul_pos (pow_pos hp.pos _) ht
    have hY : 1 ≤ 2 * p ^ j := Nat.mul_pos two_pos (pow_pos hp.pos _)
    have hp1 : 1 ≤ p := hp.pos
    have e1 : p ^ (j + 1 + 1) * t - 1 = p * (p ^ (j + 1) * t - 1) + (p - 1) := by
      have : p ^ (j + 1 + 1) * t = p * (p ^ (j + 1) * t) := by ring
      rw [this]
      obtain ⟨X, hX'⟩ : ∃ X, p ^ (j + 1) * t = X + 1 := ⟨_, (Nat.sub_add_cancel hX).symm⟩
      rw [hX', Nat.add_sub_cancel]
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    have e2 : 2 * p ^ (j + 1) - 1 = p * (2 * p ^ j - 1) + (p - 1) := by
      have : 2 * p ^ (j + 1) = p * (2 * p ^ j) := by ring
      rw [this]
      obtain ⟨Y, hY'⟩ : ∃ Y, 2 * p ^ j = Y + 1 := ⟨_, (Nat.sub_add_cancel hY).symm⟩
      rw [hY', Nat.add_sub_cancel]
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    rw [e1, e2] at h
    have hl := luc hp (p ^ (j + 1) * t - 1) (p - 1) (2 * p ^ j - 1) (p - 1) (by omega) (by omega)
    rw [Nat.choose_self, one_mul] at hl
    exact ih ((dvd_iff_of_modEq hl).mp h)

end OMAProof.A265402H2

open OMAProof.A265402H2 in
theorem OMA.solution : OMA.R_oeis_a265402_R1.H2 := by
  intro n hn hnp hdiv p hp hpn
  have hn0 : n ≠ 0 := by omega
  by_cases hp2 : p = 2
  · exfalso
    subst hp2
    obtain ⟨u, hu⟩ := hpn
    have hu2 : 2 ≤ u := by
      by_contra h
      interval_cases u
      · omega
      · exact hnp (by rw [hu]; exact Nat.prime_two)
    obtain ⟨q, rfl⟩ : ∃ q, u = q + 2 := ⟨u - 2, by omega⟩
    subst hu
    have hk : (2 : ℕ) ∈ Finset.Icc 1 (2 * (q + 2) - 1) := by
      rw [Finset.mem_Icc]
      omega
    obtain ⟨c, hc⟩ := hdiv 2 hk
    have hd := Nat.descFactorial_eq_factorial_mul_choose (2 * (2 * (q + 2))) (2 * 2)
    rw [hc] at hd
    have hdf : (2 * (2 * (q + 2))).descFactorial (2 * 2) =
        (4 * q + 8) * (4 * q + 7) * (4 * q + 6) * (4 * q + 5) := by
      rw [show 2 * (2 * (q + 2)) = 4 * q + 8 by ring, show 2 * 2 = 4 by rfl]
      simp [Nat.descFactorial_succ]
      ring
    rw [hdf, show Nat.factorial (2 * 2) = 24 by rfl] at hd
    have hX : (2 * q + 4) * (6 * c) = (2 * q + 4) * ((4 * q + 7) * (2 * q + 3) * (4 * q + 5)) := by
      nlinarith
    have hX' := Nat.eq_of_mul_eq_mul_left (by omega) hX
    have hodd : (4 * q + 7) * (2 * q + 3) * (4 * q + 5) =
        2 * (16 * q ^ 3 + 72 * q ^ 2 + 107 * q + 52) + 1 := by ring
    omega
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    obtain ⟨v, t, hpt, h2n⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := 2 * n) (by omega) p
      hp.one_lt.ne'
    have ht0 : t ≠ 0 := by
      rintro rfl
      omega
    have hv : v ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at h2n
      exact hpt (h2n ▸ Dvd.dvd.mul_left hpn 2)
    by_cases hv1 : v = 1
    · subst hv1
      rw [pow_one] at h2n
      have hte : Even t := by
        have h2 : 2 ∣ p * t := ⟨n, h2n.symm⟩
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm hp2
        · exact even_iff_two_dvd.mpr h
      have ht2 : t ≠ 2 := by
        rintro rfl
        have : n = p := by omega
        exact hnp (this ▸ hp)
      have hcore : ∀ m, Even m → 0 < m → m < t → p ∣ Nat.choose t m := by
        intro m hm hm0 hmt
        obtain ⟨b, hb⟩ := hm
        have hpm : p * m < p * t := Nat.mul_lt_mul_of_pos_left hmt hp.pos
        have hpb : p * m = p * b + p * b := by rw [hb]; ring
        have hb1 : 1 ≤ p * b := Nat.mul_pos hp.pos (by omega)
        have hk : p * b ∈ Finset.Icc 1 (n - 1) := by
          rw [Finset.mem_Icc]
          omega
        have h := dvd_trans hpn (hdiv (p * b) hk)
        rw [show 2 * n = p * t + 0 by omega, show 2 * (p * b) = p * m + 0 by omega] at h
        have hl := luc hp t 0 m 0 hp.pos hp.pos
        rw [Nat.choose_self, one_mul] at hl
        exact (dvd_iff_of_modEq hl).mp h
      obtain ⟨j, hj1, hj⟩ := core hp hp2 hpt ht2 hte ht0 hcore
      refine ⟨j + 1, by omega, ?_⟩
      rw [h2n, hj, pow_succ]
      ring
    · exfalso
      obtain ⟨j, rfl⟩ : ∃ j, v = j + 2 := ⟨v - 2, by omega⟩
      have ht1 : 1 ≤ t := by omega
      have hpk : p ^ (j + 1) < n := by
        have h3 : p ^ (j + 2) * t ≥ 3 * p ^ (j + 1) := by
          rw [pow_succ]
          have h4 : p ^ (j + 1) * 3 ≤ p ^ (j + 1) * p := Nat.mul_le_mul_left _ hp3
          have h5 : p ^ (j + 1) * p ≤ p ^ (j + 1) * p * t := Nat.le_mul_of_pos_right _ ht1
          omega
        omega
      have hk : p ^ (j + 1) ∈ Finset.Icc 1 (n - 1) := by
        rw [Finset.mem_Icc]
        exact ⟨pow_pos hp.pos _, by omega⟩
      obtain ⟨c, hc⟩ := hdiv _ hk
      have hK : 1 ≤ 2 * p ^ (j + 1) := Nat.mul_pos two_pos (pow_pos hp.pos _)
      have hid := Nat.add_one_mul_choose_eq (2 * n - 1) (2 * p ^ (j + 1) - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * n), Nat.sub_add_cancel hK, hc] at hid
      have hid2 : (2 * n) * Nat.choose (2 * n - 1) (2 * p ^ (j + 1) - 1) =
          (2 * n) * (c * p ^ (j + 1)) := by
        rw [hid]
        ring
      have hid3 := Nat.eq_of_mul_eq_mul_left (by omega) hid2
      have hdv : p ∣ Nat.choose (2 * n - 1) (2 * p ^ (j + 1) - 1) := by
        rw [hid3]
        exact Dvd.dvd.mul_left (dvd_pow_self p (by omega)) c
      rw [h2n] at hdv
      exact low_digits hp ht1 (j + 1) hdv
