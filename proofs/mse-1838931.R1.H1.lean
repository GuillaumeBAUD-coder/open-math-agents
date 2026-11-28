import OMAReductions.R_mse_1838931_R1

-- Step mse-1838931.R1.H1: hypothesis H1 of reduction mse-1838931.R1
-- Credit: @keiichisince1986-bot

namespace OMA.Mse1838931R1H1

private lemma lt_of_prime_dvd_factorial_add_one {p q : ℕ} (hp : p.Prime)
    (hdvd : p ∣ q.factorial + 1) : q < p := by
  by_contra! hle
  have hfac : p ∣ q.factorial := Nat.dvd_factorial hp.pos hle
  have h1 : p ∣ 1 := (Nat.dvd_add_right hfac).mp hdvd
  exact hp.not_dvd_one h1

private lemma factorial_reflect_zmod (p : ℕ) (hp1 : 1 ≤ p) :
    ∀ k : ℕ, k ≤ p - 1 →
      ((p - 1 - k).factorial : ZMod p) * (-1 : ZMod p) ^ k * (k.factorial : ZMod p) =
        ((p - 1).factorial : ZMod p) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp
  | succ k ih =>
    intro hk
    rw [← ih (by omega)]
    have hstep : p - 1 - k = (p - 1 - (k + 1)) + 1 := by omega
    rw [hstep, Nat.factorial_succ, Nat.factorial_succ]
    have hcast : (((p - 1 - (k + 1) + 1 : ℕ) : ZMod p)) = -(((k + 1 : ℕ) : ZMod p)) := by
      have hsub : p - 1 - (k + 1) + 1 = p - (k + 1) := by omega
      rw [hsub, Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    simp only [Nat.cast_mul, hcast, pow_succ]
    ring

end OMA.Mse1838931R1H1

theorem OMA.solution : OMA.R_mse_1838931_R1.H1 := by
  constructor
  · intro N
    obtain ⟨q, hNq, hq⟩ := Nat.exists_infinite_primes (N + 1)
    let p := (q.factorial + 1).minFac
    have hne1 : q.factorial + 1 ≠ 1 := by
      have hpos : 0 < q.factorial := Nat.factorial_pos q
      omega
    have hp : p.Prime := Nat.minFac_prime hne1
    have hdvd : p ∣ q.factorial + 1 := Nat.minFac_dvd (q.factorial + 1)
    exact ⟨p, q, by omega, OMA.Mse1838931R1H1.lt_of_prime_dvd_factorial_add_one hp hdvd,
      hp, hq, hdvd⟩
  · intro p q hp hq hq2 hdvd
    have hqp : q < p := OMA.Mse1838931R1H1.lt_of_prime_dvd_factorial_add_one hp hdvd
    have : Fact p.Prime := ⟨hp⟩
    have hrefl := OMA.Mse1838931R1H1.factorial_reflect_zmod p (by omega) (q - 1) (by omega)
    rw [show p - 1 - (q - 1) = p - q by omega, ZMod.wilsons_lemma p] at hrefl
    obtain ⟨m, hm⟩ := hq.odd_of_ne_two (by omega)
    have hpow : (-1 : ZMod p) ^ (q - 1) = 1 := by
      rw [show q - 1 = 2 * m by omega, pow_mul, neg_one_sq, one_pow]
    rw [hpow, mul_one] at hrefl
    have hmul : ((p - q).factorial : ZMod p) * (q.factorial : ZMod p) = -(q : ZMod p) := by
      have hq1 : q = (q - 1) + 1 := by omega
      have hqfac : q.factorial = q * (q - 1).factorial := by
        conv_lhs => rw [hq1, Nat.factorial_succ]
        rw [← hq1]
      rw [hqfac, Nat.cast_mul]
      linear_combination (q : ZMod p) * hrefl
    have hqmod : (q.factorial : ZMod p) = -1 := by
      have hz : ((q.factorial + 1 : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff (q.factorial + 1) p).mpr hdvd
      push_cast at hz
      linear_combination hz
    rw [hqmod] at hmul
    have heq : (q : ZMod p) = ((p - q).factorial : ZMod p) := by
      linear_combination hmul
    have hcongr : q ≡ (p - q).factorial [MOD p] :=
      (ZMod.natCast_eq_natCast_iff q (p - q).factorial p).mp heq
    have hgt2 : 2 < p - q := by
      by_contra hle2
      have hcases : p - q = 1 ∨ p - q = 2 := by omega
      rcases hcases with h1 | h2
      · rw [h1] at hcongr
        change q % p = (1 : ℕ).factorial % p at hcongr
        rw [Nat.factorial_one, Nat.mod_eq_of_lt hqp, Nat.mod_eq_of_lt (by omega)] at hcongr
        omega
      · rw [h2] at hcongr
        change q % p = (2 : ℕ).factorial % p at hcongr
        rw [Nat.factorial_two, Nat.mod_eq_of_lt hqp, Nat.mod_eq_of_lt (by omega)] at hcongr
        omega
    exact ⟨hqp, hgt2, hcongr⟩
