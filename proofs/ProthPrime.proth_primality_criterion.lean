import FormalConjectures.Wikipedia.ProthPrime

-- Problem: Proth's primality theorem
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/ProthPrime.lean:91 (declaration ProthPrime.proth_primality_criterion)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P13

theorem prime_factor_mod (k m N : ℕ) (hk : Odd k) (hNodd : N % 2 = 1)
    (hNeq : N = 2 * (k * 2 ^ m) + 1) (a : ZMod N) (ha : a ^ (k * 2 ^ m) = -1)
    (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) : 2 ^ (m + 1) ∣ p - 1 := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  have hb : (ZMod.castHom hpN (ZMod p) a) ^ (k * 2 ^ m) = -1 := by
    rw [← map_pow, ha, map_neg, map_one]
  generalize ZMod.castHom hpN (ZMod p) a = b at hb
  have hk0 : k * 2 ^ m ≠ 0 :=
    mul_ne_zero (Nat.pos_iff_ne_zero.mp hk.pos) (pow_ne_zero _ two_ne_zero)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hk0] at hb
    exact (neg_ne_zero.mpr one_ne_zero) hb.symm
  have hfermat : b ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hb0
  have hN1 : b ^ (2 ^ (m + 1) * k) = 1 := by
    rw [show 2 ^ (m + 1) * k = 2 * (k * 2 ^ m) by ring, pow_mul', hb]
    norm_num
  have hG : b ^ (Nat.gcd (p - 1) (2 ^ (m + 1) * k)) = 1 :=
    (pow_gcd_eq_one).mpr ⟨hfermat, hN1⟩
  have hcop : Nat.Coprime (2 ^ (m + 1)) k :=
    Nat.Coprime.pow_left _
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by have := Nat.odd_iff.mp hk; omega))
  rw [Nat.Coprime.gcd_mul _ hcop] at hG
  by_contra hdvd
  have hsub : Nat.gcd (p - 1) (2 ^ (m + 1)) ∣ 2 ^ m := by
    obtain ⟨j, hj, hjeq⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_right (p - 1) (2 ^ (m + 1)))
    rcases Nat.lt_or_ge j (m + 1) with hlt | hge
    · rw [hjeq]
      exact pow_dvd_pow 2 (by omega)
    · exfalso
      apply hdvd
      have hj' : j = m + 1 := by omega
      have hgeq : Nat.gcd (p - 1) (2 ^ (m + 1)) = 2 ^ (m + 1) := by rw [hjeq, hj']
      rw [← hgeq]
      exact Nat.gcd_dvd_left _ _
  have hdiv : Nat.gcd (p - 1) (2 ^ (m + 1)) * Nat.gcd (p - 1) k ∣ 2 ^ m * k :=
    mul_dvd_mul hsub (Nat.gcd_dvd_right _ _)
  obtain ⟨c, hc⟩ := hdiv
  have h1 : b ^ (k * 2 ^ m) = 1 := by
    rw [mul_comm k, hc, pow_mul, hG, one_pow]
  rw [hb] at h1
  exact ZMod.neg_one_ne_one h1

end OMA.P13

theorem OMA.solution : type_of% @ProthPrime.proth_primality_criterion := by
  intro N hN
  obtain ⟨k, n, hk, hn, hlt, heq⟩ := hN
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨X, hX⟩ : ∃ X, k * 2 ^ m = X := ⟨_, rfl⟩
  have hk1 : 1 ≤ k := by have := hk.pos; omega
  have e1 : N = 2 * X + 1 := by
    rw [← hX, heq]
    ring
  have hNodd : N % 2 = 1 := by omega
  have hhalf : (N - 1) / 2 = X := by omega
  have hXpos : 0 < X := by
    rw [← hX]
    exact Nat.mul_pos hk.pos (by positivity)
  have hNge : 2 ≤ N := by omega
  constructor
  · intro hprime
    haveI : Fact N.Prime := ⟨hprime⟩
    haveI : NeZero N := ⟨hprime.ne_zero⟩
    have hring : ringChar (ZMod N) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      omega
    obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hring
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha ⟨0, by simp⟩
    have hpow : a ^ (N / 2) = -1 := by
      rcases ZMod.pow_div_two_eq_neg_one_or_one N ha0 with h | h
      · exact absurd ((ZMod.euler_criterion N ha0).mpr h) ha
      · exact h
    refine ⟨a, ?_⟩
    have hhalfN : (N - 1) / 2 = N / 2 := by omega
    rw [hhalfN]
    exact hpow
  · rintro ⟨a, ha⟩
    rw [hhalf, ← hX] at ha
    by_contra hnp
    have hq := Nat.minFac_prime (show N ≠ 1 by omega)
    have hsq := Nat.minFac_sq_le_self (show 0 < N by omega) hnp
    have hdv := OMA.P13.prime_factor_mod k m N hk hNodd (by rw [hX]; exact e1) a ha
      N.minFac hq (Nat.minFac_dvd N)
    have hq2 := hq.two_le
    have hle : 2 ^ (m + 1) ≤ N.minFac - 1 := Nat.le_of_dvd (by omega) hdv
    rw [pow_two] at hsq
    generalize 2 ^ (m + 1) = T at hle hlt heq
    generalize N.minFac = q at hle hsq hq2
    have h1 : (T + 1) * (T + 1) ≤ q * q := Nat.mul_le_mul (by omega) (by omega)
    have h2 : (k + 1) * T ≤ T * T := Nat.mul_le_mul (by omega) (le_refl T)
    nlinarith [h1, h2, hsq, heq, hk1, hlt]
