import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H3_R1

-- Credit: @leirosario97-debug
-- The unitary balance and the odd-exponent congruence build on the parent
-- reduction and MattGaiser's notes #167841 and #167879. The Sophie Germain
-- factorization restricts every divisor of half the exponent of 2.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H3_R1_H1_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H3_R1 hiding H1 H2 main

-- The branch with half the exponent congruent to 1 modulo 8.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n t : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → 283 < n.factorization 5 →
    Odd (n.factorization 5) →
    (∀ d, d ∣ n.factorization 5 → d % 6 = 1) →
    (∀ d, 3 ≤ d → d ≤ 283 → ¬ d ∣ n.factorization 5) →
    padicValNat 2 n = 2 * t → t % 8 = 1 →
    (∀ d, d ∣ t → d % 8 = 1 ∨ d % 8 = 3) →
    (∀ d ∈ ({17, 41, 43, 59, 67, 73, 97} : Finset ℕ), ¬ d ∣ t) →
    (∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- The branch with half the exponent congruent to 3 modulo 8.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n t : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → 283 < n.factorization 5 →
    Odd (n.factorization 5) →
    (∀ d, d ∣ n.factorization 5 → d % 6 = 1) →
    (∀ d, 3 ≤ d → d ≤ 283 → ¬ d ∣ n.factorization 5) →
    padicValNat 2 n = 2 * t → t % 8 = 3 →
    (∀ d, d ∣ t → d % 8 = 1 ∨ d % 8 = 3) →
    (∀ d ∈ ({17, 41, 43, 59, 67, 73, 97} : Finset ℕ), ¬ d ∣ t) →
    (∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

theorem bad_seed_divisor_requires_five {a e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ a + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) =
      2 ^ (a + 1) * 5 ^ e * ∏ p ∈ P, p)
    (ha : 0 < a) (he : Odd e) (z : ℕ) (hz : z ∣ 2 ^ a + 1) (hz3 : z % 3 = 2) :
    5 ∣ z := by
  obtain ⟨q, hqp, hqz, hq3⟩ := exists_prime_mod3 z hz3
  by_cases hq5 : q = 5
  · simpa [hq5] using hqz
  exfalso
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := by
    intro c hc h
    exact hc (Finset.mem_singleton.mp h)
  have hqd := hqz.trans hz
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hpow : 2 ∣ 2 ^ a := dvd_pow_self 2 ha.ne'
    have h := (Nat.dvd_add_right hpow).mp hqd
    norm_num at h
  obtain ⟨_, hseed, _, _, _, _, _, hcore⟩ := facts hP (hK5 e) E
  have hqP := hseed q hqp hq2 (hnz hq5) hqd
  obtain ⟨Q, hQ, _⟩ := exists_quot_mod (z := 5) he
  have h3 : 3 ∣ 1 + 5 ^ e := by
    rw [hQ]
    exact (by norm_num : 3 ∣ 5 + 1).mul_right Q
  exact hcore 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) h3 q hqP (by omega)

theorem half_is_odd {t : ℕ}
    (hseed : ∀ z : ℕ, z ∣ 2 ^ (2 * t) + 1 → z % 3 = 2 → 5 ∣ z) : Odd t := by
  have hpow3 : 2 ^ (2 * t) % 3 = 1 := by
    rw [pow_mul, Nat.pow_mod]
    norm_num
  have hseed3 : (2 ^ (2 * t) + 1) % 3 = 2 := by
    rw [Nat.add_mod, hpow3] <;> norm_num
  have h5 := Nat.mod_eq_zero_of_dvd (hseed _ (dvd_refl _) hseed3)
  apply Nat.odd_iff.mpr
  by_contra hn
  have htwice : 2 * t = 4 * (t / 2) := by omega
  have hpow5 : 2 ^ (2 * t) % 5 = 1 := by
    rw [htwice, pow_mul, Nat.pow_mod]
    norm_num
  rw [Nat.add_mod, hpow5] at h5
  norm_num at h5

theorem odd_half_seed_dvd {d t : ℕ} (ht : Odd t) (hd : d ∣ t) :
    2 ^ (2 * d) + 1 ∣ 2 ^ (2 * t) + 1 := by
  obtain ⟨j, hj⟩ := hd
  have hjd : j ∣ t := ⟨d, by simpa [mul_comm] using hj⟩
  have hjo : Odd j := Nat.odd_iff.mpr (odd_of_dvd_odd hjd (Nat.odd_iff.mp ht))
  have hpow : (2 : ℕ) ^ (2 * t) = (2 ^ (2 * d)) ^ j := by
    rw [show 2 * t = (2 * d) * j by rw [hj]; ring, pow_mul]
  simpa only [hpow, one_pow] using Odd.nat_add_dvd_pow_add_pow (2 ^ (2 * d)) 1 hjo

theorem power_two_mod_fifteen (k : ℕ) : (2 : ℕ) ^ k % 15 = 2 ^ (k % 4) % 15 := by
  conv_lhs => rw [← Nat.mod_add_div k 4, pow_add, pow_mul]
  simp [Nat.mul_mod, Nat.pow_mod]

-- If d is 5 or 7 modulo 8, one of the two Sophie Germain factors is
-- 2 modulo 3 and coprime to 5, so it cannot divide the seed.
theorem odd_divisor_class {d t : ℕ} (ht : Odd t) (hd : d ∣ t)
    (hseed : ∀ z : ℕ, z ∣ 2 ^ (2 * t) + 1 → z % 3 = 2 → 5 ∣ z) :
    d % 8 = 1 ∨ d % 8 = 3 := by
  have hdo := odd_of_dvd_odd hd (Nat.odd_iff.mp ht)
  by_contra hclass
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = 2 * k + 1 := ⟨d / 2, by omega⟩
  have hk : k % 4 = 2 ∨ k % 4 = 3 := by omega
  let x : ℕ := 2 ^ k
  have hx : 0 < x := by dsimp [x]; positivity
  obtain ⟨y, hy⟩ : ∃ y : ℕ, x = y + 1 := ⟨x - 1, by omega⟩
  let plus := (y + 1) ^ 2 + (y + 2) ^ 2
  let minus := (y + 1) ^ 2 + y ^ 2
  have hfactor : 2 ^ (2 * (2 * k + 1)) + 1 = plus * minus := by
    rw [show 2 * (2 * k + 1) = k * 4 + 2 by omega, pow_add, pow_mul]
    change x ^ 4 * 2 ^ 2 + 1 = plus * minus
    rw [hy]
    dsimp [plus, minus]
    ring
  have hs : 2 ^ (2 * (2 * k + 1)) + 1 ∣ 2 ^ (2 * t) + 1 := odd_half_seed_dvd ht hd
  rcases hk with hk | hk
  · have hx4 : x % 15 = 4 := by
      change (2 : ℕ) ^ k % 15 = 4
      rw [power_two_mod_fifteen, hk] <;> norm_num
    have h1 : (y + 1) % 15 = 4 := by omega
    have h2 : (y + 2) % 15 = 5 := by omega
    have hs1 : (y + 1) ^ 2 % 15 = 1 := by rw [Nat.pow_mod, h1] <;> norm_num
    have hs2 : (y + 2) ^ 2 % 15 = 10 := by rw [Nat.pow_mod, h2] <;> norm_num
    have hm : plus % 15 = 11 := by
      change ((y + 1) ^ 2 + (y + 2) ^ 2) % 15 = 11
      rw [Nat.add_mod, hs1, hs2] <;> norm_num
    have hdvd : plus ∣ 2 ^ (2 * (2 * k + 1)) + 1 := ⟨minus, hfactor⟩
    have h5 := hseed plus (hdvd.trans hs) (by omega)
    have h5' := Nat.mod_eq_zero_of_dvd h5
    omega
  · have hx8 : x % 15 = 8 := by
      change (2 : ℕ) ^ k % 15 = 8
      rw [power_two_mod_fifteen, hk] <;> norm_num
    have h1 : (y + 1) % 15 = 8 := by omega
    have h2 : y % 15 = 7 := by omega
    have hs1 : (y + 1) ^ 2 % 15 = 4 := by rw [Nat.pow_mod, h1] <;> norm_num
    have hs2 : y ^ 2 % 15 = 4 := by rw [Nat.pow_mod, h2] <;> norm_num
    have hm : minus % 15 = 8 := by
      change ((y + 1) ^ 2 + y ^ 2) % 15 = 8
      rw [Nat.add_mod, hs1, hs2] <;> norm_num
    have hdvd : minus ∣ 2 ^ (2 * (2 * k + 1)) + 1 := ⟨plus, by rw [hfactor, mul_comm]⟩
    have h5 := hseed minus (hdvd.trans hs) (by omega)
    have h5' := Nat.mod_eq_zero_of_dvd h5
    omega

theorem small_divisors_excluded {t : ℕ} (ht : Odd t)
    (hseed : ∀ z : ℕ, z ∣ 2 ^ (2 * t) + 1 → z % 3 = 2 → 5 ∣ z) :
    ∀ d ∈ ({17, 41, 43, 59, 67, 73, 97} : Finset ℕ), ¬ d ∣ t := by
  have exclude {d q : ℕ} (hq : q ∣ 2 ^ (2 * d) + 1) (h3 : q % 3 = 2)
      (h5 : ¬ 5 ∣ q) (hd : d ∣ t) : False :=
    h5 (hseed q (hq.trans (odd_half_seed_dvd ht hd)) h3)
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exclude (q := 137) (by norm_num) (by norm_num) (by norm_num)
  · exact exclude (q := 10169) (by norm_num) (by norm_num) (by norm_num)
  · exact exclude (q := 173) (by norm_num) (by norm_num) (by norm_num)
  · exact exclude (q := 1181) (by norm_num) (by norm_num) (by norm_num)
  · exact exclude (q := 269) (by norm_num) (by norm_num) (by norm_num)
  · exact exclude (q := 293) (by norm_num) (by norm_num) (by norm_num)
  · exact exclude (q := 389) (by norm_num) (by norm_num) (by norm_num)

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H3_R1.H1 := by
  rintro ⟨A₁, h₁⟩ ⟨A₂, h₂⟩
  refine ⟨max A₁ A₂, fun n hn hS hlarge he hdiv hsieve haEven haSieve => ?_⟩
  by_cases hz : padicValNat 2 n = 0
  · rw [hz]
    exact Nat.zero_le _
  obtain ⟨t, ht⟩ := haEven
  have ha : padicValNat 2 n = 2 * t := by omega
  have hpos : 0 < 2 * t := by omega
  obtain ⟨hP, _, E⟩ := setup hn hS
  rw [ha] at E
  have hseed := bad_seed_divisor_requires_five hP E hpos he
  have hodd := half_is_odd hseed
  have hall := fun d hd => odd_divisor_class (d := d) hodd hd hseed
  have hsmall := small_divisors_excluded hodd hseed
  rcases hall t (dvd_refl t) with ht1 | ht3
  · exact (h₁ n t hn hS hlarge he hdiv hsieve ha ht1 hall hsmall haSieve).trans (le_max_left _ _)
  · exact (h₂ n t hn hS hlarge he hdiv hsieve ha ht3 hall hsmall haSieve).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H3_R1_H1_R1
