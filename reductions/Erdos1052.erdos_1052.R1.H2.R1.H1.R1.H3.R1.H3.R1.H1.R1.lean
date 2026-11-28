import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H3_R1
import Mathlib.NumberTheory.Fermat
import Mathlib.Tactic

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1.H3.R1.H1.R1 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1.H3.R1.H1
-- Credit: @CBaquero

-- Select the least repeated odd prime z. Failure of the product bound gives an
-- explicit upper bound for z in terms of the number of repeated primes.
-- Its square is supplied by the seed, or an odd donor supplies at least one z.
-- The seed branch restricts the exponent through the order of 2 modulo z.
-- The other branches distinguish simple donors from larger repeated donors.
namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H3_R1_H1_R1

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    n.factorization 3 = 1 → padicValNat 2 n % 2 = 0 →
    (∃ q ∈ n.primeFactors, q % 3 = 2 ∧ q % 9 ≠ 8 ∧ n.factorization q = 1 ∧
      (∀ q' ∈ n.primeFactors, q' % 3 = 2 → n.factorization q' % 2 = 1 → q' = q) ∧
      (∃ c, c.Prime ∧ c % 3 = 2 ∧ c ∣ 2 ^ padicValNat 2 n + 1 ∧ (c = q ∨ c ∈ S)) ∧
      (∀ c, c.Prime → c % 3 = 2 → c ∣ 2 ^ padicValNat 2 n + 1 → c = q ∨ c ∈ S) ∧
      (padicValNat 2 n % 8 = 4 → 17 ∈ S) ∧ (padicValNat 2 n % 32 = 16 → 65537 ∈ S) ∧
      (n.primeFactors.card % 2 = 0 ↔ (1 + q ^ n.factorization q) % 9 = 3)) →
    (∀ z ∈ S, z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ p ∈ n.primeFactors, p ≠ 2 ∧ p ≠ z ∧ z ∣ 1 + p ^ n.factorization p) →
    ∀ z ∈ S, (∀ w ∈ S, z ≤ w) → 4 * (z + 1) < 2101 * S.card * (S.card + 3) →
    z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 →
    (∀ t : ℕ, 2 ^ t ∣ padicValNat 2 n → 2 ^ (t + 1) ∣ z - 1) →
    (S.card = 2 → ¬ 128 ∣ padicValNat 2 n) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    n.factorization 3 = 1 → padicValNat 2 n % 2 = 0 →
    (∃ q ∈ n.primeFactors, q % 3 = 2 ∧ q % 9 ≠ 8 ∧ n.factorization q = 1 ∧
      (∀ q' ∈ n.primeFactors, q' % 3 = 2 → n.factorization q' % 2 = 1 → q' = q) ∧
      (∃ c, c.Prime ∧ c % 3 = 2 ∧ c ∣ 2 ^ padicValNat 2 n + 1 ∧ (c = q ∨ c ∈ S)) ∧
      (∀ c, c.Prime → c % 3 = 2 → c ∣ 2 ^ padicValNat 2 n + 1 → c = q ∨ c ∈ S) ∧
      (padicValNat 2 n % 8 = 4 → 17 ∈ S) ∧ (padicValNat 2 n % 32 = 16 → 65537 ∈ S) ∧
      (n.primeFactors.card % 2 = 0 ↔ (1 + q ^ n.factorization q) % 9 = 3)) →
    (∀ z ∈ S, z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ p ∈ n.primeFactors, p ≠ 2 ∧ p ≠ z ∧ z ∣ 1 + p ^ n.factorization p) →
    ∀ z ∈ S, (∀ w ∈ S, z ≤ w) → 4 * (z + 1) < 2101 * S.card * (S.card + 3) →
    (∃ p ∈ n.primeFactors, p ≠ 2 ∧ n.factorization p = 1 ∧
      2 * z ≤ p + 1 ∧ z ∣ p + 1) →
    padicValNat 2 n ≤ A

def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    n.factorization 3 = 1 → padicValNat 2 n % 2 = 0 →
    (∃ q ∈ n.primeFactors, q % 3 = 2 ∧ q % 9 ≠ 8 ∧ n.factorization q = 1 ∧
      (∀ q' ∈ n.primeFactors, q' % 3 = 2 → n.factorization q' % 2 = 1 → q' = q) ∧
      (∃ c, c.Prime ∧ c % 3 = 2 ∧ c ∣ 2 ^ padicValNat 2 n + 1 ∧ (c = q ∨ c ∈ S)) ∧
      (∀ c, c.Prime → c % 3 = 2 → c ∣ 2 ^ padicValNat 2 n + 1 → c = q ∨ c ∈ S) ∧
      (padicValNat 2 n % 8 = 4 → 17 ∈ S) ∧ (padicValNat 2 n % 32 = 16 → 65537 ∈ S) ∧
      (n.primeFactors.card % 2 = 0 ↔ (1 + q ^ n.factorization q) % 9 = 3)) →
    (∀ z ∈ S, z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ p ∈ n.primeFactors, p ≠ 2 ∧ p ≠ z ∧ z ∣ 1 + p ^ n.factorization p) →
    ∀ z ∈ S, (∀ w ∈ S, z ≤ w) → 4 * (z + 1) < 2101 * S.card * (S.card + 3) →
    (∃ p ∈ S, z < p ∧ z ∣ 1 + p ^ n.factorization p) →
    padicValNat 2 n ≤ A

theorem small_member_of_failed_product (S : Finset ℕ) (hk : 2 ≤ S.card)
    (hbad : ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)) :
    ∃ z ∈ S, 4 * (z + 1) < 2101 * S.card * (S.card + 3) := by
  by_contra! h
  apply hbad
  let k : ℚ := S.card
  have hk' : (2 : ℚ) ≤ k := by dsimp [k]; exact_mod_cast hk
  have hk0 : 0 < k := by linarith
  have hlarge (z : ℕ) (hz : z ∈ S) : 128 ≤ z ∧ S.card + 3 ≤ z := by
    have := h z hz
    constructor <;> nlinarith [Nat.zero_le (S.card * S.card)]
  refine ⟨hlarge, ?_⟩
  let b : ℚ := 1 - 4 / (2101 * k)
  have hb : 0 < b := by
    dsimp [b]
    have : 4 / (2101 * k) < (1 : ℚ) := (div_lt_iff₀ (by positivity)).2 (by linarith)
    linarith
  have hfactor (z : ℕ) (hz : z ∈ S) :
      ((z : ℚ) + 1) / ((z : ℚ) - 2 - k) ≤ b⁻¹ := by
    have hbound : 2101 * k * (k + 3) ≤ 4 * ((z : ℚ) + 1) := by dsimp [k]; exact_mod_cast h z hz
    have hz' : k + 3 ≤ (z : ℚ) := by dsimp [k]; exact_mod_cast (hlarge z hz).2
    rw [le_inv_comm₀ (by apply div_pos <;> linarith) hb]
    rw [inv_div]
    apply (le_div_iff₀ (by positivity)).2
    dsimp [b]
    field_simp
    nlinarith
  have hprod := Finset.prod_le_prod (fun (z : ℕ) (_ : z ∈ S) =>
    div_nonneg (show 0 ≤ (z : ℚ) + 1 by positivity) (by
      have : k + 3 ≤ (z : ℚ) := by dsimp [k]; exact_mod_cast (hlarge z ‹z ∈ S›).2
      linarith : 0 ≤ (z : ℚ) - 2 - k)) hfactor
  simp only [Finset.prod_const, inv_pow] at hprod
  refine hprod.trans ?_
  have hbern := one_add_mul_sub_le_pow (show -1 ≤ b by linarith) S.card
  have heq : 1 + (S.card : ℚ) * (b - 1) = 2097 / 2101 := by
    change 1 + k * ((1 - 4 / (2101 * k)) - 1) = _
    field_simp
    ring
  rw [heq] at hbern
  rw [inv_eq_one_div, div_le_iff₀ (pow_pos hb _)]
  linarith

-- An odd prime divisor when 128 divides the exponent must be 1 modulo 256.
-- Below 5252 the three prime candidates all have odd order after raising 2 to 128.
theorem no_small_seed_prime {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsmall : p ≤ 5251) (ha : 128 ∣ a) : ¬ p ∣ 2 ^ a + 1 := by
  obtain ⟨t, rfl⟩ := ha
  intro hd
  have hform : p ∣ (2 ^ t) ^ (2 ^ 7) + 1 := by
    simpa only [← pow_mul, show 2 ^ 7 = 128 by decide, Nat.mul_comm t 128] using hd
  obtain ⟨j, hj⟩ := Nat.pow_pow_add_primeFactors_one_lt hp hp2 hform
  norm_num at hj
  have hj' : j ≤ 20 := by omega
  have hlist : p = 257 ∨ p = 769 ∨ p = 3329 := by
    subst p
    interval_cases j <;> norm_num at *
  obtain ⟨m, hm, hm1⟩ : ∃ m : ℕ, Odd m ∧ (2 : ZMod p) ^ (128 * m) = 1 := by
    rcases hlist with rfl | rfl | rfl
    · exact ⟨1, by decide, by reduce_mod_char⟩
    · exact ⟨3, by decide, by reduce_mod_char⟩
    · exact ⟨13, by decide, by reduce_mod_char⟩
  have hneg : (2 : ZMod p) ^ (128 * t) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ p).mpr hd
  have hpow : ((2 : ZMod p) ^ (128 * t)) ^ m = 1 := by
    rw [← pow_mul, show 128 * t * m = 128 * m * t by ring, pow_mul, hm1, one_pow]
  rw [hneg, hm.neg_one_pow] at hpow
  have htwo : (2 : ZMod p) = 0 := by linear_combination -hpow
  have := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using htwo)
  exact hp2 ((Nat.dvd_prime Nat.prime_two).mp this |>.resolve_left hp.ne_one)

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H3_R1.H1 := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩
  refine ⟨max A (max B C), ?_⟩
  intro n hn S hS hk hbad h3 ha hq hsource
  obtain ⟨w, hw, hwbound⟩ := small_member_of_failed_product S hk hbad
  let z := S.min' ⟨w, hw⟩
  have hz : z ∈ S := S.min'_mem _
  have hmin (v : ℕ) (hv : v ∈ S) : z ≤ v := S.min'_le v hv
  have hbound : 4 * (z + 1) < 2101 * S.card * (S.card + 3) := by
    have := hmin w hw
    omega
  obtain ⟨hzp, hz2, _⟩ := (hS z).1 hz
  rcases hsource z hz with hseed | ⟨p, hp, hp2, hpz, hd⟩
  · have hzseed : z ∣ 2 ^ padicValNat 2 n + 1 :=
      (dvd_pow_self z (by decide : 2 ≠ 0)).trans hseed
    have horder (t : ℕ) (ht : 2 ^ t ∣ padicValNat 2 n) : 2 ^ (t + 1) ∣ z - 1 := by
      obtain ⟨d, hd⟩ := ht
      have hform : z ∣ (2 ^ d) ^ (2 ^ t) + 1 := by
        rwa [← pow_mul, Nat.mul_comm d, ← hd]
      obtain ⟨j, hj⟩ := Nat.pow_pow_add_primeFactors_one_lt hzp hz2 hform
      exact ⟨j, by rw [hj, Nat.add_sub_cancel, Nat.mul_comm]⟩
    have hsieve (hcard : S.card = 2) : ¬ 128 ∣ padicValNat 2 n := by
      rw [hcard] at hbound
      intro h128
      exact no_small_seed_prime hzp hz2 (by omega) h128 hzseed
    exact (hA n hn S hS hk hbad h3 ha hq hsource z hz hmin hbound hseed horder hsieve).trans
      (le_max_left _ _)
  · have hpp := (Nat.mem_primeFactors.mp hp).1
    by_cases hpS : p ∈ S
    · have hlt : z < p := lt_of_le_of_ne (hmin p hpS) hpz.symm
      exact (hC n hn S hS hk hbad h3 ha hq hsource z hz hmin hbound ⟨p, hpS, hlt, hd⟩).trans
        ((le_max_right B C).trans (le_max_right A _))
    · have he : n.factorization p = 1 := by
        have hpos := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1.fact_pos hp
        by_contra hne
        exact hpS ((hS p).2 ⟨hpp, hp2, (hpp.pow_dvd_iff_le_factorization hn.2.ne').2 (by omega)⟩)
      rw [he, pow_one, Nat.add_comm] at hd
      have hodd := hpp.odd_of_ne_two hp2
      have hc := (hzp.odd_of_ne_two hz2).coprime_two_left
      have h2p : 2 ∣ p + 1 := by obtain ⟨u, hu⟩ := hodd; omega
      have hzal : 2 * z ≤ p + 1 := Nat.le_of_dvd (by omega) (hc.mul_dvd_of_dvd_of_dvd h2p hd)
      exact (hB n hn S hS hk hbad h3 ha hq hsource z hz hmin hbound ⟨p, hp, hp2, he, hzal, hd⟩).trans
        ((le_max_left B C).trans (le_max_right A _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H3_R1_H1_R1
