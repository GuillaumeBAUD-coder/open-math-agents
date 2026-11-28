import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H3_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1.H3.R1.H2.R1 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1.H3.R1.H2
-- Credit: @yuka30240

/-!
# Prime factors of the unitary divisor sum of the 2-component

Write `a = v₂(n)`. The seed `2^a + 1` divides `n`. Suppose every prime of
the seed that occurs repeatedly in `n` is at most `B`. Lifting the exponent
shows that the full part of the seed at primes up to `B` divides
`(2^(2*B!) - 1) * a`. Each prime above `B` occurs once, is 1 modulo 12,
and divides none of the factors `1 + z^e(z)` for odd primes `z` dividing `n`.

The remaining estimates are a uniform cutoff `B` for the repeated seed primes
and an upper bound `C * 2^(a/2)` for the product of the isolated primes above
that cutoff. Together they give `a ≤ 8 * (2^(2*B!) - 1) * C`.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H3_R1_H2_R1

-- Uniform cutoff for repeated primes appearing in the seed.
def H1 : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    n.factorization 3 = 1 → padicValNat 2 n % 2 = 0 →
    (∃ q ∈ n.primeFactors, q % 3 = 2 ∧ n.factorization q % 2 = 1 ∧ q % 9 ≠ 8 ∧
      n.factorization q % 3 ≠ 0 ∧ 5 ≤ n.factorization q ∧
      (n.factorization q % 6 = 5 → ∃ r ∈ S, r ≠ q ∧ r % 3 = 2 ∧ r ∣ 1 + q ^ n.factorization q) ∧
      (∀ d : ℕ, d.Prime → d ∣ n.factorization q → d % 3 = 2 →
        ∃ r ∈ S, r ≠ q ∧ r % 3 = 2 ∧ r ∣ 1 + q ^ d) ∧
      (∀ q' ∈ n.primeFactors, q' % 3 = 2 → n.factorization q' % 2 = 1 → q' = q) ∧
      (∃ c, c.Prime ∧ c % 3 = 2 ∧ c ∣ 2 ^ padicValNat 2 n + 1 ∧ (c = q ∨ c ∈ S)) ∧
      (∀ c, c.Prime → c % 3 = 2 → c ∣ 2 ^ padicValNat 2 n + 1 → c = q ∨ c ∈ S) ∧
      (padicValNat 2 n % 8 = 4 → 17 ∈ S) ∧ (padicValNat 2 n % 32 = 16 → 65537 ∈ S) ∧
      (n.primeFactors.card % 2 = 0 ↔ (1 + q ^ n.factorization q) % 9 = 3)) →
    (∀ z ∈ S, z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ p ∈ n.primeFactors, p ≠ 2 ∧ p ≠ z ∧ z ∣ 1 + p ^ n.factorization p) →
    ∀ p ∈ S, p ∣ 2 ^ padicValNat 2 n + 1 → p ≤ B

-- For a fixed cutoff, bound the product of the remaining isolated primes.
def H2 : Prop :=
  ∀ B : ℕ, ∃ C : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    n.factorization 3 = 1 → padicValNat 2 n % 2 = 0 →
    (∃ q ∈ n.primeFactors, q % 3 = 2 ∧ n.factorization q % 2 = 1 ∧ q % 9 ≠ 8 ∧
      n.factorization q % 3 ≠ 0 ∧ 5 ≤ n.factorization q ∧
      (n.factorization q % 6 = 5 → ∃ r ∈ S, r ≠ q ∧ r % 3 = 2 ∧ r ∣ 1 + q ^ n.factorization q) ∧
      (∀ d : ℕ, d.Prime → d ∣ n.factorization q → d % 3 = 2 →
        ∃ r ∈ S, r ≠ q ∧ r % 3 = 2 ∧ r ∣ 1 + q ^ d) ∧
      (∀ q' ∈ n.primeFactors, q' % 3 = 2 → n.factorization q' % 2 = 1 → q' = q) ∧
      (∃ c, c.Prime ∧ c % 3 = 2 ∧ c ∣ 2 ^ padicValNat 2 n + 1 ∧ (c = q ∨ c ∈ S)) ∧
      (∀ c, c.Prime → c % 3 = 2 → c ∣ 2 ^ padicValNat 2 n + 1 → c = q ∨ c ∈ S) ∧
      (padicValNat 2 n % 8 = 4 → 17 ∈ S) ∧ (padicValNat 2 n % 32 = 16 → 65537 ∈ S) ∧
      (n.primeFactors.card % 2 = 0 ↔ (1 + q ^ n.factorization q) % 9 = 3)) →
    (∀ z ∈ S, z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ p ∈ n.primeFactors, p ≠ 2 ∧ p ≠ z ∧ z ∣ 1 + p ^ n.factorization p) →
    (∀ p ∈ S, p ∣ 2 ^ padicValNat 2 n + 1 → p ≤ B) →
    (∏ p ∈ (2 ^ padicValNat 2 n + 1).primeFactors with B < p ∧ p % 12 = 1 ∧
      n.factorization p = 1 ∧ (∀ z ∈ n.primeFactors.erase 2, ¬ p ∣ 1 + z ^ n.factorization z), p) ≤
        C * 2 ^ (padicValNat 2 n / 2)

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1
  (ppart_ne_zero factorization_ppart prod_primeFactors_pow_self two_dvd_of_isUnitaryPerfect)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1
  (fact2_eq fact_pos dvd_two_mul_of_src two_src le_fact_of_sq)

theorem seed_dvd_power_sub_one (a B : ℕ) :
    2 ^ a + 1 ∣ (2 ^ (2 * B.factorial)) ^ a - 1 := by
  have first : 2 ^ a + 1 ∣ (2 ^ a) ^ 2 - 1 := by
    simpa using (show 2 ^ a + 1 ∣ (2 ^ a) ^ 2 - 1 ^ 2 by
      rw [Nat.pow_two_sub_pow_two]
      exact dvd_mul_right _ _)
  rw [← pow_mul] at first ⊢
  exact first.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 ⟨B.factorial, by ring⟩)

theorem seed_factorization_le {a B p : ℕ} (ha : 0 < a) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpB : p ≤ B) :
    (2 ^ a + 1).factorization p ≤ ((2 ^ (2 * B.factorial) - 1) * a).factorization p := by
  let x := 2 ^ (2 * B.factorial)
  have hx : 1 < x := by
    dsimp [x]
    exact one_lt_pow₀ (by decide) (by positivity)
  have hxa : 1 < x ^ a := one_lt_pow₀ hx ha.ne'
  have hcop : Nat.Coprime 2 p := (hp.coprime_iff_not_dvd.mpr
    (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))).symm
  have hp1 : p - 1 ∣ 2 * B.factorial :=
    dvd_mul_of_dvd_right (Nat.dvd_factorial (by have := hp.two_le; omega) (by omega)) _
  have hpx : p ∣ x - 1 :=
    (Nat.dvd_of_mod_eq_zero (Nat.pow_card_sub_one_sub_one_mod_card hp hcop)).trans
      (Nat.pow_sub_one_dvd_pow_sub_one 2 hp1)
  have hnot : ¬ p ∣ x := fun h => (hp.coprime_iff_not_dvd.mp hcop.symm) (hp.dvd_of_dvd_pow h)
  have : Fact p.Prime := ⟨hp⟩
  have lift := padicValNat.pow_sub_pow (x := x) (y := 1) (hp.eq_two_or_odd'.resolve_left hp2)
    hx hpx hnot ha.ne'
  simp only [one_pow] at lift
  have upper := (Nat.factorization_le_iff_dvd (by positivity : 2 ^ a + 1 ≠ 0)
    (by omega : x ^ a - 1 ≠ 0)).mpr (seed_dvd_power_sub_one a B)
  change _ ≤ ((x - 1) * a).factorization p
  rw [Nat.factorization_mul (by omega) ha.ne', Finsupp.add_apply,
    Nat.factorization_def (x - 1) hp, Nat.factorization_def a hp, ← lift, ← Nat.factorization_def _ hp]
  exact upper p

theorem quadratic_le_exponential (k : ℕ) : k ^ 2 ≤ 2 * 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    by_cases h : k < 3
    · interval_cases k <;> decide
    · rw [pow_succ (2 : ℕ) k]
      have : 2 * k + 1 ≤ k ^ 2 := by nlinarith [Nat.sub_add_cancel (by omega : 3 ≤ k)]
      nlinarith

theorem valuation_bound_of_seed_bound {a K : ℕ} (ha : a % 2 = 0)
    (h : 2 ^ a + 1 ≤ K * a * 2 ^ (a / 2)) : a ≤ 8 * K := by
  let t := a / 2
  have ht : a = t + t := by dsimp [t]; omega
  change 2 ^ a + 1 ≤ K * a * 2 ^ t at h
  have hpow : 2 ^ t < K * a := by
    have step : 2 ^ t * 2 ^ t < K * a * 2 ^ t := by
      simpa [← pow_add, ← ht] using (show 2 ^ a < K * a * 2 ^ t by omega)
    exact (Nat.mul_lt_mul_right (by positivity : 0 < 2 ^ t)).mp step
  have hsq := quadratic_le_exponential t
  have hmul : t * t ≤ (4 * K) * t := by
    rw [ht] at hpow
    nlinarith
  by_cases hz : t = 0
  · omega
  · have := Nat.le_of_mul_le_mul_right hmul (Nat.pos_of_ne_zero hz)
    omega

/-- Every prime power at a prime at most B in the seed divides the same linear function of a. -/
theorem smooth_seed_part_dvd {a : ℕ} (ha : 0 < a) (B : ℕ) :
    (∏ p ∈ (2 ^ a + 1).primeFactors with p ≤ B, p ^ (2 ^ a + 1).factorization p) ∣
      (2 ^ (2 * B.factorial) - 1) * a := by
  let T := (2 ^ a + 1).primeFactors.filter (fun p => p ≤ B)
  have hT : T ⊆ (2 ^ a + 1).primeFactors := Finset.filter_subset _ _
  have hx : 1 < (2 : ℕ) ^ (2 * B.factorial) := one_lt_pow₀ (by decide) (by positivity)
  apply (Nat.factorization_le_iff_dvd (ppart_ne_zero hT)
    (Nat.mul_ne_zero (by omega) ha.ne')).mp
  intro p
  rw [factorization_ppart hT]
  split_ifs with hmem
  · obtain ⟨hp, hpB⟩ := Finset.mem_filter.mp hmem
    have hp2 : p ≠ 2 := by
      rintro rfl
      have hd := Nat.dvd_of_mem_primeFactors hp
      have hpow : 2 ∣ 2 ^ a := dvd_pow_self 2 ha.ne'
      omega
    exact seed_factorization_le ha (Nat.prime_of_mem_primeFactors hp) hp2 hpB
  · exact Nat.zero_le _

theorem two_mem_of_perfect {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) : 2 ∈ n.primeFactors :=
  Nat.mem_primeFactors.mpr ⟨Nat.prime_two, two_dvd_of_isUnitaryPerfect h, h.2.ne'⟩

theorem valuation_pos {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) : 0 < padicValNat 2 n := by
  rw [← fact2_eq]
  exact fact_pos (two_mem_of_perfect h)

theorem seed_dvd_number {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) :
    2 ^ padicValNat 2 n + 1 ∣ n := by
  have ha := valuation_pos h
  have hodd : Odd (2 ^ padicValNat 2 n + 1) := by
    obtain ⟨k, hk⟩ := dvd_pow_self 2 ha.ne'
    exact ⟨k, by omega⟩
  apply (Nat.coprime_two_right.mpr hodd).dvd_of_dvd_mul_left
  apply dvd_two_mul_of_src h (two_mem_of_perfect h)
  rw [fact2_eq, add_comm]

/-- For even a, the seed is a square plus one. -/
theorem seed_prime_mod_four {a p : ℕ} (ha : 0 < a) (he : a % 2 = 0)
    (hp : p.Prime) (hd : p ∣ 2 ^ a + 1) : p % 4 = 1 := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ a := dvd_pow_self 2 ha.ne'
    omega
  have : Fact p.Prime := ⟨hp⟩
  have hz := (ZMod.natCast_eq_zero_iff (2 ^ a + 1) p).mpr hd
  push_cast at hz
  have hs : ((2 : ZMod p) ^ (a / 2)) ^ 2 = -1 := by
    rw [← pow_mul, show a / 2 * 2 = a by omega]
    exact eq_neg_of_add_eq_zero_left hz
  have hfour := ZMod.mod_four_ne_three_of_sq_eq_neg_one hs
  have hpar := hp.eq_two_or_odd.resolve_left hp2
  omega

/-- Above the cutoff, a seed prime occurs once in both the seed and n, lies in 1 mod 12,
and divides none of the odd components of the unitary divisor sum. -/
theorem large_seed_prime {n B q p : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ z, z ∈ S ↔ z.Prime ∧ z ≠ 2 ∧ z ^ 2 ∣ n) (he : padicValNat 2 n % 2 = 0)
    (hq : 5 ≤ n.factorization q)
    (huniq : ∀ z ∈ n.primeFactors, z % 3 = 2 → n.factorization z % 2 = 1 → z = q)
    (hB : ∀ z ∈ S, z ∣ 2 ^ padicValNat 2 n + 1 → z ≤ B)
    (hp : p ∈ (2 ^ padicValNat 2 n + 1).primeFactors) (hbig : B < p) :
    (2 ^ padicValNat 2 n + 1).factorization p = 1 ∧ p % 12 = 1 ∧ n.factorization p = 1 ∧
      ∀ z ∈ n.primeFactors.erase 2, ¬ p ∣ 1 + z ^ n.factorization z := by
  have prime := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  have hfour := seed_prime_mod_four (valuation_pos h) he prime hd
  have hp2 : p ≠ 2 := by omega
  have hdiv := seed_dvd_number h
  have hnmem := Nat.mem_primeFactors.mpr ⟨prime, hd.trans hdiv, h.2.ne'⟩
  have hsquare : ¬ 2 ≤ n.factorization p := by
    intro hsq
    have hmem := (hS p).mpr ⟨prime, hp2, (prime.pow_dvd_iff_le_factorization h.2.ne').mpr hsq⟩
    exact (not_le_of_gt hbig) (hB p hmem hd)
  have hnexp : n.factorization p = 1 := by have := fact_pos hnmem; omega
  have hseedexp : (2 ^ padicValNat 2 n + 1).factorization p = 1 := by
    have hle := (Nat.factorization_le_iff_dvd (by positivity) h.2.ne').mpr hdiv p
    have := fact_pos hp
    omega
  have hthree : p % 3 = 1 := by
    have hnonzero : p % 3 ≠ 0 := by
      intro hz
      have : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three prime).mp
        (Nat.dvd_of_mod_eq_zero hz)
      omega
    have hnot : p % 3 ≠ 2 := by
      intro hr
      have heq := huniq p hnmem hr (by omega)
      rw [← heq, hnexp] at hq
      omega
    omega
  have hclass : p % 12 = 1 := by
    have h3 : (p % 12) % 3 = 1 := by rwa [Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 12)]
    have h4 : (p % 12) % 4 = 1 := by rwa [Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 12)]
    omega
  refine ⟨hseedexp, hclass, hnexp, ?_⟩
  intro z hz hzd
  obtain ⟨hne, hzn⟩ := Finset.mem_erase.mp hz
  have hsrc : p ∣ 1 + 2 ^ n.factorization 2 := by rwa [fact2_eq, add_comm]
  have := le_fact_of_sq h.2.ne' prime hp2 (two_src h (two_mem_of_perfect h) hzn hne.symm hsrc hzd)
  omega

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H3_R1.H2 := by
  classical
  rintro ⟨B, boundRepeated⟩ boundSimple
  obtain ⟨C, boundProduct⟩ := boundSimple B
  let K := 2 ^ (2 * B.factorial) - 1
  refine ⟨8 * (K * C), ?_⟩
  intro n h S hS hcard hnonadm hthree he witnesses sources
  have hB := boundRepeated n h S hS hcard hnonadm hthree he witnesses sources
  have hC := boundProduct n h S hS hcard hnonadm hthree he witnesses sources hB
  obtain ⟨q, _, _, _, _, _, hq, _, _, huniq, _⟩ := witnesses
  let a := padicValNat 2 n
  let D := 2 ^ a + 1
  let small := D.primeFactors.filter (fun p => p ≤ B)
  let large := D.primeFactors.filter (fun p => ¬ p ≤ B)
  let simple := D.primeFactors.filter (fun p => B < p ∧ p % 12 = 1 ∧ n.factorization p = 1 ∧
    ∀ z ∈ n.primeFactors.erase 2, ¬ p ∣ 1 + z ^ n.factorization z)
  have hlarge (p : ℕ) (hp : p ∈ large) :
      D.factorization p = 1 ∧ p % 12 = 1 ∧ n.factorization p = 1 ∧
        ∀ z ∈ n.primeFactors.erase 2, ¬ p ∣ 1 + z ^ n.factorization z := by
    obtain ⟨hpd, hnot⟩ := Finset.mem_filter.mp hp
    exact large_seed_prime h hS he hq huniq hB hpd (lt_of_not_ge hnot)
  have hsets : large = simple := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpd, hnot⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hpd, lt_of_not_ge hnot, (hlarge p hp).2⟩
    · intro hp
      obtain ⟨hpd, hbig, _⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hpd, not_le_of_gt hbig⟩
  have hprod : (∏ p ∈ large, p ^ D.factorization p) = ∏ p ∈ simple, p := by
    rw [← hsets]
    exact Finset.prod_congr rfl fun p hp => by rw [(hlarge p hp).1, pow_one]
  have hsplit : (∏ p ∈ small, p ^ D.factorization p) * (∏ p ∈ large, p ^ D.factorization p) = D :=
    (Finset.prod_filter_mul_prod_filter_not D.primeFactors (fun p => p ≤ B) _).trans
      (prod_primeFactors_pow_self (by dsimp [D]; positivity))
  have hK : 0 < K := by
    have : 1 < (2 : ℕ) ^ (2 * B.factorial) := one_lt_pow₀ (by decide) (by positivity)
    dsimp [K]
    omega
  have ha : 0 < a := valuation_pos h
  have hsmall : (∏ p ∈ small, p ^ D.factorization p) ≤ K * a :=
    Nat.le_of_dvd (Nat.mul_pos hK ha) (smooth_seed_part_dvd ha B)
  change (∏ p ∈ simple, p) ≤ C * 2 ^ (a / 2) at hC
  apply valuation_bound_of_seed_bound he
  calc
    2 ^ a + 1 = (∏ p ∈ small, p ^ D.factorization p) * ∏ p ∈ simple, p := by
      rw [← hprod]; exact hsplit.symm
    _ ≤ (K * a) * (C * 2 ^ (a / 2)) := Nat.mul_le_mul hsmall hC
    _ = (K * C) * a * 2 ^ (a / 2) := by ring

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H3_R1_H2_R1
