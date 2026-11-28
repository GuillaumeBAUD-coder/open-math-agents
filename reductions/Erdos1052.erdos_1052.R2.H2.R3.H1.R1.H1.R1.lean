import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R1
import Mathlib.NumberTheory.Multiplicity

/-!
# Fermat-factor and odd-part-quotient decomposition of seed primes

Reduction of `Erdos1052.erdos_1052.R2.H2.R3.H1.R1.H1` (uniform bound on the number of
simple primes `p in S` dividing `2^a + 1` for a fixed odd powerful core `c`).

Write `a = 2^s * m` with `s = a.factorization 2` and `m = ordCompl[2] a` odd. Then the
Fermat factor `F = 2^(2^s) + 1` divides `2^a + 1`, with complementary quotient
`Q = (2^a + 1) / F`. Using `odd_balance_eq` from the parent reduction we prove:
1. Exact identification: `S.filter (fun p => p | 2^a + 1) = (2^a + 1).primeFactors \ c.primeFactors`.
2. Squarefreeness outside `c`: every `p in S` dividing `2^a + 1` has `(2^a + 1).factorization p = 1`,
   so the primes of `S` dividing `F` and those dividing `Q` are disjoint and partition the target set.
3. Lifting-the-Exponent (LTE) valuation bound: for every prime `q | F`,
   `(ordCompl[2] a).factorization q <= c.factorization q`; in particular `q` cannot divide `m`
   when `q` does not divide `c`, and for odd `a` we have `a.factorization 3 <= c.factorization 3`.
4. Unconditional elimination of pure powers of `3` (`a = 3^t` forces `t <= c.factorization 3`),
   odd exponents for the Fermat factor (`F = 3` contributes at most `1`), and pure powers of `2`
   for the quotient (`Q = 1` contributes `0`).

This splits the seed-prime count into two independent subproblems:
- `H1`: bounding the Fermat-factor primes `p in S` dividing `2^(2^s) + 1` for even `a` (`1 <= s`).
- `H2`: bounding the odd-part-quotient primes `p in S` dividing `(2^a + 1) / (2^(2^s) + 1)`
  when `1 < ordCompl[2] a` and `a` is not a pure power of `3`.
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R1_H1_R1

open scoped BigOperators
open OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R1

/-- Uniform bound on simple primes in `S` dividing the Fermat factor `2^(2^v_2(a)) + 1`
for even exponents `a` (`1 <= a.factorization 2`). -/
def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ K : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ p ∈ b.primeFactors, (1 + p ^ b.factorization p)
      5 ≤ a → 1 ≤ a.factorization 2 → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p) →
      (S.filter (fun p => p ∣ 2 ^ (2 ^ a.factorization 2) + 1)).card ≤ K

/-- Uniform bound on simple primes in `S` dividing the odd-part quotient
`(2^a + 1) / (2^(2^v_2(a)) + 1)`, excluding pure powers of `2` and pure powers of `3`. -/
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ K : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ p ∈ b.primeFactors, (1 + p ^ b.factorization p)
      5 ≤ a → 1 < ordCompl[2] a → (¬ ∃ t : ℕ, a = 3 ^ t) →
      4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p) →
      (S.filter (fun p => p ∣ (2 ^ a + 1) / (2 ^ (2 ^ a.factorization 2) + 1))).card ≤ K

/-- Valuation of a product of distinct primes at any prime `q`. -/
theorem factorization_prime_prod {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (q : ℕ) :
    (∏ p ∈ S, p).factorization q = if q ∈ S then 1 else 0 := by
  classical
  rw [Nat.factorization_prod (fun p hp => (hS p hp).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun p hp => by rw [(hS p hp).factorization, Finsupp.single_apply])]
  exact Finset.sum_ite_eq' S q _

/-- Exact odd divisibility `2^a + 1 | c * prod_{p in S} p` from the balance equation. -/
theorem seed_dvd_core_mul_S {a c : ℕ} {S : Finset ℕ} (ha : 0 < a) (hc : Odd c)
    (hp : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 ^ a * c)
    (hbal : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
      (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p)) :
    2 ^ a + 1 ∣ c * ∏ p ∈ S, p := by
  have hp2 : ∀ p ∈ S, p.Prime ∧ p ≠ 2 := fun p h =>
    ⟨(hp p h).1, fun h2 => (hp p h).2 (h2 ▸ dvd_mul_of_dvd_left (dvd_pow_self 2 ha.ne') c)⟩
  have hodd := odd_balance_eq ha hc hp2 hbal
  rw [← hodd]
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

/-- Exact identification: the simple primes of `S` dividing `2^a + 1` are precisely the
prime factors of `2^a + 1` outside `c`. -/
theorem seed_primes_eq {a c : ℕ} {S : Finset ℕ} (ha : 0 < a) (hc : Odd c)
    (hp : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 ^ a * c)
    (hbal : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
      (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p)) :
    S.filter (fun p => p ∣ 2 ^ a + 1) = (2 ^ a + 1).primeFactors \ c.primeFactors := by
  have hdvd := seed_dvd_core_mul_S ha hc hp hbal
  ext p
  simp only [Finset.mem_filter, Finset.mem_sdiff, Nat.mem_primeFactors, ne_eq]
  constructor
  · rintro ⟨hpS, hpdvd⟩
    refine ⟨⟨(hp p hpS).1, hpdvd, by positivity⟩, ?_⟩
    rintro ⟨_, hpc, _⟩
    exact (hp p hpS).2 (dvd_mul_of_dvd_right hpc _)
  · rintro ⟨⟨hpp, hpdvd, _⟩, hnotc⟩
    have hnotcdvd : ¬ p ∣ c := fun h => hnotc ⟨hpp, h, hc.pos.ne'⟩
    have hprod : p ∣ ∏ q ∈ S, q := (hpp.dvd_mul.mp (hpdvd.trans hdvd)).resolve_left hnotcdvd
    obtain ⟨q, hqS, hpq⟩ := (hpp.prime.dvd_finsetProd_iff _).mp hprod
    have heq := (Nat.prime_dvd_prime_iff_eq hpp (hp q hqS).1).mp hpq
    exact ⟨heq ▸ hqS, hpdvd⟩

/-- Every prime `p in S` dividing `2^a + 1` divides `2^a + 1` to the exact first power. -/
theorem seed_factorization_eq_one {a c p : ℕ} {S : Finset ℕ} (ha : 0 < a) (hc : Odd c)
    (hp : ∀ q ∈ S, q.Prime ∧ ¬ q ∣ 2 ^ a * c)
    (hbal : (∏ q ∈ (2 ^ a * c).primeFactors, (1 + q ^ (2 ^ a * c).factorization q)) *
      (∏ q ∈ S, (1 + q)) = (2 * (2 ^ a * c)) * (∏ q ∈ S, q))
    (hpS : p ∈ S) (hpdvd : p ∣ 2 ^ a + 1) :
    (2 ^ a + 1).factorization p = 1 := by
  classical
  have hdvd := seed_dvd_core_mul_S ha hc hp hbal
  have hSprod : (∏ q ∈ S, q) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq => (hp q hq).1.ne_zero
  have hle := (Nat.factorization_le_iff_dvd (by positivity) (mul_ne_zero hc.pos.ne' hSprod)).mpr hdvd p
  rw [Nat.factorization_mul hc.pos.ne' hSprod, Finsupp.add_apply,
    factorization_prime_prod (fun q hq => (hp q hq).1), if_pos hpS] at hle
  have hnotc : ¬ p ∣ c := fun h => (hp p hpS).2 (dvd_mul_of_dvd_right h _)
  rw [Nat.factorization_eq_zero_of_not_dvd hnotc, zero_add] at hle
  have hpos : 1 ≤ (2 ^ a + 1).factorization p := (hp p hpS).1.factorization_pos_of_dvd (by positivity) hpdvd
  omega

/-- The Fermat factor `2^(2^v_2(a)) + 1` always divides `2^a + 1` for positive `a`. -/
theorem fermat_dvd_seed {a : ℕ} (ha : 0 < a) :
    2 ^ (2 ^ a.factorization 2) + 1 ∣ 2 ^ a + 1 := by
  have hm_odd : Odd (ordCompl[2] a) := Nat.not_even_iff_odd.mp fun h =>
    Nat.not_dvd_ordCompl Nat.prime_two ha.ne' (even_iff_two_dvd.mp h)
  have ha_split : 2 ^ a.factorization 2 * ordCompl[2] a = a := Nat.ordProj_mul_ordCompl_eq_self a 2
  have hpow : (2 : ℕ) ^ a + 1 = (2 ^ (2 ^ a.factorization 2)) ^ (ordCompl[2] a) + 1 ^ (ordCompl[2] a) := by
    rw [one_pow, ← pow_mul, ha_split]
  rw [hpow]
  exact hm_odd.nat_add_dvd_pow_add_pow (2 ^ (2 ^ a.factorization 2)) 1

/-- Lifting-the-Exponent valuation bound: for every prime `q` dividing `2^(2^v_2(a)) + 1`,
the `q`-adic valuation of `ordCompl[2] a` is at most `c.factorization q`. -/
theorem lte_odd_part_valuation {a c q : ℕ} {S : Finset ℕ} (ha : 0 < a) (hc : Odd c)
    (hp : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 ^ a * c)
    (hbal : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
      (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p))
    (hq : q.Prime) (hqF : q ∣ 2 ^ (2 ^ a.factorization 2) + 1) :
    (ordCompl[2] a).factorization q ≤ c.factorization q := by
  classical
  have h2pow_pos : 0 < 2 ^ a.factorization 2 := Nat.two_pow_pos _
  have hF_odd : Odd (2 ^ (2 ^ a.factorization 2) + 1) :=
    (even_two.pow_of_ne_zero h2pow_pos.ne').add_odd odd_one
  have hq_odd : Odd q := hF_odd.of_dvd_nat hqF
  have hq_ne2 : q ≠ 2 := by obtain ⟨k, hk⟩ := hq_odd; omega
  have hq_not_pow2 : ¬ q ∣ 2 ^ (2 ^ a.factorization 2) := fun hd =>
    hq_ne2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hd))
  have hm_odd : Odd (ordCompl[2] a) := Nat.not_even_iff_odd.mp fun h =>
    Nat.not_dvd_ordCompl Nat.prime_two ha.ne' (even_iff_two_dvd.mp h)
  have ha_split : 2 ^ a.factorization 2 * ordCompl[2] a = a := Nat.ordProj_mul_ordCompl_eq_self a 2
  have : Fact q.Prime := ⟨hq⟩
  have hlte : padicValNat q (2 ^ a + 1) =
      padicValNat q (2 ^ (2 ^ a.factorization 2) + 1) + padicValNat q (ordCompl[2] a) := by
    have hpow : (2 : ℕ) ^ a + 1 = (2 ^ (2 ^ a.factorization 2)) ^ (ordCompl[2] a) + 1 ^ (ordCompl[2] a) := by
      rw [one_pow, ← pow_mul, ha_split]
    rw [hpow]
    exact padicValNat.pow_add_pow hq_odd hqF hq_not_pow2 hm_odd
  rw [← Nat.factorization_def (2 ^ a + 1) hq,
    ← Nat.factorization_def (2 ^ (2 ^ a.factorization 2) + 1) hq,
    ← Nat.factorization_def (ordCompl[2] a) hq] at hlte
  have hF_val_pos : 1 ≤ (2 ^ (2 ^ a.factorization 2) + 1).factorization q :=
    hq.factorization_pos_of_dvd (by positivity) hqF
  have hdvd := seed_dvd_core_mul_S ha hc hp hbal
  have hSprod : (∏ p ∈ S, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p h => (hp p h).1.ne_zero
  have hle := (Nat.factorization_le_iff_dvd (by positivity) (mul_ne_zero hc.pos.ne' hSprod)).mpr hdvd q
  rw [Nat.factorization_mul hc.pos.ne' hSprod, Finsupp.add_apply,
    factorization_prime_prod (fun p h => (hp p h).1)] at hle
  split_ifs at hle <;> omega

/-- Pure powers of `3` satisfy `a = 3^t <= 3^(c.factorization 3)`. -/
theorem pow_three_exponent_bound {a c t : ℕ} {S : Finset ℕ} (ha : 0 < a) (hc : Odd c)
    (hp : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 ^ a * c)
    (hbal : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
      (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p))
    (hat : a = 3 ^ t) :
    t ≤ c.factorization 3 := by
  have ha_odd : Odd a := by rw [hat]; exact (by decide : Odd 3).pow
  have h2not : ¬ 2 ∣ a := by obtain ⟨k, hk⟩ := ha_odd; omega
  have hv2 : a.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd h2not
  have hord : ordCompl[2] a = 3 ^ t := by
    change a / 2 ^ a.factorization 2 = 3 ^ t
    rw [hv2, pow_zero, Nat.div_one, hat]
  have hlte := lte_odd_part_valuation ha hc hp hbal Nat.prime_three (by rw [hv2]; norm_num)
  rw [hord, Nat.prime_three.factorization_pow, Finsupp.single_eq_same] at hlte
  exact hlte

/-- The primes of `S` dividing `2^a + 1` split disjointly into those dividing the Fermat factor
`2^(2^v_2(a)) + 1` and those dividing its complementary odd-part quotient. -/
theorem seed_card_split {a c : ℕ} {S : Finset ℕ} (ha : 0 < a) (hc : Odd c)
    (hp : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 ^ a * c)
    (hbal : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
      (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p)) :
    (S.filter (fun p => p ∣ 2 ^ a + 1)).card =
      (S.filter (fun p => p ∣ 2 ^ (2 ^ a.factorization 2) + 1)).card +
      (S.filter (fun p => p ∣ (2 ^ a + 1) / (2 ^ (2 ^ a.factorization 2) + 1))).card := by
  let F := 2 ^ (2 ^ a.factorization 2) + 1
  let Q := (2 ^ a + 1) / F
  have hFQ : F * Q = 2 ^ a + 1 := Nat.mul_div_cancel' (fermat_dvd_seed ha)
  have hunion : S.filter (fun p => p ∣ 2 ^ a + 1) =
      S.filter (fun p => p ∣ F) ∪ S.filter (fun p => p ∣ Q) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hpS, hpdvd⟩
      rw [← hFQ] at hpdvd
      rcases (hp p hpS).1.dvd_mul.mp hpdvd with hF | hQ
      · exact Or.inl ⟨hpS, hF⟩
      · exact Or.inr ⟨hpS, hQ⟩
    · rintro (⟨hpS, hF⟩ | ⟨hpS, hQ⟩)
      · exact ⟨hpS, hFQ ▸ dvd_mul_of_dvd_left hF Q⟩
      · exact ⟨hpS, hFQ ▸ dvd_mul_of_dvd_right hQ F⟩
  have hdisj : Disjoint (S.filter (fun p => p ∣ F)) (S.filter (fun p => p ∣ Q)) := by
    refine Finset.disjoint_left.mpr fun p hpF hpQ => ?_
    obtain ⟨hpS, hF⟩ := Finset.mem_filter.mp hpF
    obtain ⟨_, hQ⟩ := Finset.mem_filter.mp hpQ
    have hsq : p ^ 2 ∣ 2 ^ a + 1 := by
      rw [sq, ← hFQ]
      exact Nat.mul_dvd_mul hF hQ
    have h2le : 2 ≤ (2 ^ a + 1).factorization p := by
      have h := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 (hp p hpS).1.ne_zero) (by positivity)).mpr hsq p
      rw [(hp p hpS).1.factorization_pow, Finsupp.single_eq_same] at h
      exact h
    have h1 := seed_factorization_eq_one ha hc hp hbal hpS (hFQ ▸ dvd_mul_of_dvd_left hF Q)
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj]

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R1.H1 := by
  intro h1 h2 c hc hpow
  obtain ⟨K1, hK1⟩ := h1 c hc hpow
  obtain ⟨K2, hK2⟩ := h2 c hc hpow
  refine ⟨max (max K1 1 + K2) (2 ^ (3 ^ c.factorization 3) + 2), ?_⟩
  intro a S b u ha hS hsub hp hbal
  by_cases hpow3 : ∃ t : ℕ, a = 3 ^ t
  · obtain ⟨t, rfl⟩ := hpow3
    have ht := pow_three_exponent_bound (by omega) hc hp hbal rfl
    have ha_le : 3 ^ t ≤ 3 ^ c.factorization 3 := Nat.pow_le_pow_right (by decide) ht
    have hseed_le : 2 ^ (3 ^ t) + 1 ≤ 2 ^ (3 ^ c.factorization 3) + 1 :=
      Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) ha_le) 1
    have hsub_range : S.filter (fun p => p ∣ 2 ^ (3 ^ t) + 1) ⊆
        Finset.range (2 ^ (3 ^ c.factorization 3) + 2) := by
      intro p hpF
      obtain ⟨_, hpdvd⟩ := Finset.mem_filter.mp hpF
      have hple := Nat.le_of_dvd (by positivity) hpdvd
      exact Finset.mem_range.mpr (by omega)
    have hcard_le : (S.filter (fun p => p ∣ 2 ^ (3 ^ t) + 1)).card ≤
        2 ^ (3 ^ c.factorization 3) + 2 := by
      simpa using Finset.card_le_card hsub_range
    exact hcard_le.trans (le_max_right _ _)
  · rw [seed_card_split (by omega) hc hp hbal]
    have hF_bound : (S.filter (fun p => p ∣ 2 ^ (2 ^ a.factorization 2) + 1)).card ≤ max K1 1 := by
      by_cases heven : 1 ≤ a.factorization 2
      · exact (hK1 a S ha heven hS hsub hp hbal).trans (le_max_left _ _)
      · have hv0 : a.factorization 2 = 0 := by omega
        rw [hv0]
        have hsub3 : S.filter (fun p => p ∣ 2 ^ (2 ^ 0) + 1) ⊆ ({3} : Finset ℕ) := by
          intro p hpF
          obtain ⟨hpS, hpdvd⟩ := Finset.mem_filter.mp hpF
          have hp3 : p ∣ 3 := by simpa using hpdvd
          exact Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq (hp p hpS).1 Nat.prime_three).mp hp3)
        exact (Finset.card_le_card hsub3).trans (by simp)
    have hQ_bound : (S.filter (fun p => p ∣ (2 ^ a + 1) / (2 ^ (2 ^ a.factorization 2) + 1))).card ≤ K2 := by
      have hm_pos : 0 < ordCompl[2] a := Nat.ordCompl_pos 2 (by omega)
      by_cases hm1 : ordCompl[2] a = 1
      · have ha_eq : 2 ^ a.factorization 2 = a := by
          have h := Nat.ordProj_mul_ordCompl_eq_self a 2
          rwa [hm1, mul_one] at h
        have hQ1 : (2 ^ a + 1) / (2 ^ (2 ^ a.factorization 2) + 1) = 1 := by
          rw [ha_eq]
          exact Nat.div_self (by positivity)
        have hempty : S.filter (fun p => p ∣ (2 ^ a + 1) / (2 ^ (2 ^ a.factorization 2) + 1)) = ∅ := by
          rw [hQ1]
          exact Finset.filter_eq_empty_iff.mpr fun p hpS h1 => (hp p hpS).1.not_dvd_one h1
        rw [hempty]
        simp
      · exact hK2 a S ha (by omega) hpow3 hS hsub hp hbal
    exact (Nat.add_le_add hF_bound hQ_bound).trans (le_max_left _ _)

end OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R1_H1_R1
