import OMAReductions.R_Erdos1052_erdos_1052_R2_H1_R1
import Mathlib.NumberTheory.Multiplicity

/-!
# Fermat-factor and odd-part-quotient decomposition of the seed-core GCD

Reduction of `Erdos1052.erdos_1052.R2.H1.R1.H1` (uniform bound on `gcd(c, 2^a + 1)` over all
unitary perfect numbers `n` with at least four simple odd prime factors, where `a = v_2(n)` and
`c` is the repeated odd core).

From the unitary divisor-sum identity `prod_{p | n} (1 + p^{v_p(n)}) = 2 * n`, we prove:
1. Exact 2-adic budget inequality: `S.card + R.card <= n.factorization 2 + 1`, so any unitary
   perfect number with `4 <= S.card` and nonempty repeated odd core `R` satisfies `4 <= a`.
2. Fermat/odd-part factorization: writing `a = 2^s * m` with `s = a.factorization 2` and
   `m = ordCompl[2] a` odd, `F = 2^(2^s) + 1` divides `2^a + 1`, giving the multiplicative
   GCD bound `gcd(c, 2^a + 1) <= gcd(c, F) * gcd(c, (2^a + 1) / F)`.
3. Lifting-the-Exponent valuation identity: for every prime `q | F`, the quotient
   `Q = (2^a + 1) / F` satisfies `Q.factorization q = m.factorization q`, isolating all shared
   factors between `F` and `Q` to primes dividing the odd part of `a`.
4. Unconditional elimination of degenerate cases:
   - `R = empty` (`c = 1`): `gcd = 1`.
   - Odd `a` (`s = 0`) in the Fermat factor: `F = 3`, so `gcd(c, F) <= 3`.
   - Pure power-of-2 exponent `a = 2^s` (`m = 1`) in the quotient: `Q = 1`, so `gcd(c, Q) = 1`.

This splits the seed-core GCD bound cleanly into two independent hypotheses:
- `H1`: uniform bound on `gcd(c, 2^(2^v_2(a)) + 1)` for `R.Nonempty`, `4 <= a`, and even `a`.
- `H2`: uniform bound on `gcd(c, (2^a + 1) / (2^(2^v_2(a)) + 1))` for `R.Nonempty`, `4 <= a`,
  and `1 < ordCompl[2] a`.
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H1_R1_H1_R2

open scoped BigOperators
open OMA.R_Erdos1052_erdos_1052_R2

/-- Uniform bound on `gcd(c, 2^(2^v_2(a)) + 1)` when `R` is nonempty, `4 <= a`, and `a` is even. -/
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    let S := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)
    let R := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)
    let c := ∏ p ∈ R, p ^ n.factorization p
    let a := n.factorization 2
    4 ≤ S.card → R.Nonempty → 4 ≤ a → 1 ≤ a.factorization 2 →
      Nat.gcd c (2 ^ (2 ^ a.factorization 2) + 1) ≤ A

/-- Uniform bound on `gcd(c, (2^a + 1) / (2^(2^v_2(a)) + 1))` when `R` is nonempty, `4 <= a`,
and `a` is not a power of `2` (`1 < ordCompl[2] a`). -/
def H2 : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    let S := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)
    let R := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)
    let c := ∏ p ∈ R, p ^ n.factorization p
    let a := n.factorization 2
    4 ≤ S.card → R.Nonempty → 4 ≤ a → 1 < ordCompl[2] a →
      Nat.gcd c ((2 ^ a + 1) / (2 ^ (2 ^ a.factorization 2) + 1)) ≤ B

/-- Every odd prime dividing `n` contributes at least one factor of `2` to `sigma*(n) = 2 * n`,
giving the 2-adic count bound `S.card + R.card <= n.factorization 2 + 1`. -/
theorem odd_prime_count_le_v2_succ {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) :
    (n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)).card +
    (n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)).card ≤
      n.factorization 2 + 1 := by
  obtain ⟨hpos, hsum⟩ := sum_udiv_of_isUnitaryPerfect hn
  rw [sum_udiv_eq_prod hpos.ne'] at hsum
  let S := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)
  let R := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)
  let O := n.primeFactors.erase 2
  have hO_eq : O = S ∪ R := by
    ext p
    simp only [O, S, R, Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
    tauto
  have hdisj : Disjoint S R := Finset.disjoint_left.mpr fun p hpS hpR =>
    (Finset.mem_filter.mp hpR).2.2 (Finset.mem_filter.mp hpS).2.2
  have hcard : S.card + R.card = O.card := by
    rw [hO_eq, Finset.card_union_of_disjoint hdisj]
  have htwo_dvd_O : 2 ^ O.card ∣ ∏ p ∈ O, (1 + p ^ n.factorization p) := by
    rw [← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun p hpO => by
      obtain ⟨hp2, hpf⟩ := Finset.mem_erase.mp hpO
      have hodd : Odd p := (Nat.prime_of_mem_primeFactors hpf).odd_of_ne_two hp2
      exact (odd_one.add_odd hodd.pow).two_dvd
  have hO_dvd_all : (∏ p ∈ O, (1 + p ^ n.factorization p)) ∣ 2 * n := by
    rw [← hsum]
    exact Finset.prod_dvd_prod_of_subset O n.primeFactors _ (Finset.erase_subset 2 _)
  have hpow_dvd : 2 ^ O.card ∣ 2 * n := htwo_dvd_O.trans hO_dvd_all
  have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero _ (by decide))
    (mul_ne_zero (by decide) hpos.ne')).mpr hpow_dvd 2
  rw [Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_mul (by decide) hpos.ne', Finsupp.add_apply,
    Nat.prime_two.factorization_self] at hle
  change S.card + R.card ≤ n.factorization 2 + 1
  omega

/-- The Fermat factor `2^(2^v_2(a)) + 1` divides `2^a + 1` for every positive `a`. -/
theorem fermat_dvd_seed {a : ℕ} (ha : 0 < a) :
    2 ^ (2 ^ a.factorization 2) + 1 ∣ 2 ^ a + 1 := by
  have hm_odd : Odd (ordCompl[2] a) := Nat.not_even_iff_odd.mp fun h =>
    Nat.not_dvd_ordCompl Nat.prime_two ha.ne' (even_iff_two_dvd.mp h)
  have ha_split : 2 ^ a.factorization 2 * ordCompl[2] a = a := Nat.ordProj_mul_ordCompl_eq_self a 2
  have hpow : (2 : ℕ) ^ a + 1 = (2 ^ (2 ^ a.factorization 2)) ^ (ordCompl[2] a) + 1 ^ (ordCompl[2] a) := by
    rw [one_pow, ← pow_mul, ha_split]
  rw [hpow]
  exact hm_odd.nat_add_dvd_pow_add_pow (2 ^ (2 ^ a.factorization 2)) 1

/-- Lifting-the-Exponent identity on the complementary odd-part quotient: for every prime `q`
dividing `F = 2^(2^v_2(a)) + 1`, the `q`-adic valuation of `(2^a + 1) / F` equals
`(ordCompl[2] a).factorization q`. -/
theorem quotient_factorization_of_dvd_fermat {a q : ℕ} (ha : 0 < a)
    (hq : q.Prime) (hqF : q ∣ 2 ^ (2 ^ a.factorization 2) + 1) :
    ((2 ^ a + 1) / (2 ^ (2 ^ a.factorization 2) + 1)).factorization q =
      (ordCompl[2] a).factorization q := by
  let F := 2 ^ (2 ^ a.factorization 2) + 1
  let Q := (2 ^ a + 1) / F
  have hF_pos : 0 < F := by positivity
  have hFQ : F * Q = 2 ^ a + 1 := Nat.mul_div_cancel' (fermat_dvd_seed ha)
  have hQ_ne : Q ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hFQ
    exact Nat.succ_ne_zero _ hFQ.symm
  have hF_odd : Odd F := (even_two.pow_of_ne_zero (Nat.two_pow_pos _).ne').add_odd odd_one
  have hq_odd : Odd q := hF_odd.of_dvd_nat hqF
  have hq_ne2 : q ≠ 2 := by obtain ⟨k, hk⟩ := hq_odd; omega
  have hq_not_pow2 : ¬ q ∣ 2 ^ (2 ^ a.factorization 2) := fun hd =>
    hq_ne2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hd))
  have hm_odd : Odd (ordCompl[2] a) := Nat.not_even_iff_odd.mp fun h =>
    Nat.not_dvd_ordCompl Nat.prime_two ha.ne' (even_iff_two_dvd.mp h)
  have ha_split : 2 ^ a.factorization 2 * ordCompl[2] a = a := Nat.ordProj_mul_ordCompl_eq_self a 2
  have : Fact q.Prime := ⟨hq⟩
  have hlte : padicValNat q (2 ^ a + 1) =
      padicValNat q F + padicValNat q (ordCompl[2] a) := by
    have hpow : (2 : ℕ) ^ a + 1 = (2 ^ (2 ^ a.factorization 2)) ^ (ordCompl[2] a) + 1 ^ (ordCompl[2] a) := by
      rw [one_pow, ← pow_mul, ha_split]
    rw [hpow]
    exact padicValNat.pow_add_pow hq_odd hqF hq_not_pow2 hm_odd
  rw [← Nat.factorization_def (2 ^ a + 1) hq,
    ← Nat.factorization_def F hq,
    ← Nat.factorization_def (ordCompl[2] a) hq] at hlte
  have hmul : (2 ^ a + 1).factorization q = F.factorization q + Q.factorization q := by
    rw [← hFQ, Nat.factorization_mul hF_pos.ne' hQ_ne, Finsupp.add_apply]
  change Q.factorization q = (ordCompl[2] a).factorization q
  omega

/-- Multiplicative GCD decomposition `gcd(c, 2^a + 1) <= gcd(c, F) * gcd(c, (2^a + 1) / F)`. -/
theorem gcd_seed_le_mul {c a : ℕ} (ha : 0 < a) :
    Nat.gcd c (2 ^ a + 1) ≤
      Nat.gcd c (2 ^ (2 ^ a.factorization 2) + 1) *
      Nat.gcd c ((2 ^ a + 1) / (2 ^ (2 ^ a.factorization 2) + 1)) := by
  let F := 2 ^ (2 ^ a.factorization 2) + 1
  let Q := (2 ^ a + 1) / F
  have hFQ : F * Q = 2 ^ a + 1 := Nat.mul_div_cancel' (fermat_dvd_seed ha)
  have hFpos : 0 < F := by positivity
  have hQpos : 0 < Q := Nat.div_pos (Nat.le_of_dvd (by positivity) (fermat_dvd_seed ha)) hFpos
  have hdvd : Nat.gcd c (2 ^ a + 1) ∣ Nat.gcd c F * Nat.gcd c Q := by
    rw [← hFQ]
    exact gcd_mul_dvd_mul_gcd c F Q
  have hpos : 0 < Nat.gcd c F * Nat.gcd c Q :=
    Nat.mul_pos (Nat.gcd_pos_of_pos_right c hFpos) (Nat.gcd_pos_of_pos_right c hQpos)
  exact Nat.le_of_dvd hpos hdvd

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H1_R1.H1 := by
  intro h1 h2
  obtain ⟨A, hA⟩ := h1
  obtain ⟨B, hB⟩ := h2
  refine ⟨max 1 (max A 3 * max B 1), fun n hn hS => ?_⟩
  let S := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)
  let R := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)
  let c := ∏ p ∈ R, p ^ n.factorization p
  let a := n.factorization 2
  change Nat.gcd c (2 ^ a + 1) ≤ max 1 (max A 3 * max B 1)
  by_cases hR : R.Nonempty
  · have hbud := odd_prime_count_le_v2_succ hn
    have hRpos : 1 ≤ R.card := Finset.card_pos.mpr hR
    have ha4 : 4 ≤ a := by
      change 4 ≤ S.card at hS
      change S.card + R.card ≤ a + 1 at hbud
      omega
    have ha0 : 0 < a := by omega
    have hF_le : Nat.gcd c (2 ^ (2 ^ a.factorization 2) + 1) ≤ max A 3 := by
      by_cases heven : 1 ≤ a.factorization 2
      · exact (hA n hn hS hR ha4 heven).trans (le_max_left _ _)
      · have hv0 : a.factorization 2 = 0 := by omega
        rw [hv0]
        exact (Nat.gcd_le_right c (by norm_num : 0 < 2 ^ (2 ^ 0) + 1)).trans (le_max_right _ _)
    have hQ_le : Nat.gcd c ((2 ^ a + 1) / (2 ^ (2 ^ a.factorization 2) + 1)) ≤ max B 1 := by
      have hm_pos : 0 < ordCompl[2] a := Nat.ordCompl_pos 2 ha0.ne'
      by_cases hm1 : ordCompl[2] a = 1
      · have ha_eq : 2 ^ a.factorization 2 = a := by
          have h := Nat.ordProj_mul_ordCompl_eq_self a 2
          rwa [hm1, mul_one] at h
        have hQ1 : (2 ^ a + 1) / (2 ^ (2 ^ a.factorization 2) + 1) = 1 := by
          rw [ha_eq]
          exact Nat.div_self (by positivity)
        rw [hQ1, Nat.gcd_one_right]
        exact le_max_right _ _
      · exact (hB n hn hS hR ha4 (show 1 < ordCompl[2] a by omega)).trans (le_max_left _ _)
    exact ((gcd_seed_le_mul ha0).trans (Nat.mul_le_mul hF_le hQ_le)).trans (le_max_right _ _)
  · have hRempty : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
    have hc1 : c = 1 := by simp [c, hRempty]
    rw [hc1, Nat.gcd_one_left]
    exact le_max_left _ _

end OMA.R_Erdos1052_erdos_1052_R2_H1_R1_H1_R2
