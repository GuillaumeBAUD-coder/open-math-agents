import FormalConjectures.ErdosProblems.«202»

/-!
# A sublinear bound for disjoint residue classes with distinct moduli

Repeatedly select a prime dividing many moduli, keep a single residue modulo that prime,
and divide it out. On the subfamily with at most K prime factors counted with multiplicity,
the descent stops after at most K divisions. Legendre's formula bounds the mean number of
prime factors and controls the discarded moduli.

The CRT criterion, reciprocal-prime estimate, and fiber-counting lemma are adapted from
the Apache-2.0 Erdős 202 formalization by Pawan Sasanka Ammanamanchi and collaborators:
https://github.com/Shashi456/erdos-formalizations and
https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos202.lean .
-/
namespace OMA.E202
open Filter Finset ArithmeticFunction
open scoped ArithmeticFunction.Omega
def residueClass (q : ℕ) (a : ℤ) : Set ℤ :=
  {n : ℤ | n ≡ a [ZMOD (q : ℤ)]}
lemma residueClass_inter_nonempty_iff
    {q r : ℕ} (_hq : 0 < q) (_hr : 0 < r) (a b : ℤ) :
    (residueClass q a ∩ residueClass r b).Nonempty ↔
      a ≡ b [ZMOD (Nat.gcd q r : ℤ)] := by
  constructor
  · rintro ⟨n, hnq, hnr⟩
    rw [residueClass, Set.mem_ofPred_eq, Int.modEq_iff_dvd] at hnq hnr
    rw [Int.modEq_iff_dvd]
    have hdq : (Nat.gcd q r : ℤ) ∣ (q : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left q r
    have hdr : (Nat.gcd q r : ℤ) ∣ (r : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_right q r
    have hqa : (Nat.gcd q r : ℤ) ∣ a - n := dvd_trans hdq hnq
    have hrb : (Nat.gcd q r : ℤ) ∣ b - n := dvd_trans hdr hnr
    have hsub : (Nat.gcd q r : ℤ) ∣ (b - n) - (a - n) := dvd_sub hrb hqa
    convert hsub using 1
    ring
  · intro hab
    rw [Int.modEq_iff_dvd] at hab
    rcases hab with ⟨k, hk⟩
    let n : ℤ := a + (q : ℤ) * Nat.gcdA q r * k
    refine ⟨n, ?_, ?_⟩
    · rw [residueClass, Set.mem_ofPred_eq, Int.modEq_iff_dvd]
      refine ⟨-(Nat.gcdA q r * k), ?_⟩
      simp [n]
      ring
    · rw [residueClass, Set.mem_ofPred_eq, Int.modEq_iff_dvd]
      refine ⟨Nat.gcdB q r * k, ?_⟩
      have hbez := Nat.gcd_eq_gcd_ab q r
      calc
        b - n = (b - a) - (q : ℤ) * Nat.gcdA q r * k := by
          simp [n]
          ring
        _ = ((Nat.gcd q r : ℤ) * k) - (q : ℤ) * Nat.gcdA q r * k := by
          rw [hk]
        _ = ((q : ℤ) * Nat.gcdA q r + (r : ℤ) * Nat.gcdB q r) * k
              - (q : ℤ) * Nat.gcdA q r * k := by
          rw [hbez]
        _ = (r : ℤ) * (Nat.gcdB q r * k) := by
          ring
lemma tendsto_loglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop := by
  exact (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
    tendsto_natCast_atTop_atTop

lemma eventually_primeCounting_nat_le_const_log :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤ B * (n : ℝ) / Real.log (n : ℝ) := by
  refine ⟨Real.log 4 + 1, ?_, ?_⟩
  · have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  · have hreal :
        ∀ᶠ x : ℝ in atTop,
          (Nat.primeCounting (Nat.floor x) : ℝ) ≤
            (Real.log 4 + 1) * x / Real.log x :=
      Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one
    have hnat := tendsto_natCast_atTop_atTop.eventually hreal
    filter_upwards [hnat] with n hn
    simpa using hn

lemma one_div_nat_succ_le_log_succ_sub_log {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) / (m + 1 : ℕ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hm)
  have hsuccpos : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have h :=
    Real.one_sub_inv_le_log_of_pos
      (div_pos hsuccpos hmpos)
  rw [Real.log_div hsuccpos.ne' hmpos.ne'] at h
  have hleft :
      1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) =
        (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    field_simp [hmpos.ne', hsuccpos.ne']
    norm_num
  calc
    (1 : ℝ) / ((m + 1 : ℕ) : ℝ)
        = 1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) := hleft.symm
    _ ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := h

lemma harmonic_Icc_one_le_one_add_log (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)) ≤
      1 + Real.log (m : ℝ) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simp
      · have hm : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)
        have htop_not : m + 1 ∉ Finset.Icc 1 m := by
          simp
        have hIcc :
            Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
          ext k
          simp
          omega
        have hterm := one_div_nat_succ_le_log_succ_sub_log (m := m) hm
        calc
          (∑ k ∈ Finset.Icc 1 (m + 1), (1 : ℝ) / (k : ℝ))
              = (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)) +
                  (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
                    rw [hIcc, Finset.sum_insert htop_not]
                    ring
          _ ≤ (1 + Real.log (m : ℝ)) +
                (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_right ih ((1 : ℝ) / ((m + 1 : ℕ) : ℝ))
          _ ≤ 1 + Real.log (((m + 1 : ℕ) : ℝ)) := by
                  linarith
          _ = 1 + Real.log ((Nat.succ m : ℕ) : ℝ) := by
                  rfl

lemma primeCounting_eq_card_Icc_filter_prime (n : ℕ) :
    ((Finset.Icc 1 n).filter Nat.Prime).card = Nat.primeCounting n := by
  have hset :
      (Finset.Icc 1 n).filter Nat.Prime =
        (Finset.range (n + 1)).filter Nat.Prime := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp ⊢
      have hpIcc := Finset.mem_Icc.mp hp.1
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpIcc.2), hp.2⟩
    · intro hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_Icc.mpr
        ⟨hp.2.one_le, Nat.le_of_lt_succ (Finset.mem_range.mp hp.1)⟩, hp.2⟩
  calc
    ((Finset.Icc 1 n).filter Nat.Prime).card
        = ((Finset.range (n + 1)).filter Nat.Prime).card := by rw [hset]
    _ = Nat.count Nat.Prime (n + 1) := by
          exact (Nat.count_eq_card_filter_range Nat.Prime (n + 1)).symm
    _ = Nat.primeCounting n := rfl

lemma reciprocal_prime_sum_Ico_pow_two_le (k : ℕ) :
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ)) ≤
      (Nat.primeCounting (2 ^ (k + 1)) : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
  classical
  let S := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime
  have hdenpos : 0 < (((2 ^ k : ℕ) : ℝ)) := by positivity
  have hpoint : ∀ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ 1 / ((2 ^ k : ℕ) : ℝ) := by
    intro p hp
    have hpS := Finset.mem_filter.mp hp
    have hpIco := Finset.mem_Ico.mp hpS.1
    have hlow_nat : 2 ^ k ≤ p := hpIco.1
    have hlow : (((2 ^ k : ℕ) : ℝ)) ≤ (p : ℝ) := by exact_mod_cast hlow_nat
    exact one_div_le_one_div_of_le hdenpos hlow
  have hcard_le :
      S.card ≤ Nat.primeCounting (2 ^ (k + 1)) := by
    rw [← primeCounting_eq_card_Icc_filter_prime]
    refine Finset.card_le_card ?_
    intro p hp
    have hpS := Finset.mem_filter.mp hp
    have hpIco := Finset.mem_Ico.mp hpS.1
    have hpPrime : Nat.Prime p := hpS.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpPrime.one_le, hpIco.2.le⟩, hpPrime⟩
  calc
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ))
        = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := rfl
    _ ≤ ∑ p ∈ S, (1 : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
          exact Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ (Nat.primeCounting (2 ^ (k + 1)) : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hcard_le) hdenpos.le

lemma reciprocal_prime_sum_Ico_pow_two_le_of_primeCounting_bound
    (B : ℝ) {k : ℕ}
    (hπ : (Nat.primeCounting (2 ^ (k + 1)) : ℝ) ≤
      B * (((2 ^ (k + 1) : ℕ) : ℝ)) /
        Real.log (((2 ^ (k + 1) : ℕ) : ℝ))) :
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ)) ≤
      (2 * B / Real.log 2) / ((k + 1 : ℕ) : ℝ) := by
  have hdenpos : 0 < (((2 ^ k : ℕ) : ℝ)) := by positivity
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  calc
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ))
        ≤ (Nat.primeCounting (2 ^ (k + 1)) : ℝ) /
            ((2 ^ k : ℕ) : ℝ) :=
          reciprocal_prime_sum_Ico_pow_two_le k
    _ ≤ (B * (((2 ^ (k + 1) : ℕ) : ℝ)) /
          Real.log (((2 ^ (k + 1) : ℕ) : ℝ))) /
            ((2 ^ k : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right hπ hdenpos.le
    _ = (2 * B / Real.log 2) / ((k + 1 : ℕ) : ℝ) := by
          have hpow_succ :
              (((2 ^ (k + 1) : ℕ) : ℝ)) =
                (2 : ℝ) * (((2 ^ k : ℕ) : ℝ)) := by
            norm_num [pow_succ, mul_comm]
          have hlog_pow :
              Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) =
                ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
            rw [show (((2 ^ (k + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 1) by norm_num]
            rw [Real.log_pow]
          rw [hlog_pow, hpow_succ]
          field_simp [hdenpos.ne', hlog2pos.ne', hkpos.ne']

lemma eventually_reciprocal_prime_sum_Ico_pow_two_le_const :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in atTop,
      (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ)) ≤
        D / ((k + 1 : ℕ) : ℝ) := by
  rcases eventually_primeCounting_nat_le_const_log with ⟨B, hBpos, hBbound⟩
  refine ⟨2 * B / Real.log 2, ?_, ?_⟩
  · positivity
  · have hpw : Tendsto (fun k : ℕ => 2 ^ (k + 1)) atTop atTop := by
      exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)).comp
        (tendsto_add_atTop_nat 1)
    have hBpow := hpw.eventually hBbound
    filter_upwards [hBpow] with k hk
    exact reciprocal_prime_sum_Ico_pow_two_le_of_primeCounting_bound B hk

lemma reciprocal_prime_sum_Ico_pow_two_le_const_global :
    ∃ D : ℝ, 0 < D ∧ ∀ k : ℕ,
      (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ)) ≤
        D / ((k + 1 : ℕ) : ℝ) := by
  classical
  rcases eventually_reciprocal_prime_sum_Ico_pow_two_le_const with
    ⟨D, hDpos, hDevent⟩
  rcases eventually_atTop.1 hDevent with ⟨K, hK⟩
  let block : ℕ → ℝ := fun k =>
    ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
      (1 : ℝ) / (p : ℝ)
  let extra : ℝ := ∑ k ∈ Finset.Icc 0 K, ((k + 1 : ℕ) : ℝ) * block k
  refine ⟨D + extra + 1, ?_, ?_⟩
  · have hextra_nonneg : 0 ≤ extra := by
      refine Finset.sum_nonneg ?_
      intro k hk
      exact mul_nonneg (by positivity)
        (by
          refine Finset.sum_nonneg ?_
          intro p hp
          exact div_nonneg zero_le_one (by positivity))
    linarith
  · intro k
    have hdenpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
    by_cases hlarge : K ≤ k
    · have hDle : D ≤ D + extra + 1 := by
        have hextra_nonneg : 0 ≤ extra := by
          refine Finset.sum_nonneg ?_
          intro j hj
          exact mul_nonneg (by positivity)
            (by
              refine Finset.sum_nonneg ?_
              intro p hp
              exact div_nonneg zero_le_one (by positivity))
        linarith
      calc
        block k ≤ D / ((k + 1 : ℕ) : ℝ) := hK k hlarge
        _ ≤ (D + extra + 1) / ((k + 1 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right hDle hdenpos.le
    · have hkle : k ≤ K := Nat.le_of_not_ge hlarge
      have hk_mem : k ∈ Finset.Icc 0 K := by
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le k, hkle⟩
      have hterm_nonneg :
          ∀ j ∈ Finset.Icc 0 K, 0 ≤ ((j + 1 : ℕ) : ℝ) * block j := by
        intro j hj
        exact mul_nonneg (by positivity)
          (by
            refine Finset.sum_nonneg ?_
            intro p hp
            exact div_nonneg zero_le_one (by positivity))
      have hsingle :
          ((k + 1 : ℕ) : ℝ) * block k ≤ extra :=
        Finset.single_le_sum hterm_nonneg hk_mem
      have hmul :
          block k * ((k + 1 : ℕ) : ℝ) ≤ D + extra + 1 := by
        calc
          block k * ((k + 1 : ℕ) : ℝ)
              = ((k + 1 : ℕ) : ℝ) * block k := by ring
          _ ≤ extra := hsingle
          _ ≤ D + extra + 1 := by linarith
      exact (le_div_iff₀ hdenpos).2 hmul

lemma reciprocal_prime_sum_le_dyadic_harmonic
    (D : ℝ)
    (hD : ∀ k : ℕ,
      (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ)) ≤
        D / ((k + 1 : ℕ) : ℝ))
    (N : ℕ) :
    (((Finset.Icc 1 N).filter Nat.Prime).sum
        (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
      ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  let T : Finset ℕ := Finset.Icc 0 (Nat.log 2 N)
  have hmaps : ∀ p ∈ S, Nat.log 2 p ∈ T := by
    intro p hp
    have hpS := Finset.mem_filter.mp hp
    have hpIcc := Finset.mem_Icc.mp hpS.1
    exact Finset.mem_Icc.mpr
      ⟨Nat.zero_le _, Nat.log_mono_right hpIcc.2⟩
  have hdecomp :
      ∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          (1 : ℝ) / (p : ℝ)
        = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_fiberwise_of_maps_to hmaps (fun p : ℕ => (1 : ℝ) / (p : ℝ))
  have hfiber_le :
      ∀ k ∈ T,
        (∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
            (1 : ℝ) / (p : ℝ)) ≤
          ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ) := by
    intro k hk
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      have hpFilter := Finset.mem_filter.mp hp
      have hpS := Finset.mem_filter.mp hpFilter.1
      have hpPrime : Nat.Prime p := hpS.2
      have hpne : p ≠ 0 := hpPrime.ne_zero
      have hlog : Nat.log 2 p = k := hpFilter.2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr
          ⟨by simpa [hlog] using Nat.pow_log_le_self 2 hpne,
            by simpa [hlog, Nat.succ_eq_add_one] using
              Nat.lt_pow_succ_log_self Nat.one_lt_two p⟩,
          hpPrime⟩
    · intro p hp _hnot
      exact div_nonneg zero_le_one (by positivity)
  have hsum_blocks :
      ∑ k ∈ T,
        (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ))
        ≤ ∑ k ∈ T, D / ((k + 1 : ℕ) : ℝ) := by
    exact Finset.sum_le_sum (fun k hk => hD k)
  have hsum_shift :
      (∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ))
        = ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / (j : ℝ) := by
    have himage :
        T.image (fun k : ℕ => k + 1) = Finset.Icc 1 (Nat.log 2 N + 1) := by
      ext j
      simp [T]
    have hinj : Set.InjOn (fun k : ℕ => k + 1) T := by
      intro a ha b hb hab
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hab)
    have hsum_image :
        (∑ j ∈ T.image (fun k : ℕ => k + 1), (1 : ℝ) / (j : ℝ))
          = ∑ k ∈ T, (1 : ℝ) / (((fun k : ℕ => k + 1) k : ℕ) : ℝ) := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hinj ha hb hab
    calc
      (∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ))
          = ∑ j ∈ T.image (fun k : ℕ => k + 1), (1 : ℝ) / (j : ℝ) := by
            exact hsum_image.symm
      _ = ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / (j : ℝ) := by
            rw [himage]
  calc
    (((Finset.Icc 1 N).filter Nat.Prime).sum
        (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
        = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := rfl
    _ = ∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          (1 : ℝ) / (p : ℝ) := hdecomp.symm
    _ ≤ ∑ k ∈ T,
          (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ)) :=
          Finset.sum_le_sum hfiber_le
    _ ≤ ∑ k ∈ T, D / ((k + 1 : ℕ) : ℝ) := hsum_blocks
    _ = D * ∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = D * ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / (j : ℝ) := by
          rw [hsum_shift]
    _ ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (harmonic_Icc_one_le_one_add_log (Nat.log 2 N + 1))
            (by
              have hD0 := hD 0
              have hblock0_nonneg :
                  0 ≤
                    (∑ p ∈ (Finset.Ico (2 ^ 0) (2 ^ (0 + 1))).filter Nat.Prime,
                      (1 : ℝ) / (p : ℝ)) := by
                refine Finset.sum_nonneg ?_
                intro p hp
                exact div_nonneg zero_le_one (by positivity)
              have hden : (((0 + 1 : ℕ) : ℝ)) = 1 := by norm_num
              nlinarith [hD0, hblock0_nonneg])

lemma eventually_one_add_log_nat_log_le_two_loglog :
    ∀ᶠ N : ℕ in atTop,
      1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
        ≤ 2 * Real.log (Real.log (N : ℝ)) := by
  let C : ℝ := 2 / Real.log 2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by positivity
  have hloglog_large :
      ∀ᶠ N : ℕ in atTop,
        1 + Real.log C ≤ Real.log (Real.log (N : ℝ)) :=
    tendsto_loglog_nat_atTop.eventually_ge_atTop (1 + Real.log C)
  filter_upwards [hloglog_large,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hll_large hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog2_lt_one : Real.log 2 < 1 :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2 Real.exp_one_gt_two
  have hlog2_le_logN : Real.log 2 ≤ Real.log (N : ℝ) := by linarith
  have hquot_ge_one : 1 ≤ Real.log (N : ℝ) / Real.log 2 := by
    have : (1 : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
      simpa using hlog2_le_logN
    exact (le_div_iff₀ hlog2pos).2 this
  have hlog_nat_le :
      ((Nat.log 2 N : ℕ) : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    have h := Real.log2_le_logb N
    simpa [Nat.log2_eq_log_two, Real.logb] using h
  have hnatlog_add_le :
      (((Nat.log 2 N + 1 : ℕ) : ℝ)) ≤ C * Real.log (N : ℝ) := by
    calc
      (((Nat.log 2 N + 1 : ℕ) : ℝ))
          = ((Nat.log 2 N : ℕ) : ℝ) + 1 := by norm_num
      _ ≤ Real.log (N : ℝ) / Real.log 2 + 1 := by linarith
      _ ≤ Real.log (N : ℝ) / Real.log 2 +
            Real.log (N : ℝ) / Real.log 2 := by linarith
      _ = C * Real.log (N : ℝ) := by
            dsimp [C]
            ring
  have hleft_pos : 0 < (((Nat.log 2 N + 1 : ℕ) : ℝ)) := by positivity
  have hright_pos : 0 < C * Real.log (N : ℝ) := mul_pos hCpos hlogpos
  have hlog_bound :
      Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
        ≤ Real.log C + Real.log (Real.log (N : ℝ)) := by
    calc
      Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
          ≤ Real.log (C * Real.log (N : ℝ)) :=
            Real.log_le_log hleft_pos hnatlog_add_le
      _ = Real.log C + Real.log (Real.log (N : ℝ)) := by
            rw [Real.log_mul hCpos.ne' hlogpos.ne']
  linarith

/-- A constant-coefficient reciprocal-prime Mertens upper bound.

This proof is intentionally non-sharp: Chebyshev's upper bound for
`Nat.primeCounting` gives an `O(1/k)` estimate on dyadic prime blocks, and the
dyadic harmonic sum is `O(log log N)`. -/
theorem reciprocal_prime_sum_mertens :
    ∃ A C : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
      (((Finset.Icc 1 N).filter Nat.Prime).sum
          (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
        ≤ A * Real.log (Real.log (N : ℝ)) + C := by
  rcases reciprocal_prime_sum_Ico_pow_two_le_const_global with ⟨D, hDpos, hD⟩
  refine ⟨2 * D, 0, by positivity, ?_⟩
  filter_upwards [eventually_one_add_log_nat_log_le_two_loglog] with N hloglog
  calc
    (((Finset.Icc 1 N).filter Nat.Prime).sum
        (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
        ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) :=
          reciprocal_prime_sum_le_dyadic_harmonic D hD N
    _ ≤ D * (2 * Real.log (Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hloglog hDpos.le
    _ = (2 * D) * Real.log (Real.log (N : ℝ)) + 0 := by ring
lemma exists_fiber_card_mul_range_card_ge {α β : Type*} [DecidableEq β]
    (s : Finset α) (B : Finset β) (g : α → β)
    (hBne : B.Nonempty) (hB : ∀ x ∈ s, g x ∈ B) :
    ∃ b ∈ B, s.card ≤ B.card * (s.filter fun x => g x = b).card := by
  classical
  rcases Finset.exists_max_image B (fun b => (s.filter fun x => g x = b).card) hBne with
    ⟨b, hb, hbmax⟩
  refine ⟨b, hb, ?_⟩
  have hsum :
      s.card = ∑ b ∈ B, (s.filter fun x => g x = b).card := by
    exact Finset.card_eq_sum_card_fiberwise hB
  have hsum_le :
      (∑ b ∈ B, (s.filter fun x => g x = b).card) ≤
        ∑ _b ∈ B, (s.filter fun x => g x = b).card := by
    exact Finset.sum_le_sum hbmax
  rw [hsum]
  exact hsum_le.trans (by simp)

private structure Packing {ι : Type} (s : Finset ι) (q : ι → ℕ) (a : ι → ℤ) (N : ℕ) : Prop where
  bounds : ∀ i ∈ s, 0 < q i ∧ q i ≤ N
  inj : Set.InjOn q (s : Set ι)
  sep : ∀ i ∈ s, ∀ j ∈ s, ∀ x : ℤ, x ≡ a i [ZMOD (q i : ℤ)] →
      x ≡ a j [ZMOD (q j : ℤ)] → i = j

private theorem Packing.restrict {ι : Type} {s t : Finset ι} {q a N}
    (h : Packing s q a N) (ht : t ⊆ s) : Packing t q a N :=
  ⟨fun i hi => h.bounds i (ht hi), h.inj.mono ht,
    fun i hi j hj => h.sep i (ht hi) j (ht hj)⟩

private theorem Packing.share {ι : Type} {s : Finset ι} {q a N} (h : Packing s q a N)
    (hs : 1 < s.card) {i j} (hi : i ∈ s) (hj : j ∈ s) :
    ∃ p ∈ (q i).primeFactors, p ∣ q j := by
  have aux : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ (q x).Coprime (q y) := by
    intro x hx y hy hxy hc
    have hm : a x ≡ a y [ZMOD (Nat.gcd (q x) (q y) : ℤ)] := by simp [hc.gcd_eq_one, Int.ModEq]
    obtain ⟨z, hz, hz'⟩ := (residueClass_inter_nonempty_iff
      (h.bounds x hx).1 (h.bounds y hy).1 (a x) (a y)).2 hm
    exact hxy (h.sep x hx y hy z hz hz')
  have hnc : ¬ (q i).Coprime (q j) := by
    by_cases he : i = j
    · subst j
      obtain ⟨b, hb, hbi⟩ := s.exists_mem_ne hs i
      intro hc
      have hone : q i = 1 := by simpa [Nat.Coprime] using hc
      exact aux i hi b hb hbi.symm (by simp [hone])
    · exact aux i hi j hj he
  obtain ⟨p, hp, hpi, hpj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpi, (h.bounds i hi).1.ne'⟩, hpj⟩

private theorem Packing.step {ι : Type} {s : Finset ι} {q a N K k D : _}
    (h : Packing s q a N) (hs : 1 < s.card) (hd : N ≤ D * s.card)
    (hk : k + 1 ≤ K) (hΩ : ∀ i ∈ s, Ω (q i) ≤ k + 1) :
    ∃ (p : ℕ) (t : Finset ι), 0 < p ∧ p ≤ D*K ∧ p ≤ N ∧
      Packing t (fun i => q i / p) (fun i => a i / (p : ℤ)) (N / p) ∧
      N / p ≤ (D*K) * t.card ∧ ∀ i ∈ t, Ω (q i / p) ≤ k := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  let g := fun j => if hj : j ∈ s then (h.share hs hi hj).choose else 0
  have hg (j) (hj : j ∈ s) : g j ∈ (q i).primeFactors ∧ g j ∣ q j := by
    simpa [g, hj] using (h.share hs hi hj).choose_spec
  obtain ⟨p, hp, hpop⟩ := exists_fiber_card_mul_range_card_ge s (q i).primeFactors g
    ⟨g i, (hg i hi).1⟩ (fun j hj => (hg j hj).1)
  let u := s.filter fun j => g j = p
  have hK : (q i).primeFactors.card ≤ K :=
    (List.toFinset_card_le _).trans ((hΩ i hi).trans hk)
  have hpop' : s.card ≤ K * u.card := hpop.trans (Nat.mul_le_mul_right _ hK)
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpN := (Nat.le_of_dvd (h.bounds i hi).1 (Nat.dvd_of_mem_primeFactors hp)).trans (h.bounds i hi).2
  have hu (j) (hj : j ∈ u) : j ∈ s ∧ p ∣ q j := by
    obtain ⟨hsj, hh⟩ := mem_filter.mp hj
    exact ⟨hsj, hh ▸ (hg j hsj).2⟩
  have hu_pos (j) (hj : j ∈ u) : 0 < q j / p :=
    Nat.div_pos (Nat.le_of_dvd (h.bounds j (hu j hj).1).1 (hu j hj).2) hprime.pos
  have inj' : Set.InjOn (fun j => q j / p) (u : Set ι) := by
    intro x hx y hy he
    apply h.inj (hu x hx).1 (hu y hy).1
    simpa only [Nat.div_mul_cancel (hu x hx).2, Nat.div_mul_cancel (hu y hy).2] using
      congrArg (fun v : ℕ => v * p) he
  have hcount : u.card ≤ N / p := by
    have := Finset.card_le_card_of_injOn (s := u) (t := Icc 1 (N / p))
      (fun j => q j / p) (fun j hj => mem_Icc.mpr ⟨hu_pos j hj,
        Nat.div_le_div_right (h.bounds j (hu j hj).1).2⟩) inj'
    simpa using this
  have hud : N ≤ (D*K) * u.card := by
    simpa only [Nat.mul_assoc] using hd.trans (Nat.mul_le_mul_left D hpop')
  have hu0 : 0 < u.card := by
    by_contra! hh
    rw [Nat.eq_zero_of_le_zero hh, Nat.mul_zero] at hpop'
    omega
  have hpDK : p ≤ D*K := by
    apply Nat.le_of_mul_le_mul_right (c := u.card) _ hu0
    exact (Nat.mul_le_mul_left p hcount).trans ((Nat.mul_div_le N p).trans hud)
  let b := fun j => (a j % (p : ℤ)).toNat
  have hpi : (0 : ℤ) < p := by exact_mod_cast hprime.pos
  have hb (j) : (b j : ℤ) = a j % (p : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hpi.ne')
  obtain ⟨r, hr, hres⟩ := exists_fiber_card_mul_range_card_ge u (range p) b
    ⟨0, by simpa using hprime.pos⟩ (fun j _ => by
      apply mem_range.mpr
      have := Int.emod_lt_of_pos (a j) hpi
      rw [← hb] at this
      exact_mod_cast this)
  let t := u.filter fun j => b j = r
  have hres' : u.card ≤ p * t.card := by simpa [t] using hres
  have ht (j) (hj : j ∈ t) : j ∈ u := (mem_filter.mp hj).1
  have heq (j) (hj : j ∈ t) : (r : ℤ) + p * (a j / (p : ℤ)) = a j := by
    rw [← (mem_filter.mp hj).2, hb]
    exact Int.emod_add_mul_ediv _ _
  refine ⟨p, t, hprime.pos, hpDK, hpN, ⟨?_, inj'.mono (filter_subset _ _), ?_⟩, ?_, ?_⟩
  · intro j hj
    exact ⟨hu_pos j (ht j hj), Nat.div_le_div_right (h.bounds j (hu j (ht j hj)).1).2⟩
  · intro j hj l hl x hx hy
    have lift (v) (hv : v ∈ t) (hxv : x ≡ a v / (p : ℤ) [ZMOD (q v / p : ℕ)]) :
        (r : ℤ) + p*x ≡ a v [ZMOD (q v : ℤ)] := by
      have hz := (Int.ModEq.mul_left' (c := (p : ℤ)) hxv).add_left (r : ℤ)
      have hprod : (p : ℤ) * (q v / p : ℕ) = q v := by
        exact_mod_cast Nat.mul_div_cancel' (hu v (ht v hv)).2
      rwa [hprod, heq v hv] at hz
    exact h.sep j (hu j (ht j hj)).1 l (hu l (ht l hl)).1 _ (lift j hj hx) (lift l hl hy)
  · have hz := hud.trans (Nat.mul_le_mul_left (D*K) hres')
    calc
      N / p ≤ ((D*K*t.card)*p)/p := Nat.div_le_div_right (by simpa only [Nat.mul_assoc, Nat.mul_comm p t.card] using hz)
      _ = _ := Nat.mul_div_cancel _ hprime.pos
  · intro j hj
    have hv := hu j (ht j hj)
    have hbound := hΩ j hv.1
    have hh := ArithmeticFunction.cardFactors_mul hprime.ne_zero (hu_pos j (ht j hj)).ne'
    rw [Nat.mul_div_cancel' hv.2, ArithmeticFunction.cardFactors_apply_prime hprime] at hh
    omega

private theorem Packing.small {ι : Type} {s : Finset ι} {q a N} (h : Packing s q a N)
    (h0 : ∀ i ∈ s, Ω (q i) ≤ 0) : s.card ≤ 1 := by
  by_contra! hs
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  obtain ⟨p, hp, -⟩ := h.share hs hx hx
  have he := cardFactors_eq_zero_iff_eq_zero_or_one.mp (Nat.eq_zero_of_le_zero (h0 x hx))
  have hxpos := (h.bounds x hx).1
  rcases he with he | he
  · omega
  · simp [he] at hp

private theorem chain {ι : Type} (K B k : ℕ) (hK : 1 ≤ K) (hk : k ≤ K)
    {s : Finset ι} {q a N D} (h : Packing s q a N) (hd : N ≤ D * s.card)
    (hΩ : ∀ i ∈ s, Ω (q i) ≤ k) (hB : D*K^k ≤ B) :
    N + 1 ≤ (B+1)^(k+1) := by
  have hDB : D ≤ B := (Nat.le_mul_of_pos_right _ (pow_pos hK _)).trans hB
  by_cases hs : s.card ≤ 1
  · have hn : N ≤ D := hd.trans (by simpa using Nat.mul_le_mul_left D hs)
    exact (Nat.succ_le_succ (hn.trans hDB)).trans (Nat.le_self_pow (by omega) _)
  · cases k with
    | zero => exact False.elim (hs (h.small hΩ))
    | succ k =>
      obtain ⟨p, t, hp, hpD, hpN, ht, hdt, hΩt⟩ := h.step (by omega) hd hk hΩ
      have hB' : (D*K)*K^k ≤ B := by simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm K] using hB
      have hpb : p ≤ B := hpD.trans ((Nat.le_mul_of_pos_right _ (pow_pos hK _)).trans hB')
      have hrec := chain K B k hK (by omega) ht hdt hΩt hB'
      have hrem := Nat.mod_lt N hp
      have hdiv := Nat.mod_add_div N p
      calc
        N+1 ≤ p * (N/p+1) := by rw [Nat.mul_add, Nat.mul_one]; omega
        _ ≤ (B+1) * (B+1)^(k+1) := Nat.mul_le_mul (by omega) hrec
        _ = _ := by rw [pow_succ (B+1) (k+1), Nat.mul_comm]
termination_by k

private theorem sum_omega_factorial (N : ℕ) :
    ∑ n ∈ Icc 1 N, Ω n = Ω N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
      cardFactors_mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _), Nat.add_comm]

private theorem omega_total (N : ℕ) :
    (∑ n ∈ Icc 1 N, (Ω n : ℝ)) ≤
        2 * N * ∑ p ∈ (Icc 1 N).filter Nat.Prime, (1 : ℝ)/p := by
  rw [← Nat.cast_sum, sum_omega_factorial, cardFactors_eq_sum_factorization, Finsupp.sum, Nat.cast_sum,
    Finset.mul_sum]
  have hsub : N.factorial.factorization.support ⊆ (Icc 1 N).filter Nat.Prime := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors (show p ∈ N.factorial.primeFactors from hp)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp'.pos, by
      by_contra! hn
      exact Finsupp.mem_support_iff.mp hp (Nat.factorization_factorial_eq_zero_of_lt hn)⟩, hp'⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)).trans ?_
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (mem_filter.mp hp).2
  have hfac := Nat.factorization_factorial_le_div_pred hprime N
  have hmul : N.factorial.factorization p * (p-1) ≤ N :=
    (Nat.mul_le_mul_right _ hfac).trans (Nat.div_mul_le_self _ _)
  have hp2 := hprime.two_le
  have hpR : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hR : (N.factorial.factorization p : ℝ)*((p:ℝ)-1) ≤ N := by
    have hh : (N.factorial.factorization p : ℝ) * (↑(p-1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hmul
    simpa [Nat.cast_sub hprime.pos] using hh
  rw [mul_one_div, le_div_iff₀ hpR]
  nlinarith [mul_nonneg (Nat.cast_nonneg (N.factorial.factorization p) : (0:ℝ) ≤ _)
    (sub_nonneg.mpr (show (2:ℝ) ≤ p by exact_mod_cast hp2))]

private theorem Packing.logbound {ι : Type} {s : Finset ι} {q a N D K} (h : Packing s q a N)
    (hN : 0 < N) (hK : 1 ≤ K) (hd : N ≤ D*s.card) (hΩ : ∀ i ∈ s, Ω (q i) ≤ K) :
    Real.log N ≤ (D+2 : ℝ) * ((K:ℝ)+1)^3 := by
  have hh := chain K (D*K^K) K hK le_rfl h hd hΩ le_rfl
  have hh' : (N:ℝ) ≤ ((D:ℝ)*(K:ℝ)^K+1)^((K:ℕ)+1) := by
    exact_mod_cast (Nat.le_of_succ_le hh)
  have hlog := Real.log_le_log (by exact_mod_cast hN) hh'
  rw [Real.log_pow] at hlog
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hbase : (D:ℝ)*K^K+1 ≤ ((D:ℝ)+1)*((K:ℝ)+1)^K := by
    have hp : (K:ℝ)^K ≤ ((K:ℝ)+1)^K := by gcongr; linarith
    have hone : 1 ≤ ((K:ℝ)+1)^K := one_le_pow₀ (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg D)]
  have hL := Real.log_le_log (by positivity) hbase
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hL
  have hlD := Real.log_le_sub_one_of_pos (show 0 < (D:ℝ)+1 by positivity)
  have hlK := Real.log_le_sub_one_of_pos (show 0 < (K:ℝ)+1 by positivity)
  push_cast at hlog
  calc
    _ ≤ ((K:ℝ)+1) * Real.log ((D:ℝ)*K^K+1) := hlog
    _ ≤ ((K:ℝ)+1) * ((D:ℝ) + (K:ℝ)^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hlK (Nat.cast_nonneg K)]
    _ ≤ _ := by
      nlinarith [mul_nonneg (Nat.cast_nonneg D) (sq_nonneg (K:ℝ)),
        mul_nonneg (Nat.cast_nonneg D) (pow_nonneg (Nat.cast_nonneg K : (0:ℝ) ≤ _) 3),
        mul_nonneg (Nat.cast_nonneg D) (Nat.cast_nonneg K : (0:ℝ) ≤ _)]

private noncomputable def cut (N : ℕ) := ⌈(Real.log (Real.log (N:ℝ)))^2⌉₊

private theorem no_dense_small (D : ℕ) : ∀ᶠ N : ℕ in atTop,
    ∀ {ι : Type} {s : Finset ι} {q a}, Packing s q a N →
      (∀ i ∈ s, Ω (q i) ≤ cut N) → ¬ N ≤ D*s.card := by
  let C : ℝ := 54*((D:ℝ)+2)
  have hC : 0 < C := by dsimp [C]; positivity
  have hpow := Real.isLittleO_pow_exp_atTop (n := 6) |>.bound (one_div_pos.mpr hC)
  filter_upwards [tendsto_loglog_nat_atTop.eventually hpow,
    tendsto_loglog_nat_atTop.eventually_ge_atTop 1,
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0),
    Filter.eventually_gt_atTop (0:ℕ)] with N hP hL hlog hN
  intro ι s q a h hΩ hd
  let L := Real.log (Real.log (N:ℝ))
  change 1 ≤ L at hL
  change ‖L^6‖ ≤ 1/C * ‖Real.exp L‖ at hP
  have he : Real.exp L = Real.log (N:ℝ) := Real.exp_log hlog
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le, he,
    one_div_mul_eq_div, le_div_iff₀ hC] at hP
  have hc : L^2 ≤ (cut N : ℝ) := Nat.le_ceil _
  have hc' : (cut N:ℝ) < L^2+1 := Nat.ceil_lt_add_one (sq_nonneg L)
  have hk : 1 ≤ cut N := by exact_mod_cast (show (1:ℝ) ≤ cut N by nlinarith)
  have hb := h.logbound hN hk hd hΩ
  have h3 : ((cut N:ℝ)+1)^3 ≤ (3*L^2)^3 := by gcongr; nlinarith
  have hpos : 0 < L^6 := pow_pos (by linarith) _
  dsimp [C] at hP
  nlinarith [mul_le_mul_of_nonneg_left h3 (show 0 ≤ (D:ℝ)+2 by positivity),
    mul_nonneg (Nat.cast_nonneg D) hpos.le]

private theorem bound_packing (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop,
    ∀ {ι : Type} {s : Finset ι} {q a}, Packing s q a N → (s.card:ℝ) ≤ ε*N := by
  classical
  obtain ⟨A,C,hA,hM⟩ := reciprocal_prime_sum_mertens
  let D := ⌈2/ε⌉₊
  have hD : (2:ℝ)/ε ≤ D := Nat.le_ceil _
  have hDε : 2 ≤ (D:ℝ)*ε := (div_le_iff₀ hε).mp hD
  have hD0 : (0:ℝ) < D := (div_pos (by norm_num) hε).trans_le hD
  filter_upwards [no_dense_small D, hM,
    tendsto_loglog_nat_atTop.eventually_ge_atTop (4*(A+|C|)/ε+1),
    tendsto_loglog_nat_atTop.eventually_ge_atTop 1] with N hsmall hpr hsize hL
  intro ι s q a h
  let t := s.filter fun i => Ω (q i) ≤ cut N
  let u := s.filter fun i => ¬ Ω (q i) ≤ cut N
  have ht := h.restrict (show t ⊆ s from filter_subset _ _)
  have hlt : D*t.card < N := Nat.lt_of_not_ge (hsmall ht (fun i hi => (mem_filter.mp hi).2))
  have htR : (t.card:ℝ) ≤ ε*N/2 := by
    have hr : (D:ℝ)*t.card < N := by exact_mod_cast hlt
    apply (le_of_mul_le_mul_left (a := (D:ℝ)) _ hD0)
    nlinarith [mul_le_mul_of_nonneg_right hDε (Nat.cast_nonneg N : (0:ℝ) ≤ _)]
  have hsum : (u.card:ℝ)*(cut N) ≤ ∑ n ∈ Icc 1 N, (Ω n:ℝ) := by
    calc
      _ = ∑ _i ∈ u, (cut N:ℝ) := by simp
      _ ≤ ∑ i ∈ u, (Ω (q i):ℝ) := sum_le_sum fun i hi => by
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge (mem_filter.mp hi).2))
      _ = ∑ n ∈ u.image q, (Ω n:ℝ) := (sum_image (s := u) (f := fun n => (Ω n : ℝ)) (h.inj.mono (show u ⊆ s from filter_subset _ _))).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (by
        intro n hn
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
        exact mem_Icc.mpr (h.bounds _ (mem_filter.mp hi).1)) (fun _ _ _ => by positivity)
  let L := Real.log (Real.log (N:ℝ))
  change 1 ≤ L at hL
  have hsL : 4*(A+|C|)/ε ≤ L := by dsimp [L]; linarith
  have hnum : 4*(A+|C|) ≤ L*ε := (div_le_iff₀ hε).mp hsL
  have hc : L^2 ≤ (cut N : ℝ) := Nat.le_ceil _
  have hcut : 0 < (cut N:ℝ) := by nlinarith
  have hcoef : 2*(A*L+C) ≤ ε/2*(cut N:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hnum (by linarith : 0 ≤ L),
      mul_le_mul_of_nonneg_left hc hε.le,
      mul_nonneg (abs_nonneg C) (sub_nonneg.mpr hL), le_abs_self C]
  have huR : (u.card:ℝ) ≤ ε*N/2 := by
    apply le_of_mul_le_mul_right (a := (cut N:ℝ)) _ hcut
    calc
      _ ≤ _ := hsum.trans (omega_total N)
      _ ≤ 2*(N:ℝ)*(A*L+C) := mul_le_mul_of_nonneg_left hpr (by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg N)]
  have hadd : t.card + u.card = s.card := Finset.card_filter_add_card_filter_not ..
  have hreal : (t.card:ℝ)+u.card = s.card := by exact_mod_cast hadd
  linarith

end OMA.E202

open Filter OMA.E202 in
theorem OMA.solution : type_of% @Erdos202.erdos_202.variants.erdos_szemeredi := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  filter_upwards [bound_packing ε hε] with N hN
  simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  apply (Nat.le_floor_iff (by positivity : 0 ≤ ε*(N:ℝ))).mp
  unfold Erdos202.f
  apply csSup_le'
  rintro r ⟨n,a,hn,hb,hd⟩
  have hp : Packing Finset.univ n a N :=
    ⟨fun i _ => hb i, hn.injective.injOn, fun i _ j _ x => hd x i j⟩
  have hr := hN hp
  simpa using (Nat.le_floor hr)
