import FormalConjectures.ErdosProblems.«11»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Tactic

/-!
# Erdos Problem 11: Granville-Soundararajan Conditional Infinitude of Non-Wieferich Primes

Proof of `Erdos11.erdos_11.variants.granville_soundararajan` following Theorem 1 and
Proposition 1 of Granville and Soundararajan (1998).
-/

open Finset Filter
open scoped Topology

private def periodTwo (p : ℕ) : ℕ :=
  if p % 8 = 1 then (p - 1) / 2 else p - 1

private lemma zmod8_eq_one_iff (n : ℕ) : (n : ZMod 8) = 1 ↔ n % 8 = 1 := by
  change ((n : ℕ) : ZMod 8) = ((1 : ℕ) : ZMod 8) ↔ n % 8 = 1
  rw [ZMod.natCast_eq_natCast_iff]
  simp [Nat.ModEq]

private lemma periodTwo_pos {p : ℕ} (hp : 8 < p) : 0 < periodTwo p := by
  unfold periodTwo
  split_ifs <;> omega

private lemma pow_periodTwo_modEq_one {p : ℕ} (hp : p.Prime) (hp8 : 8 < p)
    (hwief : 2 ^ p ≡ 2 [MOD p ^ 2]) : 2 ^ periodTwo p ≡ 1 [MOD p ^ 2] := by
  have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hcop2 : Nat.Coprime 2 (p ^ 2) := by
    refine ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_).pow_right 2
    omega
  have hwief1 : 2 ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
    apply Nat.ModEq.cancel_left_of_coprime hcop2.symm
    have hpow : 2 * 2 ^ (p - 1) = 2 ^ p := by
      calc 2 * 2 ^ (p - 1) = 2 ^ 1 * 2 ^ (p - 1) := by ring
        _ = 2 ^ (1 + (p - 1)) := (pow_add 2 1 (p - 1)).symm
        _ = 2 ^ p := by congr 1; omega
    rw [hpow, mul_one]
    exact hwief
  unfold periodTwo
  split_ifs with h8
  · have : Fact p.Prime := ⟨hp⟩
    have hsq : IsSquare (2 : ZMod p) :=
      (ZMod.exists_sq_eq_two_iff (p := p) (by omega)).mpr (Or.inl h8)
    obtain ⟨c, hc⟩ := hsq
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hc
      have h20 : ((2 : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by simpa using hc
      have hdvd : p ∣ 2 := by
        have hm := (ZMod.natCast_eq_natCast_iff 2 0 p).mp h20
        exact (Nat.modEq_zero_iff_dvd).mp hm
      have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hdvd
      omega
    have hzmod : ((2 ^ ((p - 1) / 2) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      push_cast
      rw [hc, mul_pow, ← pow_add]
      have h2div : (p - 1) / 2 + (p - 1) / 2 = p - 1 := by omega
      rw [h2div]
      simpa using ZMod.pow_card_sub_one_eq_one hc0
    have hmodp : 2 ^ ((p - 1) / 2) ≡ 1 [MOD p] :=
      (ZMod.natCast_eq_natCast_iff _ _ p).mp hzmod
    set X := 2 ^ ((p - 1) / 2)
    have hX_pos : 1 ≤ X := by
      dsimp [X]
      exact Nat.one_le_pow _ 2 (by omega)
    have hp_dvd_X1 : p ∣ X - 1 := by
      have hm0 : (X - 1) % p = 0 := by
        have hm1 : X % p = 1 % p := hmodp
        have hm1' : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
        have hdm := Nat.div_add_mod X p
        have hrem : p * (X / p) = X - 1 := by omega
        exact Nat.dvd_iff_mod_eq_zero.mp ⟨X / p, hrem.symm⟩
      exact Nat.dvd_of_mod_eq_zero hm0
    obtain ⟨q, hq⟩ := hp_dvd_X1
    have hX_eq : X = 1 + p * q := by omega
    have hX2_eq : 2 ^ (p - 1) = 1 + 2 * p * q + p ^ 2 * q ^ 2 := by
      have h2div : 2 * ((p - 1) / 2) = p - 1 := by omega
      calc 2 ^ (p - 1) = 2 ^ (((p - 1) / 2) * 2) := by congr 1; omega
        _ = X ^ 2 := pow_mul 2 ((p - 1) / 2) 2
        _ = (1 + p * q) ^ 2 := by rw [hX_eq]
        _ = 1 + 2 * p * q + p ^ 2 * q ^ 2 := by ring
    have hp2_dvd_2pq : p ^ 2 ∣ 2 * p * q := by
      have hp2_pos : 1 < p ^ 2 := by
        calc 1 < 9 * 9 := by omega
          _ ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
          _ = p ^ 2 := by ring
      have hrem1 : 2 ^ (p - 1) % p ^ 2 = 1 := by
        have h := hwief1
        rwa [Nat.ModEq, Nat.mod_eq_of_lt hp2_pos] at h
      have hdm := Nat.div_add_mod (2 ^ (p - 1)) (p ^ 2)
      have hp2_sub : p ^ 2 ∣ 2 ^ (p - 1) - 1 := ⟨2 ^ (p - 1) / p ^ 2, by omega⟩
      have hsub_eq : 2 ^ (p - 1) - 1 = 2 * p * q + p ^ 2 * q ^ 2 := by omega
      rw [hsub_eq] at hp2_sub
      exact (Nat.dvd_add_left ⟨q ^ 2, rfl⟩).mp hp2_sub
    have hp_dvd_2q : p ∣ 2 * q := by
      apply (Nat.mul_dvd_mul_iff_left hp.pos).mp
      calc p * p = p ^ 2 := by ring
        _ ∣ 2 * p * q := hp2_dvd_2pq
        _ = p * (2 * q) := by ring
    have hcop_p2 : Nat.Coprime p 2 :=
      (hp.coprime_iff_not_dvd).mpr (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega)
    obtain ⟨t, ht⟩ := hcop_p2.dvd_of_dvd_mul_left hp_dvd_2q
    have hX_p2 : X = 1 + p ^ 2 * t := by
      rw [hX_eq, ht]
      ring
    change X % p ^ 2 = 1 % p ^ 2
    rw [hX_p2, Nat.add_mul_mod_self_left]
  · exact hwief1

private lemma pow_two_modEq_of_mod_eq {p i a : ℕ} (hp : p.Prime) (hp8 : 8 < p)
    (hwief : 2 ^ p ≡ 2 [MOD p ^ 2]) (hmod : i % periodTwo p = a % periodTwo p) :
    2 ^ i ≡ 2 ^ a [MOD p ^ 2] := by
  have hd1 := pow_periodTwo_modEq_one hp hp8 hwief
  have haux : ∀ x : ℕ, 2 ^ x ≡ 2 ^ (x % periodTwo p) [MOD p ^ 2] := by
    intro x
    conv_lhs => rw [← Nat.div_add_mod x (periodTwo p)]
    rw [pow_add, pow_mul]
    have hpow := hd1.pow (x / periodTwo p)
    rw [one_pow] at hpow
    simpa using hpow.mul_right (2 ^ (x % periodTwo p))
  exact (haux i).trans (hmod ▸ (haux a).symm)

private lemma not_summable_prime_mod8_inv :
    ¬ Summable (fun n : ℕ => if n.Prime ∧ n % 8 = 1 then (1 : ℝ) / n else 0) := by
  set f : ℕ → ℝ := fun n => if n.Prime ∧ n % 8 = 1 then (1 : ℝ) / n else 0
  intro hsum
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => by
    dsimp [f]
    split_ifs <;> positivity
  have htend := hsum.hasSum.tendsto_sum_nat
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨K, hK⟩ := htend (1 / 8) (by norm_num)
  specialize hK K le_rfl
  rw [Real.dist_eq] at hK
  set f_head : ℕ → ℝ := fun n => if n < K then f n else 0
  set f_tail : ℕ → ℝ := fun n => if K ≤ n then f n else 0
  have hf_head_sum : Summable f_head :=
    summable_of_ne_finset_zero (s := Finset.range K) (fun n hn => by
      have : ¬ n < K := by simpa using hn
      simp [f_head, this])
  have hf_tail_sum : Summable f_tail :=
    hsum.of_nonneg_of_le (fun n => by dsimp [f_tail]; split_ifs <;> positivity [hf_nonneg n])
      (fun n => by dsimp [f_tail]; split_ifs <;> simp [hf_nonneg n])
  have hf_split : f = fun n => f_head n + f_tail n := by
    ext n
    dsimp [f_head, f_tail]
    by_cases h : n < K
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  have htsum_head : (∑' n, f_head n) = ∑ n ∈ Finset.range K, f n := by
    rw [tsum_eq_sum (s := Finset.range K)]
    · refine Finset.sum_congr rfl fun n hn => ?_
      simp [f_head, Finset.mem_range.mp hn]
    · intro n hn
      have : ¬ n < K := by simpa using hn
      simp [f_head, this]
  have htsum_tail_lt : (∑' n, f_tail n) < 1 / 8 := by
    have hadd : (∑' n, f n) = (∑' n, f_head n) + ∑' n, f_tail n := by
      conv_lhs => rw [hf_split]
      exact hf_head_sum.tsum_add hf_tail_sum
    rw [htsum_head] at hadd
    have habs := abs_lt.mp hK
    linarith
  let a8 : ZMod 8 := 1
  obtain ⟨C, hC⟩ :=
    ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound (q := 8) (a := a8) isUnit_one
  set g_non : ℕ → ℝ :=
    fun n => (if n.Prime then 0 else ArithmeticFunction.vonMangoldt.residueClass a8 n) / n
  have hg_non_sum : Summable g_non :=
    ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div a8
  set g_fin : ℕ → ℝ :=
    fun n => if n < K then ArithmeticFunction.vonMangoldt.residueClass a8 n else 0
  have hg_fin_sum : Summable g_fin :=
    summable_of_ne_finset_zero (s := Finset.range K) (fun n hn => by
      have : ¬ n < K := by simpa using hn
      simp [g_fin, this])
  have hg_non_nonneg : ∀ n, 0 ≤ g_non n := fun n => by
    dsimp [g_non]
    split_ifs
    · positivity
    · exact div_nonneg (ArithmeticFunction.vonMangoldt.residueClass_nonneg a8 n) (Nat.cast_nonneg n)
  have hg_fin_nonneg : ∀ n, 0 ≤ g_fin n := fun n => by
    dsimp [g_fin]
    split_ifs
    · exact ArithmeticFunction.vonMangoldt.residueClass_nonneg a8 n
    · exact le_rfl
  have hf_tail_nonneg : ∀ n, 0 ≤ f_tail n := fun n => by
    dsimp [f_tail]
    split_ifs <;> positivity [hf_nonneg n]
  set M_const : ℝ := |C| + (∑' n, g_fin n) + (∑' n, g_non n) + 1
  have hM_pos : 0 < M_const := by
    have h1 : 0 ≤ ∑' n, g_fin n := tsum_nonneg hg_fin_nonneg
    have h2 : 0 ≤ ∑' n, g_non n := tsum_nonneg hg_non_nonneg
    positivity
  set δ : ℝ := min 1 (1 / (16 * M_const))
  have hδ_pos : 0 < δ := by positivity
  have hδ_le1 : δ ≤ 1 := min_le_left _ _
  have hδM : δ * M_const ≤ 1 / 16 := by
    calc δ * M_const ≤ (1 / (16 * M_const)) * M_const :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hM_pos.le
      _ = 1 / 16 := by field_simp
  have hx_mem : 1 + δ ∈ Set.Ioc (1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hLB := hC hx_mem
  have htot8 : Nat.totient 8 = 4 := by decide
  rw [htot8] at hLB
  set h_ser : ℕ → ℝ :=
    fun n => δ * (ArithmeticFunction.vonMangoldt.residueClass a8 n / (n : ℝ) ^ (1 + δ))
  set h_maj : ℕ → ℝ := fun n => δ * g_fin n + δ * g_non n + f_tail n
  have h_maj_sum : Summable h_maj :=
    ((hg_fin_sum.mul_left δ).add (hg_non_sum.mul_left δ)).add hf_tail_sum
  have h_pw : ∀ n, h_ser n ≤ h_maj n := by
    intro n
    have hgf0 := hg_fin_nonneg n
    have hgn0 := hg_non_nonneg n
    have hft0 := hf_tail_nonneg n
    have hδgf0 : 0 ≤ δ * g_fin n := mul_nonneg hδ_pos.le hgf0
    have hδgn0 : 0 ≤ δ * g_non n := mul_nonneg hδ_pos.le hgn0
    rcases n.eq_zero_or_pos with rfl | hn_pos
    · have h0 : h_ser 0 = 0 := by simp [h_ser]
      rw [h0]
      positivity
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn_pos
      have hrc0 : 0 ≤ ArithmeticFunction.vonMangoldt.residueClass a8 n :=
        ArithmeticFunction.vonMangoldt.residueClass_nonneg a8 n
      by_cases hnK : n < K
      · have hrpow1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 + δ) := Real.one_le_rpow hn1 (by linarith)
        have hdiv : ArithmeticFunction.vonMangoldt.residueClass a8 n / (n : ℝ) ^ (1 + δ) ≤
            g_fin n := by
          dsimp [g_fin]
          rw [if_pos hnK]
          exact div_le_self hrc0 hrpow1
        have hmul := mul_le_mul_of_nonneg_left hdiv hδ_pos.le
        dsimp [h_ser, h_maj]
        linarith
      · by_cases hnp : n.Prime
        · by_cases hmod8 : (n : ZMod 8) = a8
          · have hm8 : n % 8 = 1 := (zmod8_eq_one_iff n).mp hmod8
            have hrc_eq : ArithmeticFunction.vonMangoldt.residueClass a8 n = Real.log n := by
              unfold ArithmeticFunction.vonMangoldt.residueClass
              simp [Set.indicator, hmod8, ArithmeticFunction.vonMangoldt_apply_prime hnp]
            have hft_eq : f_tail n = (1 : ℝ) / n := by
              dsimp [f_tail, f]
              rw [if_pos (by omega), if_pos ⟨hnp, hm8⟩]
            have hlog_le : δ * Real.log n ≤ (n : ℝ) ^ δ := by
              have hl := Real.log_le_rpow_div (Nat.cast_nonneg n) hδ_pos
              exact (le_div_iff₀' hδ_pos).mp hl
            have hrpow_split : (n : ℝ) ^ (1 + δ) = (n : ℝ) * (n : ℝ) ^ δ := by
              rw [Real.rpow_add (by exact_mod_cast hn_pos), Real.rpow_one]
            have hnδ_pos : 0 < (n : ℝ) ^ δ := Real.rpow_pos_of_pos (by exact_mod_cast hn_pos) δ
            have hterm_le : h_ser n ≤ f_tail n := by
              dsimp [h_ser]
              rw [hrc_eq, hrpow_split, hft_eq, mul_div_assoc']
              calc (δ * Real.log n) / ((n : ℝ) * (n : ℝ) ^ δ)
                  ≤ (n : ℝ) ^ δ / ((n : ℝ) * (n : ℝ) ^ δ) := by gcongr
                _ = 1 / (n : ℝ) := by field_simp
            dsimp [h_maj]
            linarith
          · have hrc_eq : ArithmeticFunction.vonMangoldt.residueClass a8 n = 0 := by
              unfold ArithmeticFunction.vonMangoldt.residueClass
              simp [Set.indicator, hmod8]
            have h0 : h_ser n = 0 := by simp [h_ser, hrc_eq]
            rw [h0]
            dsimp [h_maj]
            positivity
        · have hrpow_n : (n : ℝ) ≤ (n : ℝ) ^ (1 + δ) := by
            conv_lhs => rw [← Real.rpow_one (n : ℝ)]
            exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
          have hdiv : ArithmeticFunction.vonMangoldt.residueClass a8 n / (n : ℝ) ^ (1 + δ) ≤
              g_non n := by
            dsimp [g_non]
            rw [if_neg hnp]
            exact div_le_div_of_nonneg_left hrc0 (by exact_mod_cast hn_pos) hrpow_n
          have hmul := mul_le_mul_of_nonneg_left hdiv hδ_pos.le
          dsimp [h_ser, h_maj]
          linarith
  have h_ser_nonneg : ∀ n, 0 ≤ h_ser n := fun n => by
    dsimp [h_ser]
    have hrc0 := ArithmeticFunction.vonMangoldt.residueClass_nonneg a8 n
    positivity
  have htsum_le : (∑' n, h_ser n) ≤ ∑' n, h_maj n :=
    Summable.tsum_le_tsum h_pw (h_maj_sum.of_nonneg_of_le h_ser_nonneg h_pw) h_maj_sum
  have htsum_ser : (∑' n, h_ser n) =
      δ * ∑' n, ArithmeticFunction.vonMangoldt.residueClass a8 n / (n : ℝ) ^ (1 + δ) := by
    dsimp [h_ser]
    exact tsum_mul_left
  have htsum_maj : (∑' n, h_maj n) =
      δ * (∑' n, g_fin n) + δ * (∑' n, g_non n) + ∑' n, f_tail n := by
    have h1 := ((hg_fin_sum.mul_left δ).add (hg_non_sum.mul_left δ)).tsum_add hf_tail_sum
    have h2 := (hg_fin_sum.mul_left δ).tsum_add (hg_non_sum.mul_left δ)
    dsimp [h_maj]
    rw [h1, h2, tsum_mul_left, tsum_mul_left]
  have hLB_scaled : (1 : ℝ) / 4 - δ * C ≤ ∑' n, h_ser n := by
    rw [htsum_ser]
    have hm := mul_le_mul_of_nonneg_left hLB hδ_pos.le
    have hsimp : δ * (((4 : ℕ) : ℝ)⁻¹ / (1 + δ - 1) - C) = (1 : ℝ) / 4 - δ * C := by
      have hsub : 1 + δ - 1 = δ := by ring
      have h4 : ((4 : ℕ) : ℝ)⁻¹ = (1 : ℝ) / 4 := by norm_num
      rw [hsub, h4, mul_sub, mul_div_cancel₀ _ hδ_pos.ne']
    linarith
  have habsC : -|C| ≤ C := neg_abs_le C
  have hδ_bound : δ * (C + (∑' n, g_fin n) + (∑' n, g_non n)) ≤ δ * M_const := by
    apply mul_le_mul_of_nonneg_left _ hδ_pos.le
    dsimp [M_const]
    linarith [le_abs_self C]
  linarith

private lemma exists_large_prime_mod8_sum (P : ℕ) (B_target : ℝ) :
    ∃ y : ℕ, max P (2 ^ 24) ≤ y ∧
      B_target ≤ ∑ p ∈ (Nat.primesLE y).filter (fun p => P < p ∧ p % 8 = 1), (1 : ℝ) / p := by
  set f : ℕ → ℝ := fun n => if n.Prime ∧ n % 8 = 1 then (1 : ℝ) / n else 0
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => by dsimp [f]; split_ifs <;> positivity
  have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf_nonneg).mp
    not_summable_prime_mod8_inv
  rw [Filter.tendsto_atTop_atTop] at htend
  let S_P : ℝ := ∑ n ∈ Finset.range (P + 1), f n
  obtain ⟨N₀, hN₀⟩ := htend (B_target + S_P)
  let y := max N₀ (max P (2 ^ 24))
  have hy_ge : max P (2 ^ 24) ≤ y := le_max_right _ _
  have hPy : P ≤ y := le_trans (le_max_left _ _) hy_ge
  refine ⟨y, hy_ge, ?_⟩
  have hsum_ge : B_target + S_P ≤ ∑ n ∈ Finset.range (y + 1), f n :=
    hN₀ (y + 1) (by omega)
  have hsplit : (∑ n ∈ Finset.range (y + 1), f n) =
      S_P + ∑ n ∈ (Finset.range (y + 1)).filter (P < ·), f n := by
    have hpart := (Finset.sum_filter_add_sum_filter_not (Finset.range (y + 1)) (P < ·) f).symm
    have hnot : (Finset.range (y + 1)).filter (fun n => ¬ P < n) = Finset.range (P + 1) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hpart, hnot, add_comm]
  have heq_sum : (∑ n ∈ (Finset.range (y + 1)).filter (P < ·), f n) =
      ∑ p ∈ (Nat.primesLE y).filter (fun p => P < p ∧ p % 8 = 1), (1 : ℝ) / p := by
    dsimp [f]
    rw [Nat.primesLE_eq_filter_range]
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    tauto
  linarith

private lemma prod_primesLE_one_sub_inv_le (y : ℕ) (hy : 1 ≤ y) :
    ∏ p ∈ Nat.primesLE y, (1 - 1 / (p : ℝ)) ≤ 1 / Real.log (y + 1) := by
  let invHom : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by push_cast; rw [mul_inv] }
  have hnorm : ∀ {p : ℕ}, p.Prime → ‖invHom p‖ < 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  obtain ⟨hsum_norm, hhas⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := invHom) hnorm (y + 1)
  have hsum : Summable (fun m : (y + 1).smoothNumbers => (m.1 : ℝ)⁻¹) := by
    refine hsum_norm.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    change (m.1 : ℝ)⁻¹ ≤ ‖(m.1 : ℝ)⁻¹‖
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  let emb : {m // m ∈ Finset.Icc 1 y} ↪ (y + 1).smoothNumbers :=
    { toFun := fun m => ⟨m.1, Nat.mem_smoothNumbers'.mpr (fun p _ hpm => by
        have hm := Finset.mem_Icc.mp m.2
        have hle := Nat.le_of_dvd (by omega) hpm
        omega)⟩
      inj' := fun a b hab =>
        Subtype.ext (congr_arg (fun x : (y + 1).smoothNumbers => x.1) hab) }
  have hharm_le : (harmonic y : ℝ) ≤ ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹)⁻¹ := by
    have hle_tsum := Summable.sum_le_tsum ((Finset.Icc 1 y).attach.map emb)
      (fun _ _ => by positivity) hsum
    have hmap : (∑ m ∈ (Finset.Icc 1 y).attach.map emb, (m.1 : ℝ)⁻¹) = (harmonic y : ℝ) := by
      rw [Finset.sum_map]
      change (∑ x ∈ (Finset.Icc 1 y).attach, (x.1 : ℝ)⁻¹) = (harmonic y : ℝ)
      rw [Finset.sum_attach (Finset.Icc 1 y) (fun m : ℕ => (m : ℝ)⁻¹), harmonic_eq_sum_Icc]
      simp
    have hpb_eq : (y + 1).primesBelow = Nat.primesLE y := by
      ext p
      simp only [Nat.mem_primesBelow, Nat.mem_primesLE]
      constructor
      · rintro ⟨hlt, hp⟩; exact ⟨by omega, hp⟩
      · rintro ⟨hle, hp⟩; exact ⟨by omega, hp⟩
    have htsum_eq : (∑' m : (y + 1).smoothNumbers, (m.1 : ℝ)⁻¹) =
        ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹)⁻¹ := by
      have h1 := hhas.tsum_eq
      rw [hpb_eq] at h1
      exact h1
    rw [hmap, htsum_eq] at hle_tsum
    exact hle_tsum
  have hlog_le : Real.log ((y + 1 : ℕ) : ℝ) ≤ ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹)⁻¹ :=
    (log_add_one_le_harmonic y).trans hharm_le
  push_cast at hlog_le
  have hprod_pos : 0 < ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹) := by
    refine Finset.prod_pos fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have hinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  have hlog_pos : 0 < Real.log ((y : ℝ) + 1) := by
    apply Real.log_pos
    have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
    linarith
  rw [Finset.prod_inv_distrib] at hlog_le
  have hinv_le := (le_inv_comm₀ hlog_pos hprod_pos).mp hlog_le
  simpa [one_div] using hinv_le

private lemma prod_one_add_ge_one_add_sum (S : Finset ℕ) (g : ℕ → ℝ) (hg : ∀ x ∈ S, 0 ≤ g x) :
    1 + ∑ x ∈ S, g x ≤ ∏ x ∈ S, (1 + g x) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ha0 : 0 ≤ g a := hg a (Finset.mem_insert_self a s)
    have hs0 : 0 ≤ ∑ x ∈ s, g x :=
      Finset.sum_nonneg (fun x hx => hg x (Finset.mem_insert_of_mem hx))
    have hih := ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))
    have hmul : (1 + g a) * (1 + ∑ x ∈ s, g x) ≤ (1 + g a) * ∏ x ∈ s, (1 + g x) :=
      mul_le_mul_of_nonneg_left hih (by linarith)
    have hexp : 1 + (g a + ∑ x ∈ s, g x) ≤ (1 + g a) * (1 + ∑ x ∈ s, g x) := by nlinarith
    exact hexp.trans hmul

private lemma prod_periodTwo_le_of_large_sum {P y : ℕ} (hP : 8 ≤ P) (hPy : P ≤ y)
    (hy1 : 1 ≤ y)
    (hsum : 68 / (∏ p ∈ Nat.primesLE P, (1 - 1 / (p : ℝ))) ≤
      ∑ p ∈ (Nat.primesLE y).filter (fun p => P < p ∧ p % 8 = 1), (1 : ℝ) / p) :
    ∏ p ∈ (Nat.primesLE y).filter (P < ·), (1 - 1 / (periodTwo p : ℝ)) ≤
      1 / (68 * Real.log ((y : ℝ) + 1)) := by
  set F := (Nat.primesLE y).filter (P < ·)
  set F₁ := (Nat.primesLE y).filter (fun p => P < p ∧ p % 8 = 1)
  set c_P : ℝ := ∏ p ∈ Nat.primesLE P, (1 - 1 / (p : ℝ))
  have hcP_pos : 0 < c_P := by
    refine Finset.prod_pos fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have hinv : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hsplit_P : c_P * (∏ p ∈ F, (1 - 1 / (p : ℝ))) =
      ∏ p ∈ Nat.primesLE y, (1 - 1 / (p : ℝ)) := by
    have hpart := (Finset.prod_filter_mul_prod_filter_not (Nat.primesLE y) (P < ·)
      (fun p => 1 - 1 / (p : ℝ))).symm
    have hnot : (Nat.primesLE y).filter (fun p => ¬ P < p) = Nat.primesLE P := by
      ext p
      simp only [Finset.mem_filter, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨_, hp⟩, h⟩; exact ⟨by omega, hp⟩
      · rintro ⟨hle, hp⟩; exact ⟨⟨by omega, hp⟩, by omega⟩
    rw [hpart, hnot, mul_comm]
  have hF_prod_le : (∏ p ∈ F, (1 - 1 / (p : ℝ))) ≤ (1 / c_P) / Real.log ((y : ℝ) + 1) := by
    have heul := prod_primesLE_one_sub_inv_le y hy1
    rw [← hsplit_P] at heul
    rw [div_div, mul_comm c_P]
    have hlog_pos : 0 < Real.log ((y : ℝ) + 1) :=
      Real.log_pos (by norm_cast; omega)
    rw [le_div_iff₀ (mul_pos hlog_pos hcP_pos)]
    have h1 := (le_div_iff₀ hlog_pos).mp heul
    linarith
  have hterm : ∀ p ∈ F, 1 - 1 / (periodTwo p : ℝ) ≤
      (1 - 1 / (p : ℝ)) * (if p % 8 = 1 then 1 / (1 + 1 / (p : ℝ)) else 1) := by
    intro p hp
    have hp_mem := Finset.mem_filter.mp hp
    have hp_prime := Nat.prime_of_mem_primesLE hp_mem.1
    have hp_gt8 : 8 < p := by omega
    have hpR : (9 : ℝ) ≤ p := by exact_mod_cast hp_gt8
    unfold periodTwo
    split_ifs with h8
    · have hp_odd : p % 2 = 1 := hp_prime.eq_two_or_odd.resolve_left (by omega)
      have hd_cast : (((p - 1) / 2 : ℕ) : ℝ) = ((p : ℝ) - 1) / 2 := by
        have h2d : 2 * ((p - 1) / 2) + 1 = p := by omega
        have h2dR : (2 : ℝ) * (((p - 1) / 2 : ℕ) : ℝ) + 1 = p := by exact_mod_cast h2d
        linarith
      rw [hd_cast]
      have hpos1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hpos2 : (0 : ℝ) < (p : ℝ) + 1 := by linarith
      have hposp : (0 : ℝ) < p := by linarith
      have hpos_ip : (0 : ℝ) < 1 + 1 / (p : ℝ) := by positivity
      have lhs_eq : 1 - 1 / (((p : ℝ) - 1) / 2) = ((p : ℝ) - 3) / ((p : ℝ) - 1) := by
        field_simp
        ring
      have rhs_eq : (1 - 1 / (p : ℝ)) * (1 / (1 + 1 / (p : ℝ))) =
          ((p : ℝ) - 1) / ((p : ℝ) + 1) := by
        field_simp
      rw [lhs_eq, rhs_eq, div_le_div_iff₀ hpos1 hpos2]
      nlinarith
    · rw [mul_one, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
      have h1 : 1 / (p : ℝ) ≤ 1 / ((p : ℝ) - 1) :=
        one_div_le_one_div_of_le (by linarith) (by linarith)
      linarith
  have hprod_step : (∏ p ∈ F, (1 - 1 / (periodTwo p : ℝ))) ≤
      (∏ p ∈ F, (1 - 1 / (p : ℝ))) * ∏ p ∈ F₁, (1 / (1 + 1 / (p : ℝ))) := by
    calc (∏ p ∈ F, (1 - 1 / (periodTwo p : ℝ)))
        ≤ ∏ p ∈ F, ((1 - 1 / (p : ℝ)) * (if p % 8 = 1 then 1 / (1 + 1 / (p : ℝ)) else 1)) := by
          refine Finset.prod_le_prod (fun p hp => ?_) hterm
          have hp_gt8 : 8 < p := by have := (Finset.mem_filter.mp hp).2; omega
          have hd_ge2 : (2 : ℝ) ≤ periodTwo p := by
            unfold periodTwo; split_ifs <;> exact_mod_cast (show 2 ≤ _ by omega)
          have hinv : 1 / (periodTwo p : ℝ) ≤ 1 := by
            rw [div_le_one (by linarith)]; linarith
          linarith
      _ = (∏ p ∈ F, (1 - 1 / (p : ℝ))) *
            ∏ p ∈ F, (if p % 8 = 1 then 1 / (1 + 1 / (p : ℝ)) else 1) := Finset.prod_mul_distrib
      _ = (∏ p ∈ F, (1 - 1 / (p : ℝ))) * ∏ p ∈ F₁, (1 / (1 + 1 / (p : ℝ))) := by
          congr 1
          rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
          congr 1
          ext p
          simp only [F, F₁, Finset.mem_filter]
          tauto
  have hF₁_prod_le : (∏ p ∈ F₁, (1 / (1 + 1 / (p : ℝ)))) ≤ c_P / 68 := by
    have hge := prod_one_add_ge_one_add_sum F₁ (fun p => 1 / (p : ℝ)) (fun p _ => by positivity)
    have hprod_pos : 0 < ∏ p ∈ F₁, (1 + 1 / (p : ℝ)) :=
      Finset.prod_pos (fun p _ => by positivity)
    have hsum_pos : 0 < 68 / c_P := by positivity
    have h1 : 68 / c_P ≤ ∏ p ∈ F₁, (1 + 1 / (p : ℝ)) := by linarith
    have hinv : (∏ p ∈ F₁, (1 + 1 / (p : ℝ)))⁻¹ ≤ (68 / c_P)⁻¹ :=
      inv_anti₀ hsum_pos h1
    have hlhs : (∏ p ∈ F₁, (1 / (1 + 1 / (p : ℝ)))) = (∏ p ∈ F₁, (1 + 1 / (p : ℝ)))⁻¹ := by
      simp_rw [one_div, Finset.prod_inv_distrib]
    rw [inv_div] at hinv
    rw [hlhs]
    exact hinv
  have hF_nonneg : 0 ≤ ∏ p ∈ F, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).two_le
    have hinv : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hlog_pos : 0 < Real.log ((y : ℝ) + 1) :=
    Real.log_pos (by norm_cast; omega)
  calc (∏ p ∈ F, (1 - 1 / (periodTwo p : ℝ)))
      ≤ (∏ p ∈ F, (1 - 1 / (p : ℝ))) * ∏ p ∈ F₁, (1 / (1 + 1 / (p : ℝ))) := hprod_step
    _ ≤ ((1 / c_P) / Real.log ((y : ℝ) + 1)) * (c_P / 68) :=
        mul_le_mul hF_prod_le hF₁_prod_le (Finset.prod_nonneg fun _ _ => by positivity)
          (by positivity)
    _ = 1 / (68 * Real.log ((y : ℝ) + 1)) := by field_simp

private lemma card_primes_y_to_4y_ge {y : ℕ} (hy : 2 ^ 24 ≤ y) :
    (y : ℝ) / (4 * Real.log ((y : ℝ) + 1)) ≤
      (((Nat.primesLE (4 * y)).filter (y < ·)).card : ℝ) := by
  set Q := (Nat.primesLE (4 * y)).filter (y < ·)
  have hy_pos : (0 : ℝ) < y := by
    have : 0 < 2 ^ 24 := by norm_num
    exact_mod_cast (lt_of_lt_of_le this hy)
  have hth_ge := Chebyshev.theta_ge (4 * y)
  have hth_le := Chebyshev.theta_le_log4_mul_x (x := (y : ℝ)) hy_pos.le
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog2_gt := Real.log_two_gt_d9
  set u : ℝ := ((4 * y : ℕ) : ℝ) ^ (1 / 4 : ℝ)
  have hu_pos : 0 < u := Real.rpow_pos_of_pos (by positivity) _
  have hu_ge64 : 64 ≤ u := by
    have h4y : (64 : ℝ) ^ 4 ≤ ((4 * y : ℕ) : ℝ) := by
      have hnat : 64 ^ 4 ≤ 4 * y := by omega
      exact_mod_cast hnat
    calc (64 : ℝ) = ((64 : ℝ) ^ 4) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ u := Real.rpow_le_rpow (by positivity) h4y (by norm_num)
  have hu4 : u ^ 4 = 4 * (y : ℝ) := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hu2 : u ^ 2 = Real.sqrt ((4 * y : ℕ) : ℝ) := by
    dsimp [u]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hlog4y_le : Real.log ((4 * y : ℕ) : ℝ) ≤ 4 * u := by
    have hl := Real.log_le_rpow_div (Nat.cast_nonneg (4 * y)) (by norm_num : (0 : ℝ) < 1 / 4)
    dsimp [u]
    linarith
  have hlog4y1_le : Real.log (((4 * y : ℕ) : ℝ) + 1) ≤ 1 + 4 * u := by
    have hle8 : ((4 * y : ℕ) : ℝ) + 1 ≤ 2 * ((4 * y : ℕ) : ℝ) := by
      have hy1R : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
      push_cast
      linarith
    have hl := Real.log_le_log (by positivity) hle8
    rw [Real.log_mul (by norm_num) (by positivity)] at hl
    have hl2 := Real.log_two_lt_d9
    linarith
  have hdiff_ge : (y : ℝ) / 2 ≤ Chebyshev.theta ((4 * y : ℕ) : ℝ) - Chebyshev.theta (y : ℝ) := by
    rw [← hu2] at hth_ge
    push_cast at hth_ge hlog4y_le hlog4y1_le hu4 ⊢
    rw [hlog4] at hth_le
    have hpoly : 1 + 4 * u + 2 * u ^ 2 * (4 * u) ≤ 9 * u ^ 3 := by nlinarith
    have hu3_le : 9 * u ^ 3 ≤ (9 / 64) * u ^ 4 := by nlinarith
    have herr : Real.log (4 * (y : ℝ) + 1) + 2 * u ^ 2 * Real.log (4 * (y : ℝ)) ≤
        (9 / 16) * (y : ℝ) := by
      have hnonneg : 0 ≤ u ^ 2 := sq_nonneg u
      nlinarith
    have hlog2_y : (11 / 8) * (y : ℝ) ≤ 2 * Real.log 2 * (y : ℝ) := by nlinarith [hlog2_gt, hy_pos]
    nlinarith [hth_ge, hth_le, herr, hlog2_y]
  have htheta_diff : Chebyshev.theta ((4 * y : ℕ) : ℝ) - Chebyshev.theta (y : ℝ) ≤
      (Q.card : ℝ) * Real.log ((4 * y : ℕ) : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log (4 * y), Chebyshev.theta_eq_sum_primesLE_log y]
    have hpart := (Finset.sum_filter_add_sum_filter_not (Nat.primesLE (4 * y)) (y < ·)
      (fun p : ℕ => Real.log p)).symm
    have hnot : (Nat.primesLE (4 * y)).filter (fun p => ¬ y < p) = Nat.primesLE y := by
      ext p
      simp only [Finset.mem_filter, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨_, hp⟩, h⟩; exact ⟨by omega, hp⟩
      · rintro ⟨hle, hp⟩; exact ⟨⟨by omega, hp⟩, by omega⟩
    rw [hpart, hnot, add_sub_cancel_right]
    calc (∑ p ∈ Q, Real.log (p : ℝ))
        ≤ ∑ _p ∈ Q, Real.log ((4 * y : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp_mem := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
          exact Real.log_le_log (by exact_mod_cast hp_mem.2.pos) (by exact_mod_cast hp_mem.1)
      _ = (Q.card : ℝ) * Real.log ((4 * y : ℕ) : ℝ) := by simp
  have hlog4y_le_2log : Real.log ((4 * y : ℕ) : ℝ) ≤ 2 * Real.log ((y : ℝ) + 1) := by
    have hsq : ((4 * y : ℕ) : ℝ) ≤ ((y : ℝ) + 1) ^ 2 := by
      have hnat : 4 * y ≤ (y + 1) ^ 2 := by
        have h4 : 4 * y ≤ y * y := Nat.mul_le_mul_right y (by omega)
        have hexp : (y + 1) ^ 2 = y * y + 2 * y + 1 := by ring
        omega
      exact_mod_cast hnat
    calc Real.log ((4 * y : ℕ) : ℝ) ≤ Real.log (((y : ℝ) + 1) ^ 2) :=
          Real.log_le_log (by positivity) hsq
      _ = 2 * Real.log ((y : ℝ) + 1) := by rw [Real.log_pow]; norm_num
  have hlog_pos : 0 < Real.log ((y : ℝ) + 1) := Real.log_pos (by linarith)
  have h1 : (y : ℝ) / 2 ≤ (Q.card : ℝ) * (2 * Real.log ((y : ℝ) + 1)) := by
    have hcard0 : (0 : ℝ) ≤ Q.card := Nat.cast_nonneg _
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  linarith

private lemma greedy_sieve_step (T : Finset ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ a : ℕ, ((T.filter (fun x => x % m ≠ a)).card : ℝ) ≤ (T.card : ℝ) * (1 - 1 / (m : ℝ)) ∧
      ∀ x ∈ T, x ∉ T.filter (fun x => x % m ≠ a) → x % m = a % m := by
  have hsum_nat : (∑ a ∈ Finset.range m, (T.filter (fun x => x % m = a)).card) = T.card :=
    (Finset.card_eq_sum_card_fiberwise
      (fun x _ => Finset.mem_range.mpr (Nat.mod_lt x hm))).symm
  have hex : ∃ a ∈ Finset.range m,
      (T.card : ℝ) / m ≤ ((T.filter (fun x => x % m = a)).card : ℝ) := by
    by_contra hall
    have hall' : ∀ a ∈ Finset.range m,
        ((T.filter (fun x => x % m = a)).card : ℝ) < (T.card : ℝ) / m :=
      fun a ha => lt_of_not_ge fun hge => hall ⟨a, ha, hge⟩
    have hsum_lt : (∑ a ∈ Finset.range m, ((T.filter (fun x => x % m = a)).card : ℝ)) <
        ∑ _a ∈ Finset.range m, (T.card : ℝ) / m :=
      Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hm.ne') hall'
    have hlhs : (∑ a ∈ Finset.range m, ((T.filter (fun x => x % m = a)).card : ℝ)) = T.card := by
      exact_mod_cast hsum_nat
    have hrhs : (∑ _a ∈ Finset.range m, (T.card : ℝ) / m) = T.card := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp
    linarith
  obtain ⟨a, ha_mem, ha_ge⟩ := hex
  have ha_lt : a < m := Finset.mem_range.mp ha_mem
  refine ⟨a, ?_, ?_⟩
  · have hpart : (T.filter (fun x => x % m = a)).card +
        (T.filter (fun x => x % m ≠ a)).card = T.card := by
      simpa using Finset.sum_filter_add_sum_filter_not T (fun x => x % m = a) (fun _ => (1 : ℕ))
    have hpartR : ((T.filter (fun x => x % m = a)).card : ℝ) +
        ((T.filter (fun x => x % m ≠ a)).card : ℝ) = (T.card : ℝ) := by
      exact_mod_cast hpart
    have hrhs : (T.card : ℝ) * (1 - 1 / (m : ℝ)) = (T.card : ℝ) - (T.card : ℝ) / m := by ring
    linarith
  · intro x hx hx_not
    rw [Nat.mod_eq_of_lt ha_lt]
    by_contra hne
    exact hx_not (Finset.mem_filter.mpr ⟨hx, hne⟩)

private lemma greedy_sieve_finset (r : ℕ) (F : Finset ℕ) (hF : ∀ p ∈ F, 8 < p) :
    ∃ (a : ℕ → ℕ) (S_rem : Finset ℕ),
      (S_rem.card : ℝ) ≤ (r : ℝ) * (∏ p ∈ F, (1 - 1 / (periodTwo p : ℝ))) ∧
      ∀ x ∈ Finset.range r, x ∉ S_rem → ∃ p ∈ F, x % periodTwo p = (a p) % periodTwo p := by
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, Finset.range r, ?_, ?_⟩
    · simp
    · intro x hx hnot
      exact absurd hx hnot
  | insert q s hqs ih =>
    have hq8 : 8 < q := hF q (Finset.mem_insert_self q s)
    obtain ⟨a_s, S_s, hcard_s, hcov_s⟩ :=
      ih (fun p hp => hF p (Finset.mem_insert_of_mem hp))
    obtain ⟨a_q, hcard_q, hcov_q⟩ := greedy_sieve_step S_s (periodTwo_pos hq8)
    let a' : ℕ → ℕ := fun p => if p = q then a_q else a_s p
    let S' := S_s.filter (fun x => x % periodTwo q ≠ a_q)
    refine ⟨a', S', ?_, ?_⟩
    · rw [Finset.prod_insert hqs, ← mul_assoc, mul_comm (r : ℝ) (1 - 1 / (periodTwo q : ℝ)),
        mul_assoc, mul_comm (1 - 1 / (periodTwo q : ℝ))]
      have h1_nonneg : 0 ≤ 1 - 1 / (periodTwo q : ℝ) := by
        have hd_pos : (1 : ℝ) ≤ periodTwo q := by exact_mod_cast periodTwo_pos hq8
        have hinv : 1 / (periodTwo q : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        linarith
      exact hcard_q.trans (mul_le_mul_of_nonneg_right hcard_s h1_nonneg)
    · intro x hx hx_not
      by_cases hx_Ss : x ∈ S_s
      · refine ⟨q, Finset.mem_insert_self q s, ?_⟩
        dsimp [a']
        rw [if_pos rfl]
        exact hcov_q x hx_Ss hx_not
      · obtain ⟨p, hp_s, hp_mod⟩ := hcov_s x hx hx_Ss
        refine ⟨p, Finset.mem_insert_of_mem hp_s, ?_⟩
        have hp_ne_q : p ≠ q := fun heq => hqs (heq ▸ hp_s)
        dsimp [a']
        rw [if_neg hp_ne_q]
        exact hp_mod

private lemma exists_surj_on_finset (A B : Finset ℕ) (hcard : A.card ≤ B.card) :
    ∃ g : ℕ → ℕ, ∀ x ∈ A, ∃ q ∈ B, g q = x := by
  induction A using Finset.induction_on generalizing B with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert x s hxs ih =>
    rw [Finset.card_insert_of_notMem hxs] at hcard
    have hne : B.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨b₀, hb₀⟩ := hne
    have hcard' : s.card ≤ (B.erase b₀).card := by
      rw [Finset.card_erase_of_mem hb₀]
      omega
    obtain ⟨g', hg'⟩ := ih (B.erase b₀) hcard'
    refine ⟨fun q => if q = b₀ then x else g' q, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hys
    · exact ⟨b₀, hb₀, by simp⟩
    · obtain ⟨q, hqB', hgeq⟩ := hg' y hys
      have hq_ne : q ≠ b₀ := (Finset.mem_erase.mp hqB').1
      have hqB : q ∈ B := (Finset.mem_erase.mp hqB').2
      exact ⟨q, hqB, by simp [hq_ne, hgeq]⟩

private lemma crt_odd_prime_squares (U : Finset ℕ)
    (hU : ∀ p ∈ U, p.Prime ∧ 2 < p) (c : ℕ → ℕ) :
    ∃ n₀ : ℕ, n₀ % 2 = 1 ∧ ∀ p ∈ U, n₀ ≡ c p [MOD p ^ 2] := by
  induction U using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | insert q s hqs ih =>
    obtain ⟨hq_prime, hq_gt2⟩ := hU q (Finset.mem_insert_self q s)
    have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := fun p hp => hU p (Finset.mem_insert_of_mem hp)
    obtain ⟨n₁, hn₁_odd, hn₁_mod⟩ := ih hs
    let M_s := 2 * ∏ p ∈ s, p ^ 2
    have hcop_q_Ms : Nat.Coprime (q ^ 2) M_s := by
      refine Nat.Coprime.pow_left 2 ?_
      refine Nat.Coprime.mul_right ?_ ?_
      · exact (hq_prime.coprime_iff_not_dvd).mpr
          (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega)
      · refine Nat.coprime_prod_right_iff.mpr fun p hp => ?_
        have hp_prime := (hs p hp).1
        have hqp_ne : q ≠ p := fun heq => hqs (heq ▸ hp)
        exact ((Nat.coprime_primes hq_prime hp_prime).mpr hqp_ne).pow_right 2
    let sol := Nat.chineseRemainder hcop_q_Ms (c q) n₁
    refine ⟨sol.1, ?_, ?_⟩
    · have hmod2 : sol.1 ≡ n₁ [MOD 2] := sol.2.2.of_dvd ⟨∏ p ∈ s, p ^ 2, rfl⟩
      rw [Nat.ModEq] at hmod2
      omega
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hps
      · exact sol.2.1
      · have hdvd : p ^ 2 ∣ M_s :=
          dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun x => x ^ 2) hps) 2
        exact (sol.2.2.of_dvd hdvd).trans (hn₁_mod p hps)

theorem prove_erdos11_gs : type_of% @Erdos11.erdos_11.variants.granville_soundararajan := by
  intro H
  by_contra hnot_inf
  have hfin : {p : ℕ | p.Prime ∧ ¬ 2 ^ p ≡ 2 [MOD p ^ 2]}.Finite :=
    Set.not_infinite.mp hnot_inf
  obtain ⟨P₀, hP₀⟩ := hfin.bddAbove
  let P := max P₀ 8
  have hP8 : 8 ≤ P := le_max_right _ _
  have hwief_gt : ∀ p : ℕ, p.Prime → P < p → 2 ^ p ≡ 2 [MOD p ^ 2] := by
    intro p hp hgt
    by_contra hnw
    have hle : p ≤ P₀ := hP₀ ⟨hp, hnw⟩
    omega
  let c_P : ℝ := ∏ p ∈ Nat.primesLE P, (1 - 1 / (p : ℝ))
  obtain ⟨y, hy_ge, hsum_mod8⟩ := exists_large_prime_mod8_sum P (68 / c_P)
  have hPy : P ≤ y := le_trans (le_max_left _ _) hy_ge
  have hy24 : 2 ^ 24 ≤ y := le_trans (le_max_right _ _) hy_ge
  have hy1 : 1 ≤ y := by
    have : 1 ≤ 2 ^ 24 := by norm_num
    omega
  let F := (Nat.primesLE y).filter (P < ·)
  let Q := (Nat.primesLE (4 * y)).filter (y < ·)
  let r := 16 * y + 2
  have hF_gt8 : ∀ p ∈ F, 8 < p := fun p hp => by
    have := (Finset.mem_filter.mp hp).2
    omega
  obtain ⟨a_F, S_rem, hS_card, hS_cov⟩ := greedy_sieve_finset r F hF_gt8
  have hprod_F := prod_periodTwo_le_of_large_sum hP8 hPy hy1 hsum_mod8
  have hQ_card := card_primes_y_to_4y_ge hy24
  have hS_le_Q : S_rem.card ≤ Q.card := by
    have hlog_pos : 0 < Real.log ((y : ℝ) + 1) :=
      Real.log_pos (by norm_cast; omega)
    have hrR : (r : ℝ) ≤ 17 * (y : ℝ) := by
      dsimp [r]
      push_cast
      have : (2 : ℝ) ≤ y := by
        have : 2 ≤ 2 ^ 24 := by norm_num
        exact_mod_cast (le_trans this hy24)
      linarith
    have hprod_nonneg : 0 ≤ ∏ p ∈ F, (1 - 1 / (periodTwo p : ℝ)) := by
      refine Finset.prod_nonneg fun p hp => ?_
      have hp8 := hF_gt8 p hp
      have hd1 : (1 : ℝ) ≤ periodTwo p := by exact_mod_cast periodTwo_pos hp8
      have hinv : 1 / (periodTwo p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    have hreal_le : (S_rem.card : ℝ) ≤ (Q.card : ℝ) := by
      calc (S_rem.card : ℝ)
          ≤ (r : ℝ) * ∏ p ∈ F, (1 - 1 / (periodTwo p : ℝ)) := hS_card
        _ ≤ (17 * (y : ℝ)) * (1 / (68 * Real.log ((y : ℝ) + 1))) :=
            mul_le_mul hrR hprod_F hprod_nonneg (by positivity)
        _ = (y : ℝ) / (4 * Real.log ((y : ℝ) + 1)) := by field_simp; ring
        _ ≤ (Q.card : ℝ) := hQ_card
    exact_mod_cast hreal_le
  obtain ⟨g_Q, hg_Q⟩ := exists_surj_on_finset S_rem Q hS_le_Q
  let U := F ∪ Q
  let a_all : ℕ → ℕ := fun p => if p ≤ y then a_F p else g_Q p
  have hU_primes : ∀ p ∈ U, p.Prime ∧ P < p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpF | hpQ
    · have hm := Finset.mem_filter.mp hpF
      exact ⟨Nat.prime_of_mem_primesLE hm.1, hm.2⟩
    · have hm := Finset.mem_filter.mp hpQ
      exact ⟨Nat.prime_of_mem_primesLE hm.1, lt_of_le_of_lt hPy hm.2⟩
  have hU_odd : ∀ p ∈ U, p.Prime ∧ 2 < p := fun p hp => by
    obtain ⟨hp1, hp2⟩ := hU_primes p hp
    exact ⟨hp1, by omega⟩
  obtain ⟨n₀, hn₀_odd, hn₀_mod⟩ := crt_odd_prime_squares U hU_odd (fun p => 2 ^ (a_all p))
  let M := ∏ p ∈ U, p ^ 2
  have hM_pos : 0 < M := Finset.prod_pos fun p hp => pow_pos (hU_primes p hp).1.pos 2
  have h2M_pos : 0 < 2 * M := by omega
  let n := n₀ % (2 * M) + 2 * M
  have hn_odd : Odd n := by
    have hmod_2M : (n₀ % (2 * M)) % 2 = n₀ % 2 := Nat.mod_mod_of_dvd n₀ ⟨M, rfl⟩
    have hn_mod2 : n % 2 = 1 := by
      dsimp [n]
      omega
    exact Nat.odd_iff.mpr hn_mod2
  have hn_gt1 : 1 < n := by
    dsimp [n]
    omega
  have hn_lt_4M : n < 4 * M := by
    have hlt := Nat.mod_lt n₀ h2M_pos
    dsimp [n]
    omega
  have h4M_le_2r : 4 * M ≤ 2 ^ r := by
    have hU_sub : U ⊆ (Finset.range (4 * y + 1)).filter Nat.Prime := by
      intro p hp
      rw [← Nat.primesLE_eq_filter_range]
      rcases Finset.mem_union.mp hp with hpF | hpQ
      · exact Nat.primesLE_mono (by omega) (Finset.mem_filter.mp hpF).1
      · exact (Finset.mem_filter.mp hpQ).1
    have hprod_le : (∏ p ∈ U, p) ≤ 4 ^ (4 * y) := by
      calc (∏ p ∈ U, p)
          ≤ ∏ p ∈ (Finset.range (4 * y + 1)).filter Nat.Prime, p :=
            Finset.prod_le_prod_of_subset_of_one_le' hU_sub
              (fun _ hp _ => (Finset.mem_filter.mp hp).2.one_le)
        _ = primorial (4 * y) := rfl
        _ ≤ 4 ^ (4 * y) := primorial_le_four_pow (4 * y)
    have hM_eq : M = (∏ p ∈ U, p) ^ 2 := Finset.prod_pow U 2 (fun p => p)
    calc 4 * M = 4 * (∏ p ∈ U, p) ^ 2 := by rw [hM_eq]
      _ ≤ 4 * (4 ^ (4 * y)) ^ 2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hprod_le 2)
      _ = 2 ^ (16 * y + 2) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add]
          congr 1
          ring
      _ = 2 ^ r := rfl
  obtain ⟨k_sqf, l, hsqf, hn_eq⟩ := H n hn_odd hn_gt1
  have hl_lt_r : l < r := by
    have h2l_lt : 2 ^ l < 2 ^ r := by omega
    by_contra hge
    have hle : 2 ^ r ≤ 2 ^ l := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hcov_all : ∃ p ∈ U, l % periodTwo p = (a_all p) % periodTwo p := by
    by_cases hl_S : l ∈ S_rem
    · obtain ⟨q, hqQ, hgeq⟩ := hg_Q l hl_S
      refine ⟨q, Finset.mem_union_right F hqQ, ?_⟩
      have hqy : ¬ q ≤ y := by
        have hm := (Finset.mem_filter.mp hqQ).2
        omega
      dsimp [a_all]
      rw [if_neg hqy, hgeq]
    · obtain ⟨p, hpF, hp_mod⟩ := hS_cov l (Finset.mem_range.mpr hl_lt_r) hl_S
      refine ⟨p, Finset.mem_union_left Q hpF, ?_⟩
      have hpy : p ≤ y := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hpF).1).1
      dsimp [a_all]
      rw [if_pos hpy]
      exact hp_mod
  obtain ⟨p, hpU, hp_l_mod⟩ := hcov_all
  obtain ⟨hp_prime, hp_gt_P⟩ := hU_primes p hpU
  have hp2_dvd_M : p ^ 2 ∣ M := Finset.dvd_prod_of_mem (fun x => x ^ 2) hpU
  have hp2_dvd_2M : p ^ 2 ∣ 2 * M := dvd_mul_of_dvd_right hp2_dvd_M 2
  have hn_mod_p2 : n ≡ 2 ^ (a_all p) [MOD p ^ 2] := by
    have hrem_eq : (n₀ % (2 * M)) % p ^ 2 = n₀ % p ^ 2 :=
      Nat.mod_mod_of_dvd n₀ hp2_dvd_2M
    have hn_n0 : n ≡ n₀ [MOD p ^ 2] := by
      change (n₀ % (2 * M) + 2 * M) % p ^ 2 = n₀ % p ^ 2
      rw [Nat.add_mod, hrem_eq, Nat.mod_eq_zero_of_dvd hp2_dvd_2M, add_zero, Nat.mod_mod]
    exact hn_n0.trans (hn₀_mod p hpU)
  have h2l_mod_p2 : 2 ^ l ≡ 2 ^ (a_all p) [MOD p ^ 2] :=
    pow_two_modEq_of_mod_eq hp_prime (by omega) (hwief_gt p hp_prime hp_gt_P) hp_l_mod
  have hk_mod_p2 : k_sqf ≡ 0 [MOD p ^ 2] := by
    apply Nat.ModEq.add_right_cancel' (2 ^ l)
    rw [zero_add, ← hn_eq]
    exact hn_mod_p2.trans h2l_mod_p2.symm
  have hp2_dvd_k : p * p ∣ k_sqf := by
    rw [← sq]
    exact (Nat.modEq_zero_iff_dvd).mp hk_mod_p2
  exact hp_prime.ne_one (Nat.isUnit_iff.mp (hsqf p hp2_dvd_k))

theorem OMA.solution : type_of% @Erdos11.erdos_11.variants.granville_soundararajan :=
  prove_erdos11_gs
