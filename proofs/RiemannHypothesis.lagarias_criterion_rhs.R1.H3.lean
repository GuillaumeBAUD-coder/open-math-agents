import OMAReductions.R_RiemannHypothesis_lagarias_criterion_rhs_R1
import Mathlib

-- Step RiemannHypothesis.lagarias_criterion_rhs.R1.H3: hypothesis H3 of reduction RiemannHypothesis.lagarias_criterion_rhs.R1
-- Credit: @hadijannat
-- H3 := ∀ n : ℕ, 1 < n → n ≤ 5040 → σ 1 n < harmonic n + exp (harmonic n) * log (harmonic n)

namespace LagariasH3

open Real Finset Filter
open scoped ArithmeticFunction.sigma Topology

private noncomputable def trapSeq (m : ℕ) : ℝ :=
  (harmonic m : ℝ) - 1 / (2 * (m : ℝ)) - Real.log (m : ℝ)

private lemma trapSeq_lt_succ {m : ℕ} (hm : 1 ≤ m) : trapSeq m < trapSeq (m + 1) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hmpos : 0 < (m : ℝ) := by positivity
  have hm1pos : 0 < (m : ℝ) + 1 := by positivity
  let x : ℝ := 1 / (m : ℝ) + 1 / ((m : ℝ) + 1)
  have hx : 0 ≤ x := by positivity
  have hsum_le : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
    have h4 := Real.sum_le_exp_of_nonneg hx 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      Nat.factorial_zero, Nat.factorial_one, Nat.factorial_succ, Nat.cast_one, Nat.cast_mul,
      Nat.cast_ofNat, div_one] at h4
    linarith
  have hid : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 - (((m : ℝ) + 1) / (m : ℝ)) ^ 2 =
      ((2 * (m : ℝ) + 1) * ((m : ℝ) ^ 2 + (m : ℝ) + 1)) /
        (6 * (m : ℝ) ^ 3 * ((m : ℝ) + 1) ^ 3) := by
    dsimp only [x]
    field_simp
    ring
  have hpos : 0 < ((2 * (m : ℝ) + 1) * ((m : ℝ) ^ 2 + (m : ℝ) + 1)) /
      (6 * (m : ℝ) ^ 3 * ((m : ℝ) + 1) ^ 3) := by positivity
  have hlt_exp : (((m : ℝ) + 1) / (m : ℝ)) ^ 2 < Real.exp x := by linarith
  have hdiv_pos : 0 < ((m : ℝ) + 1) / (m : ℝ) := by positivity
  have hlog : Real.log (((m : ℝ) + 1) / (m : ℝ)) < x / 2 := by
    have h1 : Real.log ((((m : ℝ) + 1) / (m : ℝ)) ^ 2) < x :=
      (Real.log_lt_iff_lt_exp (sq_pos_of_pos hdiv_pos)).mpr hlt_exp
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hdiff : trapSeq (m + 1) - trapSeq m = x / 2 - Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
    dsimp only [trapSeq, x]
    rw [harmonic_succ]
    simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
    rw [Real.log_div hm1 hm0]
    field_simp
    ring
  linarith

private lemma trapSeq_mono {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : trapSeq a ≤ trapSeq b := by
  induction hab with
  | refl => exact le_rfl
  | @step m hm ih => exact ih.trans (trapSeq_lt_succ (ha.trans hm)).le

private lemma tendsto_trapSeq :
    Tendsto trapSeq atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h0 : Tendsto (fun m : ℕ => 1 / (2 * (m : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (1 / 2 : ℝ)
    rw [mul_zero] at h
    exact h.congr fun m => by simp [one_div, mul_comm]
  have h1 : Tendsto (fun m : ℕ => Real.eulerMascheroniSeq' m - 1 / (2 * (m : ℝ)))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    simpa using Real.tendsto_eulerMascheroniSeq'.sub h0
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : m ≠ 0 := by omega
  simp [trapSeq, Real.eulerMascheroniSeq', eq_false_intro hm0]
  ring

private lemma trapSeq_lt_gamma {k : ℕ} (hk : 1 ≤ k) :
    trapSeq k < Real.eulerMascheroniConstant := by
  have hk1 : trapSeq (k + 1) ≤ Real.eulerMascheroniConstant := by
    refine ge_of_tendsto tendsto_trapSeq ?_
    filter_upwards [eventually_ge_atTop (k + 1)] with m hm
    exact trapSeq_mono (by omega) hm
  exact (trapSeq_lt_succ hk).trans_le hk1

private lemma harmonic_1 : harmonic 1 = 1 := by simp [harmonic_succ]
private lemma harmonic_2 : harmonic 2 = 3 / 2 := by rw [harmonic_succ, harmonic_1]; norm_num
private lemma harmonic_3 : harmonic 3 = 11 / 6 := by rw [harmonic_succ, harmonic_2]; norm_num
private lemma harmonic_4 : harmonic 4 = 25 / 12 := by rw [harmonic_succ, harmonic_3]; norm_num
private lemma harmonic_5 : harmonic 5 = 137 / 60 := by rw [harmonic_succ, harmonic_4]; norm_num
private lemma harmonic_6 : harmonic 6 = 49 / 20 := by rw [harmonic_succ, harmonic_5]; norm_num
private lemma harmonic_7 : harmonic 7 = 363 / 140 := by rw [harmonic_succ, harmonic_6]; norm_num
private lemma harmonic_8 : harmonic 8 = 761 / 280 := by rw [harmonic_succ, harmonic_7]; norm_num
private lemma harmonic_9 : harmonic 9 = 7129 / 2520 := by rw [harmonic_succ, harmonic_8]; norm_num
private lemma harmonic_10 : harmonic 10 = 7381 / 2520 := by rw [harmonic_succ, harmonic_9]; norm_num
private lemma harmonic_11 : harmonic 11 = 83711 / 27720 := by rw [harmonic_succ, harmonic_10]; norm_num
private lemma harmonic_12 : harmonic 12 = 86021 / 27720 := by rw [harmonic_succ, harmonic_11]; norm_num
private lemma harmonic_13 : harmonic 13 = 1145993 / 360360 := by rw [harmonic_succ, harmonic_12]; norm_num
private lemma harmonic_14 : harmonic 14 = 1171733 / 360360 := by rw [harmonic_succ, harmonic_13]; norm_num
private lemma harmonic_15 : harmonic 15 = 1195757 / 360360 := by rw [harmonic_succ, harmonic_14]; norm_num
private lemma harmonic_16 : harmonic 16 = 2436559 / 720720 := by rw [harmonic_succ, harmonic_15]; norm_num

private lemma gamma_gt_5768 : (5768 / 10000 : ℝ) < Real.eulerMascheroniConstant := by
  have h16 := trapSeq_lt_gamma (k := 16) (by omega)
  have hH16 : (harmonic 16 : ℝ) = 2436559 / 720720 := by rw [harmonic_16]; norm_num
  have hlog16 : Real.log ((16 : ℕ) : ℝ) = 4 * Real.log 2 := by
    rw [show ((16 : ℕ) : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have hlog2 := Real.log_two_lt_d9
  dsimp only [trapSeq] at h16
  rw [hH16, hlog16] at h16
  push_cast at h16
  linarith

private lemma exp_5768_ge : (17803 / 10000 : ℝ) ≤ Real.exp (5768 / 10000) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5768 / 10000) 7
  refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

private lemma log_add_lt_harmonic {n : ℕ} (hn : 2 ≤ n) :
    Real.log (n : ℝ) + 5768 / 10000 < (harmonic n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hγ := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  rw [Real.eulerMascheroniSeq', if_neg hn0] at hγ
  have hlb := gamma_gt_5768
  linarith

private noncomputable def poly7 (y : ℝ) : ℝ :=
  1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 + y ^ 6 / 720 + y ^ 7 / 4410

private lemma exp_le_pow16 {x b : ℝ} (hx0 : 0 ≤ x) (hx16 : x ≤ 16)
    (hb : poly7 (x / 16) ≤ b) :
    Real.exp x ≤ b ^ 16 := by
  have hx16_0 : 0 ≤ x / 16 := by linarith
  have hx16_1 : x / 16 ≤ 1 := by linarith
  have hbound := Real.exp_bound' hx16_0 hx16_1 (n := 7) (by omega)
  have hpoly : (∑ m ∈ Finset.range 7, (x / 16) ^ m / (m.factorial : ℝ)) +
      (x / 16) ^ 7 * ((7 : ℝ) + 1) / ((Nat.factorial 7 : ℝ) * 7) = poly7 (x / 16) := by
    dsimp only [poly7]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      Nat.factorial_zero, Nat.factorial_one, Nat.factorial_succ, Nat.cast_one, Nat.cast_mul,
      Nat.cast_ofNat]
    ring
  have hsub : Real.exp (x / 16) ≤ b := hbound.trans (hpoly ▸ hb)
  have hexp : Real.exp x = (Real.exp (x / 16)) ^ (16 : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  exact pow_le_pow_left₀ (Real.exp_pos _).le hsub 16

private def ValidPair (n : ℕ) (p : ℕ × ℕ) : Prop :=
  (p.1 : ℝ) / 1000 + (p.2 : ℝ) / 1000 * (n : ℝ) <
    (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n)

private lemma lagarias_bucket_bound {A L C : ℕ} {b1 b2 : ℝ}
    (hA : 2 ≤ A) (_hLpos : 0 < L)
    (hx1_0 : 0 ≤ (L : ℝ) / 1000 - 5768 / 10000)
    (hx1_16 : (L : ℝ) / 1000 - 5768 / 10000 ≤ 16)
    (hb1 : poly7 (((L : ℝ) / 1000 - 5768 / 10000) / 16) ≤ b1)
    (hb1A : b1 ^ 16 ≤ (A : ℝ))
    (hx2_16 : ((C : ℝ) / 1000) / (17803 / 10000) ≤ 16)
    (hb2 : poly7 ((((C : ℝ) / 1000) / (17803 / 10000)) / 16) ≤ b2)
    (hb2L : b2 ^ 16 ≤ (L : ℝ) / 1000)
    {n : ℕ} (hnA : A ≤ n) :
    ValidPair n (L, C) := by
  dsimp only [ValidPair]
  have hn2 : 2 ≤ n := hA.trans hnA
  have hApos : (0 : ℝ) < (A : ℝ) := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hAn : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnA
  have hexp1 : Real.exp ((L : ℝ) / 1000 - 5768 / 10000) ≤ (A : ℝ) :=
    (exp_le_pow16 hx1_0 hx1_16 hb1).trans hb1A
  have hlogA : (L : ℝ) / 1000 - 5768 / 10000 ≤ Real.log (A : ℝ) :=
    (Real.le_log_iff_exp_le hApos).mpr hexp1
  have hlogn : Real.log (A : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log hApos hAn
  have hlog_add := log_add_lt_harmonic hn2
  have hH_gt : (L : ℝ) / 1000 < (harmonic n : ℝ) := by linarith
  have hL_pos : (0 : ℝ) < (L : ℝ) / 1000 := by positivity
  have hH_pos : (0 : ℝ) < (harmonic n : ℝ) := hL_pos.trans hH_gt
  have hx2_0 : 0 ≤ ((C : ℝ) / 1000) / (17803 / 10000) := by positivity
  have hexp2 : Real.exp (((C : ℝ) / 1000) / (17803 / 10000)) ≤ (L : ℝ) / 1000 :=
    (exp_le_pow16 hx2_0 hx2_16 hb2).trans hb2L
  have hlogL : ((C : ℝ) / 1000) / (17803 / 10000) ≤ Real.log ((L : ℝ) / 1000) :=
    (Real.le_log_iff_exp_le hL_pos).mpr hexp2
  have hlogH : ((C : ℝ) / 1000) / (17803 / 10000) ≤ Real.log (harmonic n : ℝ) :=
    hlogL.trans (Real.log_le_log hL_pos hH_gt.le)
  have hexp_H : (17803 / 10000 : ℝ) * (n : ℝ) ≤ Real.exp (harmonic n : ℝ) := by
    calc (17803 / 10000 : ℝ) * (n : ℝ)
        ≤ Real.exp (5768 / 10000) * Real.exp (Real.log (n : ℝ)) := by
          rw [Real.exp_log hnpos]
          exact mul_le_mul_of_nonneg_right exp_5768_ge hnpos.le
      _ = Real.exp (Real.log (n : ℝ) + 5768 / 10000) := by rw [Real.exp_add]; ring
      _ ≤ Real.exp (harmonic n : ℝ) := Real.exp_le_exp.mpr hlog_add.le
  have hprod : (C : ℝ) / 1000 * (n : ℝ) ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
    have heq : (C : ℝ) / 1000 * (n : ℝ) =
        ((17803 / 10000 : ℝ) * (n : ℝ)) * (((C : ℝ) / 1000) / (17803 / 10000)) := by ring
    rw [heq]
    exact mul_le_mul hexp_H hlogH hx2_0 (Real.exp_pos _).le
  linarith

private def lbList : List (ℕ × ℕ × ℕ) :=
  [ (5, 2186, 1391), (7, 2522, 1646), (10, 2879, 1882), (14, 3215, 2078),
    (20, 3572, 2266), (24, 3754, 2354), (30, 3977, 2457), (48, 4447, 2656),
    (60, 4671, 2743), (72, 4853, 2811), (120, 5364, 2990), (121, 5372, 2992),
    (180, 5769, 3119), (360, 6462, 3321), (720, 7156, 3503), (1680, 8003, 3702),
    (2520, 8408, 3790), (5040, 9101, 3931) ]

private def lbStep (n : ℕ) (acc : ℕ × ℕ) (r : ℕ × ℕ × ℕ) : ℕ × ℕ :=
  if r.1 ≤ n ∧ acc.2 ≤ r.2.2 then r.2 else acc

private def lbPair (n : ℕ) : ℕ × ℕ := lbList.foldl (lbStep n) (1675, 917)

private def lbL (n : ℕ) : ℕ := (lbPair n).1

private def lbC (n : ℕ) : ℕ := (lbPair n).2

private lemma foldl_lbStep_mono (x y : ℕ) (hxy : x ≤ y) :
    ∀ (rs : List (ℕ × ℕ × ℕ)) (ax ay : ℕ × ℕ), ax.2 ≤ ay.2 →
      (rs.foldl (lbStep x) ax).2 ≤ (rs.foldl (lbStep y) ay).2
  | [], _, _, h => h
  | (_, _, _) :: rs, ax, ay, h => by
    apply foldl_lbStep_mono x y hxy rs
    dsimp only [lbStep]
    split_ifs <;> omega

private lemma lbC_mono : Monotone lbC :=
  fun x y hxy => foldl_lbStep_mono x y hxy lbList (1675, 917) (1675, 917) le_rfl

private lemma foldl_lbStep_valid (n : ℕ) :
    ∀ (rs : List (ℕ × ℕ × ℕ)) (acc : ℕ × ℕ), ValidPair n acc →
      (∀ r ∈ rs, r.1 ≤ n → ValidPair n r.2) → ValidPair n (rs.foldl (lbStep n) acc)
  | [], _, hacc, _ => hacc
  | r :: rs, acc, hacc, hrs => by
    apply foldl_lbStep_valid n rs
    · dsimp only [lbStep]
      split_ifs with h
      · exact hrs r (List.mem_cons_self ..) h.1
      · exact hacc
    · intro r' hr'
      exact hrs r' (List.mem_cons_of_mem _ hr')

private lemma lb_spec {n : ℕ} (hn : 3 ≤ n) :
    (lbL n : ℝ) / 1000 + (lbC n : ℝ) / 1000 * (n : ℝ) <
      (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n) := by
  change ValidPair n (lbPair n)
  refine foldl_lbStep_valid n lbList (1675, 917) ?_ ?_
  · exact lagarias_bucket_bound (b1 := 21421 / 20000) (b2 := 12909 / 12500)
      (by omega) (by omega) (by norm_num) (by norm_num)
      (by norm_num [poly7]) (by norm_num) (by norm_num)
      (by norm_num [poly7]) (by norm_num) hn
  · intro r hr hrn
    simp only [lbList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lagarias_bucket_bound (b1 := 110581 / 100000) (b2 := 21001 / 20000)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 3529 / 3125) (b2 := 105949 / 100000)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 28869 / 25000) (b2 := 106831 / 100000)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 117927 / 100000) (b2 := 6723 / 6250)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 120587 / 100000) (b2 := 108281 / 100000)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 121967 / 100000) (b2 := 13577 / 12500)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 123679 / 100000) (b2 := 109009 / 100000)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 63683 / 50000) (b2 := 109773 / 100000)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 129161 / 100000) (b2 := 110109 / 100000)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 130639 / 100000) (b2 := 27593 / 25000)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 67439 / 50000) (b2 := 27767 / 25000)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 67473 / 50000) (b2 := 27769 / 25000)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 4323 / 3125) (b2 := 27893 / 25000)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 144459 / 100000) (b2 := 56183 / 50000)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 150863 / 100000) (b2 := 56543 / 50000)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 31813 / 20000) (b2 := 113879 / 100000)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 81571 / 50000) (b2 := 14279 / 12500)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn
    · exact lagarias_bucket_bound (b1 := 42591 / 25000) (b2 := 57399 / 50000)
        (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) (by norm_num)
        (by norm_num [poly7]) (by norm_num) hrn

private lemma mul_sum_pow_range {p : ℕ} (hp : 1 ≤ p) (k : ℕ) :
    (p - 1) * ∑ i ∈ Finset.range (k + 1), p ^ i = p ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    have hpow : 1 ≤ p ^ (k + 1) := Nat.one_le_pow _ _ hp
    have hpow2 : 1 ≤ p ^ (k + 1 + 1) := Nat.one_le_pow _ _ hp
    zify [hp, hpow, hpow2]
    rw [pow_succ']
    ring

private lemma sigma_prime_pow_div {p : ℕ} (hp : p.Prime) (k : ℕ) :
    σ 1 (p ^ k) = (p ^ (k + 1) - 1) / (p - 1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, ← mul_sum_pow_range hp.one_le k]
  exact (Nat.mul_div_right _ (Nat.sub_pos_of_lt hp.one_lt)).symm

private lemma strip_prime {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) :
    ∃ k m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ n = p ^ k * m := by
  refine ⟨n.factorization p, ordCompl[p] n, ?_, Nat.not_dvd_ordCompl hp hn.ne',
    (Nat.ordProj_mul_ordCompl_eq_self n p).symm⟩
  exact Nat.div_pos (Nat.le_of_dvd hn (Nat.ordProj_dvd n p)) (pow_pos hp.pos _)

private def smoothSig (a b c d : ℕ) : ℕ :=
  (2 ^ (a + 1) - 1) * ((3 ^ (b + 1) - 1) / 2) *
    ((5 ^ (c + 1) - 1) / 4) * ((7 ^ (d + 1) - 1) / 6)

private lemma smooth_decomp {n : ℕ} (hn : 0 < n) (h5040 : n ≤ 5040) :
    ∃ a b c d m : ℕ, a < 13 ∧ b < 8 ∧ c < 6 ∧ d < 5 ∧
      0 < m ∧ ¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m ∧ ¬ 7 ∣ m ∧
      n = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * m ∧
      σ 1 n = smoothSig a b c d * σ 1 m := by
  obtain ⟨a, n₁, hn1, h2n1, rfl⟩ := strip_prime (by decide : Nat.Prime 2) hn
  obtain ⟨b, n₂, hn2, h3n2, rfl⟩ := strip_prime (by decide : Nat.Prime 3) hn1
  obtain ⟨c, n₃, hn3, h5n3, rfl⟩ := strip_prime (by decide : Nat.Prime 5) hn2
  obtain ⟨d, m, hm, h7m, rfl⟩ := strip_prime (by decide : Nat.Prime 7) hn3
  have ha : a < 13 := by
    by_contra h
    have ha13 : 13 ≤ a := by omega
    have hpow : 2 ^ 13 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha13
    have hpos : 0 < 3 ^ b * (5 ^ c * (7 ^ d * m)) := by positivity
    nlinarith
  have hb : b < 8 := by
    by_contra h
    have hb8 : 8 ≤ b := by omega
    have hpow : 3 ^ 8 ≤ 3 ^ b := Nat.pow_le_pow_right (by omega) hb8
    have : 3 ^ b ≤ 2 ^ a * (3 ^ b * (5 ^ c * (7 ^ d * m))) := by
      have h1 : 0 < 2 ^ a := by positivity
      have h2 : 0 < 5 ^ c * (7 ^ d * m) := by positivity
      nlinarith
    omega
  have hc : c < 6 := by
    by_contra h
    have hc6 : 6 ≤ c := by omega
    have hpow : 5 ^ 6 ≤ 5 ^ c := Nat.pow_le_pow_right (by omega) hc6
    have : 5 ^ c ≤ 2 ^ a * (3 ^ b * (5 ^ c * (7 ^ d * m))) := by
      have h1 : 0 < 2 ^ a * 3 ^ b := by positivity
      have h2 : 0 < 7 ^ d * m := by positivity
      nlinarith
    omega
  have hd : d < 5 := by
    by_contra h
    have hd5 : 5 ≤ d := by omega
    have hpow : 7 ^ 5 ≤ 7 ^ d := Nat.pow_le_pow_right (by omega) hd5
    have : 7 ^ d ≤ 2 ^ a * (3 ^ b * (5 ^ c * (7 ^ d * m))) := by
      have h1 : 0 < 2 ^ a * 3 ^ b * 5 ^ c := by positivity
      nlinarith
    omega
  have h2m : ¬ 2 ∣ m := fun h => h2n1 (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h _) _) _)
  have h3m : ¬ 3 ∣ m := fun h => h3n2 (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h _) _)
  have h5m : ¬ 5 ∣ m := fun h => h5n3 (dvd_mul_of_dvd_right h _)
  have hc2 : Nat.Coprime (2 ^ a) (3 ^ b * (5 ^ c * (7 ^ d * m))) := by
    refine Nat.Coprime.pow_left a ?_
    exact (by decide : Nat.Prime 2).coprime_iff_not_dvd.mpr h2n1
  have hc3 : Nat.Coprime (3 ^ b) (5 ^ c * (7 ^ d * m)) := by
    refine Nat.Coprime.pow_left b ?_
    exact (by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h3n2
  have hc5 : Nat.Coprime (5 ^ c) (7 ^ d * m) := by
    refine Nat.Coprime.pow_left c ?_
    exact (by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5n3
  have hc7 : Nat.Coprime (7 ^ d) m := by
    refine Nat.Coprime.pow_left d ?_
    exact (by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr h7m
  have hmult := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  have hs2 := sigma_prime_pow_div (by decide : Nat.Prime 2) a
  have hs3 := sigma_prime_pow_div (by decide : Nat.Prime 3) b
  have hs5 := sigma_prime_pow_div (by decide : Nat.Prime 5) c
  have hs7 := sigma_prime_pow_div (by decide : Nat.Prime 7) d
  have hsig : σ 1 (2 ^ a * (3 ^ b * (5 ^ c * (7 ^ d * m)))) = smoothSig a b c d * σ 1 m := by
    rw [hmult.map_mul_of_coprime hc2, hmult.map_mul_of_coprime hc3,
        hmult.map_mul_of_coprime hc5, hmult.map_mul_of_coprime hc7,
        hs2, hs3, hs5, hs7]
    dsimp only [smoothSig]
    simp only [Nat.reduceSub, Nat.div_one]
    ring
  refine ⟨a, b, c, d, m, ha, hb, hc, hd, hm, h2m, h3m, h5m, h7m, by ring, hsig⟩

private lemma sigma_le_prod_primeFactors {m : ℕ} (hm : 0 < m) :
    (σ 1 m : ℝ) ≤ (m : ℝ) * ∏ p ∈ m.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm.ne']
  push_cast
  have hprod_eq : (m : ℝ) = ∏ p ∈ m.primeFactors, (p : ℝ) ^ (m.factorization p) := by
    have hnat : m = ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
      have h0 := Nat.prod_factorization_pow_eq_self hm.ne'
      rw [Finsupp.prod, Nat.support_factorization] at h0
      exact h0.symm
    exact_mod_cast hnat
  conv_rhs => rw [hprod_eq, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
  have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpr.one_lt
  have hpsub : 0 < (p : ℝ) - 1 := by linarith
  have hmul : ((p : ℝ) - 1) * ∑ i ∈ Finset.range (m.factorization p + 1), (p : ℝ) ^ (i * 1) =
      (p : ℝ) ^ (m.factorization p + 1) - 1 := by
    have hnat := mul_sum_pow_range hpr.one_le (m.factorization p)
    have hcast : (((p - 1 : ℕ) * ∑ i ∈ Finset.range (m.factorization p + 1), p ^ i : ℕ) : ℝ) =
        ((p ^ (m.factorization p + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    have hpow1 : 1 ≤ p ^ (m.factorization p + 1) := Nat.one_le_pow _ _ hpr.one_le
    rw [Nat.cast_mul, Nat.cast_sub hpr.one_le, Nat.cast_sub hpow1] at hcast
    push_cast at hcast
    simpa only [mul_one] using hcast
  refine le_of_mul_le_mul_left ?_ hpsub
  calc ((p : ℝ) - 1) * ∑ i ∈ Finset.range (m.factorization p + 1), (p : ℝ) ^ (i * 1)
      = (p : ℝ) ^ (m.factorization p + 1) - 1 := hmul
    _ ≤ (p : ℝ) ^ (m.factorization p + 1) := by linarith
    _ = ((p : ℝ) - 1) * ((p : ℝ) ^ m.factorization p * ((p : ℝ) / ((p : ℝ) - 1))) := by
        rw [pow_succ]
        field_simp

private lemma coprime210_min_prime {m p : ℕ} (hm2 : ¬ 2 ∣ m) (hm3 : ¬ 3 ∣ m)
    (hm5 : ¬ 5 ∣ m) (hm7 : ¬ 7 ∣ m) (hp : p ∈ m.primeFactors) : 11 ≤ p := by
  have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
  by_contra h
  have hp10 : p ≤ 10 := by omega
  interval_cases p <;> norm_num at hpr <;> contradiction

private lemma coprime210_sigma_lt_121 {m : ℕ} (hm : 1 < m) (hmlt : m < 121)
    (hm2 : ¬ 2 ∣ m) (hm3 : ¬ 3 ∣ m) (hm5 : ¬ 5 ∣ m) (hm7 : ¬ 7 ∣ m) :
    11 * σ 1 m ≤ 12 * m := by
  have hmpr : m.Prime := by
    by_contra hnp
    have hmin_ge : 11 ≤ m.minFac := by
      have hmfp : m.minFac ∈ m.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd m, by omega⟩
      exact coprime210_min_prime hm2 hm3 hm5 hm7 hmfp
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < m) hnp
    nlinarith
  have hm11 : 11 ≤ m :=
    coprime210_min_prime hm2 hm3 hm5 hm7 (Nat.mem_primeFactors.mpr ⟨hmpr, dvd_rfl, by omega⟩)
  have hsig : σ 1 m = m + 1 := by
    conv_lhs => rw [← pow_one m, ArithmeticFunction.sigma_one_apply_prime_pow hmpr]
    simp [Finset.sum_range_succ, Nat.add_comm]
  rw [hsig]
  omega

private lemma coprime210_sigma_ge_121 {m k : ℕ} (hm : 0 < m)
    (hm2 : ¬ 2 ∣ m) (hm3 : ¬ 3 ∣ m) (hm5 : ¬ 5 ∣ m) (hm7 : ¬ 7 ∣ m)
    (hk : m < 11 ^ (k + 1)) :
    (σ 1 m : ℝ) ≤ (m : ℝ) * (11 / 10 : ℝ) ^ k := by
  have hle : m.primeFactors.card ≤ k := by
    by_contra h
    have hk1 : k + 1 ≤ m.primeFactors.card := by omega
    have h11 : 11 ^ (k + 1) ≤ 11 ^ m.primeFactors.card := Nat.pow_le_pow_right (by omega) hk1
    have hprod : 11 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p := by
      calc 11 ^ m.primeFactors.card
          = ∏ _p ∈ m.primeFactors, 11 := by simp
        _ ≤ ∏ p ∈ m.primeFactors, p :=
          Finset.prod_le_prod' fun p hp => coprime210_min_prime hm2 hm3 hm5 hm7 hp
    have hdvd : ∏ p ∈ m.primeFactors, p ≤ m := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
    omega
  have hratio : ∏ p ∈ m.primeFactors, (p : ℝ) / ((p : ℝ) - 1) ≤ (11 / 10 : ℝ) ^ k := by
    calc ∏ p ∈ m.primeFactors, (p : ℝ) / ((p : ℝ) - 1)
        ≤ ∏ _p ∈ m.primeFactors, (11 / 10 : ℝ) := by
          refine Finset.prod_le_prod
            (fun p hp => div_nonneg (Nat.cast_nonneg _)
              (sub_nonneg.mpr (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)))
            (fun p hp => ?_)
          have hp11 : (11 : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast coprime210_min_prime hm2 hm3 hm5 hm7 hp
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]
          linarith
      _ = (11 / 10 : ℝ) ^ m.primeFactors.card := by simp only [Finset.prod_const, nsmul_eq_mul]
      _ ≤ (11 / 10 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hle
  calc (σ 1 m : ℝ)
      ≤ (m : ℝ) * ∏ p ∈ m.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := sigma_le_prod_primeFactors hm
    _ ≤ (m : ℝ) * (11 / 10 : ℝ) ^ k := mul_le_mul_of_nonneg_left hratio (by positivity)

private def checkTuple (a b c d : ℕ) : Bool :=
  let s := 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d
  if 5040 < s then true else
  let sig := smoothSig a b c d
  let ok0 := if s ≤ 1 ∨ s = 2 ∨ s = 4 ∨ s = 6 ∨ s = 12 then true
    else decide (1000 * sig < lbL s + lbC s * s)
  let ok1 := if 5040 < 11 * s then true else decide (1000 * 12 * sig < 11 * lbC (11 * s) * s)
  let ok2 := if 5040 < 121 * s then true else decide (1000 * 121 * sig < 100 * lbC (121 * s) * s)
  let ok3 := if 5040 < 1331 * s then true else decide (1331 * sig < lbC (1331 * s) * s)
  ok0 && ok1 && ok2 && ok3

set_option maxRecDepth 400000 in
private lemma checkAllTuples :
    ∀ a : Fin 13, ∀ b : Fin 8, ∀ c : Fin 6, ∀ d : Fin 5,
      checkTuple a.val b.val c.val d.val = true := by
  decide

private lemma exact_pow4_lagarias {n sig_n : ℕ} {Hn c_log b_log : ℝ}
    (hsig : σ 1 n = sig_n) (hH : (harmonic n : ℝ) = Hn)
    (hc0 : 0 ≤ c_log) (hc4 : c_log / 4 ≤ 1) (_hb0 : 0 ≤ b_log)
    (hlog : (∑ m ∈ Finset.range 6, (c_log / 4) ^ m / (m.factorial : ℝ)) +
            (c_log / 4) ^ 6 * 7 / ((Nat.factorial 6 : ℝ) * 6) ≤ b_log)
    (hb4 : b_log ^ 4 ≤ Hn)
    (htot : (sig_n : ℝ) <
      Hn + (∑ m ∈ Finset.range 6, (Hn / 4) ^ m / (m.factorial : ℝ)) ^ 4 * c_log)
    (hHn0 : 0 ≤ Hn) :
    (σ 1 n : ℝ) < (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n) := by
  have hbound := Real.exp_bound' (by linarith : 0 ≤ c_log / 4) hc4 (n := 6) (by omega)
  have hexp_sub : Real.exp (c_log / 4) ≤ b_log := by
    refine hbound.trans ?_
    calc (∑ m ∈ Finset.range 6, (c_log / 4) ^ m / (m.factorial : ℝ)) +
          (c_log / 4) ^ 6 * ((6 : ℝ) + 1) / ((Nat.factorial 6 : ℝ) * 6)
        = (∑ m ∈ Finset.range 6, (c_log / 4) ^ m / (m.factorial : ℝ)) +
          (c_log / 4) ^ 6 * 7 / ((Nat.factorial 6 : ℝ) * 6) := by ring
      _ ≤ b_log := hlog
  have hexp_c : Real.exp c_log ≤ Hn := by
    rw [show Real.exp c_log = (Real.exp (c_log / 4)) ^ (4 : ℕ) by
      rw [← Real.exp_nat_mul]; congr 1; ring]
    exact (pow_le_pow_left₀ (Real.exp_pos _).le hexp_sub 4).trans hb4
  have hHpos : 0 < Hn := lt_of_lt_of_le (Real.exp_pos c_log) hexp_c
  have hlog_ge : c_log ≤ Real.log Hn := (Real.le_log_iff_exp_le hHpos).mpr hexp_c
  have hsum_le : (∑ m ∈ Finset.range 6, (Hn / 4) ^ m / (m.factorial : ℝ)) ^ 4 ≤ Real.exp Hn := by
    have hs := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ Hn / 4) 6
    rw [show Real.exp Hn = (Real.exp (Hn / 4)) ^ (4 : ℕ) by
      rw [← Real.exp_nat_mul]; congr 1; ring]
    exact pow_le_pow_left₀ (by positivity) hs 4
  have hmul : (∑ m ∈ Finset.range 6, (Hn / 4) ^ m / (m.factorial : ℝ)) ^ 4 * c_log ≤
      Real.exp Hn * Real.log Hn :=
    mul_le_mul hsum_le hlog_ge hc0 (Real.exp_pos _).le
  have hcast : (σ 1 n : ℝ) = (sig_n : ℝ) := by exact_mod_cast hsig
  rw [hcast, hH]
  linarith

private lemma case_2 :
    (σ 1 2 : ℝ) < (harmonic 2 : ℝ) + Real.exp (harmonic 2) * Real.log (harmonic 2) :=
  exact_pow4_lagarias (sig_n := 3) (Hn := 3 / 2) (c_log := 40 / 100) (b_log := 2763 / 2500)
    (by decide) (by rw [harmonic_2]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)

private lemma case_4 :
    (σ 1 4 : ℝ) < (harmonic 4 : ℝ) + Real.exp (harmonic 4) * Real.log (harmonic 4) :=
  exact_pow4_lagarias (sig_n := 7) (Hn := 25 / 12) (c_log := 73 / 100) (b_log := 12003 / 10000)
    (by decide) (by rw [harmonic_4]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)

private lemma case_6 :
    (σ 1 6 : ℝ) < (harmonic 6 : ℝ) + Real.exp (harmonic 6) * Real.log (harmonic 6) :=
  exact_pow4_lagarias (sig_n := 12) (Hn := 49 / 20) (c_log := 89 / 100) (b_log := 3123 / 2500)
    (by decide) (by rw [harmonic_6]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)

private lemma case_12 :
    (σ 1 12 : ℝ) < (harmonic 12 : ℝ) + Real.exp (harmonic 12) * Real.log (harmonic 12) :=
  exact_pow4_lagarias (sig_n := 28) (Hn := 86021 / 27720) (c_log := 113 / 100) (b_log := 2653 / 2000)
    (by decide) (by rw [harmonic_12]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)

private lemma solve_le_5040 {n : ℕ} (hn1 : 1 < n) (hn5040 : n ≤ 5040) :
    (σ 1 n : ℝ) < (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n) := by
  obtain ⟨a, b, c, d, m, ha, hb, hc, hd, hm, hm2, hm3, hm5, hm7, hn_eq, hsig⟩ :=
    smooth_decomp (by omega : 0 < n) hn5040
  set s : ℕ := 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d
  have hspos : 0 < s := by positivity
  have hs5040 : s ≤ 5040 := by
    have : s ≤ s * m := Nat.le_mul_of_pos_right s hm
    rw [← hn_eq] at this
    exact this.trans hn5040
  have hchk := checkAllTuples ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩
  dsimp only [Fin.val_mk, checkTuple] at hchk
  change (if 5040 < s then true else _) = true at hchk
  rw [if_neg (by omega : ¬ 5040 < s)] at hchk
  simp only [Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨hok0, hok1⟩, hok2⟩, hok3⟩
  by_cases hm1 : m = 1
  · subst hm1
    have hns : n = s := by simpa using hn_eq
    subst hns
    have hsig0 : σ 1 s = smoothSig a b c d := by simpa using hsig
    by_cases hex : s = 2 ∨ s = 4 ∨ s = 6 ∨ s = 12
    · rcases hex with hs2 | hs4 | hs6 | hs12
      · rw [hs2]; exact case_2
      · rw [hs4]; exact case_4
      · rw [hs6]; exact case_6
      · rw [hs12]; exact case_12
    · have hs3 : 3 ≤ s := by omega
      have hcond : ¬ (s ≤ 1 ∨ s = 2 ∨ s = 4 ∨ s = 6 ∨ s = 12) := by omega
      rw [if_neg hcond, decide_eq_true_eq] at hok0
      have hreal : (σ 1 s : ℝ) < (lbL s : ℝ) / 1000 + (lbC s : ℝ) / 1000 * (s : ℝ) := by
        rw [hsig0]
        have : ((1000 * smoothSig a b c d : ℕ) : ℝ) < ((lbL s + lbC s * s : ℕ) : ℝ) := by
          exact_mod_cast hok0
        push_cast at this
        linarith
      exact hreal.trans (lb_spec hs3)
  · have hm_gt1 : 1 < m := by omega
    have hm_ge11 : 11 ≤ m := by
      have hmfp : m.minFac ∈ m.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd m, by omega⟩
      have h11 := coprime210_min_prime hm2 hm3 hm5 hm7 hmfp
      exact h11.trans (Nat.minFac_le (by omega))
    have hn3 : 3 ≤ n := by
      have h3m : 3 ≤ m := by omega
      have h1 : 3 ≤ s * m := by nlinarith
      omega
    by_cases hm121 : m < 121
    · have h11s : 11 * s ≤ n := by
        rw [hn_eq, mul_comm s m]
        exact Nat.mul_le_mul_right s hm_ge11
      have h11s_le : 11 * s ≤ 5040 := h11s.trans hn5040
      rw [if_neg (by omega : ¬ 5040 < 11 * s), decide_eq_true_eq] at hok1
      have hmsig := coprime210_sigma_lt_121 hm_gt1 hm121 hm2 hm3 hm5 hm7
      have hmono : lbC (11 * s) ≤ lbC n := lbC_mono h11s
      have hmul_nat : 1000 * 11 * σ 1 n < 11 * lbC n * n := by
        calc 1000 * 11 * σ 1 n
            = 1000 * smoothSig a b c d * (11 * σ 1 m) := by rw [hsig]; ring
          _ ≤ 1000 * smoothSig a b c d * (12 * m) := Nat.mul_le_mul_left _ hmsig
          _ = (1000 * 12 * smoothSig a b c d) * m := by ring
          _ < (11 * lbC (11 * s) * s) * m := Nat.mul_lt_mul_of_pos_right hok1 hm
          _ ≤ (11 * lbC n * s) * m := by gcongr
          _ = 11 * lbC n * n := by rw [hn_eq]; ring
      have hnat : 1000 * σ 1 n < lbC n * n :=
        Nat.lt_of_mul_lt_mul_left (show 11 * (1000 * σ 1 n) < 11 * (lbC n * n) by linarith)
      have hreal : (σ 1 n : ℝ) < (lbL n : ℝ) / 1000 + (lbC n : ℝ) / 1000 * (n : ℝ) := by
        have h1 : ((1000 * σ 1 n : ℕ) : ℝ) < ((lbC n * n : ℕ) : ℝ) := by exact_mod_cast hnat
        push_cast at h1
        have hL0 : 0 ≤ (lbL n : ℝ) / 1000 := by positivity
        linarith
      exact hreal.trans (lb_spec hn3)
    · by_cases hm1331 : m < 1331
      · have h121s : 121 * s ≤ n := by
          rw [hn_eq, mul_comm s m]
          exact Nat.mul_le_mul_right s (by omega)
        rw [if_neg (by omega : ¬ 5040 < 121 * s), decide_eq_true_eq] at hok2
        have hmsig := coprime210_sigma_ge_121 (k := 2) hm hm2 hm3 hm5 hm7 (by norm_num; omega)
        have hmono : (lbC (121 * s) : ℝ) ≤ (lbC n : ℝ) := by exact_mod_cast lbC_mono h121s
        have hok2_r : 1000 * 121 * (smoothSig a b c d : ℝ) < 100 * (lbC (121 * s) : ℝ) * (s : ℝ) := by
          exact_mod_cast hok2
        have hmpos_r : (0 : ℝ) < (m : ℝ) := by positivity
        have hreal_mul : 1000 * (σ 1 n : ℝ) < (lbC n : ℝ) * (n : ℝ) := by
          calc 1000 * (σ 1 n : ℝ)
              = 1000 * (smoothSig a b c d : ℝ) * (σ 1 m : ℝ) := by
                  have hc : (σ 1 n : ℝ) = (smoothSig a b c d : ℝ) * (σ 1 m : ℝ) := by exact_mod_cast hsig
                  rw [hc]; ring
            _ ≤ 1000 * (smoothSig a b c d : ℝ) * ((m : ℝ) * (11 / 10 : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_left hmsig (by positivity)
            _ = (1000 * 121 * (smoothSig a b c d : ℝ)) * (m : ℝ) / 100 := by ring
            _ < (100 * (lbC (121 * s) : ℝ) * (s : ℝ)) * (m : ℝ) / 100 := by
                apply div_lt_div_of_pos_right _ (by norm_num)
                exact mul_lt_mul_of_pos_right hok2_r hmpos_r
            _ = (lbC (121 * s) : ℝ) * ((s : ℝ) * (m : ℝ)) := by ring
            _ ≤ (lbC n : ℝ) * (n : ℝ) := by
                have hne_r : (n : ℝ) = (s : ℝ) * (m : ℝ) := by
                  have : n = s * m := by rw [hn_eq]
                  exact_mod_cast this
                rw [← hne_r]
                exact mul_le_mul_of_nonneg_right hmono (by positivity)
        have hreal : (σ 1 n : ℝ) < (lbL n : ℝ) / 1000 + (lbC n : ℝ) / 1000 * (n : ℝ) := by
          have hL0 : 0 ≤ (lbL n : ℝ) / 1000 := by positivity
          linarith
        exact hreal.trans (lb_spec hn3)
      · have h1331s : 1331 * s ≤ n := by
          rw [hn_eq, mul_comm s m]
          exact Nat.mul_le_mul_right s (by omega)
        rw [if_neg (by omega : ¬ 5040 < 1331 * s), decide_eq_true_eq] at hok3
        have hlt_pow : m < 11 ^ (3 + 1) := by
          have hm5040 : m ≤ 5040 := by
            have : m ≤ s * m := Nat.le_mul_of_pos_left m hspos
            rw [← hn_eq] at this
            exact this.trans hn5040
          norm_num
          omega
        have hmsig := coprime210_sigma_ge_121 (k := 3) hm hm2 hm3 hm5 hm7 hlt_pow
        have hmono : (lbC (1331 * s) : ℝ) ≤ (lbC n : ℝ) := by exact_mod_cast lbC_mono h1331s
        have hok3_r : 1331 * (smoothSig a b c d : ℝ) < (lbC (1331 * s) : ℝ) * (s : ℝ) := by
          exact_mod_cast hok3
        have hmpos_r : (0 : ℝ) < (m : ℝ) := by positivity
        have hreal_mul : 1000 * (σ 1 n : ℝ) < (lbC n : ℝ) * (n : ℝ) := by
          calc 1000 * (σ 1 n : ℝ)
              = 1000 * (smoothSig a b c d : ℝ) * (σ 1 m : ℝ) := by
                  have hc : (σ 1 n : ℝ) = (smoothSig a b c d : ℝ) * (σ 1 m : ℝ) := by exact_mod_cast hsig
                  rw [hc]; ring
            _ ≤ 1000 * (smoothSig a b c d : ℝ) * ((m : ℝ) * (11 / 10 : ℝ) ^ 3) :=
                mul_le_mul_of_nonneg_left hmsig (by positivity)
            _ = (1331 * (smoothSig a b c d : ℝ)) * (m : ℝ) := by ring
            _ < ((lbC (1331 * s) : ℝ) * (s : ℝ)) * (m : ℝ) :=
                mul_lt_mul_of_pos_right hok3_r hmpos_r
            _ = (lbC (1331 * s) : ℝ) * ((s : ℝ) * (m : ℝ)) := by ring
            _ ≤ (lbC n : ℝ) * (n : ℝ) := by
                have hne_r : (n : ℝ) = (s : ℝ) * (m : ℝ) := by
                  have : n = s * m := by rw [hn_eq]
                  exact_mod_cast this
                rw [← hne_r]
                exact mul_le_mul_of_nonneg_right hmono (by positivity)
        have hreal : (σ 1 n : ℝ) < (lbL n : ℝ) / 1000 + (lbC n : ℝ) / 1000 * (n : ℝ) := by
          have hL0 : 0 ≤ (lbL n : ℝ) / 1000 := by positivity
          linarith
        exact hreal.trans (lb_spec hn3)

end LagariasH3

theorem OMA.solution : OMA.R_RiemannHypothesis_lagarias_criterion_rhs_R1.H3 :=
  fun _ hn1 hn5040 => LagariasH3.solve_le_5040 hn1 hn5040
