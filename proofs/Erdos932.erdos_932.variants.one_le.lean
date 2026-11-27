import FormalConjectures.ErdosProblems.«932»
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Erdős Problem 932, density-zero variant

The total length of the first N prime gaps is at most p_N. Chebyshev's
bounds imply p_N = O(N log N) and π(x) = o(x). Gaps of length at least
C log(N + 1) then have proportion O(1/C). Each remaining exceptional
gap contains a different C log(N + 1)-smooth integer. The elementary
smooth-number count 2^π(y) √x makes their proportion tend to zero.
-/

noncomputable section

namespace OMA.SmoothPrimeGaps

open Asymptotics Filter Finset
open scoped Topology

private def p (n : ℕ) : ℕ := n.nth Nat.Prime

private def gap (r : ℕ) : ℕ := p (r + 1) - p r

private def exceptional (r : ℕ) : Prop :=
  ∃ m : ℕ, p r < m ∧ m < p (r + 1) ∧ m.maxPrimeFac < gap r

private theorem p_mono : StrictMono p := Nat.nth_strictMono Nat.infinite_setOfPred_prime

private theorem large_gap_count (N B : ℕ) :
    (B : ℝ) * (((range N).filter (fun r => B ≤ gap r)).card : ℝ) ≤ (p N : ℝ) := by
  let L := (range N).filter (fun r => B ≤ gap r)
  change (B : ℝ) * (L.card : ℝ) ≤ (p N : ℝ)
  calc
    _ = ∑ _r ∈ L, (B : ℝ) := by simp [mul_comm]
    _ ≤ ∑ r ∈ L, (gap r : ℝ) := Finset.sum_le_sum fun r hr =>
      Nat.cast_le.mpr (Finset.mem_filter.mp hr).2
    _ ≤ ∑ r ∈ range N, (gap r : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun r _ _ => Nat.cast_nonneg _
    _ = (p N : ℝ) - (p 0 : ℝ) := by
      have hcast (r : ℕ) : (gap r : ℝ) = (p (r + 1) : ℝ) - (p r : ℝ) :=
        Nat.cast_sub (p_mono.monotone (Nat.le_succ r))
      simp_rw [hcast]
      exact Finset.sum_range_sub (fun i => (p i : ℝ)) N
    _ ≤ (p N : ℝ) := sub_le_self _ (Nat.cast_nonneg _)

private theorem exceptional_count (N B : ℕ) :
    open scoped Classical in
    ((range N).filter exceptional).card ≤
      ((range N).filter (fun r => B ≤ gap r)).card + (Nat.smoothNumbersUpTo (p N) B).card := by
  classical
  let E := (range N).filter exceptional
  let L := (range N).filter (fun r => B ≤ gap r)
  let S := E.filter (fun r => ¬ B ≤ gap r)
  have hsplit : E.filter (fun r => B ≤ gap r) ∪ S = E := by
    ext r
    by_cases hr : B ≤ gap r
    · simp [S, hr]
    · simp [S, hr, Nat.lt_of_not_ge hr]
  have hL : (E.filter (fun r => B ≤ gap r)).card ≤ L.card := by
    apply Finset.card_le_card
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr'.1).1, hr'.2⟩
  let m (r : ℕ) : ℕ := if hr : exceptional r then Classical.choose hr else 0
  have hdata {r : ℕ} (hr : r ∈ S) :
      r < N ∧ gap r < B ∧ p r < m r ∧ m r < p (r + 1) ∧ (m r).maxPrimeFac < gap r := by
    have hr' := Finset.mem_filter.mp hr
    have he := (Finset.mem_filter.mp hr'.1).2
    exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hr'.1).1,
      Nat.lt_of_not_ge hr'.2, by simpa [m, he] using Classical.choose_spec he⟩
  have hS : S.card ≤ (Nat.smoothNumbersUpTo (p N) B).card := by
    apply Finset.card_le_card_of_injOn m
    · intro r hr
      obtain ⟨hrN, hrB, hl, hu, hfac⟩ := hdata hr
      apply Nat.mem_smoothNumbersUpTo.mpr
      refine ⟨hu.le.trans (p_mono.monotone (by omega)), Nat.mem_smoothNumbers'.mpr ?_⟩
      intro q hq hdvd
      have hqle := Nat.le_maxPrimeFac (n := m r) (by omega) hq hdvd
      omega
    · intro r hr s hs heq
      obtain ⟨_, _, hlr, hur, _⟩ := hdata hr
      obtain ⟨_, _, hls, hus, _⟩ := hdata hs
      rcases lt_trichotomy r s with h | h | h
      · have hle : p (r + 1) ≤ p s := p_mono.monotone (by omega)
        omega
      · exact h
      · have hle : p (s + 1) ≤ p r := p_mono.monotone (by omega)
        omega
  calc
    E.card = (E.filter (fun r => B ≤ gap r) ∪ S).card := by rw [hsplit]
    _ ≤ (E.filter (fun r => B ≤ gap r)).card + S.card := Finset.card_union_le ..
    _ ≤ _ := add_le_add hL hS

private def cutoff (C : ℝ) (N : ℕ) : ℕ := ⌈C * Real.log ((N : ℝ) + 1)⌉₊

private theorem cast_succ_tendsto : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
  tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

private theorem log_succ_tendsto : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop :=
  Real.tendsto_log_atTop.comp cast_succ_tendsto

private theorem eventually_log_bound (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ c * x := by
  filter_upwards [Real.isLittleO_log_id_atTop.bound hc, eventually_ge_atTop 0] with x hx hx0
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hx0] at hx
  exact (le_abs_self (Real.log x)).trans hx

private theorem prime_index_bound :
    ∀ᶠ n : ℕ in atTop, (p n : ℝ) ≤ 16 * (n : ℝ) * Real.log ((n : ℝ) + 1) := by
  let X (n : ℕ) : ℝ := (n : ℝ) + 1
  let Y (n : ℕ) : ℝ := 8 * X n * Real.log (X n)
  have hY : Tendsto Y atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ cast_succ_tendsto
    filter_upwards [log_succ_tendsto.eventually_ge_atTop 1] with n hlog
    have hX : 0 ≤ X n := by dsimp [X]; positivity
    change X n ≤ Y n
    change 1 ≤ Real.log (X n) at hlog
    dsimp [Y]
    nlinarith [mul_nonneg hX (sub_nonneg.mpr hlog)]
  have hYplus : Tendsto (fun n => Y n + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 hY
  filter_upwards [hY.eventually_ge_atTop 4,
    hYplus.eventually (eventually_log_bound (1 / 16) (by norm_num)),
    cast_succ_tendsto.eventually (eventually_log_bound (1 / 8) (by norm_num)),
    eventually_ge_atTop 1] with n hy hylog hxlog hn
  have hx : 0 < X n := by dsimp [X]; positivity
  have hy1 : 1 < Y n := by linarith
  have hypos : 0 < Real.log (Y n) := Real.log_pos hy1
  change Real.log (X n) ≤ (1 / 8) * X n at hxlog
  have hsq : Y n ≤ X n ^ 2 := by
    dsimp [Y]
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hxlog)]
  have hlogY : Real.log (Y n) ≤ 2 * Real.log (X n) := by
    have h := Real.log_le_log (by linarith : 0 < Y n) hsq
    rw [Real.log_pow] at h
    simpa using h
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnumerator : Y n / 4 ≤ (Y n - 1) * Real.log 2 - Real.log (Y n + 2) := by
    have h := mul_le_mul_of_nonneg_left hlog2 (by linarith : 0 ≤ Y n - 1)
    linarith
  have hcount : X n ≤ (Nat.primeCounting ⌊Y n⌋₊ : ℝ) := by
    refine le_trans ((le_div_iff₀ hypos).mpr ?_) (Chebyshev.pi_ge' hy1)
    calc
      X n * Real.log (Y n) ≤ X n * (2 * Real.log (X n)) :=
        mul_le_mul_of_nonneg_left hlogY hx.le
      _ = Y n / 4 := by dsimp [Y]; ring
      _ ≤ _ := hnumerator
  have hcnt : n + 1 ≤ Nat.primeCounting ⌊Y n⌋₊ := by
    change (n : ℝ) + 1 ≤ (Nat.primeCounting ⌊Y n⌋₊ : ℝ) at hcount
    exact_mod_cast hcount
  have hnth : p n ≤ ⌊Y n⌋₊ := by
    have h := Nat.nth_lt_of_lt_count (p := Nat.Prime)
      (show n < Nat.count Nat.Prime (⌊Y n⌋₊ + 1) from Nat.lt_of_succ_le hcnt)
    exact Nat.le_of_lt_succ h
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log (X n) := Real.log_nonneg (by dsimp [X]; linarith)
  calc
    (p n : ℝ) ≤ ⌊Y n⌋₊ := by exact_mod_cast hnth
    _ ≤ Y n := Nat.floor_le (by linarith)
    _ = (8 * X n) * Real.log (X n) := rfl
    _ ≤ (16 * (n : ℝ)) * Real.log ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right (by dsimp [X]; linarith) hlog0

private theorem sparse_primes (e : ℝ) (he : 0 < e) : ∀ᶠ n : ℕ in atTop,
    (Nat.primeCounting n : ℝ) ≤ e * (n : ℝ) := by
  let X : ℕ → ℝ := fun n => n
  have hX : Tendsto X atTop atTop := tendsto_natCast_atTop_atTop
  have hl := Real.tendsto_log_atTop.comp hX
  filter_upwards [hX.eventually (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num)),
    hl.eventually_ge_atTop ((Real.log 4 + 1) / e), hl.eventually_ge_atTop 1] with n hn h₁ h₂
  change (Nat.primeCounting ⌊(n : ℝ)⌋₊ : ℝ) ≤ (Real.log 4 + 1) * (n : ℝ) / Real.log (n : ℝ) at hn
  rw [Nat.floor_natCast] at hn
  have hlog : 0 < Real.log (n : ℝ) := by change 1 ≤ Real.log (n : ℝ) at h₂; linarith
  have hconst := (div_le_iff₀ he).mp h₁
  refine hn.trans ((div_le_iff₀ hlog).mpr ?_)
  calc
    (Real.log 4 + 1) * (n : ℝ) ≤ (Real.log (n : ℝ) * e) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hconst (Nat.cast_nonneg _)
    _ = e * (n : ℝ) * Real.log (n : ℝ) := by ring

private theorem smooth_count_bound (C : ℝ) (hC : 0 < C)
    (hPrime : ∀ᶠ N : ℕ in atTop, (p N : ℝ) ≤ 16 * (N : ℝ) * Real.log ((N : ℝ) + 1))
    (hSparse : ∀ e : ℝ, 0 < e → ∀ᶠ n : ℕ in atTop, (Nat.primeCounting n : ℝ) ≤ e * n) :
    ∀ᶠ N : ℕ in atTop, ((Nat.smoothNumbersUpTo (p N) (cutoff C N)).card : ℝ) ≤
      ((N : ℝ) + 1) ^ (7 / 8 : ℝ) := by
  let δ := (4 * (C + 1) * Real.log 2)⁻¹
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcut : Tendsto (cutoff C) atTop atTop := by
    exact tendsto_nat_ceil_atTop.comp ((tendsto_const_mul_atTop_of_pos hC).mpr log_succ_tendsto)
  have hlog := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)
  filter_upwards [hPrime, hcut.eventually (hSparse δ hδ), log_succ_tendsto.eventually_ge_atTop 1,
    cast_succ_tendsto.eventually (hlog.bound (show (0 : ℝ) < 1 / 16 by norm_num))] with N hp hs hL hlg
  let x := (N : ℝ) + 1
  have hx : 0 < x := by dsimp [x]; positivity
  change 1 ≤ Real.log x at hL
  change (p N : ℝ) ≤ 16 * (N : ℝ) * Real.log x at hp
  have hK : (cutoff C N : ℝ) ≤ (C + 1) * Real.log x := by
    have hceil := Nat.ceil_lt_add_one (mul_nonneg hC.le (by linarith : 0 ≤ Real.log x))
    change (⌈C * Real.log x⌉₊ : ℝ) < C * Real.log x + 1 at hceil
    change (⌈C * Real.log x⌉₊ : ℝ) ≤ (C + 1) * Real.log x
    linarith
  have hpc : (Nat.primeCounting' (cutoff C N) : ℝ) * Real.log 2 ≤ (1 / 4 : ℝ) * Real.log x := by
    have hpc1 : Nat.primeCounting' (cutoff C N) ≤ Nat.primeCounting (cutoff C N) :=
      Nat.monotone_primeCounting' (Nat.le_succ _)
    calc
      _ ≤ (δ * ((C + 1) * Real.log x)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right
          ((Nat.cast_le.mpr hpc1).trans (hs.trans (mul_le_mul_of_nonneg_left hK hδ.le))) hlog2.le
      _ = _ := by
        dsimp [δ]
        have hC1 : C + 1 ≠ 0 := by linarith
        field_simp [hC1, hlog2.ne']
  have hpow : (2 : ℝ) ^ (cutoff C N).primesBelow.card ≤ x ^ (1 / 4 : ℝ) := by
    rw [Nat.primesBelow_card_eq_primeCounting', ← Real.rpow_natCast,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hx]
    apply Real.exp_le_exp.mpr
    linarith only [hpc, mul_comm (Real.log 2) (Nat.primeCounting' (cutoff C N) : ℝ),
      mul_comm (Real.log x) (1 / 4)]
  have hlogx : 16 * Real.log x ≤ x ^ (1 / 4 : ℝ) := by
    change ‖Real.log x‖ ≤ (1 / 16 : ℝ) * ‖x ^ (1 / 4 : ℝ)‖ at hlg
    simp only [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Real.log x),
      abs_of_nonneg (Real.rpow_nonneg hx.le _)] at hlg
    linarith
  have hroot : ((p N).sqrt : ℝ) ≤ x ^ (5 / 8 : ℝ) := by
    have hP : (p N : ℝ) ≤ x ^ (5 / 4 : ℝ) := by
      calc
        _ ≤ 16 * (N : ℝ) * Real.log x := hp
        _ ≤ 16 * x * Real.log x := by
          apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ Real.log x)
          dsimp [x]
          linarith
        _ = x * (16 * Real.log x) := by ring
        _ ≤ x * x ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left hlogx hx.le
        _ = _ := by
          rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add hx, Real.rpow_one]
    refine Real.nat_sqrt_le_real_sqrt.trans ((Real.sqrt_le_sqrt hP).trans_eq ?_)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
    norm_num
  calc
    _ ≤ (2 : ℝ) ^ (cutoff C N).primesBelow.card * ((p N).sqrt : ℝ) := by
      exact_mod_cast Nat.smoothNumbersUpTo_card_le (p N) (cutoff C N)
    _ ≤ x ^ (1 / 4 : ℝ) * x ^ (5 / 8 : ℝ) :=
      mul_le_mul hpow hroot (Nat.cast_nonneg _) (Real.rpow_nonneg hx.le _)
    _ = _ := by rw [← Real.rpow_add hx]; norm_num [x]

private theorem small_power_linear (e : ℝ) (he : 0 < e) :
    ∀ᶠ N : ℕ in atTop, ((N : ℝ) + 1) ^ (7 / 8 : ℝ) ≤ (e / 4) * (N : ℝ) := by
  have ht := tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 8 by norm_num)
  have he8 : (0 : ℝ) < e / 8 := by positivity
  filter_upwards [cast_succ_tendsto.eventually (ht.eventually (gt_mem_nhds he8)),
    eventually_ge_atTop 1] with N hN hn
  let x := (N : ℝ) + 1
  have hx : 0 < x := by dsimp [x]; positivity
  change x ^ (-(1 / 8 : ℝ)) < e / 8 at hN
  have hsum : x ≤ 2 * (N : ℝ) := by
    have h : (1 : ℝ) ≤ N := by exact_mod_cast hn
    dsimp [x]; linarith
  change x ^ (7 / 8 : ℝ) ≤ _
  calc
    x ^ (7 / 8 : ℝ) = x * x ^ (-(1 / 8 : ℝ)) := by
      rw [show (7 / 8 : ℝ) = 1 + -(1 / 8) by norm_num, Real.rpow_add hx, Real.rpow_one]
    _ ≤ x * (e / 8) := mul_le_mul_of_nonneg_left hN.le hx.le
    _ ≤ (2 * (N : ℝ)) * (e / 8) := mul_le_mul_of_nonneg_right hsum he8.le
    _ = _ := by ring

theorem density_zero
    (hPrime : ∀ᶠ N : ℕ in atTop, (p N : ℝ) ≤ 16 * (N : ℝ) * Real.log ((N : ℝ) + 1))
    (hSparse : ∀ e : ℝ, 0 < e → ∀ᶠ n : ℕ in atTop, (Nat.primeCounting n : ℝ) ≤ e * n) :
    { r : ℕ | 1 ≤ (Finset.Ioo (r.nth Nat.Prime) (r.succ.nth Nat.Prime) |>.filter
      (fun m => m.maxPrimeFac < r.succ.nth Nat.Prime - r.nth Nat.Prime)).card }.HasDensity 0 := by
  classical
  have heq : { r : ℕ | 1 ≤ (Finset.Ioo (r.nth Nat.Prime) (r.succ.nth Nat.Prime) |>.filter
      (fun m => m.maxPrimeFac < r.succ.nth Nat.Prime - r.nth Nat.Prime)).card } =
      {r : ℕ | exceptional r} := by
    ext r
    change 0 < (Finset.Ioo (p r) (p (r+1)) |>.filter
      (fun m => m.maxPrimeFac < gap r)).card ↔ exceptional r
    rw [Finset.card_pos]
    simp [Finset.Nonempty, exceptional, Finset.mem_filter, Finset.mem_Ioo, and_assoc]
  rw [heq, Set.HasDensity, Metric.tendsto_nhds]
  intro e he
  let C := 64 / e
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [hPrime, smooth_count_bound C hC hPrime hSparse, small_power_linear e he,
    log_succ_tendsto.eventually_ge_atTop 1, eventually_ge_atTop 1] with N hp hs hg hlog hN
  let B := cutoff C N
  have hBN : C * Real.log ((N : ℝ) + 1) ≤ (B : ℝ) := Nat.le_ceil _
  have hL := large_gap_count N B
  let L := (range N).filter (fun r => B ≤ gap r)
  have hLp : C * (L.card : ℝ) ≤ 16 * (N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hBN (Nat.cast_nonneg L.card)
    have hc : (C * (L.card : ℝ)) * Real.log ((N : ℝ) + 1) ≤
        (16 * (N : ℝ)) * Real.log ((N : ℝ) + 1) := by
      calc
        _ = (C * Real.log ((N : ℝ) + 1)) * (L.card : ℝ) := by ring
        _ ≤ (B : ℝ) * (L.card : ℝ) := hh
        _ ≤ (p N : ℝ) := hL
        _ ≤ _ := hp
    exact (mul_le_mul_iff_of_pos_right (by linarith : 0 < Real.log ((N : ℝ) + 1))).mp hc
  have hLc : (L.card : ℝ) ≤ (e / 4) * (N : ℝ) := by
    have hCE : (e / 4) * C = 16 := by
      dsimp [C]
      field_simp
      norm_num
    apply (mul_le_mul_iff_of_pos_left hC).mp
    calc
      C * (L.card : ℝ) ≤ 16 * (N : ℝ) := hLp
      _ = ((e / 4) * C) * (N : ℝ) := by rw [hCE]
      _ = C * ((e / 4) * (N : ℝ)) := by ring
  have hnum : (({r : ℕ | exceptional r} ∩ Set.univ) ∩ Set.Iio N).ncard =
      ((range N).filter exceptional).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext r
    simp [Finset.mem_range, and_comm]
  have hden : (Set.univ ∩ Set.Iio N).ncard = N := by
    rw [Set.univ_inter, show Set.Iio N = ((range N : Finset ℕ) : Set ℕ) by ext; simp]
    simp
  have hcount := exceptional_count N B
  have hcount' : (((range N).filter exceptional).card : ℝ) ≤ (e / 2) * (N : ℝ) := by
    change ((Nat.smoothNumbersUpTo (p N) B).card : ℝ) ≤ ((N : ℝ) + 1) ^ (7 / 8 : ℝ) at hs
    exact (Nat.cast_le.mpr hcount).trans (by push_cast; linarith [hLc, hs.trans hg])
  rw [Real.dist_eq, sub_zero]
  change |((((({r : ℕ | exceptional r} ∩ Set.univ) ∩ Set.Iio N).ncard : ℕ) : ℝ) /
    ((Set.univ ∩ Set.Iio N).ncard : ℝ))| < e
  rw [hnum, hden, abs_of_nonneg (by positivity)]
  have hNZ : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (div_lt_iff₀ hNZ).mpr
  exact hcount'.trans_lt (mul_lt_mul_of_pos_right (by linarith) hNZ)

end OMA.SmoothPrimeGaps


theorem OMA.solution : type_of% @Erdos932.erdos_932.variants.one_le :=
  OMA.SmoothPrimeGaps.density_zero OMA.SmoothPrimeGaps.prime_index_bound
    OMA.SmoothPrimeGaps.sparse_primes
