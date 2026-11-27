import FormalConjectures.OptimizationConstants.«7a»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Proof of `Constant7a.c7a_le_42`

We prove that the irrationality exponent of `π` is at most `42`, following Beukers's (1979)
elementary proof for `ζ(2) = π² / 6` combined with Chebyshev's (1852) elementary bound on
`lcm(1, ..., n)`.
-/

-- Problem: Tao's Optimization Constant 7a / The Irrationality Measure of $\pi$ — c7a le 42
-- Upstream: formal-conjectures FormalConjectures/OptimizationConstants/7a.lean:121 (declaration Constant7a.c7a_le_42)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace PiIrrationality42

open Real Finset BigOperators Filter MeasureTheory intervalIntegral
open scoped Nat Topology

/- ### Section 1: Elementary Chebyshev bound on `Nat.lcmUpto` -/

private noncomputable def chebT (x : ℝ) : ℝ :=
  ∑ k ∈ Icc 1 ⌊x⌋₊, Real.log k

private lemma chebT_eq_sum_psi (x : ℝ) :
    chebT x = ∑ m ∈ Icc 1 ⌊x⌋₊, Chebyshev.psi (x / m) := by
  unfold chebT
  have h1 : ∀ k ∈ Icc 1 ⌊x⌋₊,
      Real.log (k : ℝ) = ∑ d ∈ k.divisors, ArithmeticFunction.vonMangoldt d :=
    fun k _ => (ArithmeticFunction.vonMangoldt_sum).symm
  rw [sum_congr rfl h1]
  have hswap :
      ∑ k ∈ Icc 1 ⌊x⌋₊, ∑ d ∈ k.divisors, ArithmeticFunction.vonMangoldt d =
      ∑ m ∈ Icc 1 ⌊x⌋₊, ∑ d ∈ Icc 1 (⌊x⌋₊ / m), ArithmeticFunction.vonMangoldt d := by
    rw [sum_sigma' (Icc 1 ⌊x⌋₊) (fun k => k.divisors)
          (fun _ d => ArithmeticFunction.vonMangoldt d),
        sum_sigma' (Icc 1 ⌊x⌋₊) (fun m => Icc 1 (⌊x⌋₊ / m))
          (fun _ d => ArithmeticFunction.vonMangoldt d)]
    refine sum_bij (fun p _ => ⟨p.1 / p.2, p.2⟩) ?_ ?_ ?_ ?_
    · rintro ⟨k, d⟩ hp
      simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at hp ⊢
      obtain ⟨⟨hk1, hkx⟩, hdk, hk0⟩ := hp
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdk (by omega)
      have hqpos : 1 ≤ k / d :=
        (Nat.le_div_iff_mul_le hdpos).2 (by simpa using Nat.le_of_dvd (by omega) hdk)
      have hqx : k / d ≤ ⌊x⌋₊ := (Nat.div_le_self k d).trans hkx
      refine ⟨⟨hqpos, hqx⟩, hdpos, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega)]
      have hmul : d * (k / d) = k := Nat.mul_div_cancel' hdk
      omega
    · rintro ⟨k₁, d₁⟩ hp₁ ⟨k₂, d₂⟩ hp₂ h
      simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at hp₁ hp₂
      simp only [Sigma.mk.injEq, heq_eq_eq] at h
      obtain ⟨hq, hd⟩ := h
      subst hd
      have hk1 : k₁ = d₁ * (k₁ / d₁) := (Nat.mul_div_cancel' hp₁.2.1).symm
      have hk2 : k₂ = d₁ * (k₂ / d₁) := (Nat.mul_div_cancel' hp₂.2.1).symm
      ext
      · rw [hk1, hk2, hq]
      · rfl
    · rintro ⟨m, d⟩ hp
      simp only [mem_sigma, mem_Icc, Nat.mem_divisors, exists_prop] at hp ⊢
      obtain ⟨⟨hm1, _⟩, ⟨hd1, hdm⟩⟩ := hp
      refine ⟨⟨m * d, d⟩, ⟨⟨?_, ?_⟩, dvd_mul_left d m, ?_⟩, ?_⟩
      · exact Nat.mul_pos (by omega) (by omega)
      · exact (Nat.le_div_iff_mul_le (by omega)).1 hdm |> fun h => by simpa [Nat.mul_comm] using h
      · exact Nat.mul_ne_zero (by omega) (by omega)
      · simp [Nat.mul_div_cancel _ (show 0 < d by omega)]
    · intro p _; rfl
  rw [hswap]
  refine sum_congr rfl fun m hm => ?_
  rw [Chebyshev.psi, Nat.floor_div_natCast]
  refine sum_congr ?_ fun _ _ => rfl
  ext d
  simp only [mem_Icc, mem_Ioc]
  omega

private lemma integral_log_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ t in a..b, Real.log t = (b * Real.log b - b) - (a * Real.log a - a) := by
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun u => u * Real.log u - u) (Real.log t) t := by
    intro t ht
    have htpos : 0 < t := by
      rcases Set.mem_uIcc.1 ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    have h1 := (hasDerivAt_id' t).fun_mul (Real.hasDerivAt_log htpos.ne')
    have h2 := h1.fun_sub (hasDerivAt_id' t)
    refine h2.congr_deriv ?_
    rw [one_mul, mul_inv_cancel₀ htpos.ne', add_sub_cancel_right]
  have hint : IntervalIntegrable Real.log volume a b := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    have htpos : 0 < t := by
      rcases Set.mem_uIcc.1 ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    exact (Real.continuousAt_log htpos.ne').continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

private lemma sum_log_ge (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n + 1 ≤ ∑ k ∈ Icc 1 n, Real.log k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn0
    have hstep := ih hn1
    rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have hlog : ((n + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℕ) - (n + 1 : ℕ) -
        ((n : ℝ) * Real.log n - n) ≤ Real.log (n + 1 : ℕ) := by
      have hpos1 : (0 : ℝ) < n := Nat.cast_pos.2 hn1
      have hpos2 : (0 : ℝ) < (n + 1 : ℕ) := Nat.cast_pos.2 (by omega)
      rw [← integral_log_eq (n : ℝ) ((n + 1 : ℕ) : ℝ) hpos1 hpos2]
      calc ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), Real.log t
          ≤ ∫ _ in (n : ℝ)..((n + 1 : ℕ) : ℝ), Real.log ((n + 1 : ℕ) : ℝ) := by
            refine intervalIntegral.integral_mono_on (by push_cast; linarith) ?_
              intervalIntegrable_const ?_
            · refine ContinuousOn.intervalIntegrable fun t ht =>
                (Real.continuousAt_log (by
                  rcases Set.mem_uIcc.1 ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith)).continuousWithinAt
            · intro t ht
              exact Real.log_le_log (by linarith [ht.1]) ht.2
        _ = Real.log ((n + 1 : ℕ) : ℝ) := by simp
    linarith

private lemma sum_log_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, Real.log k ≤ (n : ℝ) * Real.log n - n + Real.log (n + 1) + 1 := by
  have h1 : ∑ k ∈ Icc 1 n, Real.log k ≤
      ((n + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℕ) - (n + 1 : ℕ) + 1 := by
    induction n with
    | zero => omega
    | succ n ih =>
      rcases eq_or_ne n 0 with rfl | hn0
      · simp only [Nat.reduceAdd, Icc_self, sum_singleton, Nat.cast_one, Real.log_one,
          Nat.cast_ofNat]
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
        rw [Real.log_div one_ne_zero (by norm_num), Real.log_one, zero_sub] at this
        linarith
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn0
      have hstep := ih hn1
      rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hlog : Real.log ((n + 1 : ℕ) : ℝ) ≤
          ((n + 2 : ℕ) : ℝ) * Real.log (n + 2 : ℕ) - (n + 2 : ℕ) -
          (((n + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℕ) - (n + 1 : ℕ)) := by
        have hpos1 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
        have hpos2 : (0 : ℝ) < (n + 2 : ℕ) := by positivity
        rw [← integral_log_eq ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ) hpos1 hpos2]
        calc Real.log ((n + 1 : ℕ) : ℝ)
            = ∫ _ in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ), Real.log ((n + 1 : ℕ) : ℝ) := by
              rw [intervalIntegral.integral_const, smul_eq_mul]
              push_cast
              ring
          _ ≤ ∫ t in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ), Real.log t := by
              refine intervalIntegral.integral_mono_on (by push_cast; linarith)
                intervalIntegrable_const ?_ ?_
              · refine ContinuousOn.intervalIntegrable fun t ht =>
                  (Real.continuousAt_log (by
                    rcases Set.mem_uIcc.1 ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith)).continuousWithinAt
              · intro t ht
                exact Real.log_le_log hpos1 ht.1
      have hcast : ((n + 1 + 1 : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast]
      linarith
  have h2 : (n : ℝ) * (Real.log (n + 1) - Real.log n) ≤ 1 := by
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [← Real.log_div (by positivity) hnpos.ne']
    have hle := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
    calc (n : ℝ) * Real.log (((n : ℝ) + 1) / n)
        ≤ (n : ℝ) * (((n : ℝ) + 1) / n - 1) := mul_le_mul_of_nonneg_left hle hnpos.le
      _ = 1 := by field_simp [hnpos.ne']; ring
  push_cast at h1
  linarith

private lemma abs_chebT_sub_le (x : ℝ) (hx : 0 ≤ x) :
    |chebT x - (x * Real.log x - x)| ≤ Real.log (x + 1) + 1 := by
  by_cases hx1 : x < 1
  · have hfl : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.2 hx1
    have hT : chebT x = 0 := by simp [chebT, hfl]
    rw [hT, zero_sub, abs_neg]
    have hnonpos : x * Real.log x - x ≤ 0 := by
      rcases eq_or_lt_of_le hx with rfl | hxpos
      · simp
      have hlog : Real.log x ≤ 0 := Real.log_nonpos hx hx1.le
      nlinarith
    have hge : -1 ≤ x * Real.log x - x := by
      rcases eq_or_lt_of_le hx with rfl | hxpos
      · simp
      have hlog : Real.log x ≥ 1 - 1 / x := by
        have := Real.log_le_sub_one_of_pos (show 0 < x⁻¹ by positivity)
        rw [Real.log_inv] at this
        linarith [show x⁻¹ = 1 / x by rw [one_div]]
      have hmul : x * (1 - 1 / x) ≤ x * Real.log x :=
        mul_le_mul_of_nonneg_left hlog hx
      have hsimp : x * (1 - 1 / x) = x - 1 := by field_simp [hxpos.ne']
      linarith
    have hlog1 : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
    rw [abs_le]
    constructor <;> linarith
  · push Not at hx1
    set n := ⌊x⌋₊
    have hn1 : 1 ≤ n := (Nat.one_le_floor_iff x).2 hx1
    have hnx : (n : ℝ) ≤ x := Nat.floor_le hx
    have hxlt : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
    have hmono : (n : ℝ) * Real.log n - n ≤ x * Real.log x - x := by
      have h := integral_log_eq (n : ℝ) x hnpos (by linarith)
      have hnn : 0 ≤ ∫ t in (n : ℝ)..x, Real.log t :=
        intervalIntegral.integral_nonneg hnx fun t ht => Real.log_nonneg (by
          have : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn1
          linarith [ht.1])
      linarith
    have hdiff : (x * Real.log x - x) - ((n : ℝ) * Real.log n - n) ≤ Real.log (x + 1) := by
      have h := integral_log_eq (n : ℝ) x hnpos (by linarith)
      rw [← h]
      calc ∫ t in (n : ℝ)..x, Real.log t
          ≤ ∫ _ in (n : ℝ)..x, Real.log (x + 1) := by
            refine intervalIntegral.integral_mono_on hnx ?_ intervalIntegrable_const ?_
            · refine ContinuousOn.intervalIntegrable fun t ht =>
                (Real.continuousAt_log (by
                  rcases Set.mem_uIcc.1 ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith)).continuousWithinAt
            · intro t ht
              exact Real.log_le_log (by linarith [ht.1]) (by linarith [ht.2])
        _ = (x - n) * Real.log (x + 1) := by simp
        _ ≤ 1 * Real.log (x + 1) := by
            gcongr
            · exact Real.log_nonneg (by linarith)
            · linarith
        _ = Real.log (x + 1) := one_mul _
    have hlo := sum_log_ge n hn1
    have hhi := sum_log_le n hn1
    have hlogn : Real.log ((n : ℝ) + 1) ≤ Real.log (x + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    unfold chebT
    rw [abs_le]
    constructor <;> linarith

private noncomputable def chebA : ℝ :=
  Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 - Real.log 30 / 30

private noncomputable def chebE (x : ℝ) : ℝ :=
  chebT x - chebT (x / 2) - chebT (x / 3) - chebT (x / 5) + chebT (x / 30)

private lemma abs_chebE_sub_le (x : ℝ) (hx : 0 ≤ x) :
    |chebE x - chebA * x| ≤ 5 * (Real.log (x + 1) + 1) := by
  have hmain :
      (x * Real.log x - x) -
      ((x / 2) * Real.log (x / 2) - x / 2) -
      ((x / 3) * Real.log (x / 3) - x / 3) -
      ((x / 5) * Real.log (x / 5) - x / 5) +
      ((x / 30) * Real.log (x / 30) - x / 30) = chebA * x := by
    rcases eq_or_lt_of_le hx with rfl | hxpos
    · simp
    rw [Real.log_div hxpos.ne' (by norm_num),
        Real.log_div hxpos.ne' (by norm_num),
        Real.log_div hxpos.ne' (by norm_num),
        Real.log_div hxpos.ne' (by norm_num)]
    unfold chebA
    ring
  have h1 := abs_chebT_sub_le x hx
  have h2 := abs_chebT_sub_le (x / 2) (by positivity)
  have h3 := abs_chebT_sub_le (x / 3) (by positivity)
  have h5 := abs_chebT_sub_le (x / 5) (by positivity)
  have h30 := abs_chebT_sub_le (x / 30) (by positivity)
  have hl2 : Real.log (x / 2 + 1) ≤ Real.log (x + 1) := Real.log_le_log (by positivity) (by linarith)
  have hl3 : Real.log (x / 3 + 1) ≤ Real.log (x + 1) := Real.log_le_log (by positivity) (by linarith)
  have hl5 : Real.log (x / 5 + 1) ≤ Real.log (x + 1) := Real.log_le_log (by positivity) (by linarith)
  have hl30 : Real.log (x / 30 + 1) ≤ Real.log (x + 1) := Real.log_le_log (by positivity) (by linarith)
  rw [abs_le] at h1 h2 h3 h5 h30 ⊢
  unfold chebE
  constructor <;> linarith

private def chebCoeff (m : ℕ) : ℤ :=
  1 - (if 2 ∣ m then 1 else 0) - (if 3 ∣ m then 1 else 0) -
    (if 5 ∣ m then 1 else 0) + (if 30 ∣ m then 1 else 0)

private def chebPartSum (k : ℕ) : ℤ :=
  ∑ m ∈ Icc 1 k, chebCoeff m

private lemma chebCoeff_add_30 (m : ℕ) : chebCoeff (m + 30) = chebCoeff m := by
  unfold chebCoeff
  have h2 : (2 ∣ m + 30) ↔ (2 ∣ m) := by omega
  have h3 : (3 ∣ m + 30) ↔ (3 ∣ m) := by omega
  have h5 : (5 ∣ m + 30) ↔ (5 ∣ m) := by omega
  have h30 : (30 ∣ m + 30) ↔ (30 ∣ m) := by omega
  simp [h2, h3, h5, h30]

private lemma chebPartSum_30 : chebPartSum 30 = 0 := by decide

private lemma chebPartSum_add_30 (k : ℕ) : chebPartSum (k + 30) = chebPartSum k := by
  induction k with
  | zero => exact chebPartSum_30
  | succ k ih =>
    unfold chebPartSum at ih ⊢
    rw [show k + 1 + 30 = (k + 30) + 1 by omega]
    rw [sum_Icc_succ_top (by omega : 1 ≤ k + 30 + 1),
        sum_Icc_succ_top (by omega : 1 ≤ k + 1), ih, chebCoeff_add_30]

private lemma chebPartSum_mod (k : ℕ) : chebPartSum k = chebPartSum (k % 30) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < 30
    · rw [Nat.mod_eq_of_lt hk]
    · have hk30 : k = (k - 30) + 30 := by omega
      conv_lhs => rw [hk30]
      rw [chebPartSum_add_30, ih (k - 30) (by omega)]
      congr 1
      omega

private lemma chebPartSum_bounds (k : ℕ) : 0 ≤ chebPartSum k ∧ chebPartSum k ≤ 1 := by
  rw [chebPartSum_mod]
  have hlt : k % 30 < 30 := Nat.mod_lt k (by omega)
  have hfin : ∀ r : Fin 30, 0 ≤ chebPartSum r.1 ∧ chebPartSum r.1 ≤ 1 := by decide
  exact hfin ⟨k % 30, hlt⟩

private lemma chebE_eq_sum_psi (x : ℝ) (N : ℕ) (hN : ⌊x⌋₊ ≤ N) :
    chebE x = ∑ m ∈ Icc 1 N, (chebCoeff m : ℝ) * Chebyshev.psi (x / m) := by
  have hT_ext (y : ℝ) (M : ℕ) (hM : ⌊y⌋₊ ≤ M) :
      chebT y = ∑ m ∈ Icc 1 M, Chebyshev.psi (y / m) := by
    rw [chebT_eq_sum_psi]
    refine sum_subset (Icc_subset_Icc_right hM) fun m hm hnot => ?_
    simp only [mem_Icc] at hm hnot
    have hgt : ⌊y⌋₊ < m := by omega
    apply Chebyshev.psi_eq_zero_of_lt_two
    have hy : y < m := by
      by_cases hy0 : 0 ≤ y
      · exact (Nat.lt_floor_add_one y).trans_le (by exact_mod_cast hgt)
      · linarith [show (1 : ℝ) ≤ m by exact_mod_cast hm.1]
    have hdiv : y / (m : ℝ) < 1 := (div_lt_one (by exact_mod_cast hm.1)).2 hy
    linarith
  have hdiv_sum (d : ℕ) (hd : 1 ≤ d) :
      chebT (x / d) = ∑ m ∈ Icc 1 N, (if d ∣ m then (1 : ℝ) else 0) * Chebyshev.psi (x / m) := by
    have hfl : ⌊x / (d : ℝ)⌋₊ ≤ N / d := by
      rw [Nat.floor_div_natCast]
      exact Nat.div_le_div_right hN
    rw [hT_ext (x / d) (N / d) hfl]
    have hbij :
        ∑ k ∈ Icc 1 (N / d), Chebyshev.psi (x / d / k) =
        ∑ m ∈ (Icc 1 N).filter (d ∣ ·), Chebyshev.psi (x / m) := by
      refine sum_bij (fun k _ => d * k) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [mem_Icc, mem_filter] at hk ⊢
        refine ⟨⟨Nat.mul_pos hd hk.1, ?_⟩, dvd_mul_right d k⟩
        rw [Nat.mul_comm]
        exact (Nat.le_div_iff_mul_le hd).1 hk.2
      · intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hd h
      · intro m hm
        simp only [mem_filter, mem_Icc] at hm
        obtain ⟨⟨hm1, hmN⟩, k, rfl⟩ := hm
        have hk1 : 1 ≤ k := by
          by_contra hk0; push Not at hk0; interval_cases k; simp at hm1
        refine ⟨k, mem_Icc.2 ⟨hk1, (Nat.le_div_iff_mul_le hd).2 (by rw [Nat.mul_comm]; exact hmN)⟩, rfl⟩
      · intro k _
        rw [div_div, Nat.cast_mul]
    rw [hbij, sum_filter]
    refine sum_congr rfl fun m _ => by split_ifs <;> simp
  have h2 := hdiv_sum 2 (by omega); norm_num at h2
  have h3 := hdiv_sum 3 (by omega); norm_num at h3
  have h5 := hdiv_sum 5 (by omega); norm_num at h5
  have h30 := hdiv_sum 30 (by omega); norm_num at h30
  unfold chebE
  rw [hT_ext x N hN, h2, h3, h5, h30]
  rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  unfold chebCoeff
  push_cast
  split_ifs <;> ring

private lemma sum_by_parts_cheb (f : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ Icc 1 N, (chebCoeff m : ℝ) * f m =
    (chebPartSum N : ℝ) * f N +
      ∑ m ∈ Icc 1 (N - 1), (chebPartSum m : ℝ) * (f m - f (m + 1)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases eq_or_ne N 0 with rfl | hN0
    · simp [chebPartSum, chebCoeff]
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 hN0
    have hstep := ih hN1
    rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1), hstep]
    have hsub : N + 1 - 1 = N := by omega
    rw [hsub]
    have hps : (chebPartSum (N + 1) : ℝ) = (chebPartSum N : ℝ) + (chebCoeff (N + 1) : ℝ) := by
      unfold chebPartSum
      rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      push_cast
      rfl
    rw [hps]
    rw [show Icc 1 N = insert N (Icc 1 (N - 1)) from by
      ext k; simp only [mem_Icc, mem_insert]; omega]
    rw [sum_insert (by simp only [mem_Icc]; omega)]
    ring

private lemma chebE_le_psi (x : ℝ) (hx : 0 ≤ x) :
    chebE x ≤ Chebyshev.psi x := by
  let N := max ⌊x⌋₊ 1
  rw [chebE_eq_sum_psi x N (le_max_left _ _),
      sum_by_parts_cheb (fun m => Chebyshev.psi (x / m)) N (le_max_right _ _)]
  have h1 : (chebPartSum N : ℝ) * Chebyshev.psi (x / N) ≤ 1 * Chebyshev.psi (x / N) := by
    have hb : (chebPartSum N : ℝ) ≤ 1 := by exact_mod_cast (chebPartSum_bounds N).2
    exact mul_le_mul_of_nonneg_right hb (Chebyshev.psi_nonneg _)
  have h2 : ∑ m ∈ Icc 1 (N - 1), (chebPartSum m : ℝ) *
      (Chebyshev.psi (x / m) - Chebyshev.psi (x / (m + 1 : ℕ))) ≤
      ∑ m ∈ Icc 1 (N - 1), 1 * (Chebyshev.psi (x / m) - Chebyshev.psi (x / (m + 1 : ℕ))) := by
    refine sum_le_sum fun m hm => ?_
    have hb : (chebPartSum m : ℝ) ≤ 1 := by exact_mod_cast (chebPartSum_bounds m).2
    have hdiff : 0 ≤ Chebyshev.psi (x / m) - Chebyshev.psi (x / (m + 1 : ℕ)) := by
      have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (mem_Icc.1 hm).1
      have hle : x / ((m + 1 : ℕ) : ℝ) ≤ x / m := by
        gcongr; exact_mod_cast Nat.le_succ m
      linarith [Chebyshev.psi_mono hle]
    exact mul_le_mul_of_nonneg_right hb hdiff
  have htele_gen : ∀ M : ℕ, 1 ≤ M →
      Chebyshev.psi (x / M) +
        ∑ m ∈ Icc 1 (M - 1), (Chebyshev.psi (x / m) - Chebyshev.psi (x / (m + 1 : ℕ))) =
      Chebyshev.psi x := by
    intro M hM
    induction M with
    | zero => omega
    | succ k ih =>
      rcases eq_or_ne k 0 with rfl | hk0
      · simp
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
      have hstep := ih hk1
      have hsub : k + 1 - 1 = k := by omega
      rw [hsub]
      rw [show Icc 1 k = insert k (Icc 1 (k - 1)) from by
        ext j; simp only [mem_Icc, mem_insert]; omega]
      rw [sum_insert (by simp only [mem_Icc]; omega)]
      linarith
  have htele := htele_gen N (le_max_right _ _)
  simp only [one_mul] at h1 h2
  linarith

private lemma psi_sub_le_chebE (x : ℝ) (hx : 0 ≤ x) :
    Chebyshev.psi x - Chebyshev.psi (x / 6) + Chebyshev.psi (x / 7) - Chebyshev.psi (x / 10) ≤
      chebE x := by
  let N := max ⌊x⌋₊ 10
  rw [chebE_eq_sum_psi x N (le_max_left _ _),
      sum_by_parts_cheb (fun m => Chebyshev.psi (x / m)) N (by omega)]
  have htail1 : 0 ≤ (chebPartSum N : ℝ) * Chebyshev.psi (x / N) := by
    have hb : (0 : ℝ) ≤ chebPartSum N := by exact_mod_cast (chebPartSum_bounds N).1
    exact mul_nonneg hb (Chebyshev.psi_nonneg _)
  have hsub : Icc 1 9 ⊆ Icc 1 (N - 1) := Icc_subset_Icc_right (by omega)
  have htail2 :
      ∑ m ∈ Icc 1 9, (chebPartSum m : ℝ) *
        (Chebyshev.psi (x / m) - Chebyshev.psi (x / (m + 1 : ℕ))) ≤
      ∑ m ∈ Icc 1 (N - 1), (chebPartSum m : ℝ) *
        (Chebyshev.psi (x / m) - Chebyshev.psi (x / (m + 1 : ℕ))) := by
    refine sum_le_sum_of_subset_of_nonneg hsub fun m hm _ => ?_
    have hb : (0 : ℝ) ≤ chebPartSum m := by exact_mod_cast (chebPartSum_bounds m).1
    have hdiff : 0 ≤ Chebyshev.psi (x / m) - Chebyshev.psi (x / (m + 1 : ℕ)) := by
      have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (mem_Icc.1 hm).1
      have hle : x / ((m + 1 : ℕ) : ℝ) ≤ x / m := by
        gcongr; exact_mod_cast Nat.le_succ m
      linarith [Chebyshev.psi_mono hle]
    exact mul_nonneg hb hdiff
  have h9 :
      ∑ m ∈ Icc 1 9, (chebPartSum m : ℝ) *
        (Chebyshev.psi (x / m) - Chebyshev.psi (x / (m + 1 : ℕ))) =
      Chebyshev.psi x - Chebyshev.psi (x / 6) + Chebyshev.psi (x / 7) - Chebyshev.psi (x / 10) := by
    have hvals :
        chebPartSum 1 = 1 ∧ chebPartSum 2 = 1 ∧ chebPartSum 3 = 1 ∧
        chebPartSum 4 = 1 ∧ chebPartSum 5 = 1 ∧ chebPartSum 6 = 0 ∧
        chebPartSum 7 = 1 ∧ chebPartSum 8 = 1 ∧ chebPartSum 9 = 1 := by decide
    have hIcc : Icc 1 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
    rw [hIcc]
    simp only [sum_insert (show (1 : ℕ) ∉ ({2, 3, 4, 5, 6, 7, 8, 9} : Finset ℕ) by decide),
      sum_insert (show (2 : ℕ) ∉ ({3, 4, 5, 6, 7, 8, 9} : Finset ℕ) by decide),
      sum_insert (show (3 : ℕ) ∉ ({4, 5, 6, 7, 8, 9} : Finset ℕ) by decide),
      sum_insert (show (4 : ℕ) ∉ ({5, 6, 7, 8, 9} : Finset ℕ) by decide),
      sum_insert (show (5 : ℕ) ∉ ({6, 7, 8, 9} : Finset ℕ) by decide),
      sum_insert (show (6 : ℕ) ∉ ({7, 8, 9} : Finset ℕ) by decide),
      sum_insert (show (7 : ℕ) ∉ ({8, 9} : Finset ℕ) by decide),
      sum_insert (show (8 : ℕ) ∉ ({9} : Finset ℕ) by decide),
      sum_singleton, hvals.1, hvals.2.1, hvals.2.2.1, hvals.2.2.2.1,
      hvals.2.2.2.2.1, hvals.2.2.2.2.2.1, hvals.2.2.2.2.2.2.1, hvals.2.2.2.2.2.2.2.1,
      hvals.2.2.2.2.2.2.2.2]
    norm_num
    ring
  linarith

private lemma psi_le_cheb (x : ℝ) (hx : 0 ≤ x) :
    Chebyshev.psi x ≤ (90 / 77 : ℝ) * chebA * x + 120 * Real.sqrt x := by
  have hchebA_pos : 0 ≤ chebA := by
    have hlog30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
      rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
          Real.log_mul (by norm_num) (by norm_num)]
    unfold chebA
    rw [hlog30]
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    linarith
  suffices ∀ n : ℕ, ∀ y : ℝ, 0 ≤ y → ⌊y⌋₊ ≤ n →
      Chebyshev.psi y ≤ (90 / 77 : ℝ) * chebA * y + 120 * Real.sqrt y by
    exact this ⌊x⌋₊ x hx le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy hyn
    by_cases hy2 : y < 2
    · rw [Chebyshev.psi_eq_zero_of_lt_two hy2]
      positivity
    push Not at hy2
    have hEhi := (abs_le.1 (abs_chebE_sub_le y hy)).2
    have hE7lo := (abs_le.1 (abs_chebE_sub_le (y / 7) (by positivity))).1
    have hpsi7 : chebE (y / 7) ≤ Chebyshev.psi (y / 7) := chebE_le_psi (y / 7) (by positivity)
    have hmain := psi_sub_le_chebE y hy
    have hlog7 : Real.log (y / 7 + 1) ≤ Real.log (y + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog_sqrt : Real.log (y + 1) + 1 ≤ 3 * Real.sqrt y := by
      have h1 : Real.log (y + 1) = 2 * Real.log (Real.sqrt (y + 1)) := by
        rw [Real.log_sqrt (by linarith)]; ring
      have h2 : Real.log (Real.sqrt (y + 1)) ≤ Real.sqrt (y + 1) - 1 :=
        Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by linarith))
      have h3 : Real.sqrt (y + 1) ≤ Real.sqrt y + 1 := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ Real.sqrt y + 1)]
        apply Real.sqrt_le_sqrt
        nlinarith [Real.sq_sqrt hy, Real.sqrt_nonneg y]
      have h4 : 1 ≤ Real.sqrt y := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
      linarith
    have hfl6 : ⌊y / 6⌋₊ < n := by
      have : ⌊y / (6 : ℝ)⌋₊ < ⌊y⌋₊ := by
        rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Nat.floor_div_natCast]
        have : 2 ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy).2 hy2
        omega
      omega
    have hfl10 : ⌊y / 10⌋₊ < n := by
      have : ⌊y / (10 : ℝ)⌋₊ < ⌊y⌋₊ := by
        rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Nat.floor_div_natCast]
        have : 2 ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy).2 hy2
        omega
      omega
    have h6 := ih ⌊y / 6⌋₊ hfl6 (y / 6) (by positivity) le_rfl
    have h10 := ih ⌊y / 10⌋₊ hfl10 (y / 10) (by positivity) le_rfl
    have hsq6 : Real.sqrt (y / 6) ≤ (5 / 12 : ℝ) * Real.sqrt y := by
      rw [Real.sqrt_div hy]
      have h1 : (12 / 5 : ℝ) ≤ Real.sqrt 6 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      have h2 : 1 / Real.sqrt 6 ≤ 5 / 12 := by
        rw [div_le_div_iff₀ (Real.sqrt_pos.2 (by norm_num)) (by norm_num)]
        linarith
      calc Real.sqrt y / Real.sqrt 6 = (1 / Real.sqrt 6) * Real.sqrt y := by ring
        _ ≤ (5 / 12) * Real.sqrt y := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg y)
    have hsq10 : Real.sqrt (y / 10) ≤ (10 / 31 : ℝ) * Real.sqrt y := by
      rw [Real.sqrt_div hy]
      have h1 : (31 / 10 : ℝ) ≤ Real.sqrt 10 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      have h2 : 1 / Real.sqrt 10 ≤ 10 / 31 := by
        rw [div_le_div_iff₀ (Real.sqrt_pos.2 (by norm_num)) (by norm_num)]
        linarith
      calc Real.sqrt y / Real.sqrt 10 = (1 / Real.sqrt 10) * Real.sqrt y := by ring
        _ ≤ (10 / 31) * Real.sqrt y := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg y)
    have hsqrt_nn : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    linarith

private lemma chebA_bound : (90 / 77 : ℝ) * chebA < Real.log (59 / 20 : ℝ) := by
  have hlog30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num,
        Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num)]
  have hA : chebA = (1 / 30 : ℝ) * Real.log ((2 : ℝ) ^ 14 * (3 : ℝ) ^ 9 * (5 : ℝ) ^ 5) := by
    unfold chebA
    rw [hlog30,
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow]
    ring
  rw [hA]
  have hpow : (90 / 77 : ℝ) * ((1 / 30 : ℝ) * Real.log ((2 : ℝ) ^ 14 * 3 ^ 9 * 5 ^ 5)) =
      (1 / 77 : ℝ) * Real.log (((2 : ℝ) ^ 14 * 3 ^ 9 * 5 ^ 5) ^ 3) := by
    rw [Real.log_pow]; ring
  have hrhs : Real.log (59 / 20 : ℝ) = (1 / 77 : ℝ) * Real.log ((59 / 20 : ℝ) ^ 77) := by
    rw [Real.log_pow]; ring
  rw [hpow, hrhs]
  gcongr
  norm_num

private lemma lcmUpto_le :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (Nat.lcmUpto n : ℝ) ≤ C * (59 / 20 : ℝ) ^ n := by
  set ε : ℝ := Real.log (59 / 20 : ℝ) - (90 / 77 : ℝ) * chebA
  have hε : 0 < ε := sub_pos.2 chebA_bound
  refine ⟨Real.exp (3600 / ε), Real.exp_pos _, fun n => ?_⟩
  have hpsi : Real.log (Nat.lcmUpto n : ℝ) ≤ Real.log (Real.exp (3600 / ε) * (59 / 20 : ℝ) ^ n) := by
    rw [← Chebyshev.psi_eq_log_lcmUpto]
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow]
    have h1 := psi_le_cheb (n : ℝ) (Nat.cast_nonneg n)
    have hsq : 120 * Real.sqrt n ≤ ε * n + 3600 / ε := by
      have hsq_nn : 0 ≤ (Real.sqrt ε * Real.sqrt n - 60 / Real.sqrt ε) ^ 2 := sq_nonneg _
      have hε_sq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
      have hn_sq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
      have hε_pos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
      have hexp : (Real.sqrt ε * Real.sqrt n - 60 / Real.sqrt ε) ^ 2 =
          ε * n - 120 * Real.sqrt n + 3600 / ε := by
        rw [sub_sq, mul_pow, div_pow, hε_sq, hn_sq]
        have hcross : 2 * (Real.sqrt ε * Real.sqrt n) * (60 / Real.sqrt ε) =
            120 * Real.sqrt n := by
          field_simp [hε_pos.ne']
          ring
        linarith
      linarith
    have hε_def : (90 / 77 : ℝ) * chebA + ε = Real.log (59 / 20 : ℝ) := by
      dsimp [ε]; ring
    nlinarith
  have hpos1 : (0 : ℝ) < Nat.lcmUpto n := Nat.cast_pos.2 (Nat.lcmUpto_pos n)
  exact (Real.log_le_log_iff hpos1 (by positivity)).1 hpsi

/- ### Section 2: Beukers's Legendre Polynomials and Integration by Parts -/

private def beukersPoly (n : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ range (n + 1), ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).choose r : ℝ)) * x ^ r

private def beukersDeriv (n k : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ range (n + 1),
    ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).descFactorial k : ℝ)) * x ^ (n + r - k)

private lemma beukersDeriv_zero (n : ℕ) (x : ℝ) :
    beukersDeriv n 0 x = x ^ n * (1 - x) ^ n := by
  unfold beukersDeriv
  have hbin : (1 - x) ^ n = ∑ r ∈ range (n + 1), (-1 : ℝ) ^ r * (n.choose r : ℝ) * x ^ r := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine sum_congr rfl fun r _ => ?_
    rw [neg_eq_neg_one_mul, mul_pow, one_pow, mul_one]
    ring
  rw [hbin, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  simp only [Nat.descFactorial_zero, Nat.cast_one, mul_one, Nat.sub_zero, pow_add]
  ring

private lemma beukersDeriv_self (n : ℕ) (x : ℝ) :
    beukersDeriv n n x = (n ! : ℝ) * beukersPoly n x := by
  unfold beukersDeriv beukersPoly
  rw [mul_sum]
  refine sum_congr rfl fun r _ => ?_
  have hdesc : (n + r).descFactorial n = n ! * (n + r).choose r := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_symm_add]
  have hsub : n + r - n = r := Nat.add_sub_cancel_left n r
  rw [hdesc, hsub]
  push_cast
  ring

private lemma hasDerivAt_beukersDeriv (n k : ℕ) (_hk : k < n) (x : ℝ) :
    HasDerivAt (beukersDeriv n k) (beukersDeriv n (k + 1) x) x := by
  unfold beukersDeriv
  have hterm : ∀ r ∈ range (n + 1),
      HasDerivAt
        (fun t : ℝ => ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).descFactorial k : ℝ)) *
          t ^ (n + r - k))
        (((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).descFactorial (k + 1) : ℝ)) *
          x ^ (n + r - (k + 1))) x := by
    intro r _
    have hpow := (hasDerivAt_pow (n + r - k) x).const_mul
      ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).descFactorial k : ℝ))
    refine hpow.congr_deriv ?_
    have hsub : n + r - k - 1 = n + r - (k + 1) := by omega
    have hdesc : (n + r).descFactorial (k + 1) = (n + r - k) * (n + r).descFactorial k :=
      Nat.descFactorial_succ (n + r) k
    rw [hsub, hdesc]
    push_cast
    ring
  exact HasDerivAt.fun_sum hterm

private lemma beukersDeriv_eval_zero (n k : ℕ) (hk : k < n) :
    beukersDeriv n k 0 = 0 := by
  unfold beukersDeriv
  refine sum_eq_zero fun r _ => ?_
  have hne : n + r - k ≠ 0 := by omega
  rw [zero_pow hne, mul_zero]

private lemma beukersDeriv_symm (n k : ℕ) (hk : k ≤ n) (x : ℝ) :
    beukersDeriv n k (1 - x) = (-1 : ℝ) ^ k * beukersDeriv n k x := by
  induction k generalizing x with
  | zero =>
    simp only [pow_zero, one_mul, beukersDeriv_zero, sub_sub_cancel]
    ring
  | succ k ih =>
    have hkn : k < n := by omega
    have hfun : (fun t : ℝ => beukersDeriv n k (1 - t)) =
        (fun t : ℝ => (-1 : ℝ) ^ k * beukersDeriv n k t) :=
      funext fun t => ih (by omega) t
    have h1 : HasDerivAt (fun t : ℝ => beukersDeriv n k (1 - t))
        (beukersDeriv n (k + 1) (1 - x) * (-1)) x := by
      have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
        simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id' x)
      exact (hasDerivAt_beukersDeriv n k hkn (1 - x)).comp x hsub
    have h2 : HasDerivAt (fun t : ℝ => (-1 : ℝ) ^ k * beukersDeriv n k t)
        ((-1 : ℝ) ^ k * beukersDeriv n (k + 1) x) x :=
      (hasDerivAt_beukersDeriv n k hkn x).const_mul _
    rw [hfun] at h1
    have heq := h1.unique h2
    rw [pow_succ]
    linarith

private lemma beukersDeriv_eval_one (n k : ℕ) (hk : k < n) :
    beukersDeriv n k 1 = 0 := by
  have h := beukersDeriv_symm n k hk.le 0
  simp only [sub_zero, beukersDeriv_eval_zero n k hk, mul_zero] at h
  exact h

private lemma continuous_beukersDeriv (n k : ℕ) : Continuous (beukersDeriv n k) := by
  unfold beukersDeriv
  fun_prop

private lemma beukers_ibp (n : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    (-1 : ℝ) ^ n * ∫ x in (0 : ℝ)..1, beukersPoly n x / (1 - x * y) =
      ∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n * y ^ n / (1 - x * y) ^ (n + 1) := by
  have hden : ∀ x ∈ Set.uIcc (0 : ℝ) 1, 1 - x * y ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    have hxy : x * y ≤ y := by nlinarith [hx.1, hx.2]
    linarith
  have hstep : ∀ k ≤ n,
      ∫ x in (0 : ℝ)..1, beukersDeriv n n x / (1 - x * y) =
        (-1 : ℝ) ^ k * ∫ x in (0 : ℝ)..1,
          beukersDeriv n (n - k) x * ((k ! : ℝ) * y ^ k / (1 - x * y) ^ (k + 1)) := by
    intro k hk
    induction k with
    | zero =>
      simp [div_eq_mul_inv]
    | succ k ih =>
      have hk_le : k ≤ n := by omega
      rw [ih hk_le]
      set m := n - (k + 1)
      have hmn : m < n := by omega
      have hnk : n - k = m + 1 := by omega
      let u : ℝ → ℝ := beukersDeriv n m
      let u' : ℝ → ℝ := beukersDeriv n (m + 1)
      let v : ℝ → ℝ := fun x => (k ! : ℝ) * y ^ k / (1 - x * y) ^ (k + 1)
      let v' : ℝ → ℝ := fun x => ((k + 1)! : ℝ) * y ^ (k + 1) / (1 - x * y) ^ (k + 2)
      have hu : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt u (u' x) x :=
        fun x _ => hasDerivAt_beukersDeriv n m hmn x
      have hv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt v (v' x) x := by
        intro x hx
        have hne : 1 - x * y ≠ 0 := hden x hx
        have hlin : HasDerivAt (fun t : ℝ => 1 - t * y) (-y) x := by
          have := (hasDerivAt_id' x).mul_const y
          exact ((hasDerivAt_const x (1 : ℝ)).fun_sub this).congr_deriv (by ring)
        have hpow : HasDerivAt (fun t : ℝ => (1 - t * y) ^ (k + 1))
            ((k + 1 : ℕ) * (1 - x * y) ^ k * (-y)) x := by
          exact (hlin.fun_pow (k + 1)).congr_deriv (by simp)
        have hinv : HasDerivAt (fun t : ℝ => ((1 - t * y) ^ (k + 1))⁻¹)
            (-((k + 1 : ℕ) * (1 - x * y) ^ k * (-y)) / ((1 - x * y) ^ (k + 1)) ^ 2) x :=
          hpow.fun_inv (pow_ne_zero _ hne)
        have hmul : HasDerivAt (fun t : ℝ => (k ! : ℝ) * y ^ k * ((1 - t * y) ^ (k + 1))⁻¹)
            ((k ! : ℝ) * y ^ k * (-((k + 1 : ℕ) * (1 - x * y) ^ k * (-y)) /
              ((1 - x * y) ^ (k + 1)) ^ 2)) x :=
          hinv.const_mul ((k ! : ℝ) * y ^ k)
        have hv_eq : v = fun t : ℝ => (k ! : ℝ) * y ^ k * ((1 - t * y) ^ (k + 1))⁻¹ := by
          ext t; simp [v, div_eq_mul_inv]
        rw [hv_eq]
        refine hmul.congr_deriv ?_
        dsimp only [v']
        rw [Nat.factorial_succ]
        push_cast
        have hpow1 : ((1 - x * y) ^ (k + 1)) ^ 2 = (1 - x * y) ^ k * (1 - x * y) ^ (k + 2) := by
          rw [← pow_mul, ← pow_add]; congr 1; omega
        rw [hpow1]
        field_simp [hne, pow_ne_zero k hne, pow_ne_zero (k + 2) hne]
        ring
      have hu'int : IntervalIntegrable u' volume 0 1 :=
        (continuous_beukersDeriv n (m + 1)).intervalIntegrable 0 1
      have hv'int : IntervalIntegrable v' volume 0 1 := by
        refine ContinuousOn.intervalIntegrable fun x hx => ?_
        have hne : 1 - x * y ≠ 0 := hden x hx
        have hcont : ContinuousAt v' x := by
          dsimp [v']
          exact ContinuousAt.div continuousAt_const
            (((continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).pow _))
            (pow_ne_zero _ hne)
        exact hcont.continuousWithinAt
      have hibp := integral_mul_deriv_eq_deriv_mul hu hv hu'int hv'int
      have hu0 : u 0 = 0 := beukersDeriv_eval_zero n m hmn
      have hu1 : u 1 = 0 := beukersDeriv_eval_one n m hmn
      rw [hu0, hu1, zero_mul, zero_mul, sub_self] at hibp
      have hswap : ∫ x in (0 : ℝ)..1, u' x * v x = -(∫ x in (0 : ℝ)..1, u x * v' x) := by
        linarith
      rw [hnk]
      change (-1 : ℝ) ^ k * ∫ x in (0 : ℝ)..1, u' x * v x =
        (-1 : ℝ) ^ (k + 1) * ∫ x in (0 : ℝ)..1, u x * v' x
      rw [hswap, pow_succ]
      ring
  have hfinal := hstep n le_rfl
  simp only [Nat.sub_self, beukersDeriv_zero, beukersDeriv_self] at hfinal
  have hfac : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have hlhs : ∫ x in (0 : ℝ)..1, (n ! : ℝ) * beukersPoly n x / (1 - x * y) =
      (n ! : ℝ) * ∫ x in (0 : ℝ)..1, beukersPoly n x / (1 - x * y) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext x; ring
  have hrhs : ∫ x in (0 : ℝ)..1,
      x ^ n * (1 - x) ^ n * ((n ! : ℝ) * y ^ n / (1 - x * y) ^ (n + 1)) =
      (n ! : ℝ) * ∫ x in (0 : ℝ)..1,
        x ^ n * (1 - x) ^ n * y ^ n / (1 - x * y) ^ (n + 1) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext x; ring
  rw [hlhs, hrhs] at hfinal
  have hcancel : ∫ x in (0 : ℝ)..1, beukersPoly n x / (1 - x * y) =
      (-1 : ℝ) ^ n * ∫ x in (0 : ℝ)..1,
        x ^ n * (1 - x) ^ n * y ^ n / (1 - x * y) ^ (n + 1) := by
    apply mul_left_cancel₀ hfac
    linarith
  have hneg2 : (-1 : ℝ) ^ (2 * n) = 1 := by rw [pow_mul]; norm_num
  rw [hcancel, ← mul_assoc, ← pow_add, ← two_mul, hneg2, one_mul]

private lemma beukers_kernel_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    x * (1 - x) * y * (1 - y) / (1 - x * y) ≤ 451 / 5000 := by
  have hden : 0 < 1 - x * y := by nlinarith
  rw [div_le_iff₀ hden]
  set t := Real.sqrt (x * y)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht_sq : t ^ 2 = x * y := Real.sq_sqrt (mul_nonneg hx0 hy0)
  have ht1 : t ≤ 1 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hamgm : 2 * t ≤ x + y := by
    have hsq : 0 ≤ (Real.sqrt x - Real.sqrt y) ^ 2 := sq_nonneg _
    rw [sub_sq, Real.sq_sqrt hx0, Real.sq_sqrt hy0] at hsq
    have hmul : Real.sqrt x * Real.sqrt y = t := (Real.sqrt_mul hx0 y).symm
    linarith
  have hstep1 : x * (1 - x) * y * (1 - y) ≤ t ^ 2 * (1 - t) ^ 2 := by
    have h1 : x * (1 - x) * y * (1 - y) = t ^ 2 * (1 - (x + y) + t ^ 2) := by
      nlinarith [ht_sq]
    rw [h1]
    nlinarith [sq_nonneg t]
  have hstep2 : t ^ 2 * (1 - t) ^ 2 ≤ (451 / 5000 : ℝ) * (1 - t ^ 2) := by
    have hpoly : (451 / 5000 : ℝ) * (1 + t) - t ^ 2 * (1 - t) =
        (t - 309 / 500) ^ 2 * (t + 59 / 250) + (7 / 250000 : ℝ) * (1 - t) +
          (18968 / 500000000 : ℝ) := by ring
    have hge : 0 ≤ (451 / 5000 : ℝ) * (1 + t) - t ^ 2 * (1 - t) := by
      rw [hpoly]
      have h1 : 0 ≤ (t - 309 / 500) ^ 2 * (t + 59 / 250) :=
        mul_nonneg (sq_nonneg _) (by linarith)
      have h2 : 0 ≤ (7 / 250000 : ℝ) * (1 - t) := by linarith
      linarith
    nlinarith
  linarith [ht_sq]

private lemma intervalIntegrable_monomial_div (r : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    IntervalIntegrable (fun x : ℝ => x ^ r / (1 - x * y)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable fun x hx => ?_
  rw [Set.uIcc_of_le zero_le_one] at hx
  have hne : 1 - x * y ≠ 0 := by nlinarith [hx.1, hx.2]
  have hc : ContinuousAt (fun t : ℝ => t ^ r / (1 - t * y)) x :=
    ContinuousAt.div (continuousAt_id.pow r)
      (continuousAt_const.sub (continuousAt_id.mul continuousAt_const)) hne
  exact hc.continuousWithinAt

private lemma continuousOn_integral_monomial (r : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ContinuousOn (fun y : ℝ => ∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) (Set.Icc 0 t) := by
  intro y hy
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have h1t : 0 < 1 - t := sub_pos.2 ht1
  have h1t2 : 0 < (1 - t) ^ 2 := sq_pos_of_pos h1t
  set δ := (1 - t) ^ 2 * ε / 2
  have hδ : 0 < δ := by positivity
  refine ⟨δ, hδ, fun y' hy' hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_monomial_div r hy'.1 (hy'.2.trans_lt ht1))
    (intervalIntegrable_monomial_div r hy.1 (hy.2.trans_lt ht1))]
  have hbd : ∀ x ∈ Set.uIoc (0 : ℝ) 1,
      ‖x ^ r / (1 - x * y') - x ^ r / (1 - x * y)‖ ≤ |y' - y| / (1 - t) ^ 2 := by
    intro x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have h1 : 1 - t ≤ 1 - x * y' := by nlinarith [hx.1, hx.2, hy'.1, hy'.2]
    have h2 : 1 - t ≤ 1 - x * y := by nlinarith [hx.1, hx.2, hy.1, hy.2]
    have hp1 : 0 < 1 - x * y' := by linarith
    have hp2 : 0 < 1 - x * y := by linarith
    have hdiff : x ^ r / (1 - x * y') - x ^ r / (1 - x * y) =
        x ^ (r + 1) * (y' - y) / ((1 - x * y') * (1 - x * y)) := by
      field_simp [hp1.ne', hp2.ne']; rw [pow_succ]; ring
    rw [hdiff, Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_nonneg (pow_nonneg hx.1.le _),
        abs_of_pos (mul_pos hp1 hp2)]
    have hxpow : x ^ (r + 1) ≤ 1 := pow_le_one₀ hx.1.le hx.2
    have hprod : (1 - t) ^ 2 ≤ (1 - x * y') * (1 - x * y) := by
      rw [sq]; exact mul_le_mul h1 h2 h1t.le hp1.le
    calc x ^ (r + 1) * |y' - y| / ((1 - x * y') * (1 - x * y))
        ≤ 1 * |y' - y| / (1 - t) ^ 2 := by gcongr
      _ = |y' - y| / (1 - t) ^ 2 := by ring
  calc |∫ x in (0 : ℝ)..1, (x ^ r / (1 - x * y') - x ^ r / (1 - x * y))|
      ≤ (|y' - y| / (1 - t) ^ 2) * |1 - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbd
    _ = |y' - y| / (1 - t) ^ 2 := by norm_num
    _ < δ / (1 - t) ^ 2 := by gcongr
    _ = ε / 2 := by dsimp only [δ]; field_simp [h1t2.ne']
    _ < ε := by linarith

private lemma continuousOn_beukers_inner (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ContinuousOn
      (fun y : ℝ =>
        (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n * y ^ n / (1 - x * y) ^ (n + 1)) * (1 - y) ^ n)
      (Set.Icc 0 t) := by
  have hcongr : Set.EqOn
      (fun y : ℝ =>
        (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n * y ^ n / (1 - x * y) ^ (n + 1)) * (1 - y) ^ n)
      (fun y : ℝ =>
        ((-1 : ℝ) ^ n *
          ∑ r ∈ range (n + 1),
            ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).choose r : ℝ)) *
            (∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y))) * (1 - y) ^ n)
      (Set.Icc 0 t) := by
    intro y hy
    dsimp only
    rw [← beukers_ibp n hy.1 (hy.2.trans_lt ht1)]
    congr 2
    unfold beukersPoly
    simp_rw [sum_div]
    rw [intervalIntegral.integral_finsetSum]
    · refine sum_congr rfl fun r _ => ?_
      rw [← intervalIntegral.integral_const_mul]
      congr 1; ext x; ring
    · intro r _
      have hint := intervalIntegrable_monomial_div r hy.1 (hy.2.trans_lt ht1)
      have heq : (fun x : ℝ => ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).choose r : ℝ)) *
          x ^ r / (1 - x * y)) =
          (fun x : ℝ => ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).choose r : ℝ)) *
            (x ^ r / (1 - x * y))) := by ext x; ring
      rw [heq]
      exact hint.const_mul _
  refine ContinuousOn.congr ?_ hcongr
  refine (continuousOn_const.mul ?_).mul (by fun_prop)
  refine continuousOn_finsetSum _ fun r _ =>
    continuousOn_const.mul (continuousOn_integral_monomial r ht0 ht1)

private lemma integral_monomial_geom (r : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    HasSum (fun m : ℕ => y ^ m / ((m + r + 1 : ℕ) : ℝ))
      (∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) := by
  have hF : ∀ m : ℕ, ∫ x in (0 : ℝ)..1, x ^ (m + r) * y ^ m = y ^ m / ((m + r + 1 : ℕ) : ℝ) := by
    intro m
    rw [intervalIntegral.integral_mul_const, integral_pow]
    simp [div_eq_mul_inv, mul_comm]
  simp_rw [← hF]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun m _ => y ^ m)
    (fun m => (by fun_prop : Continuous fun x : ℝ => x ^ (m + r) * y ^ m).aestronglyMeasurable)
    ?_ ?_ ?_ ?_
  · intro m
    filter_upwards with x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx.1.le _) (pow_nonneg hy0 _))]
    calc x ^ (m + r) * y ^ m ≤ 1 * y ^ m := by
          gcongr
          exact pow_le_one₀ hx.1.le hx.2
      _ = y ^ m := one_mul _
  · filter_upwards with x _
    exact summable_geometric_of_lt_one hy0 hy1
  · exact intervalIntegrable_const
  · filter_upwards with x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hxy0 : 0 ≤ x * y := mul_nonneg hx.1.le hy0
    have hxy1 : x * y < 1 := by nlinarith [hx.1, hx.2]
    have hgeom := hasSum_geometric_of_lt_one hxy0 hxy1
    have hmul := hgeom.mul_left (x ^ r)
    have hfun : (fun m : ℕ => x ^ (m + r) * y ^ m) = (fun m : ℕ => x ^ r * (x * y) ^ m) := by
      ext m; rw [mul_pow, pow_add]; ring
    rw [hfun, div_eq_mul_inv]
    exact hmul

private lemma double_integral_monomial_geom (r s : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasSum (fun m : ℕ => t ^ (m + s + 1) / (((m + r + 1 : ℕ) : ℝ) * ((m + s + 1 : ℕ) : ℝ)))
      (∫ y in (0 : ℝ)..t, (∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) * y ^ s) := by
  have hF : ∀ m : ℕ,
      ∫ y in (0 : ℝ)..t, (y ^ m / ((m + r + 1 : ℕ) : ℝ)) * y ^ s =
        t ^ (m + s + 1) / (((m + r + 1 : ℕ) : ℝ) * ((m + s + 1 : ℕ) : ℝ)) := by
    intro m
    have hrew : (fun y : ℝ => (y ^ m / ((m + r + 1 : ℕ) : ℝ)) * y ^ s) =
        fun y : ℝ => ((m + r + 1 : ℕ) : ℝ)⁻¹ * y ^ (m + s) := by
      ext y; rw [pow_add]; ring
    rw [hrew, intervalIntegral.integral_const_mul, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero _), sub_zero]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    push_cast
    ring
  simp_rw [← hF]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun m _ => t ^ m)
    (fun m => (by fun_prop : Continuous fun y : ℝ => (y ^ m / ((m + r + 1 : ℕ) : ℝ)) * y ^ s).aestronglyMeasurable)
    ?_ ?_ ?_ ?_
  · intro m
    filter_upwards with y hy
    rw [Set.uIoc_of_le ht0] at hy
    have hy0 : 0 ≤ y := hy.1.le
    have hden1 : (1 : ℝ) ≤ (m + r + 1 : ℕ) := by exact_mod_cast Nat.succ_pos (m + r)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (y ^ m / ((m + r + 1 : ℕ) : ℝ)) * y ^ s
        ≤ (y ^ m / 1) * 1 := by
          gcongr
          exact pow_le_one₀ hy0 (hy.2.trans ht1.le)
      _ = y ^ m := by ring
      _ ≤ t ^ m := pow_le_pow_left₀ hy0 hy.2 m
  · filter_upwards with y _
    exact summable_geometric_of_lt_one ht0 ht1
  · exact intervalIntegrable_const
  · filter_upwards with y hy
    rw [Set.uIoc_of_le ht0] at hy
    have h1 := integral_monomial_geom r hy.1.le (hy.2.trans_lt ht1)
    exact h1.mul_right (y ^ s)

private lemma hasSum_one_div_sq_shift :
    HasSum (fun m : ℕ => (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 6) := by
  have h := hasSum_zeta_two
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [range_one, sum_singleton, Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0),
    div_zero, sub_zero] at h
  exact h

private lemma hasSum_shifted_diag (r : ℕ) :
    HasSum (fun m : ℕ => (1 : ℝ) / (((m + r + 1 : ℕ) : ℝ) * ((m + r + 1 : ℕ) : ℝ)))
      (π ^ 2 / 6 - ∑ k ∈ Icc 1 r, (1 : ℝ) / (k : ℝ) ^ 2) := by
  have h := hasSum_one_div_sq_shift
  rw [← hasSum_nat_add_iff' r] at h
  have hsum : ∑ i ∈ range r, (1 : ℝ) / ((i + 1 : ℕ) : ℝ) ^ 2 =
      ∑ k ∈ Icc 1 r, (1 : ℝ) / (k : ℝ) ^ 2 := by
    refine sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
    · intro i hi; simp only [mem_range, mem_Icc] at hi ⊢; omega
    · intro a _ b _ hab; omega
    · intro k hk; simp only [mem_Icc, mem_range] at hk ⊢; exact ⟨k - 1, by omega, by omega⟩
    · intro i _; rfl
  rw [hsum] at h
  have hfun : (fun m : ℕ => (1 : ℝ) / (((m + r + 1 : ℕ) : ℝ) * ((m + r + 1 : ℕ) : ℝ))) =
      (fun m : ℕ => (1 : ℝ) / (((m + r + 1 : ℕ) : ℝ) ^ 2)) := by
    ext m; rw [sq]
  rw [hfun]
  exact h

private lemma hasSum_shifted_offdiag {a b : ℕ} (hab : a < b) :
    HasSum (fun m : ℕ => (1 : ℝ) / (((m + a + 1 : ℕ) : ℝ) * ((m + b + 1 : ℕ) : ℝ)))
      ((1 : ℝ) / ((b - a : ℕ) : ℝ) * ∑ k ∈ Icc (a + 1) b, (1 : ℝ) / (k : ℝ)) := by
  set d := b - a
  have hd : 0 < d := by omega
  have hb : b = a + d := by omega
  have hpartial : ∀ N : ℕ,
      ∑ m ∈ range N, (1 : ℝ) / (((m + a + 1 : ℕ) : ℝ) * ((m + b + 1 : ℕ) : ℝ)) =
      (1 : ℝ) / (d : ℝ) *
        ((∑ k ∈ Icc (a + 1) b, (1 : ℝ) / (k : ℝ)) -
          (∑ k ∈ Icc (N + a + 1) (N + b), (1 : ℝ) / (k : ℝ))) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, ih]
      have hterm : (1 : ℝ) / (((N + a + 1 : ℕ) : ℝ) * ((N + b + 1 : ℕ) : ℝ)) =
          (1 : ℝ) / (d : ℝ) * ((1 : ℝ) / ((N + a + 1 : ℕ) : ℝ) -
            (1 : ℝ) / ((N + b + 1 : ℕ) : ℝ)) := by
        have h1 : ((N + a + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have h2 : ((N + b + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have h3 : (d : ℝ) ≠ 0 := by positivity
        have hdiff : ((N + b + 1 : ℕ) : ℝ) - ((N + a + 1 : ℕ) : ℝ) = (d : ℝ) := by
          rw [hb]; push_cast; ring
        field_simp [h1, h2, h3]
        linarith
      have hshift :
          ∑ k ∈ Icc (N + 1 + a + 1) (N + 1 + b), (1 : ℝ) / (k : ℝ) =
          (∑ k ∈ Icc (N + a + 1) (N + b), (1 : ℝ) / (k : ℝ)) -
            (1 : ℝ) / ((N + a + 1 : ℕ) : ℝ) + (1 : ℝ) / ((N + b + 1 : ℕ) : ℝ) := by
        have hleft : Icc (N + a + 1) (N + b + 1) =
            insert (N + a + 1) (Icc (N + 1 + a + 1) (N + 1 + b)) := by
          ext k; simp only [mem_Icc, mem_insert]; omega
        have hright : Icc (N + a + 1) (N + b + 1) =
            insert (N + b + 1) (Icc (N + a + 1) (N + b)) := by
          ext k; simp only [mem_Icc, mem_insert]; omega
        have h1 := congrArg (fun S : Finset ℕ => ∑ k ∈ S, (1 : ℝ) / (k : ℝ)) hleft
        have h2 := congrArg (fun S : Finset ℕ => ∑ k ∈ S, (1 : ℝ) / (k : ℝ)) hright
        rw [sum_insert (by simp only [mem_Icc]; omega)] at h1
        rw [sum_insert (by simp only [mem_Icc]; omega)] at h2
        linarith
      rw [hterm, hshift]
      ring
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun m => by positivity)]
  simp_rw [hpartial]
  have htail : Tendsto (fun N : ℕ => ∑ k ∈ Icc (N + a + 1) (N + b), (1 : ℝ) / (k : ℝ))
      atTop (𝓝 0) := by
    refine squeeze_zero (g := fun N : ℕ => (d : ℝ) / ((N + 1 : ℕ) : ℝ))
      (fun N => sum_nonneg fun k _ => by positivity) ?_ ?_
    · intro N
      calc ∑ k ∈ Icc (N + a + 1) (N + b), (1 : ℝ) / (k : ℝ)
          ≤ ∑ _k ∈ Icc (N + a + 1) (N + b), (1 : ℝ) / ((N + 1 : ℕ) : ℝ) := by
            refine sum_le_sum fun k hk => ?_
            have hk1 : (N + 1 : ℕ) ≤ k := by simp only [mem_Icc] at hk; omega
            gcongr
        _ = (d : ℝ) / ((N + 1 : ℕ) : ℝ) := by
            rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
            have hcard : N + b + 1 - (N + a + 1) = d := by omega
            rw [hcard, mul_one_div]
    · simpa [div_eq_mul_inv] using
        (tendsto_const_nhds (x := (d : ℝ))).mul
          ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).inv_tendsto_atTop)
  have hlim := ((tendsto_const_nhds (x := ∑ k ∈ Icc (a + 1) b, (1 : ℝ) / (k : ℝ))).sub htail).const_mul
    ((1 : ℝ) / (d : ℝ))
  simpa [sub_zero] using hlim

private noncomputable def beukersTerm (r s : ℕ) : ℝ :=
  if r = s then π ^ 2 / 6 - ∑ k ∈ Icc 1 r, (1 : ℝ) / (k : ℝ) ^ 2
  else (1 : ℝ) / ((max r s - min r s : ℕ) : ℝ) *
    ∑ k ∈ Icc (min r s + 1) (max r s), (1 : ℝ) / (k : ℝ)

private lemma hasSum_beukersTerm (r s : ℕ) :
    HasSum (fun m : ℕ => (1 : ℝ) / (((m + r + 1 : ℕ) : ℝ) * ((m + s + 1 : ℕ) : ℝ)))
      (beukersTerm r s) := by
  unfold beukersTerm
  rcases lt_trichotomy r s with hlt | rfl | hgt
  · rw [if_neg hlt.ne, max_eq_right hlt.le, min_eq_left hlt.le]
    exact hasSum_shifted_offdiag hlt
  · rw [if_pos rfl]
    exact hasSum_shifted_diag r
  · rw [if_neg hgt.ne', max_eq_left hgt.le, min_eq_right hgt.le]
    simpa [mul_comm] using hasSum_shifted_offdiag hgt

private lemma tendsto_double_integral_monomial (r s : ℕ) :
    Tendsto
      (fun t : ℝ => ∫ y in (0 : ℝ)..t, (∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) * y ^ s)
      (𝓝[<] 1) (𝓝 (beukersTerm r s)) := by
  have hev : ∀ᶠ t : ℝ in 𝓝[<] 1,
      ∫ y in (0 : ℝ)..t, (∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) * y ^ s =
        ∑' m : ℕ, t ^ (m + s + 1) / (((m + r + 1 : ℕ) : ℝ) * ((m + s + 1 : ℕ) : ℝ)) := by
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    exact (double_integral_monomial_geom r s ht.1.le ht.2).tsum_eq.symm
  rw [tendsto_congr' hev, ← (hasSum_beukersTerm r s).tsum_eq]
  refine tendsto_tsum_of_dominated_convergence (bound := fun m : ℕ => (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2)
    hasSum_one_div_sq_shift.summable ?_ ?_
  · intro m
    have hpow : Tendsto (fun t : ℝ => t ^ (m + s + 1)) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
      have hid : Tendsto (fun t : ℝ => t) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using hid.pow (m + s + 1)
    simpa using hpow.div_const (((m + r + 1 : ℕ) : ℝ) * ((m + s + 1 : ℕ) : ℝ))
  · filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ht m
    have ht0 : 0 ≤ t := ht.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hnum : t ^ (m + s + 1) ≤ 1 := pow_le_one₀ ht0 ht.2.le
    have hden1 : ((m + 1 : ℕ) : ℝ) ≤ (m + r + 1 : ℕ) := by exact_mod_cast (by omega : m + 1 ≤ m + r + 1)
    have hden2 : ((m + 1 : ℕ) : ℝ) ≤ (m + s + 1 : ℕ) := by exact_mod_cast (by omega : m + 1 ≤ m + s + 1)
    rw [sq]
    gcongr

/- ### Section 3: Beukers Linear Form, Integrality, and Bounds -/

private def beukersA (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n * ∑ r ∈ range (n + 1), (n.choose r : ℤ) ^ 2 * ((n + r).choose r : ℤ)

private def beukersB (n : ℕ) : ℚ :=
  (-1 : ℚ) ^ n *
    ∑ r ∈ range (n + 1), ∑ s ∈ range (n + 1),
      ((-1 : ℚ) ^ r * (n.choose r : ℚ) * ((n + r).choose r : ℚ)) *
      ((-1 : ℚ) ^ s * (n.choose s : ℚ)) *
      (if r = s then -(∑ k ∈ Icc 1 r, (1 : ℚ) / (k : ℚ) ^ 2)
       else (1 : ℚ) / ((max r s - min r s : ℕ) : ℚ) *
         ∑ k ∈ Icc (min r s + 1) (max r s), (1 : ℚ) / (k : ℚ))

private lemma beukersB_denom_int (n : ℕ) :
    ∃ p : ℤ, (p : ℝ) = (Nat.lcmUpto n : ℝ) ^ 2 * (beukersB n : ℝ) := by
  have hdvd_k (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) : k ∣ Nat.lcmUpto n :=
    Finset.dvd_lcm (mem_Icc.2 ⟨hk1, hkn⟩)
  have hterm_int : ∀ r ∈ range (n + 1), ∀ s ∈ range (n + 1),
      ∃ z : ℤ, (z : ℚ) = (Nat.lcmUpto n : ℚ) ^ 2 *
        (if r = s then -(∑ k ∈ Icc 1 r, (1 : ℚ) / (k : ℚ) ^ 2)
         else (1 : ℚ) / ((max r s - min r s : ℕ) : ℚ) *
           ∑ k ∈ Icc (min r s + 1) (max r s), (1 : ℚ) / (k : ℚ)) := by
    intro r hr s hs
    have hrn : r ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hr)
    have hsn : s ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hs)
    split_ifs with hrs
    · refine ⟨-(∑ k ∈ Icc 1 r, ((Nat.lcmUpto n / k : ℕ) : ℤ) ^ 2), ?_⟩
      rw [mul_neg, mul_sum, Int.cast_neg, Int.cast_sum]
      congr 1
      refine sum_congr rfl fun k hk => ?_
      simp only [mem_Icc] at hk
      have hkd : k ∣ Nat.lcmUpto n := hdvd_k k hk.1 (hk.2.trans hrn)
      have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have hdiv : ((Nat.lcmUpto n / k : ℕ) : ℚ) = (Nat.lcmUpto n : ℚ) / (k : ℚ) :=
        Nat.cast_div hkd hk0
      rw [Int.cast_pow, Int.cast_natCast, hdiv, div_pow, mul_one_div]
    · set hi := max r s
      set lo := min r s
      have hdiff1 : 1 ≤ hi - lo := by omega
      have hdiffn : hi - lo ≤ n := by omega
      have hdd : hi - lo ∣ Nat.lcmUpto n := hdvd_k (hi - lo) hdiff1 hdiffn
      refine ⟨((Nat.lcmUpto n / (hi - lo) : ℕ) : ℤ) *
          ∑ k ∈ Icc (lo + 1) hi, ((Nat.lcmUpto n / k : ℕ) : ℤ), ?_⟩
      rw [Int.cast_mul, Int.cast_natCast, Int.cast_sum]
      have hd0 : ((hi - lo : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have hdiv1 : ((Nat.lcmUpto n / (hi - lo) : ℕ) : ℚ) =
          (Nat.lcmUpto n : ℚ) / ((hi - lo : ℕ) : ℚ) := Nat.cast_div hdd hd0
      rw [hdiv1, mul_sum, mul_sum, mul_sum]
      refine sum_congr rfl fun k hk => ?_
      simp only [mem_Icc] at hk
      have hkd : k ∣ Nat.lcmUpto n := hdvd_k k (by omega) (by omega)
      have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have hdiv2 : ((Nat.lcmUpto n / k : ℕ) : ℚ) = (Nat.lcmUpto n : ℚ) / (k : ℚ) :=
        Nat.cast_div hkd hk0
      rw [Int.cast_natCast, hdiv2]
      ring
  choose f hf using hterm_int
  refine ⟨(-1 : ℤ) ^ n * ∑ r ∈ range (n + 1), ∑ s ∈ range (n + 1),
      ((-1 : ℤ) ^ r * (n.choose r : ℤ) * ((n + r).choose r : ℤ)) *
      ((-1 : ℤ) ^ s * (n.choose s : ℤ)) *
      (if h : r ∈ range (n + 1) ∧ s ∈ range (n + 1) then f r h.1 s h.2 else 0), ?_⟩
  suffices hq : ((((-1 : ℤ) ^ n * ∑ r ∈ range (n + 1), ∑ s ∈ range (n + 1),
      ((-1 : ℤ) ^ r * (n.choose r : ℤ) * ((n + r).choose r : ℤ)) *
      ((-1 : ℤ) ^ s * (n.choose s : ℤ)) *
      (if h : r ∈ range (n + 1) ∧ s ∈ range (n + 1) then f r h.1 s h.2 else 0) : ℤ) : ℚ)) =
      (Nat.lcmUpto n : ℚ) ^ 2 * beukersB n by
    have := congrArg (fun q : ℚ => (q : ℝ)) hq
    simpa using this
  unfold beukersB
  rw [mul_left_comm]
  push_cast
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun r hr => ?_
  rw [mul_sum]
  refine sum_congr rfl fun s hs => ?_
  rw [dif_pos ⟨hr, hs⟩, hf r hr s hs]
  ring

private lemma beukers_linear_form_eq (n : ℕ) :
    (beukersA n : ℝ) * (π ^ 2 / 6) + (beukersB n : ℝ) =
      (-1 : ℝ) ^ n *
        ∑ r ∈ range (n + 1), ∑ s ∈ range (n + 1),
          ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).choose r : ℝ)) *
          ((-1 : ℝ) ^ s * (n.choose s : ℝ)) * beukersTerm r s := by
  unfold beukersA beukersB beukersTerm
  push_cast
  have hsplit : ∀ r s : ℕ,
      (if r = s then π ^ 2 / 6 - ∑ k ∈ Icc 1 r, (1 : ℝ) / (k : ℝ) ^ 2
       else (1 : ℝ) / ((max r s - min r s : ℕ) : ℝ) *
         ∑ k ∈ Icc (min r s + 1) (max r s), (1 : ℝ) / (k : ℝ)) =
      (if r = s then π ^ 2 / 6 else 0) +
      (if r = s then -(∑ k ∈ Icc 1 r, (1 : ℝ) / (k : ℝ) ^ 2)
       else (1 : ℝ) / ((max r s - min r s : ℕ) : ℝ) *
         ∑ k ∈ Icc (min r s + 1) (max r s), (1 : ℝ) / (k : ℝ)) := by
    intro r s; split_ifs <;> ring
  simp_rw [hsplit, mul_add, sum_add_distrib, mul_add]
  congr 1
  · rw [mul_assoc]
    congr 1
    rw [sum_mul]
    refine sum_congr rfl fun r hr => ?_
    simp only [mul_ite, mul_zero, sum_ite_eq, hr, ite_true]
    have hsign : (-1 : ℝ) ^ r * (-1 : ℝ) ^ r = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    calc ((n.choose r : ℝ) ^ 2 * ((n + r).choose r : ℝ)) * (π ^ 2 / 6)
        = ((-1 : ℝ) ^ r * (-1 : ℝ) ^ r) *
            ((n.choose r : ℝ) ^ 2 * ((n + r).choose r : ℝ)) * (π ^ 2 / 6) := by
          rw [hsign, one_mul]
      _ = ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).choose r : ℝ)) *
            ((-1 : ℝ) ^ r * (n.choose r : ℝ)) * (π ^ 2 / 6) := by ring
  · congr 1
    refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
    split_ifs <;> push_cast <;> rfl

private lemma beukers_integral_bounds (n : ℕ) :
    0 < (beukersA n : ℝ) * (π ^ 2 / 6) + (beukersB n : ℝ) ∧
    (beukersA n : ℝ) * (π ^ 2 / 6) + (beukersB n : ℝ) ≤ (451 / 5000 : ℝ) ^ n * (π ^ 2 / 6) := by
  let I : ℝ → ℝ := fun t =>
    ∫ y in (0 : ℝ)..t,
      (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n * y ^ n / (1 - x * y) ^ (n + 1)) * (1 - y) ^ n
  have hI_eq : ∀ t : ℝ, 0 ≤ t → t < 1 →
      I t = (-1 : ℝ) ^ n *
        ∑ r ∈ range (n + 1), ∑ s ∈ range (n + 1),
          ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).choose r : ℝ)) *
          ((-1 : ℝ) ^ s * (n.choose s : ℝ)) *
          (∫ y in (0 : ℝ)..t, (∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) * y ^ s) := by
    intro t ht0 ht1
    dsimp only [I]
    have hinner : ∀ y ∈ Set.uIcc (0 : ℝ) t,
        (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n * y ^ n / (1 - x * y) ^ (n + 1)) * (1 - y) ^ n =
        (-1 : ℝ) ^ n *
          ∑ r ∈ range (n + 1), ∑ s ∈ range (n + 1),
            ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).choose r : ℝ)) *
            ((-1 : ℝ) ^ s * (n.choose s : ℝ)) *
            ((∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) * y ^ s) := by
      intro y hy
      rw [Set.uIcc_of_le ht0] at hy
      have hy0 : 0 ≤ y := hy.1
      have hy1 : y < 1 := hy.2.trans_lt ht1
      rw [← beukers_ibp n hy0 hy1]
      have hpoly : ∫ x in (0 : ℝ)..1, beukersPoly n x / (1 - x * y) =
          ∑ r ∈ range (n + 1),
            ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).choose r : ℝ)) *
            (∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) := by
        unfold beukersPoly
        simp_rw [sum_div]
        rw [intervalIntegral.integral_finsetSum]
        · refine sum_congr rfl fun r _ => ?_
          rw [← intervalIntegral.integral_const_mul]
          congr 1; ext x; ring
        · intro r _
          have heq : (fun x : ℝ => ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).choose r : ℝ)) *
              x ^ r / (1 - x * y)) =
              (fun x : ℝ => ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).choose r : ℝ)) *
                (x ^ r / (1 - x * y))) := by ext x; ring
          rw [heq]
          exact (intervalIntegrable_monomial_div r hy0 hy1).const_mul _
      have hbin : (1 - y) ^ n =
          ∑ s ∈ range (n + 1), (-1 : ℝ) ^ s * (n.choose s : ℝ) * y ^ s := by
        rw [sub_eq_add_neg, add_comm, add_pow]
        refine sum_congr rfl fun s _ => ?_
        rw [neg_eq_neg_one_mul, mul_pow, one_pow, mul_one]; ring
      rw [hpoly, hbin, mul_assoc, sum_mul]
      congr 1
      refine sum_congr rfl fun r _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun s _ => ?_
      ring
    rw [intervalIntegral.integral_congr hinner]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hcont_term : ∀ r s : ℕ,
        ContinuousOn (fun y : ℝ =>
          ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).choose r : ℝ)) *
          ((-1 : ℝ) ^ s * (n.choose s : ℝ)) *
          ((∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) * y ^ s)) (Set.Icc 0 t) := fun r s =>
      continuousOn_const.mul ((continuousOn_integral_monomial r ht0 ht1).mul (by fun_prop))
    have hint_term : ∀ r s : ℕ,
        IntervalIntegrable (fun y : ℝ =>
          ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).choose r : ℝ)) *
          ((-1 : ℝ) ^ s * (n.choose s : ℝ)) *
          ((∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) * y ^ s)) volume 0 t := fun r s =>
      (hcont_term r s).intervalIntegrable_of_Icc ht0
    rw [intervalIntegral.integral_finsetSum]
    · refine sum_congr rfl fun r _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      · refine sum_congr rfl fun s _ => ?_
        rw [intervalIntegral.integral_const_mul]
      · intro s _; exact hint_term r s
    · intro r _
      exact (continuousOn_finsetSum _ fun s _ => hcont_term r s).intervalIntegrable_of_Icc ht0
  have hI_tendsto : Tendsto I (𝓝[<] 1) (𝓝 ((beukersA n : ℝ) * (π ^ 2 / 6) + (beukersB n : ℝ))) := by
    rw [beukers_linear_form_eq]
    have hev : ∀ᶠ t : ℝ in 𝓝[<] 1,
        I t = (-1 : ℝ) ^ n *
          ∑ r ∈ range (n + 1), ∑ s ∈ range (n + 1),
            ((-1 : ℝ) ^ r * (n.choose r : ℝ) * ((n + r).choose r : ℝ)) *
            ((-1 : ℝ) ^ s * (n.choose s : ℝ)) *
            (∫ y in (0 : ℝ)..t, (∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) * y ^ s) := by
      filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ht
      exact hI_eq t ht.1.le ht.2
    rw [tendsto_congr' hev]
    refine Tendsto.const_mul _ ?_
    refine tendsto_finsetSum _ fun r _ => ?_
    refine tendsto_finsetSum _ fun s _ => ?_
    exact (tendsto_double_integral_monomial r s).const_mul _
  have hI_le : ∀ t ∈ Set.Ioo (0 : ℝ) 1, I t ≤ (451 / 5000 : ℝ) ^ n * (π ^ 2 / 6) := by
    intro t ht
    dsimp only [I]
    have hinner_le : ∀ y ∈ Set.Icc (0 : ℝ) t,
        (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n * y ^ n / (1 - x * y) ^ (n + 1)) * (1 - y) ^ n ≤
        (451 / 5000 : ℝ) ^ n * ∫ x in (0 : ℝ)..1, 1 / (1 - x * y) := by
      intro y hy
      rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ ?_
      · refine ContinuousOn.intervalIntegrable fun x hx => ?_
        rw [Set.uIcc_of_le zero_le_one] at hx
        have hne : 1 - x * y ≠ 0 := by nlinarith [hx.1, hx.2, hy.1, hy.2, ht.2]
        have hc : ContinuousAt
            (fun u : ℝ => u ^ n * (1 - u) ^ n * y ^ n / (1 - u * y) ^ (n + 1) * (1 - y) ^ n) x :=
          ContinuousAt.mul
            (ContinuousAt.div
              (((continuousAt_id.pow n).mul ((continuousAt_const.sub continuousAt_id).pow n)).mul
                continuousAt_const)
              ((continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).pow (n + 1))
              (pow_ne_zero _ hne))
            continuousAt_const
        exact hc.continuousWithinAt
      · have hint0 := intervalIntegrable_monomial_div 0 hy.1 (hy.2.trans_lt ht.2)
        simpa only [pow_zero] using hint0.const_mul ((451 / 5000 : ℝ) ^ n)
      · intro x hx
        have hden : 0 < 1 - x * y := by nlinarith [hx.1, hx.2, hy.1, hy.2, ht.2]
        have hk := beukers_kernel_le hx.1 hx.2 hy.1 (hy.2.trans_lt ht.2)
        have hx0 : 0 ≤ x := hx.1
        have hy0 : 0 ≤ y := hy.1
        have h1x : 0 ≤ 1 - x := by linarith [hx.2]
        have h1y : 0 ≤ 1 - y := by linarith [hy.2, ht.2]
        have hk0 : 0 ≤ x * (1 - x) * y * (1 - y) / (1 - x * y) := by positivity
        have hpow := pow_le_pow_left₀ hk0 hk n
        have hrew : x ^ n * (1 - x) ^ n * y ^ n / (1 - x * y) ^ (n + 1) * (1 - y) ^ n =
            (x * (1 - x) * y * (1 - y) / (1 - x * y)) ^ n * (1 / (1 - x * y)) := by
          rw [div_pow, mul_pow, mul_pow, mul_pow, pow_succ]
          field_simp [hden.ne']
        rw [hrew]
        exact mul_le_mul_of_nonneg_right hpow (by positivity)
    have hint_lhs : IntervalIntegrable (fun y : ℝ =>
        (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n * y ^ n / (1 - x * y) ^ (n + 1)) * (1 - y) ^ n)
        volume 0 t :=
      (continuousOn_beukers_inner n ht.1.le ht.2).intervalIntegrable_of_Icc ht.1.le
    have hint_rhs : IntervalIntegrable (fun y : ℝ =>
        (451 / 5000 : ℝ) ^ n * ∫ x in (0 : ℝ)..1, 1 / (1 - x * y)) volume 0 t := by
      have hc := continuousOn_integral_monomial 0 ht.1.le ht.2
      simp only [pow_zero] at hc
      exact (continuousOn_const.mul hc).intervalIntegrable_of_Icc ht.1.le
    have hstep := intervalIntegral.integral_mono_on ht.1.le hint_lhs hint_rhs hinner_le
    rw [intervalIntegral.integral_const_mul] at hstep
    have hbase : ∫ y in (0 : ℝ)..t, ∫ x in (0 : ℝ)..1, (1 : ℝ) / (1 - x * y) ≤ π ^ 2 / 6 := by
      have h00 := double_integral_monomial_geom 0 0 ht.1.le ht.2
      simp only [pow_zero, mul_one, add_zero] at h00
      rw [← h00.tsum_eq, ← hasSum_one_div_sq_shift.tsum_eq]
      refine Summable.tsum_le_tsum (fun m => ?_) h00.summable hasSum_one_div_sq_shift.summable
      rw [sq]
      gcongr
      exact pow_le_one₀ ht.1.le ht.2.le
    calc I t ≤ (451 / 5000 : ℝ) ^ n * ∫ y in (0 : ℝ)..t, ∫ x in (0 : ℝ)..1, 1 / (1 - x * y) := hstep
      _ ≤ (451 / 5000 : ℝ) ^ n * (π ^ 2 / 6) :=
        mul_le_mul_of_nonneg_left hbase (by positivity)
  have hI_pos : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ioo (1 / 2 : ℝ) 1, c ≤ I t := by
    refine ⟨I (1 / 2), ?_, ?_⟩
    · dsimp only [I]
      refine intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1 / 2)
        (continuousOn_beukers_inner n (by norm_num) (by norm_num)) ?_ ?_
      · intro y hy
        have hnn : 0 ≤ ∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n * y ^ n / (1 - x * y) ^ (n + 1) := by
          refine intervalIntegral.integral_nonneg zero_le_one fun x hx => ?_
          have hx0 : 0 ≤ x := hx.1
          have hy0 : 0 ≤ y := hy.1.le
          have hden : 0 < 1 - x * y := by nlinarith [hx.1, hx.2, hy.1, hy.2]
          have h1x : 0 ≤ 1 - x := by linarith [hx.2]
          positivity
        exact mul_nonneg hnn (pow_nonneg (by linarith [hy.2]) n)
      · refine ⟨1 / 4, ⟨by norm_num, by norm_num⟩, ?_⟩
        refine mul_pos ?_ (pow_pos (by norm_num) n)
        refine intervalIntegral.integral_pos zero_lt_one ?_ ?_
          ⟨1 / 2, ⟨by norm_num, by norm_num⟩, by positivity⟩
        · intro x hx
          have hne : 1 - x * (1 / 4 : ℝ) ≠ 0 := by nlinarith [hx.1, hx.2]
          have hc : ContinuousAt
              (fun u : ℝ => u ^ n * (1 - u) ^ n * (1 / 4 : ℝ) ^ n / (1 - u * (1 / 4)) ^ (n + 1)) x :=
            ContinuousAt.div
              (((continuousAt_id.pow n).mul ((continuousAt_const.sub continuousAt_id).pow n)).mul
                continuousAt_const)
              ((continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).pow (n + 1))
              (pow_ne_zero _ hne)
          exact hc.continuousWithinAt
        · intro x hx
          have hx0 : 0 ≤ x := hx.1.le
          have hden : 0 < 1 - x * (1 / 4 : ℝ) := by nlinarith [hx.1, hx.2]
          have h1x : 0 ≤ 1 - x := by linarith [hx.2]
          positivity
    · intro t ht
      have hsplit : I t = I (1 / 2) +
          ∫ y in (1 / 2 : ℝ)..t,
            (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n * y ^ n / (1 - x * y) ^ (n + 1)) * (1 - y) ^ n := by
        dsimp only [I]
        have hint : IntervalIntegrable (fun y : ℝ =>
            (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n * y ^ n / (1 - x * y) ^ (n + 1)) * (1 - y) ^ n)
            volume 0 t :=
          (continuousOn_beukers_inner n (by linarith [ht.1]) ht.2).intervalIntegrable_of_Icc
            (by linarith [ht.1])
        exact (intervalIntegral.integral_add_adjacent_intervals
          (hint.mono_set (Set.uIcc_subset_uIcc_left
            (by rw [Set.uIcc_of_le (by linarith [ht.1])]; exact ⟨by norm_num, ht.1.le⟩)))
          (hint.mono_set (Set.uIcc_subset_uIcc_right
            (by rw [Set.uIcc_of_le (by linarith [ht.1])]; exact ⟨by norm_num, ht.1.le⟩)))).symm
      rw [hsplit]
      have hnn : 0 ≤ ∫ y in (1 / 2 : ℝ)..t,
          (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n * y ^ n / (1 - x * y) ^ (n + 1)) * (1 - y) ^ n := by
        refine intervalIntegral.integral_nonneg ht.1.le fun y hy => ?_
        have hnnx : 0 ≤ ∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n * y ^ n / (1 - x * y) ^ (n + 1) := by
          refine intervalIntegral.integral_nonneg zero_le_one fun x hx => ?_
          have hx0 : 0 ≤ x := hx.1
          have hy0 : 0 ≤ y := by linarith [hy.1]
          have hden : 0 < 1 - x * y := by nlinarith [hx.1, hx.2, hy.1, hy.2, ht.2]
          have h1x : 0 ≤ 1 - x := by linarith [hx.2]
          positivity
        exact mul_nonneg hnnx (pow_nonneg (by linarith [hy.2, ht.2]) n)
      linarith
  obtain ⟨c, hcpos, hc⟩ := hI_pos
  constructor
  · have hge : c ≤ (beukersA n : ℝ) * (π ^ 2 / 6) + (beukersB n : ℝ) :=
      ge_of_tendsto hI_tendsto (by
        filter_upwards [Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with t ht
        exact hc t ht)
    linarith
  · exact le_of_tendsto hI_tendsto (by
      filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ht
      exact hI_le t ht)

private lemma beukersA_abs_le :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, |(beukersA n : ℝ)| ≤ C * (111 / 10 : ℝ) ^ n := by
  have hterm : ∀ n r : ℕ, r ≤ n →
      ((n.choose r : ℝ) ^ 2 * ((n + r).choose r : ℝ)) ≤ (832 / 75 : ℝ) ^ n := by
    intro n r hr
    have h1 : (n.choose r : ℝ) * (8 / 5 : ℝ) ^ r ≤ (13 / 5 : ℝ) ^ n := by
      have hpow : (13 / 5 : ℝ) ^ n = ∑ k ∈ range (n + 1), (n.choose k : ℝ) * (8 / 5 : ℝ) ^ k := by
        rw [show (13 / 5 : ℝ) = 8 / 5 + 1 by norm_num, add_pow]
        refine sum_congr rfl fun k _ => by rw [one_pow, mul_one, mul_comm]
      rw [hpow]
      exact Finset.single_le_sum (f := fun k => (n.choose k : ℝ) * (8 / 5 : ℝ) ^ k)
        (fun k _ => by positivity) (mem_range.2 (by omega))
    have h2 : ((n + r).choose r : ℝ) * (25 / 39 : ℝ) ^ r ≤ (64 / 39 : ℝ) ^ (n + r) := by
      have hpow : (64 / 39 : ℝ) ^ (n + r) =
          ∑ k ∈ range (n + r + 1), ((n + r).choose k : ℝ) * (25 / 39 : ℝ) ^ k := by
        rw [show (64 / 39 : ℝ) = 25 / 39 + 1 by norm_num, add_pow]
        refine sum_congr rfl fun k _ => by rw [one_pow, mul_one, mul_comm]
      rw [hpow]
      exact Finset.single_le_sum (f := fun k => ((n + r).choose k : ℝ) * (25 / 39 : ℝ) ^ k)
        (fun k _ => by positivity) (mem_range.2 (by omega))
    have h1sq : (n.choose r : ℝ) ^ 2 * ((8 / 5 : ℝ) ^ r) ^ 2 ≤ ((13 / 5 : ℝ) ^ n) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h1 2
    have hmul := mul_le_mul h1sq h2 (by positivity) (by positivity)
    have hposr : (0 : ℝ) < (64 / 39 : ℝ) ^ r := by positivity
    have hlhs : ((n.choose r : ℝ) ^ 2 * ((8 / 5 : ℝ) ^ r) ^ 2) *
        (((n + r).choose r : ℝ) * (25 / 39 : ℝ) ^ r) =
        ((n.choose r : ℝ) ^ 2 * ((n + r).choose r : ℝ)) * (64 / 39 : ℝ) ^ r := by
      have h64 : ((8 / 5 : ℝ) ^ r) ^ 2 * (25 / 39 : ℝ) ^ r = (64 / 39 : ℝ) ^ r := by
        rw [← pow_mul, mul_comm r 2, pow_mul, ← mul_pow]; norm_num
      calc ((n.choose r : ℝ) ^ 2 * ((8 / 5 : ℝ) ^ r) ^ 2) *
            (((n + r).choose r : ℝ) * (25 / 39 : ℝ) ^ r)
          = ((n.choose r : ℝ) ^ 2 * ((n + r).choose r : ℝ)) *
            (((8 / 5 : ℝ) ^ r) ^ 2 * (25 / 39 : ℝ) ^ r) := by ring
        _ = ((n.choose r : ℝ) ^ 2 * ((n + r).choose r : ℝ)) * (64 / 39 : ℝ) ^ r := by rw [h64]
    have hrhs : ((13 / 5 : ℝ) ^ n) ^ 2 * (64 / 39 : ℝ) ^ (n + r) =
        (832 / 75 : ℝ) ^ n * (64 / 39 : ℝ) ^ r := by
      rw [pow_add, ← pow_mul, mul_comm n 2, pow_mul, ← mul_assoc, ← mul_pow]
      norm_num
    rw [hlhs, hrhs] at hmul
    exact le_of_mul_le_mul_right hmul hposr
  refine ⟨2000, by norm_num, fun n => ?_⟩
  unfold beukersA
  push_cast
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (sum_nonneg fun r _ => by positivity)]
  have hsum : ∑ r ∈ range (n + 1), (n.choose r : ℝ) ^ 2 * ((n + r).choose r : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) * (832 / 75 : ℝ) ^ n := by
    calc ∑ r ∈ range (n + 1), (n.choose r : ℝ) ^ 2 * ((n + r).choose r : ℝ)
        ≤ ∑ _r ∈ range (n + 1), (832 / 75 : ℝ) ^ n :=
          sum_le_sum fun r hr => hterm n r (Nat.lt_succ_iff.1 (mem_range.1 hr))
      _ = ((n + 1 : ℕ) : ℝ) * (832 / 75 : ℝ) ^ n := by
          rw [sum_const, card_range, nsmul_eq_mul]
  have hlin : ((n + 1 : ℕ) : ℝ) ≤ 2000 * ((111 / 10 : ℝ) / (832 / 75 : ℝ)) ^ n := by
    have hratio : (1 + 1 / 1700 : ℝ) ≤ (111 / 10 : ℝ) / (832 / 75 : ℝ) := by norm_num
    have hbern : 1 + (n : ℝ) * (1 / 1700 : ℝ) ≤ (1 + 1 / 1700 : ℝ) ^ n := by
      have := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1 / 1700) n
      linarith
    have hpow := pow_le_pow_left₀ (by norm_num) hratio n
    push_cast
    nlinarith
  calc ∑ r ∈ range (n + 1), (n.choose r : ℝ) ^ 2 * ((n + r).choose r : ℝ)
      ≤ ((n + 1 : ℕ) : ℝ) * (832 / 75 : ℝ) ^ n := hsum
    _ ≤ (2000 * ((111 / 10 : ℝ) / (832 / 75 : ℝ)) ^ n) * (832 / 75 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hlin (by positivity)
    _ = 2000 * (111 / 10 : ℝ) ^ n := by
        rw [div_pow, mul_assoc, div_mul_cancel₀ _ (by positivity)]

private lemma beukersA_sign (n : ℕ) :
    (Even n → 0 < beukersA n) ∧ (Odd n → beukersA n < 0) := by
  have hsum_pos : (0 : ℤ) < ∑ r ∈ range (n + 1), (n.choose r : ℤ) ^ 2 * ((n + r).choose r : ℤ) := by
    have h0 : (1 : ℤ) ≤ ∑ r ∈ range (n + 1), (n.choose r : ℤ) ^ 2 * ((n + r).choose r : ℤ) := by
      calc (1 : ℤ) = (n.choose 0 : ℤ) ^ 2 * ((n + 0).choose 0 : ℤ) := by simp
        _ ≤ _ := Finset.single_le_sum (f := fun r => (n.choose r : ℤ) ^ 2 * ((n + r).choose r : ℤ))
            (fun r _ => by positivity) (mem_range.2 (Nat.succ_pos n))
    omega
  unfold beukersA
  constructor
  · intro he; rw [he.neg_one_pow, one_mul]; exact hsum_pos
  · intro ho; rw [ho.neg_one_pow, neg_one_mul]; omega

/- ### Section 4: Irrationality Measure Bound and Reduction -/

private lemma not_liouvilleWith_of_alternating_approx
    {x : ℝ} (p q : ℕ → ℤ)
    {α β C₁ C₂ : ℝ} {k : ℕ}
    (hα : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hαβ : α * β ^ k < 1)
    (hC₁ : 1 ≤ C₁) (hC₂ : 0 < C₂)
    (hpos : ∀ n, 0 < (q n : ℝ) * x + (p n : ℝ))
    (hle : ∀ n, (q n : ℝ) * x + (p n : ℝ) ≤ C₁ * β ^ n)
    (hq_abs : ∀ n, |(q n : ℝ)| ≤ C₂ * α ^ n)
    (hq_even : ∀ n, Even n → 0 < q n)
    (hq_odd : ∀ n, Odd n → q n < 0)
    {μ : ℝ} (hμ : (k + 1 : ℝ) < μ) :
    ¬ LiouvilleWith μ x := by
  intro hL
  obtain ⟨C, hC0, hfreq⟩ := hL.exists_pos
  set c₀ : ℝ := 1 / (2 * C₂ * α ^ 2 * (2 * C₁) ^ k)
  have hc₀_pos : 0 < c₀ := by positivity
  have hlower : ∀ (b : ℕ) (a : ℤ), 1 ≤ b → x ≠ (a : ℝ) / (b : ℝ) →
      c₀ / (b : ℝ) ^ (k + 1) ≤ |x - (a : ℝ) / (b : ℝ)| := by
    intro b a hb hne
    have hbpos : (0 : ℝ) < b := Nat.cast_pos.2 hb
    have hex : ∃ n : ℕ, (b : ℝ) * C₁ * β ^ n ≤ 1 / 2 := by
      have htend : Tendsto (fun n : ℕ => (b : ℝ) * C₁ * β ^ n) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul ((b : ℝ) * C₁)
      exact (htend.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
    let n := Nat.find hex
    have hn_le : (b : ℝ) * C₁ * β ^ n ≤ 1 / 2 := Nat.find_spec hex
    have hn_pos : 1 ≤ n := by
      by_contra h0
      have hn0 : n = 0 := by omega
      rw [hn0, pow_zero, mul_one] at hn_le
      have : (1 : ℝ) ≤ b := by exact_mod_cast hb
      nlinarith
    have hn_prev : 1 / 2 < (b : ℝ) * C₁ * β ^ (n - 1) := by
      have := Nat.find_min hex (show n - 1 < n by omega)
      push Not at this
      exact this
    have hex_m : ∃ m : ℕ, (m = n ∨ m = n + 1) ∧ q m * a + p m * (b : ℤ) ≠ 0 := by
      by_cases hD : q n * a + p n * (b : ℤ) ≠ 0
      · exact ⟨n, Or.inl rfl, hD⟩
      · push Not at hD
        refine ⟨n + 1, Or.inr rfl, ?_⟩
        intro hD1
        have h1 : (q n : ℝ) * ((a : ℝ) / (b : ℝ)) + (p n : ℝ) = 0 := by
          have hcast : ((q n * a + p n * (b : ℤ) : ℤ) : ℝ) = 0 := by exact_mod_cast hD
          push_cast at hcast
          field_simp [hbpos.ne']
          linarith
        have h2 : (q (n + 1) : ℝ) * ((a : ℝ) / (b : ℝ)) + (p (n + 1) : ℝ) = 0 := by
          have hcast : ((q (n + 1) * a + p (n + 1) * (b : ℤ) : ℤ) : ℝ) = 0 := by
            exact_mod_cast hD1
          push_cast at hcast
          field_simp [hbpos.ne']
          linarith
        have hp1 : 0 < (q n : ℝ) * (x - (a : ℝ) / (b : ℝ)) := by linarith [hpos n]
        have hp2 : 0 < (q (n + 1) : ℝ) * (x - (a : ℝ) / (b : ℝ)) := by linarith [hpos (n + 1)]
        rcases Nat.even_or_odd n with he | ho
        · have hqn : (0 : ℝ) < q n := by exact_mod_cast hq_even n he
          have hqn1 : (q (n + 1) : ℝ) < 0 := by exact_mod_cast hq_odd (n + 1) (he.add_one)
          have hxa1 : 0 < x - (a : ℝ) / (b : ℝ) := pos_of_mul_pos_right hp1 hqn.le
          nlinarith
        · have hqn : (q n : ℝ) < 0 := by exact_mod_cast hq_odd n ho
          have hqn1 : (0 : ℝ) < q (n + 1) := by exact_mod_cast hq_even (n + 1) (ho.add_one)
          have hxa1 : 0 < x - (a : ℝ) / (b : ℝ) := pos_of_mul_pos_right hp2 hqn1.le
          nlinarith
    obtain ⟨m, hm_or, hDm⟩ := hex_m
    have hmn : n ≤ m := by rcases hm_or with rfl | rfl <;> omega
    have hm_le : m ≤ n + 1 := by rcases hm_or with rfl | rfl <;> omega
    have hD1 : (1 : ℝ) ≤ |((q m * a + p m * (b : ℤ) : ℤ) : ℝ)| := by
      have : 1 ≤ |q m * a + p m * (b : ℤ)| := Int.one_le_abs hDm
      exact_mod_cast this
    have hD_tri : |((q m * a + p m * (b : ℤ) : ℤ) : ℝ)| ≤
        |(q m : ℝ)| * (b : ℝ) * |x - (a : ℝ) / (b : ℝ)| +
          (b : ℝ) * |(q m : ℝ) * x + (p m : ℝ)| := by
      have hid : ((q m * a + p m * (b : ℤ) : ℤ) : ℝ) =
          -(q m : ℝ) * (b : ℝ) * (x - (a : ℝ) / (b : ℝ)) +
            (b : ℝ) * ((q m : ℝ) * x + (p m : ℝ)) := by
        push_cast; field_simp [hbpos.ne']; ring
      rw [hid]
      calc |-(q m : ℝ) * (b : ℝ) * (x - (a : ℝ) / (b : ℝ)) +
              (b : ℝ) * ((q m : ℝ) * x + (p m : ℝ))|
          ≤ |-(q m : ℝ) * (b : ℝ) * (x - (a : ℝ) / (b : ℝ))| +
              |(b : ℝ) * ((q m : ℝ) * x + (p m : ℝ))| := abs_add_le _ _
        _ = |(q m : ℝ)| * (b : ℝ) * |x - (a : ℝ) / (b : ℝ)| +
              (b : ℝ) * |(q m : ℝ) * x + (p m : ℝ)| := by
            rw [abs_mul, abs_mul, abs_neg, abs_mul, abs_of_pos hbpos]
    have herr_m : (b : ℝ) * |(q m : ℝ) * x + (p m : ℝ)| ≤ 1 / 2 := by
      rw [abs_of_pos (hpos m)]
      calc (b : ℝ) * ((q m : ℝ) * x + (p m : ℝ))
          ≤ (b : ℝ) * (C₁ * β ^ m) := mul_le_mul_of_nonneg_left (hle m) hbpos.le
        _ = (b : ℝ) * C₁ * β ^ m := by ring
        _ ≤ (b : ℝ) * C₁ * β ^ n :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hβ0.le hβ1.le hmn) (by positivity)
        _ ≤ 1 / 2 := hn_le
    have hhalf : 1 / 2 ≤ |(q m : ℝ)| * (b : ℝ) * |x - (a : ℝ) / (b : ℝ)| := by linarith
    have hqm_le : |(q m : ℝ)| ≤ C₂ * α ^ (n + 1) := by
      calc |(q m : ℝ)| ≤ C₂ * α ^ m := hq_abs m
        _ ≤ C₂ * α ^ (n + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hα.le hm_le) hC₂.le
    have hα_bd : α ^ (n - 1) ≤ (2 * C₁ * (b : ℝ)) ^ k := by
      have hinv : (1 / β) ^ (n - 1) ≤ 2 * C₁ * (b : ℝ) := by
        rw [one_div, inv_pow, inv_eq_one_div, div_le_iff₀ (pow_pos hβ0 _)]
        linarith
      have hα_lt : α ≤ (1 / β) ^ k := by
        rw [div_pow, one_pow, le_div_iff₀ (pow_pos hβ0 _)]
        exact hαβ.le
      calc α ^ (n - 1) ≤ ((1 / β) ^ k) ^ (n - 1) := pow_le_pow_left₀ (by linarith) hα_lt _
        _ = ((1 / β) ^ (n - 1)) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (2 * C₁ * (b : ℝ)) ^ k := pow_le_pow_left₀ (by positivity) hinv k
    have hα_n1 : α ^ (n + 1) ≤ α ^ 2 * (2 * C₁) ^ k * (b : ℝ) ^ k := by
      have hpow : α ^ (n + 1) = α ^ 2 * α ^ (n - 1) := by
        rw [← pow_add]; congr 1; omega
      rw [hpow]
      calc α ^ 2 * α ^ (n - 1) ≤ α ^ 2 * (2 * C₁ * (b : ℝ)) ^ k :=
            mul_le_mul_of_nonneg_left hα_bd (by positivity)
        _ = α ^ 2 * (2 * C₁) ^ k * (b : ℝ) ^ k := by rw [mul_pow]; ring
    have hqb : |(q m : ℝ)| * (b : ℝ) ≤ C₂ * α ^ 2 * (2 * C₁) ^ k * (b : ℝ) ^ (k + 1) := by
      calc |(q m : ℝ)| * (b : ℝ)
          ≤ (C₂ * α ^ (n + 1)) * (b : ℝ) := mul_le_mul_of_nonneg_right hqm_le hbpos.le
        _ ≤ (C₂ * (α ^ 2 * (2 * C₁) ^ k * (b : ℝ) ^ k)) * (b : ℝ) := by gcongr
        _ = C₂ * α ^ 2 * (2 * C₁) ^ k * (b : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
    have hmul_le : 1 / 2 ≤
        (C₂ * α ^ 2 * (2 * C₁) ^ k * (b : ℝ) ^ (k + 1)) * |x - (a : ℝ) / (b : ℝ)| := by
      calc 1 / 2 ≤ |(q m : ℝ)| * (b : ℝ) * |x - (a : ℝ) / (b : ℝ)| := hhalf
        _ ≤ (C₂ * α ^ 2 * (2 * C₁) ^ k * (b : ℝ) ^ (k + 1)) * |x - (a : ℝ) / (b : ℝ)| :=
          mul_le_mul_of_nonneg_right hqb (abs_nonneg _)
    rw [show c₀ / (b : ℝ) ^ (k + 1) =
        (1 / 2) / (C₂ * α ^ 2 * (2 * C₁) ^ k * (b : ℝ) ^ (k + 1)) by
      dsimp only [c₀]; field_simp]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hev : ∀ᶠ b : ℕ in atTop, C / (b : ℝ) ^ μ ≤ c₀ / (b : ℝ) ^ (k + 1) := by
    have hpow : Tendsto (fun b : ℕ => (b : ℝ) ^ (μ - (k + 1 : ℝ))) atTop atTop :=
      (tendsto_rpow_atTop (sub_pos.2 hμ)).comp tendsto_natCast_atTop_atTop
    filter_upwards [hpow.eventually (eventually_ge_atTop (C / c₀)), eventually_ge_atTop 1] with b hb hge1
    have hbpos : (0 : ℝ) < b := Nat.cast_pos.2 hge1
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hbpos _) (pow_pos hbpos _)]
    have hsplit : (b : ℝ) ^ μ = (b : ℝ) ^ (k + 1) * (b : ℝ) ^ (μ - (k + 1 : ℝ)) := by
      rw [← Real.rpow_natCast (b : ℝ) (k + 1), ← Real.rpow_add hbpos]
      congr 1; push_cast; ring
    rw [hsplit]
    have h1 : C ≤ c₀ * (b : ℝ) ^ (μ - (k + 1 : ℝ)) := by
      linarith [(div_le_iff₀ hc₀_pos).1 hb]
    have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hbpos.le (k + 1))
    linarith
  obtain ⟨b, hle_b, hb1, a, hne, hlt⟩ := (hev.and_frequently hfreq).exists
  have hlo := hlower b a hb1 hne
  linarith

private lemma not_liouvilleWith_zeta_two {μ : ℝ} (hμ : (21 : ℝ) < μ) :
    ¬ LiouvilleWith μ (π ^ 2 / 6) := by
  obtain ⟨Cd, hCd_pos, hCd⟩ := lcmUpto_le
  obtain ⟨Ca, hCa_pos, hCa⟩ := beukersA_abs_le
  choose p hp using beukersB_denom_int
  let q : ℕ → ℤ := fun n => (Nat.lcmUpto n : ℤ) ^ 2 * beukersA n
  let α : ℝ := (59 / 20 : ℝ) ^ 2 * (111 / 10 : ℝ)
  let β : ℝ := (59 / 20 : ℝ) ^ 2 * (451 / 5000 : ℝ)
  have hα : 1 < α := by dsimp [α]; norm_num
  have hβ0 : 0 < β := by dsimp [β]; norm_num
  have hβ1 : β < 1 := by dsimp [β]; norm_num
  have hαβ : α * β ^ 20 < 1 := by dsimp [α, β]; norm_num
  set C₁ : ℝ := max (Cd ^ 2 * (π ^ 2 / 6)) 1
  have hC₁ : 1 ≤ C₁ := le_max_right _ _
  set C₂ : ℝ := Cd ^ 2 * Ca
  have hC₂ : 0 < C₂ := by positivity
  refine not_liouvilleWith_of_alternating_approx p q hα hβ0 hβ1 hαβ hC₁ hC₂ ?_ ?_ ?_ ?_ ?_ (by norm_num [hμ])
  · intro n
    have hrew : (q n : ℝ) * (π ^ 2 / 6) + (p n : ℝ) =
        (Nat.lcmUpto n : ℝ) ^ 2 * ((beukersA n : ℝ) * (π ^ 2 / 6) + (beukersB n : ℝ)) := by
      dsimp [q]; rw [hp n]; push_cast; ring
    rw [hrew]
    exact mul_pos (pow_pos (Nat.cast_pos.2 (Nat.lcmUpto_pos n)) 2) (beukers_integral_bounds n).1
  · intro n
    have hrew : (q n : ℝ) * (π ^ 2 / 6) + (p n : ℝ) =
        (Nat.lcmUpto n : ℝ) ^ 2 * ((beukersA n : ℝ) * (π ^ 2 / 6) + (beukersB n : ℝ)) := by
      dsimp [q]; rw [hp n]; push_cast; ring
    rw [hrew]
    have hd2 : (Nat.lcmUpto n : ℝ) ^ 2 ≤ Cd ^ 2 * ((59 / 20 : ℝ) ^ 2) ^ n := by
      have h1 := pow_le_pow_left₀ (Nat.cast_nonneg _) (hCd n) 2
      rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul] at h1
      exact h1
    calc (Nat.lcmUpto n : ℝ) ^ 2 * ((beukersA n : ℝ) * (π ^ 2 / 6) + (beukersB n : ℝ))
        ≤ (Cd ^ 2 * ((59 / 20 : ℝ) ^ 2) ^ n) * ((451 / 5000 : ℝ) ^ n * (π ^ 2 / 6)) :=
          mul_le_mul hd2 (beukers_integral_bounds n).2
            (beukers_integral_bounds n).1.le (by positivity)
      _ = (Cd ^ 2 * (π ^ 2 / 6)) * β ^ n := by
          dsimp [β]; rw [mul_pow]; ring
      _ ≤ C₁ * β ^ n := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · intro n
    dsimp [q]
    push_cast
    rw [abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg _)]
    have hd2 : (Nat.lcmUpto n : ℝ) ^ 2 ≤ Cd ^ 2 * ((59 / 20 : ℝ) ^ 2) ^ n := by
      have h1 := pow_le_pow_left₀ (Nat.cast_nonneg _) (hCd n) 2
      rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul] at h1
      exact h1
    calc (Nat.lcmUpto n : ℝ) ^ 2 * |(beukersA n : ℝ)|
        ≤ (Cd ^ 2 * ((59 / 20 : ℝ) ^ 2) ^ n) * (Ca * (111 / 10 : ℝ) ^ n) :=
          mul_le_mul hd2 (hCa n) (abs_nonneg _) (by positivity)
      _ = C₂ * α ^ n := by dsimp [C₂, α]; rw [mul_pow]; ring
  · intro n he
    dsimp [q]
    exact mul_pos (pow_pos (by exact_mod_cast Nat.lcmUpto_pos n) 2) ((beukersA_sign n).1 he)
  · intro n ho
    dsimp [q]
    exact mul_neg_of_pos_of_neg (pow_pos (by exact_mod_cast Nat.lcmUpto_pos n) 2)
      ((beukersA_sign n).2 ho)

private lemma liouvilleWith_sq_div_six_of_pi {p : ℝ} (hp : 0 ≤ p) (h : LiouvilleWith p π) :
    LiouvilleWith (p / 2) (π ^ 2 / 6) := by
  have hsq : LiouvilleWith (p / 2) (π ^ 2) := by
    obtain ⟨C, hC0, hfreq⟩ := h.exists_pos
    refine ⟨(2 * π + C) * C, ?_⟩
    have hsq_tendsto : Tendsto (fun n : ℕ => n ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num)
    refine hsq_tendsto.frequently (hfreq.mono ?_)
    rintro n ⟨hn1, m, hne, hlt⟩
    refine ⟨m ^ 2, ?_, ?_⟩
    · intro heq
      have h1 : (π - (m : ℝ) / n) * (π + (m : ℝ) / n) = 0 := by
        push_cast at heq
        have : ((m : ℝ) / n) ^ 2 = (m : ℝ) ^ 2 / (n : ℝ) ^ 2 := div_pow _ _ 2
        linarith
      rcases mul_eq_zero.1 h1 with hsub | hadd
      · exact hne (sub_eq_zero.1 hsub)
      · exact irrational_pi ⟨((-m : ℤ) : ℚ) / (n : ℚ), by
          push_cast
          have : (-(m : ℝ)) / (n : ℝ) = -((m : ℝ) / (n : ℝ)) := neg_div _ _
          linarith⟩
    · have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
      have hnpow1 : (1 : ℝ) ≤ (n : ℝ) ^ p :=
        Real.one_le_rpow (by exact_mod_cast hn1) hp
      have hdiffC : |π - (m : ℝ) / n| < C := by
        calc |π - (m : ℝ) / n| < C / (n : ℝ) ^ p := hlt
          _ ≤ C / 1 := div_le_div_of_nonneg_left hC0.le zero_lt_one hnpow1
          _ = C := div_one C
      have hsum_bd : |π + (m : ℝ) / n| ≤ 2 * π + C := by
        have hrew : π + (m : ℝ) / n = 2 * π - (π - (m : ℝ) / n) := by ring
        rw [hrew]
        calc |2 * π - (π - (m : ℝ) / n)|
            ≤ |2 * π| + |π - (m : ℝ) / n| := abs_sub _ _
          _ = 2 * π + |π - (m : ℝ) / n| := by rw [abs_of_pos (by positivity)]
          _ ≤ 2 * π + C := by linarith
      have hdiff_sq : π ^ 2 - ((m ^ 2 : ℤ) : ℝ) / ((n ^ 2 : ℕ) : ℝ) =
          (π + (m : ℝ) / n) * (π - (m : ℝ) / n) := by
        push_cast; field_simp [hnpos.ne']; ring
      rw [hdiff_sq, abs_mul]
      have hden_eq : (((n ^ 2 : ℕ) : ℝ)) ^ (p / 2) = (n : ℝ) ^ p := by
        push_cast
        rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_mul hnpos.le]
        congr 1; ring
      rw [hden_eq, mul_div_assoc]
      calc |π + (m : ℝ) / n| * |π - (m : ℝ) / n|
          ≤ (2 * π + C) * |π - (m : ℝ) / n| :=
            mul_le_mul_of_nonneg_right hsum_bd (abs_nonneg _)
        _ < (2 * π + C) * (C / (n : ℝ) ^ p) :=
            mul_lt_mul_of_pos_left hlt (by positivity)
  have hmul := hsq.mul_rat (r := (1 / 6 : ℚ)) (by norm_num)
  simpa [div_eq_mul_inv] using hmul

private lemma c7a_le_42_proof : Constant7a.C7a ≤ 42 := by
  unfold Constant7a.C7a Constant7a.irrationalityExponent
  rw [sSup_le_iff]
  rintro x ⟨p, hp, rfl⟩
  by_contra hgt
  push Not at hgt
  have hp42 : (42 : ℝ) < (p : ℝ) := by
    have : (42 : NNReal) < p := by
      exact_mod_cast hgt
    exact_mod_cast this
  have h21 : (21 : ℝ) < (p : ℝ) / 2 := by linarith
  exact not_liouvilleWith_zeta_two h21 (liouvilleWith_sq_div_six_of_pi p.coe_nonneg hp)

end PiIrrationality42

theorem OMA.solution : type_of% @Constant7a.c7a_le_42 :=
  PiIrrationality42.c7a_le_42_proof
