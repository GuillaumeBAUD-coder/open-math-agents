import FormalConjectures.ErdosProblems.«394»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Chebyshev lower bound for the sum of `Erdos394.t 2`.
-/

-- Problem: Erdős Problem 394 — lower bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/394.lean:112 (declaration Erdos394.erdos_394.variants.lower_bound)
-- Credit: @mbilenko03 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset Filter Asymptotics Nat Chebyshev

lemma t_two_prime {p : ℕ} (hp : p.Prime) : Erdos394.t 2 p = p - 1 := by
  have hlt : 1 < p := hp.one_lt
  refine Erdos394.t_eq_of (Nat.sub_pos_of_lt hlt) ?_ ?_
  · have hprod : ∏ i ∈ range 2, ((p - 1) + i) = (p - 1) * p := by
      rw [prod_range_succ, prod_range_succ, prod_range_zero, one_mul, add_zero,
        Nat.sub_add_cancel hlt.le]
    rw [hprod]
    exact dvd_mul_left _ _
  · intro m hm hm0
    have hm' : m < p - 1 := mem_range.mp hm
    rw [prod_range_succ, prod_range_succ, prod_range_zero, one_mul, add_zero]
    have h1 : m + 1 < p := by omega
    have h0 : m < p := by omega
    exact hp.not_dvd_mul (not_dvd_of_pos_of_lt hm0 h0) (not_dvd_of_pos_of_lt (Nat.succ_pos _) h1)

lemma sum_t_ge_primes (n : ℕ) :
    ∑ p ∈ primesLE n, ((p : ℝ) - 1) ≤ ∑ k ∈ Icc 1 n, (Erdos394.t 2 k : ℝ) := by
  have hsub : primesLE n ⊆ Icc 1 n := by
    intro p hp
    have hmem := mem_primesLE.mp hp
    refine mem_Icc.mpr ⟨?_, hmem.1⟩
    have := hmem.2.two_le
    omega
  calc
    ∑ p ∈ primesLE n, ((p : ℝ) - 1) = ∑ p ∈ primesLE n, (Erdos394.t 2 p : ℝ) := by
      refine sum_congr rfl fun p hp => ?_
      have hmem := mem_primesLE.mp hp
      rw [t_two_prime hmem.2]
      simpa [Nat.cast_one] using
        (Nat.cast_sub hmem.2.one_lt.le : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - (1 : ℕ)).symm
    _ ≤ ∑ k ∈ Icc 1 n, (Erdos394.t 2 k : ℝ) := by
      refine sum_le_sum_of_subset_of_nonneg hsub ?_
      intro k _ _
      exact Nat.cast_nonneg _

lemma log_add_two_eventually :
    ∀ᶠ n : ℕ in atTop, Real.log ((n : ℝ) + 2) ≤ Real.log 2 / 16 * ((n : ℝ) + 2) := by
  have hε : 0 < Real.log 2 / 16 := by
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity
  have hten : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  have hbnd : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ Real.log 2 / 16 * ‖x‖ := by
    simpa [id_eq] using Real.isLittleO_log_id_atTop.bound hε
  filter_upwards [hten.eventually hbnd] with n hn
  have hxpos : 0 < (n : ℝ) + 2 := by positivity
  have hlogpos : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  rw [Real.norm_eq_abs, abs_of_pos hlogpos, Real.norm_eq_abs, abs_of_pos hxpos] at hn
  exact hn

lemma log_sqrt_eventually :
    ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ≤ Real.log 2 / 16 * Real.sqrt (n : ℝ) := by
  have hε : 0 < Real.log 2 / 16 := by
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity
  have hr : 0 < (1 : ℝ) / 2 := by norm_num
  have hten : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hbnd : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ Real.log 2 / 16 * ‖x ^ ((1 : ℝ) / 2)‖ :=
    (isLittleO_log_rpow_atTop hr).bound hε
  filter_upwards [hten.eventually hbnd, eventually_gt_atTop 1] with n hn hn1
  have hx : (1 : ℝ) < n := by exact_mod_cast hn1
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hx
  have hrpow : 0 < (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.norm_eq_abs, abs_of_pos hlogpos, Real.norm_eq_abs, abs_of_pos hrpow] at hn
  rw [← Real.sqrt_eq_rpow] at hn
  exact hn

set_option maxHeartbeats 2000000 in
lemma sum_ge_of_bounds {n : ℕ} (hn : 16 ≤ n)
    (hlog1 : Real.log ((n : ℝ) + 2) ≤ Real.log 2 / 16 * ((n : ℝ) + 2))
    (hlog2 : Real.log (n : ℝ) ≤ Real.log 2 / 16 * Real.sqrt (n : ℝ)) :
    Real.log 2 / 64 * ((n : ℝ) ^ 2 / Real.log (n : ℝ)) ≤
      ∑ k ∈ Icc 1 n, (Erdos394.t 2 k : ℝ) := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hA : Real.log 2 ≤ Real.log 2 / 8 * (n : ℝ) := by
    have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast (show 8 ≤ n by omega)
    nlinarith
  have hB : Real.log ((n : ℝ) + 2) ≤ Real.log 2 / 8 * (n : ℝ) := by
    have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
    calc
      Real.log ((n : ℝ) + 2) ≤ Real.log 2 / 16 * ((n : ℝ) + 2) := hlog1
      _ = Real.log 2 / 16 * (n : ℝ) + Real.log 2 / 8 := by ring
      _ ≤ Real.log 2 / 8 * (n : ℝ) := by nlinarith
  have hC : 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ Real.log 2 / 8 * (n : ℝ) := by
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = n :=
      Real.mul_self_sqrt (Nat.cast_nonneg n)
    have hstep : 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤
        2 * Real.sqrt (n : ℝ) * (Real.log 2 / 16 * Real.sqrt (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hlog2
      positivity
    calc
      2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)
          ≤ 2 * Real.sqrt (n : ℝ) * (Real.log 2 / 16 * Real.sqrt (n : ℝ)) := hstep
      _ = Real.log 2 / 8 * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
      _ = Real.log 2 / 8 * (n : ℝ) := by rw [hsq]
  have herr : Real.log 2 + Real.log ((n : ℝ) + 2) +
      2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ 3 / 8 * Real.log 2 * (n : ℝ) := by
    linarith [hA, hB, hC]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hge := theta_ge' (x := (n : ℝ)) hn1
  have hup := theta_le_log4_mul_x (x := (n : ℝ) / 16) (by positivity)
  have hrest : Real.log 2 / 2 * (n : ℝ) ≤
      ((n : ℝ) - 1) * Real.log 2 - Real.log ((n : ℝ) + 2) -
        2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) - Real.log 4 * ((n : ℝ) / 16) := by
    rw [hlog4]
    linarith
  have hgap : Real.log 2 / 2 * (n : ℝ) ≤ theta (n : ℝ) - theta ((n : ℝ) / 16) := by
    linarith
  let large := (primesLE n).filter (fun p => n < p * 16)
  have hsmall_set : (primesLE n).filter (fun p => p * 16 ≤ n) = primesLE (n / 16) := by
    ext p
    simp only [mem_filter, mem_primesLE]
    constructor
    · intro h
      obtain ⟨⟨_, hp⟩, hmul⟩ := h
      exact ⟨(Nat.le_div_iff_mul_le (by norm_num : 0 < 16)).2 hmul, hp⟩
    · intro h
      obtain ⟨hdiv, hp⟩ := h
      have hmul : p * 16 ≤ n := (Nat.le_div_iff_mul_le (by norm_num : 0 < 16)).1 hdiv
      exact ⟨⟨le_trans hdiv (Nat.div_le_self n 16), hp⟩, hmul⟩
  have hlogeq : ∑ p ∈ large, Real.log (p : ℝ) =
      theta (n : ℝ) - theta ((n : ℝ) / 16) := by
    have hadd := sum_filter_add_sum_filter_not (primesLE n) (fun p => n < p * 16)
      (fun p => Real.log (p : ℝ))
    have hnot : (primesLE n).filter (fun p => ¬ n < p * 16) =
        (primesLE n).filter (fun p => p * 16 ≤ n) := by
      ext p
      simp [not_lt]
    have hfloor : ⌊(n : ℝ) / 16⌋₊ = n / 16 := Nat.floor_div_eq_div n 16
    have hsmall : ∑ p ∈ primesLE (n / 16), Real.log (p : ℝ) = theta ((n : ℝ) / 16) := by
      simpa [hfloor] using (theta_eq_sum_primesLE ((n : ℝ) / 16)).symm
    have hall : ∑ p ∈ primesLE n, Real.log (p : ℝ) = theta (n : ℝ) :=
      (theta_eq_sum_primesLE_log n).symm
    rw [hnot, hsmall_set, hsmall, hall] at hadd
    linarith
  have hcard : theta (n : ℝ) - theta ((n : ℝ) / 16) ≤ (large.card : ℝ) * Real.log (n : ℝ) := by
    rw [← hlogeq]
    have hpoint : ∑ p ∈ large, Real.log (p : ℝ) ≤ ∑ p ∈ large, Real.log (n : ℝ) := by
      refine sum_le_sum fun p hp => ?_
      have hmem := mem_primesLE.mp (mem_filter.mp hp).1
      have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hmem.2.pos
      exact Real.log_le_log hp_pos (by exact_mod_cast hmem.1)
    have hconst : ∑ p ∈ large, Real.log (n : ℝ) = (large.card : ℝ) * Real.log (n : ℝ) := by
      rw [sum_const, nsmul_eq_mul]
    linarith
  have hcard' : (theta (n : ℝ) - theta ((n : ℝ) / 16)) / Real.log (n : ℝ) ≤ large.card :=
    (div_le_iff₀ hlogn).2 (by simpa [mul_comm] using hcard)
  have hsum_const : ∑ p ∈ large, (n : ℝ) / 16 = (n : ℝ) / 16 * (large.card : ℝ) := by
    rw [sum_const, nsmul_eq_mul, mul_comm]
  have hsump : (n : ℝ) / 16 * (large.card : ℝ) ≤ ∑ p ∈ large, (p : ℝ) := by
    rw [← hsum_const]
    refine sum_le_sum fun p hp => ?_
    have hlt : n < p * 16 := (mem_filter.mp hp).2
    have : (n : ℝ) ≤ (p : ℝ) * 16 := by exact_mod_cast hlt.le
    rwa [div_le_iff₀ (by norm_num : (0 : ℝ) < 16)]
  have hhalf_pt : ∀ p ∈ large, (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by
    intro p hp
    have hp2 : 2 ≤ p := (mem_primesLE.mp (mem_filter.mp hp).1).2.two_le
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  have hhalf : (∑ p ∈ large, (p : ℝ)) / 2 ≤ ∑ p ∈ large, ((p : ℝ) - 1) := by
    have hdiv : ∑ p ∈ large, (p : ℝ) / 2 = (∑ p ∈ large, (p : ℝ)) / 2 := by
      simp_rw [div_eq_mul_inv]
      exact (sum_mul large (fun p => (p : ℝ)) (2 : ℝ)⁻¹).symm
    rw [← hdiv]
    exact sum_le_sum hhalf_pt
  have hsublarge : ∑ p ∈ large, ((p : ℝ) - 1) ≤ ∑ p ∈ primesLE n, ((p : ℝ) - 1) := by
    refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) ?_
    intro p hp _
    have hp2 : 2 ≤ p := (mem_primesLE.mp hp).2.two_le
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  have hcoeff : Real.log 2 / 64 * ((n : ℝ) ^ 2 / Real.log (n : ℝ)) =
      (1 / 2) * ((n : ℝ) / 16) *
        ((Real.log 2 / 2) * (n : ℝ) / Real.log (n : ℝ)) := by
    field_simp
    ring
  have hposHalf : 0 ≤ (1 : ℝ) / 2 * ((n : ℝ) / 16) := by positivity
  calc
    Real.log 2 / 64 * ((n : ℝ) ^ 2 / Real.log (n : ℝ))
        = (1 / 2) * ((n : ℝ) / 16) *
            ((Real.log 2 / 2) * (n : ℝ) / Real.log (n : ℝ)) := hcoeff
    _ ≤ (1 / 2) * ((n : ℝ) / 16) *
          ((theta (n : ℝ) - theta ((n : ℝ) / 16)) / Real.log (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hposHalf
        exact div_le_div_of_nonneg_right hgap hlogn.le
    _ ≤ (1 / 2) * ((n : ℝ) / 16) * (large.card : ℝ) := by
        apply mul_le_mul_of_nonneg_left hcard' hposHalf
    _ = (1 / 2) * ((n : ℝ) / 16 * (large.card : ℝ)) := by ring
    _ ≤ (1 / 2) * ∑ p ∈ large, (p : ℝ) := by
        apply mul_le_mul_of_nonneg_left hsump
        norm_num
    _ = (∑ p ∈ large, (p : ℝ)) / 2 := by ring
    _ ≤ ∑ p ∈ large, ((p : ℝ) - 1) := hhalf
    _ ≤ ∑ p ∈ primesLE n, ((p : ℝ) - 1) := hsublarge
    _ ≤ ∑ k ∈ Icc 1 n, (Erdos394.t 2 k : ℝ) := sum_t_ge_primes n

lemma eventually_sum_ge :
    ∀ᶠ n : ℕ in atTop,
      Real.log 2 / 64 * ((n : ℝ) ^ 2 / Real.log (n : ℝ)) ≤
        ∑ k ∈ Icc 1 ⌊(n : ℝ)⌋₊, (Erdos394.t 2 k : ℝ) := by
  filter_upwards [log_add_two_eventually, log_sqrt_eventually, eventually_ge_atTop 16]
    with n h1 h2 hn
  rw [Nat.floor_natCast]
  exact sum_ge_of_bounds hn h1 h2

theorem OMA.solution : type_of% @Erdos394.erdos_394.variants.lower_bound := by
  refine IsBigO.of_bound (64 / Real.log 2) ?_
  filter_upwards [eventually_sum_ge, eventually_ge_atTop 3] with n hn hn3
  have hfloor : ⌊n⌋₊ = n := rfl
  simp only [Nat.floor_natCast, hfloor] at hn ⊢
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hleft : 0 ≤ (n : ℝ) ^ 2 / Real.log (n : ℝ) := div_nonneg (sq_nonneg _) hlog.le
  have hright : 0 ≤ ∑ k ∈ Icc 1 n, (Erdos394.t 2 k : ℝ) :=
    sum_nonneg fun _ _ => Nat.cast_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright]
  have hpos : 0 < Real.log 2 / 64 := by
    have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity
  rw [← mul_le_mul_iff_of_pos_left hpos]
  calc
    Real.log 2 / 64 * ((n : ℝ) ^ 2 / Real.log (n : ℝ)) ≤
        ∑ k ∈ Icc 1 n, (Erdos394.t 2 k : ℝ) := hn
    _ = Real.log 2 / 64 * ((64 / Real.log 2) *
        ∑ k ∈ Icc 1 n, (Erdos394.t 2 k : ℝ)) := by
      field_simp
