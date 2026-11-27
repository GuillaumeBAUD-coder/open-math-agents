import OMAReductions.R_Erdos688_erdos_688_variants_lglglg_over_lglg_is_big_o_R1
import Mathlib

/-! The smooth-number estimates below are excerpted from OpenAI's
LongGapsBetweenPrimes.lean, commit 03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b,
via @marcusbuffett's merged Rankin proof (PR 2593). Used under Apache-2.0.
Upstream source: https://github.com/openai/LongGapsBetweenPrimes
SPDX-License-Identifier: Apache-2.0

The final step uses the estimate at x = H = n. -/

namespace LongGapsBetweenPrimes
noncomputable section
/-- The logarithms of distinct prime divisors sum to at most `log n`. -/
lemma sum_log_prime_divisors_le_log {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (∑ p ∈ N.primesLE, if p ∣ n then Real.log p else 0) ≤ Real.log n := by
  have hfilter : N.primesLE.filter (fun p => p ∣ n) = n.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
    exact ⟨fun h => ⟨h.1.2, h.2, hn.ne'⟩,
      fun h => ⟨⟨(Nat.le_of_dvd hn h.2.1).trans hnN, h.1⟩, h.2.1⟩⟩
  rw [← Finset.sum_filter, hfilter, ← Real.log_prod (fun p hp =>
    Nat.cast_ne_zero.mpr (Nat.mem_primeFactors.mp hp).1.ne_zero)]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp =>
      Nat.cast_pos.mpr (Nat.mem_primeFactors.mp hp).1.pos
  · rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/-- An elementary upper bound for the logarithmically weighted prime harmonic sum. -/
theorem sum_prime_log_div_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ N.primesLE, Real.log p / p) ≤ Real.log N + Real.log 4 := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcount (p : ℕ) (_hp : p ∈ N.primesLE) :
      (N : ℝ) / p - 1 ≤ (N / p : ℕ) := by
    simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using
      (Nat.sub_one_lt_floor ((N : ℝ) / p)).le
  have hsum : (∑ p ∈ N.primesLE, ((N / p : ℕ) : ℝ) * Real.log p) ≤
      (N : ℝ) * Real.log N := by
    calc
      _ = ∑ p ∈ N.primesLE, ∑ n ∈ Finset.range N,
          if p ∣ n + 1 then Real.log p else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [← Nat.card_multiples N p, ← Finset.sum_boole]
        simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
      _ = ∑ n ∈ Finset.range N, ∑ p ∈ N.primesLE,
          if p ∣ n + 1 then Real.log p else 0 := Finset.sum_comm
      _ ≤ ∑ n ∈ Finset.range N, Real.log N := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN : n + 1 ≤ N := by simpa using Finset.mem_range.mp hn
        exact (sum_log_prime_divisors_le_log (by omega : 0 < n + 1) hnN).trans
          (Real.log_le_log (by positivity) (by exact_mod_cast hnN))
      _ = (N : ℝ) * Real.log N := by simp
  have hlower : (N : ℝ) * (∑ p ∈ N.primesLE, Real.log p / p) -
      Chebyshev.theta N ≤ (N : ℝ) * Real.log N := by
    apply le_trans _ hsum
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have h := mul_le_mul_of_nonneg_right (hcount p hp)
      (Nat.mem_primesLE.mp hp).2.log_pos.le
    calc
      (N : ℝ) * (Real.log p / p) - Real.log p =
        ((N : ℝ) / p - 1) * Real.log p := by ring
      _ ≤ _ := h
  have htheta := Chebyshev.theta_le_log4_mul_x hNr.le
  apply (mul_le_mul_iff_right₀ hNr).mp
  nlinarith

/-- The finite Euler product over primes at most N. -/
def eulerProduct (N : ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ N.primesLE, (1 - (p : ℝ) ^ (-σ))⁻¹

/-- The multiplicative weight `n ↦ n ^ (-σ)`. -/
def natPowerHom (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_one' := by simp
  map_mul' a b := by
    simp only [Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The weighted sum over smooth numbers is bounded by the finite Euler product. -/
lemma sum_smooth_le_eulerProduct {N : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (S : Finset ℕ) (hS : ∀ n ∈ S, n ∈ (N + 1).smoothNumbers) :
    (∑ n ∈ S, (n : ℝ) ^ (-σ)) ≤ eulerProduct N σ := by
  classical
  have hprime {p : ℕ} (hp : p.Prime) : ‖natPowerHom σ p‖ < 1 := by
    change ‖(p : ℝ) ^ (-σ)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hσ)
  have hsum :=
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := natPowerHom σ) hprime (N + 1)).2
  rw [← Finset.sum_subtype_of_mem _ hS]
  exact sum_le_hasSum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hsum

/-- The elementary zeta-function bound obtained by integrating t^(-σ). -/
theorem tsum_succ_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hexp : -σ < -1 := neg_lt_neg hσ
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici 1) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) hxy (by linarith)
  have htail := AntitoneOn.tsum_comp_add_le_integral 1 (by simpa using hanti)
    (integrableOn_Ioi_rpow_of_lt hexp (by norm_num))
    (fun x hx => Real.rpow_nonneg (le_of_lt (lt_trans (by norm_num) hx)) _)
  rw [integral_Ioi_rpow_of_lt hexp (by norm_num), Nat.cast_one, Real.one_rpow,
    show -σ + 1 = -(σ - 1) by ring, neg_div_neg_eq] at htail
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-σ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hexp)
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, Real.one_rpow]
  apply add_le_add le_rfl
  simpa only [Nat.cast_add, Nat.cast_one] using htail

/-- For `σ > 1`, the finite Euler product is at most `1 + 1 / (σ - 1)`. -/
lemma eulerProduct_le_zeta_bound {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    eulerProduct N σ ≤ 1 + 1 / (σ - 1) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have ht := Summable.tsum_subtype_le (fun n : ℕ => (n : ℝ) ^ (-σ))
    ((N + 1).smoothNumbers) (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) hs
  have hseries := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := natPowerHom σ) (fun {p} hp => by
      change ‖(p : ℝ) ^ (-σ)‖ < 1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt)
        (by linarith)) (N + 1)).2
  change HasSum (fun n : (N + 1).smoothNumbers => (n.val : ℝ) ^ (-σ))
    (eulerProduct N σ) at hseries
  rw [hseries.tsum_eq] at ht
  rw [hs.tsum_eq_zero_add, Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), zero_add] at ht
  simp only [Nat.cast_add, Nat.cast_one] at ht
  exact ht.trans (tsum_succ_rpow_le hσ)

/-- Compare an Euler factor at exponent one with its shift by `r`. -/
lemma euler_factor_comparison {p r : ℝ} (hp : 2 ≤ p) (hr : 0 ≤ r) :
    (1 - p ^ (-(1 : ℝ)))⁻¹ ≤
      (1 - p ^ (-(1 + r)))⁻¹ * Real.exp (2 * r * Real.log p / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp
  have hden : 0 < 1 - p ^ (-(1 + r)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))
  have hpm : 0 < p - 1 := sub_pos.mpr hp1
  have hlog : 0 ≤ r * Real.log p := mul_nonneg hr (Real.log_pos hp1).le
  have hpow : 1 - p ^ (-r) ≤ r * Real.log p := by
    rw [Real.rpow_def_of_pos hp0]
    have h := Real.add_one_le_exp (Real.log p * -r)
    nlinarith
  rw [Real.rpow_neg_one, ← div_eq_inv_mul]
  apply (le_div_iff₀ hden).mpr
  rw [← div_eq_inv_mul]
  calc
    (1 - p ^ (-(1 + r))) / (1 - p⁻¹) =
        1 + (1 - p ^ (-r)) / (p - 1) := by
      rw [neg_add, Real.rpow_add hp0, Real.rpow_neg_one]
      field_simp
      ring
    _ ≤ 1 + (r * Real.log p) / (p - 1) :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hpow hpm.le)
    _ ≤ 1 + 2 * r * Real.log p / p := by
      apply add_le_add le_rfl
      apply (div_le_div_iff₀ hpm hp0).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) hlog]
    _ ≤ Real.exp (2 * r * Real.log p / p) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * r * Real.log p / p)

/-- Moving the Euler product to the right of its pole has bounded cost. -/
theorem eulerProduct_comparison (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    eulerProduct N 1 ≤ eulerProduct N (1 + r) *
      Real.exp (2 * r * ∑ p ∈ N.primesLE, Real.log p / p) := by
  unfold eulerProduct
  calc
    _ ≤ ∏ p ∈ N.primesLE,
        (1 - (p : ℝ) ^ (-(1 + r)))⁻¹ * Real.exp (2 * r * Real.log p / p) := by
      apply Finset.prod_le_prod
      · intro p hp
        apply inv_nonneg.mpr
        apply sub_nonneg.mpr
        exact (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt)
          (by norm_num : -(1 : ℝ) < 0)).le
      · intro p hp
        exact euler_factor_comparison
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le) hr
    _ = _ := by
      simp_rw [mul_div_assoc]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]

/-- An explicit weak Mertens upper bound, sufficient throughout the proof. -/
theorem eulerProduct_one_le {N : ℕ} (hN : 2 ≤ N) :
    eulerProduct N 1 ≤ Real.exp 6 * (1 + Real.log N) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog4 : Real.log 4 ≤ 2 * Real.log N := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 4)
        (show (4 : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith)
  have hsum : (∑ p ∈ N.primesLE, Real.log p / p) ≤ 3 * Real.log N := by
    linarith [sum_prime_log_div_le (by omega : 1 ≤ N)]
  have hcost : 2 * (Real.log N)⁻¹ * (∑ p ∈ N.primesLE, Real.log p / p) ≤ 6 := by
    calc
      _ ≤ 2 * (Real.log N)⁻¹ * (3 * Real.log N) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 6 := by field_simp; norm_num
  have hzeta : eulerProduct N (1 + (Real.log N)⁻¹) ≤ 1 + Real.log N := by
    simpa using eulerProduct_le_zeta_bound
      (lt_add_of_pos_right 1 (inv_pos.mpr hlog)) N
  calc
    _ ≤ eulerProduct N (1 + (Real.log N)⁻¹) *
        Real.exp (2 * (Real.log N)⁻¹ * ∑ p ∈ N.primesLE, Real.log p / p) :=
      eulerProduct_comparison N (inv_nonneg.mpr hlog.le)
    _ ≤ (1 + Real.log N) * Real.exp 6 :=
      mul_le_mul hzeta (Real.exp_le_exp.mpr hcost) (Real.exp_nonneg _) (by positivity)
    _ = _ := mul_comm _ _

/-- The finite Euler product is positive at every positive exponent. -/
lemma eulerProduct_pos (N : ℕ) {σ : ℝ} (hσ : 0 < σ) : 0 < eulerProduct N σ := by
  apply Finset.prod_pos
  intro p hp
  exact inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt) (by linarith)))

/-- A uniform geometric factor for the smooth-number estimate. -/
def smoothEulerConstant : ℝ := (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

/-- The smooth Euler constant is positive. -/
lemma smoothEulerConstant_pos : 0 < smoothEulerConstant := by
  exact inv_pos.mpr (sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)))

/-- The scale constant used to choose the smoothness cutoff and tilt. -/
def smoothScaleConstant : ℝ := 3 * smoothEulerConstant + 10

/-- The smoothness scale constant is positive. -/
lemma smoothScaleConstant_pos : 0 < smoothScaleConstant := by
  unfold smoothScaleConstant
  linarith [smoothEulerConstant_pos]

/-- Bound the cost of shifting an Euler factor to exponent `1 - t`. -/
lemma euler_factor_left_comparison {p t : ℝ} (hp : 2 ≤ p) (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    (1 - p ^ (-(1 - t)))⁻¹ ≤ (1 - p ^ (-(1 : ℝ)))⁻¹ *
      Real.exp (smoothEulerConstant * (p ^ t - 1) / p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hpow : p ^ (-(1 - t)) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ p ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by norm_num) hp (by norm_num)
  have hcden : 0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hden : 0 < 1 - p ^ (-(1 - t)) := by linarith
  have hnum : 0 ≤ p ^ t - 1 := sub_nonneg.mpr (Real.one_le_rpow hp1 ht)
  have hsplit : p ^ (-(1 - t)) = p ^ t / p := by
    rw [show -(1 - t) = t + -1 by ring, Real.rpow_add hp0, Real.rpow_neg_one,
      div_eq_mul_inv]
  have he : (1 - p⁻¹) * (1 - p ^ (-(1 - t)))⁻¹ =
      1 + ((p ^ t - 1) / p) / (1 - p ^ (-(1 - t))) := by
    have hpt : p ^ t < p := (div_lt_one hp0).mp (by rw [← hsplit]; linarith)
    rw [hsplit]
    field_simp [ne_of_gt hp0, ne_of_gt (sub_pos.mpr hpt)]
    ring
  have hratio : (1 - p⁻¹) * (1 - p ^ (-(1 - t)))⁻¹ ≤
      Real.exp (smoothEulerConstant * (p ^ t - 1) / p) := by
    rw [he]
    calc
      _ ≤ 1 + ((p ^ t - 1) / p) / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) := by
        exact add_le_add le_rfl
          (div_le_div_of_nonneg_left (div_nonneg hnum hp0.le) hcden (by linarith))
      _ = 1 + smoothEulerConstant * (p ^ t - 1) / p := by
        unfold smoothEulerConstant
        ring
      _ ≤ _ := by simpa only [add_comm] using
        Real.add_one_le_exp (smoothEulerConstant * (p ^ t - 1) / p)
  rw [Real.rpow_neg_one, inv_mul_eq_div]
  apply (le_div_iff₀ (show 0 < 1 - p⁻¹ by
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith)))).mpr
  simpa only [mul_comm] using hratio

/-- Bound the cost of shifting the Euler product to exponent `1 - t`. -/
lemma eulerProduct_left_comparison (N : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    eulerProduct N (1 - t) ≤ eulerProduct N 1 *
      Real.exp (smoothEulerConstant * ∑ p ∈ N.primesLE, ((p : ℝ) ^ t - 1) / p) := by
  unfold eulerProduct
  calc
    _ ≤ ∏ p ∈ N.primesLE, (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ *
        Real.exp (smoothEulerConstant * ((p : ℝ) ^ t - 1) / p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt) (by linarith)).le)
      · intro p hp
        exact euler_factor_left_comparison
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le) ht ht'
    _ = _ := by
      simp_rw [mul_div_assoc]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]

/-- A secant bound controls `p ^ t - 1` using the ratio `log p / log z`. -/
lemma rpow_secant_log {p z t : ℝ} (hp : 1 ≤ p) (hpz : p ≤ z) (hz : 1 < z)
    (ht : 0 ≤ t) : p ^ t - 1 ≤ (Real.log p / Real.log z) * (Real.exp (t * Real.log z) - 1) := by
  rcases ht.eq_or_lt with rfl | _
  · simp
  have hlogz := Real.log_pos hz
  have hratio : Real.log p / Real.log z ≤ 1 :=
    (div_le_one hlogz).mpr (Real.log_le_log (zero_lt_one.trans_le hp) hpz)
  have h := convexOn_exp.2 (Set.mem_univ (t * Real.log z)) (Set.mem_univ 0)
    (div_nonneg (Real.log_nonneg hp) hlogz.le) (sub_nonneg.mpr hratio)
    (show Real.log p / Real.log z + (1 - Real.log p / Real.log z) = 1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  have harg : Real.log p / Real.log z * (t * Real.log z) = Real.log p * t := by
    field_simp
  rw [harg, ← Real.rpow_def_of_pos (zero_lt_one.trans_le hp)] at h
  linarith

/-- Bound the shifted Euler product using the tilt and the largest prime cutoff. -/
lemma eulerProduct_left_bound {N : ℕ} {z t : ℝ} (hN : 2 ≤ N) (hNz : (N : ℝ) ≤ z)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    eulerProduct N (1 - t) ≤ eulerProduct N 1 *
      Real.exp (3 * smoothEulerConstant * Real.exp (t * Real.log z)) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hz : 1 < z := by linarith
  have hlogz := Real.log_pos hz
  have hlogN : Real.log N ≤ Real.log z :=
    Real.log_le_log (by linarith) hNz
  have hlog4 : Real.log 4 ≤ 2 * Real.log z := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 4)
        (show (4 : ℝ) ≤ z ^ 2 by nlinarith)
  have hlogs : (∑ p ∈ N.primesLE, Real.log p / p) ≤ 3 * Real.log z := by
    linarith [sum_prime_log_div_le (by omega : 1 ≤ N)]
  have hsum : (∑ p ∈ N.primesLE, ((p : ℝ) ^ t - 1) / p) ≤
      3 * Real.exp (t * Real.log z) := by
    calc
      _ ≤ ∑ p ∈ N.primesLE,
          (Real.log p / p) * (Real.exp (t * Real.log z) / Real.log z) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpN, hp⟩ := Nat.mem_primesLE.mp hp
        calc
          _ ≤ (Real.log p / Real.log z) * (Real.exp (t * Real.log z) - 1) / p :=
            div_le_div_of_nonneg_right
              (rpow_secant_log (by exact_mod_cast hp.one_lt.le)
                ((by exact_mod_cast hpN : (p : ℝ) ≤ N).trans hNz) hz ht)
              (Nat.cast_nonneg p)
          _ ≤ (Real.log p / Real.log z) * Real.exp (t * Real.log z) / p := by
            gcongr
            exact sub_le_self _ zero_le_one
          _ = _ := by ring
      _ = (∑ p ∈ N.primesLE, Real.log p / p) *
          (Real.exp (t * Real.log z) / Real.log z) := (Finset.sum_mul ..).symm
      _ ≤ (3 * Real.log z) * (Real.exp (t * Real.log z) / Real.log z) :=
        mul_le_mul_of_nonneg_right hlogs (by positivity)
      _ = 3 * Real.exp (t * Real.log z) := by field_simp
  apply (eulerProduct_left_comparison N ht ht').trans
  apply mul_le_mul_of_nonneg_left _ (eulerProduct_pos N (by norm_num)).le
  apply Real.exp_le_exp.mpr
  simpa [mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hsum smoothEulerConstant_pos.le

/-- A finite Euler-product bound for the count of smooth integers up to `H`. -/
lemma smooth_count_rankin {N H : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 H)
    (hsmooth : ∀ n ∈ S, n ∈ (N + 1).smoothNumbers) :
    (S.card : ℝ) ≤ (H : ℝ) ^ σ * eulerProduct N σ := by
  have hsum := sum_smooth_le_eulerProduct hσ S hsmooth
  have hpoint (n : ℕ) (hn : n ∈ S) : (1 : ℝ) ≤ (H : ℝ) ^ σ * (n : ℝ) ^ (-σ) := by
    have hnI := Finset.mem_Icc.mp (hS hn)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnH : (n : ℝ) ≤ H := by exact_mod_cast hnI.2
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hn0 σ)).mpr
      (by simpa only [one_mul] using Real.rpow_le_rpow hn0.le hnH hσ.le)
  calc
    (S.card : ℝ) = ∑ _n ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ S, (H : ℝ) ^ σ * (n : ℝ) ^ (-σ) := Finset.sum_le_sum hpoint
    _ = (H : ℝ) ^ σ * ∑ n ∈ S, (n : ℝ) ^ (-σ) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg H) σ)

/-- The logarithmic smoothness cutoff in the covering construction. -/
def coverLogZ (x : ℝ) : ℝ :=
  Real.log x * Real.log (Real.log (Real.log x)) /
    (smoothScaleConstant * Real.log (Real.log x))

/-- The smoothness cutoff in the covering construction, rounded down to an integer. -/
def coverZ (x : ℝ) : ℕ := ⌊Real.exp (coverLogZ x)⌋₊

/-- The small-prime cutoff, given by the integer part of `(log x)^4`. -/
def coverW (x : ℝ) : ℕ := ⌊(Real.log x) ^ 4⌋₊

/-- The Rankin tilt used to count smooth integers. -/
def coverTilt (x : ℝ) : ℝ := smoothScaleConstant * Real.log (Real.log x) / Real.log x

/-- The smoothness scale constant exceeds ten. -/
lemma smoothScaleConstant_gt_ten : 10 < smoothScaleConstant := by
  unfold smoothScaleConstant
  linarith [smoothEulerConstant_pos]

/-- The covering tilt times the logarithmic cutoff equals the third iterated logarithm. -/
lemma coverTilt_mul_coverLogZ {x : ℝ} (hx : 1 < x) (hlog : 1 < Real.log x) :
    coverTilt x * coverLogZ x = Real.log (Real.log (Real.log x)) := by
  have hl1 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hl2 : Real.log (Real.log x) ≠ 0 := (Real.log_pos hlog).ne'
  unfold coverTilt coverLogZ
  field_simp [hl1, hl2, smoothScaleConstant_pos.ne']

/-- The size, ordering, and tilt bounds for the covering parameters hold eventually. -/
lemma eventually_cover_parameters : ∀ᶠ x : ℝ in Filter.atTop,
    2 ≤ x ∧ 2 ≤ Real.log x ∧ 1 ≤ Real.log (Real.log x) ∧ 1 ≤ Real.log (Real.log (Real.log x)) ∧
    4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 ≤ Real.log x ∧
    0 ≤ coverTilt x ∧ coverTilt x ≤ 1 / 2 ∧
    4 * Real.log (Real.log x) ≤ coverLogZ x ∧ coverLogZ x ≤ Real.log x := by
  have hlog := Real.tendsto_log_atTop
  have hloglog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x))
      Filter.atTop Filter.atTop := hlog.comp hlog
  have hlogloglog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log (Real.log x)))
      Filter.atTop Filter.atTop := hlog.comp hloglog
  have hsmall : Filter.Tendsto
      (fun x : ℝ => 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 / Real.log x)
      Filter.atTop (nhds 0) := by
    simpa [mul_div_assoc] using ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      hlog).const_mul (4 * smoothScaleConstant)
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ), hlog.eventually_ge_atTop 2,
    hloglog.eventually_ge_atTop 1, hlogloglog.eventually_ge_atTop 1,
    hsmall.eventually_le_const zero_lt_one] with x hx hl hll hlll hsmall
  have hl0 : 0 < Real.log x := by linarith
  have hll0 : 0 < Real.log (Real.log x) := by linarith
  have hquad : 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 ≤ Real.log x :=
    (div_le_one hl0).mp hsmall
  have hlinear : 4 * smoothScaleConstant * Real.log (Real.log x) ≤ Real.log x := by
    calc
      _ ≤ 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith)
          (mul_nonneg (by norm_num) smoothScaleConstant_pos.le)
      _ ≤ _ := hquad
  refine ⟨hx, hl, hll, hlll, hquad, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg smoothScaleConstant_pos.le hll0.le) hl0.le
  · unfold coverTilt
    apply (div_le_iff₀ hl0).mpr
    nlinarith
  · unfold coverLogZ
    apply (le_div_iff₀ (mul_pos smoothScaleConstant_pos hll0)).mpr
    calc
      _ = 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 := by ring
      _ ≤ Real.log x := hquad
      _ ≤ Real.log x * Real.log (Real.log (Real.log x)) :=
        le_mul_of_one_le_right hl0.le hlll
  · unfold coverLogZ
    apply (div_le_iff₀ (mul_pos smoothScaleConstant_pos hll0)).mpr
    apply mul_le_mul_of_nonneg_left _ hl0.le
    calc
      _ ≤ Real.log (Real.log x) := by
        linarith [Real.log_le_sub_one_of_pos hll0]
      _ ≤ smoothScaleConstant * Real.log (Real.log x) :=
        le_mul_of_one_le_left hll0.le (by linarith [smoothScaleConstant_gt_ten])

/-- The small-prime cutoff does not exceed the smoothness cutoff. -/
lemma coverW_le_coverZ {x : ℝ} (hx : 1 < x)
    (hz : 4 * Real.log (Real.log x) ≤ coverLogZ x) : coverW x ≤ coverZ x := by
  apply Nat.floor_mono
  calc
    (Real.log x) ^ 4 = Real.exp ((4 : ℕ) * Real.log (Real.log x)) := by
      rw [Real.exp_nat_mul, Real.exp_log (Real.log_pos hx)]
    _ ≤ Real.exp (coverLogZ x) := Real.exp_le_exp.mpr hz

/-- The smoothness cutoff is at most the integer part of `x`. -/
lemma coverZ_le_floor {x : ℝ} (hx : 0 < x) (hz : coverLogZ x ≤ Real.log x) : coverZ x ≤ ⌊x⌋₊ := by
  exact Nat.floor_mono ((Real.exp_le_exp.mpr hz).trans_eq (Real.exp_log hx))

/-- The small-prime cutoff is at least two when `log x ≥ 2`. -/
lemma coverW_ge_two {x : ℝ} (hL : 2 ≤ Real.log x) : 2 ≤ coverW x := by
  apply Nat.le_floor
  exact (by norm_num : (2 : ℝ) ≤ 2 ^ 4).trans
    (pow_le_pow_left₀ (by norm_num) hL 4)

/-- Eventually, at most `H / (log x)^3` integers up to `H` are `coverZ x`-smooth. -/
lemma eventually_smooth_count : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ H : ℕ, x ≤ H → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 H →
    (∀ n ∈ S, ∀ p : ℕ, p.Prime → p ∣ n → p ≤ coverZ x) →
    (S.card : ℝ) ≤ (H : ℝ) / Real.log x ^ 3 := by
  filter_upwards [eventually_cover_parameters,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 2]
    with x hparameters hlarge
  simp only [Function.comp_apply] at hlarge
  obtain ⟨hx, hl, hll, _, _, ht, ht', hZlow, hZhigh⟩ := hparameters
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hl1 : 1 < Real.log x := by linarith
  have hll0 : 0 < Real.log (Real.log x) := by linarith
  have hZ : 2 ≤ coverZ x :=
    (coverW_ge_two hl).trans (coverW_le_coverZ hx1 hZlow)
  have hlogZ : Real.log (coverZ x) ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < coverZ x))
      ((by exact_mod_cast coverZ_le_floor hx0 hZhigh : (coverZ x : ℝ) ≤ ⌊x⌋₊).trans
        (Nat.floor_le hx0.le))
  have hEulerOne : eulerProduct (coverZ x) 1 ≤
      Real.exp (7 * Real.log (Real.log x)) := by
    calc
      _ ≤ Real.exp 6 * (1 + Real.log (coverZ x)) := eulerProduct_one_le hZ
      _ ≤ Real.exp 6 * Real.log x ^ 2 := by
        gcongr
        nlinarith
      _ = Real.exp (6 + 2 * Real.log (Real.log x)) := by
        rw [Real.exp_add, show Real.exp (2 * Real.log (Real.log x)) =
          Real.log x ^ 2 by
            simpa [Real.exp_log hl0] using Real.exp_nat_mul (Real.log (Real.log x)) 2]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hEuler : eulerProduct (coverZ x) (1 - coverTilt x) ≤
      Real.exp ((smoothScaleConstant - 3) * Real.log (Real.log x)) := by
    have hbound := eulerProduct_left_bound hZ
      (Nat.floor_le (Real.exp_pos (coverLogZ x)).le) ht ht'
    rw [Real.log_exp, coverTilt_mul_coverLogZ hx1 hl1, Real.exp_log hll0] at hbound
    calc
      _ ≤ eulerProduct (coverZ x) 1 *
          Real.exp (3 * smoothEulerConstant * Real.log (Real.log x)) := hbound
      _ ≤ Real.exp (7 * Real.log (Real.log x)) *
          Real.exp (3 * smoothEulerConstant * Real.log (Real.log x)) := by
        gcongr
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        unfold smoothScaleConstant
        ring
  intro H hxH S hS hsmooth
  have hH0 : 0 < (H : ℝ) := hx0.trans_le hxH
  have hpower : (H : ℝ) ^ (1 - coverTilt x) ≤
      H * Real.exp (-smoothScaleConstant * Real.log (Real.log x)) := by
    rw [sub_eq_add_neg, Real.rpow_add hH0, Real.rpow_one]
    apply mul_le_mul_of_nonneg_left _ hH0.le
    calc
      _ ≤ x ^ (-coverTilt x) := Real.rpow_le_rpow_of_nonpos hx0 hxH (neg_nonpos.mpr ht)
      _ = _ := by
        rw [Real.rpow_def_of_pos hx0]
        congr 1
        unfold coverTilt
        field_simp
  calc
    (S.card : ℝ) ≤ (H : ℝ) ^ (1 - coverTilt x) *
        eulerProduct (coverZ x) (1 - coverTilt x) := by
      apply smooth_count_rankin (by linarith) S hS
      intro n hn
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp (hS hn)).1; omega
      apply Nat.mem_smoothNumbers.mpr
      refine ⟨hn0, ?_⟩
      intro p hp
      obtain ⟨hp, hpn⟩ := (Nat.mem_primeFactorsList hn0).mp hp
      exact Nat.lt_succ_of_le (hsmooth n hn p hp hpn)
    _ ≤ (H * Real.exp (-smoothScaleConstant * Real.log (Real.log x))) *
        Real.exp ((smoothScaleConstant - 3) * Real.log (Real.log x)) :=
      mul_le_mul hpower hEuler (eulerProduct_pos _ (by linarith)).le (by positivity)
    _ = (H : ℝ) / Real.log x ^ 3 := by
      rw [mul_assoc, ← Real.exp_add,
        show -smoothScaleConstant * Real.log (Real.log x) +
          (smoothScaleConstant - 3) * Real.log (Real.log x) =
          -(3 * Real.log (Real.log x)) by ring,
        Real.exp_neg, show Real.exp (3 * Real.log (Real.log x)) = Real.log x ^ 3 by
          simpa [Real.exp_log hl0] using Real.exp_nat_mul (Real.log (Real.log x)) 3,
        div_eq_mul_inv]

end
end LongGapsBetweenPrimes

open Filter Finset Real LongGapsBetweenPrimes

theorem OMA.solution : OMA.R_Erdos688_erdos_688_variants_lglglg_over_lglg_is_big_o_R1.H2 := by
  classical
  refine ⟨smoothScaleConstant, smoothScaleConstant_pos, ?_⟩
  have hx := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [hx.eventually eventually_smooth_count,
    (tendsto_log_atTop.comp hx).eventually_ge_atTop 4, eventually_ge_atTop (1 : ℕ)]
    with n hcount hlog hn
  change 4 ≤ log (n : ℝ) at hlog
  let S := (Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors,
    (p : ℝ) ≤ (n : ℝ) ^ (log (log (log n)) / (smoothScaleConstant*log (log n)))
  change (S.card : ℝ) ≤ (n : ℝ)/(16*log n)
  have hc := hcount n le_rfl S (filter_subset _ _) (by
    intro m hm p hp hd
    have hmn := mem_Icc.mp (mem_filter.mp hm).1
    have h : (p : ℝ) ≤ (n : ℝ) ^ (log (log (log n)) / (smoothScaleConstant*log (log n))) :=
      (mem_filter.mp hm).2 p (Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩)
    apply Nat.le_floor
    rw [Real.rpow_def_of_pos (by exact_mod_cast (show 0 < n by omega))] at h
    simpa [coverLogZ, mul_div_assoc] using h)
  apply hc.trans
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
  nlinarith [mul_nonneg (show 0 ≤ log (n : ℝ)-4 by linarith) (sq_nonneg (log (n : ℝ))),
    sq_nonneg (log (n : ℝ)-4)]
