import OMAReductions.R_Erdos687_erdos_687_variants_fgkmt_R1
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


/-- `smoothEulerConstant ≤ 4`. -/
lemma smoothEulerConstant_le_four : smoothEulerConstant ≤ 4 := by
  unfold smoothEulerConstant
  have hs : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (4 / 3 : ℝ) = Real.sqrt ((4 / 3) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsp : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, inv_le_comm₀ hsp (by norm_num)]
    norm_num
    linarith
  have hpos : 0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith
  rw [inv_le_comm₀ hpos (by norm_num)]
  norm_num
  linarith

lemma fifty_le_exp_four : (50 : ℝ) ≤ Real.exp 4 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith
  calc (50 : ℝ) ≤ 2.7 ^ 4 := by norm_num
    _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4

/-- The final exponent comparison. -/
lemma exponent_bound {t L L2 L3 : ℝ} (hL3 : 64 ≤ L3) (hL2 : 0 ≤ L2)
    (htL : t * L = (L3 - 4) * (4 * L2 / L3)) :
    -(t * L) + 3 * smoothEulerConstant * (L2 / Real.exp 4) ≤ -(7 / 2) * L2 := by
  have hL3pos : 0 < L3 := by linarith
  have e1 : (L3 - 4) * (4 * L2 / L3) = 4 * L2 - 16 * L2 / L3 := by
    field_simp
    ring
  have h1 : 16 * L2 / L3 ≤ L2 / 4 := by
    rw [div_le_iff₀ hL3pos]
    nlinarith
  have hCE := smoothEulerConstant_le_four
  have hCE0 := smoothEulerConstant_pos
  have he4 := fifty_le_exp_four
  have h2 : L2 / Real.exp 4 ≤ L2 / 50 :=
    div_le_div_of_nonneg_left hL2 (by norm_num) he4
  have h3 : 3 * smoothEulerConstant * (L2 / Real.exp 4) ≤ 3 * 4 * (L2 / 50) := by
    apply mul_le_mul (by linarith) h2 (div_nonneg hL2 (Real.exp_pos 4).le) (by norm_num)
  rw [htL, e1]
  nlinarith

lemma two_exp_six_le : 2 * Real.exp 6 ≤ Real.exp 7 := by
  have h : Real.exp 7 = Real.exp 1 * Real.exp 6 := by rw [← Real.exp_add]; norm_num
  rw [h]
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos 6).le

lemma final_bound {L L2 : ℝ} (hexpL2 : Real.exp L2 = L) (hL2 : 14 ≤ L2) :
    2 * Real.exp 6 * (L * L * L) * Real.exp (-(7 / 2) * L2) ≤ 1 := by
  have hL3' : L * L * L = Real.exp (3 * L2) := by
    rw [← hexpL2, ← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [hL3']
  calc 2 * Real.exp 6 * Real.exp (3 * L2) * Real.exp (-(7 / 2) * L2)
      ≤ Real.exp 7 * Real.exp (3 * L2) * Real.exp (-(7 / 2) * L2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right two_exp_six_le (Real.exp_pos _).le
    _ = Real.exp (7 + 3 * L2 + -(7 / 2) * L2) := by rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

end
end LongGapsBetweenPrimes

open Filter Finset LongGapsBetweenPrimes

set_option maxHeartbeats 1000000 in
theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_fgkmt_R1.H2 := by
  classical
  have hx : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hx
  have hl2 : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hl
  have hl3 : Tendsto (fun x : ℕ => Real.log (Real.log (Real.log (x : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hl2
  filter_upwards [hl.eventually_ge_atTop 256, hl3.eventually_ge_atTop 64,
    eventually_ge_atTop 2] with x hL hL3 hx2
  set L := Real.log (x : ℝ) with hLdef
  set L2 := Real.log L with hL2def
  set L3 := Real.log L2 with hL3def
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hLpos : 0 < L := by linarith
  have hL2pos : 0 < L2 := Real.log_pos (by linarith)
  have hL3pos : 0 < L3 := by linarith
  have hL2big : Real.exp 64 ≤ L2 := by
    have h := Real.exp_le_exp.mpr hL3
    rwa [hL3def, Real.exp_log hL2pos] at h
  have hL2_64 : 64 ≤ L2 := by linarith [Real.add_one_le_exp (64 : ℝ)]
  have hexpL2 : Real.exp L2 = L := Real.exp_log hLpos
  -- `8 log log x ≤ log x`
  have hL2L : 8 * L2 ≤ L := by
    have h1 : L2 ≤ 2 * Real.sqrt L := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hLpos)
      rw [Real.log_sqrt hLpos.le] at h
      linarith [Real.sqrt_nonneg L]
    have h2 : 16 ≤ Real.sqrt L := by
      rw [show (16 : ℝ) = Real.sqrt (16 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num; linarith)
    have h3 : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
    nlinarith
  have hL3le : L3 ≤ L2 := by linarith [Real.log_le_sub_one_of_pos hL2pos]
  -- the smoothness cutoff `z = x ^ e`
  set e := L3 / (4 * L2) with he
  have hepos : 0 < e := div_pos hL3pos (by linarith)
  have he1 : e ≤ 1 / 4 := by
    rw [he, div_le_iff₀ (by linarith)]
    linarith
  set z := (x : ℝ) ^ e with hz
  have hzpos : 0 < z := Real.rpow_pos_of_pos hxpos e
  have hlogz : Real.log z = e * L := Real.log_rpow hxpos e
  have hlogzL : Real.log z ≤ L := by
    rw [hlogz]
    nlinarith
  have hlogz2 : 2 * L3 ≤ Real.log z := by
    rw [hlogz, he, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith
  have hz2 : (2 : ℝ) ≤ z := by
    have h := Real.exp_le_exp.mpr (show (128 : ℝ) ≤ Real.log z by linarith)
    rw [Real.exp_log hzpos] at h
    linarith [Real.add_one_le_exp (128 : ℝ)]
  set N := ⌊z⌋₊ with hNdef
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hz2)
  have hNz : (N : ℝ) ≤ z := Nat.floor_le hzpos.le
  have hNpos : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  -- the Rankin tilt `t = (log₃ x - 4) / log z`
  have hlogzpos : 0 < Real.log z := by linarith
  set t := (L3 - 4) / Real.log z with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hlogzpos.le
  have ht1 : t ≤ 1 / 2 := by
    rw [ht, div_le_iff₀ hlogzpos]
    linarith
  have htz : t * Real.log z = L3 - 4 := by
    rw [ht]; field_simp
  have htL : t * L = (L3 - 4) * (4 * L2 / L3) := by
    rw [ht, hlogz, he]
    field_simp
  -- the interval `[1, H]`, `H = ⌊x log x⌋`
  set H := ⌊(x : ℝ) * L⌋₊ with hHdef
  have hxL : (x : ℝ) ≤ x * L := by nlinarith
  have hHx : x ≤ H := Nat.le_floor hxL
  have hHle : (H : ℝ) ≤ x * L := Nat.floor_le (by positivity)
  have hHpos : (0 : ℝ) < H := by
    have : (2 : ℝ) ≤ H := by exact_mod_cast (le_trans hx2 hHx)
    linarith
  set S := (Icc 1 H).filter fun n : ℕ => ∀ p : ℕ, p ≤ n → p.Prime → p ∣ n → (p : ℝ) ≤ z with hS
  show (S.card : ℝ) ≤ x / L
  have hsm : ∀ n ∈ S, n ∈ (N + 1).smoothNumbers := by
    intro n hn
    rw [hS, mem_filter, mem_Icc] at hn
    rw [Nat.mem_smoothNumbers]
    refine ⟨by omega, fun p hp => ?_⟩
    have hpp := Nat.prime_of_mem_primeFactorsList hp
    have hpd := Nat.dvd_of_mem_primeFactorsList hp
    have hpn := Nat.le_of_dvd (by omega) hpd
    have h := hn.2 p hpn hpp hpd
    have : p ≤ N := Nat.le_floor h
    omega
  have hcount := smooth_count_rankin (σ := 1 - t) (by linarith) S (filter_subset _ _) hsm
  have hE := eulerProduct_left_bound hN2 hNz ht0 ht1
  have hE1 := eulerProduct_one_le hN2
  have hEpos := eulerProduct_pos N (show (0 : ℝ) < 1 by norm_num)
  -- `H ^ (1 - t) ≤ x log x · exp (-t log x)`
  have hHσ : (H : ℝ) ^ (1 - t) ≤ (x * L) * Real.exp (-(t * L)) := by
    rw [Real.rpow_def_of_pos hHpos]
    have hlogH : L ≤ Real.log H := Real.log_le_log hxpos (by exact_mod_cast hHx)
    have hlogH2 : Real.log H ≤ Real.log (x * L) := Real.log_le_log hHpos hHle
    have h : Real.log H * (1 - t) ≤ Real.log (x * L) - t * L := by nlinarith
    calc Real.exp (Real.log H * (1 - t)) ≤ Real.exp (Real.log (x * L) - t * L) :=
          Real.exp_le_exp.mpr h
      _ = (x * L) * Real.exp (-(t * L)) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by positivity)]
  have hlogN : 1 + Real.log N ≤ 2 * L := by
    have := Real.log_le_log hNpos hNz
    linarith
  have hexpz : Real.exp (t * Real.log z) = L2 / Real.exp 4 := by
    rw [htz, Real.exp_sub, Real.exp_log hL2pos]
  have hX := exponent_bound hL3 hL2pos.le htL
  -- assemble
  have hstep1 : (S.card : ℝ) ≤ ((x * L) * Real.exp (-(t * L))) *
      (Real.exp 6 * (2 * L) * Real.exp (3 * smoothEulerConstant * (L2 / Real.exp 4))) := by
    calc (S.card : ℝ) ≤ (H : ℝ) ^ (1 - t) * eulerProduct N (1 - t) := hcount
      _ ≤ ((x * L) * Real.exp (-(t * L))) *
          (eulerProduct N 1 * Real.exp (3 * smoothEulerConstant * Real.exp (t * Real.log z))) :=
          mul_le_mul hHσ hE (eulerProduct_pos N (by linarith)).le (by positivity)
      _ ≤ ((x * L) * Real.exp (-(t * L))) *
          (Real.exp 6 * (2 * L) * Real.exp (3 * smoothEulerConstant * (L2 / Real.exp 4))) := by
          rw [hexpz]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          calc eulerProduct N 1 ≤ Real.exp 6 * (1 + Real.log N) := hE1
            _ ≤ Real.exp 6 * (2 * L) := mul_le_mul_of_nonneg_left hlogN (Real.exp_pos 6).le
  have hexpX : Real.exp (-(t * L)) * Real.exp (3 * smoothEulerConstant * (L2 / Real.exp 4)) ≤
      Real.exp (-(7 / 2) * L2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hX
  have hfin := final_bound hexpL2 (by linarith)
  rw [le_div_iff₀ hLpos]
  have hprod : ((x * L) * Real.exp (-(t * L))) *
      (Real.exp 6 * (2 * L) * Real.exp (3 * smoothEulerConstant * (L2 / Real.exp 4))) * L =
      x * (2 * Real.exp 6 * (L * L * L) *
        (Real.exp (-(t * L)) * Real.exp (3 * smoothEulerConstant * (L2 / Real.exp 4)))) := by
    ring
  have hmono : 2 * Real.exp 6 * (L * L * L) *
      (Real.exp (-(t * L)) * Real.exp (3 * smoothEulerConstant * (L2 / Real.exp 4))) ≤ 1 := by
    calc _ ≤ 2 * Real.exp 6 * (L * L * L) * Real.exp (-(7 / 2) * L2) :=
          mul_le_mul_of_nonneg_left hexpX (by positivity)
      _ ≤ 1 := hfin
  calc (S.card : ℝ) * L ≤ ((x * L) * Real.exp (-(t * L))) *
        (Real.exp 6 * (2 * L) * Real.exp (3 * smoothEulerConstant * (L2 / Real.exp 4))) * L :=
        mul_le_mul_of_nonneg_right hstep1 hLpos.le
    _ = _ := hprod
    _ ≤ x * 1 := mul_le_mul_of_nonneg_left hmono hxpos.le
    _ = x := mul_one _
