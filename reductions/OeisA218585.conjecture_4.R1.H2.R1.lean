import OMAReductions.R_OeisA218585_conjecture_4_R1
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Weighted angular equidistribution of split Eisenstein primes

Following Hecke's angular character method, test the fundamental sector against
the functions cos(6kθ). Dyadic prime counts control the change from counting
measure to norm weights. Chebyshev polynomials then give all continuous tests.

The arithmetic reference is E. Hecke, *Eine neue Art von Zetafunktionen und ihre
Beziehungen zur Verteilung der Primzahlen*, II, Math. Z. 6 (1920), 11–51.
-/

namespace OMA.R_OeisA218585_conjecture_4_R1_H2_R1

open OeisA218585 Real Filter MeasureTheory
open scoped Topology BigOperators

/-- Cancellation of the nonconstant angular Hecke characters, paired with their conjugates
and averaged over the split rational primes. -/
def H1 : Prop :=
  let z (p : ℕ) : ℂ := ⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩
  let primes (N : ℕ) := (Finset.range N).filter fun p => p.Prime ∧ p % 3 = 1
  ∀ k : ℕ, k ≠ 0 → Tendsto (fun N =>
    (∑ p ∈ primes N, cos ((k : ℝ) * (6 * (z p).arg))) / (primes N).card) atTop (𝓝 0)

/-- A dyadic counting estimate for primes congruent to one modulo three.
The prime number theorem in this progression gives limiting proportion one half. -/
def H2 : Prop :=
  let primes (N : ℕ) := (Finset.range N).filter fun p => p.Prime ∧ p % 3 = 1
  ∀ᶠ N in atTop, (primes N).card ≤ 3 * ((primes N).filter fun p => N ≤ 2 * p).card

/-- Both coordinate searches take their values from representations of the same norm. -/
lemma ordinate_le_abscissa (p : ℕ) : yp p ≤ xp p := by
  let hasOrdinate (u : ℕ) := (List.range u).any fun v =>
    0 < v && u ^ 2 + u * v + v ^ 2 == p
  let hasAbscissa (v : ℕ) := 0 < v && (List.Ico (v + 1) p).any fun u =>
    u ^ 2 + u * v + v ^ 2 == p
  change ((List.range p).find? hasAbscissa).getD 0 ≤ ((List.range p).find? hasOrdinate).getD 0
  cases hy : (List.range p).find? hasAbscissa with
  | none => simp
  | some y =>
    obtain ⟨hypos, u, ⟨hyu, hup⟩, hu⟩ :
        0 < y ∧ ∃ u, (y + 1 ≤ u ∧ u < p) ∧ u ^ 2 + u * y + y ^ 2 = p := by
      simpa [hasAbscissa] using List.find?_some hy
    have hX : hasOrdinate u := by simpa [hasOrdinate] using
      (show ∃ v < u, 0 < v ∧ u ^ 2 + u * v + v ^ 2 = p from ⟨y, by omega, hypos, hu⟩)
    cases hx : (List.range p).find? hasOrdinate with
    | none => exact False.elim ((List.find?_eq_none.mp hx u (List.mem_range.mpr hup)) hX)
    | some x =>
      obtain ⟨v, hvx, _, hv⟩ : ∃ v < x, 0 < v ∧ x ^ 2 + x * v + v ^ 2 = p := by
        simpa [hasOrdinate] using List.find?_some hx
      change y ≤ x
      by_contra! h
      have hxu : x < u := by omega
      have hvy : v < y := by omega
      nlinarith [Nat.pow_lt_pow_left hxu (by decide : 2 ≠ 0),
        Nat.mul_le_mul hxu.le hvy.le, Nat.pow_le_pow_left hvy.le 2]

lemma sector_angle (p : ℕ) :
    (⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩ : ℂ).arg ∈
      Set.Icc 0 (π / 6) := by
  let x : ℝ := xp p
  let y : ℝ := yp p
  let z : ℂ := ⟨x + y / 2, √3 * y / 2⟩
  change z.arg ∈ _
  have hy : 0 ≤ y := Nat.cast_nonneg _
  have hxy : y ≤ x := by dsimp [x, y]; exact_mod_cast ordinate_le_abscissa p
  have hx : 0 ≤ x := hy.trans hxy
  have hs : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨Complex.arg_nonneg_iff.mpr (show 0 ≤ √3 * y / 2 by positivity), ?_⟩
  by_cases hz : z = 0
  · rw [hz, Complex.arg_zero]; positivity
  have hn := norm_pos_iff.mpr hz
  have hns : ‖z‖ ^ 2 = x ^ 2 + x * y + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [z]
    linear_combination (y ^ 2 / 4) * hs
  have bound : √3 * y ≤ ‖z‖ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ x + 2 * y by positivity),
      show (√3 * y) ^ 2 = 3 * y ^ 2 by rw [mul_pow, hs]]
  rw [Complex.arg_of_re_nonneg (show 0 ≤ x + y / 2 by positivity),
      ← Real.arcsin_sin (x := π / 6) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
      Real.sin_pi_div_six]
  apply Real.monotone_arcsin
  apply (div_le_iff₀ hn).mpr
  change √3 * y / 2 ≤ _
  linarith

lemma abel_identity (a : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ Finset.range N, (p : ℝ) * a p =
      N * (∑ p ∈ Finset.range N, a p) -
        ∑ j ∈ Finset.range N, ∑ p ∈ Finset.range (j + 1), a p := by
  induction N with
  | zero => simp
  | succ N ih => simp only [Finset.sum_range_succ, Nat.cast_succ, ih]; ring

/-- Transfer cancellation from counting measure to prime-norm weights by partial summation. -/
lemma transfer_weights (P : ℕ → Prop) [DecidablePred P] (a : ℕ → ℝ) (C : ℝ)
    (bound : ∀ᶠ (N : ℕ) in atTop,
      (N : ℝ) * ((Finset.range N).filter P).card ≤
        C * ∑ p ∈ (Finset.range N).filter P, (p : ℝ))
    (positive : ∀ᶠ N in atTop, 0 < ∑ p ∈ (Finset.range N).filter P, (p : ℝ))
    (cancel : Tendsto (fun N => (∑ p ∈ (Finset.range N).filter P, a p) /
        ((Finset.range N).filter P).card) atTop (𝓝 0)) :
    Tendsto (fun N => (∑ p ∈ (Finset.range N).filter P, (p : ℝ) * a p) /
        ∑ p ∈ (Finset.range N).filter P, (p : ℝ)) atTop (𝓝 0) := by
  let primes (n : ℕ) := (Finset.range n).filter P
  let A (n : ℕ) := ∑ p ∈ primes n, a p
  let count (n : ℕ) : ℝ := (primes n).card
  let mass (n : ℕ) := ∑ p ∈ primes n, (p : ℝ)
  let W (n : ℕ) := ∑ p ∈ primes n, (p : ℝ) * a p
  let r (n : ℕ) := |A n / count n|
  have hr : Tendsto r atTop (𝓝 0) := by simpa [r, A, count, primes] using cancel.abs
  have hshift : Tendsto (fun j => r (j + 1)) atTop (𝓝 0) :=
    hr.comp (tendsto_add_atTop_nat 1)
  let b (n : ℕ) := r n + (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, r (j + 1)
  have hb : Tendsto b atTop (𝓝 0) := by simpa [b] using hr.add hshift.cesaro
  have split (n : ℕ) : |A n| = r n * count n := by
    by_cases h : primes n = ∅
    · simp [r, A, count, h]
    have hn : count n ≠ 0 := by simp [count, h]
    rw [show r n = |A n| / count n by simp [r, abs_div, count]]
    exact (div_mul_cancel₀ _ hn).symm
  have mono_count : Monotone count := by
    intro m n h
    dsimp [count, primes]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter P (Finset.range_mono h))
  have abel (n : ℕ) : W n = n * A n - ∑ j ∈ Finset.range n, A (j + 1) := by
    simpa [W, A, primes, Finset.sum_filter, mul_ite] using
      abel_identity (fun p => if P p then a p else 0) n
  change Tendsto (fun n => W n / mass n) atTop (𝓝 0)
  apply squeeze_zero_norm' (a := fun n => b n * C) _ (by simpa using hb.mul_const C)
  filter_upwards [bound, positive, eventually_ge_atTop 1] with n hn hm hpos
  change (n : ℝ) * count n ≤ C * mass n at hn
  change 0 < mass n at hm
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hsum : |∑ j ∈ Finset.range n, A (j + 1)| ≤
      (∑ j ∈ Finset.range n, r (j + 1)) * count n := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro j hj
    rw [split]
    exact mul_le_mul_of_nonneg_left (mono_count (Finset.mem_range.mp hj)) (abs_nonneg _)
  have hw : |W n| ≤ b n * ((n : ℝ) * count n) := calc
    |W n| ≤ |(n : ℝ) * A n| + |∑ j ∈ Finset.range n, A (j + 1)| := by
      rw [abel]; exact abs_sub _ _
    _ ≤ (n : ℝ) * (r n * count n) + (∑ j ∈ Finset.range n, r (j + 1)) * count n := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n), split]; gcongr
    _ = b n * ((n : ℝ) * count n) := by dsimp [b]; field_simp
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hm, div_le_iff₀ hm]
  have hbpos : 0 ≤ b n := by dsimp [b, r]; positivity
  exact hw.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hn hbpos)

open Polynomial Polynomial.Chebyshev

/-- Finite cosine sums are uniformly dense on the fundamental sector. -/
lemma cosine_approximation (f : ℝ → ℝ) (hf : Continuous f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (K : ℕ) (c : ℕ → ℝ), ∀ t ∈ Set.Icc 0 (π / 6),
      |(∑ k ∈ Finset.range K, c k * cos (k * (6 * t))) - f t| < δ := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1
    (fun u => f (arccos u / 6)) (by fun_prop) δ hδ
  let K := p.natDegree + 1
  have hmem : p ∈ degreeLT ℝ K := by
    rw [mem_degreeLT]
    exact p.degree_le_natDegree.trans_lt (by dsimp [K]; exact_mod_cast Nat.lt_succ_self _)
  rw [← Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp),
    show Set.Iio K = (Finset.range K : Set ℕ) by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨K, c, fun t ht => ?_⟩
  have h := hp (cos (6 * t)) (cos_mem_Icc _)
  rw [arccos_cos (by linarith [ht.1]) (by linarith [ht.2]),
    show 6 * t / 6 = t by ring, ← hc] at h
  simpa [eval_finsetSum, eval_smul, chebyshevTsequence, smul_eq_mul] using h

lemma integral_cosine_mode (k : ℕ) (hk : k ≠ 0) :
    (∫ t in 0..π / 6, cos (k * (6 * t))) = 0 := by
  have h : (k : ℝ) * 6 ≠ 0 := by positivity
  simp_rw [← mul_assoc]
  rw [intervalIntegral.integral_comp_mul_left _ h, integral_cos, mul_zero,
    show (k : ℝ) * 6 * (π / 6) = k * π by ring, Real.sin_nat_mul_pi, Real.sin_zero]
  simp

/-- A weighted Weyl criterion on the sector, using the real parts of the angular characters. -/
lemma sector_criterion (P : ℕ → Finset ℕ) (θ : ℕ → ℝ) (w : ℕ → ℕ → ℝ)
    (hθ : ∀ p, θ p ∈ Set.Icc 0 (π / 6)) (hw : ∀ n p, 0 ≤ w n p)
    (hunit : ∀ᶠ n in atTop, ∑ p ∈ P n, w n p = 1)
    (modes : ∀ k : ℕ, k ≠ 0 → Tendsto
      (fun n => ∑ p ∈ P n, w n p * cos (k * (6 * θ p))) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : Continuous f) :
    Tendsto (fun n => ∑ p ∈ P n, w n p * f (θ p)) atTop
      (𝓝 ((6 / π) * ∫ t in 0..π / 6, f t)) := by
  let M (n : ℕ) (g : ℝ → ℝ) := ∑ p ∈ P n, w n p * g (θ p)
  let J (g : ℝ → ℝ) := (6 / π) * ∫ t in 0..π / 6, g t
  let mode (k : ℕ) (t : ℝ) := cos ((k : ℝ) * (6 * t))
  have hmode (k : ℕ) : Tendsto (fun n => M n (mode k)) atTop (𝓝 (J (mode k))) := by
    by_cases hk : k = 0
    · subst k
      have one : J (mode 0) = 1 := by simp [J, mode]
      rw [one]
      apply tendsto_const_nhds.congr'
      filter_upwards [hunit] with n hn
      simpa [M, mode] using hn.symm
    · simpa [J, mode, integral_cosine_mode k hk] using modes k hk
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, c, happ⟩ := cosine_approximation f hf δ hδ
  let g (t : ℝ) := ∑ k ∈ Finset.range K, c k * mode k t
  have hg : Continuous g := by dsimp [g, mode]; fun_prop
  have rearrange (n : ℕ) : M n g = ∑ k ∈ Finset.range K, c k * M n (mode k) := by
    dsimp [M, g]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have integrate : J g = ∑ k ∈ Finset.range K, c k * J (mode k) := by
    dsimp [J, g]
    rw [intervalIntegral.integral_finsetSum (fun k _ =>
      (show Continuous (fun t => c k * mode k t) by dsimp [mode]; fun_prop).intervalIntegrable _ _)]
    simp_rw [intervalIntegral.integral_const_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hlim : Tendsto (fun n => M n g) atTop (𝓝 (J g)) := by
    simp_rw [rearrange, integrate]
    exact tendsto_finsetSum _ fun k _ => (hmode k).const_mul _
  have hi : |J g - J f| ≤ δ := by
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π / 6)
      (C := δ) (f := fun t => g t - f t) (by
        intro t ht
        rw [Set.uIoc_of_le (by positivity : 0 ≤ π / 6)] at ht
        exact (happ t ⟨ht.1.le, ht.2⟩).le)
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) (hf.intervalIntegrable _ _)] at hI
    dsimp [J]
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 6 / π)]
    apply (mul_le_mul_of_nonneg_left hI (by positivity : 0 ≤ 6 / π)).trans
    rw [sub_zero, abs_of_pos (by positivity : 0 < π / 6)]
    apply le_of_eq
    field_simp
  filter_upwards [(Metric.tendsto_nhds.mp hlim) δ hδ, hunit] with n hn hu
  have he : |M n g - M n f| ≤ δ := calc
    _ = |∑ p ∈ P n, w n p * (g (θ p) - f (θ p))| := by simp [M, mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ p ∈ P n, |w n p * (g (θ p) - f (θ p))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P n, w n p * δ := Finset.sum_le_sum fun p _ => by
      rw [abs_mul, abs_of_nonneg (hw n p)]
      exact mul_le_mul_of_nonneg_left (happ _ (hθ p)).le (hw n p)
    _ = δ := by rw [← Finset.sum_mul, hu, one_mul]
  change dist (M n f) (J f) < ε
  rw [Real.dist_eq] at hn ⊢
  have h₁ := abs_le.mp he
  have h₂ := abs_le.mp hi
  have h₃ := abs_lt.mp hn
  dsimp [δ] at *
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem main : H1 → H2 → OMA.R_OeisA218585_conjecture_4_R1.H2 := by
  intro hcancel hdyadic f hf
  let P (p : ℕ) := p.Prime ∧ p % 3 = 1
  let primes (N : ℕ) := (Finset.range N).filter P
  let θ (p : ℕ) := (⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩ : ℂ).arg
  let mass (N : ℕ) := ∑ p ∈ primes N, (p : ℝ)
  let w (N p : ℕ) := (p : ℝ) / mass N
  have hm : ∀ᶠ N in atTop, 0 < mass N := by
    filter_upwards [eventually_ge_atTop 8] with N hN
    have h7 : 7 ∈ primes N := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), by decide⟩
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (7 : ℕ)) <|
      Finset.single_le_sum (f := fun p : ℕ => (p : ℝ)) (fun p _ => Nat.cast_nonneg p) h7
  have bound : ∀ᶠ (N : ℕ) in atTop, (N : ℝ) * (primes N).card ≤ 6 * mass N := by
    filter_upwards [hdyadic] with N hN
    let upper := (primes N).filter fun p => N ≤ 2 * p
    have hc : ((primes N).card : ℝ) ≤ 3 * (upper.card : ℝ) := by exact_mod_cast hN
    have hu : (N : ℝ) * upper.card ≤ 2 * mass N := calc
      (N : ℝ) * upper.card = ∑ _p ∈ upper, (N : ℝ) := by simp [mul_comm]
      _ ≤ ∑ p ∈ upper, 2 * (p : ℝ) := Finset.sum_le_sum fun p hp => by
        exact_mod_cast (Finset.mem_filter.mp hp).2
      _ ≤ ∑ p ∈ primes N, 2 * (p : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun p _ _ => by positivity)
      _ = 2 * mass N := (Finset.mul_sum ..).symm
    linarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg N)]
  have normalize (g : ℕ → ℝ) (N : ℕ) :
      (∑ p ∈ primes N, w N p * g p) = (∑ p ∈ primes N, (p : ℝ) * g p) / mass N := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp [w]
    ring
  have modes (k : ℕ) (hk : k ≠ 0) :
      Tendsto (fun N => ∑ p ∈ primes N, w N p * cos ((k : ℝ) * (6 * θ p))) atTop (𝓝 0) := by
    simp_rw [normalize (fun p => cos ((k : ℝ) * (6 * θ p)))]
    exact transfer_weights P _ 6 bound hm (hcancel k hk)
  have unit : ∀ᶠ N in atTop, ∑ p ∈ primes N, w N p = 1 := by
    filter_upwards [hm] with N hN
    change (∑ p ∈ primes N, (p : ℝ) / mass N) = 1
    rw [← Finset.sum_div]
    exact div_self hN.ne'
  have nn (N p : ℕ) : 0 ≤ w N p := by dsimp [w, mass]; positivity
  have result := sector_criterion primes θ w sector_angle nn unit modes f hf
  simp_rw [normalize (fun p => f (θ p))] at result
  exact result

end OMA.R_OeisA218585_conjecture_4_R1_H2_R1
