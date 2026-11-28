import OMAStatements.S_oeis_a246860
import Mathlib

/-!
# Proof of OEIS A246860 (Johnston's Conjecture for Even Trace Moments on O(4))

We prove that for normalized Haar probability measure `mu` on `O(4)` and all `n >= 1`:
  `E[trace(O)^(2n)] = C_n * (C_n + 1) / 2`
where `C_n = catalan n`.

Proof overview:
1. Elementary 1D Gaussian and Gamma moments on `R`:
   `int_{R} x^(2n) exp(-x^2) dx = (2n)! / (4^n n!) * sqrt(pi)` and
   `int_{(0, infty)} u^k exp(-u) du = k!`.
2. Radial-angular scaling via Tonelli (`lintegral_lintegral_swap`) on `R^4` with the
   4D Gaussian probability measure `gamma4`:
   `int_{R^4} (2 x_0 / ||x||)^(2n) d gamma4 = catalan n`.
3. Pushforward of `gamma4` to unit quaternions `UnitQuat = {q : H[R] // normSq q = 1}`
   gives a left-invariant Borel probability measure `muS3` with
   `int (2 q.re)^(2n) d muS3 = catalan n`.
4. The surjective continuous double-cover map `Phi : UnitQuat x UnitQuat x Bool -> O(4)`
   sending `(q1, q2, false) |-> (x |-> q1 * x * star q2)` and
   `(q1, q2, true) |-> (x |-> q1 * star x * star q2)` has traces `4 q1.re q2.re` and
   `-2 (q1 * q2).re`. Surjectivity follows from three quaternion Householder reflections
   `Phi (v, v, true)`.
5. The pushforward of `muS3 x muS3 x uniformBool` under `Phi` is a left-invariant Borel
   probability measure on compact second-countable `O(4)`, hence coincides with `mu` by
   `isMulLeftInvariant_eq_smul`. Evaluating the integral over `UnitQuat x UnitQuat x Bool`
   yields `(C_n^2 + C_n) / 2`.
-/

namespace A246860Proof

open MeasureTheory Filter Topology Real Set
open scoped BigOperators ENNReal Matrix Quaternion

/-! ### Section 1: 1D Gamma and Gaussian moments -/

lemma integral_Ioi_exp_neg_mul_pow (k : ℕ) :
    ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ k = (k.factorial : ℝ) := by
  have h1 := Real.Gamma_eq_integral (s := (k : ℝ) + 1) (by positivity)
  have h2 := Real.Gamma_nat_eq_factorial k
  rw [h2] at h1
  rw [h1]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [add_sub_cancel_right, Real.rpow_natCast]

lemma lintegral_Ioi_exp_neg_mul_pow (k : ℕ) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-u) * u ^ k) =
      ENNReal.ofReal (k.factorial : ℝ) := by
  have hnonneg : 0 ≤ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
      fun u : ℝ => Real.exp (-u) * u ^ k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (le_of_lt hu) _)
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ k) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (k : ℝ)) (p := 1) (b := 1)
      (by linarith [Nat.cast_nonneg (α := ℝ) k]) zero_lt_one zero_lt_one
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    dsimp only
    rw [Real.rpow_natCast, Real.rpow_one, neg_mul, one_mul, mul_comm]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg, integral_Ioi_exp_neg_mul_pow]

lemma lintegral_Ioi_exp_neg_from (a : ℝ) (ha : 0 ≤ a) :
    ∫⁻ u in Ioi a, ENNReal.ofReal (Real.exp (-u)) = ENNReal.ofReal (Real.exp (-a)) := by
  have hnonneg : 0 ≤ᶠ[ae (volume.restrict (Ioi a))] fun u : ℝ => Real.exp (-u) :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi a) := by
    have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (0 : ℝ)) (p := 1) (b := 1)
      (by norm_num) zero_lt_one zero_lt_one
    have h0' : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 0) := by
      refine h0.congr_fun (fun u _ => ?_) measurableSet_Ioi
      simp
    exact h0'.mono_set (Ioi_subset_Ioi ha)
  have hval : ∫ u in Ioi a, Real.exp (-u) = Real.exp (-a) := by
    have hderiv : ∀ x ∈ Ici a, HasDerivAt (fun t : ℝ => -Real.exp (-t)) (Real.exp (-x)) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => -t) (-1) x := (hasDerivAt_id x).neg
      have h2 : HasDerivAt (fun t : ℝ => -Real.exp (-t)) (-(Real.exp (-x) * -1)) x := h1.exp.neg
      convert h2 using 1; ring
    have htend : Tendsto (fun t : ℝ => -Real.exp (-t)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero).neg
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
    simpa using hftc
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg, hval]

lemma integrable_pow_mul_exp_neg_sq (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) zero_lt_one (s := (k : ℝ))
    (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have h' : Integrable (fun x : ℝ => |x| ^ k * Real.exp (-x ^ 2)) := by
    rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union,
      integrableOn_Ici_iff_integrableOn_Ioi]
    have hpos : IntegrableOn (fun x : ℝ => |x| ^ k * Real.exp (-x ^ 2)) (Ioi 0) := by
      refine h.integrableOn.congr_fun (fun x hx => ?_) measurableSet_Ioi
      have hx0 : 0 ≤ x := le_of_lt hx
      simp [abs_of_nonneg hx0, Real.rpow_natCast]
    refine ⟨?_, hpos⟩
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simp only [Function.comp_def, abs_neg, neg_sq, neg_preimage, neg_Iio, neg_zero]
    exact hpos
  refine h'.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (Real.exp_pos _).le]

lemma integral_even_pow_gaussian (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2) =
      ((2 * n).factorial : ℝ) / ((4 : ℝ) ^ n * (n.factorial : ℝ)) * Real.sqrt Real.pi := by
  induction n with
  | zero =>
    have hg := integral_gaussian 1
    simp only [mul_zero, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, div_one]
    simpa using hg
  | succ n ih =>
    have hderiv : ∀ x : ℝ, HasDerivAt (fun t : ℝ => t ^ (2 * n + 1) * Real.exp (-t ^ 2))
        (((2 * n + 1 : ℕ) : ℝ) * x ^ (2 * n) * Real.exp (-x ^ 2) -
          2 * (x ^ (2 * n + 2) * Real.exp (-x ^ 2))) x := by
      intro x
      have h1 : HasDerivAt (fun t : ℝ => t ^ (2 * n + 1)) (((2 * n + 1 : ℕ) : ℝ) * x ^ (2 * n)) x := by
        simpa using hasDerivAt_pow (2 * n + 1) x
      have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t ^ 2)) (Real.exp (-x ^ 2) * (-2 * x)) x := by
        have hsq : HasDerivAt (fun t : ℝ => -(t ^ 2)) (-(2 * x ^ (2 - 1))) x :=
          (hasDerivAt_pow 2 x).neg
        have hsq' : HasDerivAt (fun t : ℝ => -t ^ 2) (-2 * x) x := by
          convert hsq using 1; ring
        exact hsq'.exp
      have h3 := h1.mul h2
      have hder : ((2 * n + 1 : ℕ) : ℝ) * x ^ (2 * n) * Real.exp (-x ^ 2) +
          x ^ (2 * n + 1) * (Real.exp (-x ^ 2) * (-2 * x)) =
          ((2 * n + 1 : ℕ) : ℝ) * x ^ (2 * n) * Real.exp (-x ^ 2) -
            2 * (x ^ (2 * n + 2) * Real.exp (-x ^ 2)) := by
        rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, pow_succ]
        ring
      exact hder ▸ h3
    have hint1 : Integrable (fun x : ℝ => ((2 * n + 1 : ℕ) : ℝ) * x ^ (2 * n) * Real.exp (-x ^ 2)) := by
      simpa [mul_assoc] using (integrable_pow_mul_exp_neg_sq (2 * n)).const_mul ((2 * n + 1 : ℕ) : ℝ)
    have hint2 : Integrable (fun x : ℝ => 2 * (x ^ (2 * n + 2) * Real.exp (-x ^ 2))) :=
      (integrable_pow_mul_exp_neg_sq (2 * n + 2)).const_mul 2
    have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv (hint1.sub hint2)
      (integrable_pow_mul_exp_neg_sq (2 * n + 1))
    rw [integral_sub hint1 hint2, integral_const_mul] at hzero
    have hstep : ∫ x : ℝ, x ^ (2 * (n + 1)) * Real.exp (-x ^ 2) =
        (((2 * n + 1 : ℕ) : ℝ) / 2) * ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2) := by
      have h1 : ∫ x : ℝ, ((2 * n + 1 : ℕ) : ℝ) * x ^ (2 * n) * Real.exp (-x ^ 2) =
          ((2 * n + 1 : ℕ) : ℝ) * ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2) := by
        simpa [mul_assoc] using integral_const_mul ((2 * n + 1 : ℕ) : ℝ)
          (fun x : ℝ => x ^ (2 * n) * Real.exp (-x ^ 2))
      rw [h1] at hzero
      have hmul : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [hmul]; linarith
    rw [hstep, ih]
    have hfac1 : ((2 * (n + 1)).factorial : ℝ) =
        ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * ((2 * n).factorial : ℝ) := by
      have : (2 * (n + 1)).factorial = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ, mul_assoc]
      exact_mod_cast this
    have hfac2 : ((n + 1).factorial : ℝ) = ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hne1 : ((n.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    have hne2 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hne3 : (4 : ℝ) ^ n ≠ 0 := by positivity
    rw [hfac1, hfac2, pow_succ]
    push_cast
    field_simp
    ring

/-! ### Section 2: 4D Gaussian measure and radial-angular moment identity -/

def sqNorm (x : Fin 4 → ℝ) : ℝ := ∑ i : Fin 4, (x i) ^ 2

lemma sqNorm_nonneg (x : Fin 4 → ℝ) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sqNorm_eq_zero_iff (x : Fin 4 → ℝ) : sqNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have hle : (x i) ^ 2 ≤ sqNorm x :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    have hsq : (x i) ^ 2 = 0 := le_antisymm (h ▸ hle) (sq_nonneg _)
    exact sq_eq_zero_iff.1 hsq
  · rintro rfl; simp [sqNorm]

lemma sqNorm_smul (r : ℝ) (x : Fin 4 → ℝ) : sqNorm (r • x) = r ^ 2 * sqNorm x := by
  simp only [sqNorm, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]

lemma continuous_sqNorm : Continuous sqNorm := by
  unfold sqNorm; fun_prop

lemma measurable_sqNorm : Measurable sqNorm := continuous_sqNorm.measurable

lemma exp_neg_sqNorm_eq_prod (x : Fin 4 → ℝ) :
    Real.exp (-sqNorm x) = ∏ i : Fin 4, Real.exp (-(x i) ^ 2) := by
  simp only [sqNorm, ← Real.exp_sum, Finset.sum_neg_distrib]

lemma integral_exp_neg_sqNorm :
    ∫ x : Fin 4 → ℝ, Real.exp (-sqNorm x) = Real.pi ^ 2 := by
  simp_rw [exp_neg_sqNorm_eq_prod]
  rw [integral_fintype_prod_volume_eq_pow (fun t : ℝ => Real.exp (-t ^ 2))]
  have hg : ∫ t : ℝ, Real.exp (-t ^ 2) = Real.sqrt Real.pi := by simpa using integral_gaussian 1
  rw [hg, Fintype.card_fin]
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  calc Real.sqrt Real.pi ^ 4 = (Real.sqrt Real.pi ^ 2) ^ 2 := by ring
    _ = Real.pi ^ 2 := by rw [hsq]

lemma integrable_exp_neg_sqNorm : Integrable (fun x : Fin 4 → ℝ => Real.exp (-sqNorm x)) := by
  have h1 : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) zero_lt_one
  have hprod : Integrable (fun x : Fin 4 → ℝ => ∏ i : Fin 4, Real.exp (-(x i) ^ 2)) :=
    Integrable.fintype_prod (f := fun (_ : Fin 4) (t : ℝ) => Real.exp (-t ^ 2)) (fun _ => h1)
  simpa [exp_neg_sqNorm_eq_prod] using hprod

lemma lintegral_exp_neg_sqNorm :
    ∫⁻ x : Fin 4 → ℝ, ENNReal.ofReal (Real.exp (-sqNorm x)) = ENNReal.ofReal (Real.pi ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_exp_neg_sqNorm
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le), integral_exp_neg_sqNorm]

lemma integral_coord0_pow_exp_neg_sqNorm (n : ℕ) :
    ∫ x : Fin 4 → ℝ, (2 * x 0) ^ (2 * n) * Real.exp (-sqNorm x) =
      (((2 * n).factorial : ℝ) / (n.factorial : ℝ)) * Real.pi ^ 2 := by
  let f : Fin 4 → ℝ → ℝ := fun i t =>
    if i = 0 then (2 * t) ^ (2 * n) * Real.exp (-t ^ 2) else Real.exp (-t ^ 2)
  have hprod : ∀ x : Fin 4 → ℝ,
      (2 * x 0) ^ (2 * n) * Real.exp (-sqNorm x) = ∏ i : Fin 4, f i (x i) := by
    intro x
    rw [exp_neg_sqNorm_eq_prod, Fin.prod_univ_four, Fin.prod_univ_four]
    simp [f]; ring
  simp_rw [hprod]
  rw [integral_fintype_prod_volume_eq_prod f, Fin.prod_univ_four]
  have h0 : ∫ t : ℝ, f 0 t =
      (((2 * n).factorial : ℝ) / (n.factorial : ℝ)) * Real.sqrt Real.pi := by
    have hmul : ∀ t : ℝ, f 0 t = (4 : ℝ) ^ n * (t ^ (2 * n) * Real.exp (-t ^ 2)) := by
      intro t
      simp only [f, ↓reduceIte, mul_pow, pow_mul]
      norm_num; ring
    simp_rw [hmul]
    rw [integral_const_mul, integral_even_pow_gaussian]
    have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
  have hg : ∫ t : ℝ, Real.exp (-t ^ 2) = Real.sqrt Real.pi := by simpa using integral_gaussian 1
  have h1 : ∫ t : ℝ, f 1 t = Real.sqrt Real.pi := by simpa [f] using hg
  have h2 : ∫ t : ℝ, f 2 t = Real.sqrt Real.pi := by simpa [f] using hg
  have h3 : ∫ t : ℝ, f 3 t = Real.sqrt Real.pi := by simpa [f] using hg
  rw [h0, h1, h2, h3]
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  calc (((2 * n).factorial : ℝ) / (n.factorial : ℝ)) * Real.sqrt Real.pi *
        Real.sqrt Real.pi * Real.sqrt Real.pi * Real.sqrt Real.pi
      = (((2 * n).factorial : ℝ) / (n.factorial : ℝ)) * (Real.sqrt Real.pi ^ 2) ^ 2 := by ring
    _ = (((2 * n).factorial : ℝ) / (n.factorial : ℝ)) * Real.pi ^ 2 := by rw [hsq]

lemma integrable_coord0_pow_exp_neg_sqNorm (n : ℕ) :
    Integrable (fun x : Fin 4 → ℝ => (2 * x 0) ^ (2 * n) * Real.exp (-sqNorm x)) := by
  let f : Fin 4 → ℝ → ℝ := fun i t =>
    if i = 0 then (2 * t) ^ (2 * n) * Real.exp (-t ^ 2) else Real.exp (-t ^ 2)
  have hprod : ∀ x : Fin 4 → ℝ,
      (2 * x 0) ^ (2 * n) * Real.exp (-sqNorm x) = ∏ i : Fin 4, f i (x i) := by
    intro x
    rw [exp_neg_sqNorm_eq_prod, Fin.prod_univ_four, Fin.prod_univ_four]
    simp [f]; ring
  simp_rw [hprod]
  refine Integrable.fintype_prod fun i => ?_
  by_cases hi : i = 0
  · subst hi
    have hmul : f 0 = fun t : ℝ => (4 : ℝ) ^ n * (t ^ (2 * n) * Real.exp (-t ^ 2)) := by
      funext t; simp only [f, ↓reduceIte, mul_pow, pow_mul]; norm_num; ring
    rw [hmul]
    exact (integrable_pow_mul_exp_neg_sq (2 * n)).const_mul _
  · have : f i = fun t : ℝ => Real.exp (-t ^ 2) := by funext t; simp [f, hi]
    rw [this]
    simpa using integrable_exp_neg_mul_sq (b := 1) zero_lt_one

lemma lintegral_ball_smul {r : ℝ} (hr : 0 < r) {g : (Fin 4 → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in {x : Fin 4 → ℝ | sqNorm x ≤ r ^ 2}, g x =
      ENNReal.ofReal (r ^ 4) * ∫⁻ y in {y : Fin 4 → ℝ | sqNorm y ≤ 1}, g (r • y) := by
  have hmap := Measure.map_addHaar_smul (volume : Measure (Fin 4 → ℝ)) (ne_of_gt hr)
  have hfin : Module.finrank ℝ (Fin 4 → ℝ) = 4 := Module.finrank_fin_fun ℝ
  rw [hfin, abs_of_pos (by positivity : 0 < (r ^ 4)⁻¹)] at hmap
  have hvol : (volume : Measure (Fin 4 → ℝ)) =
      ENNReal.ofReal (r ^ 4) • Measure.map (r • ·) (volume : Measure (Fin 4 → ℝ)) := by
    rw [hmap, smul_smul, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
      ENNReal.ofReal_one, one_smul]
  have hms1 : MeasurableSet {x : Fin 4 → ℝ | sqNorm x ≤ r ^ 2} :=
    measurableSet_le measurable_sqNorm measurable_const
  have hms2 : MeasurableSet {y : Fin 4 → ℝ | sqNorm y ≤ 1} :=
    measurableSet_le measurable_sqNorm measurable_const
  rw [← lintegral_indicator hms1]
  conv_lhs => rw [hvol]
  rw [lintegral_smul_measure, lintegral_map (hg.indicator hms1) (measurable_const_smul r)]
  congr 1
  rw [← lintegral_indicator hms2]
  refine lintegral_congr fun y => ?_
  by_cases hy : sqNorm y ≤ 1
  · have hry : sqNorm (r • y) ≤ r ^ 2 := by
      rw [sqNorm_smul]; nlinarith [sq_nonneg r]
    rw [Set.indicator_of_mem (show r • y ∈ {x | sqNorm x ≤ r ^ 2} from hry),
      Set.indicator_of_mem (show y ∈ {y | sqNorm y ≤ 1} from hy)]
  · have hry : ¬ sqNorm (r • y) ≤ r ^ 2 := by
      rw [sqNorm_smul]
      have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
      nlinarith
    rw [Set.indicator_of_notMem (show r • y ∉ {x | sqNorm x ≤ r ^ 2} from hry),
      Set.indicator_of_notMem (show y ∉ {y | sqNorm y ≤ 1} from hy)]

lemma lintegral_exp_neg_sqNorm_eq_two_mul_ball {f : (Fin 4 → ℝ) → ℝ≥0∞} (hf : Measurable f)
    (d : ℕ) (hhom : ∀ (r : ℝ) (x : Fin 4 → ℝ), 0 < r → f (r • x) = ENNReal.ofReal (r ^ (2 * d)) * f x) :
    ∫⁻ x : Fin 4 → ℝ, f x * ENNReal.ofReal (Real.exp (-sqNorm x)) =
      ENNReal.ofReal ((d + 2).factorial : ℝ) * ∫⁻ y in {y : Fin 4 → ℝ | sqNorm y ≤ 1}, f y := by
  have hrewrite : ∀ x : Fin 4 → ℝ,
      f x * ENNReal.ofReal (Real.exp (-sqNorm x)) =
      ∫⁻ u in Ioi (0 : ℝ), Set.indicator {p : (Fin 4 → ℝ) × ℝ | sqNorm p.1 ≤ p.2}
        (fun p => f p.1 * ENNReal.ofReal (Real.exp (-p.2))) (x, u) := by
    intro x
    rw [← lintegral_Ioi_exp_neg_from (sqNorm x) (sqNorm_nonneg x), ← lintegral_const_mul _ (by fun_prop)]
    have hms : MeasurableSet {u : ℝ | sqNorm x ≤ u} := measurableSet_le measurable_const measurable_id
    have h1 : ∫⁻ u in Ioi (0 : ℝ),
        Set.indicator {p : (Fin 4 → ℝ) × ℝ | sqNorm p.1 ≤ p.2}
          (fun p => f p.1 * ENNReal.ofReal (Real.exp (-p.2))) (x, u) =
        ∫⁻ u in Ioi (0 : ℝ) ∩ {u : ℝ | sqNorm x ≤ u}, f x * ENNReal.ofReal (Real.exp (-u)) := by
      symm
      rw [inter_comm, ← Measure.restrict_restrict hms, ← lintegral_indicator hms]
      refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      by_cases hu : sqNorm x ≤ u <;> simp [Set.indicator, hu]
    have hset : ((Ioi (0 : ℝ) ∩ {u : ℝ | sqNorm x ≤ u} : Set ℝ) =ᵐ[volume] Ioi (sqNorm x)) := by
      have hsub : Ioi (sqNorm x) ⊆ Ioi (0 : ℝ) ∩ {u : ℝ | sqNorm x ≤ u} := by
        intro u hu
        exact ⟨lt_of_le_of_lt (sqNorm_nonneg x) (mem_Ioi.1 hu), le_of_lt (mem_Ioi.1 hu)⟩
      have hdiff : (Ioi (0 : ℝ) ∩ {u : ℝ | sqNorm x ≤ u}) \ Ioi (sqNorm x) ⊆ {sqNorm x} := by
        rintro u ⟨⟨_, hu2⟩, hunot⟩
        exact le_antisymm (le_of_not_gt hunot) hu2
      rw [ae_eq_set]
      exact ⟨measure_mono_null hdiff (by simp), by rw [Set.sdiff_eq_empty.2 hsub, measure_empty]⟩
    rw [h1, setLIntegral_congr hset]
  simp_rw [hrewrite]
  have hmeas_prod : Measurable (Set.indicator {p : (Fin 4 → ℝ) × ℝ | sqNorm p.1 ≤ p.2}
      (fun p => f p.1 * ENNReal.ofReal (Real.exp (-p.2)))) := by
    refine Measurable.indicator ?_ (measurableSet_le (measurable_sqNorm.comp measurable_fst) measurable_snd)
    exact (hf.comp measurable_fst).mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_snd.neg))
  rw [lintegral_lintegral_swap
    (f := fun x u => Set.indicator {p : (Fin 4 → ℝ) × ℝ | sqNorm p.1 ≤ p.2}
      (fun p => f p.1 * ENNReal.ofReal (Real.exp (-p.2))) (x, u)) hmeas_prod.aemeasurable]
  have hinner : ∀ u ∈ Ioi (0 : ℝ),
      (∫⁻ x : Fin 4 → ℝ, Set.indicator {p : (Fin 4 → ℝ) × ℝ | sqNorm p.1 ≤ p.2}
        (fun p => f p.1 * ENNReal.ofReal (Real.exp (-p.2))) (x, u)) =
      ENNReal.ofReal (Real.exp (-u) * u ^ (d + 2)) * ∫⁻ y in {y : Fin 4 → ℝ | sqNorm y ≤ 1}, f y := by
    intro u hu
    have hu_pos : 0 < u := hu
    have hr_pos : 0 < Real.sqrt u := Real.sqrt_pos.2 hu_pos
    have hms_u : MeasurableSet {x : Fin 4 → ℝ | sqNorm x ≤ u} :=
      measurableSet_le measurable_sqNorm measurable_const
    have hind : (∫⁻ x : Fin 4 → ℝ, Set.indicator {p : (Fin 4 → ℝ) × ℝ | sqNorm p.1 ≤ p.2}
        (fun p => f p.1 * ENNReal.ofReal (Real.exp (-p.2))) (x, u)) =
        ENNReal.ofReal (Real.exp (-u)) * ∫⁻ x in {x : Fin 4 → ℝ | sqNorm x ≤ (Real.sqrt u) ^ 2}, f x := by
      rw [Real.sq_sqrt hu_pos.le, ← lintegral_const_mul _ hf, ← lintegral_indicator hms_u]
      refine lintegral_congr fun x => ?_
      by_cases hx : sqNorm x ≤ u <;> simp [Set.indicator, hx, mul_comm]
    rw [hind, lintegral_ball_smul hr_pos hf]
    have hhom_u : (∫⁻ y in {y : Fin 4 → ℝ | sqNorm y ≤ 1}, f (Real.sqrt u • y)) =
        ENNReal.ofReal (u ^ d) * ∫⁻ y in {y : Fin 4 → ℝ | sqNorm y ≤ 1}, f y := by
      have hrew : ∀ y : Fin 4 → ℝ, f (Real.sqrt u • y) = ENNReal.ofReal (u ^ d) * f y := by
        intro y
        rw [hhom (Real.sqrt u) y hr_pos, pow_mul, Real.sq_sqrt hu_pos.le]
      simp_rw [hrew]
      rw [lintegral_const_mul _ hf]
    rw [hhom_u]
    have h4 : Real.sqrt u ^ 4 = u ^ 2 := by
      calc Real.sqrt u ^ 4 = (Real.sqrt u ^ 2) ^ 2 := by ring
        _ = u ^ 2 := by rw [Real.sq_sqrt hu_pos.le]
    rw [h4, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2; ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner,
    lintegral_mul_const _ (by fun_prop), lintegral_Ioi_exp_neg_mul_pow (d + 2)]

/-- Normalized unit-ball ratio between `(2 y 0)^(2n)` and `(2 y 0 / ||y||)^(2n)`. -/
lemma lintegral_ball_radial_ratio (n : ℕ) (hn : 1 ≤ n) :
    ∫⁻ y in {y : Fin 4 → ℝ | sqNorm y ≤ 1}, ENNReal.ofReal ((2 * y 0) ^ (2 * n)) =
      ENNReal.ofReal (2 / ((n : ℝ) + 2)) *
        ∫⁻ y in {y : Fin 4 → ℝ | sqNorm y ≤ 1},
          ENNReal.ofReal (if y = 0 then 0 else (2 * y 0 / Real.sqrt (sqNorm y)) ^ (2 * n)) := by
  let B : Set (Fin 4 → ℝ) := {y | sqNorm y ≤ 1}
  have hB_meas : MeasurableSet B := measurableSet_le measurable_sqNorm measurable_const
  let h : (Fin 4 → ℝ) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (if y = 0 then 0 else (2 * y 0 / Real.sqrt (sqNorm y)) ^ (2 * n))
  have hh_meas : Measurable h := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
    have h0 : Measurable (fun y : Fin 4 → ℝ => y 0) := measurable_pi_apply 0
    exact ((measurable_const.mul h0).div (Real.continuous_sqrt.measurable.comp measurable_sqNorm)).pow_const _
  have hh_hom : ∀ (r : ℝ) (y : Fin 4 → ℝ), 0 < r → h (r • y) = h y := by
    intro r y hr
    dsimp only [h]
    by_cases hy : y = 0
    · simp [hy]
    · have hry : r • y ≠ 0 := smul_ne_zero (ne_of_gt hr) hy
      simp only [hy, hry, ↓reduceIte]
      rw [Pi.smul_apply, smul_eq_mul, sqNorm_smul, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
      congr 2
      have hne : r ≠ 0 := ne_of_gt hr
      field_simp
  -- Step 1: Tonelli on B × Ioc 0 1 with weight n * u^(n - 1)
  have htonelli :
      ∫⁻ y in B, h y * ENNReal.ofReal (1 - (sqNorm y) ^ n) =
        ENNReal.ofReal ((n : ℝ) / ((n : ℝ) + 2)) * ∫⁻ y in B, h y := by
    have hinner_y : ∀ y ∈ B,
        h y * ENNReal.ofReal (1 - (sqNorm y) ^ n) =
        ∫⁻ u in Ioc (0 : ℝ) 1, Set.indicator {p : (Fin 4 → ℝ) × ℝ | sqNorm p.1 ≤ p.2}
          (fun p => h p.1 * ENNReal.ofReal ((n : ℝ) * p.2 ^ (n - 1))) (y, u) := by
      intro y hy
      have hy0 : 0 ≤ sqNorm y := sqNorm_nonneg y
      have hy1 : sqNorm y ≤ 1 := hy
      have hint_val : ∫⁻ u in Ioc (sqNorm y) 1, ENNReal.ofReal ((n : ℝ) * u ^ (n - 1)) =
          ENNReal.ofReal (1 - (sqNorm y) ^ n) := by
        have hcont : ContinuousOn (fun u : ℝ => (n : ℝ) * u ^ (n - 1)) (Icc (sqNorm y) 1) := by
          fun_prop
        have hint : IntegrableOn (fun u : ℝ => (n : ℝ) * u ^ (n - 1)) (Ioc (sqNorm y) 1) :=
          (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
        have hnonneg : 0 ≤ᶠ[ae (volume.restrict (Ioc (sqNorm y) 1))]
            fun u : ℝ => (n : ℝ) * u ^ (n - 1) := by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
          exact mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (le_trans hy0 hu.1.le) _)
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
          ← intervalIntegral.integral_of_le hy1, intervalIntegral.integral_const_mul,
          integral_pow]
        rw [show n - 1 + 1 = n by omega]
        have hn0 : (n : ℝ) ≠ 0 := by positivity
        congr 1
        rw [show ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) by rw [Nat.cast_sub hn, Nat.cast_one]; ring,
          one_pow, mul_div_cancel₀ _ hn0]
      rw [← hint_val, ← lintegral_const_mul _ (by fun_prop)]
      have hms : MeasurableSet {u : ℝ | sqNorm y ≤ u} := measurableSet_le measurable_const measurable_id
      have h1 : (∫⁻ u in Ioc (0 : ℝ) 1,
          Set.indicator {p : (Fin 4 → ℝ) × ℝ | sqNorm p.1 ≤ p.2}
            (fun p => h p.1 * ENNReal.ofReal ((n : ℝ) * p.2 ^ (n - 1))) (y, u)) =
          ∫⁻ u in Ioc (0 : ℝ) 1 ∩ {u : ℝ | sqNorm y ≤ u},
            h y * ENNReal.ofReal ((n : ℝ) * u ^ (n - 1)) := by
        symm
        rw [inter_comm, ← Measure.restrict_restrict hms, ← lintegral_indicator hms]
        refine setLIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
        by_cases hu : sqNorm y ≤ u <;> simp [Set.indicator, hu]
      have hset : ((Ioc (0 : ℝ) 1 ∩ {u : ℝ | sqNorm y ≤ u} : Set ℝ) =ᵐ[volume] Ioc (sqNorm y) 1) := by
        have hsub : Ioc (sqNorm y) 1 ⊆ Ioc (0 : ℝ) 1 ∩ {u : ℝ | sqNorm y ≤ u} := by
          intro u hu
          exact ⟨⟨lt_of_le_of_lt hy0 hu.1, hu.2⟩, le_of_lt hu.1⟩
        have hdiff : (Ioc (0 : ℝ) 1 ∩ {u : ℝ | sqNorm y ≤ u}) \ Ioc (sqNorm y) 1 ⊆ {sqNorm y} := by
          rintro u ⟨⟨⟨_, hu12⟩, hu2⟩, hunot⟩
          have hle : u ≤ sqNorm y := by
            by_contra hgt
            exact hunot ⟨lt_of_not_ge hgt, hu12⟩
          exact le_antisymm hle hu2
        rw [ae_eq_set]
        exact ⟨measure_mono_null hdiff (by simp), by rw [Set.sdiff_eq_empty.2 hsub, measure_empty]⟩
      rw [h1, setLIntegral_congr hset]
    rw [setLIntegral_congr_fun hB_meas hinner_y]
    have hmeas_prod : Measurable (Set.indicator {p : (Fin 4 → ℝ) × ℝ | sqNorm p.1 ≤ p.2}
        (fun p => h p.1 * ENNReal.ofReal ((n : ℝ) * p.2 ^ (n - 1)))) := by
      refine Measurable.indicator ?_ (measurableSet_le (measurable_sqNorm.comp measurable_fst) measurable_snd)
      exact (hh_meas.comp measurable_fst).mul
        (ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_snd.pow_const _)))
    rw [lintegral_lintegral_swap
      (f := fun y u => Set.indicator {p : (Fin 4 → ℝ) × ℝ | sqNorm p.1 ≤ p.2}
        (fun p => h p.1 * ENNReal.ofReal ((n : ℝ) * p.2 ^ (n - 1))) (y, u)) hmeas_prod.aemeasurable]
    have hinner_u : ∀ u ∈ Ioc (0 : ℝ) 1,
        (∫⁻ y in B, Set.indicator {p : (Fin 4 → ℝ) × ℝ | sqNorm p.1 ≤ p.2}
          (fun p => h p.1 * ENNReal.ofReal ((n : ℝ) * p.2 ^ (n - 1))) (y, u)) =
        ENNReal.ofReal ((n : ℝ) * u ^ (n + 1)) * ∫⁻ y in B, h y := by
      intro u hu
      have hu_pos : 0 < u := hu.1
      have hu_le : u ≤ 1 := hu.2
      have hr_pos : 0 < Real.sqrt u := Real.sqrt_pos.2 hu_pos
      have hms_u : MeasurableSet {y : Fin 4 → ℝ | sqNorm y ≤ u} :=
        measurableSet_le measurable_sqNorm measurable_const
      have hsub_u : {y : Fin 4 → ℝ | sqNorm y ≤ u} ⊆ B := fun y hy => le_trans hy hu_le
      have hstep : (∫⁻ y in B, Set.indicator {p : (Fin 4 → ℝ) × ℝ | sqNorm p.1 ≤ p.2}
          (fun p => h p.1 * ENNReal.ofReal ((n : ℝ) * p.2 ^ (n - 1))) (y, u)) =
          ENNReal.ofReal ((n : ℝ) * u ^ (n - 1)) * ∫⁻ y in {y : Fin 4 → ℝ | sqNorm y ≤ (Real.sqrt u) ^ 2}, h y := by
        rw [Real.sq_sqrt hu_pos.le, ← lintegral_const_mul _ hh_meas, ← lintegral_indicator hms_u,
          ← lintegral_indicator hB_meas]
        refine lintegral_congr fun y => ?_
        by_cases hyu : sqNorm y ≤ u
        · have hyB : y ∈ B := hsub_u hyu
          simp [Set.indicator, hyu, hyB, mul_comm]
        · by_cases hyB : y ∈ B <;> simp [Set.indicator, hyu, hyB]
      rw [hstep, lintegral_ball_smul hr_pos hh_meas]
      simp_rw [hh_hom (Real.sqrt u) _ hr_pos]
      have h4 : Real.sqrt u ^ 4 = u ^ 2 := by
        calc Real.sqrt u ^ 4 = (Real.sqrt u ^ 2) ^ 2 := by ring
          _ = u ^ 2 := by rw [Real.sq_sqrt hu_pos.le]
      rw [h4, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [mul_assoc, ← pow_add, show n - 1 + 2 = n + 1 by omega]
    rw [setLIntegral_congr_fun measurableSet_Ioc hinner_u, lintegral_mul_const _ (by fun_prop)]
    congr 1
    have hcont : ContinuousOn (fun u : ℝ => (n : ℝ) * u ^ (n + 1)) (Icc 0 1) := by fun_prop
    have hint : IntegrableOn (fun u : ℝ => (n : ℝ) * u ^ (n + 1)) (Ioc 0 1) :=
      (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hnonneg : 0 ≤ᶠ[ae (volume.restrict (Ioc (0 : ℝ) 1))] fun u : ℝ => (n : ℝ) * u ^ (n + 1) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hu.1.le _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
      ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul, integral_pow]
    congr 1; push_cast; ring
  -- Step 2: Combine (sqNorm y)^n + (1 - (sqNorm y)^n) = 1 on B \ {0}
  have hsum : (∫⁻ y in B, ENNReal.ofReal ((2 * y 0) ^ (2 * n))) +
      (∫⁻ y in B, h y * ENNReal.ofReal (1 - (sqNorm y) ^ n)) = ∫⁻ y in B, h y := by
    have hzero : volume ({(0 : Fin 4 → ℝ)}) = 0 := by simp
    have h1 : ∫⁻ y in B, ENNReal.ofReal ((2 * y 0) ^ (2 * n)) =
        ∫⁻ y in B, h y * ENNReal.ofReal ((sqNorm y) ^ n) := by
      refine setLIntegral_congr_fun_ae hB_meas ?_
      filter_upwards [compl_mem_ae_iff.2 hzero] with y hy _
      have hy_ne : y ≠ 0 := hy
      have hpos : 0 < sqNorm y := lt_of_le_of_ne (sqNorm_nonneg y) (Ne.symm (mt (sqNorm_eq_zero_iff y).1 hy_ne))
      dsimp only [h]
      rw [if_neg hy_ne, ← ENNReal.ofReal_mul (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)]
      congr 1
      rw [div_pow, pow_mul (Real.sqrt (sqNorm y)), Real.sq_sqrt hpos.le,
        div_mul_cancel₀ _ (pow_ne_zero n hpos.ne')]
    rw [h1, ← lintegral_add_left (f := fun y => h y * ENNReal.ofReal (sqNorm y ^ n))
      (hh_meas.mul (ENNReal.measurable_ofReal.comp (measurable_sqNorm.pow_const n)))]
    refine setLIntegral_congr_fun hB_meas fun y hy => ?_
    have hy1 : (sqNorm y) ^ n ≤ 1 := pow_le_one₀ (sqNorm_nonneg y) hy
    rw [← mul_add, ← ENNReal.ofReal_add (pow_nonneg (sqNorm_nonneg y) n) (sub_nonneg.2 hy1)]
    simp
  have hfin : ∫⁻ y in B, h y ≠ ⊤ := by
    have hbound : ∀ y : Fin 4 → ℝ, h y ≤ ENNReal.ofReal ((4 : ℝ) ^ n) := by
      intro y
      dsimp only [h]
      apply ENNReal.ofReal_le_ofReal
      by_cases hy : y = 0
      · simp [hy]
      · rw [if_neg hy]
        have hpos : 0 < sqNorm y := lt_of_le_of_ne (sqNorm_nonneg y) (Ne.symm (mt (sqNorm_eq_zero_iff y).1 hy))
        have hle : (y 0) ^ 2 ≤ sqNorm y :=
          Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ 0)
        have habs : |y 0| ≤ Real.sqrt (sqNorm y) := by
          rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hle
        have hdiv : |2 * y 0 / Real.sqrt (sqNorm y)| ≤ 2 := by
          rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_pos (Real.sqrt_pos.2 hpos), div_le_iff₀ (Real.sqrt_pos.2 hpos)]
          linarith
        calc (2 * y 0 / Real.sqrt (sqNorm y)) ^ (2 * n)
            = |2 * y 0 / Real.sqrt (sqNorm y)| ^ (2 * n) := by rw [pow_mul, ← sq_abs, ← pow_mul]
          _ ≤ 2 ^ (2 * n) := pow_le_pow_left₀ (abs_nonneg _) hdiv _
          _ = (4 : ℝ) ^ n := by rw [pow_mul]; norm_num
    have hB_fin : volume B < ⊤ := by
      have hsub : B ⊆ Set.univ.pi (fun _ : Fin 4 => Icc (-1 : ℝ) 1) := by
        intro y hy i _
        have hle : (y i) ^ 2 ≤ 1 :=
          le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)) hy
        exact abs_le.1 (by nlinarith [sq_abs (y i)])
      exact lt_of_le_of_lt (measure_mono hsub) (by
        rw [show (volume : Measure (Fin 4 → ℝ)) = Measure.pi (fun _ => volume) from rfl, Measure.pi_pi]
        exact ENNReal.prod_lt_top fun _ _ => by simp)
    refine ne_of_lt (lt_of_le_of_lt (setLIntegral_mono' hB_meas fun y _ => hbound y) ?_)
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB_fin
  rw [htonelli] at hsum
  have h1eq : (1 : ℝ≥0∞) = ENNReal.ofReal (2 / ((n : ℝ) + 2)) + ENNReal.ofReal ((n : ℝ) / ((n : ℝ) + 2)) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    have hden : (n : ℝ) + 2 ≠ 0 := by positivity
    rw [show (2 : ℝ) / ((n : ℝ) + 2) + (n : ℝ) / ((n : ℝ) + 2) = 1 by field_simp; ring, ENNReal.ofReal_one]
  have hsum2 : (∫⁻ y in B, ENNReal.ofReal ((2 * y 0) ^ (2 * n))) +
      ENNReal.ofReal ((n : ℝ) / ((n : ℝ) + 2)) * (∫⁻ y in B, h y) =
      ENNReal.ofReal (2 / ((n : ℝ) + 2)) * (∫⁻ y in B, h y) +
      ENNReal.ofReal ((n : ℝ) / ((n : ℝ) + 2)) * (∫⁻ y in B, h y) := by
    rw [← add_mul, ← h1eq, one_mul]; exact hsum
  have hfin2 : ENNReal.ofReal ((n : ℝ) / ((n : ℝ) + 2)) * (∫⁻ y in B, h y) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  exact (ENNReal.add_left_inj hfin2).1 hsum2

lemma lintegral_gaussian_div_norm (n : ℕ) (hn : 1 ≤ n) :
    ∫⁻ x : Fin 4 → ℝ,
      ENNReal.ofReal (if x = 0 then 0 else (2 * x 0 / Real.sqrt (sqNorm x)) ^ (2 * n)) *
        ENNReal.ofReal (Real.exp (-sqNorm x)) =
      ENNReal.ofReal ((catalan n : ℝ) * Real.pi ^ 2) := by
  let h : (Fin 4 → ℝ) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (if x = 0 then 0 else (2 * x 0 / Real.sqrt (sqNorm x)) ^ (2 * n))
  let H : (Fin 4 → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal ((2 * x 0) ^ (2 * n))
  have hh_meas : Measurable h := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
    exact ((measurable_const.mul (measurable_pi_apply 0)).div
      (Real.continuous_sqrt.measurable.comp measurable_sqNorm)).pow_const _
  have hH_meas : Measurable H := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (measurable_const.mul (measurable_pi_apply 0)).pow_const _
  have h1 := lintegral_exp_neg_sqNorm_eq_two_mul_ball hh_meas 0 (fun r x hr => by
    simp only [mul_zero, pow_zero, ENNReal.ofReal_one, one_mul, h]
    by_cases hx : x = 0
    · simp [hx]
    · have hrx : r • x ≠ 0 := smul_ne_zero (ne_of_gt hr) hx
      simp only [hx, hrx, ↓reduceIte]
      rw [Pi.smul_apply, smul_eq_mul, sqNorm_smul, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
      congr 2; have hne : r ≠ 0 := ne_of_gt hr; field_simp)
  have h2 := lintegral_exp_neg_sqNorm_eq_two_mul_ball hH_meas n (fun r x hr => by
    simp only [H, Pi.smul_apply, smul_eq_mul]
    rw [show 2 * (r * x 0) = r * (2 * x 0) by ring, mul_pow, ENNReal.ofReal_mul (by positivity)])
  have h3 := lintegral_ball_radial_ratio n hn
  -- Compute LHS of h2 via integral_coord0_pow_exp_neg_sqNorm
  have hH_val : ∫⁻ x : Fin 4 → ℝ, H x * ENNReal.ofReal (Real.exp (-sqNorm x)) =
      ENNReal.ofReal ((((2 * n).factorial : ℝ) / (n.factorial : ℝ)) * Real.pi ^ 2) := by
    have hmul : ∀ x : Fin 4 → ℝ,
        H x * ENNReal.ofReal (Real.exp (-sqNorm x)) =
        ENNReal.ofReal ((2 * x 0) ^ (2 * n) * Real.exp (-sqNorm x)) := fun x => by
      dsimp only [H]
      rw [← ENNReal.ofReal_mul (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)]
    simp_rw [hmul]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_coord0_pow_exp_neg_sqNorm n)
      (Filter.Eventually.of_forall fun x => mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)
        (Real.exp_pos _).le), integral_coord0_pow_exp_neg_sqNorm]
  -- Relate h1, h2, h3:
  -- h2 = (n+2)! * (2/(n+2)) * ball_h = (n+1)! * (2 * ball_h) = (n+1)! * h1!
  have hrel : ENNReal.ofReal (((n + 1).factorial : ℝ)) *
      (∫⁻ x : Fin 4 → ℝ, h x * ENNReal.ofReal (Real.exp (-sqNorm x))) =
      ENNReal.ofReal ((((2 * n).factorial : ℝ) / (n.factorial : ℝ)) * Real.pi ^ 2) := by
    rw [h1, ← hH_val, h2, h3, ← mul_assoc, ← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hfac : ((n + 2).factorial : ℝ) = ((n : ℝ) + 2) * ((n + 1).factorial : ℝ) := by
      rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ]; push_cast; ring
    have hden : (n : ℝ) + 2 ≠ 0 := by positivity
    simp only [zero_add, Nat.factorial_two, Nat.cast_ofNat]
    rw [hfac]; field_simp
  have hcat : ((catalan n : ℝ) * ((n + 1).factorial : ℝ)) =
      ((2 * n).factorial : ℝ) / (n.factorial : ℝ) := by
    have hnat1 : catalan n * (n + 1) = (2 * n).choose n := by
      rw [← Nat.centralBinom_eq_two_mul_choose, catalan_eq_centralBinom_div]
      exact Nat.div_mul_cancel n.succ_dvd_centralBinom
    have hnat2 : (2 * n).choose n * n.factorial * n.factorial = (2 * n).factorial := by
      have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
      rwa [show 2 * n - n = n by omega] at this
    have hnat3 : catalan n * (n + 1).factorial * n.factorial = (2 * n).factorial := by
      calc catalan n * (n + 1).factorial * n.factorial
          = catalan n * ((n + 1) * n.factorial) * n.factorial := by rw [Nat.factorial_succ]
        _ = (catalan n * (n + 1)) * n.factorial * n.factorial := by ring
        _ = (2 * n).choose n * n.factorial * n.factorial := by rw [hnat1]
        _ = (2 * n).factorial := hnat2
    have hr3 : (catalan n : ℝ) * ((n + 1).factorial : ℝ) * (n.factorial : ℝ) = ((2 * n).factorial : ℝ) := by
      exact_mod_cast hnat3
    have hnf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    field_simp; linarith
  have hpos : ENNReal.ofReal ((n + 1).factorial : ℝ) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (by positivity)
  have htop : ENNReal.ofReal ((n + 1).factorial : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.mul_right_inj hpos htop).1
  rw [hrel, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← mul_assoc, mul_comm ((n + 1).factorial : ℝ) (catalan n : ℝ), hcat]

noncomputable def gamma4 : Measure (Fin 4 → ℝ) :=
  (ENNReal.ofReal (Real.pi ^ 2))⁻¹ •
    volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-sqNorm x)))

instance : IsProbabilityMeasure gamma4 := by
  constructor
  simp only [gamma4, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_exp_neg_sqNorm]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.2 (by positivity)) ENNReal.ofReal_ne_top

lemma gamma4_singleton_zero : gamma4 {(0 : Fin 4 → ℝ)} = 0 := by
  simp [gamma4]

lemma integral_div_norm_gamma4 (n : ℕ) (hn : 1 ≤ n) :
    ∫ x : Fin 4 → ℝ, (if x = 0 then 0 else (2 * x 0 / Real.sqrt (sqNorm x)) ^ (2 * n)) ∂gamma4 =
      (catalan n : ℝ) := by
  let f : (Fin 4 → ℝ) → ℝ := fun x =>
    if x = 0 then 0 else (2 * x 0 / Real.sqrt (sqNorm x)) ^ (2 * n)
  have hf_meas : Measurable f := by
    refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
    exact ((measurable_const.mul (measurable_pi_apply 0)).div
      (Real.continuous_sqrt.measurable.comp measurable_sqNorm)).pow_const _
  have hf_nonneg : ∀ x, 0 ≤ f x := fun x => by
    dsimp only [f]; split_ifs
    · exact le_rfl
    · rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
  have hf_bound : ∀ x, ‖f x‖ ≤ (4 : ℝ) ^ n := fun x => by
    rw [Real.norm_of_nonneg (hf_nonneg x)]
    dsimp only [f]; split_ifs with hx
    · positivity
    · have hpos : 0 < sqNorm x := lt_of_le_of_ne (sqNorm_nonneg x) (Ne.symm (mt (sqNorm_eq_zero_iff x).1 hx))
      have hle : (x 0) ^ 2 ≤ sqNorm x :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ 0)
      have habs : |x 0| ≤ Real.sqrt (sqNorm x) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hle
      have hdiv : |2 * x 0 / Real.sqrt (sqNorm x)| ≤ 2 := by
        rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos (Real.sqrt_pos.2 hpos), div_le_iff₀ (Real.sqrt_pos.2 hpos)]
        linarith
      calc (2 * x 0 / Real.sqrt (sqNorm x)) ^ (2 * n)
          = |2 * x 0 / Real.sqrt (sqNorm x)| ^ (2 * n) := by rw [pow_mul, ← sq_abs, ← pow_mul]
        _ ≤ 2 ^ (2 * n) := pow_le_pow_left₀ (abs_nonneg _) hdiv _
        _ = (4 : ℝ) ^ n := by rw [pow_mul]; norm_num
  have hint : Integrable f gamma4 :=
    Integrable.of_bound hf_meas.aestronglyMeasurable ((4 : ℝ) ^ n) (Filter.Eventually.of_forall hf_bound)
  have hlin : ∫⁻ x, ENNReal.ofReal (f x) ∂gamma4 = ENNReal.ofReal (catalan n : ℝ) := by
    simp only [gamma4, lintegral_smul_measure, smul_eq_mul]
    rw [lintegral_withDensity_eq_lintegral_mul (μ := volume)
      (f := fun x => ENNReal.ofReal (Real.exp (-sqNorm x)))
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_sqNorm.neg))
      (g := fun x => ENNReal.ofReal (f x))
      (ENNReal.measurable_ofReal.comp hf_meas)]
    have hcomm : (∫⁻ x : Fin 4 → ℝ, ENNReal.ofReal (Real.exp (-sqNorm x)) * ENNReal.ofReal (f x)) =
        ∫⁻ x : Fin 4 → ℝ, ENNReal.ofReal (f x) * ENNReal.ofReal (Real.exp (-sqNorm x)) :=
      lintegral_congr fun x => mul_comm _ _
    dsimp only [Pi.mul_apply]
    rw [hcomm, lintegral_gaussian_div_norm n hn, ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← mul_assoc, mul_comm _ (ENNReal.ofReal (catalan n : ℝ)), mul_assoc,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.2 (by positivity)) ENNReal.ofReal_ne_top,
      mul_one]
  have heq := ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hf_nonneg)
  rw [hlin] at heq
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hf_nonneg) (Nat.cast_nonneg _)).1 heq

lemma measurePreserving_mulVec_volume (M : Matrix.orthogonalGroup (Fin 4) ℝ) :
    MeasurePreserving (fun x : Fin 4 → ℝ => M.val.mulVec x) volume volume := by
  let e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
    { toLinearMap := Matrix.toLin' M.val
      invFun := M.valᵀ.mulVec
      left_inv := fun x => by
        change M.valᵀ.mulVec (M.val.mulVec x) = x
        rw [Matrix.mulVec_mulVec, (Matrix.mem_orthogonalGroup_iff' _ _).1 M.property, Matrix.one_mulVec]
      right_inv := fun x => by
        change M.val.mulVec (M.valᵀ.mulVec x) = x
        rw [Matrix.mulVec_mulVec, (Matrix.mem_orthogonalGroup_iff _ _).1 M.property, Matrix.one_mulVec] }
  have hdet : |LinearMap.det (e.symm : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))| = 1 := by
    have h1 : (e.symm : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) = Matrix.toLin' M.valᵀ := rfl
    rw [h1, LinearMap.det_toLin', Matrix.det_transpose]
    have hsq : M.val.det * M.val.det = 1 := by
      have hmul := congr_arg Matrix.det ((Matrix.mem_orthogonalGroup_iff _ _).1 M.property)
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hmul
      exact hmul
    rcases mul_self_eq_one_iff.1 hsq with h | h <;> simp [h]
  refine ⟨(Matrix.toLin' M.val).continuous_of_finiteDimensional.measurable, ?_⟩
  ext s hs
  change Measure.map (Matrix.toLin' M.val) volume s = volume s
  rw [Measure.map_apply (Matrix.toLin' M.val).continuous_of_finiteDimensional.measurable hs]
  have hpre := Measure.addHaar_preimage_linearEquiv (volume : Measure (Fin 4 → ℝ)) e s
  rw [hdet, ENNReal.ofReal_one, one_mul] at hpre
  exact hpre

lemma sqNorm_mulVec_orthogonal (M : Matrix.orthogonalGroup (Fin 4) ℝ) (x : Fin 4 → ℝ) :
    sqNorm (M.val.mulVec x) = sqNorm x := by
  have hdot : dotProduct (M.val.mulVec x) (M.val.mulVec x) = dotProduct x x := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
      (Matrix.mem_orthogonalGroup_iff' _ _).1 M.property, Matrix.one_mulVec]
  simpa [sqNorm, dotProduct, sq] using hdot

lemma measurePreserving_mulVec_gamma4 (M : Matrix.orthogonalGroup (Fin 4) ℝ) :
    MeasurePreserving (fun x : Fin 4 → ℝ => M.val.mulVec x) gamma4 gamma4 := by
  have hmeas : Measurable (fun x : Fin 4 → ℝ => M.val.mulVec x) :=
    (Matrix.toLin' M.val).continuous_of_finiteDimensional.measurable
  refine ⟨hmeas, ?_⟩
  ext s hs
  rw [Measure.map_apply hmeas hs]
  simp only [gamma4, Measure.smul_apply, smul_eq_mul, withDensity_apply _ (hmeas hs),
    withDensity_apply _ hs]
  congr 1
  rw [← lintegral_indicator (hmeas hs), ← lintegral_indicator hs]
  have hmp := measurePreserving_mulVec_volume M
  have hmap_int : ∫⁻ y, s.indicator (fun y => ENNReal.ofReal (Real.exp (-sqNorm y))) y ∂volume =
      ∫⁻ x, s.indicator (fun y => ENNReal.ofReal (Real.exp (-sqNorm y))) (M.val.mulVec x) ∂volume := by
    conv_lhs => rw [← hmp.map_eq]
    exact lintegral_map ((ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp measurable_sqNorm.neg)).indicator hs) hmeas
  rw [hmap_int]
  refine lintegral_congr fun x => ?_
  by_cases hx : M.val.mulVec x ∈ s
  · simp [Set.indicator, hx, sqNorm_mulVec_orthogonal M x]
  · simp [Set.indicator, hx]

/-! ### Section 3: Unit quaternions, double cover `Phi : S^3 x S^3 x Bool -> O(4)`, and surjectivity -/

noncomputable local instance instMeasurableSpaceQuaternion : MeasurableSpace ℍ[ℝ] := borel ℍ[ℝ]
local instance instBorelSpaceQuaternion : BorelSpace ℍ[ℝ] := ⟨rfl⟩

def qMk (a b c d : ℝ) : ℍ[ℝ] := ⟨a, b, c, d⟩

lemma qMk_re (a b c d : ℝ) : (qMk a b c d).re = a := rfl
lemma qMk_imI (a b c d : ℝ) : (qMk a b c d).imI = b := rfl
lemma qMk_imJ (a b c d : ℝ) : (qMk a b c d).imJ = c := rfl
lemma qMk_imK (a b c d : ℝ) : (qMk a b c d).imK = d := rfl

lemma q_equivTuple_0 (q : ℍ[ℝ]) : Quaternion.equivTuple ℝ q 0 = q.re := rfl
lemma q_equivTuple_1 (q : ℍ[ℝ]) : Quaternion.equivTuple ℝ q 1 = q.imI := rfl
lemma q_equivTuple_2 (q : ℍ[ℝ]) : Quaternion.equivTuple ℝ q 2 = q.imJ := rfl
lemma q_equivTuple_3 (q : ℍ[ℝ]) : Quaternion.equivTuple ℝ q 3 = q.imK := rfl

lemma q_star_re (q : ℍ[ℝ]) : (star q).re = q.re := by simp
lemma q_star_imI (q : ℍ[ℝ]) : (star q).imI = -q.imI := by simp
lemma q_star_imJ (q : ℍ[ℝ]) : (star q).imJ = -q.imJ := by simp
lemma q_star_imK (q : ℍ[ℝ]) : (star q).imK = -q.imK := by simp

lemma q_star_smul (c : ℝ) (q : ℍ[ℝ]) : star (c • q) = c • star q := by
  ext <;> simp

lemma q_normSq_eq (q : ℍ[ℝ]) :
    Quaternion.normSq q = q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 := by
  rw [Quaternion.normSq_def']

lemma q_symm_single0 : (Quaternion.equivTuple ℝ).symm (Pi.single 0 1) = qMk 1 0 0 0 := by
  ext <;> simp [qMk_re, qMk_imI, qMk_imJ, qMk_imK]
lemma q_symm_single1 : (Quaternion.equivTuple ℝ).symm (Pi.single 1 1) = qMk 0 1 0 0 := by
  ext <;> simp [qMk_re, qMk_imI, qMk_imJ, qMk_imK]
lemma q_symm_single2 : (Quaternion.equivTuple ℝ).symm (Pi.single 2 1) = qMk 0 0 1 0 := by
  ext <;> simp [qMk_re, qMk_imI, qMk_imJ, qMk_imK]
lemma q_symm_single3 : (Quaternion.equivTuple ℝ).symm (Pi.single 3 1) = qMk 0 0 0 1 := by
  ext <;> simp [qMk_re, qMk_imI, qMk_imJ, qMk_imK]

abbrev UnitQuat := {q : ℍ[ℝ] // Quaternion.normSq q = 1}

lemma normSq_eq_sqNorm (q : ℍ[ℝ]) :
    Quaternion.normSq q = sqNorm (Quaternion.equivTuple ℝ q) := by
  rw [q_normSq_eq, sqNorm, Fin.sum_univ_four,
    q_equivTuple_0, q_equivTuple_1, q_equivTuple_2, q_equivTuple_3]

instance : One UnitQuat := ⟨⟨1, Quaternion.normSq.map_one⟩⟩

noncomputable instance : Mul UnitQuat :=
  ⟨fun q1 q2 => ⟨q1.1 * q2.1, by rw [Quaternion.normSq.map_mul, q1.2, q2.2, mul_one]⟩⟩

instance : Inv UnitQuat :=
  ⟨fun q => ⟨star q.1, by rw [Quaternion.normSq_star, q.2]⟩⟩

noncomputable instance : Group UnitQuat where
  mul_assoc a b c := Subtype.ext (mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (one_mul a.1)
  mul_one a := Subtype.ext (mul_one a.1)
  inv_mul_cancel a := Subtype.ext (by
    change star a.1 * a.1 = 1
    rw [Quaternion.star_mul_self, a.2]; simp)

lemma unitQuat_one_val : ((1 : UnitQuat) : ℍ[ℝ]) = 1 := rfl
lemma unitQuat_mul_val (a b : UnitQuat) : ((a * b : UnitQuat) : ℍ[ℝ]) = a.1 * b.1 := rfl
lemma unitQuat_inv_val (a : UnitQuat) : ((a⁻¹ : UnitQuat) : ℍ[ℝ]) = star a.1 := rfl

instance : ContinuousMul UnitQuat where
  continuous_mul := (continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd) |>.subtype_mk _

instance : ContinuousInv UnitQuat where
  continuous_inv := (continuous_star.comp continuous_subtype_val).subtype_mk _

instance : IsTopologicalGroup UnitQuat where

lemma quaternion_equivTuple_continuous : Continuous (Quaternion.equivTuple ℝ) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact Quaternion.continuous_re
  · exact Quaternion.continuous_imI
  · exact Quaternion.continuous_imJ
  · exact Quaternion.continuous_imK

lemma quaternion_equivTuple_symm_continuous : Continuous (Quaternion.equivTuple ℝ).symm := by
  have h : ⇑(Quaternion.equivTuple ℝ).symm = fun v : Fin 4 → ℝ =>
      (v 0 • qMk 1 0 0 0 + v 1 • qMk 0 1 0 0) + (v 2 • qMk 0 0 1 0 + v 3 • qMk 0 0 0 1) := by
    funext v
    ext <;> simp [qMk_re, qMk_imI, qMk_imJ, qMk_imK]
  rw [h]
  exact (((continuous_apply 0).smul continuous_const).add
    ((continuous_apply 1).smul continuous_const)).add
    (((continuous_apply 2).smul continuous_const).add
    ((continuous_apply 3).smul continuous_const))

local instance instSecondCountableQuaternion : SecondCountableTopology ℍ[ℝ] :=
  let h : ℍ[ℝ] ≃ₜ (Fin 4 → ℝ) :=
    { toEquiv := Quaternion.equivTuple ℝ
      continuous_toFun := quaternion_equivTuple_continuous
      continuous_invFun := quaternion_equivTuple_symm_continuous }
  h.isInducing.secondCountableTopology

noncomputable def projS3 (x : Fin 4 → ℝ) : UnitQuat :=
  if hx : x = 0 then 1
  else
    ⟨(Real.sqrt (sqNorm x))⁻¹ • (Quaternion.equivTuple ℝ).symm x, by
      have hpos : 0 < sqNorm x :=
        lt_of_le_of_ne (sqNorm_nonneg x) (Ne.symm (mt (sqNorm_eq_zero_iff x).1 hx))
      rw [normSq_eq_sqNorm]
      have hlin : Quaternion.equivTuple ℝ ((Real.sqrt (sqNorm x))⁻¹ • (Quaternion.equivTuple ℝ).symm x) =
          (Real.sqrt (sqNorm x))⁻¹ • x := by
        ext i; fin_cases i <;> rfl
      rw [hlin, sqNorm_smul, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']⟩

lemma measurable_projS3 : Measurable projS3 := by
  have hval : (fun x : Fin 4 → ℝ => (projS3 x).1) =
      fun x => if x = 0 then (1 : ℍ[ℝ])
        else (Real.sqrt (sqNorm x))⁻¹ • (Quaternion.equivTuple ℝ).symm x := by
    funext x
    by_cases hx : x = 0 <;> simp [projS3, hx, unitQuat_one_val]
  have hmeas_val : Measurable (fun x : Fin 4 → ℝ => (projS3 x).1) := by
    rw [hval]
    refine Measurable.ite (measurableSet_singleton (0 : Fin 4 → ℝ)) measurable_const ?_
    exact ((Real.continuous_sqrt.measurable.comp measurable_sqNorm).inv).smul
      quaternion_equivTuple_symm_continuous.measurable
  exact hmeas_val.subtype_mk

noncomputable def muS3 : Measure UnitQuat := gamma4.map projS3

instance : IsProbabilityMeasure muS3 :=
  Measure.isProbabilityMeasure_map measurable_projS3.aemeasurable

/-- Linear action of `(q1, q2, s)` on `Fin 4 → ℝ` via quaternions. -/
noncomputable def quatActionFun (q1 q2 : UnitQuat) (s : Bool) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  Quaternion.equivTuple ℝ (q1.1 * (if s then star ((Quaternion.equivTuple ℝ).symm x)
    else (Quaternion.equivTuple ℝ).symm x) * star q2.1)

noncomputable def quatActionLin (q1 q2 : UnitQuat) (s : Bool) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun := quatActionFun q1 q2 s
  map_add' x y := by
    cases s <;>
    · simp only [quatActionFun, ↓reduceIte, Bool.false_eq_true]
      have hadd : (Quaternion.equivTuple ℝ).symm (x + y) =
          (Quaternion.equivTuple ℝ).symm x + (Quaternion.equivTuple ℝ).symm y := by
        ext <;> rfl
      rw [hadd]
      try rw [star_add]
      rw [mul_add, add_mul]
      ext i; fin_cases i <;> rfl
  map_smul' c x := by
    cases s <;>
    · simp only [quatActionFun, ↓reduceIte, Bool.false_eq_true, RingHom.id_apply]
      have hsmul : (Quaternion.equivTuple ℝ).symm (c • x) =
          c • (Quaternion.equivTuple ℝ).symm x := by
        ext <;> rfl
      rw [hsmul]
      try rw [q_star_smul]
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      ext i; fin_cases i <;> rfl

lemma sqNorm_quatActionFun (q1 q2 : UnitQuat) (s : Bool) (x : Fin 4 → ℝ) :
    sqNorm (quatActionFun q1 q2 s x) = sqNorm x := by
  dsimp only [quatActionFun]
  rw [← normSq_eq_sqNorm, Quaternion.normSq.map_mul, Quaternion.normSq.map_mul,
    Quaternion.normSq_star, q1.2, q2.2, one_mul, mul_one]
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, normSq_eq_sqNorm, Equiv.apply_symm_apply]
  · simp only [↓reduceIte, Quaternion.normSq_star, normSq_eq_sqNorm, Equiv.apply_symm_apply]

lemma dotProduct_quatActionFun (q1 q2 : UnitQuat) (s : Bool) (x y : Fin 4 → ℝ) :
    dotProduct (quatActionFun q1 q2 s x) (quatActionFun q1 q2 s y) = dotProduct x y := by
  have hpol : ∀ u v : Fin 4 → ℝ,
      2 * dotProduct u v = sqNorm (u + v) - sqNorm u - sqNorm v := by
    intro u v
    simp only [dotProduct, sqNorm, Pi.add_apply, Fin.sum_univ_four]; ring
  have h1 := sqNorm_quatActionFun q1 q2 s (x + y)
  have h2 := sqNorm_quatActionFun q1 q2 s x
  have h3 := sqNorm_quatActionFun q1 q2 s y
  have hadd : quatActionFun q1 q2 s (x + y) = quatActionFun q1 q2 s x + quatActionFun q1 q2 s y :=
    (quatActionLin q1 q2 s).map_add x y
  rw [hadd] at h1
  linarith [hpol (quatActionFun q1 q2 s x) (quatActionFun q1 q2 s y), hpol x y]

noncomputable def phiMat (q1 q2 : UnitQuat) (s : Bool) : Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toMatrix' (quatActionLin q1 q2 s)

lemma phiMat_mulVec (q1 q2 : UnitQuat) (s : Bool) (x : Fin 4 → ℝ) :
    (phiMat q1 q2 s).mulVec x = quatActionFun q1 q2 s x := by
  change (Matrix.toLin' (LinearMap.toMatrix' (quatActionLin q1 q2 s))) x = _
  rw [Matrix.toLin'_toMatrix']; rfl

lemma phiMat_mem_orthogonal (q1 q2 : UnitQuat) (s : Bool) :
    phiMat q1 q2 s ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ]
  ext i j
  have hdot := dotProduct_quatActionFun q1 q2 s (Pi.single i 1) (Pi.single j 1)
  rw [← phiMat_mulVec, ← phiMat_mulVec] at hdot
  have hlhs : ((phiMat q1 q2 s)ᵀ * phiMat q1 q2 s) i j =
      dotProduct ((phiMat q1 q2 s).mulVec (Pi.single i 1))
        ((phiMat q1 q2 s).mulVec (Pi.single j 1)) := by
    simp [Matrix.mul_apply, Matrix.mulVec_single, dotProduct]
  have hrhs : (1 : Matrix (Fin 4) (Fin 4) ℝ) i j =
      dotProduct (Pi.single i (1 : ℝ)) (Pi.single j 1) := by
    simp [Matrix.one_apply, dotProduct, Pi.single_apply]
    by_cases h : i = j <;> simp [h, eq_comm]
  rw [hlhs, hrhs, hdot]

noncomputable def Phi (g : UnitQuat × UnitQuat × Bool) : Matrix.orthogonalGroup (Fin 4) ℝ :=
  ⟨phiMat g.1 g.2.1 g.2.2, phiMat_mem_orthogonal g.1 g.2.1 g.2.2⟩

lemma continuous_Phi : Continuous Phi := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hentry : ∀ g : UnitQuat × UnitQuat × Bool,
      phiMat g.1 g.2.1 g.2.2 i j = quatActionFun g.1 g.2.1 g.2.2 (Pi.single j 1) i := fun g => by
    have := congr_fun (phiMat_mulVec g.1 g.2.1 g.2.2 (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  simp_rw [hentry]
  have hcond : Continuous (fun g : UnitQuat × UnitQuat × Bool =>
      if g.2.2 then star ((Quaternion.equivTuple ℝ).symm (Pi.single j (1 : ℝ)))
      else (Quaternion.equivTuple ℝ).symm (Pi.single j (1 : ℝ))) :=
    (continuous_of_discreteTopology (f := fun b : Bool =>
      if b then star ((Quaternion.equivTuple ℝ).symm (Pi.single j (1 : ℝ)))
      else (Quaternion.equivTuple ℝ).symm (Pi.single j (1 : ℝ)))).comp
      (continuous_snd.comp continuous_snd)
  have hmul : Continuous (fun g : UnitQuat × UnitQuat × Bool =>
      g.1.1 * (if g.2.2 then star ((Quaternion.equivTuple ℝ).symm (Pi.single j (1 : ℝ)))
        else (Quaternion.equivTuple ℝ).symm (Pi.single j (1 : ℝ))) * star g.2.1.1) :=
    ((continuous_subtype_val.comp continuous_fst).mul hcond).mul
      (continuous_star.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))
  exact (continuous_apply i).comp (quaternion_equivTuple_continuous.comp hmul)

noncomputable def act (p1 p2 : UnitQuat) (s1 : Bool) (g : UnitQuat × UnitQuat × Bool) :
    UnitQuat × UnitQuat × Bool :=
  if s1 then (p1 * g.2.1, p2 * g.1, !g.2.2)
  else (p1 * g.1, p2 * g.2.1, g.2.2)

lemma Phi_act (p1 p2 : UnitQuat) (s1 : Bool) (g : UnitQuat × UnitQuat × Bool) :
    Phi (act p1 p2 s1 g) = Phi (p1, p2, s1) * Phi g := by
  rcases g with ⟨q1, q2, s2⟩
  apply Subtype.ext
  change phiMat _ _ _ = phiMat p1 p2 s1 * phiMat q1 q2 s2
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
    Matrix.toLin'_apply, phiMat_mulVec, phiMat_mulVec, phiMat_mulVec]
  cases s1 <;> cases s2 <;>
  · simp only [act, quatActionFun, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
      Equiv.symm_apply_apply]
    congr 1
    change _ * _ * star (_ * _) = _
    simp only [unitQuat_mul_val, star_mul, star_star, mul_assoc]

/-! ### Section 4: Left-invariance of `muS3` and surjectivity of `Phi` -/

instance isMulLeftInvariant_muS3 : Measure.IsMulLeftInvariant muS3 := by
  constructor
  intro q
  have hmp : MeasurePreserving (fun x : Fin 4 → ℝ => (phiMat q 1 false).mulVec x) gamma4 gamma4 :=
    measurePreserving_mulVec_gamma4 (Phi (q, 1, false))
  have hcomm : ∀ x : Fin 4 → ℝ, x ≠ 0 →
      projS3 ((phiMat q 1 false).mulVec x) = q * projS3 x := by
    intro x hx
    rw [phiMat_mulVec]
    have hsq : sqNorm (quatActionFun q 1 false x) = sqNorm x := sqNorm_quatActionFun q 1 false x
    have hne : quatActionFun q 1 false x ≠ 0 := fun h0 => hx ((sqNorm_eq_zero_iff x).1 (hsq ▸ h0 ▸ (sqNorm_eq_zero_iff 0).2 rfl))
    apply Subtype.ext
    simp only [projS3, hx, hne, ↓reduceDIte, hsq]
    change (Real.sqrt (sqNorm x))⁻¹ • (Quaternion.equivTuple ℝ).symm (quatActionFun q 1 false x) =
      q.1 * ((Real.sqrt (sqNorm x))⁻¹ • (Quaternion.equivTuple ℝ).symm x)
    simp only [quatActionFun, Bool.false_eq_true, ↓reduceIte, Equiv.symm_apply_apply]
    change (Real.sqrt (sqNorm x))⁻¹ • (q.1 * (Quaternion.equivTuple ℝ).symm x * star (1 : ℍ[ℝ])) = _
    rw [star_one, mul_one, Algebra.mul_smul_comm]
  unfold muS3
  rw [Measure.map_map (continuous_const_mul q).measurable measurable_projS3]
  have hae : ((fun y => q * y) ∘ projS3) =ᵐ[gamma4]
      (projS3 ∘ fun x => (phiMat q 1 false).mulVec x) := by
    filter_upwards [compl_mem_ae_iff.2 gamma4_singleton_zero] with x hx
    exact (hcomm x hx).symm
  rw [Measure.map_congr hae, ← Measure.map_map measurable_projS3 hmp.measurable, hmp.map_eq]

lemma integral_muS3_re_pow (n : ℕ) (hn : 1 ≤ n) :
    ∫ q : UnitQuat, (2 * q.1.re) ^ (2 * n) ∂muS3 = (catalan n : ℝ) := by
  have hcont : Continuous (fun q : UnitQuat => (2 * q.1.re) ^ (2 * n)) :=
    (continuous_const.mul (Quaternion.continuous_re.comp continuous_subtype_val)).pow _
  unfold muS3
  rw [integral_map measurable_projS3.aemeasurable hcont.aestronglyMeasurable]
  rw [← integral_div_norm_gamma4 n hn]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 gamma4_singleton_zero] with x hx
  have hx' : x ≠ 0 := hx
  simp only [projS3, hx', ↓reduceDIte, ↓reduceIte]
  have hre : ((Real.sqrt (sqNorm x))⁻¹ • (Quaternion.equivTuple ℝ).symm x).re =
      (Real.sqrt (sqNorm x))⁻¹ * x 0 := rfl
  rw [hre]
  congr 1; ring

/-- Trace of `Phi (q1, q2, false)` is `4 * q1.re * q2.re`. -/
lemma trace_Phi_false (q1 q2 : UnitQuat) :
    (Phi (q1, q2, false)).val.trace = 4 * q1.1.re * q2.1.re := by
  change ∑ i : Fin 4, phiMat q1 q2 false i i = 4 * q1.1.re * q2.1.re
  have hentry : ∀ i : Fin 4,
      phiMat q1 q2 false i i = quatActionFun q1 q2 false (Pi.single i 1) i := fun i => by
    have := congr_fun (phiMat_mulVec q1 q2 false (Pi.single i 1)) i
    simpa [Matrix.mulVec_single] using this
  simp_rw [hentry]
  rw [Fin.sum_univ_four]
  simp only [quatActionFun, Bool.false_eq_true, ↓reduceIte,
    q_equivTuple_0, q_equivTuple_1, q_equivTuple_2, q_equivTuple_3,
    q_symm_single0, q_symm_single1, q_symm_single2, q_symm_single3]
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    q_star_re, q_star_imI, q_star_imJ, q_star_imK, qMk_re, qMk_imI, qMk_imJ, qMk_imK]
  ring

/-- Trace of `Phi (q1, q2, true)` is `-2 * (q1 * q2).re`. -/
lemma trace_Phi_true (q1 q2 : UnitQuat) :
    (Phi (q1, q2, true)).val.trace = -2 * (q1.1 * q2.1).re := by
  change ∑ i : Fin 4, phiMat q1 q2 true i i = -2 * (q1.1 * q2.1).re
  have hentry : ∀ i : Fin 4,
      phiMat q1 q2 true i i = quatActionFun q1 q2 true (Pi.single i 1) i := fun i => by
    have := congr_fun (phiMat_mulVec q1 q2 true (Pi.single i 1)) i
    simpa [Matrix.mulVec_single] using this
  simp_rw [hentry]
  rw [Fin.sum_univ_four]
  simp only [quatActionFun, ↓reduceIte,
    q_equivTuple_0, q_equivTuple_1, q_equivTuple_2, q_equivTuple_3,
    q_symm_single0, q_symm_single1, q_symm_single2, q_symm_single3]
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    q_star_re, q_star_imI, q_star_imJ, q_star_imK, qMk_re, qMk_imI, qMk_imJ, qMk_imK]
  ring

/-- Helper: Householder reflection `Phi (v, v, true)` for a unit purely imaginary quaternion `v`. -/
lemma householder_apply (v : UnitQuat) (x : ℍ[ℝ]) :
    (Quaternion.equivTuple ℝ).symm (quatActionFun v v true (Quaternion.equivTuple ℝ x)) =
      v.1 * star x * star v.1 := by
  dsimp only [quatActionFun]
  rw [if_pos rfl, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

lemma householder_refl_formula (v : UnitQuat) (hv : v.1.re = 0) (x : ℍ[ℝ]) (hx : x.re = 0) :
    v.1 * star x * star v.1 =
      x - (2 * (v.1.imI * x.imI + v.1.imJ * x.imJ + v.1.imK * x.imK)) • v.1 := by
  have hnorm : v.1.imI ^ 2 + v.1.imJ ^ 2 + v.1.imK ^ 2 = 1 := by
    have := v.2
    rw [q_normSq_eq, hv] at this
    linarith
  ext
  · simp [hv, hx]; ring
  · simp [hv, hx]
    linear_combination x.imI * hnorm
  · simp [hv, hx]
    linear_combination x.imJ * hnorm
  · simp [hv, hx]
    linear_combination x.imK * hnorm

lemma Phi_surjective : Function.Surjective Phi := by
  intro M
  -- Work via the orthogonal linear action `T x = equivTuple.symm (M.val *ᵥ equivTuple x)` on ℍ[ℝ].
  let actionOf (A : Matrix.orthogonalGroup (Fin 4) ℝ) (x : ℍ[ℝ]) : ℍ[ℝ] :=
    (Quaternion.equivTuple ℝ).symm (A.val.mulVec (Quaternion.equivTuple ℝ x))
  have hact_mul : ∀ A B : Matrix.orthogonalGroup (Fin 4) ℝ, ∀ x : ℍ[ℝ],
      actionOf (A * B) x = actionOf A (actionOf B x) := fun A B x => by
    dsimp only [actionOf]
    rw [Equiv.apply_symm_apply]
    change (Quaternion.equivTuple ℝ).symm ((A.val * B.val).mulVec (Quaternion.equivTuple ℝ x)) = _
    rw [Matrix.mulVec_mulVec]
  have hact_norm : ∀ A : Matrix.orthogonalGroup (Fin 4) ℝ, ∀ x : ℍ[ℝ],
      Quaternion.normSq (actionOf A x) = Quaternion.normSq x := fun A x => by
    simp only [actionOf, normSq_eq_sqNorm, Equiv.apply_symm_apply]
    exact sqNorm_mulVec_orthogonal A _
  have hact_dot : ∀ A : Matrix.orthogonalGroup (Fin 4) ℝ, ∀ x y : ℍ[ℝ],
      (actionOf A x).re * (actionOf A y).re + (actionOf A x).imI * (actionOf A y).imI +
        (actionOf A x).imJ * (actionOf A y).imJ + (actionOf A x).imK * (actionOf A y).imK =
      x.re * y.re + x.imI * y.imI + x.imJ * y.imJ + x.imK * y.imK := fun A x y => by
    have hpol : ∀ u v : ℍ[ℝ],
        2 * (u.re * v.re + u.imI * v.imI + u.imJ * v.imJ + u.imK * v.imK) =
        Quaternion.normSq (u + v) - Quaternion.normSq u - Quaternion.normSq v := fun u v => by
      simp only [q_normSq_eq, Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
        Quaternion.imK_add]; ring
    have hadd : actionOf A (x + y) = actionOf A x + actionOf A y := by
      dsimp only [actionOf]
      have h1 : Quaternion.equivTuple ℝ (x + y) = Quaternion.equivTuple ℝ x + Quaternion.equivTuple ℝ y := by
        ext i; fin_cases i <;> rfl
      rw [h1, Matrix.mulVec_add]
      ext <;> rfl
    have h1 := hact_norm A (x + y)
    rw [hadd] at h1
    linarith [hpol (actionOf A x) (actionOf A y), hpol x y, hact_norm A x, hact_norm A y]
  have hact_Phi : ∀ g : UnitQuat × UnitQuat × Bool, ∀ x : ℍ[ℝ],
      actionOf (Phi g) x = g.1.1 * (if g.2.2 then star x else x) * star g.2.1.1 := fun ⟨q1, q2, s⟩ x => by
    dsimp only [actionOf, Phi]
    rw [phiMat_mulVec]
    dsimp only [quatActionFun]
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  let ei : ℍ[ℝ] := qMk 0 1 0 0
  let ej : ℍ[ℝ] := qMk 0 0 1 0
  let ek : ℍ[ℝ] := qMk 0 0 0 1
  have heq_of_basis : ∀ A : Matrix.orthogonalGroup (Fin 4) ℝ,
      actionOf A 1 = 1 → actionOf A ei = ei → actionOf A ej = ej → actionOf A ek = ek →
      A = 1 := by
    intro A h1 hi hj hk
    apply Subtype.ext
    ext r c
    have hcol : ∀ (q : ℍ[ℝ]) (idx : Fin 4), Quaternion.equivTuple ℝ q = Pi.single idx 1 →
        actionOf A q = q → A.val r idx = (1 : Matrix (Fin 4) (Fin 4) ℝ) r idx := by
      intro q idx hq hAq
      have hv := congr_arg (Quaternion.equivTuple ℝ) hAq
      simp only [actionOf, Equiv.apply_symm_apply, hq] at hv
      have hr := congr_fun hv r
      simpa [Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply] using hr
    fin_cases c
    · exact hcol 1 0 (by ext a; fin_cases a <;> simp [q_equivTuple_0, q_equivTuple_1, q_equivTuple_2, q_equivTuple_3]) h1
    · exact hcol ei 1 (by ext a; fin_cases a <;> simp [ei, qMk_re, qMk_imI, qMk_imJ, qMk_imK, q_equivTuple_0, q_equivTuple_1, q_equivTuple_2, q_equivTuple_3]) hi
    · exact hcol ej 2 (by ext a; fin_cases a <;> simp [ej, qMk_re, qMk_imI, qMk_imJ, qMk_imK, q_equivTuple_0, q_equivTuple_1, q_equivTuple_2, q_equivTuple_3]) hj
    · exact hcol ek 3 (by ext a; fin_cases a <;> simp [ek, qMk_re, qMk_imI, qMk_imJ, qMk_imK, q_equivTuple_0, q_equivTuple_1, q_equivTuple_2, q_equivTuple_3]) hk
  -- Subgroup closure of Set.range Phi:
  have hmem_one : (1 : Matrix.orthogonalGroup (Fin 4) ℝ) ∈ Set.range Phi := by
    refine ⟨(1, 1, false), heq_of_basis _ ?_ ?_ ?_ ?_⟩ <;>
    · rw [hact_Phi]; simp [unitQuat_one_val]
  have hmem_mul : ∀ {A B}, A ∈ Set.range Phi → B ∈ Set.range Phi → A * B ∈ Set.range Phi := by
    rintro _ _ ⟨g1, rfl⟩ ⟨g2, rfl⟩
    exact ⟨act g1.1 g1.2.1 g1.2.2 g2, Phi_act g1.1 g1.2.1 g1.2.2 g2⟩
  -- Step 1: reduce to A1 fixing 1 via left-multiplication by q0 = actionOf M 1
  let q0 : UnitQuat := ⟨actionOf M 1, by rw [hact_norm, Quaternion.normSq.map_one]⟩
  let A1 : Matrix.orthogonalGroup (Fin 4) ℝ := Phi (q0⁻¹, 1, false) * M
  have hA1_1 : actionOf A1 1 = 1 := by
    rw [hact_mul, hact_Phi]
    simp only [Bool.false_eq_true, ↓reduceIte, unitQuat_inv_val, unitQuat_one_val, star_one, mul_one]
    change star q0.1 * q0.1 = 1
    rw [Quaternion.star_mul_self, q0.2]; simp
  -- Step 2: fix ei using at most one Householder reflection
  have hstep2 : ∃ g2 : UnitQuat × UnitQuat × Bool,
      actionOf (Phi g2 * A1) 1 = 1 ∧ actionOf (Phi g2 * A1) ei = ei := by
    let w := actionOf A1 ei
    have hw_norm : Quaternion.normSq w = 1 := by
      rw [hact_norm, q_normSq_eq]; simp [ei, qMk_re, qMk_imI, qMk_imJ, qMk_imK]
    have hw_re : w.re = 0 := by
      have hd := hact_dot A1 1 ei
      rw [hA1_1] at hd; simp [ei, qMk_re, qMk_imI, qMk_imJ, qMk_imK] at hd; exact hd
    by_cases hweq : w = ei
    · refine ⟨(1, 1, false), ?_, ?_⟩
      · rw [hact_mul, hA1_1, hact_Phi]; simp [unitQuat_one_val]
      · rw [hact_mul, show actionOf A1 ei = ei from hweq, hact_Phi]; simp [unitQuat_one_val]
    · let d : ℍ[ℝ] := w - ei
      have hd_ne : d ≠ 0 := sub_ne_zero.2 hweq
      have hd_pos : 0 < Quaternion.normSq d := by
        rw [normSq_eq_sqNorm]
        refine lt_of_le_of_ne (sqNorm_nonneg _) (Ne.symm fun h0 => hd_ne ?_)
        have := (sqNorm_eq_zero_iff _).1 h0
        exact (Quaternion.equivTuple ℝ).injective (by simpa using this)
      let v : UnitQuat := ⟨(Real.sqrt (Quaternion.normSq d))⁻¹ • d, by
        rw [normSq_eq_sqNorm]
        have hlin : Quaternion.equivTuple ℝ ((Real.sqrt (Quaternion.normSq d))⁻¹ • d) =
            (Real.sqrt (Quaternion.normSq d))⁻¹ • Quaternion.equivTuple ℝ d := by ext a; fin_cases a <;> rfl
        rw [hlin, sqNorm_smul, inv_pow, ← normSq_eq_sqNorm, Real.sq_sqrt hd_pos.le,
          inv_mul_cancel₀ hd_pos.ne']⟩
      have hv_re : v.1.re = 0 := by
        change (Real.sqrt (Quaternion.normSq d))⁻¹ * (w.re - ei.re) = 0
        simp [ei, qMk_re, hw_re]
      refine ⟨(v, v, true), ?_, ?_⟩
      · rw [hact_mul, hA1_1, hact_Phi]
        simp only [↓reduceIte, star_one, mul_one, Quaternion.self_mul_star, v.2]; simp
      · rw [hact_mul, hact_Phi]
        simp only [↓reduceIte]
        change v.1 * star w * star v.1 = ei
        rw [householder_refl_formula v hv_re w hw_re]
        have hdot_dw : d.imI * w.imI + d.imJ * w.imJ + d.imK * w.imK =
            Quaternion.normSq d / 2 := by
          rw [q_normSq_eq] at hw_norm ⊢
          have hdre : d.re = 0 := by change w.re - ei.re = 0; simp [ei, qMk_re, hw_re]
          have hdi : d.imI = w.imI - 1 := by change w.imI - ei.imI = w.imI - 1; simp [ei, qMk_imI]
          have hdj : d.imJ = w.imJ := by change w.imJ - ei.imJ = w.imJ; simp [ei, qMk_imJ]
          have hdk : d.imK = w.imK := by change w.imK - ei.imK = w.imK; simp [ei, qMk_imK]
          rw [hw_re] at hw_norm
          rw [hdre, hdi, hdj, hdk]
          linarith
        have hdot_vw : v.1.imI * w.imI + v.1.imJ * w.imJ + v.1.imK * w.imK =
            Real.sqrt (Quaternion.normSq d) / 2 := by
          have h1 : v.1.imI * w.imI + v.1.imJ * w.imJ + v.1.imK * w.imK =
              (Real.sqrt (Quaternion.normSq d))⁻¹ * (d.imI * w.imI + d.imJ * w.imJ + d.imK * w.imK) := by
            simp [v]; ring
          rw [h1, hdot_dw]
          have hsq : Real.sqrt (Quaternion.normSq d) * Real.sqrt (Quaternion.normSq d) = Quaternion.normSq d :=
            Real.mul_self_sqrt hd_pos.le
          have hsne : Real.sqrt (Quaternion.normSq d) ≠ 0 := (Real.sqrt_pos.2 hd_pos).ne'
          field_simp; linarith
        rw [hdot_vw]
        have hsc : (2 * (Real.sqrt (Quaternion.normSq d) / 2)) • v.1 = d := by
          dsimp only [v]
          rw [smul_smul]
          have hsne : Real.sqrt (Quaternion.normSq d) ≠ 0 := (Real.sqrt_pos.2 hd_pos).ne'
          rw [show 2 * (Real.sqrt (Quaternion.normSq d) / 2) * (Real.sqrt (Quaternion.normSq d))⁻¹ = 1 by
            field_simp, one_smul]
        rw [hsc]; simp [d]
  rcases hstep2 with ⟨g2, hA2_1, hA2_i⟩
  let A2 := Phi g2 * A1
  -- Step 3: fix ej while keeping 1 and ei fixed
  have hstep3 : ∃ g3 : UnitQuat × UnitQuat × Bool,
      actionOf (Phi g3 * A2) 1 = 1 ∧ actionOf (Phi g3 * A2) ei = ei ∧ actionOf (Phi g3 * A2) ej = ej := by
    let w := actionOf A2 ej
    have hw_norm : Quaternion.normSq w = 1 := by
      rw [hact_norm, q_normSq_eq]; simp [ej, qMk_re, qMk_imI, qMk_imJ, qMk_imK]
    have hw_re : w.re = 0 := by
      have hd := hact_dot A2 1 ej; rw [hA2_1] at hd; simp [ej, qMk_re, qMk_imI, qMk_imJ, qMk_imK] at hd; exact hd
    have hw_imI : w.imI = 0 := by
      have hd := hact_dot A2 ei ej; rw [hA2_i] at hd; simp [ei, ej, qMk_re, qMk_imI, qMk_imJ, qMk_imK] at hd; exact hd
    by_cases hweq : w = ej
    · refine ⟨(1, 1, false), ?_, ?_, ?_⟩
      · rw [hact_mul, hA2_1, hact_Phi]; simp [unitQuat_one_val]
      · rw [hact_mul, hA2_i, hact_Phi]; simp [unitQuat_one_val]
      · rw [hact_mul, show actionOf A2 ej = ej from hweq, hact_Phi]; simp [unitQuat_one_val]
    · let d : ℍ[ℝ] := w - ej
      have hd_ne : d ≠ 0 := sub_ne_zero.2 hweq
      have hd_pos : 0 < Quaternion.normSq d := by
        rw [normSq_eq_sqNorm]
        refine lt_of_le_of_ne (sqNorm_nonneg _) (Ne.symm fun h0 => hd_ne ?_)
        have := (sqNorm_eq_zero_iff _).1 h0
        exact (Quaternion.equivTuple ℝ).injective (by simpa using this)
      let v : UnitQuat := ⟨(Real.sqrt (Quaternion.normSq d))⁻¹ • d, by
        rw [normSq_eq_sqNorm]
        have hlin : Quaternion.equivTuple ℝ ((Real.sqrt (Quaternion.normSq d))⁻¹ • d) =
            (Real.sqrt (Quaternion.normSq d))⁻¹ • Quaternion.equivTuple ℝ d := by ext a; fin_cases a <;> rfl
        rw [hlin, sqNorm_smul, inv_pow, ← normSq_eq_sqNorm, Real.sq_sqrt hd_pos.le,
          inv_mul_cancel₀ hd_pos.ne']⟩
      have hv_re : v.1.re = 0 := by
        change (Real.sqrt (Quaternion.normSq d))⁻¹ * (w.re - ej.re) = 0
        simp [ej, qMk_re, hw_re]
      have hv_imI : v.1.imI = 0 := by
        change (Real.sqrt (Quaternion.normSq d))⁻¹ * (w.imI - ej.imI) = 0
        simp [ej, qMk_imI, hw_imI]
      refine ⟨(v, v, true), ?_, ?_, ?_⟩
      · rw [hact_mul, hA2_1, hact_Phi]
        simp only [↓reduceIte, star_one, mul_one, Quaternion.self_mul_star, v.2]; simp
      · rw [hact_mul, hA2_i, hact_Phi]
        simp only [↓reduceIte]
        rw [householder_refl_formula v hv_re ei rfl]
        simp [ei, qMk_imI, qMk_imJ, qMk_imK, hv_imI]
      · rw [hact_mul, hact_Phi]
        simp only [↓reduceIte]
        change v.1 * star w * star v.1 = ej
        rw [householder_refl_formula v hv_re w hw_re]
        have hdot_dw : d.imI * w.imI + d.imJ * w.imJ + d.imK * w.imK =
            Quaternion.normSq d / 2 := by
          rw [q_normSq_eq] at hw_norm ⊢
          have hdre : d.re = 0 := by change w.re - ej.re = 0; simp [ej, qMk_re, hw_re]
          have hdi : d.imI = 0 := by change w.imI - ej.imI = 0; simp [ej, qMk_imI, hw_imI]
          have hdj : d.imJ = w.imJ - 1 := by change w.imJ - ej.imJ = w.imJ - 1; simp [ej, qMk_imJ]
          have hdk : d.imK = w.imK := by change w.imK - ej.imK = w.imK; simp [ej, qMk_imK]
          rw [hw_re, hw_imI] at hw_norm
          rw [hdre, hdi, hdj, hdk]
          linarith
        have hdot_vw : v.1.imI * w.imI + v.1.imJ * w.imJ + v.1.imK * w.imK =
            Real.sqrt (Quaternion.normSq d) / 2 := by
          have h1 : v.1.imI * w.imI + v.1.imJ * w.imJ + v.1.imK * w.imK =
              (Real.sqrt (Quaternion.normSq d))⁻¹ * (d.imI * w.imI + d.imJ * w.imJ + d.imK * w.imK) := by
            simp [v]; ring
          rw [h1, hdot_dw]
          have hsq : Real.sqrt (Quaternion.normSq d) * Real.sqrt (Quaternion.normSq d) = Quaternion.normSq d :=
            Real.mul_self_sqrt hd_pos.le
          have hsne : Real.sqrt (Quaternion.normSq d) ≠ 0 := (Real.sqrt_pos.2 hd_pos).ne'
          field_simp; linarith
        rw [hdot_vw]
        have hsc : (2 * (Real.sqrt (Quaternion.normSq d) / 2)) • v.1 = d := by
          dsimp only [v]
          rw [smul_smul]
          have hsne : Real.sqrt (Quaternion.normSq d) ≠ 0 := (Real.sqrt_pos.2 hd_pos).ne'
          rw [show 2 * (Real.sqrt (Quaternion.normSq d) / 2) * (Real.sqrt (Quaternion.normSq d))⁻¹ = 1 by
            field_simp, one_smul]
        rw [hsc]; simp [d]
  rcases hstep3 with ⟨g3, hA3_1, hA3_i, hA3_j⟩
  let A3 := Phi g3 * A2
  -- Step 4: actionOf A3 ek is ±ek, so A3 = 1 or Phi (vk, vk, true) * A3 = 1
  have hA3_mem : A3 ∈ Set.range Phi := by
    let w := actionOf A3 ek
    have hw_norm : Quaternion.normSq w = 1 := by
      rw [hact_norm, q_normSq_eq]; simp [ek, qMk_re, qMk_imI, qMk_imJ, qMk_imK]
    have hw_re : w.re = 0 := by have hd := hact_dot A3 1 ek; rw [hA3_1] at hd; simp [ek, qMk_re, qMk_imI, qMk_imJ, qMk_imK] at hd; exact hd
    have hw_imI : w.imI = 0 := by have hd := hact_dot A3 ei ek; rw [hA3_i] at hd; simp [ei, ek, qMk_re, qMk_imI, qMk_imJ, qMk_imK] at hd; exact hd
    have hw_imJ : w.imJ = 0 := by have hd := hact_dot A3 ej ek; rw [hA3_j] at hd; simp [ej, ek, qMk_re, qMk_imI, qMk_imJ, qMk_imK] at hd; exact hd
    have hw_k2 : w.imK * w.imK = 1 := by
      rw [q_normSq_eq, hw_re, hw_imI, hw_imJ] at hw_norm; nlinarith
    rcases mul_self_eq_one_iff.1 hw_k2 with hk1 | hkm1
    · have hw_eq : w = ek := by ext <;> simp [ek, qMk_re, qMk_imI, qMk_imJ, qMk_imK, hw_re, hw_imI, hw_imJ, hk1]
      rw [heq_of_basis A3 hA3_1 hA3_i hA3_j hw_eq]; exact hmem_one
    · let vk : UnitQuat := ⟨ek, by rw [q_normSq_eq]; simp [ek, qMk_re, qMk_imI, qMk_imJ, qMk_imK]⟩
      have hprod1 : Phi (vk, vk, true) * A3 = 1 := by
        apply heq_of_basis
        · rw [hact_mul, hA3_1, hact_Phi]
          simp only [↓reduceIte, star_one, mul_one, Quaternion.self_mul_star, vk.2]; simp
        · rw [hact_mul, hA3_i, hact_Phi]; simp only [↓reduceIte]
          rw [householder_refl_formula vk rfl ei rfl]
          simp [vk, ei, ek, qMk_imI, qMk_imJ, qMk_imK]
        · rw [hact_mul, hA3_j, hact_Phi]; simp only [↓reduceIte]
          rw [householder_refl_formula vk rfl ej rfl]
          simp [vk, ej, ek, qMk_imI, qMk_imJ, qMk_imK]
        · rw [hact_mul, hact_Phi]; simp only [↓reduceIte]
          change vk.1 * star w * star vk.1 = ek
          rw [householder_refl_formula vk rfl w hw_re]
          ext <;> simp [vk, ek, qMk_re, qMk_imI, qMk_imJ, qMk_imK, hw_re, hw_imI, hw_imJ, hkm1]
          ring
      have hinv_vk : Phi (vk, vk, true) * Phi (vk, vk, true) = 1 := by
        rw [← Phi_act]; simp only [act, ↓reduceIte, Bool.not_true]
        have hvk2 : (vk * vk : UnitQuat).1 = -1 := by
          rw [unitQuat_mul_val]
          ext <;> simp [vk, ek, qMk_re, qMk_imI, qMk_imJ, qMk_imK]
        apply heq_of_basis <;>
        · rw [hact_Phi]; simp only [Bool.false_eq_true, ↓reduceIte, hvk2]; simp
      have hA3_eq : A3 = Phi (vk, vk, true) := by
        calc A3 = 1 * A3 := (one_mul A3).symm
          _ = (Phi (vk, vk, true) * Phi (vk, vk, true)) * A3 := by rw [hinv_vk]
          _ = Phi (vk, vk, true) * (Phi (vk, vk, true) * A3) := mul_assoc _ _ _
          _ = Phi (vk, vk, true) := by rw [hprod1, mul_one]
      exact ⟨(vk, vk, true), hA3_eq.symm⟩
  -- Unwind: M = Phi (q0, 1, false) * (Phi g2)⁻¹ * (Phi g3)⁻¹ * A3
  have hmem_inv : ∀ g : UnitQuat × UnitQuat × Bool, (Phi g)⁻¹ ∈ Set.range Phi := fun ⟨q1, q2, s⟩ => by
    let ginv : UnitQuat × UnitQuat × Bool := if s then (q2⁻¹, q1⁻¹, true) else (q1⁻¹, q2⁻¹, false)
    have hmul1 : Phi ginv * Phi (q1, q2, s) = 1 := by
      rw [← Phi_act]
      cases s <;>
      · simp only [act, ↓reduceIte, Bool.false_eq_true, Bool.not_true, inv_mul_cancel]
        apply heq_of_basis <;> (rw [hact_Phi]; simp [unitQuat_one_val])
    refine ⟨ginv, eq_inv_of_mul_eq_one_left hmul1⟩
  have hM : M = Phi (q0, 1, false) * ((Phi g2)⁻¹ * ((Phi g3)⁻¹ * A3)) := by
    have hq0inv : Phi (q0, 1, false) * Phi (q0⁻¹, 1, false) = 1 := by
      rw [← Phi_act]; simp only [act, Bool.false_eq_true, ↓reduceIte, mul_inv_cancel, mul_one]
      apply heq_of_basis <;> (rw [hact_Phi]; simp [unitQuat_one_val])
    calc M = 1 * M := (one_mul M).symm
      _ = Phi (q0, 1, false) * (Phi (q0⁻¹, 1, false) * M) := by rw [← mul_assoc, hq0inv, one_mul]
      _ = Phi (q0, 1, false) * A1 := rfl
      _ = Phi (q0, 1, false) * ((Phi g2)⁻¹ * A2) := by simp [A2, ← mul_assoc]
      _ = Phi (q0, 1, false) * ((Phi g2)⁻¹ * ((Phi g3)⁻¹ * A3)) := by simp [A3, ← mul_assoc]
  rw [hM]
  exact hmem_mul ⟨(q0, 1, false), rfl⟩ (hmem_mul (hmem_inv g2) (hmem_mul (hmem_inv g3) hA3_mem))

/-! ### Section 5: Compactness of `O(4)`, Haar measure identification, and trace moment -/

lemma compactSpace_orthogonalGroup4 : CompactSpace (Matrix.orthogonalGroup (Fin 4) ℝ) := by
  rw [← isCompact_univ_iff]
  have hclosed : IsClosed {A : Matrix (Fin 4) (Fin 4) ℝ | A ∈ Matrix.orthogonalGroup (Fin 4) ℝ} := by
    have heq : {A : Matrix (Fin 4) (Fin 4) ℝ | A ∈ Matrix.orthogonalGroup (Fin 4) ℝ} =
        {A : Matrix (Fin 4) (Fin 4) ℝ | A * Aᵀ = 1} := by
      ext A; exact Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ
    rw [heq]
    exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_transpose) continuous_const
  have hsub : {A : Matrix (Fin 4) (Fin 4) ℝ | A ∈ Matrix.orthogonalGroup (Fin 4) ℝ} ⊆
      Set.univ.pi (fun _ : Fin 4 => Set.univ.pi (fun _ : Fin 4 => Icc (-1 : ℝ) 1)) := by
    intro A hA i _ j _
    have hmul : (A * Aᵀ) i i = 1 := by
      rw [(Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).1 hA]; simp
    have hsum : ∑ k : Fin 4, (A i k) ^ 2 = 1 := by
      simpa [Matrix.mul_apply, sq] using hmul
    have hle : (A i j) ^ 2 ≤ 1 := by
      rw [← hsum]
      exact Finset.single_le_sum (fun k _ => sq_nonneg (A i k)) (Finset.mem_univ j)
    exact abs_le.1 (by nlinarith [sq_abs (A i j)])
  have hcomp_box : IsCompact (Set.univ.pi fun _ : Fin 4 => Set.univ.pi fun _ : Fin 4 => Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hcomp : IsCompact {A : Matrix (Fin 4) (Fin 4) ℝ | A ∈ Matrix.orthogonalGroup (Fin 4) ℝ} :=
    hcomp_box.of_isClosed_subset hclosed hsub
  exact isCompact_iff_compactSpace.1 hcomp |>.isCompact_univ

noncomputable def muBool : Measure Bool := (2⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure muBool := by
  constructor
  simp only [muBool, Measure.smul_apply, smul_eq_mul, Measure.count_univ, ENat.card_eq_coe_fintype_card,
    Fintype.card_bool, Nat.cast_ofNat]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

lemma measurePreserving_not_muBool : MeasurePreserving (! ·) muBool muBool := by
  refine ⟨measurable_of_countable _, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_of_countable _) hs]
  simp only [muBool, Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [← lintegral_indicator_one (measurable_of_countable _ hs), ← lintegral_indicator_one hs,
    lintegral_count, lintegral_count, tsum_fintype, tsum_fintype, Fintype.sum_bool, Fintype.sum_bool]
  by_cases h1 : false ∈ s <;> by_cases h2 : true ∈ s <;> simp [Set.indicator, h1, h2]

noncomputable def nuG : Measure (UnitQuat × UnitQuat × Bool) :=
  muS3.prod (muS3.prod muBool)

instance : IsProbabilityMeasure nuG := by unfold nuG; infer_instance

lemma measurePreserving_act (p1 p2 : UnitQuat) (s1 : Bool) :
    MeasurePreserving (act p1 p2 s1) nuG nuG := by
  have hmul1 : MeasurePreserving (p1 * ·) muS3 muS3 :=
    ⟨(continuous_const_mul p1).measurable, map_mul_left_eq_self muS3 p1⟩
  have hmul2 : MeasurePreserving (p2 * ·) muS3 muS3 :=
    ⟨(continuous_const_mul p2).measurable, map_mul_left_eq_self muS3 p2⟩
  cases s1
  · have hact : act p1 p2 false = Prod.map (p1 * ·) (Prod.map (p2 * ·) id) := by
      funext ⟨q1, q2, s2⟩; rfl
    rw [hact]
    exact hmul1.prod (hmul2.prod (MeasurePreserving.id muBool))
  · -- act p1 p2 true = (Prod.map (p1 * ·) (Prod.map (p2 * ·) (! ·))) ∘ swap12
    let swap12 : UnitQuat × UnitQuat × Bool → UnitQuat × UnitQuat × Bool :=
      fun g => (g.2.1, g.1, g.2.2)
    have hact : act p1 p2 true = (Prod.map (p1 * ·) (Prod.map (p2 * ·) (! ·))) ∘ swap12 := by
      funext ⟨q1, q2, s2⟩; rfl
    have hswap : MeasurePreserving swap12 nuG nuG := by
      have heq : swap12 =
          (MeasurableEquiv.prodAssoc).toFun ∘
          (Prod.map Prod.swap id) ∘
          (MeasurableEquiv.prodAssoc).symm.toFun := by
        funext ⟨q1, q2, s2⟩; rfl
      rw [heq]
      have h1 := measurePreserving_prodAssoc muS3 muS3 muBool
      have h2 : MeasurePreserving (Prod.map Prod.swap (id : Bool → Bool))
          ((muS3.prod muS3).prod muBool) ((muS3.prod muS3).prod muBool) :=
        (Measure.measurePreserving_swap (μ := muS3) (ν := muS3)).prod (MeasurePreserving.id muBool)
      exact h1.comp (h2.comp h1.symm)
    rw [hact]
    exact (hmul1.prod (hmul2.prod measurePreserving_not_muBool)).comp hswap

theorem main_proof :
    ∀ [MeasurableSpace (Matrix.orthogonalGroup (Fin 4) ℝ)]
      [BorelSpace (Matrix.orthogonalGroup (Fin 4) ℝ)]
      (μ : Measure (Matrix.orthogonalGroup (Fin 4) ℝ))
      [Measure.IsHaarMeasure μ]
      [IsProbabilityMeasure μ]
      (n : ℕ), 1 ≤ n →
      OMA.S_oeis_a246860.a μ n = (catalan n : ℝ) * ((catalan n : ℝ) + 1) / 2 := by
  intro mO hBorel μ hHaar hProb n hn
  have : CompactSpace (Matrix.orthogonalGroup (Fin 4) ℝ) := compactSpace_orthogonalGroup4
  have : SecondCountableTopology (Matrix (Fin 4) (Fin 4) ℝ) := by
    change SecondCountableTopology (Fin 4 → Fin 4 → ℝ)
    infer_instance
  have : SecondCountableTopology (Matrix.orthogonalGroup (Fin 4) ℝ) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let ν : Measure (Matrix.orthogonalGroup (Fin 4) ℝ) := nuG.map Phi
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map continuous_Phi.measurable.aemeasurable
  have : Measure.IsMulLeftInvariant ν := by
    constructor
    intro M
    rcases Phi_surjective M with ⟨⟨p1, p2, s1⟩, rfl⟩
    dsimp only [ν]
    rw [Measure.map_map (continuous_const_mul _).measurable continuous_Phi.measurable]
    have hcomp : ((fun x => Phi (p1, p2, s1) * x) ∘ Phi) = Phi ∘ act p1 p2 s1 := by
      funext g; exact (Phi_act p1 p2 s1 g).symm
    rw [hcomp, ← Measure.map_map continuous_Phi.measurable (measurePreserving_act p1 p2 s1).measurable,
      (measurePreserving_act p1 p2 s1).map_eq]
  have hμ_eq : ν = μ := by
    have hsmul := Measure.isMulLeftInvariant_eq_smul ν μ
    have huniv : ν Set.univ = (Measure.haarScalarFactor ν μ : ℝ≥0∞) * μ Set.univ := by
      have := congr_arg (fun m : Measure (Matrix.orthogonalGroup (Fin 4) ℝ) => m Set.univ) hsmul
      simpa [Measure.smul_apply, smul_eq_mul] using this
    rw [measure_univ, measure_univ, mul_one] at huniv
    have h1 : Measure.haarScalarFactor ν μ = 1 := ENNReal.coe_eq_one.1 huniv.symm
    rw [hsmul, h1, one_smul]
  unfold OMA.S_oeis_a246860.a
  rw [← hμ_eq]
  have hcont_f : Continuous (fun O : Matrix.orthogonalGroup (Fin 4) ℝ => (O.val.trace) ^ (2 * n)) := by
    have htr : Continuous (fun O : Matrix.orthogonalGroup (Fin 4) ℝ => O.val.trace) := by
      change Continuous (fun O : Matrix.orthogonalGroup (Fin 4) ℝ => ∑ i : Fin 4, O.val i i)
      exact continuous_finsetSum _ fun i _ =>
        (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
    exact htr.pow _
  rw [integral_map continuous_Phi.measurable.aemeasurable hcont_f.aestronglyMeasurable]
  -- Evaluate the integral over nuG = muS3 × (muS3 × muBool)
  have : CompactSpace UnitQuat := by
    have hcomp_box : IsCompact ((Quaternion.equivTuple ℝ).symm ''
        (Set.univ.pi fun _ : Fin 4 => Icc (-1 : ℝ) 1)) :=
      (isCompact_univ_pi fun _ => isCompact_Icc).image quaternion_equivTuple_symm_continuous
    have hclosed : IsClosed {q : ℍ[ℝ] | Quaternion.normSq q = 1} := by
      have heq : {q : ℍ[ℝ] | Quaternion.normSq q = 1} =
          {q : ℍ[ℝ] | sqNorm (Quaternion.equivTuple ℝ q) = 1} := by
        ext q
        exact ⟨fun h => (normSq_eq_sqNorm q).symm.trans h, fun h => (normSq_eq_sqNorm q).trans h⟩
      rw [heq]
      exact isClosed_eq (continuous_sqNorm.comp quaternion_equivTuple_continuous) continuous_const
    have hsub : {q : ℍ[ℝ] | Quaternion.normSq q = 1} ⊆
        (Quaternion.equivTuple ℝ).symm '' (Set.univ.pi fun _ : Fin 4 => Icc (-1 : ℝ) 1) := by
      intro q hq
      refine ⟨Quaternion.equivTuple ℝ q, ?_, Equiv.symm_apply_apply _ q⟩
      intro i _
      have h1 : sqNorm (Quaternion.equivTuple ℝ q) = 1 := (normSq_eq_sqNorm q).symm.trans hq
      have hle : (Quaternion.equivTuple ℝ q i) ^ 2 ≤ 1 := by
        rw [← h1]
        exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      exact abs_le.1 (by nlinarith [sq_abs (Quaternion.equivTuple ℝ q i)])
    exact isCompact_iff_compactSpace.1 (hcomp_box.of_isClosed_subset hclosed hsub)
  have hintG : Integrable (fun g : UnitQuat × UnitQuat × Bool => ((Phi g).val.trace) ^ (2 * n)) nuG :=
    (hcont_f.comp continuous_Phi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold nuG at hintG ⊢
  rw [integral_prod _ hintG]
  have hinner_q1 : ∀ q1 : UnitQuat,
      (∫ p : UnitQuat × Bool, ((Phi (q1, p)).val.trace) ^ (2 * n) ∂(muS3.prod muBool)) =
        (1 / 2 : ℝ) * ((2 * q1.1.re) ^ (2 * n) * (catalan n : ℝ)) +
        (1 / 2 : ℝ) * (catalan n : ℝ) := by
    intro q1
    have hint_p : Integrable (fun p : UnitQuat × Bool => ((Phi (q1, p)).val.trace) ^ (2 * n))
        (muS3.prod muBool) := by
      have hcont_p : Continuous (fun p : UnitQuat × Bool => ((Phi (q1, p)).val.trace) ^ (2 * n)) :=
        (hcont_f.comp continuous_Phi).comp (continuous_const.prodMk continuous_id)
      exact hcont_p.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [integral_prod_symm _ hint_p]
    have hbool_eval : ∀ F : Bool → ℝ, ∫ b : Bool, F b ∂muBool = (1 / 2 : ℝ) * F false + (1 / 2 : ℝ) * F true := by
      intro F
      simp only [muBool, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul,
        integral_countable (Integrable.of_finite), tsum_fintype, Fintype.sum_bool,
        Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_mul]
      ring
    rw [hbool_eval]
    congr 1
    · congr 1
      have hrew : ∀ q2 : UnitQuat,
          ((Phi (q1, q2, false)).val.trace) ^ (2 * n) =
          (2 * q1.1.re) ^ (2 * n) * (2 * q2.1.re) ^ (2 * n) := fun q2 => by
        rw [trace_Phi_false, show (4 : ℝ) * q1.1.re * q2.1.re = (2 * q1.1.re) * (2 * q2.1.re) by ring,
          mul_pow]
      simp_rw [hrew]
      rw [integral_const_mul, integral_muS3_re_pow n hn]
    · congr 1
      have hrew : ∀ q2 : UnitQuat,
          ((Phi (q1, q2, true)).val.trace) ^ (2 * n) =
          (2 * (q1 * q2).1.re) ^ (2 * n) := fun q2 => by
        rw [trace_Phi_true]
        change (-2 * (q1 * q2).1.re) ^ (2 * n) = (2 * (q1 * q2).1.re) ^ (2 * n)
        rw [pow_mul, pow_mul]; congr 1; ring
      simp_rw [hrew]
      rw [integral_mul_left_eq_self (fun q : UnitQuat => (2 * q.1.re) ^ (2 * n)) q1,
        integral_muS3_re_pow n hn]
  simp_rw [hinner_q1]
  have hint_q1 : Integrable (fun q1 : UnitQuat => (1 / 2 : ℝ) * ((2 * q1.1.re) ^ (2 * n) * (catalan n : ℝ))) muS3 := by
    have hcont : Continuous (fun q1 : UnitQuat => (1 / 2 : ℝ) * ((2 * q1.1.re) ^ (2 * n) * (catalan n : ℝ))) :=
      continuous_const.mul (((continuous_const.mul (Quaternion.continuous_re.comp continuous_subtype_val)).pow _).mul continuous_const)
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_add hint_q1 (integrable_const _), integral_const_mul, integral_mul_const,
    integral_muS3_re_pow n hn, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  ring

end A246860Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a246860.main :=
  A246860Proof.main_proof
