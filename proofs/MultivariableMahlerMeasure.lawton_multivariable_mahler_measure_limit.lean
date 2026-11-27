import FormalConjectures.Wikipedia.MultivariableMahlerMeasure
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Lawton's limit theorem for Mahler measure

A translated difference removes a character while retaining a set on which
the two translates are small. This gives a uniform power bound on the
measure of sublevel sets. The logarithm can then be truncated uniformly,
and the torus Fourier polynomials give convergence for the truncation.
-/

/-
# Uniform small-value estimates for short character sums

A translate eliminates one term while retaining part of a small-value set.
The estimates are uniform in frequencies provided distinct characters have
uniformly separated phases in measure. For the sparse small-value estimates
underlying Mahler's limit theorem, see Wayne M. Lawton, arXiv:1904.09373.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LawtonSmallBall

section Shift

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

/-- A small set of excluded shifts cannot carry most of the average overlap
of a measurable set with its translates. -/
theorem exists_shift {E Bad : Set G} (hE : MeasurableSet E) (hBad : MeasurableSet Bad)
    (hm : 0 < μ.real E) (hsmall : μ.real Bad ≤ μ.real E / 4) :
    ∃ y ∉ Bad, (μ.real E) ^ 2 / 2 ≤ μ.real (E ∩ (fun x => x + y) ⁻¹' E) := by
  classical
  let overlap (y : G) : Set G := E ∩ (fun x => x + y) ⁻¹' E
  let shear (q : G × G) : G × G := (q.2, q.2 + q.1)
  have hs : MeasurePreserving shear (μ.prod μ) (μ.prod μ) :=
    measurePreserving_prod_add_swap μ μ
  have hmean : (∫⁻ y, μ (overlap y) ∂μ) = μ E * μ E := by
    have hprod := hs.measure_preimage (hE.prod hE).nullMeasurableSet
    rw [Measure.prod_prod, Measure.prod_apply ((hE.prod hE).preimage hs.measurable)] at hprod
    exact hprod
  by_contra! hnone
  let m := μ E
  let half := m * m / 2
  have hmfin : m ≠ ∞ := measure_ne_top μ E
  have hhfin : half ≠ ∞ := by
    dsimp only [half]
    finiteness
  have hbound (y : G) :
      μ (overlap y) ≤ half + Bad.indicator (fun _ => m) y := by
    by_cases hy : y ∈ Bad
    · rw [Set.indicator_of_mem hy]
      exact (measure_mono inter_subset_left).trans (le_add_self)
    · rw [Set.indicator_of_notMem hy, add_zero]
      have hr : μ.real (overlap y) ≤ (μ.real E) ^ 2 / 2 := (hnone y hy).le
      apply (ENNReal.toReal_le_toReal (measure_ne_top μ _) hhfin).mp
      simpa only [Measure.real, half, m, ENNReal.toReal_div, ENNReal.toReal_mul,
        ENNReal.toReal_ofNat, pow_two] using hr
  have hI : μ E * μ E ≤ half + m * μ Bad := by
    rw [← hmean]
    calc
      _ ≤ ∫⁻ y, (half + Bad.indicator (fun _ => m) y) ∂μ := lintegral_mono hbound
      _ = _ := by
        rw [lintegral_add_left measurable_const, lintegral_const, lintegral_indicator_const hBad,
          measure_univ, mul_one]
  have hfin : half + m * μ Bad ≠ ∞ := by finiteness
  have hR := ENNReal.toReal_mono hfin hI
  have hmB : m * μ Bad ≠ ∞ := by finiteness
  rw [ENNReal.toReal_mul, ENNReal.toReal_add hhfin hmB, ENNReal.toReal_mul] at hR
  have he : half.toReal = (μ.real E) ^ 2 / 2 := by
    simp only [half, m, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      Measure.real, pow_two]
  rw [he] at hR
  change μ.real E * μ.real E ≤ (μ.real E) ^ 2 / 2 + μ.real E * μ.real Bad at hR
  nlinarith only [hR, mul_le_mul_of_nonneg_left hsmall hm.le, sq_pos_of_pos hm]

end Shift

/-- The exponent in the power-form small-ball estimate for a sum with `k+1` terms. -/
def exponent : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * exponent k + 1

/-- The corresponding constant, independent of the chosen character frequencies. -/
noncomputable def constant : ℕ → ℝ
  | 0 => 1
  | k + 1 => (8 * 2 ^ exponent k) * constant k

private lemma exponent_pos (k : ℕ) : 0 < exponent k := by
  cases k <;> simp only [exponent] <;> omega

private lemma constant_pos (k : ℕ) : 0 < constant k := by
  induction k with
  | zero => norm_num [constant]
  | succ k ih => rw [constant]; positivity

section Estimate

variable {G ι : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (χ : ι → G → ℂ)

/-- Sublevel sets for a finite linear combination of characters. -/
def sublevel (s : Finset ι) (a : ι → ℂ) (ε : ℝ) : Set G :=
  {x | ‖∑ i ∈ s, a i * χ i x‖ ≤ ε}

omit [AddCommGroup G] [MeasurableAdd₂ G] in
private lemma measurable_sublevel (hmeas : ∀ i, Measurable (χ i))
    (s : Finset ι) (a : ι → ℂ) (ε : ℝ) : MeasurableSet (sublevel χ s a ε) := by
  have hf : Measurable (fun x => ∑ i ∈ s, a i * χ i x) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.mul (hmeas i))
  exact measurableSet_le hf.norm measurable_const

/-- A uniform power bound for sublevel measures, in terms of any one
distinguished coefficient of the sum. -/
theorem bound (hmeas : ∀ i, Measurable (χ i))
    (hadd : ∀ i x y, χ i (x + y) = χ i x * χ i y)
    (hnorm : ∀ i x, ‖χ i x‖ = 1)
    (hphase : ∀ {i j : ι}, i ≠ j → ∀ δ : ℝ, 0 ≤ δ →
      μ.real {y | ‖χ i y - χ j y‖ < δ} ≤ δ)
    (k : ℕ) (s : Finset ι) (hs : s.card = k + 1) (a : ι → ℂ) {i : ι} (hi : i ∈ s)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μ.real (sublevel χ s a ε)) ^ exponent k * ‖a i‖ ≤ constant k * ε := by
  classical
  induction k generalizing s a i ε with
  | zero =>
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hs
    obtain rfl := Finset.mem_singleton.mp hi
    by_cases h : ‖a i‖ ≤ ε
    · have hm : μ.real (sublevel χ {i} a ε) ≤ 1 := by
        simpa [Measure.real] using
          (measureReal_mono (μ := μ) (Set.subset_univ (sublevel χ {i} a ε)))
      simpa only [exponent, constant, pow_one, one_mul] using
        (mul_le_mul_of_nonneg_right hm (norm_nonneg (a i))).trans (by simpa using h)
    · have he : sublevel χ {i} a ε = ∅ := by
        ext x
        simp [sublevel, hnorm, h]
      simp [he, exponent, constant, hε]
  | succ k ih =>
    let E := sublevel χ s a ε
    let m := μ.real E
    have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
    by_cases hm : m = 0
    · change m ^ exponent (k + 1) * ‖a i‖ ≤ constant (k + 1) * ε
      rw [hm, zero_pow (exponent_pos (k + 1)).ne', zero_mul]
      exact mul_nonneg (constant_pos _).le hε
    have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm)
    have hjp : (s.erase i).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hi, hs]; omega)
    obtain ⟨j, hj⟩ := hjp
    obtain ⟨hji, hjs⟩ := Finset.mem_erase.mp hj
    let Bad := {y | ‖χ i y - χ j y‖ < m / 4}
    have hBad : MeasurableSet Bad :=
      measurableSet_lt ((hmeas i).sub (hmeas j)).norm measurable_const
    obtain ⟨y, hy, hyMass⟩ := exists_shift μ (measurable_sublevel χ hmeas s a ε) hBad hmpos
      (hphase hji.symm (m / 4) (by positivity))
    have hyPhase : m / 4 ≤ ‖χ i y - χ j y‖ := le_of_not_gt hy
    let a' (l : ι) := a l * (χ l y - χ j y)
    let s' := s.erase j
    have hs' : s'.card = k + 1 := by
      rw [Finset.card_erase_of_mem hjs, hs]
      omega
    have hi' : i ∈ s' := Finset.mem_erase.mpr ⟨hji.symm, hi⟩
    have hfunc (x : G) : (∑ l ∈ s', a' l * χ l x) =
        (∑ l ∈ s, a l * χ l (x + y)) - χ j y * (∑ l ∈ s, a l * χ l x) := by
      have hz : a' j * χ j x = 0 := by simp [a']
      have hall := Finset.sum_erase_add s (fun l => a' l * χ l x) hjs
      rw [hz, add_zero] at hall
      rw [hall, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by rw [hadd]; dsimp only [a']; ring
    have hsub : E ∩ (fun x => x + y) ⁻¹' E ⊆ sublevel χ s' a' (2 * ε) := by
      intro x hx
      obtain ⟨h1, h2⟩ := hx
      change ‖∑ l ∈ s, a l * χ l x‖ ≤ ε at h1
      change ‖∑ l ∈ s, a l * χ l (x + y)‖ ≤ ε at h2
      change ‖∑ l ∈ s', a' l * χ l x‖ ≤ 2 * ε
      rw [hfunc]
      have h := norm_sub_le (∑ l ∈ s, a l * χ l (x + y)) (χ j y * (∑ l ∈ s, a l * χ l x))
      rw [norm_mul, hnorm, one_mul] at h
      linarith only [h, h1, h2]
    have hyMass' : m ^ 2 / 2 ≤ μ.real (sublevel χ s' a' (2 * ε)) :=
      hyMass.trans (measureReal_mono hsub)
    have ha' : m / 4 * ‖a i‖ ≤ ‖a' i‖ := by
      rw [show ‖a' i‖ = ‖a i‖ * ‖χ i y - χ j y‖ by exact norm_mul _ _, mul_comm ‖a i‖]
      exact mul_le_mul_of_nonneg_right hyPhase (norm_nonneg _)
    have hpow : (m ^ 2 / 2) ^ exponent k ≤
        (μ.real (sublevel χ s' a' (2 * ε))) ^ exponent k :=
      pow_le_pow_left₀ (by positivity) hyMass' _
    have hEstimate : (m ^ 2 / 2) ^ exponent k * (m / 4 * ‖a i‖) ≤ constant k * (2 * ε) :=
      (mul_le_mul hpow ha' (by positivity) (by positivity)).trans
        (ih s' hs' a' hi' (by positivity))
    have he : (m ^ 2 / 2) ^ exponent k * (m / 4 * ‖a i‖) =
        m ^ exponent (k + 1) * ‖a i‖ / (4 * 2 ^ exponent k) := by
      rw [exponent, div_pow, ← pow_mul, pow_succ]
      ring
    rw [he] at hEstimate
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * 2 ^ exponent k)).mp hEstimate
    change m ^ exponent (k + 1) * ‖a i‖ ≤ constant (k + 1) * ε
    rw [constant]
    nlinarith only [h]

end Estimate

end LawtonSmallBall

namespace LawtonSmallBall

/-- The additive real torus, with normalized Haar measure in each coordinate. -/
abbrev Torus (n : ℕ) := Fin n → AddCircle (1 : ℝ)

local instance positiveUnitPeriod : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

local instance probabilityUnitCircle : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by rw [AddCircle.measure_univ]; norm_num⟩

local instance probabilityTorus (n : ℕ) : IsProbabilityMeasure (volume : Measure (Torus n)) := by
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin n => (volume : Measure (AddCircle (1 : ℝ)))))
  infer_instance

/-- The additive map associated to an integer frequency vector. -/
def dot {n : ℕ} (k : Fin n → ℤ) : Torus n →+ AddCircle (1 : ℝ) where
  toFun x := ∑ j, k j • x j
  map_zero' := by simp
  map_add' := by simp [Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem continuous_dot {n : ℕ} (k : Fin n → ℤ) : Continuous (dot k) := by
  change Continuous (fun x : Torus n => ∑ j, k j • x j)
  fun_prop

private lemma dot_sub {n : ℕ} (k l : Fin n → ℤ) (x : Torus n) :
    dot (k - l) x = dot k x - dot l x := by
  change (∑ j, (k j - l j) • x j) = (∑ j, k j • x j) - ∑ j, l j • x j
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => by
    simpa only [sub_eq_add_neg] using (sub_zsmul (x j) (k j) (l j)))

private lemma zsmul_surjective {k : ℤ} (hk : k ≠ 0) :
    Function.Surjective (fun x : AddCircle (1 : ℝ) => k • x) := by
  intro y
  let r : ℝ := (AddCircle.equivIoc 1 0 y : Set.Ioc (0 : ℝ) (0 + 1)).val
  have hr : (r : AddCircle (1 : ℝ)) = y := AddCircle.coe_equivIoc (p := 1) (a := 0)
  refine ⟨((r / (k : ℝ) : ℝ) : AddCircle (1 : ℝ)), ?_⟩
  rw [← hr]
  change k • ((r / (k : ℝ) : ℝ) : AddCircle (1 : ℝ)) = _
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  congr 1
  exact mul_div_cancel₀ _ (by exact_mod_cast hk)

private lemma dot_surjective {n : ℕ} {k : Fin n → ℤ} (hk : k ≠ 0) :
    Function.Surjective (dot k) := by
  classical
  have h : ∃ j, k j ≠ 0 := by
    by_contra! ha
    exact hk (funext ha)
  obtain ⟨j, hj⟩ := h
  intro y
  obtain ⟨u, hu⟩ := zsmul_surjective hj y
  refine ⟨Function.update (0 : Torus n) j u, ?_⟩
  change (∑ i : Fin n, k i • Function.update (0 : Torus n) j u i) = y
  rw [Finset.sum_eq_single j]
  · simpa using hu
  · intro i _ hi
    simp only [Function.update_of_ne hi, Pi.zero_apply, smul_zero]
  · simp

theorem dot_measurePreserving {n : ℕ} {k : Fin n → ℤ} (hk : k ≠ 0) :
    MeasurePreserving (dot k) (volume : Measure (Torus n)) (volume : Measure (AddCircle (1 : ℝ))) :=
  AddMonoidHom.measurePreserving (continuous_dot k) (dot_surjective hk) (by simp only [measure_univ])

private noncomputable def circlePhase (x : AddCircle (1 : ℝ)) : ℂ := AddCircle.toCircle x

private lemma circlePhase_add (x y : AddCircle (1 : ℝ)) :
    circlePhase (x + y) = circlePhase x * circlePhase y := by
  simp only [circlePhase, AddCircle.toCircle_add, Circle.coe_mul]

private lemma circlePhase_norm (x : AddCircle (1 : ℝ)) : ‖circlePhase x‖ = 1 :=
  Circle.norm_coe _

private lemma norm_circlePhase_sub (x y : AddCircle (1 : ℝ)) :
    ‖circlePhase x - circlePhase y‖ = ‖circlePhase (x - y) - 1‖ := by
  have h : circlePhase x - circlePhase y = (circlePhase (x - y) - 1) * circlePhase y := by
    rw [sub_mul, one_mul, ← circlePhase_add, sub_add_cancel]
  rw [h, norm_mul, circlePhase_norm, mul_one]

private lemma four_mul_norm_le_chord (u : AddCircle (1 : ℝ)) :
    4 * ‖u‖ ≤ ‖circlePhase u - 1‖ := by
  let r := AddCircle.equivIoc 1 (-(1 / 2 : ℝ)) u
  have hr : ((r.val : ℝ) : AddCircle (1 : ℝ)) = u :=
    AddCircle.coe_equivIoc (p := 1) (a := -(1 / 2 : ℝ))
  have hb : |r.val| ≤ 1 / 2 := by
    exact abs_le.mpr ⟨r.property.1.le, by linarith [r.property.2]⟩
  have hn : ‖u‖ = |r.val| := by
    rw [← hr]
    exact (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr (by simpa using hb)
  have hc : circlePhase u = Complex.exp (Complex.I * ((2 * Real.pi * r.val : ℝ) : ℂ)) := by
    rw [← hr, circlePhase, AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one, mul_comm]
  rw [hc, Complex.norm_exp_I_mul_ofReal_sub_one, hn, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hh : |Real.pi * r.val| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    exact (mul_le_mul_of_nonneg_left hb Real.pi_pos.le).trans_eq (by ring)
  have hsin := Real.mul_abs_le_abs_sin hh
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  have he : 2 / Real.pi * (Real.pi * |r.val|) = 2 * |r.val| := by
    field_simp [Real.pi_pos.ne']
  rw [he] at hsin
  rw [show 2 * Real.pi * r.val / 2 = Real.pi * r.val by ring]
  linarith only [hsin]

/-- The unit-valued torus character associated to an integer frequency vector. -/
noncomputable def torusChar {n : ℕ} (k : Fin n → ℤ) (x : Torus n) : ℂ :=
  circlePhase (dot k x)

theorem continuous_torusChar {n : ℕ} (k : Fin n → ℤ) : Continuous (torusChar k) :=
  (continuous_subtype_val.comp AddCircle.continuous_toCircle).comp (continuous_dot k)

theorem torusChar_add {n : ℕ} (k : Fin n → ℤ) (x y : Torus n) :
    torusChar k (x + y) = torusChar k x * torusChar k y := by
  simp only [torusChar, map_add, circlePhase_add]

theorem torusChar_norm {n : ℕ} (k : Fin n → ℤ) (x : Torus n) :
    ‖torusChar k x‖ = 1 := circlePhase_norm _

theorem torusChar_eq_mFourier {n : ℕ} (k : Fin n → ℤ) (x : Torus n) :
    torusChar k x = UnitAddTorus.mFourier k x := by
  classical
  change circlePhase (∑ j, k j • x j) = ∏ j, circlePhase (k j • x j)
  have h (s : Finset (Fin n)) :
      circlePhase (∑ j ∈ s, k j • x j) = ∏ j ∈ s, circlePhase (k j • x j) := by
    induction s using Finset.induction_on with
    | empty => simp [circlePhase]
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.prod_insert hj, circlePhase_add, ih]
  exact h Finset.univ

theorem torusChar_specialize {n : ℕ} (k r : Fin n → ℤ) (x : AddCircle (1 : ℝ)) :
    torusChar k (fun j => r j • x) = fourier (∑ j, k j * r j) x := by
  change circlePhase (∑ j, k j • (r j • x)) = circlePhase ((∑ j, k j * r j) • x)
  congr 1
  simp only [Finset.sum_smul, mul_smul]

private lemma chord_measure_le {G : Type*} [MeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasure μ] {f : G → AddCircle (1 : ℝ)}
    (hf : MeasurePreserving f μ volume) (δ : ℝ) (hδ : 0 ≤ δ) :
    μ.real {x | ‖circlePhase (f x) - 1‖ < δ} ≤ δ := by
  let B : Set (AddCircle (1 : ℝ)) := Metric.closedBall 0 (δ / 4)
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hm := hf.measure_preimage hB.nullMeasurableSet
  have hsub : {x | ‖circlePhase (f x) - 1‖ < δ} ⊆ f ⁻¹' B := by
    intro x hx
    change ‖circlePhase (f x) - 1‖ < δ at hx
    have h := (four_mul_norm_le_chord (f x)).trans_lt hx
    change dist (f x) 0 ≤ δ / 4
    rw [dist_zero_right]
    linarith only [h]
  have hb : (volume : Measure (AddCircle (1 : ℝ))).real B ≤ δ := by
    rw [Measure.real, AddCircle.volume_closedBall, ENNReal.toReal_ofReal (le_min zero_le_one (by positivity))]
    exact (min_le_right _ _).trans (by linarith)
  have h := measureReal_mono (μ := μ) hsub
  change (μ {x | ‖circlePhase (f x) - 1‖ < δ}).toReal ≤ (μ (f ⁻¹' B)).toReal at h
  rw [hm] at h
  exact h.trans hb

theorem phase_bound {n : ℕ} {k l : Fin n → ℤ} (hkl : k ≠ l) (δ : ℝ) (hδ : 0 ≤ δ) :
    (volume : Measure (Torus n)).real {x | ‖torusChar k x - torusChar l x‖ < δ} ≤ δ := by
  have he : {x | ‖torusChar k x - torusChar l x‖ < δ} =
      {x | ‖circlePhase (dot (k - l) x) - 1‖ < δ} := by
    ext x
    change ‖circlePhase (dot k x) - circlePhase (dot l x)‖ < δ ↔
      ‖circlePhase (dot (k - l) x) - 1‖ < δ
    rw [norm_circlePhase_sub, ← dot_sub]
  rw [he]
  exact chord_measure_le volume (dot_measurePreserving (sub_ne_zero.mpr hkl)) δ hδ

/-- Uniform power bound for finite sums of distinct integer characters of the torus. -/
theorem torus_bound {n : ℕ} {ι : Type*} (freq : ι → Fin n → ℤ) (hf : Function.Injective freq)
    (k : ℕ) (s : Finset ι) (hs : s.card = k + 1) (a : ι → ℂ) {i : ι} (hi : i ∈ s)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ((volume : Measure (Torus n)).real (sublevel (fun j => torusChar (freq j)) s a ε)) ^ exponent k *
      ‖a i‖ ≤ constant k * ε :=
  bound volume (fun j => torusChar (freq j))
    (fun j => (continuous_torusChar (freq j)).measurable)
    (fun j => torusChar_add (freq j))
    (fun j => torusChar_norm (freq j))
    (fun h => phase_bound (fun e => h (hf e))) k s hs a hi hε

private lemma zsmul_measurePreserving {k : ℤ} (hk : k ≠ 0) :
    MeasurePreserving (fun x : AddCircle (1 : ℝ) => k • x) volume volume := by
  let f : AddCircle (1 : ℝ) →+ AddCircle (1 : ℝ) :=
    { toFun := fun x => k • x, map_zero' := smul_zero _, map_add' := smul_add _ }
  exact AddMonoidHom.measurePreserving (f := f)
    (continuous_zsmul k) (zsmul_surjective hk) rfl

private lemma fourier_phase_bound {k l : ℤ} (hkl : k ≠ l) (δ : ℝ) (hδ : 0 ≤ δ) :
    (volume : Measure (AddCircle (1 : ℝ))).real {x | ‖fourier k x - fourier l x‖ < δ} ≤ δ := by
  have he : {x : AddCircle (1 : ℝ) | ‖fourier k x - fourier l x‖ < δ} =
      {x | ‖circlePhase ((k - l) • x) - 1‖ < δ} := by
    ext x
    change ‖circlePhase (k • x) - circlePhase (l • x)‖ < δ ↔
      ‖circlePhase ((k - l) • x) - 1‖ < δ
    have hz : (k - l) • x = k • x - l • x := by
      simpa only [sub_eq_add_neg] using (sub_zsmul x k l)
    rw [norm_circlePhase_sub, hz]
  rw [he]
  exact chord_measure_le volume (zsmul_measurePreserving (sub_ne_zero.mpr hkl)) δ hδ

/-- One-dimensional version on the additive unit circle, using its Fourier monomials. -/
theorem circle_bound {ι : Type*} (freq : ι → ℤ) (hf : Function.Injective freq)
    (k : ℕ) (s : Finset ι) (hs : s.card = k + 1) (a : ι → ℂ) {i : ι} (hi : i ∈ s)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ((volume : Measure (AddCircle (1 : ℝ))).real (sublevel (fun j x => fourier (freq j) x) s a ε)) ^
      exponent k * ‖a i‖ ≤ constant k * ε := by
  apply bound volume (fun j x => fourier (freq j) x) _ _ _ _ k s hs a hi hε
  · exact fun j => (fourier (freq j)).continuous.measurable
  · intro j x y
    simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
  · exact fun j x => Circle.norm_coe _
  · exact fun h => fourier_phase_bound (fun e => h (hf e))

end LawtonSmallBall

/- Equidistribution of specializations that have no short integer relation. -/

noncomputable section

namespace LawtonEquidistribution

open MeasureTheory MultivariableMahlerMeasure UnitAddTorus Set
open scoped BigOperators

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def specialize {n : ℕ} (r : Fin n → ℤ) (z : UnitAddCircle) : UnitAddTorus (Fin n) :=
  fun i => r i • z

private theorem continuous_specialize {n : ℕ} (r : Fin n → ℤ) :
    Continuous (specialize r) :=
  continuous_pi (fun i => continuous_const_smul (r i))

private theorem fourier_specialize {n : ℕ} (r s : Fin n → ℤ) (z : UnitAddCircle) :
    mFourier s (specialize r z) = fourier (∑ i, s i * r i) z := by
  have hterm (i : Fin n) : fourier (s i) (specialize r z i) = fourier (s i * r i) z := by
    simp only [fourier_apply, specialize, mul_smul]
  simp only [mFourier, ContinuousMap.coe_mk, hterm]
  induction (Finset.univ : Finset (Fin n)) using Finset.induction with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, fourier_zero]
  | @insert i A hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, fourier_add, ih]

private theorem integral_fourier (s : ℤ) :
    (∫ z : UnitAddCircle, fourier s z ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) = if s = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T := (1 : ℝ)))) 0 s
  simpa only [ContinuousMap.inner_toLp, ← fourier_neg, ← fourier_add, neg_zero,
    add_zero, eq_comm] using h.symm

private theorem integral_mFourier {n : ℕ} (s : Fin n → ℤ) :
    (∫ z : UnitAddTorus (Fin n), mFourier s z) = if s = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := Fin n))) 0 s
  simpa only [ContinuousMap.inner_toLp, ← mFourier_neg, ← mFourier_add, neg_zero,
    add_zero, eq_comm] using h.symm

private theorem noShort_mono {n B C : ℕ} {r : Fin n → ℤ}
    (hBC : B ≤ C) (h : HasNoShortRelation C r) : HasNoShortRelation B r := by
  intro s hs hsr
  obtain ⟨i, hi⟩ := h s hs hsr
  exact ⟨i, (by exact_mod_cast hBC : (B : ℤ) ≤ C).trans_lt hi⟩

private theorem eventually_equal_monomial {n : ℕ} (s : Fin n → ℤ) :
    ∃ B : ℕ, ∀ r : Fin n → ℤ, HasNoShortRelation B r →
      (∫ z : UnitAddCircle, mFourier s (specialize r z) ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) =
        ∫ z : UnitAddTorus (Fin n), mFourier s z := by
  classical
  refine ⟨Finset.univ.sup (fun i => (s i).natAbs), fun r hr => ?_⟩
  simp_rw [fourier_specialize, integral_fourier, integral_mFourier]
  by_cases hs : s = 0
  · simp [hs]
  · have hh : ∑ i, s i * r i ≠ 0 := by
      intro h
      obtain ⟨i, hi⟩ := hr s hs h
      have hk : (s i).natAbs ≤ Finset.univ.sup (fun i => (s i).natAbs) :=
        Finset.le_sup (f := fun j => (s j).natAbs) (Finset.mem_univ i)
      rw [← Int.natCast_natAbs] at hi
      exact (not_lt_of_ge (by exact_mod_cast hk)) hi
    simp only [hs, hh, if_false]

private theorem eventually_equal_span {n : ℕ} {f : C(UnitAddTorus (Fin n), ℂ)}
    (hf : f ∈ Submodule.span ℂ (range (mFourier (d := Fin n)))) :
    ∃ B : ℕ, ∀ r : Fin n → ℤ, HasNoShortRelation B r →
      (∫ z : UnitAddCircle, f (specialize r z) ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) =
        ∫ z : UnitAddTorus (Fin n), f z := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨s, rfl⟩ := hg
      exact eventually_equal_monomial s
  | zero => exact ⟨0, fun _ _ => by simp⟩
  | add f g _ _ ihf ihg =>
      obtain ⟨B, hB⟩ := ihf
      obtain ⟨C, hC⟩ := ihg
      refine ⟨max B C, fun r hr => ?_⟩
      have hfr := (f.continuous.comp (continuous_specialize r)).integrable_of_hasCompactSupport
        (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle))
        (HasCompactSupport.of_compactSpace _)
      have hgr := (g.continuous.comp (continuous_specialize r)).integrable_of_hasCompactSupport
        (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle))
        (HasCompactSupport.of_compactSpace _)
      have hft := f.continuous.integrable_of_hasCompactSupport (μ := volume) (HasCompactSupport.of_compactSpace _)
      have hgt := g.continuous.integrable_of_hasCompactSupport (μ := volume) (HasCompactSupport.of_compactSpace _)
      simp only [Function.comp_def] at hfr hgr
      simp only [ContinuousMap.add_apply]
      rw [integral_add hfr hgr, integral_add hft hgt, hB r (noShort_mono (le_max_left B C) hr),
        hC r (noShort_mono (le_max_right B C) hr)]
  | smul a f _ ih =>
      obtain ⟨B, hB⟩ := ih
      refine ⟨B, fun r hr => ?_⟩
      simp only [ContinuousMap.smul_apply, integral_smul, hB r hr]

private theorem integral_norm_sub_le {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    [TopologicalSpace Y] [CompactSpace Y] (f g : C(Y, ℂ)) {p : X → Y} (hp : Continuous p) :
    ‖(∫ x, f (p x) ∂μ) - (∫ x, g (p x) ∂μ)‖ ≤ ‖f - g‖ := by
  have hf := (f.continuous.comp hp).integrable_of_hasCompactSupport (μ := μ)
    (HasCompactSupport.of_compactSpace _)
  have hg := (g.continuous.comp hp).integrable_of_hasCompactSupport (μ := μ)
    (HasCompactSupport.of_compactSpace _)
  simp only [Function.comp_def] at hf hg
  rw [← integral_sub hf hg]
  simpa only [ContinuousMap.sub_apply, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ)
      (ae_of_all _ fun x => (f - g).norm_coe_le_norm (p x)))

theorem continuous_integral_limit {n : ℕ} (f : C(UnitAddTorus (Fin n), ℂ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, ∀ r : Fin n → ℤ, HasNoShortRelation B r →
      ‖(∫ z : UnitAddCircle, f (specialize r z) ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) -
        (∫ z : UnitAddTorus (Fin n), f z)‖ < ε := by
  let S := Submodule.span ℂ (range (mFourier (d := Fin n)))
  have hcl : f ∈ closure (S : Set C(UnitAddTorus (Fin n), ℂ)) := by
    change f ∈ S.topologicalClosure
    rw [span_mFourier_closure_eq_top]
    exact Submodule.mem_top
  obtain ⟨g, hgS, hgf⟩ := Metric.mem_closure_iff.mp hcl (ε / 2) (by positivity)
  have hfg : ‖f - g‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hgf
  obtain ⟨B, hB⟩ := eventually_equal_span hgS
  refine ⟨B, fun r hr => ?_⟩
  let u := ∫ z : UnitAddCircle, f (specialize r z) ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)
  let v := ∫ z : UnitAddTorus (Fin n), g z
  let w := ∫ z : UnitAddTorus (Fin n), f z
  have huv : ‖u - v‖ ≤ ‖f - g‖ := by
    dsimp only [u, v]
    rw [← hB r hr]
    exact integral_norm_sub_le f g (continuous_specialize r)
  have hwv : ‖w - v‖ ≤ ‖f - g‖ := integral_norm_sub_le f g continuous_id
  change ‖u - w‖ < ε
  calc
    ‖u - w‖ = ‖(u - v) + -(w - v)‖ := by congr 1; abel
    _ ≤ ‖u - v‖ + ‖-(w - v)‖ := norm_add_le _ _
    _ < ε := by rw [norm_neg]; linarith

end LawtonEquidistribution

/- The error from truncating a logarithm under exponential sublevel estimates. -/

noncomputable section

open Set Filter MeasureTheory Real
open scoped ENNReal Topology

namespace LawtonLogTail

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private def tail (L : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  max 0 (-L - Real.log (f x))

private theorem exponential_integral {a C L : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => C * Real.exp (-a * (L + t))) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, C * Real.exp (-a * (L + t))) = C * Real.exp (-a * L) / a := by
  have hid (t : ℝ) : C * Real.exp (-a * (L + t)) =
      (C * Real.exp (-a * L)) * Real.exp (-(a * t)) := by
    rw [show -a * (L + t) = -a * L + -(a * t) by ring, Real.exp_add, mul_assoc]
  simp_rw [hid]
  constructor
  · refine Integrable.const_mul ?_ _
    exact (integrableOn_Ioi_comp_mul_left_iff (fun x => Real.exp (-x)) 0 ha).mpr
      (integrableOn_exp_neg_Ioi _)
  · rw [integral_const_mul, integral_comp_mul_left_Ioi (fun t => Real.exp (-t)) 0 ha,
      mul_zero, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one, div_eq_mul_inv]

private theorem tail_bound {f : X → ℝ} (hf : Measurable f) {a C L : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hsub : ∀ s : ℝ, 0 ≤ s →
      μ {x | f x < Real.exp (-s)} ≤ ENNReal.ofReal (C * Real.exp (-a * s))) :
    Integrable (tail L f) μ ∧ (∫ x, tail L f x ∂μ) ≤ C * Real.exp (-a * L) / a := by
  have hm : Measurable (tail L f) := measurable_const.max
    (measurable_const.sub (Real.measurable_log.comp hf))
  have hn : 0 ≤ᵐ[μ] tail L f := ae_of_all _ fun _ => le_max_left _ _
  have hPoint (t : ℝ) (ht : 0 < t) :
      μ {x | t < tail L f x} ≤ ENNReal.ofReal (C * Real.exp (-a * (L + t))) := by
    refine le_trans (measure_mono ?_) (hsub (L + t) (by positivity))
    intro x hx
    change t < max 0 (-L - Real.log (f x)) at hx
    have hlog : Real.log (f x) < -(L + t) := by
      rcases lt_max_iff.mp hx with hx | hx
      · linarith
      · linarith
    by_cases hp : 0 < f x
    · exact (Real.log_lt_iff_lt_exp hp).mp hlog
    · exact (le_of_not_gt hp).trans_lt (Real.exp_pos _)
  have hExp := exponential_integral (C := C) (L := L) ha
  have hExpNonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t => C * Real.exp (-a * (L + t)) := ae_of_all _ fun _ => by positivity
  have hBound :
      (∫⁻ x, ENNReal.ofReal (tail L f x) ∂μ) ≤
        ENNReal.ofReal (C * Real.exp (-a * L) / a) := by
    rw [lintegral_eq_lintegral_meas_lt μ hn hm.aemeasurable, ← hExp.2,
      ofReal_integral_eq_lintegral_ofReal hExp.1 hExpNonneg]
    exact setLIntegral_mono' measurableSet_Ioi (fun t ht => hPoint t ht)
  have hInt : Integrable (tail L f) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hn).mp
      (ne_of_lt (lt_of_le_of_lt hBound ENNReal.ofReal_lt_top))
  refine ⟨hInt, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hBound

variable [IsFiniteMeasure μ]

private theorem ae_pos {f : X → ℝ} {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hsub : ∀ s : ℝ, 0 ≤ s →
      μ {x | f x < Real.exp (-s)} ≤ ENNReal.ofReal (C * Real.exp (-a * s))) :
    ∀ᵐ x ∂μ, 0 < f x := by
  rw [ae_iff]
  let s : Set X := {x | ¬0 < f x}
  have hle (t : ℝ) (ht : 0 ≤ t) : μ s ≤ ENNReal.ofReal (C * Real.exp (-a * t)) :=
    (measure_mono (fun x hx => (le_of_not_gt hx).trans_lt (Real.exp_pos _))).trans (hsub t ht)
  have hlim : Tendsto (fun t : ℝ => C * Real.exp (-a * t)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_const_mul_atTop_of_pos ha).mpr tendsto_id)
    simpa only [Function.comp_apply, id_eq, neg_mul, mul_zero] using h.const_mul C
  have hev : ∀ᶠ t : ℝ in atTop, μ.real s ≤ C * Real.exp (-a * t) :=
    (eventually_ge_atTop 0).mono (fun t ht =>
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC (Real.exp_pos _).le) (hle t ht))
  have hr : μ.real s ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hev
  exact (measureReal_eq_zero_iff (measure_ne_top μ s)).mp (le_antisymm hr (by positivity))

theorem log_cutoff_error {f : X → ℝ} (hf : Measurable f) {a C L : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hsub : ∀ s : ℝ, 0 ≤ s →
      μ {x | f x < Real.exp (-s)} ≤ ENNReal.ofReal (C * Real.exp (-a * s)))
    (hcut : Integrable (fun x => Real.log (max (Real.exp (-L)) (f x))) μ) :
    Integrable (fun x => Real.log (f x)) μ ∧
      |(∫ x, Real.log (max (Real.exp (-L)) (f x)) ∂μ) - (∫ x, Real.log (f x) ∂μ)|
        ≤ C * Real.exp (-a * L) / a := by
  obtain ⟨hInt, hBound⟩ := tail_bound (μ := μ) hf ha hC hL hsub
  have hid : (fun x => Real.log (max (Real.exp (-L)) (f x))) =ᵐ[μ]
      fun x => Real.log (f x) + tail L f x := by
    filter_upwards [ae_pos ha hC hsub] with x hp
    unfold tail
    by_cases h : Real.exp (-L) ≤ f x
    · rw [max_eq_right h, max_eq_left, add_zero]
      have hh := Real.log_le_log (Real.exp_pos (-L)) h
      rw [Real.log_exp] at hh
      linarith
    · have h' := le_of_not_ge h
      rw [max_eq_left h', Real.log_exp, max_eq_right]
      · ring
      · have hh := Real.log_le_log hp h'
        rw [Real.log_exp] at hh
        linarith
  have hlog : Integrable (fun x => Real.log (f x)) μ := by
    apply (hcut.sub hInt).congr
    filter_upwards [hid] with x hx
    rw [Pi.sub_apply, hx]
    ring
  refine ⟨hlog, ?_⟩
  rw [integral_congr_ae hid, integral_add hlog hInt, add_sub_cancel_left,
    abs_of_nonneg (integral_nonneg fun _ => le_max_left _ _)]
  exact hBound

end LawtonLogTail

/- Polynomial evaluation and Fourier characters under torus specialization. -/

noncomputable section

namespace LawtonEvaluation

open MvPolynomial MeasureTheory MultivariableMahlerMeasure UnitAddTorus Set

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def evaluate {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (z : UnitAddTorus (Fin n)) : ℂ :=
  eval (fun i => fourier 1 (z i)) P

theorem continuous_evaluate {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    Continuous (evaluate P) :=
  (MvPolynomial.continuous_eval P).comp
    (continuous_pi (fun i => (fourier (T := (1 : ℝ)) 1).continuous.comp (continuous_apply i)))

def freq {n : ℕ} (m : Fin n →₀ ℕ) : Fin n → ℤ := fun i => (m i : ℤ)

theorem freq_injective (n : ℕ) : Function.Injective (freq (n := n)) := by
  intro a b h
  ext i
  have hv : (a i : ℤ) = (b i : ℤ) := congrFun h i
  exact_mod_cast hv

private theorem fourier_pow (k : ℕ) (z : UnitAddCircle) :
    fourier (k : ℤ) z = (fourier 1 z)^k := by
  induction k with
  | zero => simp only [Nat.cast_zero, fourier_zero, pow_zero]
  | succ k ih => rw [Nat.cast_succ, fourier_add, ih, pow_succ]

theorem eval_characters {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (z : UnitAddTorus (Fin n)) :
    evaluate P z = ∑ m ∈ P.support, P.coeff m * mFourier (freq m) z := by
  unfold evaluate
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mFourier, ContinuousMap.coe_mk, freq, fourier_pow]

theorem eval_coe {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (θ : Fin n → ℝ) :
    evaluate P (fun i => (θ i : UnitAddCircle)) = eval (torusPoint θ) P := by
  unfold evaluate
  congr 2
  ext i
  rw [fourier_coe_apply]
  simp only [Int.cast_one, mul_one, Complex.ofReal_one, div_one, torusPoint]
  congr 1
  ring

theorem coe_zsmul {n : ℕ} (r : Fin n → ℤ) (t : ℝ) (i : Fin n) :
    r i • (t : UnitAddCircle) = (((r i : ℝ) * t : ℝ) : UnitAddCircle) := by
  rw [← QuotientAddGroup.mk_zsmul, zsmul_eq_mul]

theorem specialization_injective {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    ∃ B : ℕ, ∀ r : Fin n → ℤ, HasNoShortRelation B r →
      Set.InjOn (fun m : Fin n →₀ ℕ => ∑ i, freq m i * r i) ↑P.support := by
  classical
  let B : ℕ := P.support.sup (fun m => Finset.univ.sup (fun i => m i))
  refine ⟨B, ?_⟩
  intro r hr m hm m' hm' hEq
  by_contra hNe
  let s : Fin n → ℤ := freq m - freq m'
  have hsn : s ≠ 0 := fun h => hNe (freq_injective n (sub_eq_zero.mp h))
  have hsr : ∑ i, s i * r i = 0 := by
    simp only [s, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hEq, sub_self]
  obtain ⟨i, hi⟩ := hr s hsn hsr
  have hUpper (u : Fin n →₀ ℕ) (hu : u ∈ P.support) : u i ≤ B := by
    apply le_trans (b := Finset.univ.sup (fun j => u j))
    · exact Finset.le_sup (f := fun j => u j) (Finset.mem_univ i)
    · exact Finset.le_sup (f := fun v => Finset.univ.sup (fun j => v j)) hu
  have hLeft : (m i : ℤ) ≤ (B : ℤ) := by exact_mod_cast hUpper m hm
  have hRight : (m' i : ℤ) ≤ (B : ℤ) := by exact_mod_cast hUpper m' hm'
  have hs : |s i| ≤ (B : ℤ) := by
    rw [abs_le]
    change -(B : ℤ) ≤ (m i : ℤ) - (m' i : ℤ) ∧ (m i : ℤ) - (m' i : ℤ) ≤ B
    have hmpos : 0 ≤ (m i : ℤ) := Int.natCast_nonneg _
    have hm'pos : 0 ≤ (m' i : ℤ) := Int.natCast_nonneg _
    omega
  exact (not_lt_of_ge hs) hi

theorem integral_cube {n : ℕ} (f : UnitAddTorus (Fin n) → ℝ) :
    (∫ θ in Icc (0 : Fin n → ℝ) 1, f (fun j => (θ j : UnitAddCircle))) =
      ∫ z : UnitAddTorus (Fin n), f z := by
  have h := UnitAddTorus.integral_preimage f (0 : Fin n → ℝ)
  simp only [Pi.zero_apply, zero_add] at h
  rw [volume_pi, ← setIntegral_congr_set Measure.univ_pi_Ioc_ae_eq_Icc, ← volume_pi]
  have hSet : univ.pi (fun i : Fin n => Ioc ((0 : Fin n → ℝ) i) ((1 : Fin n → ℝ) i)) =
      {x : Fin n → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} := by
    ext x
    simp only [mem_univ_pi, Pi.zero_apply, Pi.one_apply, Set.mem_ofPred_eq]
  simpa only [hSet] using h.symm

theorem integral_circle (f : UnitAddCircle → ℝ) :
    (∫ t in Icc (0 : ℝ) 1, f (t : UnitAddCircle)) =
      ∫ z : UnitAddCircle, f z ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  rw [← setIntegral_congr_set Ioc_ae_eq_Icc]
  have h := AddCircle.integral_preimage (1 : ℝ) 0 f
  simpa only [zero_add, AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul] using h

end LawtonEvaluation

namespace LawtonProof

open Filter MeasureTheory Set MultivariableMahlerMeasure LawtonEvaluation LawtonEquidistribution UnitAddTorus
open scoped ENNReal Topology

private theorem unit_haar_eq_volume :
    (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

private theorem torus_haar_eq_volume (n : ℕ) :
    (Measure.pi (fun _ : Fin n => (AddCircle.haarAddCircle : Measure UnitAddCircle))) =
      (volume : Measure (UnitAddTorus (Fin n))) := by
  rw [volume_pi]
  simp only [unit_haar_eq_volume]

private theorem exponential_of_power {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {U : Set X} {p : ℕ} (hp : 0 < p) {b K t : ℝ} (hb : 0 < b)
    (hK : 0 ≤ K) (h : μ.real U ^ p * b ≤ K * Real.exp (-t)) :
    μ U ≤ ENNReal.ofReal ((K / b) ^ (1 / (p : ℝ)) * Real.exp (-(1 / (p : ℝ)) * t)) := by
  have hpow : μ.real U ^ p ≤ (K / b) * Real.exp (-t) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hb]
    exact h
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hdiv : 0 ≤ K / b := div_nonneg hK hb.le
  apply (ENNReal.toReal_le_toReal (measure_ne_top μ U) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  calc
    μ.real U = (μ.real U ^ p) ^ (1 / (p : ℝ)) :=
      by simpa only [one_div] using (Real.pow_rpow_inv_natCast (x := μ.real U) (by positivity) hp.ne').symm
    _ ≤ ((K / b) * Real.exp (-t)) ^ (1 / (p : ℝ)) :=
      Real.rpow_le_rpow (by positivity) hpow (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hdiv (Real.exp_pos _).le, ← Real.exp_mul]
      congr 2
      ring

private theorem sublevel_bounds {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0) :
    ∃ (B : ℕ) (a C : ℝ), 0 < a ∧ 0 ≤ C ∧
      (∀ t : ℝ, 0 ≤ t → (volume : Measure (UnitAddTorus (Fin n)))
        {z | ‖evaluate P z‖ < Real.exp (-t)} ≤ ENNReal.ofReal (C * Real.exp (-a * t))) ∧
      ∀ r : Fin n → ℤ, HasNoShortRelation B r →
        ∀ t : ℝ, 0 ≤ t → (volume : Measure UnitAddCircle)
          {z | ‖evaluate P (specialize r z)‖ < Real.exp (-t)} ≤ ENNReal.ofReal (C * Real.exp (-a * t)) := by
  classical
  obtain ⟨B, hB⟩ := specialization_injective P
  have hs : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP
  obtain ⟨m, hm⟩ := hs
  let ι := ↥P.support
  let s : Finset ι := Finset.univ
  let coeff (i : ι) : ℂ := P.coeff i.val
  let i : ι := ⟨m, hm⟩
  let k := P.support.card - 1
  have hcard : s.card = k + 1 := by
    have hpos : 0 < P.support.card := Finset.card_pos.mpr ⟨m, hm⟩
    simpa only [s, ι, Finset.card_univ, Fintype.card_coe, k] using
      (Nat.sub_add_cancel (show 1 ≤ P.support.card from hpos)).symm
  have hcoeff : 0 < ‖coeff i‖ := norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp hm)
  let p := LawtonSmallBall.exponent k
  let K := LawtonSmallBall.constant k
  have hp : 0 < p := LawtonSmallBall.exponent_pos k
  have hK : 0 ≤ K := (LawtonSmallBall.constant_pos k).le
  have hsum (z : UnitAddTorus (Fin n)) :
      evaluate P z =
        ∑ j ∈ s, coeff j * LawtonSmallBall.torusChar (freq j.val) z := by
    rw [eval_characters, ← Finset.sum_attach P.support (fun m => P.coeff m * mFourier (freq m) z)]
    change (∑ j ∈ s, coeff j * mFourier (freq j.val) z) = _
    simp only [LawtonSmallBall.torusChar_eq_mFourier]
  have hFreq : Function.Injective (fun j : ι => freq j.val) :=
    (freq_injective n).comp Subtype.val_injective
  refine ⟨B, 1 / (p : ℝ), (K / ‖coeff i‖) ^ (1 / (p : ℝ)), by positivity,
    by positivity, ?_, ?_⟩
  · intro t _
    have hbound := LawtonSmallBall.torus_bound _ hFreq k s hcard coeff
      (Finset.mem_univ i) (Real.exp_pos (-t)).le
    refine (measure_mono ?_).trans (exponential_of_power hp hcoeff hK hbound)
    intro z hz
    change ‖∑ j ∈ s, coeff j * LawtonSmallBall.torusChar (freq j.val) z‖ ≤ Real.exp (-t)
    rw [← hsum]
    exact hz.le
  · intro r hr t _
    let fr (j : ι) : ℤ := ∑ l, freq j.val l * r l
    have hfr : Function.Injective fr := fun j j' hh =>
      Subtype.ext (hB r hr j.property j'.property hh)
    have hbound := LawtonSmallBall.circle_bound fr hfr k s hcard coeff
      (Finset.mem_univ i) (Real.exp_pos (-t)).le
    refine (measure_mono ?_).trans (exponential_of_power hp hcoeff hK hbound)
    intro z hz
    change ‖∑ j ∈ s, coeff j * fourier (fr j) z‖ ≤ Real.exp (-t)
    have hev : evaluate P (specialize r z) = ∑ j ∈ s, coeff j * fourier (fr j) z := by
      rw [hsum]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact LawtonSmallBall.torusChar_specialize (freq j.val) r z
    rw [← hev]
    exact (show ‖evaluate P (specialize r z)‖ < Real.exp (-t) from hz).le

private def cutoff {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (L : ℝ)
    (z : UnitAddTorus (Fin n)) : ℝ :=
  Real.log (max (Real.exp (-L)) ‖evaluate P z‖)

private theorem cutoff_continuous {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (L : ℝ) :
    Continuous (cutoff P L) := by
  apply (continuous_const.max (continuous_evaluate P).norm).log
  intro z
  exact ((Real.exp_pos (-L)).trans_le (le_max_left _ _)).ne'

private theorem cutoff_compare {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (L : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, ∀ r : Fin n → ℤ, HasNoShortRelation B r →
      |(∫ z : UnitAddCircle, cutoff P L (specialize r z)) -
        (∫ z : UnitAddTorus (Fin n), cutoff P L z)| < ε := by
  let g : C(UnitAddTorus (Fin n), ℂ) :=
    ⟨fun z => ((cutoff P L z) : ℂ), Complex.continuous_ofReal.comp (cutoff_continuous P L)⟩
  obtain ⟨B, hB⟩ := continuous_integral_limit g hε
  refine ⟨B, fun r hr => ?_⟩
  have h := hB r hr
  change ‖(∫ z : UnitAddCircle, ((cutoff P L (specialize r z)) : ℂ)
      ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) -
    (∫ z : UnitAddTorus (Fin n), ((cutoff P L z) : ℂ)
      ∂Measure.pi (fun _ : Fin n => (AddCircle.haarAddCircle : Measure UnitAddCircle)))‖ < ε at h
  rw [torus_haar_eq_volume, unit_haar_eq_volume] at h
  simpa only [integral_complex_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h

private theorem torus_log_eq {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.logMahlerMeasure P =
      ∫ z : UnitAddTorus (Fin n), Real.log ‖evaluate P z‖ := by
  unfold MvPolynomial.logMahlerMeasure
  simp_rw [← eval_coe]
  have h := integral_cube (fun z : UnitAddTorus (Fin n) => Real.log ‖evaluate P z‖)
  change _ = (∫ z : UnitAddTorus (Fin n), Real.log ‖evaluate P z‖
    ∂Measure.pi (fun _ : Fin n => (AddCircle.haarAddCircle : Measure UnitAddCircle))) at h
  rwa [torus_haar_eq_volume] at h

private theorem circle_log_eq {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (r : Fin n → ℤ) :
    univariateSpecLogMahler P r =
      ∫ z : UnitAddCircle, Real.log ‖evaluate P (specialize r z)‖ := by
  unfold univariateSpecLogMahler
  have h := integral_circle (fun z => Real.log ‖evaluate P (specialize r z)‖)
  rw [unit_haar_eq_volume] at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t _
  change Real.log ‖MvPolynomial.eval (MvPolynomial.torusPoint (fun j => (r j : ℝ) * t)) P‖ =
    Real.log ‖evaluate P (specialize r (t : UnitAddCircle))‖
  have he : specialize r (t : UnitAddCircle) = (fun j => ↑((r j : ℝ) * t)) :=
    funext (coe_zsmul r t)
  rw [he, eval_coe]

private theorem cutoff_error_tendsto_zero {a C : ℝ} (ha : 0 < a) :
    Tendsto (fun L : ℝ => C * Real.exp (-a * L) / a) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_const_mul_atTop_of_pos ha).mpr tendsto_id)
  simpa only [Function.comp_apply, id_eq, neg_mul, mul_zero, zero_div] using
    (h.const_mul C).div_const a

theorem solution {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℕ, ∀ r : Fin n → ℤ, HasNoShortRelation B r →
      |univariateSpecLogMahler P r - MvPolynomial.logMahlerMeasure P| < ε := by
  obtain ⟨B, a, C, ha, hC, htorus, hcircle⟩ := sublevel_bounds P hP
  have hlim := cutoff_error_tendsto_zero (C := C) ha
  have hsmall : ∀ᶠ L : ℝ in atTop, C * Real.exp (-a * L) / a < ε / 3 :=
    hlim.eventually (gt_mem_nhds (by positivity : 0 < ε / 3))
  obtain ⟨L, hL, hErr⟩ := ((eventually_ge_atTop 0).and hsmall).exists
  obtain ⟨B', hcut⟩ := cutoff_compare P L (show 0 < ε / 3 by positivity)
  refine ⟨max B B', fun r hr => ?_⟩
  have hR := hcircle r (noShort_mono (le_max_left B B') hr)
  have hClose := hcut r (noShort_mono (le_max_right B B') hr)
  have hcont := cutoff_continuous P L
  have hcutT := hcont.integrable_of_hasCompactSupport (μ := volume)
    (HasCompactSupport.of_compactSpace _)
  have hcutR := (hcont.comp (continuous_specialize r)).integrable_of_hasCompactSupport
    (μ := (volume : Measure UnitAddCircle)) (HasCompactSupport.of_compactSpace _)
  have hT := (LawtonLogTail.log_cutoff_error (continuous_evaluate P).norm.measurable
    ha hC hL htorus hcutT).2
  have hU := (LawtonLogTail.log_cutoff_error
    ((continuous_evaluate P).comp (continuous_specialize r)).norm.measurable
    ha hC hL hR hcutR).2
  let u := ∫ z : UnitAddCircle, Real.log ‖evaluate P (specialize r z)‖
  let v := ∫ z : UnitAddCircle, cutoff P L (specialize r z)
  let w := ∫ z : UnitAddTorus (Fin n), cutoff P L z
  let q := ∫ z : UnitAddTorus (Fin n), Real.log ‖evaluate P z‖
  change |w - q| ≤ _ at hT
  change |v - u| ≤ _ at hU
  change |v - w| < _ at hClose
  rw [circle_log_eq, torus_log_eq]
  change |u - q| < ε
  calc
    |u - q| = |((u - v) + (v - w)) + (w - q)| := by congr 1; ring
    _ ≤ |u - v| + |v - w| + |w - q| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ < ε := by rw [abs_sub_comm u v]; linarith

end LawtonProof

theorem OMA.solution : type_of% @MultivariableMahlerMeasure.lawton_multivariable_mahler_measure_limit :=
  LawtonProof.solution