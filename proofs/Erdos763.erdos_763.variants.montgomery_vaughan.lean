import FormalConjectures.ErdosProblems.«763»
import Mathlib

/-!
# The sharp Erdős–Fuchs theorem

H. L. Montgomery and R. C. Vaughan, On the Erdős–Fuchs theorems,
A Tribute to Paul Erdős (1990), 331–338.
https://personal.science.psu.edu/rcv4/personal/Publications/EF90.pdf

We subtract the circle means at radii r and r². For the difference of the
pole terms we use the exact mean of the squared Cauchy kernel and the
radial variation of the geometric block. This removes the logarithmic loss.
The coefficients of that block times the indicator series are integers,
so their squares dominate them even after radial subtraction.

The circle Parseval identity and supporting convolution and block lemmas are
adapted from plby/lean-proofs, ErdosProblems/Erdos763.lean at commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Copyright 2026 The Formal
Conjectures Authors. Used under Apache-2.0. The source credits Codex and
GPT-5.6 Sol for the bounded-error formalization. The damped error and radial
difference estimates used here establish the stronger little-o conclusion.
-/

open Filter Metric Set
open scoped BigOperators Topology Asymptotics Real

namespace EF763

/-- The `ℕ`-valued indicator of a subset of the natural numbers. -/
noncomputable def indicator (A : Set ℕ) (n : ℕ) : ℕ :=
  open scoped Classical in
  if n ∈ A then 1 else 0

/-- The ordered representation function `(1_A * 1_A)(n)`. -/
noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (n + 1), indicator A a * indicator A (n - a)

/-- The summatory ordered representation function through `N`, inclusive. -/
noncomputable def summatoryRepresentationCount (A : Set ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), representationCount A n

@[simp] lemma indicator_eq_one_iff {A : Set ℕ} {n : ℕ} :
    indicator A n = 1 ↔ n ∈ A := by
  classical
  simp [indicator]

@[simp] lemma indicator_le_one (A : Set ℕ) (n : ℕ) : indicator A n ≤ 1 := by
  classical
  by_cases hn : n ∈ A <;> simp [indicator, hn]

@[simp] lemma norm_indicator_cast (A : Set ℕ) (n : ℕ) :
    ‖(indicator A n : ℂ)‖ = indicator A n := by
  classical
  by_cases hn : n ∈ A <;> simp [indicator, hn]

/- ## Bounded power series and Parseval on a circle -/

/-- The analytic function represented by a sequence of complex coefficients. -/
noncomputable def powerSeriesValue (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, a n * z ^ n

/-- The degree `< K` truncation of a coefficient sequence. -/
noncomputable def truncPolynomial (a : ℕ → ℂ) (r : ℝ) (K : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range K, Polynomial.monomial n (a n * (r : ℂ) ^ n)

lemma summable_norm_mul_pow_of_bounded {a : ℕ → ℂ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Summable fun n : ℕ ↦ ‖a n * ((r : ℂ) * z) ^ n‖ := by
  have hgeom : Summable fun n : ℕ ↦ C * r ^ n :=
    (summable_geometric_of_norm_lt_one (K := ℝ) (by simpa [abs_of_nonneg hr0])).mul_left C
  apply Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) _ hgeom
  intro n
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0]
  calc
    ‖a n‖ * (r * ‖z‖) ^ n ≤ C * (r * ‖z‖) ^ n := by
      exact mul_le_mul_of_nonneg_right (ha n)
        (pow_nonneg (mul_nonneg hr0 (norm_nonneg z)) n)
    _ ≤ C * r ^ n := by
      gcongr
      exact mul_le_of_le_one_right hr0 hz

lemma summable_mul_pow_of_bounded {a : ℕ → ℂ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Summable fun n : ℕ ↦ a n * ((r : ℂ) * z) ^ n :=
  (summable_norm_mul_pow_of_bounded hC hr0 hr1 ha z hz).of_norm

lemma truncPolynomial_eval (a : ℕ → ℂ) (r : ℝ) (K : ℕ) (z : ℂ) :
    (truncPolynomial a r K).eval z =
      ∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n := by
  rw [truncPolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Polynomial.eval_monomial, mul_pow]
  ring

lemma truncPolynomial_coeff (a : ℕ → ℂ) (r : ℝ) (K n : ℕ) :
    (truncPolynomial a r K).coeff n =
      if n < K then a n * (r : ℂ) ^ n else 0 := by
  simp [truncPolynomial, Polynomial.coeff_monomial, Finset.mem_range]

lemma truncPolynomial_support_subset (a : ℕ → ℂ) (r : ℝ) (K : ℕ) :
    (truncPolynomial a r K).support ⊆ Finset.range K := by
  intro n hn
  rw [Polynomial.mem_support_iff] at hn
  rw [Finset.mem_range]
  by_contra hnot
  apply hn
  rw [truncPolynomial_coeff]
  simp [hnot]

lemma truncPolynomial_parseval (a : ℕ → ℂ) {r : ℝ} (hr0 : 0 ≤ r) (K : ℕ) :
    ∑ n ∈ Finset.range K, ‖a n‖ ^ 2 * r ^ (2 * n) =
      Real.circleAverage
        (fun z : ℂ ↦ ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖ ^ 2) 0 1 := by
  let p := truncPolynomial a r K
  have havg :
      Real.circleAverage
          (fun z : ℂ ↦ ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖ ^ 2) 0 1 =
        Real.circleAverage (fun z : ℂ ↦ ‖p.eval z‖ ^ 2) 0 1 := by
    apply congrArg (fun f : ℂ → ℝ ↦ Real.circleAverage f 0 1)
    funext z
    dsimp only [p]
    rw [truncPolynomial_eval]
  rw [havg, ← p.sum_sq_norm_coeff_eq_circleAverage]
  have hsupp : p.support ⊆ Finset.range K := truncPolynomial_support_subset a r K
  rw [Finset.sum_subset hsupp]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [p, truncPolynomial_coeff, Finset.mem_range.mp hn, if_pos]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    ring
  · intro n hnrange hnsupp
    simp only [Polynomial.mem_support_iff, ne_eq, not_not] at hnsupp
    simp [hnsupp]

lemma powerSeriesValue_continuousOn_sphere {a : ℕ → ℂ} {C r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) :
    ContinuousOn (fun z : ℂ ↦ powerSeriesValue a ((r : ℂ) * z)) (sphere 0 1) := by
  apply continuousOn_tsum (u := fun n : ℕ ↦ C * r ^ n)
  · intro n
    fun_prop
  · exact (summable_geometric_of_norm_lt_one (K := ℝ)
      (by simpa [abs_of_nonneg hr0])).mul_left C
  · intro n z hz
    have hznorm : ‖z‖ = 1 := by simpa using hz
    simpa [powerSeriesValue, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0, hznorm] using
      mul_le_mul_of_nonneg_right (ha n) (pow_nonneg hr0 n)

lemma powerSeriesValue_trunc_error {a : ℕ → ℂ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) {z : ℂ} (hz : ‖z‖ ≤ 1) (K : ℕ) :
    ‖(∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n) -
        powerSeriesValue a ((r : ℂ) * z)‖ ≤ C * r ^ K / (1 - r) := by
  apply norm_sub_le_of_geometric_bound_of_hasSum hr1
      (f := fun n : ℕ ↦ a n * ((r : ℂ) * z) ^ n) ?_
      ((summable_mul_pow_of_bounded hC hr0 hr1 ha z hz).hasSum)
  intro n
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0]
  calc
    ‖a n‖ * (r * ‖z‖) ^ n ≤ C * (r * ‖z‖) ^ n := by
      exact mul_le_mul_of_nonneg_right (ha n)
        (pow_nonneg (mul_nonneg hr0 (norm_nonneg z)) n)
    _ ≤ C * r ^ n := by
      gcongr
      exact mul_le_of_le_one_right hr0 hz

lemma powerSeriesValue_norm_le {a : ℕ → ℂ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖powerSeriesValue a ((r : ℂ) * z)‖ ≤ C / (1 - r) := by
  calc
    ‖powerSeriesValue a ((r : ℂ) * z)‖ ≤ ∑' n : ℕ, ‖a n * ((r : ℂ) * z) ^ n‖ :=
      norm_tsum_le_tsum_norm (summable_norm_mul_pow_of_bounded hC hr0 hr1 ha z hz)
    _ ≤ ∑' n : ℕ, C * r ^ n := by
      apply (summable_norm_mul_pow_of_bounded hC hr0 hr1 ha z hz).tsum_le_tsum
      · intro n
        rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hr0]
        calc
          ‖a n‖ * (r * ‖z‖) ^ n ≤ C * (r * ‖z‖) ^ n := by
            exact mul_le_mul_of_nonneg_right (ha n)
              (pow_nonneg (mul_nonneg hr0 (norm_nonneg z)) n)
          _ ≤ C * r ^ n := by
            gcongr
            exact mul_le_of_le_one_right hr0 hz
      · exact (summable_geometric_of_norm_lt_one (K := ℝ)
          (by simpa [abs_of_nonneg hr0])).mul_left C
    _ = C / (1 - r) := by
      rw [tsum_mul_left, (hasSum_geometric_of_norm_lt_one (K := ℝ)
        (by simpa [abs_of_nonneg hr0])).tsum_eq]
      field_simp

lemma truncValue_norm_le {a : ℕ → ℂ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) {z : ℂ} (hz : ‖z‖ ≤ 1) (K : ℕ) :
    ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖ ≤ C / (1 - r) := by
  calc
    ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖ ≤
        ∑ n ∈ Finset.range K, C * r ^ n := by
      refine (norm_sum_le _ _).trans ?_
      gcongr with n hn
      rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hr0]
      calc
        ‖a n‖ * (r * ‖z‖) ^ n ≤ C * (r * ‖z‖) ^ n := by
          exact mul_le_mul_of_nonneg_right (ha n)
            (pow_nonneg (mul_nonneg hr0 (norm_nonneg z)) n)
        _ ≤ C * r ^ n := by
          gcongr
          exact mul_le_of_le_one_right hr0 hz
    _ ≤ ∑' n : ℕ, C * r ^ n := by
      exact ((summable_geometric_of_norm_lt_one (K := ℝ)
        (by simpa [abs_of_nonneg hr0])).mul_left C).sum_le_tsum
          (Finset.range K) (fun _ _ ↦ mul_nonneg hC (pow_nonneg hr0 _))
    _ = C / (1 - r) := by
      rw [tsum_mul_left, (hasSum_geometric_of_norm_lt_one (K := ℝ)
        (by simpa [abs_of_nonneg hr0])).tsum_eq]
      field_simp

lemma abs_circleAverage_sub_le {f g : ℂ → ℝ} {R B : ℝ}
    (hR : 0 ≤ R) (hf : ContinuousOn f (sphere 0 R))
    (hg : ContinuousOn g (sphere 0 R))
    (hB : ∀ z ∈ sphere (0 : ℂ) R, |f z - g z| ≤ B) :
    |Real.circleAverage f 0 R - Real.circleAverage g 0 R| ≤ B := by
  have hfi := hf.circleIntegrable hR
  have hgi := hg.circleIntegrable hR
  rw [← Real.circleAverage_sub hfi hgi]
  calc
    |Real.circleAverage (f - g) 0 R| ≤
        Real.circleAverage (fun z ↦ |(f - g) z|) 0 R :=
      Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage (fun _ : ℂ ↦ B) 0 R := by
      apply Real.circleAverage_mono
      · exact (hf.sub hg).abs.circleIntegrable hR
      · exact continuousOn_const.circleIntegrable hR
      · intro z hz
        apply hB z
        simpa [abs_of_nonneg hR] using hz
    _ = B := Real.circleAverage_const B 0 R

lemma summable_sq_norm_mul_rpow {a : ℕ → ℂ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) :
    Summable fun n : ℕ ↦ ‖a n‖ ^ 2 * r ^ (2 * n) := by
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hgeom : Summable fun n : ℕ ↦ C ^ 2 * (r ^ 2) ^ n :=
    (summable_geometric_of_norm_lt_one (K := ℝ)
      (by simpa [abs_of_nonneg (sq_nonneg r)] using hr2)).mul_left (C ^ 2)
  apply Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (sq_nonneg _) (pow_nonneg hr0 _)) _ hgeom
  intro n
  have hsq : ‖a n‖ ^ 2 ≤ C ^ 2 := by
    nlinarith [ha n, norm_nonneg (a n)]
  calc
    ‖a n‖ ^ 2 * r ^ (2 * n) ≤ C ^ 2 * r ^ (2 * n) := by
      exact mul_le_mul_of_nonneg_right hsq (pow_nonneg hr0 _)
    _ = C ^ 2 * (r ^ 2) ^ n := by ring

lemma circleParseval_bounded {a : ℕ → ℂ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) :
    Real.circleAverage
        (fun z : ℂ ↦ ‖powerSeriesValue a ((r : ℂ) * z)‖ ^ 2) 0 1 =
      ∑' n : ℕ, ‖a n‖ ^ 2 * r ^ (2 * n) := by
  let S : ℂ → ℂ := fun z ↦ powerSeriesValue a ((r : ℂ) * z)
  let P : ℕ → ℂ → ℂ := fun K z ↦
    ∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n
  have hScont : ContinuousOn S (sphere 0 1) :=
    powerSeriesValue_continuousOn_sphere hr0 hr1 ha
  have hPcont (K : ℕ) : ContinuousOn (P K) (sphere 0 1) := by
    exact (by
      dsimp only [P]
      fun_prop : Continuous (P K)).continuousOn
  have hleft : Tendsto
      (fun K ↦ Real.circleAverage (fun z : ℂ ↦ ‖P K z‖ ^ 2) 0 1) atTop
      (𝓝 (Real.circleAverage (fun z : ℂ ↦ ‖S z‖ ^ 2) 0 1)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have herr : Tendsto
        (fun K : ℕ ↦ (C * r ^ K / (1 - r)) * (2 * (C / (1 - r)))) atTop (𝓝 0) := by
      have hp : Tendsto (fun K : ℕ ↦ r ^ K) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one
          (by simpa [abs_of_nonneg hr0])
      have hc : Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C) := tendsto_const_nhds
      have hp' : Tendsto (fun K : ℕ ↦ C * r ^ K / (1 - r)) atTop (𝓝 0) :=
        by simpa using (hc.mul hp).div_const (1 - r)
      simpa using hp'.mul_const (2 * (C / (1 - r)))
    exact squeeze_zero (g := fun K : ℕ ↦
      (C * r ^ K / (1 - r)) * (2 * (C / (1 - r))))
      (fun _ ↦ dist_nonneg) (fun K ↦ by
        rw [Real.dist_eq]
        apply abs_circleAverage_sub_le (R := (1 : ℝ)) (B :=
          (C * r ^ K / (1 - r)) * (2 * (C / (1 - r)))) zero_le_one
        · exact (hPcont K).norm.pow 2
        · exact hScont.norm.pow 2
        · intro z hz
          have hznorm : ‖z‖ ≤ 1 := le_of_eq (by simpa using hz)
          have htail := powerSeriesValue_trunc_error hC hr0 hr1 ha hznorm K
          have hPnorm := truncValue_norm_le hC hr0 hr1 ha hznorm K
          have hSnorm := powerSeriesValue_norm_le hC hr0 hr1 ha hznorm
          dsimp only [P, S]
          rw [abs_sub_comm]
          calc
            |‖powerSeriesValue a ((r : ℂ) * z)‖ ^ 2 -
                ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖ ^ 2| =
                |‖powerSeriesValue a ((r : ℂ) * z)‖ -
                  ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖| *
                (‖powerSeriesValue a ((r : ℂ) * z)‖ +
                  ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖) := by
              rw [sq_sub_sq, abs_mul,
                abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
              ring
            _ ≤ ‖powerSeriesValue a ((r : ℂ) * z) -
                  ∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖ *
                  (2 * (C / (1 - r))) := by
              apply mul_le_mul
              · exact abs_norm_sub_norm_le _ _
              · linarith
              · positivity
              · positivity
            _ ≤ (C * r ^ K / (1 - r)) * (2 * (C / (1 - r))) := by
              apply mul_le_mul_of_nonneg_right
              · simpa only [norm_sub_rev] using htail
              · positivity) herr
  have hright : Tendsto
      (fun K ↦ ∑ n ∈ Finset.range K, ‖a n‖ ^ 2 * r ^ (2 * n)) atTop
      (𝓝 (∑' n : ℕ, ‖a n‖ ^ 2 * r ^ (2 * n))) :=
    (summable_sq_norm_mul_rpow hC hr0 hr1 ha).hasSum.tendsto_sum_nat
  have hright' : Tendsto
      (fun K ↦ Real.circleAverage (fun z : ℂ ↦ ‖P K z‖ ^ 2) 0 1) atTop
      (𝓝 (∑' n : ℕ, ‖a n‖ ^ 2 * r ^ (2 * n))) := by
    apply hright.congr'
    filter_upwards [] with K
    exact truncPolynomial_parseval a hr0 K
  exact tendsto_nhds_unique hleft hright'

/- ## The convolution series and the bounded-error identity -/

/-- The complex-valued indicator coefficients. -/
noncomputable def indicatorComplex (A : Set ℕ) (n : ℕ) : ℂ := indicator A n

/-- The real error after normalizing the summatory function by `c (n + 1)`. -/
noncomputable def summatoryError (A : Set ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  summatoryRepresentationCount A n - c * (n + 1)

lemma indicatorComplex_norm_le_one (A : Set ℕ) (n : ℕ) :
    ‖indicatorComplex A n‖ ≤ 1 := by
  simp [indicatorComplex]

lemma summatoryRepresentationCount_succ (A : Set ℕ) (n : ℕ) :
    summatoryRepresentationCount A (n + 1) =
      summatoryRepresentationCount A n + representationCount A (n + 1) := by
  simp [summatoryRepresentationCount, Finset.sum_range_succ]

lemma representationCount_zero (A : Set ℕ) :
    representationCount A 0 = summatoryRepresentationCount A 0 := by
  simp [representationCount, summatoryRepresentationCount]

lemma representationCount_cast_complex (A : Set ℕ) (n : ℕ) :
    (representationCount A n : ℂ) =
      ∑ k ∈ Finset.range (n + 1),
        indicatorComplex A k * indicatorComplex A (n - k) := by
  simp [representationCount, indicatorComplex, Nat.cast_sum, Nat.cast_mul]

lemma representationCount_eq_error_difference (A : Set ℕ) (c : ℝ) :
    ∀ n : ℕ,
      (representationCount A n : ℝ) = c + summatoryError A c n -
        if n = 0 then 0 else summatoryError A c (n - 1) := by
  intro n
  cases n with
  | zero =>
      simp [summatoryError, representationCount_zero]
  | succ n =>
      rw [if_neg (Nat.succ_ne_zero n)]
      simp only [Nat.succ_sub_one]
      rw [summatoryError, summatoryError, summatoryRepresentationCount_succ]
      push_cast
      ring

lemma summable_norm_coeff_mul_pow {a : ℕ → ℂ} {D : ℝ} {z : ℂ}
    (ha : ∀ n, ‖a n‖ ≤ D) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ ↦ ‖a n * z ^ n‖ := by
  have hgeom : Summable fun n : ℕ ↦ D * ‖z‖ ^ n :=
    (summable_geometric_of_norm_lt_one (K := ℝ) (by simpa using hz)).mul_left D
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hgeom
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (norm_nonneg z) n)

lemma indicator_series_summable' (A : Set ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ ↦ ‖indicatorComplex A n * z ^ n‖ := by
  exact summable_norm_coeff_mul_pow (indicatorComplex_norm_le_one A) hz

lemma indicatorSeries_sq {A : Set ℕ} {z : ℂ} (hz : ‖z‖ < 1) :
    powerSeriesValue (indicatorComplex A) z ^ 2 =
      powerSeriesValue (fun n ↦ (representationCount A n : ℂ)) z := by
  have hs := indicator_series_summable' A hz
  rw [pow_two, powerSeriesValue,
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hs hs]
  apply tsum_congr
  intro n
  simp only [representationCount_cast_complex]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  calc
    indicatorComplex A k * z ^ k * (indicatorComplex A (n - k) * z ^ (n - k)) =
        indicatorComplex A k * indicatorComplex A (n - k) *
          (z ^ k * z ^ (n - k)) := by ring
    _ = indicatorComplex A k * indicatorComplex A (n - k) * z ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hkn]

/- ## A finite geometric block and its integer coefficients -/

/-- `1 + z + ⋯ + z^(M-1)`. -/
def geometricBlock (M : ℕ) (z : ℂ) : ℂ := ∑ k ∈ Finset.range M, z ^ k

/-- Coefficients of `geometricBlock M * indicatorSeries A`. -/
noncomputable def blockCoefficient (A : Set ℕ) (M n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range M, if k ≤ n then indicator A (n - k) else 0

lemma blockCoefficient_le (A : Set ℕ) (M n : ℕ) : blockCoefficient A M n ≤ M := by
  rw [blockCoefficient]
  calc
    (∑ k ∈ Finset.range M, if k ≤ n then indicator A (n - k) else 0) ≤
        ∑ _k ∈ Finset.range M, 1 := by
      gcongr with k hk
      split_ifs <;> simp
    _ = M := by simp

lemma cauchy_block_sum (A : Set ℕ) (M n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        (if k < M then 1 else 0) * indicator A (n - k)) = blockCoefficient A M n := by
  rw [blockCoefficient]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro k hk
    rfl

lemma block_sequence_summable_norm (M : ℕ) (z : ℂ) :
    Summable fun k : ℕ ↦ ‖((if k < M then 1 else 0 : ℕ) : ℂ) * z ^ k‖ := by
  apply summable_of_ne_finset_zero (s := Finset.range M)
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  simp [hk]

lemma block_sequence_tsum (M : ℕ) (z : ℂ) :
    (∑' k : ℕ, ((if k < M then 1 else 0 : ℕ) : ℂ) * z ^ k) = geometricBlock M z := by
  rw [tsum_eq_sum (s := Finset.range M)]
  · apply Finset.sum_congr rfl
    intro k hk
    simp [Finset.mem_range.mp hk]
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [hk]

lemma blockSeries_identity {A : Set ℕ} (M : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    geometricBlock M z * powerSeriesValue (indicatorComplex A) z =
      powerSeriesValue (fun n ↦ (blockCoefficient A M n : ℂ)) z := by
  have hBlock := block_sequence_summable_norm M z
  have hInd := indicator_series_summable' A hz
  rw [← block_sequence_tsum, powerSeriesValue,
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hBlock hInd]
  apply tsum_congr
  intro n
  have hcast : (blockCoefficient A M n : ℂ) =
      ∑ k ∈ Finset.range (n + 1),
        (((if k < M then 1 else 0 : ℕ) : ℂ) * indicatorComplex A (n - k)) := by
    simp [indicatorComplex]
    norm_cast
    simpa using (cauchy_block_sum A M n).symm
  change (∑ k ∈ Finset.range (n + 1),
      (((if k < M then 1 else 0 : ℕ) : ℂ) * z ^ k) *
        (indicatorComplex A (n - k) * z ^ (n - k))) =
    (blockCoefficient A M n : ℂ) * z ^ n
  rw [hcast, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  calc
    ((((if k < M then 1 else 0 : ℕ) : ℂ) * z ^ k) *
        (indicatorComplex A (n - k) * z ^ (n - k))) =
        (((if k < M then 1 else 0 : ℕ) : ℂ) * indicatorComplex A (n - k)) *
          (z ^ k * z ^ (n - k)) := by ring
    _ = (((if k < M then 1 else 0 : ℕ) : ℂ) * indicatorComplex A (n - k)) * z ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hkn]

lemma blockCoefficient_complex_norm_le (A : Set ℕ) (M n : ℕ) :
    ‖(blockCoefficient A M n : ℂ)‖ ≤ M := by
  simpa using blockCoefficient_le A M n

lemma block_parseval {A : Set ℕ} (M : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage
        (fun z : ℂ ↦ ‖geometricBlock M ((r : ℂ) * z) *
          powerSeriesValue (indicatorComplex A) ((r : ℂ) * z)‖ ^ 2) 0 1 =
      ∑' n : ℕ, (blockCoefficient A M n : ℝ) ^ 2 * r ^ (2 * n) := by
  have hparse := circleParseval_bounded (a := fun n ↦ (blockCoefficient A M n : ℂ))
    (C := (M : ℝ)) (r := r) (Nat.cast_nonneg M) hr0 hr1
    (blockCoefficient_complex_norm_le A M)
  have hparse' :
      Real.circleAverage
          (fun z : ℂ ↦ ‖powerSeriesValue (fun n ↦ (blockCoefficient A M n : ℂ))
            ((r : ℂ) * z)‖ ^ 2) 0 1 =
        ∑' n : ℕ, (blockCoefficient A M n : ℝ) ^ 2 * r ^ (2 * n) := by
    simpa using hparse
  rw [← hparse']
  apply Real.circleAverage_congr_sphere
  intro z hz
  have hznorm : ‖z‖ = 1 := by simpa using hz
  change ‖geometricBlock M ((r : ℂ) * z) *
      powerSeriesValue (indicatorComplex A) ((r : ℂ) * z)‖ ^ 2 =
    ‖powerSeriesValue (fun n ↦ (blockCoefficient A M n : ℂ)) ((r : ℂ) * z)‖ ^ 2
  rw [← blockSeries_identity M (by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hznorm]
    simpa using hr1)]

lemma blockCoefficient_real_series_identity {A : Set ℕ} (M : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n : ℕ, (blockCoefficient A M n : ℝ) * q ^ n) =
      (∑ k ∈ Finset.range M, q ^ k) *
        ∑' n : ℕ, (indicator A n : ℝ) * q ^ n := by
  have hBlock : Summable fun k : ℕ ↦
      ‖((if k < M then 1 else 0 : ℕ) : ℝ) * q ^ k‖ := by
    apply summable_of_ne_finset_zero (s := Finset.range M)
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [hk]
  have hInd : Summable fun n : ℕ ↦ ‖(indicator A n : ℝ) * q ^ n‖ := by
    have hgeom : Summable fun n : ℕ ↦ q ^ n :=
      summable_geometric_of_norm_lt_one (K := ℝ) (by
        simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)
    apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hgeom
    intro n
    rw [norm_mul, norm_pow]
    simp only [Real.norm_eq_abs, abs_of_nonneg hq0]
    have hind : ‖(indicator A n : ℝ)‖ ≤ 1 := by
      by_cases hn : n ∈ A <;> simp [indicator, hn]
    simpa using mul_le_mul_of_nonneg_right hind (pow_nonneg hq0 n)
  calc
    (∑' n : ℕ, (blockCoefficient A M n : ℝ) * q ^ n) =
        ∑' n : ℕ, ∑ k ∈ Finset.range (n + 1),
          (((if k < M then 1 else 0 : ℕ) : ℝ) * q ^ k) *
            ((indicator A (n - k) : ℝ) * q ^ (n - k)) := by
      apply tsum_congr
      intro n
      have hcast : (blockCoefficient A M n : ℝ) =
          ∑ k ∈ Finset.range (n + 1),
            (((if k < M then 1 else 0 : ℕ) : ℝ) * (indicator A (n - k) : ℝ)) := by
        norm_cast
        simpa using (cauchy_block_sum A M n).symm
      rw [hcast, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      push_cast
      have hp : q ^ k * q ^ (n - k) = q ^ n := by
        rw [← pow_add, Nat.add_sub_of_le hkn]
      rw [← hp]
      ring
    _ = (∑' k : ℕ, ((if k < M then 1 else 0 : ℕ) : ℝ) * q ^ k) *
        ∑' n : ℕ, (indicator A n : ℝ) * q ^ n :=
      (tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hBlock hInd).symm
    _ = (∑ k ∈ Finset.range M, q ^ k) *
        ∑' n : ℕ, (indicator A n : ℝ) * q ^ n := by
      congr 1
      rw [tsum_eq_sum (s := Finset.range M)]
      · apply Finset.sum_congr rfl
        intro k hk
        simp [Finset.mem_range.mp hk]
      · intro k hk
        simp only [Finset.mem_range, not_lt] at hk
        simp [hk]

lemma summable_real_coeff_mul_pow_of_bounded {a : ℕ → ℝ} {C q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (ha : ∀ n, |a n| ≤ C) :
    Summable fun n : ℕ ↦ a n * q ^ n := by
  have hgeom : Summable fun n : ℕ ↦ C * q ^ n :=
    (summable_geometric_of_norm_lt_one (K := ℝ) (by
      simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)).mul_left C
  have habs : Summable fun n : ℕ ↦ ‖a n * q ^ n‖ := by
    apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hgeom
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hq0]
    exact mul_le_mul_of_nonneg_right (ha n) (pow_nonneg hq0 n)
  exact habs.of_norm

lemma blockCoefficient_series_summable (A : Set ℕ) (M : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n : ℕ ↦ (blockCoefficient A M n : ℝ) * q ^ n := by
  apply summable_real_coeff_mul_pow_of_bounded (C := M) hq0 hq1
  intro n
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast blockCoefficient_le A M n

lemma blockCoefficient_sq_series_summable (A : Set ℕ) (M : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ ↦ (blockCoefficient A M n : ℝ) ^ 2 * r ^ (2 * n) := by
  simpa using summable_sq_norm_mul_rpow (a := fun n ↦ (blockCoefficient A M n : ℂ))
    (C := (M : ℝ)) (r := r) (Nat.cast_nonneg M) hr0 hr1
    (blockCoefficient_complex_norm_le A M)

lemma natCast_le_sq (n : ℕ) : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hn : n ≤ n * n := Nat.le_mul_self n
  exact_mod_cast (by simpa [pow_two] using hn)

lemma block_parseval_lower {A : Set ℕ} (M : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑ k ∈ Finset.range M, (r ^ 2) ^ k) *
        (∑' n : ℕ, (indicator A n : ℝ) * (r ^ 2) ^ n) ≤
      Real.circleAverage
        (fun z : ℂ ↦ ‖geometricBlock M ((r : ℂ) * z) *
          powerSeriesValue (indicatorComplex A) ((r : ℂ) * z)‖ ^ 2) 0 1 := by
  have hr2_0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hr2_1 : r ^ 2 < 1 := by nlinarith
  rw [block_parseval M hr0 hr1, ← blockCoefficient_real_series_identity M hr2_0 hr2_1]
  apply (blockCoefficient_series_summable A M hr2_0 hr2_1).tsum_le_tsum
  · intro n
    simpa [pow_mul] using
      mul_le_mul_of_nonneg_right (natCast_le_sq (blockCoefficient A M n))
        (pow_nonneg hr2_0 n)
  · exact blockCoefficient_sq_series_summable A M hr0 hr1

/-- The nonnegative real value of the indicator generating series on the real interval. -/
noncomputable def indicatorSeriesReal (A : Set ℕ) (q : ℝ) : ℝ :=
  ∑' n : ℕ, (indicator A n : ℝ) * q ^ n

lemma indicator_real_series_summable (A : Set ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n : ℕ ↦ (indicator A n : ℝ) * q ^ n := by
  apply summable_real_coeff_mul_pow_of_bounded (C := 1) hq0 hq1
  intro n
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast indicator_le_one A n

lemma indicatorSeriesReal_nonneg (A : Set ℕ) {q : ℝ} (hq0 : 0 ≤ q) :
    0 ≤ indicatorSeriesReal A q := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0 n)

lemma indicatorSeries_at_real {A : Set ℕ} {q : ℝ} :
    powerSeriesValue (indicatorComplex A) (q : ℂ) = indicatorSeriesReal A q := by
  rw [powerSeriesValue, indicatorSeriesReal]
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp [indicatorComplex]

lemma geometricBlock_norm_le (M : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖geometricBlock M w‖ ≤ M := by
  rw [geometricBlock]
  calc
    ‖∑ k ∈ Finset.range M, w ^ k‖ ≤ ∑ k ∈ Finset.range M, ‖w ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range M, (1 : ℝ) := by
      gcongr with k hk
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg w) hw
    _ = M := by simp

lemma geometricBlock_circle_sq (M : ℕ) {r : ℝ} (hr0 : 0 ≤ r) :
    Real.circleAverage (fun z : ℂ ↦ ‖geometricBlock M ((r : ℂ) * z)‖ ^ 2) 0 1 =
      ∑ k ∈ Finset.range M, r ^ (2 * k) := by
  symm
  simpa [geometricBlock] using truncPolynomial_parseval (fun _ : ℕ ↦ (1 : ℂ)) hr0 M

lemma geometricBlock_circle_sq_le (M : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.circleAverage (fun z : ℂ ↦ ‖geometricBlock M ((r : ℂ) * z)‖ ^ 2) 0 1 ≤ M := by
  rw [geometricBlock_circle_sq M hr0]
  calc
    (∑ k ∈ Finset.range M, r ^ (2 * k)) ≤ ∑ _k ∈ Finset.range M, (1 : ℝ) := by
      gcongr with k hk
      exact pow_le_one₀ hr0 hr1
    _ = M := by simp

/-- The reciprocal distance to the pole at `1`, in angular coordinates. -/
lemma one_sub_mul_geometricBlock (M : ℕ) (z : ℂ) :
    (1 - z) * geometricBlock M z = 1 - z ^ M := by
  rw [geometricBlock, mul_comm]
  exact geom_sum_mul_neg z M

lemma circleKernel_continuousOn {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (fun z : ℂ ↦ ‖(1 : ℂ) - (r : ℂ) * z‖⁻¹) (sphere 0 1) := by
  apply ContinuousOn.inv₀
  · fun_prop
  · intro z hz hzero
    have hznorm : ‖z‖ = 1 := by simpa using hz
    have hcomplex : (1 : ℂ) - (r : ℂ) * z = 0 := norm_eq_zero.mp hzero
    have heq : (1 : ℂ) = (r : ℂ) * z := sub_eq_zero.mp hcomplex
    have heqnorm := congrArg norm heq
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hznorm] at heqnorm
    linarith

lemma young_two_mul {α x y : ℝ} (hα : 0 < α) :
    2 * x * y ≤ α * x ^ 2 + y ^ 2 / α := by
  have heq : α * x ^ 2 + y ^ 2 / α = (α ^ 2 * x ^ 2 + y ^ 2) / α := by
    field_simp
  rw [heq, le_div_iff₀ hα]
  nlinarith [sq_nonneg (α * x - y)]

lemma geometricBlock_real_lower (M : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hclose : (M : ℝ) * (1 - q) ≤ 1 / 2) :
    (M : ℝ) / 2 ≤ ∑ k ∈ Finset.range M, q ^ k := by
  calc
    (M : ℝ) / 2 = ∑ _k ∈ Finset.range M, (1 / 2 : ℝ) := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ k ∈ Finset.range M, q ^ k := by
      gcongr with k hk
      have hkM : (k : ℝ) ≤ M := by
        exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hk))
      have hbern := one_add_mul_sub_le_pow (a := q) (by linarith) k
      have hnonneg : 0 ≤ ((M : ℝ) - k) * (1 - q) :=
        mul_nonneg (sub_nonneg.mpr hkM) (sub_nonneg.mpr hq1)
      nlinarith


end EF763

open Filter Metric Set
open scoped BigOperators Topology Asymptotics Real
namespace EF763

def damp (a : ℕ → ℂ) (t : ℝ) (n : ℕ) : ℂ := a n * (t : ℂ)^n

lemma damp_value (a : ℕ → ℂ) (t : ℝ) (z : ℂ) :
    powerSeriesValue a ((t : ℂ)*z) = powerSeriesValue (damp a t) z := by
  unfold powerSeriesValue damp
  simp only [mul_pow, mul_assoc]

lemma damp_norm (a : ℕ → ℂ) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ‖damp a t n‖ = ‖a n‖*t^n := by simp [damp,norm_mul,norm_pow,abs_of_nonneg ht]

lemma weighted_summable {a : ℕ → ℂ} {t D : ℝ} (ht : 0 < t)
    (h : ∀ n, ‖damp a t n‖ ≤ D) {z : ℂ} (hz : ‖z‖ < t) :
    Summable fun n => a n * z^n := by
  have small : ‖z / (t : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, div_lt_one ht]
    exact hz
  have hs := (summable_norm_coeff_mul_pow h small).of_norm
  apply hs.congr
  intro n
  simp only [damp, div_pow]
  field_simp [ht.ne']

lemma shifted_error_weighted {A : Set ℕ} {c : ℝ} {z : ℂ}
    (hs : Summable fun n : ℕ => (summatoryError A c n : ℂ) * z ^ n) (hz : ‖z‖ < 1) :
    HasSum
      (fun n : ℕ ↦ ((if n = 0 then 0 else summatoryError A c (n - 1)) : ℂ) * z ^ n)
      (z * powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z) := by
  have hsum : Summable fun n : ℕ ↦ (summatoryError A c n : ℂ) * z ^ n := by
    exact hs
  let g : ℕ → ℂ := fun n ↦
    ((if n = 0 then 0 else summatoryError A c (n - 1)) : ℂ) * z ^ n
  have htail : HasSum (fun n : ℕ ↦ g (n + 1))
      (z * powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z) := by
    have hm := hsum.hasSum.mul_left z
    simpa [g, powerSeriesValue, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hm
  have hall := (hasSum_nat_add_iff (f := g) 1).mp htail
  simpa [g] using hall

lemma representation_series_weighted {A : Set ℕ} {c : ℝ} {z : ℂ}
    (hs : Summable fun n : ℕ => (summatoryError A c n : ℂ) * z ^ n) (hz : ‖z‖ < 1) :
    powerSeriesValue (fun n ↦ (representationCount A n : ℂ)) z =
      (c : ℂ) / (1 - z) + (1 - z) *
        powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z := by
  have heSum : Summable fun n : ℕ ↦ (summatoryError A c n : ℂ) * z ^ n := by
    exact hs
  have hcSum : HasSum (fun n : ℕ ↦ (c : ℂ) * z ^ n) ((c : ℂ) / (1 - z)) := by
    simpa [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hz).mul_left (c : ℂ)
  have hshift := shifted_error_weighted (A := A) hs hz
  have htotal := hcSum.add heSum.hasSum |>.sub hshift
  rw [powerSeriesValue, powerSeriesValue]
  calc
    (∑' n : ℕ, (representationCount A n : ℂ) * z ^ n) =
        ∑' n : ℕ, ((c : ℂ) * z ^ n + (summatoryError A c n : ℂ) * z ^ n -
          ((if n = 0 then 0 else summatoryError A c (n - 1)) : ℂ) * z ^ n) := by
      apply tsum_congr
      intro n
      have hrC : (representationCount A n : ℂ) =
          (c : ℂ) + (summatoryError A c n : ℂ) -
            (((if n = 0 then 0 else summatoryError A c (n - 1)) : ℝ) : ℂ) := by
        exact_mod_cast representationCount_eq_error_difference A c n
      rw [hrC]
      split_ifs
      all_goals simp_all <;> ring
    _ = (c : ℂ) / (1 - z) +
        (∑' n : ℕ, (summatoryError A c n : ℂ) * z ^ n) -
          z * ∑' n : ℕ, (summatoryError A c n : ℂ) * z ^ n := htotal.tsum_eq
    _ = (c : ℂ) / (1 - z) + (1 - z) *
        ∑' n : ℕ, (summatoryError A c n : ℂ) * z ^ n := by ring

lemma indicatorSeries_weighted {A : Set ℕ} {c : ℝ} {z : ℂ}
    (hs : Summable fun n : ℕ => (summatoryError A c n : ℂ) * z ^ n) (hz : ‖z‖ < 1) :
    powerSeriesValue (indicatorComplex A) z ^ 2 =
      (c : ℂ) / (1 - z) + (1 - z) *
        powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z := by
  rw [indicatorSeries_sq hz, representation_series_weighted hs hz]

lemma weighted_master {A : Set ℕ} {c : ℝ}
    (M : ℕ) {z : ℂ} (hs : Summable fun n : ℕ => (summatoryError A c n : ℂ) * z ^ n) (hz : ‖z‖ < 1) :
    (geometricBlock M z * powerSeriesValue (indicatorComplex A) z) ^ 2 =
      (c : ℂ) * geometricBlock M z ^ 2 / (1 - z) +
        (1 - z ^ M) * geometricBlock M z *
          powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z := by
  rw [mul_pow, indicatorSeries_weighted hs hz]
  have hg := one_sub_mul_geometricBlock M z
  calc
    geometricBlock M z ^ 2 *
          ((c : ℂ) / (1 - z) + (1 - z) *
            powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z) =
        (c : ℂ) * geometricBlock M z ^ 2 / (1 - z) +
          ((1 - z) * geometricBlock M z) * geometricBlock M z *
            powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z := by ring
    _ = (c : ℂ) * geometricBlock M z ^ 2 / (1 - z) +
        (1 - z ^ M) * geometricBlock M z *
          powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z := by rw [hg]

lemma weighted_integrand {A : Set ℕ} {c : ℝ} (hc : 0 ≤ c)
    (M : ℕ) {z : ℂ} (hs : Summable fun n : ℕ => (summatoryError A c n : ℂ) * z ^ n)
    (hz : ‖z‖ < 1) :
    ‖geometricBlock M z * powerSeriesValue (indicatorComplex A) z‖ ^ 2 ≤
      c * ‖geometricBlock M z‖ ^ 2 * ‖1 - z‖⁻¹ +
        2 * ‖geometricBlock M z‖ *
          ‖powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z‖ := by
  have hpow : ‖z ^ M‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg z) hz.le
  calc
    ‖geometricBlock M z * powerSeriesValue (indicatorComplex A) z‖ ^ 2 =
        ‖(geometricBlock M z * powerSeriesValue (indicatorComplex A) z) ^ 2‖ := by
      rw [norm_pow]
    _ = ‖(c : ℂ) * geometricBlock M z ^ 2 / (1 - z) +
        (1 - z ^ M) * geometricBlock M z *
          powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z‖ := by
      rw [weighted_master M hs hz]
    _ ≤ ‖(c : ℂ) * geometricBlock M z ^ 2 / (1 - z)‖ +
        ‖(1 - z ^ M) * geometricBlock M z *
          powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z‖ := norm_add_le _ _
    _ ≤ c * ‖geometricBlock M z‖ ^ 2 * ‖1 - z‖⁻¹ +
        2 * ‖geometricBlock M z‖ *
          ‖powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z‖ := by
      simp only [norm_div, norm_mul, norm_pow]
      have hcabs : ‖(c : ℂ)‖ = c := by simp [Real.norm_eq_abs, abs_of_nonneg hc]
      rw [hcabs, div_eq_mul_inv]
      have hsub : ‖(1 : ℂ) - z ^ M‖ ≤ 2 := by
        have hpow' : ‖z‖ ^ M ≤ 1 := by simpa only [norm_pow] using hpow
        calc
          ‖(1 : ℂ) - z ^ M‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ M‖ := norm_sub_le _ _
          _ ≤ 2 := by norm_num; linarith
      gcongr

lemma bounded_circle_sq {a : ℕ → ℂ} {D r : ℝ} (hD : 0 ≤ D)
    (he : ∀ n, ‖a n‖ ≤ D) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage
        (fun z : ℂ ↦ ‖powerSeriesValue a
          ((r : ℂ) * z)‖ ^ 2) 0 1 ≤
      D ^ 2 / (1 - r ^ 2) := by
  have heC : ∀ n, ‖(a n)‖ ≤ D := by
    intro n
    simpa using he n
  have hr2 : r ^ 2 < 1 := by nlinarith
  rw [circleParseval_bounded hD hr0 hr1 heC]
  calc
    (∑' n : ℕ, ‖(a n)‖ ^ 2 * r ^ (2 * n)) ≤
        ∑' n : ℕ, D ^ 2 * (r ^ 2) ^ n := by
      apply (summable_sq_norm_mul_rpow hD hr0 hr1 heC).tsum_le_tsum
      · intro n
        have hsq : ‖(a n)‖ ^ 2 ≤ D ^ 2 := by
          nlinarith [heC n, norm_nonneg (a n)]
        simpa [pow_mul] using
          mul_le_mul_of_nonneg_right hsq (pow_nonneg (sq_nonneg r) n)
      · exact (summable_geometric_of_norm_lt_one (K := ℝ)
          (by simpa [abs_of_nonneg (sq_nonneg r)] using hr2)).mul_left (D ^ 2)
    _ = D ^ 2 / (1 - r ^ 2) := by
      rw [tsum_mul_left, (hasSum_geometric_of_norm_lt_one (K := ℝ)
        (by simpa [abs_of_nonneg (sq_nonneg r)] using hr2)).tsum_eq]
      field_simp

end EF763

open Filter Set
open scoped BigOperators Topology Asymptotics Real
namespace EF763
lemma geometric_slope (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (n : ℝ) * (1-t) * t^n ≤ 1 := by
  have hs : (n : ℝ) * t^n ≤ ∑ k ∈ Finset.range n, t^k := by
    calc
      _ = ∑ _k ∈ Finset.range n, t^n := by simp
      _ ≤ _ := Finset.sum_le_sum fun k hk => pow_le_pow_of_le_one ht ht1 (Finset.mem_range.mp hk).le
  have hh := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr ht1)
  rw [geom_sum_mul_neg] at hh
  nlinarith [pow_nonneg ht n]

end EF763

open Filter Set Metric
open scoped BigOperators Topology
namespace EF763

noncomputable def kernel (r : ℝ) (z : ℂ) : ℝ := ‖1-(r:ℂ)*z‖⁻¹
noncomputable def blk (M : ℕ) (r : ℝ) (z : ℂ) : ℂ := geometricBlock M ((r:ℂ)*z)
noncomputable def mainInt (M : ℕ) (r : ℝ) (z : ℂ) : ℝ := ‖blk M r z‖^2 * kernel r z
noncomputable def fullInt (A : Set ℕ) (M : ℕ) (r : ℝ) (z : ℂ) : ℝ :=
  ‖blk M r z * powerSeriesValue (indicatorComplex A) ((r:ℂ)*z)‖^2

lemma norm_rad {r : ℝ} (hr : 0 ≤ r) {z : ℂ} (hz : ‖z‖ = 1) : ‖(r:ℂ)*z‖ = r := by
  simp [norm_mul,Complex.norm_real,abs_of_nonneg hr,hz]
lemma kernel_pos {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    0 < ‖(1:ℂ)-(r:ℂ)*z‖ := by
  apply norm_pos_iff.mpr
  intro he
  have h := congrArg norm (sub_eq_zero.mp he)
  rw [norm_one,norm_rad hr hz] at h
  linarith
lemma block_bd {M : ℕ} {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖blk M r z‖ ≤ M := geometricBlock_norm_le _ ((norm_rad hr hz).le.trans hr1)
lemma block_cont (M : ℕ) (r : ℝ) : Continuous (blk M r) := by unfold blk geometricBlock; fun_prop
lemma kernel_cont {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) : ContinuousOn (kernel r) (sphere 0 1) :=
  circleKernel_continuousOn hr hr1
lemma main_cont (M : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) : ContinuousOn (mainInt M r) (sphere 0 1) :=
  ((block_cont M r).norm.pow 2).continuousOn.mul (kernel_cont hr hr1)
lemma full_cont (A : Set ℕ) (M : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (fullInt A M r) (sphere 0 1) :=
  ((block_cont M r).continuousOn.mul (powerSeriesValue_continuousOn_sphere hr hr1 (indicatorComplex_norm_le_one A))).norm.pow 2

lemma block_rad_diff {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hr : r ≤ 1)
    (M : ℕ) {z : ℂ} (hz : ‖z‖ = 1) : ‖blk M r z - blk M s z‖ ≤ M^2 * (r-s) := by
  have hp (k : ℕ) : r^k-s^k ≤ k*(r-s) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hsrk := pow_le_pow_left₀ hs hsr k
      have hsk : s^k ≤ 1 := pow_le_one₀ hs (hsr.trans hr)
      rw [pow_succ,pow_succ,Nat.cast_succ]
      nlinarith [mul_nonneg (sub_nonneg.mpr hsrk) (sub_nonneg.mpr hr),
        mul_nonneg (sub_nonneg.mpr hsk) (sub_nonneg.mpr hsr)]
  unfold blk geometricBlock
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ _ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range M, (M:ℝ)*(r-s) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [mul_pow,mul_pow,← sub_mul,norm_mul,norm_pow,hz,one_pow,mul_one,
        ← Complex.ofReal_pow,← Complex.ofReal_pow,← Complex.ofReal_sub,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hs hsr k))]
      exact (hp k).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hk).le) (sub_nonneg.mpr hsr))
    _ = _ := by simp; ring

lemma kernel_rad_diff {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = 1) : kernel r z - kernel s z ≤ (r-s)*(kernel r z^2 + kernel s z^2) := by
  let x : ℝ := ‖1-(r:ℂ)*z‖
  let y : ℝ := ‖1-(s:ℂ)*z‖
  have hx : 0<x := kernel_pos (hs.trans hsr) hr1 hz
  have hy : 0<y := kernel_pos hs (hsr.trans_lt hr1) hz
  have hdiff : y-x ≤ r-s := by
    have h := norm_sub_norm_le ((1:ℂ)-(s:ℂ)*z) (1-(r:ℂ)*z)
    rw [show (1:ℂ)-(s:ℂ)*z - (1-(r:ℂ)*z) = ((r-s:ℝ):ℂ)*z by push_cast; ring,
      norm_rad (sub_nonneg.mpr hsr) hz] at h
    exact h
  change x⁻¹ - y⁻¹ ≤ (r-s)*(x⁻¹^2+y⁻¹^2)
  calc
    _ = (y-x)*(x⁻¹*y⁻¹) := by field_simp
    _ ≤ (r-s)*(x⁻¹*y⁻¹) := mul_le_mul_of_nonneg_right hdiff (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith only [sq_nonneg (x⁻¹-y⁻¹),sq_nonneg x⁻¹,sq_nonneg y⁻¹]) (sub_nonneg.mpr hsr)

lemma main_rad_diff {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hr1 : r < 1)
    (M : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    mainInt M r z - mainInt M s z ≤
      (2*(M:ℝ)^3*(r-s))*kernel r z + ((M:ℝ)^2*(r-s))*(kernel r z^2+kernel s z^2) := by
  have ba := block_bd (M := M) (hs.trans hsr) hr1.le hz
  have bb := block_bd (M := M) hs (hsr.trans hr1.le) hz
  have hdiff := (norm_sub_norm_le (blk M r z) (blk M s z)).trans (block_rad_diff hs hsr hr1.le M hz)
  have hsum := add_le_add ba bb
  have hsq : ‖blk M r z‖^2 - ‖blk M s z‖^2 ≤ 2*(M:ℝ)^3*(r-s) := by
    rw [sq_sub_sq,mul_comm (‖blk M r z‖+‖blk M s z‖)]
    calc
      _ ≤ ((M:ℝ)^2*(r-s))*(‖blk M r z‖+‖blk M s z‖) :=
        mul_le_mul_of_nonneg_right hdiff (by positivity)
      _ ≤ ((M:ℝ)^2*(r-s))*((M:ℝ)+M) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hsr))
      _ = _ := by ring
  have kb : 0 ≤ kernel r z := inv_nonneg.2 (norm_nonneg _)
  have h1 := mul_le_mul_of_nonneg_right hsq kb
  have h2 := mul_le_mul_of_nonneg_left (kernel_rad_diff hs hsr hr1 hz) (sq_nonneg ‖blk M s z‖)
  have h3 := mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg _)).2 bb)
    (mul_nonneg (sub_nonneg.mpr hsr) (add_nonneg (sq_nonneg (kernel r z)) (sq_nonneg (kernel s z))))
  unfold mainInt
  linarith only [h1,h2,h3]

end EF763

open Filter Set Metric
open scoped BigOperators Topology
namespace EF763

noncomputable def avg (f : ℂ → ℝ) := Real.circleAverage f 0 1
abbrev Cts (f : ℂ → ℝ) := ContinuousOn f (sphere 0 1)

lemma avg_const (a : ℝ) : avg (fun _ => a) = a := Real.circleAverage_const _ _ _
lemma avg_scale (a : ℝ) (f : ℂ → ℝ) : avg (fun z => a*f z) = a*avg f := by
  change Real.circleAverage (a • f) 0 1 = a • Real.circleAverage f 0 1
  rw [Real.circleAverage_smul]
lemma avg_add {f g : ℂ → ℝ} (hf : Cts f) (hg : Cts g) :
    avg (fun z => f z + g z) = avg f + avg g :=
  Real.circleAverage_fun_add (hf.circleIntegrable zero_le_one) (hg.circleIntegrable zero_le_one)
lemma avg_sub {f g : ℂ → ℝ} (hf : Cts f) (hg : Cts g) :
    avg (fun z => f z - g z) = avg f - avg g :=
  Real.circleAverage_sub (hf.circleIntegrable zero_le_one) (hg.circleIntegrable zero_le_one)
lemma avg_le {f g : ℂ → ℝ} (hf : Cts f) (hg : Cts g) (h : ∀ z : ℂ, ‖z‖=1 → f z ≤ g z) :
    avg f ≤ avg g := Real.circleAverage_mono (hf.circleIntegrable zero_le_one)
      (hg.circleIntegrable zero_le_one) (fun z hz => h z (by simpa using hz))

lemma avg_kernel_sq {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    avg (fun z => kernel r z^2) = (1-r^2)⁻¹ := by
  let a : ℕ → ℂ := fun _ => 1
  have hh : ∀ n, ‖a n‖ ≤ 1 := by simp [a]
  have h := circleParseval_bounded zero_le_one hr hr1 hh
  have hc : avg (fun z => kernel r z^2) =
      Real.circleAverage (fun z => ‖powerSeriesValue a ((r:ℂ)*z)‖^2) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hw := norm_rad hr (show ‖z‖ = 1 by simpa using hz)
    have hgeom := (hasSum_geometric_of_norm_lt_one (hw.trans_lt hr1)).tsum_eq
    simp [a,powerSeriesValue,hgeom,kernel]
  rw [hc,h]
  have hgeom := (hasSum_geometric_of_norm_lt_one (K := ℝ) (ξ := r^2)
    (by simpa [abs_of_nonneg (sq_nonneg r)] using pow_lt_one₀ hr hr1 (by decide : 2 ≠ 0))).tsum_eq
  simpa [a,pow_mul] using hgeom

lemma avg_kernel_le {r N X : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (hX : 0 < X)
    (hX2 : X^2=N) (hbound : (1-r^2)⁻¹ ≤ N) : avg (kernel r) ≤ X := by
  have hk := kernel_cont hr hr1
  have hmono : avg (fun z => (2*X)*kernel r z) ≤ avg (fun z => X^2 + kernel r z^2) := by
    apply avg_le (continuousOn_const.mul hk) (continuousOn_const.add (hk.pow 2))
    intro z _
    change 2*X*kernel r z ≤ X^2+(kernel r z)^2
    nlinarith [sq_nonneg (X-kernel r z)]
  rw [avg_scale,avg_add (f:=fun _ => X^2) (g:=fun z => kernel r z^2) continuousOn_const (hk.pow 2),avg_const,avg_kernel_sq hr hr1] at hmono
  by_contra! hbad
  nlinarith only [hmono,hbound,hX2,mul_pos hX (sub_pos.mpr hbad)]

lemma avg_main_diff {s r N X : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hr1 : r < 1)
    (hX : 0 < X) (hX2 : X^2=N) (hbound : (1-r^2)⁻¹ ≤ N)
    (hgap : (r-s)*N ≤ 2) (M : ℕ) (hM : (M:ℝ) ≤ X) :
    avg (mainInt M r) - avg (mainInt M s) ≤ 8*(M:ℝ)^2 := by
  have hr := hs.trans hsr
  have hs1 := hsr.trans_lt hr1
  have hsbound : (1-s^2)⁻¹ ≤ N := by
    apply le_trans _ hbound
    exact inv_anti₀ (sub_pos.mpr (pow_lt_one₀ hr hr1 (by decide)))
      (sub_le_sub_left ((sq_le_sq₀ hs hr).2 hsr) 1)
  let u := 2*(M:ℝ)^3*(r-s)
  let v := (M:ℝ)^2*(r-s)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have kc := kernel_cont hr hr1
  have ks := kernel_cont hs hs1
  have hh := avg_le ((main_cont M hr hr1).sub (main_cont M hs hs1))
    ((continuousOn_const.mul kc).add (continuousOn_const.mul ((kc.pow 2).add (ks.pow 2))))
    (fun z hz => main_rad_diff hs hsr hr1 M hz)
  change avg (fun z => mainInt M r z-mainInt M s z) ≤
    avg (fun z => u*kernel r z + v*(kernel r z^2+kernel s z^2)) at hh
  rw [avg_sub (main_cont M hr hr1) (main_cont M hs hs1),
    avg_add (f:= fun z => u*kernel r z) (g:=fun z => v*(kernel r z^2+kernel s z^2)) (continuousOn_const.mul kc) (continuousOn_const.mul ((kc.pow 2).add (ks.pow 2))),
    avg_scale,avg_scale,avg_add (f:=fun z => kernel r z^2) (g:=fun z => kernel s z^2) (kc.pow 2) (ks.pow 2),avg_kernel_sq hr hr1,avg_kernel_sq hs hs1] at hh
  have h1 := mul_le_mul_of_nonneg_left (avg_kernel_le hr hr1 hX hX2 hbound) hu
  have h2 := mul_le_mul_of_nonneg_left (add_le_add hbound hsbound) hv
  have hMX : (M:ℝ)*X ≤ N := by rw [← hX2,pow_two]; gcongr
  have hdiff := sub_nonneg.mpr hsr
  have haux : (M:ℝ)*X*(r-s) ≤ 2 := (mul_le_mul_of_nonneg_right hMX hdiff).trans (by linarith only [hgap])
  have ha := mul_le_mul_of_nonneg_left haux (show 0 ≤ 2*(M:ℝ)^2 by positivity)
  have hb := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2*(M:ℝ)^2 by positivity)
  dsimp [u,v] at h1 h2
  dsimp [u,v] at hh
  linarith only [hh,h1,h2,ha,hb]
end EF763

open Filter Set Metric
open scoped BigOperators Topology
namespace EF763

lemma avg_error {A : Set ℕ} {t r c D α : ℝ} (hc : 0 ≤ c) (hD : 0 ≤ D)
    (ht : 0 < t) (ht1 : t < 1) (hrt : r=t^2)
    (he : ∀ n, ‖damp (fun k => (summatoryError A c k : ℂ)) t n‖ ≤ D)
    (hα : 0 < α) (M : ℕ) :
    |avg (fullInt A M r) - c*avg (mainInt M r)| ≤ α*M+α⁻¹*(D^2/(1-r)) := by
  have hr : 0 ≤ r := hrt ▸ sq_nonneg _
  have hr1 : r<1 := hrt ▸ pow_lt_one₀ ht.le ht1 (by decide)
  let E (z : ℂ) := powerSeriesValue (fun k => (summatoryError A c k : ℂ)) ((r:ℂ)*z)
  have hrewrite (z : ℂ) : E z = powerSeriesValue (damp (fun k => (summatoryError A c k : ℂ)) t) ((t:ℂ)*z) := by
    dsimp [E]; rw [← damp_value]; push_cast [hrt]; ring_nf
  have hEcont : ContinuousOn E (sphere 0 1) := by
    simpa only [funext hrewrite] using powerSeriesValue_continuousOn_sphere ht.le ht1 he
  have henergy : avg (fun z => ‖E z‖^2) ≤ D^2/(1-r) := by
    simpa only [avg,hrewrite,hrt] using (bounded_circle_sq hD he ht.le ht1)
  have hblock : avg (fun z => ‖blk M r z‖^2) ≤ M := geometricBlock_circle_sq_le M hr hr1.le
  have point (z : ℂ) (hz : ‖z‖=1) :
      |fullInt A M r z - c*mainInt M r z| ≤ α*‖blk M r z‖^2 + α⁻¹*‖E z‖^2 := by
    let w := (r:ℂ)*z
    have hw : ‖w‖=r := norm_rad hr hz
    have hw1 := hw.trans_lt hr1
    have hwt : ‖w‖<t := by rw [hw,hrt]; nlinarith only [mul_pos ht (sub_pos.mpr ht1)]
    have h := weighted_master (A := A) (c := c) M (weighted_summable ht he hwt) hw1
    let U := (c:ℂ)*geometricBlock M w^2/(1-w)
    let V := (1-w^M)*geometricBlock M w*E z
    have hid : (blk M r z * powerSeriesValue (indicatorComplex A) w)^2 = U+V := h
    have hT : fullInt A M r z = ‖U+V‖ := by
      unfold fullInt
      rw [← hid,norm_pow]
    have hU : c*mainInt M r z = ‖U‖ := by
      simp [mainInt,blk,kernel,U,w,norm_div,norm_mul,norm_pow,abs_of_nonneg hc,div_eq_mul_inv,mul_assoc]
    have hnorm : ‖1-w^M‖ ≤ 2 := by
      calc
        _ ≤ ‖(1:ℂ)‖ + ‖w^M‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one,norm_pow]; linarith [pow_le_one₀ (norm_nonneg w) hw1.le (n:=M)]
    rw [hT,hU]
    calc
      _ ≤ ‖U+V-U‖ := abs_norm_sub_norm_le _ _
      _ = ‖V‖ := by rw [add_sub_cancel_left]
      _ ≤ 2*‖blk M r z‖*‖E z‖ := by
        dsimp only [V]; rw [norm_mul,norm_mul]; gcongr <;> rfl
      _ ≤ _ := by simpa [div_eq_inv_mul] using young_two_mul (x:=‖blk M r z‖) (y:=‖E z‖) hα
  let f := fullInt A M r
  let g := fun z => c*mainInt M r z
  let b := fun z => α*‖blk M r z‖^2 + α⁻¹*‖E z‖^2
  have hf : Cts f := full_cont _ _ hr hr1
  have hg : Cts g := continuousOn_const.mul (main_cont M hr hr1)
  have hH : Cts (fun z => ‖blk M r z‖^2) := ((block_cont M r).norm.pow 2).continuousOn
  have hE : Cts (fun z => ‖E z‖^2) := hEcont.norm.pow 2
  have hb : Cts b := (continuousOn_const.mul hH).add (continuousOn_const.mul hE)
  have hab : |avg f - avg g| ≤ avg b := by
    rw [← avg_sub hf hg]
    refine Real.abs_circleAverage_le_circleAverage_abs.trans ?_
    exact avg_le (hf.sub hg).abs hb point
  change |avg (fullInt A M r)-avg (fun z => c*mainInt M r z)| ≤ avg b at hab
  rw [avg_scale] at hab
  apply hab.trans
  dsimp only [b]
  rw [avg_add (f:=fun z => α*‖blk M r z‖^2) (g:=fun z => α⁻¹*‖E z‖^2) (continuousOn_const.mul hH) (continuousOn_const.mul hE),avg_scale,avg_scale]
  exact add_le_add (mul_le_mul_of_nonneg_left hblock hα.le) (mul_le_mul_of_nonneg_left henergy (inv_nonneg.2 hα.le))

lemma radial_parseval_lower {A : Set ℕ} (M : ℕ) {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hr1 : r < 1) :
    (∑ k ∈ Finset.range M, (r^2)^k) * indicatorSeriesReal A (r^2) -
    (∑ k ∈ Finset.range M, (s^2)^k) * indicatorSeriesReal A (s^2) ≤
        avg (fullInt A M r) - avg (fullInt A M s) := by
  have hr := hs.trans hsr
  have hs1 := hsr.trans_lt hr1
  let b (n : ℕ) : ℝ := blockCoefficient A M n
  have hlin (u : ℝ) (hu : 0 ≤ u) (hu1 : u<1) : Summable fun n => b n*(u^2)^n :=
    blockCoefficient_series_summable A M (sq_nonneg u) (pow_lt_one₀ hu hu1 (by decide))
  have hsq (u : ℝ) (hu : 0 ≤ u) (hu1 : u<1) : Summable fun n => b n^2*(u^2)^n :=
    by simpa [b,pow_mul] using blockCoefficient_sq_series_summable A M hu hu1
  have hdiff := ((hlin r hr hr1).sub (hlin s hs hs1)).tsum_le_tsum (g := fun n => b n^2*(r^2)^n-b n^2*(s^2)^n)
    (fun n => show b n*(r^2)^n-b n*(s^2)^n ≤ _ by
      rw [← mul_sub,← mul_sub]
      exact mul_le_mul_of_nonneg_right (natCast_le_sq (blockCoefficient A M n))
        (sub_nonneg.2 (pow_le_pow_left₀ (sq_nonneg s) ((sq_le_sq₀ hs hr).2 hsr) n)))
    ((hsq r hr hr1).sub (hsq s hs hs1))
  change (∑' n, (b n*(r^2)^n-b n*(s^2)^n)) ≤ _ at hdiff
  rw [Summable.tsum_sub (hlin r hr hr1) (hlin s hs hs1),Summable.tsum_sub (hsq r hr hr1) (hsq s hs hs1)] at hdiff
  unfold avg fullInt blk
  rw [block_parseval M hr hr1,block_parseval M hs hs1]
  unfold indicatorSeriesReal
  rw [← blockCoefficient_real_series_identity M (sq_nonneg r) (pow_lt_one₀ hr hr1 (by decide)),
      ← blockCoefficient_real_series_identity M (sq_nonneg s) (pow_lt_one₀ hs hs1 (by decide))]
  simpa only [b,pow_mul] using hdiff
end EF763

open Filter Set Metric
open scoped BigOperators Topology
namespace EF763
lemma real_approx {A : Set ℕ} {c D t q : ℝ} (hD : 0 ≤ D)
    (ht : 0 < t) (ht1 : t < 1) (hq : q = t^4)
    (he : ∀ n, ‖damp (fun k => (summatoryError A c k : ℂ)) t n‖ ≤ D) :
    |(indicatorSeriesReal A q)^2 - c / (1-q)| ≤ 4*D := by
  have hq0 : 0 ≤ q := hq ▸ by positivity
  have hqt : q < t := by
    rw [hq]
    calc
      t^4 = t*t^3 := by ring
      _ < t*1 := mul_lt_mul_of_pos_left (pow_lt_one₀ ht.le ht1 (by decide)) ht
      _ = t := mul_one _
  have hq1 := hqt.trans ht1
  have hqnorm : ‖(q : ℂ)‖ < t := by simpa [abs_of_nonneg hq0]
  have hid := indicatorSeries_weighted (A := A) (c := c) (weighted_summable ht he hqnorm) (hqnorm.trans ht1)
  rw [indicatorSeries_at_real] at hid
  have harg : ‖((t : ℂ)^2)‖ ≤ 1 := by simp [norm_pow,abs_of_pos ht,pow_le_one₀ ht.le ht1.le]
  have herr := powerSeriesValue_norm_le hD ht.le ht1 he harg
  rw [← damp_value] at herr
  have hfour : (t : ℂ) * ((t : ℂ) * (t : ℂ)^2) = (q : ℂ) := by rw [hq]; push_cast; ring
  rw [hfour] at herr
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hre :
      |(powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) (q : ℂ)).re| ≤
        D / (1 - t) :=
    (Complex.abs_re_le_norm _).trans herr
  apply_fun Complex.re at hid
  have hmain : ((c : ℂ) / ((1 : ℂ) - (q : ℂ))).re = c / (1 - q) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div,
      Complex.ofReal_re]
  have hleft : ((indicatorSeriesReal A q : ℂ) ^ 2).re =
      (indicatorSeriesReal A q) ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hprod :
      (((1 : ℂ) - (q : ℂ)) *
        powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) (q : ℂ)).re =
        (1 - q) *
          (powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) (q : ℂ)).re := by
    simp
  simp only [Complex.add_re] at hid
  rw [hleft, hmain, hprod] at hid
  have hh : 1-q ≤ 4*(1-t) := by
    rw [hq]
    have hb := one_add_mul_sub_le_pow (a := t) (by linarith) 4
    norm_num at hb
    linarith
  have hb : (1-q) * (D / (1-t)) ≤ 4*D := by
    rw [← mul_div_assoc,div_le_iff₀ (sub_pos.mpr ht1)]
    nlinarith [mul_le_mul_of_nonneg_right hh hD]
  rw [hid,add_sub_cancel_left,abs_mul,abs_of_pos hden]
  exact (mul_le_mul_of_nonneg_left hre hden.le).trans hb

lemma difference_real {A : Set ℕ} {c N D X q : ℝ} (hc : 0 < c) (hN : 0 < N) (hX : 0 < X)
    (hX2 : X^2=N) (hq : 1/2 ≤ q) (hq1 : q<1)
    (hgap : 1-q ≤ 4/N) (hsmallgap : 1/N ≤ 1-q) (hD : 192*D ≤ c*N)
    (he1 : |(indicatorSeriesReal A q)^2 - c/(1-q)| ≤ 4*D)
    (he2 : |(indicatorSeriesReal A (q^2))^2 - c/(1-q^2)| ≤ 4*D) :
    (c/(48*(c+1)))*X ≤ indicatorSeriesReal A q - indicatorSeriesReal A (q^2) := by
  let u := indicatorSeriesReal A q
  let v := indicatorSeriesReal A (q^2)
  have h0 : 0 ≤ q := by linarith
  have hu : 0 ≤ u := indicatorSeriesReal_nonneg A h0
  have hv : 0 ≤ v := indicatorSeriesReal_nonneg A (sq_nonneg _)
  have gap := sub_pos.mpr hq1
  have g2 := sub_pos.mpr (pow_lt_one₀ h0 hq1 (by decide : 2 ≠ 0))
  have hq2 : q^2 ≤ q := by nlinarith only [mul_nonneg h0 gap.le]
  have hlow : c*N/4 ≤ c/(1-q) := by
    rw [le_div_iff₀ gap]
    calc
      _ ≤ (c*N/4)*(4/N) := mul_le_mul_of_nonneg_left hgap (by positivity)
      _ = _ := by field_simp
  have hmax : c/(1-q) ≤ c*N := by
    rw [div_le_iff₀ gap]
    calc
      c = (c*N)*(1/N) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmallgap (by positivity)
  have hmax2 : c/(1-q^2) ≤ c/(1-q) := div_le_div_of_nonneg_left hc.le gap (by linarith)
  have hmain : c*N/12 ≤ c/(1-q) - c/(1-q^2) := by
    have hm : 1/3 ≤ q/(1+q) := (le_div_iff₀ (by linarith)).2 (by linarith)
    calc
      _ = c*N/4*(1/3) := by ring
      _ ≤ (c/(1-q))*(q/(1+q)) := mul_le_mul hlow hm (by norm_num) (by positivity)
      _ = _ := by field_simp [gap.ne',g2.ne',show 1+q ≠ 0 by linarith]; ring
  change |u^2-c/(1-q)| ≤ _ at he1
  change |v^2-c/(1-q^2)| ≤ _ at he2
  have hdiff : c*N/24 ≤ u^2-v^2 := by linarith only [(abs_le.1 he1).1,(abs_le.1 he2).2,hmain,hD]
  have hDpos := (abs_nonneg (u^2-c/(1-q))).trans he1
  have hlim : 2*c*N ≤ ((c+1)*X)^2 := by
    rw [mul_pow,hX2]
    nlinarith only [mul_nonneg (sq_nonneg c) hN.le,hN.le]
  have hupp : u ≤ (c+1)*X := (sq_le_sq₀ hu (by positivity)).1 (by linarith only [(abs_le.1 he1).2,hmax,hD,hlim,hDpos])
  have hvpp : v ≤ (c+1)*X := (sq_le_sq₀ hv (by positivity)).1 (by linarith only [(abs_le.1 he2).2,hmax,hmax2,hD,hlim,hDpos])
  have huv : 0 ≤ u-v := by
    have := (sq_le_sq₀ hv hu).1 (by linarith only [hdiff,mul_pos hc hN])
    linarith
  change _ ≤ u-v
  have hprod : c*N/24 ≤ (2*(c+1)*X)*(u-v) := by
    calc
      _ ≤ _ := hdiff
      _ = (u+v)*(u-v) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hupp,hvpp]) huv
  apply le_of_mul_le_mul_left (a := 2*(c+1)*X) _ (by positivity)
  calc
    _ = c*N/24 := by rw [← hX2]; field_simp; ring
    _ ≤ _ := hprod
end EF763

open Filter Set
open scoped Topology
namespace EF763

noncomputable def quarter (x : ℝ) := √(√x)
lemma quarter_eq {x : ℝ} (hx : 0 ≤ x) : quarter x = x^(1/4:ℝ) := by
  rw [quarter,Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hx]; norm_num
lemma quarter_top : Tendsto quarter atTop atTop := Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop
lemma quarter_ratio {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : quarter y ≤ (y/x)*quarter x := by
  rw [quarter_eq hx.le,quarter_eq (hx.le.trans hxy)]
  have h1 : 1 ≤ y/x := (one_le_div hx).2 hxy
  have hpow := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num : (1/4:ℝ) ≤ 1)
  rw [Real.rpow_one,Real.div_rpow (hx.le.trans hxy) hx.le] at hpow
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hx _)).1 hpow

lemma quarter_envelope {e : ℕ → ℝ}
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ‖e n‖ ≤ δ * quarter n)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, ‖e n‖ * (1 - 1/(N : ℝ))^n ≤ δ * quarter N := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hsmall δ hδ)
  let B : ℝ := ∑ k ∈ Finset.range K, ‖e k‖
  have hw := (quarter_top.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (B/δ)
  filter_upwards [hw,eventually_ge_atTop (2:ℕ)] with N hWN hN n
  change B/δ ≤ quarter N at hWN
  have Nx : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hNx : 1 < (N:ℝ) := by linarith
  let t := 1 - 1 / (N:ℝ)
  have ht : 0 ≤ t := sub_nonneg.2 ((div_le_one (by positivity : 0<(N:ℝ))).2 hNx.le)
  have ht1 : t ≤ 1 := sub_le_self _ (by positivity)
  change ‖e n‖ * t^n ≤ _
  by_cases hn : n < K
  · have hb : ‖e n‖ ≤ B := Finset.single_le_sum (fun i _ => norm_nonneg (e i)) (Finset.mem_range.2 hn)
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ ht ht1)).trans <|
      hb.trans (by simpa [mul_comm] using (div_le_iff₀ hδ).mp hWN)
  have hs := hK n (by omega)
  by_cases hnN : n ≤ N
  · exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ ht ht1)).trans
      (hs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (by exact_mod_cast hnN))) hδ.le))
  have hNn : (N:ℝ) ≤ n := by exact_mod_cast (by omega : N ≤ n)
  have hv := quarter_ratio (show 0<(N:ℝ) by linarith) hNn
  have hslope : ((n:ℝ)/(N:ℝ))*t^n ≤ 1 := by
    simpa [t,div_eq_mul_inv] using geometric_slope n ht ht1
  calc
    _ ≤ (δ * ((n:ℝ)/(N:ℝ) * quarter N)) * t^n := by gcongr; exact hs.trans (by gcongr)
    _ = (δ*quarter N) * (((n:ℝ)/(N:ℝ))*t^n) := by ring
    _ ≤ _ := mul_le_of_le_one_right (mul_nonneg hδ.le (Real.sqrt_nonneg _)) hslope
end EF763

open Filter Set Metric
open scoped BigOperators Topology Asymptotics Real
namespace EF763

set_option maxHeartbeats 2500000 in
lemma impossible_sharp {A : Set ℕ} {c a b δ N : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) (hb1 : b ≤ 1) (hd : 0 < δ)
    (ha16 : 16*a = c/(48*(c+1))) (hcb : 8*c*b ≤ a)
    (hdc : 192*δ ≤ c) (hd2 : δ^2 ≤ a^2*(b/2))
    (hN : 64 ≤ N) (hlarge : 2 ≤ b * √N)
    (he : ∀ n, ‖summatoryError A c n‖ * (1 - 1/N)^n ≤ δ * quarter N) : False := by
  let X := √N
  let W := quarter N
  let D := δ*W
  let M := ⌊b*X⌋₊
  let t := 1-1/N
  let r := t^2
  let s := r^2
  have hNp : 0 < N := by linarith
  have hXp : 0 < X := Real.sqrt_pos.2 hNp
  have hX2 : X^2=N := Real.sq_sqrt hNp.le
  have hX8 : 8 ≤ X := by nlinarith only [hX2,hXp.le,hN]
  have hWp : 0 < W := Real.sqrt_pos.2 hXp
  have hW2 : W^2=X := Real.sq_sqrt hXp.le
  have hWX : W ≤ X := by nlinarith only [hW2,hX8,sq_nonneg (W-1)]
  have hXN : X ≤ N := by nlinarith only [hX2,mul_nonneg hXp.le (show 0 ≤ X-1 by linarith only [hX8])]
  have hDp : 0 ≤ D := mul_nonneg hd.le hWp.le
  have hDn : 192*D ≤ c*N := by
    dsimp only [D]
    calc
      _ = (192*δ)*W := by ring
      _ ≤ c*N := mul_le_mul hdc (hWX.trans hXN) hWp.le hc.le
  have hhN : 1/N ≤ 1/64 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN
  have ht : 0<t := by dsimp [t]; linarith only [hhN]
  have ht1 : t<1 := by dsimp [t]; linarith only [one_div_pos.mpr hNp]
  have htgap : 1-t = 1/N := by dsimp [t]; ring
  have hr : 0<r := sq_pos_of_pos ht
  have hr1 : r<1 := pow_lt_one₀ ht.le ht1 (by decide)
  have hs : 0<s := sq_pos_of_pos hr
  have hs1 : s<1 := pow_lt_one₀ hr.le hr1 (by decide)
  have hsr : s≤r := by dsimp [s]; nlinarith only [mul_nonneg hr.le (sub_nonneg.mpr hr1.le)]
  have hrt : r≤t := by dsimp [r]; nlinarith only [mul_nonneg ht.le (sub_nonneg.mpr ht1.le)]
  have hs4 : s=t^4 := by dsimp [s,r]; ring
  have hs8 : s^2=r^4 := by dsimp [s]; ring
  have hsgap : 1-s ≤ 4/N := by
    have hbern := one_add_mul_sub_le_pow (a:=t) (by linarith only [ht.le]) 4
    norm_num at hbern
    rw [hs4,show 4/N=4*(1/N) by ring,← htgap]; linarith only [hbern]
  have hsHalf : 1/2 ≤ s := by
    have hf : 4/N ≤ 4/64 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN
    linarith only [hf,hsgap]
  have hsi : (1-s)⁻¹ ≤ N := by
    rw [inv_eq_one_div,div_le_iff₀ (sub_pos.mpr hs1)]
    have hh := mul_le_mul_of_nonneg_left (show 1/N ≤ 1-s by linarith only [htgap,hsr,hrt]) hNp.le
    rwa [mul_one_div_cancel hNp.ne'] at hh
  have hri : (1-r)⁻¹ ≤ N := by
    rw [inv_eq_one_div,div_le_iff₀ (sub_pos.mpr hr1)]
    have hh := mul_le_mul_of_nonneg_left (show 1/N ≤ 1-r by linarith only [htgap,hrt]) hNp.le
    rwa [mul_one_div_cancel hNp.ne'] at hh
  have hdr : (r-s)*N ≤ 2 := by
    have hd1 : r-s ≤ 1-r := by dsimp [s]; nlinarith only [sq_nonneg (1-r)]
    have hd2 : 1-r ≤ 2*(1-t) := by dsimp [r]; nlinarith only [sq_nonneg (1-t)]
    have h := mul_le_mul_of_nonneg_right (hd1.trans hd2) hNp.le
    rw [htgap] at h
    calc
      _ ≤ _ := h
      _ = _ := by field_simp
  have hm : (M:ℝ) ≤ b*X := Nat.floor_le (by positivity)
  have hm' : b*X/2 ≤ (M:ℝ) := by
    have := Nat.lt_floor_add_one (b*X); change 2 ≤ b*X at hlarge
    change b*X/2 ≤ (⌊b*X⌋₊:ℝ); linarith only [this,hlarge]
  have hMp : 0 < (M:ℝ) := lt_of_lt_of_le (by positivity) hm'
  have hMX : (M:ℝ) ≤ X := hm.trans (mul_le_of_le_one_left hXp.le hb1)
  have dw : ∀ n, ‖damp (fun k => (summatoryError A c k : ℂ)) t n‖ ≤ D := by
    intro n; rw [damp_norm _ ht.le, Complex.norm_real]; exact he n
  have dw' : ∀ n, ‖damp (fun k => (summatoryError A c k : ℂ)) r n‖ ≤ D := by
    intro n; rw [damp_norm _ hr.le,Complex.norm_real]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hrt n) (norm_nonneg _)).trans (he n)
  have hF := difference_real hc hNp hXp hX2 hsHalf hs1 hsgap
    (show 1/N ≤ 1-s by linarith only [htgap,hrt,hsr]) hDn
    (real_approx (A:=A) hDp ht ht1 hs4 dw) (real_approx (A:=A) hDp hr hr1 hs8 dw')
  rw [← ha16] at hF
  have hclose : (M:ℝ)*(1-s) ≤ 1/2 := by
    calc
      _ ≤ X*(4/N) := mul_le_mul hMX hsgap (sub_nonneg.mpr hs1.le) hXp.le
      _ ≤ _ := by rw [←mul_div_assoc,div_le_iff₀ hNp]; nlinarith only [hX2,mul_nonneg hXp.le (sub_nonneg.mpr hX8)]
  let B (u : ℝ) := ∑ k ∈ Finset.range M, u^k
  have hB : (M:ℝ)/2 ≤ B s := geometricBlock_real_lower M hs.le hs1.le hclose
  have hBB : B (s^2) ≤ B s := by
    apply Finset.sum_le_sum; intro k _
    exact pow_le_pow_left₀ (sq_nonneg _) (by nlinarith only [mul_nonneg hs.le (sub_nonneg.mpr hs1.le)]) k
  have hlow := radial_parseval_lower (A:=A) M hs.le hsr hr1
  change B s * indicatorSeriesReal A s - B (s^2) * indicatorSeriesReal A (s^2) ≤ _ at hlow
  have hlow' : (M:ℝ)/2*(16*a*X) ≤ avg (fullInt A M r)-avg (fullInt A M s) := by
    apply le_trans _ hlow
    have h1 := mul_le_mul hB hF (by positivity) (Finset.sum_nonneg fun k _ => pow_nonneg hs.le k)
    have h2 := mul_le_mul_of_nonneg_right hBB (indicatorSeriesReal_nonneg A (sq_nonneg s))
    linarith only [h1,h2]
  have hDsq : D^2 ≤ a^2*M := by
    dsimp only [D]; rw [mul_pow,hW2]
    calc
      _ ≤ (a^2*(b/2))*X := mul_le_mul_of_nonneg_right hd2 hXp.le
      _ = a^2*(b*X/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hm' (sq_nonneg a)
  have herr (u : ℝ) (hu : (1-u)⁻¹ ≤ N) : (a*X)⁻¹ * (D^2/(1-u)) ≤ a*X*M := by
    rw [←div_eq_inv_mul,div_le_iff₀ (mul_pos ha hXp)]
    calc
      D^2/(1-u) ≤ D^2*N := by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hu (sq_nonneg _)
      _ ≤ (a^2*M)*N := mul_le_mul_of_nonneg_right hDsq hNp.le
      _ = _ := by rw [←hX2]; ring
  have e1 := (abs_le.1 (avg_error hc.le hDp ht ht1 (rfl:r=t^2) dw (mul_pos ha hXp) M)).2
  have e2 := (abs_le.1 (avg_error hc.le hDp hr hr1 (rfl:s=r^2) dw' (mul_pos ha hXp) M)).1
  have mm := mul_le_mul_of_nonneg_left (avg_main_diff hs.le hsr hr1 hXp hX2 hsi hdr M hMX) hc.le
  have hmb : c*(8*(M:ℝ)^2) ≤ a*X*M := by
    calc
      _ = (8*c)*(M:ℝ)*M := by ring
      _ ≤ (8*c)*(b*X)*M := by gcongr
      _ = (8*c*b)*X*M := by ring
      _ ≤ _ := by gcongr
  linarith only [hlow',e1,e2,mm,hmb,herr r hri,herr s hsi,mul_pos (mul_pos ha hXp) hMp]
end EF763

open Filter Set
open scoped BigOperators Topology Asymptotics Real
namespace EF763

lemma sharp_rep_eq (A : Set ℕ) (n : ℕ) : representationCount A n = AdditiveCombinatorics.sumRep A n := by
  classical
  unfold representationCount AdditiveCombinatorics.sumRep AdditiveCombinatorics.sumConv
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => Set.indicatorOne (R := ℕ) A x * Set.indicatorOne (R := ℕ) A y) n]
  apply Finset.sum_congr rfl
  intro k hk
  simp [indicator, Set.indicatorOne, Set.indicator]

end EF763

open EF763 in
theorem OMA.solution : type_of% @Erdos763.erdos_763.variants.montgomery_vaughan := by
  rintro ⟨A,c,hc,hlittle⟩
  have herr (n : ℕ) : summatoryError A c n =
      (∑ k ∈ Finset.range (n+1), (AdditiveCombinatorics.sumRep A k : ℝ)) - c*(n:ℝ) - c := by
    simp only [summatoryError,summatoryRepresentationCount,Nat.cast_sum,sharp_rep_eq]
    ring
  have hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ‖summatoryError A c n‖ ≤ ε*quarter n := by
    intro ε hε
    have hbound := hlittle.bound (by positivity : 0 < ε/2)
    have hconst := (quarter_top.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (c/(ε/2))
    filter_upwards [hbound,hconst] with n hn hn'
    change c/(ε/2) ≤ quarter n at hn'
    change ‖(∑ k ∈ Finset.range (n+1), (AdditiveCombinatorics.sumRep A k : ℝ)) - c*(n:ℝ)‖ ≤
        ε/2 * ‖(n:ℝ)^(1/4:ℝ)‖ at hn
    rw [← quarter_eq (Nat.cast_nonneg n),Real.norm_eq_abs (quarter n),abs_of_nonneg (show 0 ≤ quarter n from Real.sqrt_nonneg _)] at hn
    rw [herr]
    refine (norm_sub_le _ _).trans ?_
    rw [Real.norm_eq_abs c,abs_of_pos hc]
    have := (div_le_iff₀ (by positivity : 0 < ε/2)).1 hn'
    linarith
  let a := (c/(48*(c+1)))/16
  have ha : 0<a := by dsimp [a]; positivity
  have ha16 : 16*a=c/(48*(c+1)) := by dsimp [a]; ring
  let b := min 1 (a/(8*c))
  have hb : 0 < b := lt_min (by norm_num) (by positivity)
  have hb1 : b ≤ 1 := min_le_left _ _
  have hba : 8*c*b ≤ a := by
    have := (le_div_iff₀ (by positivity : 0 < 8*c)).1 (min_le_right 1 (a/(8*c)))
    linarith
  let δ := min (c/192) (a*√(b/2))
  have hd : 0 < δ := lt_min (by positivity) (by positivity)
  have hdc : 192*δ ≤ c := by
    have : δ ≤ c/192 := min_le_left _ _
    linarith
  have hd2 : δ^2 ≤ a^2*(b/2) := by
    have h : δ ≤ a*√(b/2) := min_le_right _ _
    calc
      _ ≤ (a*√(b/2))^2 := by gcongr
      _ = _ := by rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hN := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop 64
  have hX := (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (2/b)
  obtain ⟨N,he,hN',hX'⟩ := ((quarter_envelope hsmall hd).and (hN.and hX)).exists
  change 2/b ≤ √(N:ℝ) at hX'
  exact impossible_sharp hc ha hb hb1 hd ha16 hba hdc hd2 hN'
    (by simpa [mul_comm] using (div_le_iff₀ hb).1 hX') he
