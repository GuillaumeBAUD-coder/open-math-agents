import FormalConjectures.Paper.LennonPittelStableMatchings
import Mathlib


-- Reduction LennonPittel.lennon_pittel_conjecture.R2 of Lennon–Pittel conjecture on random stable matchings
-- Credit: @tatashbar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1: Gale–Shapley existence (same statement as R1.H1; true, not yet formalized).
-- H2: bounded second-moment ratio, a published theorem of Lennon–Pittel (2009), not open.
-- H3: uniformly bounded variance of log S_n, the open concentration core. Stronger than strictly
--     needed, supported by numerics (sd(log S_n) ≈ 0.46–0.61 for n ≤ 400, decreasing in n).
-- main: Paley–Zygmund (from H2) locates E[log S_n] within O(1) of log E[S_n];
--     Chebyshev (from H3) then bounds the lower tail by V / (log(1/ε_n) - O(1))^2 → 0.

open MeasureTheory Filter
open scoped Topology ENNReal

namespace OMA.R_LennonPittel_lennon_pittel_conjecture_R2

/-- Paley–Zygmund at level `M/2`, proved with a pointwise AM-GM bound (no Cauchy–Schwarz). -/
lemma pz_half {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : ∀ x, 1 ≤ f x) (C : ℝ)
    (hC : ∫ x, f x ^ 2 ∂μ ≤ C * (∫ x, f x ∂μ) ^ 2) :
    0 < C ∧ 1 / (4 * C) ≤ μ.real {x | (∫ y, f y ∂μ) / 2 ≤ f x} := by
  set M := ∫ y, f y ∂μ with hMdef
  have hM1 : 1 ≤ M := by
    have : ∫ _y : α, (1 : ℝ) ∂μ ≤ M :=
      integral_mono (Integrable.of_finite) (Integrable.of_finite) hf
    simpa using this
  have hM : 0 < M := by linarith
  have hsq1 : 1 ≤ ∫ x, f x ^ 2 ∂μ := by
    have : ∫ _y : α, (1 : ℝ) ∂μ ≤ ∫ x, f x ^ 2 ∂μ :=
      integral_mono (Integrable.of_finite) (Integrable.of_finite)
        (fun x => by have := hf x; nlinarith)
    simpa using this
  have hCpos : 0 < C := by
    by_contra! h
    have : C * M ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg _)
    linarith
  refine ⟨hCpos, ?_⟩
  set A := {x | M / 2 ≤ f x} with hA
  set lam := 2 * C * M with hlam
  have hlam_pos : 0 < lam := by positivity
  -- pointwise: f ≤ M/2 + f^2/(2 lam) + (lam/2) 1_A
  have hpt : ∀ x, f x ≤ M / 2 + f x ^ 2 / (2 * lam) + A.indicator (fun _ => lam / 2) x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      have h1 : f x ≤ f x ^ 2 / (2 * lam) + lam / 2 := by
        rw [div_add' _ _ _ (by positivity : (2 * lam) ≠ 0)]
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (f x - lam)]
      linarith
    · rw [Set.indicator_of_notMem hx]
      have : f x < M / 2 := by simpa [hA] using hx
      have : 0 ≤ f x ^ 2 / (2 * lam) := by positivity
      linarith
  have hint : M ≤ M / 2 + (∫ x, f x ^ 2 ∂μ) / (2 * lam) + lam / 2 * μ.real A := by
    have h := integral_mono (μ := μ) (Integrable.of_finite) (Integrable.of_finite) hpt
    rw [integral_add (Integrable.of_finite) (Integrable.of_finite),
      integral_add (Integrable.of_finite) (Integrable.of_finite), integral_const,
      integral_div, integral_indicator_const _ ((Set.toFinite _).measurableSet)] at h
    simpa [smul_eq_mul, mul_comm] using h
  have h2 : (∫ x, f x ^ 2 ∂μ) / (2 * lam) ≤ M / 4 := by
    rw [div_le_iff₀ (by positivity)]
    calc ∫ x, f x ^ 2 ∂μ ≤ C * M ^ 2 := hC
      _ = M / 4 * (2 * lam) := by rw [hlam]; ring
  have h3 : M / 4 ≤ C * M * μ.real A := by
    have : lam / 2 * μ.real A = C * M * μ.real A := by rw [hlam]; ring
    linarith
  rw [div_le_iff₀ (by positivity)]
  have : M / 4 ≤ M * (μ.real A * (4 * C)) / 4 := by
    calc M / 4 ≤ C * M * μ.real A := h3
      _ = M * (μ.real A * (4 * C)) / 4 := by ring
  have h4 : M * 1 ≤ M * (μ.real A * (4 * C)) := by linarith
  exact le_of_mul_le_mul_left h4 hM

/-- Chebyshev, in the form we need. -/
lemma cheb {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
    (μ : Measure α) [IsProbabilityMeasure μ] (g : α → ℝ) (L t : ℝ) (ht : 0 < t) :
    μ.real {x | t ≤ |g x - L|} ≤ (∫ x, (g x - L) ^ 2 ∂μ) / t ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have hpt : ∀ x, {x | t ≤ |g x - L|}.indicator (fun _ => t ^ 2) x ≤ (g x - L) ^ 2 := by
    intro x
    by_cases hx : x ∈ {x | t ≤ |g x - L|}
    · rw [Set.indicator_of_mem hx]
      have : t ≤ |g x - L| := hx
      have := pow_le_pow_left₀ ht.le this 2
      simpa [sq_abs] using this
    · rw [Set.indicator_of_notMem hx]; positivity
  have h := integral_mono (μ := μ) (Integrable.of_finite) (Integrable.of_finite) hpt
  rw [integral_indicator_const _ ((Set.toFinite _).measurableSet)] at h
  simpa [smul_eq_mul, mul_comm] using h

/-- The abstract tail bound: a uniform second-moment ratio and a uniform log-variance bound
give a lower-tail bound depending only on `C`, `V`, `ε`. -/
lemma tail_bound {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : ∀ x, 1 ≤ f x) (C V : ℝ)
    (hC : ∫ x, f x ^ 2 ∂μ ≤ C * (∫ x, f x ∂μ) ^ 2)
    (hV : ∫ x, (Real.log (f x) - ∫ y, Real.log (f y) ∂μ) ^ 2 ∂μ ≤ V)
    (ε : ℝ) (hε : 0 < ε) (hs : 0 < -Real.log (2 * ε) - (Real.sqrt (8 * C * V) + 1)) :
    μ.real {x | f x < ε * ∫ y, f y ∂μ} ≤
      V / (-Real.log (2 * ε) - (Real.sqrt (8 * C * V) + 1)) ^ 2 := by
  set M := ∫ y, f y ∂μ with hMdef
  set L := ∫ y, Real.log (f y) ∂μ with hLdef
  set t0 := Real.sqrt (8 * C * V) + 1 with ht0
  set s := -Real.log (2 * ε) - t0 with hsdef
  obtain ⟨hCpos, hPZ⟩ := pz_half μ f hf C hC
  have hM1 : 1 ≤ M := by
    have : ∫ _y : α, (1 : ℝ) ∂μ ≤ M :=
      integral_mono (Integrable.of_finite) (Integrable.of_finite) hf
    simpa using this
  have hV0 : 0 ≤ V := le_trans (integral_nonneg (fun _ => sq_nonneg _)) hV
  have ht0pos : 0 < t0 := by positivity
  have ht0sq : 8 * C * V < t0 ^ 2 := by
    have h := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 8 * C * V)
    have h0 := Real.sqrt_nonneg (8 * C * V)
    rw [ht0]; nlinarith
  -- Chebyshev at t0: small mass
  have hcheb0 := cheb μ (fun x => Real.log (f x)) L t0 ht0pos
  have hsmall : μ.real {x | t0 ≤ |Real.log (f x) - L|} < μ.real {x | M / 2 ≤ f x} := by
    calc μ.real {x | t0 ≤ |Real.log (f x) - L|} ≤ V / t0 ^ 2 := hcheb0.trans
            (div_le_div_of_nonneg_right hV (by positivity))
      _ < 1 / (4 * C) := by
            rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
      _ ≤ _ := hPZ
  -- so some x with M/2 ≤ f x has |log f x - L| < t0
  have hloc : Real.log (M / 2) < L + t0 := by
    by_contra! hcon
    have hsub : {x | M / 2 ≤ f x} ⊆ {x | t0 ≤ |Real.log (f x) - L|} := by
      intro x hx
      have hx' : M / 2 ≤ f x := hx
      have : Real.log (M / 2) ≤ Real.log (f x) :=
        Real.log_le_log (by positivity) hx'
      show t0 ≤ |Real.log (f x) - L|
      rw [abs_of_nonneg (by linarith)]; linarith
    exact absurd (measureReal_mono hsub) (not_le.mpr hsmall)
  -- the bad event sits inside a Chebyshev event at level s
  have hsub : {x | f x < ε * M} ⊆ {x | s ≤ |Real.log (f x) - L|} := by
    intro x hx
    have hx' : f x < ε * M := hx
    have hfx : 0 < f x := by linarith [hf x]
    have hlog : Real.log (f x) < Real.log (ε * M) := Real.log_lt_log hfx hx'
    have hsplit : Real.log (ε * M) = Real.log (2 * ε) + Real.log (M / 2) := by
      rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; ring
    show s ≤ |Real.log (f x) - L|
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [hsdef]; linarith
  calc μ.real {x | f x < ε * M} ≤ μ.real {x | s ≤ |Real.log (f x) - L|} := measureReal_mono hsub
    _ ≤ (∫ x, (Real.log (f x) - L) ^ 2 ∂μ) / s ^ 2 := cheb μ _ L s hs
    _ ≤ V / s ^ 2 := div_le_div_of_nonneg_right hV (by positivity)

open StableMarriage

/-- Every complete strict preference profile has a stable complete matching (Gale–Shapley).
Same statement as `LennonPittel.lennon_pittel_conjecture.R1.H1`. -/
def H1 : Prop := ∀ n (p : StableMarriage.Profile n), 0 < StableMarriage.numStableMatchings p

/-- Bounded second-moment ratio, `E[S_n^2] ≤ C E[S_n]^2` for all `n`.
This is a theorem of Lennon and Pittel (CPC 18 (2009), 371–421): `E[S_n^2]/E[S_n]^2 → 1 + e^{-1}/2`. -/
def H2 : Prop := ∃ C : ℝ, ∀ n,
  ∫ p, (StableMarriage.numStableMatchings p : ℝ) ^ 2 ∂(StableMarriage.uniformProfile n).toMeasure ≤
    C * StableMarriage.expectedNumStableMatchings n ^ 2

/-- The open core: `log S_n` has uniformly bounded variance (concentration of `log S_n`). -/
def H3 : Prop := ∃ V : ℝ, ∀ n,
  ∫ p, (Real.log (StableMarriage.numStableMatchings p) -
      ∫ q, Real.log (StableMarriage.numStableMatchings q) ∂(StableMarriage.uniformProfile n).toMeasure) ^ 2
    ∂(StableMarriage.uniformProfile n).toMeasure ≤ V

theorem main : H1 → H2 → H3 → type_of% @LennonPittel.lennon_pittel_conjecture := by
  intro hpos ⟨C, hC⟩ ⟨V, hV⟩ ε hεpos _hεanti hεlim
  let μ (n : ℕ) := (StableMarriage.uniformProfile n).toMeasure
  let f (n : ℕ) (p : Profile n) : ℝ := (numStableMatchings p : ℝ)
  have hf : ∀ n (p : Profile n), 1 ≤ f n p := fun n p => by
    simp only [f]; exact_mod_cast hpos n p
  set t0 := Real.sqrt (8 * C * V) + 1 with ht0
  -- the real bound tends to zero
  have hε' : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεlim, Eventually.of_forall hεpos⟩
  have h2ε : Tendsto (fun n => 2 * ε n) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => by
      have := hεpos n; show 0 < 2 * ε n; positivity⟩
    simpa using hεlim.const_mul 2
  have hs_top : Tendsto (fun n => -Real.log (2 * ε n) - t0) atTop atTop := by
    have := (Real.tendsto_log_nhdsGT_zero.comp h2ε)
    exact tendsto_atTop_add_const_right _ _ (tendsto_neg_atBot_atTop.comp this)
  have hbound : Tendsto (fun n => V / (-Real.log (2 * ε n) - t0) ^ 2) atTop (𝓝 0) := by
    have : Tendsto (fun n => (-Real.log (2 * ε n) - t0) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (two_ne_zero)).comp hs_top
    exact this.const_div_atTop V
  -- real measure of the bad event tends to zero
  have hbadR : Tendsto (fun n => (μ n).real {p | f n p < ε n * expectedNumStableMatchings n})
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    · exact Eventually.of_forall fun n => measureReal_nonneg
    · filter_upwards [hs_top.eventually_gt_atTop 0] with n hn
      exact tail_bound (μ n) (f n) (hf n) C V (hC n) (hV n) (ε n) (hεpos n) hn
  have hbad : Tendsto (fun n => μ n {p | f n p < ε n * expectedNumStableMatchings n})
      atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_ofReal hbadR)
    simp only [ENNReal.ofReal_zero] at h
    refine h.congr fun n => ?_
    exact ofReal_measureReal (measure_ne_top _ _)
  have hgood (n : ℕ) : μ n
      {p | (StableMarriage.numStableMatchings p : ℝ) ≥ ε n * StableMarriage.expectedNumStableMatchings n} =
      1 - μ n {p | f n p < ε n * StableMarriage.expectedNumStableMatchings n} := by
    have heq : {p : StableMarriage.Profile n | (StableMarriage.numStableMatchings p : ℝ) ≥
        ε n * StableMarriage.expectedNumStableMatchings n} =
        {p | f n p < ε n * StableMarriage.expectedNumStableMatchings n}ᶜ := by
      ext p; simp only [f, Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
    rw [heq, measure_compl MeasurableSpace.measurableSet_top (measure_ne_top _ _), measure_univ]
  change Tendsto (fun n => μ n _) atTop (𝓝 1)
  simp_rw [hgood]
  simpa only [Function.comp_def, tsub_zero] using
    ((ENNReal.continuous_sub_left (a := 1) (by simp)).tendsto 0).comp hbad

end OMA.R_LennonPittel_lennon_pittel_conjecture_R2
