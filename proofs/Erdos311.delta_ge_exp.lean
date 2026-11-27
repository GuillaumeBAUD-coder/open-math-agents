import FormalConjectures.ErdosProblems.«311»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Proof of `Erdos311.delta_ge_exp` via the elementary lcm lower bound and Newman's Tauberian
proof of the Prime Number Theorem upper bound.
-/

-- Problem: Erdős Problem 311 — delta ge exp
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/311.lean:70 (declaration Erdos311.delta_ge_exp)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

section Erdos311Proof

open scoped Real
open Complex Filter Topology MeasureTheory Finset

/- Part 1: Elementary lower bound `delta N ≥ 1 / lcmUpto N` -/

private lemma delta_ge_inv_lcm_aux (N : ℕ) :
    1 / ((Nat.lcmUpto N : ℕ) : ℝ) ≤ Erdos311.delta N := by
  unfold Erdos311.delta
  refine le_csInf ⟨1, one_ne_zero, ∅, empty_subset _, by simp⟩ ?_
  rintro x ⟨hx, A, hA, rfl⟩
  set L : ℕ := Nat.lcmUpto N
  have hL_pos : 0 < L := Nat.lcmUpto_pos N
  have hL_pos_real : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL_pos
  set k : ℤ := (L : ℤ) - ∑ n ∈ A, ((L / n : ℕ) : ℤ)
  have hk_cast : (k : ℝ) = (L : ℝ) * (1 - ∑ n ∈ A, (1 : ℝ) / n) := by
    simp only [k, Int.cast_sub, Int.cast_natCast, Int.cast_sum, mul_sub, mul_one, mul_sum]
    congr 1
    refine sum_congr rfl fun n hn => ?_
    have hn_mem : n ∈ Icc 1 N := hA hn
    have hn_pos : 0 < n := (mem_Icc.mp hn_mem).1
    have hn_dvd : n ∣ L := by
      simpa [L, Nat.lcmUpto] using (Finset.dvd_lcm hn_mem : id n ∣ (Icc 1 N).lcm id)
    rw [Nat.cast_div hn_dvd (Nat.cast_ne_zero.mpr hn_pos.ne'), mul_one_div]
  have hLx : (L : ℝ) * |1 - ∑ n ∈ A, (1 : ℝ) / n| = |(k : ℝ)| := by
    rw [hk_cast, abs_mul, abs_of_pos hL_pos_real]
  have hk_ne : k ≠ 0 := by
    intro hk0
    have : (L : ℝ) * |1 - ∑ n ∈ A, (1 : ℝ) / n| = 0 := by rw [hLx, hk0]; simp
    rcases mul_eq_zero.mp this with h | h
    · exact hL_pos_real.ne' h
    · exact hx h
  have hk_abs : (1 : ℝ) ≤ |(k : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
    exact_mod_cast h1
  rw [div_le_iff₀ hL_pos_real, mul_comm]
  linarith [hLx, hk_abs]

/- Part 2: Holomorphic continuation of the Laplace transform of `e^{-t} ψ(e^t) - 1` -/

private noncomputable def Phi (s : ℂ) : ℂ :=
  -deriv (DirichletCharacter.LFunctionTrivChar₁ 1) s / DirichletCharacter.LFunctionTrivChar₁ 1 s

private noncomputable def G_fun (z : ℂ) : ℂ :=
  (Phi (z + 1) - 1) / (z + 1)

private def U_dom : Set ℂ :=
  {z : ℂ | DirichletCharacter.LFunctionTrivChar₁ 1 (z + 1) ≠ 0 ∧ z + 1 ≠ 0}

private lemma isOpen_U_dom : IsOpen U_dom := by
  have hcont : Continuous (fun z : ℂ => DirichletCharacter.LFunctionTrivChar₁ 1 (z + 1)) :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).continuous.comp
      (continuous_id.add continuous_const)
  exact (isOpen_ne.preimage hcont).inter (isOpen_ne.preimage (continuous_id.add continuous_const))

private lemma re_nonneg_subset_U_dom : {z : ℂ | 0 ≤ z.re} ⊆ U_dom := by
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  have hre : 1 ≤ (z + 1).re := by simp [hz]
  have hs0 : z + 1 ≠ 0 := by
    intro h
    have : (z + 1).re = 0 := by rw [h]; simp
    linarith
  refine ⟨?_, hs0⟩
  rcases eq_or_ne (z + 1) 1 with h1 | h1
  · rw [h1]
    exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1
  · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne h1,
      DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hre)

private lemma differentiableOn_G_fun : DifferentiableOn ℂ G_fun U_dom := by
  have hL : Differentiable ℂ (DirichletCharacter.LFunctionTrivChar₁ 1) :=
    DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
  have hdL : Differentiable ℂ (deriv (DirichletCharacter.LFunctionTrivChar₁ 1)) :=
    hL.deriv
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have hadd : DifferentiableAt ℂ (fun w : ℂ => w + 1) z := differentiableAt_id.add (differentiableAt_const 1)
  have hPhi : DifferentiableAt ℂ (fun w : ℂ => Phi (w + 1)) z := by
    unfold Phi
    have h1 : DifferentiableAt ℂ (fun w : ℂ => deriv (DirichletCharacter.LFunctionTrivChar₁ 1) (w + 1)) z :=
      ((hdL (z + 1)).hasDerivAt.comp_add_const z 1).differentiableAt
    have h2 : DifferentiableAt ℂ (fun w : ℂ => DirichletCharacter.LFunctionTrivChar₁ 1 (w + 1)) z :=
      ((hL (z + 1)).hasDerivAt.comp_add_const z 1).differentiableAt
    exact h1.neg.div h2 hz.1
  exact (hPhi.sub (differentiableAt_const 1)).div hadd hz.2

private lemma G_fun_eq_LSeries {z : ℂ} (hz : 0 < z.re) :
    G_fun z = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (z + 1) / (z + 1) - 1 / z := by
  have hs_re : 1 < (z + 1).re := by simp [hz]
  have hs1 : z + 1 ≠ 1 := by
    intro h
    have : (z + 1).re = 1 := by rw [h]; simp
    linarith
  have hs0 : z + 1 ≠ 0 := by
    intro h
    have : (z + 1).re = 0 := by rw [h]; simp
    linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hzeta : riemannZeta (z + 1) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs_re.le
  have hLmod : DirichletCharacter.LFunctionTrivChar 1 = riemannZeta :=
    DirichletCharacter.LFunction_modOne_eq
  have hPhi : Phi (z + 1) = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (z + 1) - 1 / z := by
    unfold Phi
    rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs1,
      DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1,
      hLmod, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs_re]
    have hsub : z + 1 - 1 = z := add_sub_cancel_right z 1
    rw [hsub]
    field_simp [hz0, hzeta]
    ring
  unfold G_fun
  rw [hPhi]
  field_simp [hs0, hz0]
  ring

/- Part 3: Laplace transform of `f_psi` equals `G_fun` on `Re(z) > 0` -/

private noncomputable def f_psi (t : ℝ) : ℝ :=
  Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1

private lemma f_psi_measurable : Measurable f_psi := by
  unfold f_psi
  exact ((Real.continuous_exp.comp continuous_neg).measurable.mul
    (Chebyshev.psi_mono.measurable.comp Real.continuous_exp.measurable)).sub measurable_const

private lemma f_psi_abs_le {t : ℝ} : |f_psi t| ≤ Real.log 4 + 4 := by
  unfold f_psi
  have h0 : 0 ≤ Real.exp (-t) * Chebyshev.psi (Real.exp t) :=
    mul_nonneg (Real.exp_nonneg _) (Chebyshev.psi_nonneg _)
  have h1 : Real.exp (-t) * Chebyshev.psi (Real.exp t) ≤ Real.log 4 + 4 := by
    have hpsi := Chebyshev.psi_le_const_mul_self (Real.exp_nonneg t)
    calc Real.exp (-t) * Chebyshev.psi (Real.exp t)
        ≤ Real.exp (-t) * ((Real.log 4 + 4) * Real.exp t) := by
          gcongr
      _ = Real.log 4 + 4 := by
          rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> linarith

private lemma integrableOn_cexp_neg_mul_Ioi {z : ℂ} (hz : 0 < z.re) (a : ℝ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ))) (Set.Ioi a) volume := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Complex.exp (-z * (t : ℂ)))
      (volume.restrict (Set.Ioi a)) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  have hnorm : ∀ t : ℝ, ‖Complex.exp (-z * (t : ℂ))‖ = Real.exp ((-z.re) * t) := fun t => by
    rw [Complex.norm_exp]
    simp
  have hint : IntegrableOn (fun t : ℝ => Real.exp ((-z.re) * t)) (Set.Ioi a) volume :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hz) a
  exact hint.mono' hmeas (Filter.Eventually.of_forall fun t => by rw [hnorm])

private lemma integral_cexp_neg_mul_Ioi {z : ℂ} (hz : 0 < z.re) (a : ℝ) :
    ∫ t in Set.Ioi a, Complex.exp (-z * (t : ℂ)) = Complex.exp (-z * (a : ℂ)) / z := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hderiv : ∀ t ∈ Set.Ici a,
      HasDerivAt (fun x : ℝ => -Complex.exp (-z * (x : ℂ)) / z) (Complex.exp (-z * (t : ℂ))) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => -z * (x : ℂ)) (-z) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-z)
    have h2 : HasDerivAt (fun x : ℝ => Complex.exp (-z * (x : ℂ)))
        (Complex.exp (-z * (t : ℂ)) * (-z)) t := h1.cexp
    have h3 : HasDerivAt (fun x : ℝ => -Complex.exp (-z * (x : ℂ)) / z)
        (-(Complex.exp (-z * (t : ℂ)) * (-z)) / z) t := (h2.neg).div_const z
    have h4 : -(Complex.exp (-z * (t : ℂ)) * (-z)) / z = Complex.exp (-z * (t : ℂ)) := by
      rw [mul_neg, neg_neg, mul_div_cancel_right₀ _ hz0]
    exact h4 ▸ h3
  have htend : Tendsto (fun x : ℝ => -Complex.exp (-z * (x : ℂ)) / z) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : (fun x : ℝ => ‖-Complex.exp (-z * (x : ℂ)) / z‖) =
        fun x : ℝ => Real.exp ((-z.re) * x) / ‖z‖ := by
      ext x
      rw [norm_div, norm_neg, Complex.norm_exp]
      simp
    rw [hnorm]
    have hexp : Tendsto (fun x : ℝ => Real.exp ((-z.re) * x)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hz) tendsto_id)
    simpa using hexp.div_const ‖z‖
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_cexp_neg_mul_Ioi hz a) htend]
  ring

private lemma integral_psi_cexp_Ioi {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Set.Ioi (0 : ℝ), (Chebyshev.psi (Real.exp t) : ℂ) * Complex.exp (-s * (t : ℂ)) =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s / s := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  have hs_ne : s ≠ 0 := by
    intro h; rw [h] at hs0; simp at hs0
  let u : ℕ → ℝ → ℂ := fun n t =>
    if 1 ≤ n ∧ Real.log n ≤ t then (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.exp (-s * (t : ℂ))
    else 0
  have hu_eq : ∀ n : ℕ, 1 ≤ n →
      ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        u n t = (Set.Ioi (Real.log n)).indicator
          (fun t => (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.exp (-s * (t : ℂ))) t := by
    intro n hn
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn)
    have hne : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), t ≠ Real.log n := by
      refine ae_restrict_of_ae ?_
      rw [ae_iff]
      simp
    filter_upwards [ae_restrict_mem measurableSet_Ioi, hne] with t ht htn
    simp only [u, hn, true_and, Set.indicator, Set.mem_Ioi]
    by_cases hlt : Real.log n < t
    · simp [hlt, hlt.le]
    · have hle : ¬ Real.log n ≤ t := fun h => hlt (lt_of_le_of_ne h htn.symm)
      simp [hlt, hle]
  have hu_int : ∀ n : ℕ, Integrable (u n) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hu0 : u 0 = 0 := by ext t; simp [u]
      rw [hu0]
      exact integrable_zero _ _ _
    · have h1 : IntegrableOn (fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.exp (-s * (t : ℂ)))
          (Set.Ioi (Real.log n)) volume :=
        (integrableOn_cexp_neg_mul_Ioi hs0 (Real.log n)).const_mul _
      have h2 : Integrable ((Set.Ioi (Real.log n)).indicator
          (fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.exp (-s * (t : ℂ))))
          (volume.restrict (Set.Ioi (0 : ℝ))) :=
        (h1.integrable_indicator measurableSet_Ioi).restrict
      exact h2.congr (Filter.EventuallyEq.symm (hu_eq n hn))
  have hu_integral : ∀ n : ℕ,
      ∫ t in Set.Ioi (0 : ℝ), u n t =
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n / s := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [u]
    · have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn)
      have hsub : Set.Ioi (Real.log n) ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi hlog_nonneg
      rw [integral_congr_ae (hu_eq n hn), integral_indicator measurableSet_Ioi,
        Measure.restrict_restrict measurableSet_Ioi, Set.inter_eq_self_of_subset_left hsub,
        integral_const_mul, integral_cexp_neg_mul_Ioi hs0 (Real.log n)]
      rw [LSeries.term_of_ne_zero hn.ne']
      have hcpow : Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) = ((n : ℂ) ^ s)⁻¹ := by
        have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
        rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn.ne'), ← Complex.exp_neg,
          ← Complex.ofReal_natCast, ← Complex.ofReal_log hn_pos.le]
        congr 1
        ring
      rw [hcpow]
      simp [div_eq_mul_inv, mul_assoc, mul_comm]
  have hu_norm_integral : ∀ n : ℕ,
      ∫ t in Set.Ioi (0 : ℝ), ‖u n t‖ =
        ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ / s.re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [u]
    · have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn)
      have hsub : Set.Ioi (Real.log n) ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi hlog_nonneg
      have hnorm_ae : (fun t => ‖u n t‖) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
          (Set.Ioi (Real.log n)).indicator
            (fun t => ArithmeticFunction.vonMangoldt n * Real.exp ((-s.re) * t)) := by
        filter_upwards [hu_eq n hn] with t ht
        rw [ht]
        by_cases hmem : t ∈ Set.Ioi (Real.log n)
        · simp only [Set.indicator_of_mem hmem, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.norm_exp]
          simp
        · simp [Set.indicator_of_notMem hmem]
      rw [integral_congr_ae hnorm_ae, integral_indicator measurableSet_Ioi,
        Measure.restrict_restrict measurableSet_Ioi, Set.inter_eq_self_of_subset_left hsub,
        integral_const_mul]
      have hreal_int : ∫ t in Set.Ioi (Real.log (n : ℝ)), Real.exp ((-s.re) * t) =
          Real.exp ((-s.re) * Real.log (n : ℝ)) / s.re := by
        have h := congrArg Complex.re (integral_cexp_neg_mul_Ioi (z := (s.re : ℂ)) (by simpa using hs0) (Real.log n))
        have hre_int : (∫ t in Set.Ioi (Real.log (n : ℝ)), Complex.exp (-(s.re : ℂ) * (t : ℂ))).re =
            ∫ t in Set.Ioi (Real.log (n : ℝ)), Real.exp ((-s.re) * t) := by
          have hc := Complex.reCLM.integral_comp_comm (integrableOn_cexp_neg_mul_Ioi (z := (s.re : ℂ)) (by simpa using hs0) (Real.log n))
          have h1 : (∫ t in Set.Ioi (Real.log (n : ℝ)), Complex.reCLM (Complex.exp (-(s.re : ℂ) * (t : ℂ)))) =
              ∫ t in Set.Ioi (Real.log (n : ℝ)), Real.exp ((-s.re) * t) := by
            congr 1 with t
            rw [Complex.reCLM_apply,
              show -(s.re : ℂ) * (t : ℂ) = (((-s.re) * t : ℝ) : ℂ) by push_cast; ring,
              ← Complex.ofReal_exp, Complex.ofReal_re]
          rw [← h1, hc, Complex.reCLM_apply]
        rw [hre_int] at h
        rw [h, show -(s.re : ℂ) * (Real.log (n : ℝ) : ℂ) = (((-s.re) * Real.log (n : ℝ) : ℝ) : ℂ) by
          push_cast; ring, ← Complex.ofReal_exp, ← Complex.ofReal_div, Complex.ofReal_re]
      rw [hreal_int, LSeries.term_of_ne_zero hn.ne', norm_div, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.norm_natCast_cpow_of_re_ne_zero n hs0.ne']
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      rw [show Real.exp ((-s.re) * Real.log (n : ℝ)) = ((n : ℝ) ^ s.re)⁻¹ by
        rw [Real.rpow_def_of_pos hn_pos, ← Real.exp_neg]; congr 1; ring]
      ring
  have hsum_norm : Summable (fun n : ℕ => ∫ t in Set.Ioi (0 : ℝ), ‖u n t‖) := by
    simp_rw [hu_norm_integral]
    exact (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm.div_const s.re
  have htsum_eq := integral_tsum_of_summable_integral_norm hu_int hsum_norm
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ),
      ∑' n : ℕ, u n t = (Chebyshev.psi (Real.exp t) : ℂ) * Complex.exp (-s * (t : ℂ)) := by
    intro t ht
    have hsupp : ∀ n : ℕ, n ∉ Ioc 0 ⌊Real.exp t⌋₊ → u n t = 0 := by
      intro n hn
      simp only [u, ite_eq_right_iff]
      intro ⟨hn1, hlog⟩
      exfalso
      apply hn
      rw [mem_Ioc]
      refine ⟨hn1, Nat.le_floor ?_⟩
      have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
      rwa [← Real.log_le_iff_le_exp hnpos]
    rw [tsum_eq_sum hsupp]
    have hsum_eq : ∑ n ∈ Ioc 0 ⌊Real.exp t⌋₊, u n t =
        ∑ n ∈ Ioc 0 ⌊Real.exp t⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.exp (-s * (t : ℂ)) := by
      refine sum_congr rfl fun n hn => ?_
      rw [mem_Ioc] at hn
      have hlog : Real.log (n : ℝ) ≤ t := by
        rw [Real.log_le_iff_le_exp (Nat.cast_pos.mpr hn.1)]
        exact (Nat.le_floor_iff (Real.exp_nonneg t)).mp hn.2
      have hcond : 1 ≤ n ∧ Real.log (n : ℝ) ≤ t := ⟨hn.1, hlog⟩
      simp only [u, hcond, and_self, ↓reduceIte]
    rw [hsum_eq, ← sum_mul, Chebyshev.psi]
    simp
  have hcongr : ∫ t in Set.Ioi (0 : ℝ), ∑' n : ℕ, u n t =
      ∫ t in Set.Ioi (0 : ℝ), (Chebyshev.psi (Real.exp t) : ℂ) * Complex.exp (-s * (t : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => hpt t ht
  rw [← hcongr, ← htsum_eq]
  simp_rw [hu_integral, tsum_div_const]
  rfl

private lemma G_fun_eq_laplace {z : ℂ} (hz : 0 < z.re) :
    G_fun z = ∫ t in Set.Ioi (0 : ℝ), (f_psi t : ℂ) * Complex.exp (-z * (t : ℂ)) := by
  have hs : 1 < (z + 1).re := by simp [hz]
  rw [G_fun_eq_LSeries hz, ← integral_psi_cexp_Ioi hs]
  have h1 : IntegrableOn (fun t : ℝ => (Chebyshev.psi (Real.exp t) : ℂ) * Complex.exp (-(z + 1) * (t : ℂ)))
      (Set.Ioi (0 : ℝ)) volume := by
    have hmeas : AEStronglyMeasurable
        (fun t : ℝ => (Chebyshev.psi (Real.exp t) : ℂ) * Complex.exp (-(z + 1) * (t : ℂ)))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      ((Complex.continuous_ofReal.measurable.comp
        (Chebyshev.psi_mono.measurable.comp Real.continuous_exp.measurable)).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable).aestronglyMeasurable
    have hdom : IntegrableOn (fun t : ℝ => (Real.log 4 + 4) * Real.exp ((-z.re) * t)) (Set.Ioi (0 : ℝ)) volume :=
      (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hz) 0).const_mul _
    refine hdom.mono' hmeas (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Chebyshev.psi_nonneg _), Complex.norm_exp]
    have hre : (-(z + 1) * (t : ℂ)).re = (-z.re) * t - t := by simp; ring
    rw [hre, Real.exp_sub]
    calc Chebyshev.psi (Real.exp t) * (Real.exp ((-z.re) * t) / Real.exp t)
        = (Chebyshev.psi (Real.exp t) / Real.exp t) * Real.exp ((-z.re) * t) := by ring
      _ ≤ (Real.log 4 + 4) * Real.exp ((-z.re) * t) := by
          gcongr
          rw [div_le_iff₀ (Real.exp_pos t)]
          exact Chebyshev.psi_le_const_mul_self (Real.exp_nonneg t)
  have h2 : IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ))) (Set.Ioi (0 : ℝ)) volume :=
    integrableOn_cexp_neg_mul_Ioi hz 0
  have h2val : ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-z * (t : ℂ)) = 1 / z := by
    simpa using integral_cexp_neg_mul_Ioi hz 0
  rw [← h2val, ← integral_sub h1 h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [f_psi, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_one, sub_mul, one_mul]
  congr 1
  rw [mul_comm (Complex.exp (-(t : ℂ))), mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/- Part 4: Newman's Analytic Theorem -/

private noncomputable def laplaceTrunc (f : ℝ → ℝ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..T, (f t : ℂ) * Complex.exp (-z * (t : ℂ))

private lemma differentiable_laplaceTrunc {f : ℝ → ℝ} {B : ℝ} (hB : 0 < B)
    (hf_meas : Measurable f) (hf_bound : ∀ t ≥ 0, |f t| ≤ B) {T : ℝ} (hT : 0 ≤ T) :
    Differentiable ℂ (laplaceTrunc f T) := by
  intro z₀
  let F : ℂ → ℝ → ℂ := fun z t => (f t : ℂ) * Complex.exp (-z * (t : ℂ))
  let F' : ℂ → ℝ → ℂ := fun z t => -(t : ℂ) * (f t : ℂ) * Complex.exp (-z * (t : ℂ))
  let s : Set ℂ := Metric.ball z₀ 1
  let bound : ℝ → ℝ := fun _ => T * B * Real.exp ((‖z₀‖ + 1) * T)
  have hs : s ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ one_pos
  have hF_meas : ∀ z : ℂ, AEStronglyMeasurable (F z) (volume.restrict (Set.uIoc 0 T)) := fun z =>
    ((Complex.continuous_ofReal.measurable.comp hf_meas).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable).aestronglyMeasurable
  have hF_int : IntervalIntegrable (F z₀) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    have hdom : IntegrableOn (fun _ : ℝ => B * Real.exp (‖z₀‖ * T)) (Set.Ioc 0 T) volume :=
      integrableOn_const (by simp)
    refine hdom.mono' (by simpa [Set.uIoc_of_le hT] using hF_meas z₀) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-z₀ * (t : ℂ)).re ≤ ‖z₀‖ * T := by
      have : (-z₀ * (t : ℂ)).re = -z₀.re * t := by simp
      rw [this]
      calc -z₀.re * t ≤ |z₀.re| * t := mul_le_mul_of_nonneg_right (neg_le_abs z₀.re) ht.1.le
        _ ≤ ‖z₀‖ * t := mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z₀) ht.1.le
        _ ≤ ‖z₀‖ * T := mul_le_mul_of_nonneg_left ht.2 (norm_nonneg z₀)
    exact mul_le_mul (hf_bound t ht.1.le) (Real.exp_le_exp.mpr hre) (Real.exp_nonneg _) hB.le
  have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict (Set.uIoc 0 T)) :=
    (((Complex.continuous_ofReal.measurable.neg).mul (Complex.continuous_ofReal.measurable.comp hf_meas)).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable).aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 T → ∀ z ∈ s, ‖F' z t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall fun t ht z hz => ?_
    rw [Set.uIoc_of_le hT] at ht
    have hz_norm : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have : ‖z - z₀‖ < 1 := by simpa [Complex.dist_eq] using Metric.mem_ball.mp hz
      have htri := norm_add_le (z - z₀) z₀
      simp only [sub_add_cancel] at htri
      linarith
    simp only [F', bound, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht.1, Complex.norm_exp]
    have hre : (-z * (t : ℂ)).re ≤ (‖z₀‖ + 1) * T := by
      have : (-z * (t : ℂ)).re = -z.re * t := by simp
      rw [this]
      calc -z.re * t ≤ |z.re| * t := mul_le_mul_of_nonneg_right (neg_le_abs z.re) ht.1.le
        _ ≤ ‖z‖ * t := mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) ht.1.le
        _ ≤ (‖z₀‖ + 1) * T := mul_le_mul hz_norm ht.2 ht.1.le (by positivity)
    have h1 : t * |f t| ≤ T * B := mul_le_mul ht.2 (hf_bound t ht.1.le) (abs_nonneg _) hT
    exact mul_le_mul h1 (Real.exp_le_exp.mpr hre) (Real.exp_nonneg _) (mul_nonneg hT hB.le)
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 T → ∀ z ∈ s, HasDerivAt (fun w => F w t) (F' z t) z := by
    refine Filter.Eventually.of_forall fun t _ z _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => -w * (t : ℂ)) (-(t : ℂ)) z := by
      simpa using (hasDerivAt_id z).neg.mul_const (t : ℂ)
    have h2 : HasDerivAt (fun w : ℂ => (f t : ℂ) * Complex.exp (-w * (t : ℂ)))
        ((f t : ℂ) * (Complex.exp (-z * (t : ℂ)) * -(t : ℂ))) z := h1.cexp.const_mul _
    convert h2 using 1
    simp only [F']
    ring
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas h_bound intervalIntegrable_const h_diff).2.differentiableAt

private lemma exists_delta_rect_subset {U : Set ℂ} (hU_open : IsOpen U)
    (hU_sub : {z : ℂ | 0 ≤ z.re} ⊆ U) {R : ℝ} (hR : 0 < R) :
    ∃ δ > 0, (Set.Icc (-δ) R) ×ℂ (Set.Icc (-R) R) ⊆ U := by
  let K : Set ℂ := Set.Icc (0 : ℝ) R ×ℂ Set.Icc (-R) R
  have hK_compact : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hK_sub : K ⊆ U := fun z hz => hU_sub hz.1.1
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := hK_compact.exists_thickening_subset_open hU_open hK_sub
  refine ⟨δ / 2, half_pos hδ_pos, fun z hz => hδ_sub ?_⟩
  rw [Metric.mem_thickening_iff]
  rcases le_or_gt 0 z.re with hre | hre
  · exact ⟨z, ⟨⟨hre, hz.1.2⟩, hz.2⟩, by simp [hδ_pos]⟩
  · refine ⟨(z.im : ℂ) * I, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simp [hR.le]
      · simpa using hz.2
    · rw [Complex.dist_eq]
      have hsub : z - (z.im : ℂ) * I = (z.re : ℂ) := by
        apply Complex.ext <;> simp
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hre]
      linarith [hz.1.1]

/-- Key algebraic norm identity on the circle `z = R * exp(θ * I)`:
`(I * z) * (1 / z + z / R^2) = I * exp(θ * I) * (2 * cos θ)`. -/
private lemma circle_kernel_eq (R θ : ℝ) (hR : 0 < R) :
    (I * (R * Complex.exp ((θ : ℂ) * I))) *
      (1 / (R * Complex.exp ((θ : ℂ) * I)) + (R * Complex.exp ((θ : ℂ) * I)) / (R : ℂ) ^ 2) =
    I * Complex.exp ((θ : ℂ) * I) * (2 * (Real.cos θ : ℂ)) := by
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hexp0 : Complex.exp ((θ : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  have hcos : (2 : ℂ) * (Real.cos θ : ℂ) = Complex.exp ((θ : ℂ) * I) + Complex.exp (-((θ : ℂ) * I)) := by
    rw [Complex.ofReal_cos, Complex.cos]
    have : -((θ : ℂ) * I) = -(θ : ℂ) * I := by ring
    rw [this]
    ring
  rw [hcos]
  field_simp [hR0, hexp0]
  rw [mul_add, ← sq, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, add_comm]

private lemma norm_circle_kernel (R θ : ℝ) (hR : 0 < R) :
    ‖(I * (R * Complex.exp ((θ : ℂ) * I))) *
      (1 / (R * Complex.exp ((θ : ℂ) * I)) + (R * Complex.exp ((θ : ℂ) * I)) / (R : ℂ) ^ 2)‖ =
    2 * |Real.cos θ| := by
  rw [circle_kernel_eq R θ hR, norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs]

private lemma integral_comp_exp_complex {g : ℝ → ℂ} {a b : ℝ}
    (hg : ContinuousOn g (Set.uIcc (Real.exp a) (Real.exp b))) :
    (∫ x : ℝ in a..b, g (Real.exp x) * (Real.exp x : ℂ)) =
      ∫ u : ℝ in Real.exp a..Real.exp b, g u := by
  have hge_cont : ContinuousOn (fun x : ℝ => g (Real.exp x) * (Real.exp x : ℂ)) (Set.uIcc a b) := by
    refine (hg.comp Real.continuous_exp.continuousOn fun x hx => ?_).mul
      (Complex.continuous_ofReal.comp Real.continuous_exp).continuousOn
    rcases le_total a b with hab | hba
    · rw [Set.uIcc_of_le hab] at hx
      rw [Set.uIcc_of_le (Real.exp_le_exp.mpr hab)]
      exact ⟨Real.exp_le_exp.mpr hx.1, Real.exp_le_exp.mpr hx.2⟩
    · rw [Set.uIcc_of_ge hba] at hx
      rw [Set.uIcc_of_ge (Real.exp_le_exp.mpr hba)]
      exact ⟨Real.exp_le_exp.mpr hx.1, Real.exp_le_exp.mpr hx.2⟩
  have hint1 : IntervalIntegrable (fun x : ℝ => g (Real.exp x) * (Real.exp x : ℂ)) volume a b :=
    hge_cont.intervalIntegrable
  have hint2 : IntervalIntegrable g volume (Real.exp a) (Real.exp b) := hg.intervalIntegrable
  have himg : Real.exp '' Set.uIcc a b ⊆ Set.uIcc (Real.exp a) (Real.exp b) := by
    rintro _ ⟨x, hx, rfl⟩
    rcases le_total a b with hab | hba
    · rw [Set.uIcc_of_le hab] at hx
      rw [Set.uIcc_of_le (Real.exp_le_exp.mpr hab)]
      exact ⟨Real.exp_le_exp.mpr hx.1, Real.exp_le_exp.mpr hx.2⟩
    · rw [Set.uIcc_of_ge hba] at hx
      rw [Set.uIcc_of_ge (Real.exp_le_exp.mpr hba)]
      exact ⟨Real.exp_le_exp.mpr hx.1, Real.exp_le_exp.mpr hx.2⟩
  apply Complex.ext
  · have hre1 := Complex.reCLM.intervalIntegral_comp_comm hint1
    have hre2 := Complex.reCLM.intervalIntegral_comp_comm hint2
    simp only [Complex.reCLM_apply] at hre1 hre2
    rw [← hre1, ← hre2]
    have hcomp := intervalIntegral.integral_comp_mul_deriv'
      (f := Real.exp) (f' := Real.exp) (g := fun u => (g u).re)
      (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
      ((Complex.continuous_re.comp_continuousOn hg).mono himg)
    refine Eq.trans ?_ hcomp
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp [Complex.exp_ofReal_re, mul_comm]
  · have him1 := Complex.imCLM.intervalIntegral_comp_comm hint1
    have him2 := Complex.imCLM.intervalIntegral_comp_comm hint2
    simp only [Complex.imCLM_apply] at him1 him2
    rw [← him1, ← him2]
    have hcomp := intervalIntegral.integral_comp_mul_deriv'
      (f := Real.exp) (f' := Real.exp) (g := fun u => (g u).im)
      (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
      ((Complex.continuous_im.comp_continuousOn hg).mono himg)
    refine Eq.trans ?_ hcomp
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp [Complex.exp_ofReal_re, mul_comm]

private lemma inv_left_rect_integral {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    -(∫ x : ℝ in (-δ)..0, (1 : ℂ) / ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) +
      I * (∫ y : ℝ in (-R)..R, (1 : ℂ) / (((-δ : ℝ) : ℂ) + (y : ℂ) * I)) +
      (∫ x : ℝ in (-δ)..0, (1 : ℂ) / ((x : ℂ) + (R : ℂ) * I)) = -(I * (π : ℂ)) := by
  have hbot : ∫ x : ℝ in (-δ)..0, (1 : ℂ) / ((x : ℂ) + ((-R : ℝ) : ℂ) * I) =
      Complex.log (-(((0 : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * I)) -
      Complex.log (-(((-δ : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * I)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => Complex.log (-((x : ℂ) + ((-R : ℝ) : ℂ) * I))) (fun x _ => ?_) ?_
    · have h1 : HasDerivAt (fun t : ℝ => -((t : ℂ) + ((-R : ℝ) : ℂ) * I)) (-1 : ℂ) x :=
        ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const (((-R : ℝ) : ℂ) * I)).fun_neg
      have hslit : -((x : ℂ) + ((-R : ℝ) : ℂ) * I) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]
        right
        simp [hR.ne']
      have h2 := h1.clog_real hslit
      have heq : (-1 : ℂ) / -((x : ℂ) + ((-R : ℝ) : ℂ) * I) = (1 : ℂ) / ((x : ℂ) + ((-R : ℝ) : ℂ) * I) := by
        rw [div_neg, neg_div, neg_neg]
      exact heq ▸ h2
    · refine ContinuousOn.intervalIntegrable ?_
      intro x _
      refine (continuousAt_const.div ?_ ?_).continuousWithinAt
      · exact (Complex.continuous_ofReal.add continuous_const).continuousAt
      · intro h; have := congrArg Complex.im h; simp [hR.ne'] at this
  have htop : ∫ x : ℝ in (-δ)..0, (1 : ℂ) / ((x : ℂ) + (R : ℂ) * I) =
      Complex.log (-(((0 : ℝ) : ℂ) + (R : ℂ) * I)) -
      Complex.log (-(((-δ : ℝ) : ℂ) + (R : ℂ) * I)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => Complex.log (-((x : ℂ) + (R : ℂ) * I))) (fun x _ => ?_) ?_
    · have h1 : HasDerivAt (fun t : ℝ => -((t : ℂ) + (R : ℂ) * I)) (-1 : ℂ) x :=
        ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((R : ℂ) * I)).fun_neg
      have hslit : -((x : ℂ) + (R : ℂ) * I) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]
        right
        simp [hR.ne']
      have h2 := h1.clog_real hslit
      have heq : (-1 : ℂ) / -((x : ℂ) + (R : ℂ) * I) = (1 : ℂ) / ((x : ℂ) + (R : ℂ) * I) := by
        rw [div_neg, neg_div, neg_neg]
      exact heq ▸ h2
    · refine ContinuousOn.intervalIntegrable ?_
      intro x _
      refine (continuousAt_const.div ?_ ?_).continuousWithinAt
      · exact (Complex.continuous_ofReal.add continuous_const).continuousAt
      · intro h; have := congrArg Complex.im h; simp [hR.ne'] at this
  have hleft : I * (∫ y : ℝ in (-R)..R, (1 : ℂ) / (((-δ : ℝ) : ℂ) + (y : ℂ) * I)) =
      Complex.log (-(((-δ : ℝ) : ℂ) + (R : ℂ) * I)) -
      Complex.log (-(((-δ : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * I)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => Complex.log (-(((-δ : ℝ) : ℂ) + (y : ℂ) * I))) (fun y _ => ?_) ?_
    · have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) (1 * I) y :=
        (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
      have h1 : HasDerivAt (fun t : ℝ => -(((-δ : ℝ) : ℂ) + (t : ℂ) * I)) (-I) y := by
        simpa using (h0.const_add ((-δ : ℝ) : ℂ)).fun_neg
      have hslit : -(((-δ : ℝ) : ℂ) + (y : ℂ) * I) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]
        left
        simp [hδ]
      have h2 := h1.clog_real hslit
      have heq : (-I) / -(((-δ : ℝ) : ℂ) + (y : ℂ) * I) =
          I * ((1 : ℂ) / (((-δ : ℝ) : ℂ) + (y : ℂ) * I)) := by
        rw [div_neg, neg_div, neg_neg, mul_one_div]
      exact heq ▸ h2
    · refine ContinuousOn.intervalIntegrable ?_
      intro y _
      refine (continuousAt_const.mul (continuousAt_const.div ?_ ?_)).continuousWithinAt
      · exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
      · intro h; have := congrArg Complex.re h; simp [hδ.ne'] at this
  rw [hbot, htop, hleft]
  have htel :
      -(Complex.log (-(((0 : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * I)) -
        Complex.log (-(((-δ : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * I))) +
      (Complex.log (-(((-δ : ℝ) : ℂ) + (R : ℂ) * I)) -
        Complex.log (-(((-δ : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * I))) +
      (Complex.log (-(((0 : ℝ) : ℂ) + (R : ℂ) * I)) -
        Complex.log (-(((-δ : ℝ) : ℂ) + (R : ℂ) * I))) =
      Complex.log (-((R : ℂ) * I)) - Complex.log ((R : ℂ) * I) := by
    simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_neg, neg_mul, neg_neg]
    ring
  rw [htel]
  have hlog_pos : Complex.log ((R : ℂ) * I) = (Real.log R : ℂ) + (π / 2 : ℝ) * I := by
    rw [Complex.log_ofReal_mul hR I_ne_zero, Complex.log_I]
    push_cast
    ring
  have hlog_neg : Complex.log (-((R : ℂ) * I)) = (Real.log R : ℂ) - (π / 2 : ℝ) * I := by
    rw [show -((R : ℂ) * I) = (R : ℂ) * (-I) by ring,
      Complex.log_ofReal_mul hR (neg_ne_zero.mpr I_ne_zero), Complex.log_neg_I]
    push_cast
    ring
  rw [hlog_pos, hlog_neg]
  push_cast
  ring

private lemma contour_formula_G {G : ℂ → ℂ} {U : Set ℂ} {R δ T : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hU_open : IsOpen U)
    (hrect : Set.Icc (-δ) R ×ℂ Set.Icc (-R) R ⊆ U)
    (hG_diff : DifferentiableOn ℂ G U) :
    let H_G : ℂ → ℂ := fun z => G z * Complex.exp (z * (T : ℂ)) * (1 / z + z / (R : ℂ) ^ 2)
    (2 * (π : ℂ) * I) * G 0 =
      (∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * H_G (R * Complex.exp ((θ : ℂ) * I))) -
      (-(∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) +
        I * (∫ y : ℝ in (-R)..R, H_G (((-δ : ℝ) : ℂ) + (y : ℂ) * I)) +
        (∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + (R : ℂ) * I))) := by
  intro H_G
  have h0_mem : (0 : ℂ) ∈ U := hrect ⟨⟨by simp; linarith, by simp; exact hR.le⟩,
    ⟨by simp; linarith, by simp; exact hR.le⟩⟩
  let g_exp : ℂ → ℂ := fun w => G w * Complex.exp (w * (T : ℂ))
  have hg_diff : DifferentiableOn ℂ g_exp U :=
    hG_diff.mul ((differentiable_id.mul (differentiable_const (T : ℂ))).cexp.differentiableOn)
  have hg0_diff : DifferentiableAt ℂ g_exp 0 := hg_diff.differentiableAt (hU_open.mem_nhds h0_mem)
  let F : ℂ → ℂ := Function.update
    (fun z => (g_exp z - G 0) / z + g_exp z * z / (R : ℂ) ^ 2) 0 (deriv g_exp 0)
  have hF_of_ne : ∀ z : ℂ, z ≠ 0 → F z = H_G z - G 0 / z := by
    intro z hz
    simp only [F, Function.update_of_ne hz, H_G, g_exp]
    field_simp [hz, Complex.ofReal_ne_zero.mpr hR.ne']
    ring
  have hF_cont : ContinuousOn F U := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · refine ContinuousAt.continuousWithinAt ?_
      have h1 : Tendsto (fun w : ℂ => (g_exp w - g_exp 0) / w) (𝓝[≠] 0) (𝓝 (deriv g_exp 0)) :=
        hg0_diff.hasDerivAt.tendsto_slope_zero.congr fun w => by
          simp [zero_add, smul_eq_mul, inv_mul_eq_div]
      have h2 : Tendsto (fun w : ℂ => g_exp w * w / (R : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 0) := by
        have hc : ContinuousAt (fun w : ℂ => g_exp w * w / (R : ℂ) ^ 2) 0 :=
          (hg0_diff.continuousAt.mul continuousAt_id).div_const _
        have hc' : Tendsto (fun w : ℂ => g_exp w * w / (R : ℂ) ^ 2) (𝓝[≠] 0)
            (𝓝 (g_exp 0 * 0 / (R : ℂ) ^ 2)) := hc.continuousWithinAt
        simpa using hc'
      have h3 : Tendsto (fun w : ℂ => (g_exp w - G 0) / w + g_exp w * w / (R : ℂ) ^ 2)
          (𝓝[≠] 0) (𝓝 (deriv g_exp 0 + 0)) := by
        have h1' : Tendsto (fun w : ℂ => (g_exp w - G 0) / w) (𝓝[≠] 0) (𝓝 (deriv g_exp 0)) := by
          simpa [g_exp] using h1
        exact h1'.add h2
      rw [add_zero] at h3
      refine continuousWithinAt_compl_self.mp ?_
      have hF0 : F 0 = deriv g_exp 0 := by simp [F]
      rw [ContinuousWithinAt, hF0]
      refine h3.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      simp only [F, Function.update_of_ne hw]
    · refine ContinuousAt.continuousWithinAt ?_
      have hg_at : DifferentiableAt ℂ g_exp z := hg_diff.differentiableAt (hU_open.mem_nhds hz)
      have hcont_at : ContinuousAt (fun w => (g_exp w - G 0) / w + g_exp w * w / (R : ℂ) ^ 2) z :=
        ((hg_at.continuousAt.sub continuousAt_const).div continuousAt_id hz0).add
          ((hg_at.continuousAt.mul continuousAt_id).div_const _)
      refine hcont_at.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
      simp only [F, Function.update_of_ne hw]
  have hF_diff : ∀ z ∈ U \ {0}, DifferentiableAt ℂ F z := by
    intro z ⟨hzU, hz0⟩
    have hg_at : DifferentiableAt ℂ g_exp z := hg_diff.differentiableAt (hU_open.mem_nhds hzU)
    have hd : DifferentiableAt ℂ (fun w => (g_exp w - G 0) / w + g_exp w * w / (R : ℂ) ^ 2) z :=
      ((hg_at.sub (differentiableAt_const _)).div differentiableAt_id hz0).add
        ((hg_at.mul differentiableAt_id).div_const _)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
    simp only [F, Function.update_of_ne hw]
  -- Step 1: Left rectangle `[-δ, 0] × [-R, R]`
  have hrect_left :
      (∫ x : ℝ in (-δ)..0, F ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) -
      (∫ x : ℝ in (-δ)..0, F ((x : ℂ) + (R : ℂ) * I)) +
      I * (∫ y : ℝ in (-R)..R, F (((0 : ℝ) : ℂ) + (y : ℂ) * I)) -
      I * (∫ y : ℝ in (-R)..R, F (((-δ : ℝ) : ℂ) + (y : ℂ) * I)) = 0 := by
    let z₁ : ℂ := ⟨-δ, -R⟩
    let w₁ : ℂ := ⟨0, R⟩
    have hsub1 : Set.uIcc z₁.re w₁.re ×ℂ Set.uIcc z₁.im w₁.im ⊆ U := by
      intro z hz
      apply hrect
      simp only [z₁, w₁, Set.uIcc_of_le (show -δ ≤ 0 by linarith),
        Set.uIcc_of_le (show -R ≤ R by linarith)] at hz
      exact ⟨⟨hz.1.1, hz.1.2.trans hR.le⟩, hz.2⟩
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable F z₁ w₁ {0}
      (Set.countable_singleton 0) (hF_cont.mono hsub1) (fun z hz => hF_diff z ⟨hsub1 ⟨?_, ?_⟩, hz.2⟩)
    · simpa [z₁, w₁, smul_eq_mul] using h
    · exact Set.Ioo_subset_Icc_self (by simpa [Set.uIcc] using hz.1.1)
    · exact Set.Ioo_subset_Icc_self (by simpa [Set.uIcc] using hz.1.2)
  -- Step 2: Right semicircle via polar rectangle `[log ε, log R] × [-π/2, π/2]`, sending `ε → 0⁺`
  have hsemi :
      (∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * F (R * Complex.exp ((θ : ℂ) * I))) =
      I * (∫ y : ℝ in (-R)..R, F ((y : ℂ) * I)) := by
    -- For each `ε ∈ (0, R)`, Cauchy-Goursat on `[log ε, log R] × [-π/2, π/2]` applied to `w ↦ F (exp w) * exp w`
    have h_eps : ∀ ε : ℝ, 0 < ε → ε < R →
        (∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * F (R * Complex.exp ((θ : ℂ) * I))) -
        (∫ θ : ℝ in (-π / 2)..(π / 2), (I * (ε * Complex.exp ((θ : ℂ) * I))) * F (ε * Complex.exp ((θ : ℂ) * I))) =
        I * (∫ y : ℝ in (-R)..(-ε), F ((y : ℂ) * I)) + I * (∫ y : ℝ in ε..R, F ((y : ℂ) * I)) := by
      intro ε hε hεR
      let z₂ : ℂ := ⟨Real.log ε, -π / 2⟩
      let w₂ : ℂ := ⟨Real.log R, π / 2⟩
      let g_pol : ℂ → ℂ := fun w => F (Complex.exp w) * Complex.exp w
      have hpol_mem : ∀ w ∈ Set.uIcc z₂.re w₂.re ×ℂ Set.uIcc z₂.im w₂.im, Complex.exp w ∈ U \ {0} := by
        intro w hw
        have hre_le : Real.log ε ≤ Real.log R := Real.log_le_log hε hεR.le
        have him_le : -π / 2 ≤ π / 2 := by linarith [Real.pi_pos]
        simp only [z₂, w₂, Set.uIcc_of_le hre_le, Set.uIcc_of_le him_le] at hw
        refine ⟨hrect ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, Complex.exp_ne_zero w⟩
        · have hcos : 0 ≤ Real.cos w.im := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hw.2.1], hw.2.2⟩
          rw [Complex.exp_re]
          linarith [mul_nonneg (Real.exp_nonneg w.re) hcos]
        · rw [Complex.exp_re]
          calc Real.exp w.re * Real.cos w.im ≤ Real.exp w.re * 1 :=
                mul_le_mul_of_nonneg_left (Real.cos_le_one _) (Real.exp_nonneg _)
            _ ≤ Real.exp (Real.log R) := by rw [mul_one]; exact Real.exp_le_exp.mpr hw.1.2
            _ = R := Real.exp_log hR
        · rw [Complex.exp_im]
          have h1 : -1 ≤ Real.sin w.im := Real.neg_one_le_sin _
          have h2 : Real.exp w.re ≤ R := (Real.exp_le_exp.mpr hw.1.2).trans_eq (Real.exp_log hR)
          nlinarith [Real.exp_nonneg w.re]
        · rw [Complex.exp_im]
          have h1 : Real.sin w.im ≤ 1 := Real.sin_le_one _
          have h2 : Real.exp w.re ≤ R := (Real.exp_le_exp.mpr hw.1.2).trans_eq (Real.exp_log hR)
          nlinarith [Real.exp_nonneg w.re]
      have hpol_diff : DifferentiableOn ℂ g_pol (Set.uIcc z₂.re w₂.re ×ℂ Set.uIcc z₂.im w₂.im) := by
        intro w hw
        have hm := hpol_mem w hw
        exact ((hF_diff _ hm).comp w (Complex.differentiableAt_exp)).mul
          Complex.differentiableAt_exp |>.differentiableWithinAt
      have hcg := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g_pol z₂ w₂ hpol_diff
      simp only [z₂, w₂, smul_eq_mul] at hcg
      -- Rewrite each of the 4 sides
      have hbot : (∫ x : ℝ in Real.log ε..Real.log R, g_pol ((x : ℂ) + ((-π / 2 : ℝ) : ℂ) * I)) =
          -I * (∫ y : ℝ in (-R)..(-ε), F ((y : ℂ) * I)) := by
        have hstep1 : (∫ x : ℝ in Real.log ε..Real.log R, g_pol ((x : ℂ) + ((-π / 2 : ℝ) : ℂ) * I)) =
            ∫ x : ℝ in Real.log ε..Real.log R, (-I) * (F ((-Real.exp x : ℝ) * I) * (Real.exp x : ℂ)) := by
          refine intervalIntegral.integral_congr fun x _ => ?_
          simp only [g_pol, Complex.exp_add]
          have hpi : Complex.exp (((-π / 2 : ℝ) : ℂ) * I) = -I := by
            rw [show (((-π / 2 : ℝ) : ℂ) * I) = -((π / 2 : ℂ) * I) by push_cast; ring,
              Complex.exp_neg, Complex.exp_pi_div_two_mul_I, inv_I]
          rw [hpi, ← Complex.ofReal_exp]
          push_cast
          ring
        rw [hstep1, intervalIntegral.integral_const_mul]
        congr 1
        have hsub_exp : (∫ x : ℝ in Real.log ε..Real.log R, F ((-Real.exp x : ℝ) * I) * (Real.exp x : ℂ)) =
            ∫ u : ℝ in ε..R, F ((-u : ℝ) * I) := by
          have hcomp := integral_comp_exp_complex (g := fun u : ℝ => F ((-u : ℝ) * I))
            (a := Real.log ε) (b := Real.log R) (by
              rw [Real.exp_log hε, Real.exp_log hR, Set.uIcc_of_le hεR.le]
              refine hF_cont.comp ((Complex.continuous_ofReal.comp continuous_neg).mul continuous_const).continuousOn
                fun u hu => hrect ⟨⟨by simp; linarith, by simp; exact hR.le⟩, ?_⟩
              exact ⟨by simp; linarith [hu.2], by simp; linarith [hu.1]⟩)
          simpa [Real.exp_log hε, Real.exp_log hR] using hcomp
        rw [hsub_exp]
        have hneg := intervalIntegral.integral_comp_neg (f := fun y : ℝ => F ((y : ℂ) * I)) (a := ε) (b := R)
        simpa using hneg
      have htop : (∫ x : ℝ in Real.log ε..Real.log R, g_pol ((x : ℂ) + ((π / 2 : ℝ) : ℂ) * I)) =
          I * (∫ y : ℝ in ε..R, F ((y : ℂ) * I)) := by
        have hstep1 : (∫ x : ℝ in Real.log ε..Real.log R, g_pol ((x : ℂ) + ((π / 2 : ℝ) : ℂ) * I)) =
            ∫ x : ℝ in Real.log ε..Real.log R, I * (F ((Real.exp x : ℝ) * I) * (Real.exp x : ℂ)) := by
          refine intervalIntegral.integral_congr fun x _ => ?_
          simp only [g_pol, Complex.exp_add]
          have hpi : Complex.exp (((π / 2 : ℝ) : ℂ) * I) = I := by
            rw [Complex.exp_mul_I]
            simp
          rw [hpi, ← Complex.ofReal_exp]
          ring
        rw [hstep1, intervalIntegral.integral_const_mul]
        congr 1
        have hcomp := integral_comp_exp_complex (g := fun u : ℝ => F ((u : ℂ) * I))
          (a := Real.log ε) (b := Real.log R) (by
            rw [Real.exp_log hε, Real.exp_log hR, Set.uIcc_of_le hεR.le]
            refine hF_cont.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
              fun u hu => hrect ⟨⟨by simp; linarith, by simp; exact hR.le⟩, ?_⟩
            exact ⟨by simp; linarith [hu.1], by simp; exact hu.2⟩)
        simpa [Real.exp_log hε, Real.exp_log hR] using hcomp
      have hright : I * (∫ θ : ℝ in (-π / 2)..(π / 2), g_pol ((Real.log R : ℂ) + (θ : ℂ) * I)) =
          ∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * F (R * Complex.exp ((θ : ℂ) * I)) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        simp only [g_pol, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hR]
        ring
      have hleft : I * (∫ θ : ℝ in (-π / 2)..(π / 2), g_pol ((Real.log ε : ℂ) + (θ : ℂ) * I)) =
          ∫ θ : ℝ in (-π / 2)..(π / 2), (I * (ε * Complex.exp ((θ : ℂ) * I))) * F (ε * Complex.exp ((θ : ℂ) * I)) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        simp only [g_pol, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hε]
        ring
      rw [hbot, htop, hright, hleft] at hcg
      linear_combination hcg
    -- Take limit as `ε → 0⁺`
    have hK_comp : IsCompact (Set.Icc (-δ) R ×ℂ Set.Icc (-R) R) := isCompact_Icc.reProdIm isCompact_Icc
    obtain ⟨M, hM⟩ := hK_comp.exists_bound_of_continuousOn (hF_cont.mono hrect)
    have hM_nonneg : 0 ≤ M := by
      have h0 := hM 0 ⟨⟨by simp; linarith, by simp; exact hR.le⟩,
        ⟨by simp; linarith, by simp; exact hR.le⟩⟩
      exact (norm_nonneg _).trans h0
    have hcont_axis : ContinuousOn (fun y : ℝ => F ((y : ℂ) * I)) (Set.Icc (-R) R) := by
      refine hF_cont.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn fun y hy => ?_
      apply hrect
      exact ⟨⟨by simp; linarith, by simp; exact hR.le⟩, by simpa using hy⟩
    have hint_axis : IntervalIntegrable (fun y : ℝ => F ((y : ℂ) * I)) volume (-R) R :=
      (hcont_axis.mono (by rw [Set.uIcc_of_le (by linarith)])).intervalIntegrable
    have hdiff_bound : ∀ ε : ℝ, 0 < ε → ε < R →
        ‖(∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * F (R * Complex.exp ((θ : ℂ) * I))) -
          I * (∫ y : ℝ in (-R)..R, F ((y : ℂ) * I))‖ ≤ (π + 2) * M * ε := by
      intro ε hε hεR
      have hsplit1 : (∫ y : ℝ in (-R)..R, F ((y : ℂ) * I)) =
          (∫ y : ℝ in (-R)..(-ε), F ((y : ℂ) * I)) +
          (∫ y : ℝ in (-ε)..ε, F ((y : ℂ) * I)) +
          (∫ y : ℝ in ε..R, F ((y : ℂ) * I)) := by
        have hint_a : IntervalIntegrable (fun y : ℝ => F ((y : ℂ) * I)) volume (-R) (-ε) :=
          hint_axis.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
            (by rw [Set.uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩))
        have hint_b : IntervalIntegrable (fun y : ℝ => F ((y : ℂ) * I)) volume (-ε) ε :=
          hint_axis.mono_set (Set.uIcc_subset_uIcc
            (by rw [Set.uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩)
            (by rw [Set.uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩))
        have hint_c : IntervalIntegrable (fun y : ℝ => F ((y : ℂ) * I)) volume ε R :=
          hint_axis.mono_set (Set.uIcc_subset_uIcc
            (by rw [Set.uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩)
            Set.right_mem_uIcc)
        have hint_ab : IntervalIntegrable (fun y : ℝ => F ((y : ℂ) * I)) volume (-R) ε :=
          hint_axis.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
            (by rw [Set.uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩))
        have h1 := intervalIntegral.integral_add_adjacent_intervals hint_a hint_b
        have h2 := intervalIntegral.integral_add_adjacent_intervals hint_ab hint_c
        rw [← h2, ← h1]
      have heq :
          (∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * F (R * Complex.exp ((θ : ℂ) * I))) -
          I * (∫ y : ℝ in (-R)..R, F ((y : ℂ) * I)) =
          (∫ θ : ℝ in (-π / 2)..(π / 2), (I * (ε * Complex.exp ((θ : ℂ) * I))) * F (ε * Complex.exp ((θ : ℂ) * I))) -
          I * (∫ y : ℝ in (-ε)..ε, F ((y : ℂ) * I)) := by
        rw [hsplit1]
        linear_combination h_eps ε hε hεR
      rw [heq]
      have hnorm1 : ‖∫ θ : ℝ in (-π / 2)..(π / 2),
          (I * (ε * Complex.exp ((θ : ℂ) * I))) * F (ε * Complex.exp ((θ : ℂ) * I))‖ ≤ M * ε * π := by
        have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := M * ε)
          (a := -π / 2) (b := π / 2) (f := fun θ : ℝ =>
            (I * (ε * Complex.exp ((θ : ℂ) * I))) * F (ε * Complex.exp ((θ : ℂ) * I)))
          (fun θ hθ => by
            rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
            rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
              Real.norm_of_nonneg hε.le, Complex.norm_exp_ofReal_mul_I, mul_one]
            have hmem : (ε : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ Set.Icc (-δ) R ×ℂ Set.Icc (-R) R := by
              refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
              · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
                  Complex.exp_ofReal_mul_I_re]
                have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩
                linarith [mul_nonneg hε.le hcos]
              · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
                  Complex.exp_ofReal_mul_I_re]
                nlinarith [Real.cos_le_one θ]
              · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
                  Complex.exp_ofReal_mul_I_im]
                nlinarith [Real.neg_one_le_sin θ]
              · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
                  Complex.exp_ofReal_mul_I_im]
                nlinarith [Real.sin_le_one θ]
            have hFle := hM _ hmem
            nlinarith)
        calc _ ≤ M * ε * |π / 2 - -π / 2| := hb
          _ = M * ε * π := by
              rw [show π / 2 - -π / 2 = π by ring, abs_of_pos Real.pi_pos]
      have hnorm2 : ‖I * (∫ y : ℝ in (-ε)..ε, F ((y : ℂ) * I))‖ ≤ 2 * M * ε := by
        rw [norm_mul, Complex.norm_I, one_mul]
        have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := M)
          (a := -ε) (b := ε) (f := fun y : ℝ => F ((y : ℂ) * I))
          (fun y hy => by
            rw [Set.uIoc_of_le (by linarith)] at hy
            refine hM _ ⟨⟨?_, ?_⟩, ?_⟩
            · simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
                Complex.ofReal_im, Complex.I_im, zero_mul, sub_self]
              linarith
            · simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
                Complex.ofReal_im, Complex.I_im, zero_mul, sub_self]
              exact hR.le
            · exact ⟨by simp; linarith [hy.1], by simp; linarith [hy.2]⟩)
        calc _ ≤ M * |ε - -ε| := hb
          _ = 2 * M * ε := by
              rw [show ε - -ε = 2 * ε by ring, abs_of_pos (by linarith)]
              ring
      calc _ ≤ ‖∫ θ : ℝ in (-π / 2)..(π / 2),
              (I * (ε * Complex.exp ((θ : ℂ) * I))) * F (ε * Complex.exp ((θ : ℂ) * I))‖ +
            ‖I * (∫ y : ℝ in (-ε)..ε, F ((y : ℂ) * I))‖ := norm_sub_le _ _
        _ ≤ M * ε * π + 2 * M * ε := add_le_add hnorm1 hnorm2
        _ = (π + 2) * M * ε := by ring
    apply sub_eq_zero.mp
    rw [← norm_eq_zero]
    refine le_antisymm ?_ (norm_nonneg _)
    by_contra! hpos
    set c := ‖(∫ θ : ℝ in (-π / 2)..(π / 2),
        (I * (R * Complex.exp ((θ : ℂ) * I))) * F (R * Complex.exp ((θ : ℂ) * I))) -
      I * (∫ y : ℝ in (-R)..R, F ((y : ℂ) * I))‖
    let ε := min (R / 2) (c / (2 * ((π + 2) * M + 1)))
    have hε_pos : 0 < ε := by
      refine lt_min (half_pos hR) (div_pos hpos ?_)
      have : 0 ≤ (π + 2) * M := mul_nonneg (by linarith [Real.pi_pos]) hM_nonneg
      linarith
    have hεR : ε < R := (min_le_left _ _).trans_lt (half_lt_self hR)
    have hle := hdiff_bound ε hε_pos hεR
    have hε_le : ε ≤ c / (2 * ((π + 2) * M + 1)) := min_le_right _ _
    have hden_pos : 0 < 2 * ((π + 2) * M + 1) := by
      have : 0 ≤ (π + 2) * M := mul_nonneg (by linarith [Real.pi_pos]) hM_nonneg
      linarith
    have hlt : (π + 2) * M * ε < c := by
      calc (π + 2) * M * ε ≤ (π + 2) * M * (c / (2 * ((π + 2) * M + 1))) :=
            mul_le_mul_of_nonneg_left hε_le (mul_nonneg (by linarith [Real.pi_pos]) hM_nonneg)
        _ < ((π + 2) * M + 1) * (c / (2 * ((π + 2) * M + 1))) :=
            mul_lt_mul_of_pos_right (by linarith) (div_pos hpos hden_pos)
        _ = c / 2 := by field_simp [hden_pos.ne']
        _ < c := half_lt_self hpos
    linarith
  -- Step 3: Combine `hsemi` and `hrect_left` and peel off `G 0 / z`
  have hF_eq :
      (∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * F (R * Complex.exp ((θ : ℂ) * I))) =
      -(∫ x : ℝ in (-δ)..0, F ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) +
      I * (∫ y : ℝ in (-R)..R, F (((-δ : ℝ) : ℂ) + (y : ℂ) * I)) +
      (∫ x : ℝ in (-δ)..0, F ((x : ℂ) + (R : ℂ) * I)) := by
    have h0 : I * (∫ y : ℝ in (-R)..R, F (((0 : ℝ) : ℂ) + (y : ℂ) * I)) =
        I * (∫ y : ℝ in (-R)..R, F ((y : ℂ) * I)) := by simp
    rw [h0] at hrect_left
    linear_combination hsemi + hrect_left
  -- Rewrite each integral of `F` as integral of `H_G` minus `G 0 * integral of (1/z)`
  have hH_cont : ContinuousOn H_G (U \ {0}) := by
    intro z ⟨hzU, hz0⟩
    refine ContinuousAt.continuousWithinAt ?_
    have hG_at : ContinuousAt G z := (hG_diff.differentiableAt (hU_open.mem_nhds hzU)).continuousAt
    exact (hG_at.mul ((continuous_id.mul continuous_const).cexp.continuousAt)).mul
      ((continuousAt_const.div continuousAt_id hz0).add (continuousAt_id.div_const _))
  have hinv_cont : ContinuousOn (fun z : ℂ => G 0 / z) (U \ {0}) := fun z hz =>
    (continuousAt_const.div continuousAt_id hz.2).continuousWithinAt
  have hsemi_split :
      (∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * F (R * Complex.exp ((θ : ℂ) * I))) =
      (∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * H_G (R * Complex.exp ((θ : ℂ) * I))) -
      I * (π : ℂ) * G 0 := by
    have hcongr : ∀ θ ∈ Set.uIcc (-π / 2) (π / 2),
        (I * (R * Complex.exp ((θ : ℂ) * I))) * F (R * Complex.exp ((θ : ℂ) * I)) =
        (I * (R * Complex.exp ((θ : ℂ) * I))) * H_G (R * Complex.exp ((θ : ℂ) * I)) - I * G 0 := by
      intro θ _
      have hz0 : (R : ℂ) * Complex.exp ((θ : ℂ) * I) ≠ 0 :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Complex.exp_ne_zero _)
      rw [hF_of_ne _ hz0, mul_sub]
      congr 1
      have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
      have hexp0 : Complex.exp ((θ : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
      field_simp [hR0, hexp0]
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub]
    · simp only [intervalIntegral.integral_const, Complex.real_smul]
      have : (π / 2 - -π / 2 : ℝ) = π := by ring
      rw [this]
      ring
    · refine ContinuousOn.intervalIntegrable ?_
      have hmap : Continuous (fun θ : ℝ => (R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
        continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
      refine (continuous_const.mul hmap).continuousOn.mul (hH_cont.comp hmap.continuousOn fun θ hθ => ?_)
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
      refine ⟨hrect ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩,
        mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Complex.exp_ne_zero _)⟩
      · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.exp_ofReal_mul_I_re]
        linarith [mul_nonneg hR.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩)]
      · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.exp_ofReal_mul_I_re]
        nlinarith [Real.cos_le_one θ]
      · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          Complex.exp_ofReal_mul_I_im]
        nlinarith [Real.neg_one_le_sin θ]
      · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          Complex.exp_ofReal_mul_I_im]
        nlinarith [Real.sin_le_one θ]
    · exact intervalIntegrable_const
  have hbot_split :
      (∫ x : ℝ in (-δ)..0, F ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) =
      (∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) -
      G 0 * (∫ x : ℝ in (-δ)..0, (1 : ℂ) / ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) := by
    have hne : ∀ x : ℝ, (x : ℂ) + ((-R : ℝ) : ℂ) * I ≠ 0 := fun x h => by
      have := congrArg Complex.im h; simp [hR.ne'] at this
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun x _ => ?_
      rw [hF_of_ne _ (hne x), mul_one_div]
    · refine ContinuousOn.intervalIntegrable ?_
      refine hH_cont.comp (Complex.continuous_ofReal.add continuous_const).continuousOn fun x hx => ?_
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact ⟨hrect ⟨⟨by simpa using hx.1, by simp; linarith [hx.2]⟩,
        ⟨by simp, by simp; linarith⟩⟩, hne x⟩
    · refine (ContinuousOn.intervalIntegrable ?_).const_mul _
      intro x _
      exact (continuousAt_const.div (Complex.continuous_ofReal.add continuous_const).continuousAt
        (hne x)).continuousWithinAt
  have htop_split :
      (∫ x : ℝ in (-δ)..0, F ((x : ℂ) + (R : ℂ) * I)) =
      (∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + (R : ℂ) * I)) -
      G 0 * (∫ x : ℝ in (-δ)..0, (1 : ℂ) / ((x : ℂ) + (R : ℂ) * I)) := by
    have hne : ∀ x : ℝ, (x : ℂ) + (R : ℂ) * I ≠ 0 := fun x h => by
      have := congrArg Complex.im h; simp [hR.ne'] at this
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun x _ => ?_
      rw [hF_of_ne _ (hne x), mul_one_div]
    · refine ContinuousOn.intervalIntegrable ?_
      refine hH_cont.comp (Complex.continuous_ofReal.add continuous_const).continuousOn fun x hx => ?_
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact ⟨hrect ⟨⟨by simpa using hx.1, by simp; linarith [hx.2]⟩,
        ⟨by simp; linarith, by simp⟩⟩, hne x⟩
    · refine (ContinuousOn.intervalIntegrable ?_).const_mul _
      intro x _
      exact (continuousAt_const.div (Complex.continuous_ofReal.add continuous_const).continuousAt
        (hne x)).continuousWithinAt
  have hleft_split :
      (∫ y : ℝ in (-R)..R, F (((-δ : ℝ) : ℂ) + (y : ℂ) * I)) =
      (∫ y : ℝ in (-R)..R, H_G (((-δ : ℝ) : ℂ) + (y : ℂ) * I)) -
      G 0 * (∫ y : ℝ in (-R)..R, (1 : ℂ) / (((-δ : ℝ) : ℂ) + (y : ℂ) * I)) := by
    have hne : ∀ y : ℝ, ((-δ : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := fun y h => by
      have := congrArg Complex.re h; simp [hδ.ne'] at this
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun y _ => ?_
      rw [hF_of_ne _ (hne y), mul_one_div]
    · refine ContinuousOn.intervalIntegrable ?_
      refine hH_cont.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
        fun y hy => ?_
      rw [Set.uIcc_of_le (by linarith)] at hy
      exact ⟨hrect ⟨⟨by simp, by simp; linarith⟩, by simpa using hy⟩, hne y⟩
    · refine (ContinuousOn.intervalIntegrable ?_).const_mul _
      intro y _
      exact (continuousAt_const.div
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
        (hne y)).continuousWithinAt
  rw [hsemi_split, hbot_split, htop_split, hleft_split] at hF_eq
  have hinv := inv_left_rect_integral hR hδ
  linear_combination -hF_eq + G 0 * hinv

private lemma circle_formula_laplaceTrunc {f : ℝ → ℝ} {B R T : ℝ}
    (hB : 0 < B) (hR : 0 < R) (hT : 0 ≤ T)
    (hf_meas : Measurable f) (hf_bound : ∀ t ≥ 0, |f t| ≤ B) :
    let H_g : ℂ → ℂ := fun z => laplaceTrunc f T z * Complex.exp (z * (T : ℂ)) * (1 / z + z / (R : ℂ) ^ 2)
    (2 * (π : ℂ) * I) * laplaceTrunc f T 0 =
      (∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * H_g (R * Complex.exp ((θ : ℂ) * I))) +
      (∫ θ : ℝ in (π / 2)..(3 * π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * H_g (R * Complex.exp ((θ : ℂ) * I))) := by
  intro H_g
  let P : ℂ → ℂ := fun z => laplaceTrunc f T z * Complex.exp (z * (T : ℂ)) * (1 + z ^ 2 / (R : ℂ) ^ 2)
  have hP_diff : Differentiable ℂ P :=
    ((differentiable_laplaceTrunc hB hf_meas hf_bound hT).mul
      ((differentiable_id.mul (differentiable_const (T : ℂ))).cexp)).mul
      ((differentiable_const 1).add ((differentiable_id.pow 2).div_const _))
  have hcauchy := Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
    (c := 0) (f := P) hR Set.countable_empty hP_diff.continuous.continuousOn
    (fun z _ => hP_diff z)
  have hP0 : P 0 = laplaceTrunc f T 0 := by simp [P]
  rw [hP0] at hcauchy
  simp only [smul_eq_mul, sub_zero] at hcauchy
  -- Unfold `circleIntegral`
  let φ : ℝ → ℂ := fun θ => (I * (R * Complex.exp ((θ : ℂ) * I))) * H_g (R * Complex.exp ((θ : ℂ) * I))
  have hcircle_eq : (∮ z in C(0, R), z⁻¹ * P z) = ∫ θ : ℝ in (0 : ℝ)..(2 * π), φ θ := by
    unfold circleIntegral
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hz0 : (R : ℂ) * Complex.exp ((θ : ℂ) * I) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Complex.exp_ne_zero _)
    have hmap : circleMap 0 R θ = (R : ℂ) * Complex.exp ((θ : ℂ) * I) := by simp [circleMap]
    have hderiv : deriv (circleMap 0 R) θ = (R : ℂ) * Complex.exp ((θ : ℂ) * I) * I := by
      simp [deriv_circleMap, circleMap]
    rw [smul_eq_mul, hderiv, hmap]
    simp only [P, φ, H_g]
    field_simp [hz0, Complex.ofReal_ne_zero.mpr hR.ne']
  have hφ_per : Function.Periodic φ (2 * π) := by
    intro θ
    simp only [φ]
    have hexp : Complex.exp (((θ + 2 * π : ℝ) : ℂ) * I) = Complex.exp ((θ : ℂ) * I) := by
      rw [Complex.ofReal_add, add_mul, Complex.exp_add]
      have : ((2 * π : ℝ) : ℂ) * I = 2 * (π : ℂ) * I := by push_cast; ring
      rw [this, Complex.exp_two_pi_mul_I, mul_one]
    rw [hexp]
  have hφ_cont : Continuous φ := by
    have hmap : Continuous (fun θ : ℝ => (R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
      continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
    have hmap_ne : ∀ θ : ℝ, (R : ℂ) * Complex.exp ((θ : ℂ) * I) ≠ 0 := fun θ =>
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Complex.exp_ne_zero _)
    have hg_cont : Continuous (laplaceTrunc f T) :=
      (differentiable_laplaceTrunc hB hf_meas hf_bound hT).continuous
    refine (continuous_const.mul hmap).mul ?_
    exact ((hg_cont.comp hmap).mul
      (Complex.continuous_exp.comp (hmap.mul continuous_const))).mul
      ((continuous_const.div hmap hmap_ne).add (hmap.div_const _))
  have hshift : (∫ θ : ℝ in (0 : ℝ)..(2 * π), φ θ) = ∫ θ : ℝ in (-π / 2)..(3 * π / 2), φ θ := by
    have h := hφ_per.intervalIntegral_add_eq (-π / 2) 0
    simpa [show -π / 2 + 2 * π = 3 * π / 2 by ring] using h.symm
  have hsplit : (∫ θ : ℝ in (-π / 2)..(3 * π / 2), φ θ) =
      (∫ θ : ℝ in (-π / 2)..(π / 2), φ θ) + (∫ θ : ℝ in (π / 2)..(3 * π / 2), φ θ) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hφ_cont.intervalIntegrable _ _) (hφ_cont.intervalIntegrable _ _)).symm
  rw [← hcauchy, hcircle_eq, hshift, hsplit]

private lemma newman_tauberian
    {f : ℝ → ℝ} {B : ℝ} (hB : 0 < B)
    (hf_meas : Measurable f)
    (hf_bound : ∀ t ≥ 0, |f t| ≤ B)
    {G : ℂ → ℂ} {U : Set ℂ} (hU_open : IsOpen U)
    (hU_sub : {z : ℂ | 0 ≤ z.re} ⊆ U)
    (hG_diff : DifferentiableOn ℂ G U)
    (hG_lap : ∀ z : ℂ, 0 < z.re →
      G z = ∫ t in Set.Ioi (0 : ℝ), (f t : ℂ) * Complex.exp (-z * (t : ℂ))) :
    Tendsto (fun T : ℝ => laplaceTrunc f T 0) atTop (𝓝 (G 0)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  -- Choose `R > 0` so that `2 * B / R < η / 2`
  let R : ℝ := 4 * B / η + 1
  have hR : 0 < R := by positivity
  have hBR : 2 * B / R < η / 2 := by
    rw [div_lt_iff₀ hR]
    have h1 : 4 * B / η < R := by simp [R]
    have : 2 * B = (η / 2) * (4 * B / η) := by field_simp [hη.ne']; ring
    rw [this]
    exact mul_lt_mul_of_pos_left h1 (half_pos hη)
  -- Choose `δ > 0` such that `[-δ, R] × [-R, R] ⊆ U`
  obtain ⟨δ, hδ, hrect⟩ := exists_delta_rect_subset hU_open hU_sub hR
  -- Uniform bound `M` on `G(z) * (1/z + z/R^2)` along the three segments of `L_rect`
  let K_base : ℂ → ℂ := fun z => G z * (1 / z + z / (R : ℂ) ^ 2)
  have hK_cont : ContinuousOn K_base (U \ {0}) := by
    intro z ⟨hzU, hz0⟩
    exact ((hG_diff.differentiableAt (hU_open.mem_nhds hzU)).continuousAt.mul
      ((continuousAt_const.div continuousAt_id hz0).add (continuousAt_id.div_const _))).continuousWithinAt
  have hbot_cont : ContinuousOn (fun x : ℝ => K_base ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) (Set.Icc (-δ) 0) := by
    refine hK_cont.comp (Complex.continuous_ofReal.add continuous_const).continuousOn fun x hx => ?_
    refine ⟨hrect ⟨⟨by simpa using hx.1, by simp; linarith [hx.2]⟩, ⟨by simp, by simp; linarith⟩⟩, ?_⟩
    intro h; have := congrArg Complex.im h; simp [hR.ne'] at this
  have htop_cont : ContinuousOn (fun x : ℝ => K_base ((x : ℂ) + (R : ℂ) * I)) (Set.Icc (-δ) 0) := by
    refine hK_cont.comp (Complex.continuous_ofReal.add continuous_const).continuousOn fun x hx => ?_
    refine ⟨hrect ⟨⟨by simpa using hx.1, by simp; linarith [hx.2]⟩, ⟨by simp; linarith, by simp⟩⟩, ?_⟩
    intro h; have := congrArg Complex.im h; simp [hR.ne'] at this
  have hleft_cont : ContinuousOn (fun y : ℝ => K_base (((-δ : ℝ) : ℂ) + (y : ℂ) * I)) (Set.Icc (-R) R) := by
    refine hK_cont.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      fun y hy => ?_
    refine ⟨hrect ⟨⟨by simp, by simp; linarith⟩, by simpa using hy⟩, ?_⟩
    intro h; have := congrArg Complex.re h; simp [hδ.ne'] at this
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hbot_cont
  obtain ⟨M₂, hM₂⟩ := isCompact_Icc.exists_bound_of_continuousOn htop_cont
  obtain ⟨M₃, hM₃⟩ := isCompact_Icc.exists_bound_of_continuousOn hleft_cont
  let M : ℝ := max 1 (max M₁ (max M₂ M₃))
  have hM_pos : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hM₁_le : ∀ x ∈ Set.Icc (-δ) 0, ‖K_base ((x : ℂ) + ((-R : ℝ) : ℂ) * I)‖ ≤ M := fun x hx =>
    (hM₁ x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hM₂_le : ∀ x ∈ Set.Icc (-δ) 0, ‖K_base ((x : ℂ) + (R : ℂ) * I)‖ ≤ M := fun x hx =>
    (hM₂ x hx).trans (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  have hM₃_le : ∀ y ∈ Set.Icc (-R) R, ‖K_base (((-δ : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ M := fun y hy =>
    (hM₃ y hy).trans (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  -- Main estimate for any `T > 0`
  have hmain : ∀ T : ℝ, 0 < T →
      ‖G 0 - laplaceTrunc f T 0‖ ≤ 2 * B / R + (M / π) * (R * Real.exp (-δ * T) + 1 / T) := by
    intro T hT
    let H_G : ℂ → ℂ := fun z => G z * Complex.exp (z * (T : ℂ)) * (1 / z + z / (R : ℂ) ^ 2)
    let H_g : ℂ → ℂ := fun z => laplaceTrunc f T z * Complex.exp (z * (T : ℂ)) * (1 / z + z / (R : ℂ) ^ 2)
    have hG_eq := contour_formula_G (T := T) hR hδ hU_open hrect hG_diff
    have hg_eq := circle_formula_laplaceTrunc hB hR hT.le hf_meas hf_bound
    have hsub_eq :
        (2 * (π : ℂ) * I) * (G 0 - laplaceTrunc f T 0) =
        ((∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * H_G (R * Complex.exp ((θ : ℂ) * I))) -
         (∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * H_g (R * Complex.exp ((θ : ℂ) * I)))) -
        (∫ θ : ℝ in (π / 2)..(3 * π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * H_g (R * Complex.exp ((θ : ℂ) * I))) -
        (-(∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) +
          I * (∫ y : ℝ in (-R)..R, H_G (((-δ : ℝ) : ℂ) + (y : ℂ) * I)) +
          (∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + (R : ℂ) * I))) := by
      linear_combination hG_eq - hg_eq
    -- Bound Term 1: right semicircle `θ ∈ [-π/2, π/2]`
    have hterm1 :
        ‖(∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * H_G (R * Complex.exp ((θ : ℂ) * I))) -
         (∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * H_g (R * Complex.exp ((θ : ℂ) * I)))‖ ≤
        2 * π * B / R := by
      have hmap : Continuous (fun θ : ℝ => (R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
        continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
      have hmap_ne : ∀ θ : ℝ, (R : ℂ) * Complex.exp ((θ : ℂ) * I) ≠ 0 := fun θ =>
        mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Complex.exp_ne_zero _)
      have hG_int : IntervalIntegrable
          (fun θ : ℝ => (I * (R * Complex.exp ((θ : ℂ) * I))) * H_G (R * Complex.exp ((θ : ℂ) * I)))
          volume (-π / 2) (π / 2) := by
        refine ContinuousOn.intervalIntegrable ?_
        have hH_cont : ContinuousOn H_G (U \ {0}) := fun z ⟨hzU, hz0⟩ =>
          (((hG_diff.differentiableAt (hU_open.mem_nhds hzU)).continuousAt.mul
            ((continuous_id.mul continuous_const).cexp.continuousAt)).mul
            ((continuousAt_const.div continuousAt_id hz0).add (continuousAt_id.div_const _))).continuousWithinAt
        refine (continuous_const.mul hmap).continuousOn.mul (hH_cont.comp hmap.continuousOn fun θ hθ => ?_)
        rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
        refine ⟨hrect ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hmap_ne θ⟩
        · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
            Complex.exp_ofReal_mul_I_re]
          linarith [mul_nonneg hR.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩)]
        · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
            Complex.exp_ofReal_mul_I_re]
          nlinarith [Real.cos_le_one θ]
        · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
            Complex.exp_ofReal_mul_I_im]
          nlinarith [Real.neg_one_le_sin θ]
        · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
            Complex.exp_ofReal_mul_I_im]
          nlinarith [Real.sin_le_one θ]
      have hg_int : IntervalIntegrable
          (fun θ : ℝ => (I * (R * Complex.exp ((θ : ℂ) * I))) * H_g (R * Complex.exp ((θ : ℂ) * I)))
          volume (-π / 2) (π / 2) := by
        have hcont : Continuous
            (fun θ : ℝ => (I * (R * Complex.exp ((θ : ℂ) * I))) * H_g (R * Complex.exp ((θ : ℂ) * I))) :=
          (continuous_const.mul hmap).mul
            ((((differentiable_laplaceTrunc hB hf_meas hf_bound hT.le).continuous.comp hmap).mul
              (Complex.continuous_exp.comp (hmap.mul continuous_const))).mul
              ((continuous_const.div hmap hmap_ne).add (hmap.div_const _)))
        exact hcont.intervalIntegrable _ _
      rw [← intervalIntegral.integral_sub hG_int hg_int]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 * B / R)
        (a := -π / 2) (b := π / 2)
        (f := fun θ : ℝ =>
          (I * (R * Complex.exp ((θ : ℂ) * I))) * H_G (R * Complex.exp ((θ : ℂ) * I)) -
          (I * (R * Complex.exp ((θ : ℂ) * I))) * H_g (R * Complex.exp ((θ : ℂ) * I)))
        (fun θ hθ => ?_)
      · calc _ ≤ (2 * B / R) * |π / 2 - -π / 2| := hb
          _ = 2 * π * B / R := by
              rw [show π / 2 - -π / 2 = π by ring, abs_of_pos Real.pi_pos]
              ring
      · rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
        set z : ℂ := (R : ℂ) * Complex.exp ((θ : ℂ) * I)
        have hfact :
            (I * z) * H_G z - (I * z) * H_g z =
            (G z - laplaceTrunc f T z) * Complex.exp (z * (T : ℂ)) *
              ((I * z) * (1 / z + z / (R : ℂ) ^ 2)) := by
          simp only [H_G, H_g]; ring
        rw [hfact, norm_mul, norm_mul, norm_circle_kernel R θ hR]
        rcases eq_or_lt_of_le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩) with hcos0 | hcos_pos
        · rw [← hcos0, abs_zero, mul_zero, mul_zero]
          positivity
        · have hz_re : z.re = R * Real.cos θ := by
            simp [z, Complex.mul_re, Complex.exp_ofReal_mul_I_re]
          have hz_re_pos : 0 < z.re := by rw [hz_re]; positivity
          have htail : G z - laplaceTrunc f T z =
              ∫ t in Set.Ioi T, (f t : ℂ) * Complex.exp (-z * (t : ℂ)) := by
            rw [hG_lap z hz_re_pos, laplaceTrunc, intervalIntegral.integral_of_le hT.le]
            have hunion : Set.Ioi (0 : ℝ) = Set.Ioc 0 T ∪ Set.Ioi T := by
              ext t
              simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
              constructor
              · intro ht
                rcases le_or_gt t T with hle | hgt
                · exact Or.inl ⟨ht, hle⟩
                · exact Or.inr hgt
              · rintro (⟨ht, _⟩ | ht)
                · exact ht
                · exact hT.trans ht
            have hdisj : Disjoint (Set.Ioc (0 : ℝ) T) (Set.Ioi T) :=
              Set.disjoint_left.mpr fun t ht1 ht2 => not_lt_of_ge ht1.2 ht2
            have hint_all : IntegrableOn (fun t : ℝ => (f t : ℂ) * Complex.exp (-z * (t : ℂ)))
                (Set.Ioi (0 : ℝ)) volume := by
              have hmeas : AEStronglyMeasurable (fun t : ℝ => (f t : ℂ) * Complex.exp (-z * (t : ℂ)))
                  (volume.restrict (Set.Ioi (0 : ℝ))) :=
                ((Complex.continuous_ofReal.measurable.comp hf_meas).mul
                  (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable).aestronglyMeasurable
              have hdom : IntegrableOn (fun t : ℝ => B * Real.exp ((-z.re) * t)) (Set.Ioi (0 : ℝ)) volume :=
                (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hz_re_pos) 0).const_mul B
              refine hdom.mono' hmeas ?_
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
              have hre : (-z * (t : ℂ)).re = (-z.re) * t := by simp
              rw [hre]
              exact mul_le_mul_of_nonneg_right (hf_bound t ht.le) (Real.exp_nonneg _)
            rw [hunion, setIntegral_union hdisj measurableSet_Ioi
              (hint_all.mono_set (by rw [hunion]; exact Set.subset_union_left))
              (hint_all.mono_set (by rw [hunion]; exact Set.subset_union_right)),
              add_sub_cancel_left]
          have htail_norm : ‖G z - laplaceTrunc f T z‖ ≤ B * Real.exp (-z.re * T) / z.re := by
            rw [htail]
            have hdom : IntegrableOn (fun t : ℝ => B * Real.exp ((-z.re) * t)) (Set.Ioi T) volume :=
              (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hz_re_pos) T).const_mul B
            have hle : ‖∫ t in Set.Ioi T, (f t : ℂ) * Complex.exp (-z * (t : ℂ))‖ ≤
                ∫ t in Set.Ioi T, B * Real.exp ((-z.re) * t) := by
              refine (norm_integral_le_integral_norm _).trans ?_
              refine setIntegral_mono_on ?_ hdom measurableSet_Ioi fun t ht => ?_
              · have hmeas : AEStronglyMeasurable (fun t : ℝ => (f t : ℂ) * Complex.exp (-z * (t : ℂ)))
                    (volume.restrict (Set.Ioi T)) :=
                  ((Complex.continuous_ofReal.measurable.comp hf_meas).mul
                    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable).aestronglyMeasurable
                exact (hdom.mono' hmeas (by
                    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
                    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
                    have : (-z * (u : ℂ)).re = (-z.re) * u := by simp
                    rw [this]
                    exact mul_le_mul_of_nonneg_right (hf_bound u (hT.trans hu).le) (Real.exp_nonneg _))).norm
              · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
                have : (-z * (t : ℂ)).re = (-z.re) * t := by simp
                rw [this]
                exact mul_le_mul_of_nonneg_right (hf_bound t (hT.trans ht).le) (Real.exp_nonneg _)
            have hreal_int : ∫ t in Set.Ioi T, B * Real.exp ((-z.re) * t) =
                B * Real.exp (-z.re * T) / z.re := by
              rw [integral_const_mul]
              have h := congrArg Complex.re
                (integral_cexp_neg_mul_Ioi (z := (z.re : ℂ)) (by simpa using hz_re_pos) T)
              have hre_int : (∫ t in Set.Ioi T, Complex.exp (-(z.re : ℂ) * (t : ℂ))).re =
                  ∫ t in Set.Ioi T, Real.exp ((-z.re) * t) := by
                have hc := Complex.reCLM.integral_comp_comm
                  (integrableOn_cexp_neg_mul_Ioi (z := (z.re : ℂ)) (by simpa using hz_re_pos) T)
                have h1 : (∫ t in Set.Ioi T, Complex.reCLM (Complex.exp (-(z.re : ℂ) * (t : ℂ)))) =
                    ∫ t in Set.Ioi T, Real.exp ((-z.re) * t) := by
                  congr 1 with t
                  rw [Complex.reCLM_apply,
                    show -(z.re : ℂ) * (t : ℂ) = (((-z.re) * t : ℝ) : ℂ) by push_cast; ring,
                    ← Complex.ofReal_exp, Complex.ofReal_re]
                rw [← h1, hc, Complex.reCLM_apply]
              rw [hre_int] at h
              rw [h, show -(z.re : ℂ) * (T : ℂ) = (((-z.re) * T : ℝ) : ℂ) by push_cast; ring,
                ← Complex.ofReal_exp, ← Complex.ofReal_div, Complex.ofReal_re]
              ring
            exact hle.trans_eq hreal_int
          have hexp_norm : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
            rw [Complex.norm_exp]; simp
          rw [hexp_norm, abs_of_pos hcos_pos]
          calc ‖G z - laplaceTrunc f T z‖ * Real.exp (z.re * T) * (2 * Real.cos θ)
              ≤ (B * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T) * (2 * Real.cos θ) := by
                gcongr
            _ = 2 * B / R := by
                rw [hz_re]
                have hexp_cancel : Real.exp (-(R * Real.cos θ) * T) * Real.exp (R * Real.cos θ * T) = 1 := by
                  rw [← Real.exp_add]; simp
                have : (B * Real.exp (-(R * Real.cos θ) * T) / (R * Real.cos θ)) *
                    Real.exp (R * Real.cos θ * T) * (2 * Real.cos θ) =
                    (B * (Real.exp (-(R * Real.cos θ) * T) * Real.exp (R * Real.cos θ * T)) *
                      (2 * Real.cos θ)) / (R * Real.cos θ) := by ring
                rw [this, hexp_cancel, mul_one]
                field_simp [hR.ne', hcos_pos.ne']
    -- Bound Term 2: left semicircle `θ ∈ [π/2, 3π/2]`
    have hterm2 :
        ‖∫ θ : ℝ in (π / 2)..(3 * π / 2),
          (I * (R * Complex.exp ((θ : ℂ) * I))) * H_g (R * Complex.exp ((θ : ℂ) * I))‖ ≤
        2 * π * B / R := by
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 * B / R)
        (a := π / 2) (b := 3 * π / 2)
        (f := fun θ : ℝ =>
          (I * (R * Complex.exp ((θ : ℂ) * I))) * H_g (R * Complex.exp ((θ : ℂ) * I)))
        (fun θ hθ => ?_)
      · calc _ ≤ (2 * B / R) * |3 * π / 2 - π / 2| := hb
          _ = 2 * π * B / R := by
              rw [show 3 * π / 2 - π / 2 = π by ring, abs_of_pos Real.pi_pos]
              ring
      · rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
        set z : ℂ := (R : ℂ) * Complex.exp ((θ : ℂ) * I)
        have hfact :
            (I * z) * H_g z =
            laplaceTrunc f T z * Complex.exp (z * (T : ℂ)) *
              ((I * z) * (1 / z + z / (R : ℂ) ^ 2)) := by
          simp only [H_g]; ring
        rw [hfact, norm_mul, norm_mul, norm_circle_kernel R θ hR]
        have hcos_nonpos : Real.cos θ ≤ 0 := by
          have hθ' : θ - π ∈ Set.Icc (-(π / 2)) (π / 2) := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
          have h := Real.cos_nonneg_of_mem_Icc hθ'
          rw [Real.cos_sub_pi] at h
          linarith
        rcases eq_or_lt_of_le hcos_nonpos with hcos0 | hcos_neg
        · rw [hcos0, abs_zero, mul_zero, mul_zero]
          positivity
        · have hz_re : z.re = R * Real.cos θ := by
            simp [z, Complex.mul_re, Complex.exp_ofReal_mul_I_re]
          have hz_re_neg : z.re < 0 := by
            rw [hz_re]
            exact mul_neg_of_pos_of_neg hR hcos_neg
          have hpos_a : 0 < -z.re := neg_pos.mpr hz_re_neg
          have hg_norm : ‖laplaceTrunc f T z‖ ≤ B * Real.exp (-z.re * T) / (-z.re) := by
            unfold laplaceTrunc
            have hle : ‖∫ t : ℝ in (0 : ℝ)..T, (f t : ℂ) * Complex.exp (-z * (t : ℂ))‖ ≤
                ∫ t : ℝ in (0 : ℝ)..T, B * Real.exp ((-z.re) * t) := by
              refine intervalIntegral.norm_integral_le_of_norm_le hT.le ?_ ?_
              · refine Filter.Eventually.of_forall fun t ht => ?_
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
                have : (-z * (t : ℂ)).re = (-z.re) * t := by simp
                rw [this]
                exact mul_le_mul_of_nonneg_right (hf_bound t ht.1.le) (Real.exp_nonneg _)
              · exact (continuous_const.mul (Real.continuous_exp.comp
                  (continuous_const.mul continuous_id))).intervalIntegrable _ _
            have hcalc : ∫ t : ℝ in (0 : ℝ)..T, B * Real.exp ((-z.re) * t) =
                B * (Real.exp ((-z.re) * T) - 1) / (-z.re) := by
              rw [intervalIntegral.integral_const_mul]
              have hftc : ∫ t : ℝ in (0 : ℝ)..T, Real.exp ((-z.re) * t) =
                  Real.exp ((-z.re) * T) / (-z.re) - Real.exp ((-z.re) * 0) / (-z.re) := by
                refine intervalIntegral.integral_eq_sub_of_hasDerivAt
                  (f := fun x : ℝ => Real.exp ((-z.re) * x) / (-z.re)) (fun t _ => ?_) ?_
                · have h1 : HasDerivAt (fun x : ℝ => (-z.re) * x) (-z.re) t := by
                    simpa using (hasDerivAt_id t).const_mul (-z.re)
                  have h2 := (h1.exp).div_const (-z.re)
                  have heq : Real.exp ((-z.re) * t) * (-z.re) / (-z.re) = Real.exp ((-z.re) * t) :=
                    mul_div_cancel_right₀ _ hpos_a.ne'
                  exact heq ▸ h2
                · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
              rw [hftc, mul_zero, Real.exp_zero]
              ring
            rw [hcalc] at hle
            refine hle.trans ?_
            gcongr
            linarith
          have hexp_norm : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
            rw [Complex.norm_exp]; simp
          rw [hexp_norm, abs_of_neg hcos_neg]
          calc ‖laplaceTrunc f T z‖ * Real.exp (z.re * T) * (2 * -Real.cos θ)
              ≤ (B * Real.exp (-z.re * T) / (-z.re)) * Real.exp (z.re * T) * (2 * -Real.cos θ) := by
                gcongr
                linarith
            _ = 2 * B / R := by
                rw [hz_re]
                have hexp_cancel : Real.exp (-(R * Real.cos θ) * T) * Real.exp (R * Real.cos θ * T) = 1 := by
                  rw [← Real.exp_add]; simp
                have : (B * Real.exp (-(R * Real.cos θ) * T) / -(R * Real.cos θ)) *
                    Real.exp (R * Real.cos θ * T) * (2 * -Real.cos θ) =
                    (B * (Real.exp (-(R * Real.cos θ) * T) * Real.exp (R * Real.cos θ * T)) *
                      (2 * -Real.cos θ)) / (R * -Real.cos θ) := by ring
                rw [this, hexp_cancel, mul_one]
                field_simp [hR.ne', hcos_neg.ne]
    -- Bound Term 3: left rectangle `L_rect`
    have hbot_norm : ‖∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + ((-R : ℝ) : ℂ) * I)‖ ≤ M / T := by
      have hle : ‖∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + ((-R : ℝ) : ℂ) * I)‖ ≤
          ∫ x : ℝ in (-δ)..0, M * Real.exp (x * T) := by
        refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_ ?_
        · refine Filter.Eventually.of_forall fun x hx => ?_
          have hfact : H_G ((x : ℂ) + ((-R : ℝ) : ℂ) * I) =
              K_base ((x : ℂ) + ((-R : ℝ) : ℂ) * I) *
                Complex.exp (((x : ℂ) + ((-R : ℝ) : ℂ) * I) * (T : ℂ)) := by
            simp only [H_G, K_base]; ring
          rw [hfact, norm_mul, Complex.norm_exp]
          have hre : (((x : ℂ) + ((-R : ℝ) : ℂ) * I) * (T : ℂ)).re = x * T := by simp
          rw [hre]
          exact mul_le_mul_of_nonneg_right (hM₁_le x ⟨hx.1.le, hx.2⟩) (Real.exp_nonneg _)
        · exact (continuous_const.mul (Real.continuous_exp.comp
            (continuous_id.mul continuous_const))).intervalIntegrable _ _
      have hcalc : ∫ x : ℝ in (-δ)..0, M * Real.exp (x * T) = M * (1 - Real.exp (-δ * T)) / T := by
        rw [intervalIntegral.integral_const_mul]
        have hftc : ∫ x : ℝ in (-δ)..0, Real.exp (x * T) =
            Real.exp (0 * T) / T - Real.exp ((-δ) * T) / T := by
          refine intervalIntegral.integral_eq_sub_of_hasDerivAt
            (f := fun u : ℝ => Real.exp (u * T) / T) (fun x _ => ?_) ?_
          · have h1 : HasDerivAt (fun u : ℝ => u * T) T x := by
              simpa using (hasDerivAt_id x).mul_const T
            have h2 := (h1.exp).div_const T
            have heq : Real.exp (x * T) * T / T = Real.exp (x * T) := mul_div_cancel_right₀ _ hT.ne'
            exact heq ▸ h2
          · exact (Real.continuous_exp.comp (continuous_id.mul continuous_const)).intervalIntegrable _ _
        rw [hftc, zero_mul, Real.exp_zero]
        ring
      rw [hcalc] at hle
      refine hle.trans ?_
      have : 1 - Real.exp (-δ * T) ≤ 1 := by linarith [Real.exp_nonneg (-δ * T)]
      calc M * (1 - Real.exp (-δ * T)) / T ≤ M * 1 / T := by gcongr
        _ = M / T := by ring
    have htop_norm : ‖∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + (R : ℂ) * I)‖ ≤ M / T := by
      have hle : ‖∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + (R : ℂ) * I)‖ ≤
          ∫ x : ℝ in (-δ)..0, M * Real.exp (x * T) := by
        refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_ ?_
        · refine Filter.Eventually.of_forall fun x hx => ?_
          have hfact : H_G ((x : ℂ) + (R : ℂ) * I) =
              K_base ((x : ℂ) + (R : ℂ) * I) *
                Complex.exp (((x : ℂ) + (R : ℂ) * I) * (T : ℂ)) := by
            simp only [H_G, K_base]; ring
          rw [hfact, norm_mul, Complex.norm_exp]
          have hre : (((x : ℂ) + (R : ℂ) * I) * (T : ℂ)).re = x * T := by simp
          rw [hre]
          exact mul_le_mul_of_nonneg_right (hM₂_le x ⟨hx.1.le, hx.2⟩) (Real.exp_nonneg _)
        · exact (continuous_const.mul (Real.continuous_exp.comp
            (continuous_id.mul continuous_const))).intervalIntegrable _ _
      have hcalc : ∫ x : ℝ in (-δ)..0, M * Real.exp (x * T) = M * (1 - Real.exp (-δ * T)) / T := by
        rw [intervalIntegral.integral_const_mul]
        have hftc : ∫ x : ℝ in (-δ)..0, Real.exp (x * T) =
            Real.exp (0 * T) / T - Real.exp ((-δ) * T) / T := by
          refine intervalIntegral.integral_eq_sub_of_hasDerivAt
            (f := fun u : ℝ => Real.exp (u * T) / T) (fun x _ => ?_) ?_
          · have h1 : HasDerivAt (fun u : ℝ => u * T) T x := by
              simpa using (hasDerivAt_id x).mul_const T
            have h2 := (h1.exp).div_const T
            have heq : Real.exp (x * T) * T / T = Real.exp (x * T) := mul_div_cancel_right₀ _ hT.ne'
            exact heq ▸ h2
          · exact (Real.continuous_exp.comp (continuous_id.mul continuous_const)).intervalIntegrable _ _
        rw [hftc, zero_mul, Real.exp_zero]
        ring
      rw [hcalc] at hle
      refine hle.trans ?_
      have : 1 - Real.exp (-δ * T) ≤ 1 := by linarith [Real.exp_nonneg (-δ * T)]
      calc M * (1 - Real.exp (-δ * T)) / T ≤ M * 1 / T := by gcongr
        _ = M / T := by ring
    have hleft_norm : ‖I * (∫ y : ℝ in (-R)..R, H_G (((-δ : ℝ) : ℂ) + (y : ℂ) * I))‖ ≤
        2 * R * M * Real.exp (-δ * T) := by
      rw [norm_mul, Complex.norm_I, one_mul]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := M * Real.exp (-δ * T))
        (a := -R) (b := R) (f := fun y : ℝ => H_G (((-δ : ℝ) : ℂ) + (y : ℂ) * I)) (fun y hy => by
          rw [Set.uIoc_of_le (by linarith)] at hy
          have hfact : H_G (((-δ : ℝ) : ℂ) + (y : ℂ) * I) =
              K_base (((-δ : ℝ) : ℂ) + (y : ℂ) * I) *
                Complex.exp ((((-δ : ℝ) : ℂ) + (y : ℂ) * I) * (T : ℂ)) := by
            simp only [H_G, K_base]; ring
          rw [hfact, norm_mul, Complex.norm_exp]
          have hre : ((((-δ : ℝ) : ℂ) + (y : ℂ) * I) * (T : ℂ)).re = -δ * T := by simp
          rw [hre]
          exact mul_le_mul_of_nonneg_right (hM₃_le y ⟨hy.1.le, hy.2⟩) (Real.exp_nonneg _))
      calc _ ≤ M * Real.exp (-δ * T) * |R - -R| := hb
        _ = 2 * R * M * Real.exp (-δ * T) := by
            rw [show R - -R = 2 * R by ring, abs_of_pos (by linarith)]
            ring
    have hterm3 :
        ‖-(∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) +
          I * (∫ y : ℝ in (-R)..R, H_G (((-δ : ℝ) : ℂ) + (y : ℂ) * I)) +
          (∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + (R : ℂ) * I))‖ ≤
        2 * R * M * Real.exp (-δ * T) + 2 * M / T := by
      have h1 := norm_add_le
        (-(∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) +
          I * (∫ y : ℝ in (-R)..R, H_G (((-δ : ℝ) : ℂ) + (y : ℂ) * I)))
        (∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + (R : ℂ) * I))
      have h2 := norm_add_le
        (-(∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + ((-R : ℝ) : ℂ) * I)))
        (I * (∫ y : ℝ in (-R)..R, H_G (((-δ : ℝ) : ℂ) + (y : ℂ) * I)))
      rw [norm_neg] at h2
      have h2MT : M / T + M / T = 2 * M / T := by ring
      linarith
    have htotal : ‖(2 * (π : ℂ) * I) * (G 0 - laplaceTrunc f T 0)‖ ≤
        4 * π * B / R + 2 * R * M * Real.exp (-δ * T) + 2 * M / T := by
      rw [hsub_eq]
      have h1 := norm_sub_le
        (((∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * H_G (R * Complex.exp ((θ : ℂ) * I))) -
         (∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * H_g (R * Complex.exp ((θ : ℂ) * I)))) -
        (∫ θ : ℝ in (π / 2)..(3 * π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * H_g (R * Complex.exp ((θ : ℂ) * I))))
        (-(∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) +
          I * (∫ y : ℝ in (-R)..R, H_G (((-δ : ℝ) : ℂ) + (y : ℂ) * I)) +
          (∫ x : ℝ in (-δ)..0, H_G ((x : ℂ) + (R : ℂ) * I)))
      have h2 := norm_sub_le
        ((∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * H_G (R * Complex.exp ((θ : ℂ) * I))) -
         (∫ θ : ℝ in (-π / 2)..(π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * H_g (R * Complex.exp ((θ : ℂ) * I))))
        (∫ θ : ℝ in (π / 2)..(3 * π / 2), (I * (R * Complex.exp ((θ : ℂ) * I))) * H_g (R * Complex.exp ((θ : ℂ) * I)))
      have h4pi : 2 * π * B / R + 2 * π * B / R = 4 * π * B / R := by ring
      linarith
    have hnorm_lhs : ‖(2 * (π : ℂ) * I) * (G 0 - laplaceTrunc f T 0)‖ =
        (2 * π) * ‖G 0 - laplaceTrunc f T 0‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
    rw [hnorm_lhs] at htotal
    have h2pi : 0 < 2 * π := by positivity
    rw [← le_div_iff₀' h2pi] at htotal
    refine htotal.trans_eq ?_
    field_simp [Real.pi_pos.ne']
    ring
  -- Now choose `T₀` large enough that `(M / π) * (R * exp(-δ * T) + 1 / T) < η / 2`
  have htail_tend : Tendsto (fun T : ℝ => (M / π) * (R * Real.exp (-δ * T) + 1 / T)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => R * Real.exp (-δ * T)) atTop (𝓝 0) := by
      have hexp := Real.tendsto_exp_atBot.comp
        (Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hδ) tendsto_id)
      simpa using hexp.const_mul R
    have h2 : Tendsto (fun T : ℝ => (1 : ℝ) / T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using (h1.add h2).const_mul (M / π)
  have hev := (tendsto_order.mp htail_tend).2 (η / 2) (half_pos hη)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨T₁, hT₁⟩ := hev
  refine ⟨max 1 T₁, fun T hT => ?_⟩
  have hT_pos : 0 < T := lt_of_lt_of_le one_pos ((le_max_left 1 T₁).trans hT)
  have hT_ge : T₁ ≤ T := (le_max_right 1 T₁).trans hT
  rw [dist_comm, dist_eq_norm]
  calc ‖G 0 - laplaceTrunc f T 0‖
      ≤ 2 * B / R + (M / π) * (R * Real.exp (-δ * T) + 1 / T) := hmain T hT_pos
    _ < η / 2 + η / 2 := add_lt_add hBR (hT₁ T hT_ge)
    _ = η := add_halves η

/- Part 5: From convergence of `∫_0^T (e^{-t} ψ(e^t) - 1) dt` to `ψ(N) ≤ (1 + ε) * N` -/

private lemma psi_eventually_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Chebyshev.psi N ≤ (1 + ε) * (N : ℝ) := by
  have hB : (0 : ℝ) < Real.log 4 + 4 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have htend_c : Tendsto (fun T : ℝ => laplaceTrunc f_psi T 0) atTop (𝓝 (G_fun 0)) :=
    newman_tauberian hB f_psi_measurable (fun t _ => f_psi_abs_le)
      isOpen_U_dom re_nonneg_subset_U_dom differentiableOn_G_fun (fun z hz => G_fun_eq_laplace hz)
  have htend : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f_psi t) atTop (𝓝 (G_fun 0).re) := by
    have hre := (Complex.continuous_re.tendsto (G_fun 0)).comp htend_c
    refine hre.congr fun T => ?_
    simp only [Function.comp_apply, laplaceTrunc, neg_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
  set δ : ℝ := Real.log (1 + ε / 2)
  have hδ_pos : 0 < δ := Real.log_pos (by linarith)
  have hexp_δ : Real.exp δ = 1 + ε / 2 := Real.exp_log (by linarith)
  set c : ℝ := (1 + ε) / (1 + ε / 2) - 1
  have hc_pos : 0 < c := by
    have hden : 0 < 1 + ε / 2 := by linarith
    rw [sub_pos, one_lt_div hden]
    linarith
  have hcδ : 0 < c * δ / 2 := by positivity
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨T₀, hT₀⟩ := htend (c * δ / 2) hcδ
  have hN_ev : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ T₀ ≤ Real.log (N : ℝ) := by
    have h1 : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop 1
    have h2 : ∀ᶠ N : ℕ in atTop, T₀ ≤ Real.log (N : ℝ) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop T₀)
    exact h1.and h2
  filter_upwards [hN_ev] with N ⟨hN1, hN_log⟩
  by_contra! hgt
  set T : ℝ := Real.log (N : ℝ)
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN1
  have hexp_T : Real.exp T = (N : ℝ) := Real.exp_log hN_pos
  have hf_int : ∀ a b : ℝ, IntervalIntegrable f_psi volume a b := fun a b => by
    have hmono : Monotone (fun t : ℝ => Chebyshev.psi (Real.exp t)) :=
      Chebyshev.psi_mono.comp Real.exp_monotone
    have h1 : IntervalIntegrable (fun t : ℝ => Chebyshev.psi (Real.exp t)) volume a b :=
      hmono.intervalIntegrable
    have h2 : Continuous (fun t : ℝ => Real.exp (-t)) :=
      Real.continuous_exp.comp continuous_neg
    have hprod : IntervalIntegrable (fun t : ℝ => Real.exp (-t) * Chebyshev.psi (Real.exp t)) volume a b := by
      simpa only [mul_comm] using h1.continuousOn_mul h2.continuousOn
    exact hprod.sub intervalIntegrable_const
  have hint_upper : (∫ t in T..(T + δ), f_psi t) < c * δ := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hf_int 0 T) (hf_int T (T + δ))
    have hdiff : ∫ t in T..(T + δ), f_psi t =
        (∫ t in (0 : ℝ)..(T + δ), f_psi t) - (∫ t in (0 : ℝ)..T, f_psi t) := by
      linarith
    rw [hdiff]
    have h1 := hT₀ (T + δ) (by linarith)
    have h2 := hT₀ T hN_log
    rw [Real.dist_eq] at h1 h2
    have h3 : (∫ t in (0 : ℝ)..(T + δ), f_psi t) - (∫ t in (0 : ℝ)..T, f_psi t) ≤
        |(∫ t in (0 : ℝ)..(T + δ), f_psi t) - (G_fun 0).re| +
        |(∫ t in (0 : ℝ)..T, f_psi t) - (G_fun 0).re| := by
      calc _ = ((∫ t in (0 : ℝ)..(T + δ), f_psi t) - (G_fun 0).re) -
              ((∫ t in (0 : ℝ)..T, f_psi t) - (G_fun 0).re) := by ring
        _ ≤ _ := by linarith [le_abs_self ((∫ t in (0 : ℝ)..(T + δ), f_psi t) - (G_fun 0).re),
            neg_le_abs ((∫ t in (0 : ℝ)..T, f_psi t) - (G_fun 0).re)]
    linarith
  have hint_lower : c * δ ≤ ∫ t in T..(T + δ), f_psi t := by
    have hconst : ∫ _ in T..(T + δ), c = c * δ := by
      simp [smul_eq_mul, mul_comm]
    rw [← hconst]
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const (hf_int T (T + δ))
      fun t ht => ?_
    have hexp_ge : (N : ℝ) ≤ Real.exp t := by
      rw [← hexp_T]
      exact Real.exp_le_exp.mpr ht.1
    have hexp_le : Real.exp t ≤ (N : ℝ) * (1 + ε / 2) := by
      calc Real.exp t ≤ Real.exp (T + δ) := Real.exp_le_exp.mpr ht.2
        _ = Real.exp T * Real.exp δ := Real.exp_add T δ
        _ = (N : ℝ) * (1 + ε / 2) := by rw [hexp_T, hexp_δ]
    have hpsi_ge : (1 + ε) * (N : ℝ) ≤ Chebyshev.psi (Real.exp t) :=
      hgt.le.trans (Chebyshev.psi_mono hexp_ge)
    unfold f_psi
    rw [Real.exp_neg, inv_mul_eq_div]
    have hden_pos : 0 < (N : ℝ) * (1 + ε / 2) := by positivity
    have h1 : (1 + ε) / (1 + ε / 2) = ((1 + ε) * (N : ℝ)) / ((N : ℝ) * (1 + ε / 2)) := by
      field_simp [hN_pos.ne']
    have h2 : ((1 + ε) * (N : ℝ)) / ((N : ℝ) * (1 + ε / 2)) ≤
        Chebyshev.psi (Real.exp t) / Real.exp t := by
      calc ((1 + ε) * (N : ℝ)) / ((N : ℝ) * (1 + ε / 2))
          ≤ ((1 + ε) * (N : ℝ)) / Real.exp t :=
            div_le_div_of_nonneg_left (by positivity) (Real.exp_pos t) hexp_le
        _ ≤ Chebyshev.psi (Real.exp t) / Real.exp t :=
            div_le_div_of_nonneg_right hpsi_ge (Real.exp_nonneg t)
    linarith [h1, h2]
  linarith

end Erdos311Proof

theorem OMA.solution : type_of% @Erdos311.delta_ge_exp := by
  intro ε hε
  filter_upwards [psi_eventually_le ε hε] with N hN
  have hlcm_pos : (0 : ℝ) < ((Nat.lcmUpto N : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.lcmUpto_pos N)
  have hlog : Real.log ((Nat.lcmUpto N : ℕ) : ℝ) ≤ (1 + ε) * (N : ℝ) := by
    rwa [← Chebyshev.psi_eq_log_lcmUpto]
  have hlcm_le : ((Nat.lcmUpto N : ℕ) : ℝ) ≤ Real.exp ((1 + ε) * (N : ℝ)) := by
    calc ((Nat.lcmUpto N : ℕ) : ℝ)
        = Real.exp (Real.log ((Nat.lcmUpto N : ℕ) : ℝ)) := (Real.exp_log hlcm_pos).symm
      _ ≤ Real.exp ((1 + ε) * (N : ℝ)) := Real.exp_le_exp.mpr hlog
  calc Real.exp (-(1 + ε) * (N : ℝ))
      = 1 / Real.exp ((1 + ε) * (N : ℝ)) := by
        rw [neg_mul, Real.exp_neg, one_div]
    _ ≤ 1 / ((Nat.lcmUpto N : ℕ) : ℝ) :=
        one_div_le_one_div_of_le hlcm_pos hlcm_le
    _ ≤ Erdos311.delta N := delta_ge_inv_lcm_aux N
