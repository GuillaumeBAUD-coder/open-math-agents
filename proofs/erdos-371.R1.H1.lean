import OMAReductions.R_erdos_371_R1
import Mathlib
/-!
Fixed-cutoff smooth-count theorem for Left to Solve erdos-371 H1 (card t_35cb78e1).
Port, not an independent proof: adapted from OpenAI/math @ 3344da59991ed94f9ba711217b29c1d760badfa6
(OAI.NumberTheory.JointDickman.*, OAI.NumberTheory.Jacobsthal.Renewal.DickmanFiniteDecay), and
PrimeNumberTheoremAnd @ c39a751132c88b6e8080b74c74023fd95b3d8be0 (Erdos970.EulerMaclaurin,
Erdos970.MertensClassical; Mertens' second theorem). Declaration slice plus a new final assembly
`OAI.JointDickman.fixedSmooth_count_tendsto` (direct primeAvoidanceDegree_tendsto + bounded
inclusion-exclusion; no joint distribution). Checked against formal-conjectures FC pin with
Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1.
-/
namespace Erdos970

open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2

lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by unfold B1; fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring

end Erdos970


















namespace Erdos970

theorem Filter.EventuallyEq.iff_eventually {α : Type _} {β : Type _} {l : Filter α} {f g : α → β} : f =ᶠ[l] g ↔ ∀ᶠ (x : α) in l, f x = g x := by rfl

namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics

theorem inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert tendsto_log_atTop.inv_tendsto_atTop using 1
    ext; simp

theorem one_eq_o_log_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log (log x)) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)

end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology

private lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  ·                                                             
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  ·                                                         
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
                    
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
                            
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
                                                                                  
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep

private lemma integral_log_mul_exp_neg_eq_deriv_Gamma :
    ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) = deriv Real.Gamma 1 := by
  set I : ℝ := ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) with hI
                                              
  have h1 := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
                                                                                   
  have hval : (∫ t : ℝ in Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))))
      = (I : ℂ) := by
    have key : ∀ t : ℝ, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
        = ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
      intro t
      rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
    simp_rw [key]
    rw [integral_complex_ofReal, hI]
  rw [hval] at h1
                                                                                 
  have h2 : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0:ℝ) < (1:ℂ).re by norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz
                            
  have h3 := h2.real_of_complex
  have h4 : HasDerivAt Real.Gamma I 1 := by
    have hcongr : (fun x : ℝ => (Complex.Gamma ↑x).re) = Real.Gamma := by
      funext x
      rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rw [hcongr, Complex.ofReal_re] at h3
    exact h3
  rw [← h4.deriv]

private theorem mul_integ_log_log_eq_aux (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) =
      - Real.log (s - 1) + deriv Real.Gamma 1 := by
  have hs0 : 0 < s - 1 := by linarith
  set f : ℝ → ℝ := fun x => (s - 1) * Real.log x with hf_def
  set f' : ℝ → ℝ := fun x => (s - 1) / x with hf'_def
  set g : ℝ → ℝ := fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u) with hg_def
            
  have hf1 : f 1 = 0 := by simp [hf_def]
                           
  have hf_cont : ContinuousOn f (Ici 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [mem_Ici] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
                          
  have hft : Tendsto f atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hs0
    exact Real.tendsto_log_atTop
                                                      
  have hff' : ∀ x ∈ Ioi (1:ℝ), HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    simp only [mem_Ioi] at hx
    have hxne : x ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hxne).const_mul (s - 1)
    have h2 : HasDerivAt f ((s - 1) * x⁻¹) x := this
    have : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
    rw [this] at h2
    exact h2.hasDerivWithinAt
                                          
  have hmono : StrictMonoOn f (Ici 1) := by
    intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    apply mul_lt_mul_of_pos_left _ hs0
    exact Real.log_lt_log (by linarith) hab
  have himg_Ioi : f '' Ioi 1 = Ioi 0 := by
    ext y
    simp only [Set.mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 < Real.log x := Real.log_pos hx
      positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_lt_exp_iff.mpr (div_pos hy hs0)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  have himg_Ici : f '' Ici 1 = Ici 0 := by
    ext y
    simp only [Set.mem_image, mem_Ici]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 ≤ Real.log x := Real.log_nonneg hx
      rw [hf_def]; positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_le_exp_iff.mpr (div_nonneg hy hs0.le)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
                                                         
  have hg_cont : ContinuousOn g (f '' Ioi 1) := by
    rw [himg_Ioi]
    apply ContinuousOn.mul
    · apply ContinuousOn.sub _ continuousOn_const
      apply Real.continuousOn_log.mono
      intro u hu
      simp only [mem_Ioi] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn
                                                         
  have hg1 : IntegrableOn g (f '' Ici 1) := by
    rw [himg_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have : g = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [this]
    exact e1.sub e2
                                                     
  have hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1) := by
                                                         
    have hff'_Ici : ∀ x ∈ Ici (1:ℝ), HasDerivWithinAt f (f' x) (Ici 1) x := by
      intro x hx
      simp only [mem_Ici] at hx
      have hxne : x ≠ 0 := by linarith
      have hd : HasDerivAt f ((s - 1) * x⁻¹) x := (Real.hasDerivAt_log hxne).const_mul (s - 1)
      have heq : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
      rw [heq] at hd
      exact hd.hasDerivWithinAt
                            
    have hinj : InjOn f (Ici 1) := hmono.injOn
                                                                  
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Ici (1:ℝ)) (f := f) (f' := f') measurableSet_Ici hff'_Ici hinj g
    rw [hiff] at hg1
                                        
    apply hg1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    simp only [mem_Ici] at hx
    have hxpos : (0:ℝ) < x := by linarith
    have hf'pos : 0 < f' x := by rw [hf'_def]; positivity
    simp only [smul_eq_mul, Function.comp, abs_of_pos hf'pos]
    ring
                               
  have hcov := integral_comp_mul_deriv_Ioi hf_cont hft hff' hg_cont hg1 hg2
  rw [hf1] at hcov
                                                       
  have hrhs : ∫ u in Ioi (0:ℝ), g u = deriv Real.Gamma 1 - Real.log (s - 1) := by
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have hsplit : (fun u => g u)
        = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [show (∫ u in Ioi (0:ℝ), g u)
        = ∫ u in Ioi (0:ℝ), (Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u))
        from by rw [hsplit]]
    rw [integral_sub e1 e2, integral_log_mul_exp_neg_eq_deriv_Gamma]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
                                                                                  
  have hlhs : ∫ x in Ioi (1:ℝ), (g ∘ f) x * f' x
      = (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) := by
    have hpt : ∀ x ∈ Ioi (1:ℝ), (g ∘ f) x * f' x
        = (s - 1) * (Real.log (Real.log x) * x ^ (-s)) := by
      intro x hx
      simp only [mem_Ioi] at hx
      have hxpos : (0:ℝ) < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
      have hs1ne : s - 1 ≠ 0 := ne_of_gt hs0
      simp only [Function.comp, hf_def, hg_def, hf'_def]
                                                      
      rw [Real.log_mul hs1ne hlogne]
                                              
      have hexp : Real.exp (-((s - 1) * Real.log x)) = x ^ (-(s - 1)) := by
        rw [Real.rpow_def_of_pos hxpos]
        ring_nf
      rw [hexp]
                                                  
      have hx1 : x ^ (-(s - 1)) * ((s - 1) / x) = (s - 1) * x ^ (-s) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one x]
        rw [show x ^ (-(s - 1)) * ((s - 1) * x ^ (-1 : ℝ))
            = (s - 1) * (x ^ (-(s - 1)) * x ^ (-1 : ℝ)) by ring]
        rw [← Real.rpow_add hxpos]
        ring_nf
      rw [show (Real.log (s - 1) + Real.log (Real.log x) - Real.log (s - 1))
          = Real.log (Real.log x) by ring]
      linear_combination Real.log (Real.log x) * hx1
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [hlhs, hrhs] at hcov
  rw [hcov]
  ring

end Issue1584

namespace Mertens

open _root_.Real Erdos970.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa

theorem sum_log_eq {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n =
      x * log x - (x - ⌊x⌋₊ - 1 / 2) * log x - x + 1 + ∫ t in 1..x, (t - ⌊t⌋₊ - 1 / 2) / t := by
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  have : 1 = ⌊(1 : ℝ)⌋₊ := by simp
  nth_rw 1 [this]
  rw [sum_eq_integral_add_integral_deriv (by norm_num) hx (fun _ _ ↦ (by fun_prop (disch := grind)))]
  · simp only [log_one, B1, Nat.floor_one, Nat.cast_one, sub_self, zero_sub,
    RCLike.ofReal_real_eq_id, id_eq, mul_neg, zero_mul, neg_zero, integral_log, mul_zero, sub_zero,
    deriv_log']
    ring_nf
    congr
    ext
    ring
  · simp only [deriv_log', Set.uIcc_of_le hx]
    fun_prop (disch := grind)

theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_log_factorial (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n = log (Nat.floor x).factorial := by
    rw [←prod_Ico_id_eq_factorial, ←log_prod, prod_natCast]
    · congr
    intro x hx
    simp at hx ⊢; grind

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩

theorem E₁Λ.bounded : E₁Λ =O[atTop] (fun _ ↦ (1:ℝ)) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one,
    eventually_atTop]
  exact ⟨log 4 + 4, 1, fun _ hx ↦ sum_mangoldt_div_eq_log hx⟩

theorem one_eq_o_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log x) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp tendsto_log_atTop

theorem sum_mangoldt_div_eq_log' :
    (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert! E₁Λ.bounded using 1

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩

theorem sum_log_prime_div_eq_log' : E₁p =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop, E₁p]
    exact ⟨ log 4 + 4, 1, fun _ ↦ sum_log_prime_div_eq_log ⟩

theorem sum_log_prime_div_eq_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert! sum_log_prime_div_eq_log' using 1

noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)



private theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁Λ.bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · have h : Measurable (fun x : ℝ => ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d) := (show Measurable (fun n : ℕ => ∑ d ∈ Ioc 0 n, (Λ d) / d) from measurable_from_top).comp (by fun_prop : Measurable (fun x : ℝ => ⌊x⌋₊))
    exact Measurable.aestronglyMeasurable (by unfold E₁Λ; fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · have h : Measurable (fun x : ℝ => ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p) := (show Measurable (fun n : ℕ => ∑ p ∈ Ioc 0 n with p.Prime, (log p) / p) from measurable_from_top).comp (by fun_prop : Measurable (fun x : ℝ => ⌊x⌋₊))
    exact Measurable.aestronglyMeasurable (by unfold E₁p; fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

theorem E₂Λ.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  unfold E₂Λ
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  conv => lhs; arg 1; arg 1; arg 2; ext n; rw [(by field : Λ n / (n * log n) = (Λ n / n) / log n)]
  rw [sum_div_log_eq hx]
  rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, Λ n / n) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁Λ t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold γ
    calc
    _ = E₁Λ x / log x + (∫ (x : ℝ) in 2..x, E₁Λ x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁Λ t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁Λ_div_mul_log_sq (by rfl)) (integrable_E₁Λ_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁Λ_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp

theorem E₂Λ.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂Λ.eq hx, abs_le']
    constructor
    · grw [E₁Λ.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≥ - 2 / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2) hx)
            (integrable_E₁Λ_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2) hx
      grw [this]
      grind
    grw [E₁Λ.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem E₂Λ.bound : E₂Λ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6, 2
    intro x hx
    convert E₂Λ.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂Λ.bound' : E₂Λ =o[atTop] (fun _ ↦ (1:ℝ)) := E₂Λ.bound.trans_isLittleO inv_log_eq_o_one

theorem log_zeta_eq_sum (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = ∑' n, Λ n / (n^s * log n) := by
  have hsc : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
                           
  have hep := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) hsc
  set S : ℂ := ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) with hS
                                        
  have hcpow : ∀ p : Nat.Primes, (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro p
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
                                      
  set z : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s) with hz
                
  have hz_pos : ∀ p : Nat.Primes, 0 < z p := fun p => by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    positivity
  have hz_lt_one : ∀ p : Nat.Primes, z p < 1 := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    change (p : ℝ) ^ (-s) < 1
    rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]
    right
    exact (Real.one_lt_rpow_iff_of_pos (by positivity)).mpr (Or.inl ⟨hp1, by linarith⟩)
                                                
  have hterm : ∀ p : Nat.Primes,
      -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) = ((-Real.log (1 - z p) : ℝ) : ℂ) := by
    intro p
    rw [hcpow p]
    have h1z : (0 : ℝ) < 1 - z p := by have := hz_lt_one p; linarith
    rw [show (1 : ℂ) - ((z p : ℝ) : ℂ) = (((1 - z p : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_log h1z.le]
    push_cast; ring
                                                       
  set Sr : ℝ := ∑' p : Nat.Primes, -Real.log (1 - z p) with hSr
  have hSeq : S = (Sr : ℂ) := by
    rw [hS, hSr, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hSim : S.im = 0 := by rw [hSeq]; exact Complex.ofReal_im _
  have hSre : S.re = Sr := by rw [hSeq]; exact Complex.ofReal_re _
                               
  have hlog_zeta : Complex.log (riemannZeta (s : ℂ)) = S := by
    rw [← hep, Complex.log_exp (by rw [hSim]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [hSim]; exact Real.pi_pos.le)]
                                      
  have hkey : Real.log (riemannZeta (s : ℂ)).re = Sr := by
    have hζim : (riemannZeta (s : ℂ)).im = 0 := riemannZeta_im_eq_zero_of_one_lt hs
    have hζeq : riemannZeta (s : ℂ) = ((riemannZeta (s : ℂ)).re : ℂ) := by
      apply Complex.ext <;> simp [hζim]
    have : Real.log (riemannZeta (s : ℂ)).re
        = (Complex.log (riemannZeta (s : ℂ))).re := by
      conv_rhs => rw [hζeq]
      rw [Complex.log_ofReal_re]
    rw [this, hlog_zeta, hSre]
  rw [hkey]

  have habs : ∀ p : Nat.Primes, |z p| < 1 := by
    intro p
    rw [abs_of_pos (hz_pos p)]; exact hz_lt_one p
  have htaylor : ∀ p : Nat.Primes,
      HasSum (fun n : ℕ => (z p) ^ (n + 1) / (n + 1)) (-Real.log (1 - z p)) :=
    fun p => hasSum_pow_div_log_of_abs_lt_one (habs p)
  have hSr_double : Sr = ∑' (p : Nat.Primes) (n : ℕ), (z p) ^ (n + 1) / (n + 1) := by
    rw [hSr]
    exact tsum_congr fun p => ((htaylor p).tsum_eq).symm
                                       
  have hsummable_z : Summable z := Nat.Primes.summable_rpow.mpr (by linarith)
                                      
  have hsummable_prime : Summable (fun p : Nat.Primes => -Real.log (1 - z p)) := by
    have := Real.summable_log_one_add_of_summable hsummable_z.neg
    convert! this.neg using 1
                                      
  have hg_nonneg : ∀ pk : Nat.Primes × ℕ, 0 ≤ (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1) := by
    intro pk; positivity [hz_pos pk.1]
  have hsummable_g : Summable (fun pk : Nat.Primes × ℕ => (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1)) := by
    rw [summable_prod_of_nonneg hg_nonneg]
    refine ⟨fun p => (htaylor p).summable, ?_⟩
    refine hsummable_prime.congr (fun p => ?_)
    exact ((htaylor p).tsum_eq).symm
                                      
  have hpoint : ∀ (p : Nat.Primes) (n : ℕ),
      Λ ((p : ℕ) ^ (n + 1)) /
        ((((p : ℕ) ^ (n + 1) : ℕ) : ℝ) ^ s * Real.log (((p : ℕ) ^ (n + 1) : ℕ) : ℝ))
      = (z p) ^ (n + 1) / (n + 1) := by
    intro p n
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    rw [vonMangoldt_apply_pow (Nat.succ_ne_zero n), vonMangoldt_apply_prime p.prop]
    have hcast : (((p : ℕ) ^ (n + 1) : ℕ) : ℝ) = (p : ℝ) ^ (n + 1) := by push_cast; ring
    rw [hcast, Real.log_pow]
    rw [show (z p) ^ (n + 1) = ((p : ℝ) ^ (n + 1)) ^ (-s) by
      rw [hz]; rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) (n + 1),
        ← Real.rpow_natCast ((p : ℝ)) (n + 1), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by positivity)]; ring_nf]
    rw [Real.rpow_neg (by positivity)]
    field_simp
    push_cast
    ring
                                                 
  set F : ℕ → ℝ := fun n => Λ n / ((n : ℝ) ^ s * Real.log n) with hF
                                              
  have hsupp : Function.support F ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    rw [Function.mem_support] at hn
    simp only [Set.mem_ofPred_eq]
    by_contra hpp
    apply hn
    simp only [hF, vonMangoldt_eq_zero_iff.mpr hpp, zero_div]
                                           
  have hprod_eq : (∑' pk : Nat.Primes × ℕ, (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1))
      = ∑' m : {n : ℕ // IsPrimePow n}, F m.val := by
    rw [← Equiv.tsum_eq Nat.Primes.prodNatEquiv (fun m : {n : ℕ // IsPrimePow n} => F m.val)]
    apply tsum_congr
    intro pk
    rw [Nat.Primes.coe_prodNatEquiv_apply, hF]
    exact (hpoint pk.1 pk.2).symm
             
  rw [hSr_double, ← hsummable_g.tsum_prod' (fun p => (htaylor p).summable), hprod_eq]
  exact tsum_subtype_eq_of_support_subset hsupp

section
open MeasureTheory Set

namespace LogZetaInteg

private noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)

private noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]

private lemma c_nonneg (d : ℕ) : 0 ≤ c d := by
  unfold c
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · apply div_nonneg vonMangoldt_nonneg
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    positivity

private lemma summable_log_rpow_div_rpow (a : ℝ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (Real.log n) ^ a / (n:ℝ) ^ s) := by
  have hε : (0:ℝ) < (s - 1) / 2 := by linarith
  refine summable_of_isBigO_nat (g := fun n : ℕ => (n:ℝ) ^ ((s - 1) / 2 - s)) ?_ ?_
  · rw [Real.summable_nat_rpow]; linarith
  · have ho : (fun x : ℝ => (Real.log x) ^ a) =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2)) :=
      (isLittleO_log_rpow_rpow_atTop a hε).isBigO
    have hmul : (fun x : ℝ => (Real.log x) ^ a / x ^ s)
        =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s) := by
      simpa only [div_eq_mul_inv] using ho.mul (isBigO_refl (fun x : ℝ => (x ^ s)⁻¹) atTop)
    have heq : (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s)
        =ᶠ[atTop] (fun x : ℝ => x ^ ((s - 1) / 2 - s)) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_sub hx]
    exact (hmul.trans_eventuallyEq heq).natCast_atTop

private lemma summable_vonMangoldt_div_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (Λ n : ℝ) / (n:ℝ) ^ s) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg vonMangoldt_nonneg (by positivity)) ?_
    (summable_log_rpow_div_rpow 1 hs)
  intro n
  rw [Real.rpow_one]
  gcongr
  exact vonMangoldt_le_log

private lemma summable_c_term (s : ℝ) (hs : 1 < s) :
    Summable (fun d : ℕ => c d * ((d:ℝ) ^ (1 - s) / (s - 1))) := by
  have hs1 : (0:ℝ) < s - 1 := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
                                                                                            
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_)
    ((summable_vonMangoldt_div_rpow s hs).mul_left (1 / (Real.log 2 * (s - 1))))
  ·                               
    refine mul_nonneg (c_nonneg d) (div_nonneg ?_ hs1.le)
    rcases eq_or_ne (d:ℝ) 0 with hd | hd
    · rw [hd, Real.zero_rpow (by linarith : (1 - s) ≠ 0)]
    · positivity
  ·                                                         
    rcases lt_or_ge d 2 with hd | hd
    · have hc : c d = 0 := by interval_cases d <;> simp
      rw [hc, zero_mul]
      exact mul_nonneg (by positivity) (div_nonneg vonMangoldt_nonneg (by positivity))
    · have hd2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      have hd0 : (0:ℝ) < (d:ℝ) := by linarith
      have hlogge : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd2
      have hds : (0:ℝ) < (d:ℝ) ^ s := Real.rpow_pos_of_pos hd0 s
      have hkey : c d * ((d:ℝ) ^ (1 - s) / (s - 1)) = Λ d / ((d:ℝ) ^ s * Real.log d * (s - 1)) := by
        unfold c
        rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hd0, Real.rpow_one, Real.rpow_neg hd0.le]
        field_simp
                                                                                   
      have hcb : (d:ℝ) ^ s * Real.log 2 * (s - 1) ≤ (d:ℝ) ^ s * Real.log d * (s - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogge hds.le) hs1.le
      rw [hkey, show (1 / (Real.log 2 * (s - 1))) * ((Λ d : ℝ) / (d:ℝ) ^ s)
          = Λ d / ((d:ℝ) ^ s * Real.log 2 * (s - 1)) from by field_simp]
      exact div_le_div_of_nonneg_left vonMangoldt_nonneg (by positivity) hcb

theorem log_zeta_eq_integ_aux (s : ℝ) (hs : 1 < s) :
    Real.log (riemannZeta (s:ℂ)).re =
      (s - 1) * ∫ x in Set.Ioi 1, (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) := by
  rw [Mertens.log_zeta_eq_sum s hs]
  symm
  have hstep1 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s)
        = (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, c d) * x ^ (-s) := by
    intro x hx
    simp only [Mertens.E₂Λ, c]
    ring
  have hstep2 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) = ∑' d : ℕ, f s d x := by
    intro x hx
    rw [hstep1 x hx]
    simp only [f]
    rw [Finset.sum_mul]
    have hx0 : (0:ℝ) ≤ x := by have := hx; simp only [Set.mem_Ioi] at this; linarith
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) ?_]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.mem_Ioc] at hd
      have hdx : (d:ℝ) ≤ x := by
        rw [← Nat.le_floor_iff hx0]; exact hd.2
      rw [Set.indicator_of_mem (by simpa using hdx)]
    · intro d hd
      simp only [Finset.mem_Ioc, not_and, not_le] at hd
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · subst hd0; simp
      · have hfloor : ⌊x⌋₊ < d := hd hd0
        have hdx : x < (d:ℝ) := by
          rw [← Nat.floor_lt hx0]; exact hfloor
        rw [Set.indicator_of_notMem (by simpa using not_le.mpr hdx)]
        ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hstep2]
  have hperterm : ∀ d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0; simp [f]
    simp only [f]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_indicator measurableSet_Ici]
    congr 1
    have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd0
    have hdR0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    set A : Set ℝ := Set.Ioi (1:ℝ) ∩ Set.Ici (d:ℝ) with hA
    have hae : A =ᵐ[volume] Set.Ioi (d:ℝ) := by
      have h1 : A =ᵐ[volume] (Set.Ici (1:ℝ) ∩ Set.Ici (d:ℝ) : Set ℝ) :=
        MeasureTheory.ae_eq_set_inter MeasureTheory.Ioi_ae_eq_Ici (ae_eq_refl _)
      rw [Set.Ici_inter_Ici, max_eq_right hdR] at h1
      exact h1.trans MeasureTheory.Ioi_ae_eq_Ici.symm
    rw [MeasureTheory.setIntegral_congr_set hae]
    rw [integral_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) hdR0,
      show (-s + 1 : ℝ) = 1 - s by ring]
    have hs1 : (1 - s) ≠ 0 := by linarith
    have hs2 : (s - 1) ≠ 0 := by linarith
    field_simp
    ring
  have hint : ∀ d : ℕ, MeasureTheory.IntegrableOn (f s d) (Set.Ioi (1:ℝ)) := by
    intro d
    unfold f
    apply MeasureTheory.Integrable.const_mul
    rw [show MeasureTheory.Integrable ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
        (volume.restrict (Set.Ioi (1:ℝ)))
      ↔ MeasureTheory.IntegrableOn ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
          (Set.Ioi (1:ℝ)) volume from Iff.rfl,
      MeasureTheory.integrableOn_indicator_iff measurableSet_Ici]
    apply MeasureTheory.IntegrableOn.mono_set
      (integrableOn_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) (by norm_num : (0:ℝ) < 1/2))
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith [hx.2]
  have hnorm_int : ∀ d : ℕ,
      ∫ x in Set.Ioi (1:ℝ), ‖f s d x‖ = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rw [← hperterm d]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hfnn : 0 ≤ f s d x := by
      simp only [f]
      apply mul_nonneg (c_nonneg d)
      by_cases hxd : (d:ℝ) ≤ x
      · rw [Set.indicator_of_mem (by simpa using hxd)]
        exact le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
      · rw [Set.indicator_of_notMem (by simpa using hxd)]
    change ‖f s d x‖ = f s d x
    rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  have hinterchange : ∫ x in Set.Ioi (1:ℝ), ∑' d : ℕ, f s d x
      = ∑' d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x := by
    refine (MeasureTheory.integral_tsum_of_summable_integral_norm hint ?_).symm
    apply (summable_c_term s hs).congr
    intro d
    exact (hnorm_int d).symm
  rw [hinterchange]
  simp_rw [hperterm]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0; simp
  · have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    have hsub : (d:ℝ) ^ (1 - s) = (d:ℝ) ^ (-s) * (d:ℝ) := by
      rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hdR, Real.rpow_one]
    have hs1 : s - 1 ≠ 0 := by linarith
    have hneg : (d:ℝ) ^ (-s) = ((d:ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hdR)]
    unfold c
    rw [hsub, hneg]
    field_simp

end LogZetaInteg
end

private theorem log_zeta_eq_integ (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = (s - 1) * ∫ x in .Ioi 1, (log (log x) + γ + E₂Λ x) * x^(-s) :=
  LogZetaInteg.log_zeta_eq_integ_aux s hs

private theorem mul_integ_log_log_eq (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in .Ioi 1, log (log x) * x^(-s) = - log (s - 1) + deriv Gamma 1 :=
  mul_integ_log_log_eq_aux s hs

private theorem mul_integ_gamma_eq (s) (hs : 1 < s) : (s - 1) * ∫ x in .Ioi 1, γ * x^(-s) = γ := by
  rw [MeasureTheory.integral_const_mul γ (· ^ (-s)), @integral_Ioi_rpow_of_lt (-s), one_rpow] <;>
    grind

private theorem integrableOn_Ioi_mul_rpow_neg_of_abs_le
    {c B a s : ℝ} (hc : 0 < c) (has : a + 1 < s) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x ∈ Set.Ioi c, |f x| ≤ B * x ^ a) :
    MeasureTheory.IntegrableOn (fun x => f x * x ^ (-s)) (Set.Ioi c) := by
  have hg : MeasureTheory.IntegrableOn (fun x => B * x ^ (a - s)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a - s < -1) hc).const_mul B
  refine MeasureTheory.Integrable.mono' hg
    (hf.mul (measurable_id.pow_const (-s))).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : (0:ℝ) < x := hc.trans hx
  have hxs : (0:ℝ) < x ^ (-s) := Real.rpow_pos_of_pos hxpos _
  rw [norm_mul, norm_eq_abs, norm_eq_abs, abs_of_pos hxs]
  calc |f x| * x ^ (-s) ≤ B * x ^ a * x ^ (-s) :=
        mul_le_mul_of_nonneg_right (hbound x hx) hxs.le
    _ = B * x ^ (a - s) := by rw [mul_assoc, ← Real.rpow_add hxpos, sub_eq_add_neg]

private theorem integrableOn_log_log_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => log (log x) * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  apply MeasureTheory.IntegrableOn.union
  ·                                                                                 
    have hll : MeasureTheory.IntegrableOn (fun x => log (log x)) (Set.Ioc 1 2) := by
      have h : IntervalIntegrable (log ∘ log) MeasureTheory.volume 1 2 := by
        apply MeromorphicOn.intervalIntegrable_log
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
        exact (analyticAt_log (by linarith [hx.1] : 0 < x)).meromorphicAt
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h
    have hmul : MeasureTheory.IntegrableOn (fun x => x ^ (-s) * log (log x)) (Set.Ioc 1 2) := by
      apply hll.bdd_mul (c := 1)
      · fun_prop
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        rw [norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) _)]
        calc x ^ (-s) ≤ (1:ℝ) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1.le (by linarith)
          _ = 1 := Real.one_rpow _
    simpa [mul_comm] using hmul
  ·                                                                                                
    set ε := (s - 1) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := ε) (B := 1 / ε + |log (log 2)|)
      (by norm_num) (by rw [hε]; linarith) (Real.measurable_log.comp Real.measurable_log) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hx1 : (1:ℝ) ≤ x ^ ε := Real.one_le_rpow (by linarith) hεpos.le
    have hlogx : 0 < log x := Real.log_pos (by linarith)
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hmono : log 2 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
    have hub : log (log x) ≤ x ^ ε / ε :=
      calc log (log x) ≤ log x := (Real.log_le_sub_one_of_pos hlogx).trans (by linarith)
        _ ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hεpos
    have hlb : log (log 2) ≤ log (log x) := Real.log_le_log hlog2 hmono
    have hxε : 0 ≤ x ^ ε / ε := by positivity
    calc |log (log x)| ≤ x ^ ε / ε + |log (log 2)| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le (log (log 2))],
            by linarith [abs_nonneg (log (log 2))]⟩
      _ ≤ (1 / ε + |log (log 2)|) * x ^ ε := by
          have h2 : |log (log 2)| ≤ |log (log 2)| * x ^ ε := le_mul_of_one_le_right (abs_nonneg _) hx1
          have h1 : x ^ ε / ε = 1 / ε * x ^ ε := by ring
          rw [add_mul]; linarith

private theorem integrableOn_γ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => γ * x ^ (-s)) (Set.Ioi 1) := by
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) one_pos).const_mul γ

private theorem integrableOn_E₂Λ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => E₂Λ x * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioo_union_Ici_eq_Ioi (by norm_num : (1:ℝ) < 2)]
  apply MeasureTheory.IntegrableOn.union
  ·                                                                        
    have hsub : Set.Ioo (1:ℝ) 2 ⊆ Set.Ioi 1 := fun x hx => hx.1
    have h1 := (integrableOn_γ_mul_rpow s hs).mono_set hsub
    have h2 := (integrableOn_log_log_mul_rpow s hs).mono_set hsub
    have hb : MeasureTheory.IntegrableOn
        (fun x => -(log (log x) * x ^ (-s)) - γ * x ^ (-s)) (Set.Ioo 1 2) :=
      h2.neg.sub h1
    apply hb.congr_fun _ measurableSet_Ioo
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hfloor : ⌊ x ⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by push_cast; linarith [hx.1], by push_cast; linarith [hx.2]⟩
    have hsum : (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / ((d:ℝ) * log d)) = 0 := by rw [hfloor]; norm_num
    change -(log (log x) * x ^ (-s)) - γ * x ^ (-s)
        = (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ) * x ^ (-s)
    rw [hsum]; ring
  ·                                                                                              
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := 0) (B := (log 4 + 6) / log 2)
      (by norm_num) (by linarith) (by fun_prop) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hc : 0 ≤ log 4 + 6 := by positivity
    rw [Real.rpow_zero, mul_one]
    have hb2 : (log 4 + 6) / log x ≤ (log 4 + 6) / log 2 :=
      div_le_div_of_nonneg_left hc hlog2 (Real.log_le_log (by norm_num) (le_of_lt hx))
    exact (E₂Λ.abs_le (le_of_lt hx)).trans hb2

private theorem log_zeta_eq (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = - log (s - 1) + deriv Gamma 1 + γ + (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x^(-s) := by
                                                          
  rw [log_zeta_eq_integ s hs]
                                                                                               
  have key : (∫ x in Set.Ioi 1, (log (log x) + γ + E₂Λ x) * x ^ (-s))
      = (∫ x in Set.Ioi 1, log (log x) * x ^ (-s))
        + (∫ x in Set.Ioi 1, γ * x ^ (-s))
        + (∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)) := by
    rw [← MeasureTheory.integral_add (integrableOn_log_log_mul_rpow s hs)
      (integrableOn_γ_mul_rpow s hs)]
    rw [← MeasureTheory.integral_add (f := fun x => log (log x) * x ^ (-s) + γ * x ^ (-s))
      (g := fun x => E₂Λ x * x ^ (-s))
      ((integrableOn_log_log_mul_rpow s hs).add (integrableOn_γ_mul_rpow s hs))
      (integrableOn_E₂Λ_mul_rpow s hs)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
                                                                
  rw [key, mul_add, mul_add, mul_integ_log_log_eq s hs, mul_integ_gamma_eq s hs]

private lemma zeta_pole_mul_re_tendsto_one :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hofReal :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_compl_singleton_iff.mpr (by
        norm_num
        exact ne_of_gt (Set.mem_Ioi.mp hs))
  have hcomplex :
      Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    riemannZeta_residue_one.comp hofReal
  have hreal :
      Filter.Tendsto
        (fun s : ℝ => (((s : ℂ) - 1) * riemannZeta (s : ℂ)).re)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℝ)) :=
    (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simpa [Complex.ofReal_sub, Complex.ofReal_mul] using hreal

private theorem log_zeta_limit :
    Filter.Tendsto
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      zeta_pole_mul_re_tendsto_one
  have hEq :
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
        =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s - 1 := sub_pos.mpr (Set.mem_Ioi.mp hs)
    have hzpos : 0 < (riemannZeta (s : ℂ)).re :=
      riemannZeta_re_pos_of_one_lt (Set.mem_Ioi.mp hs)
    rw [Real.log_mul hspos.ne' hzpos.ne']
    ring
  simpa using hlog.congr' (hEq.mono fun s hs => hs.symm)

section
open MeasureTheory Set

private lemma measurable_E₂Λ : Measurable E₂Λ := by
  have h : Measurable (fun x : ℝ => ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d)) := (show Measurable (fun n : ℕ => ∑ d ∈ Ioc 0 n, (Λ d) / (d * log d)) from measurable_from_top).comp (by fun_prop : Measurable (fun x : ℝ => ⌊x⌋₊))
  unfold E₂Λ
  fun_prop

private lemma E₂Λ_eq_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    E₂Λ x = - log (log x) - γ := by
  obtain ⟨h1, h2⟩ := hx
  have hf : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast h1.le, by exact_mod_cast h2⟩
  unfold E₂Λ
  rw [hf]
  simp

private lemma abs_E₂Λ_le_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    |E₂Λ x| ≤ |log (x - 1)| + log 2 + |γ| := by
  obtain ⟨hx1, hx2⟩ := hx
  have hloglog : |log (log x)| ≤ |log (x - 1)| + log 2 := by
    have hxpos : (0:ℝ) < x := by linarith
    have hlogx_pos : 0 < log x := Real.log_pos hx1
    have hxm1 : 0 < x - 1 := by linarith
    have hub : log x ≤ x - 1 := by have := Real.log_le_sub_one_of_pos hxpos; linarith
    have hlb2 : (x - 1) / 2 ≤ log x := by
      have h := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one] at h
      simp only [zero_sub] at h
      have h12 : (x - 1) / 2 ≤ 1 - 1 / x := by
        rw [← sub_nonneg]
        have e : (1 - 1 / x) - (x - 1) / 2 = (3 * x - 2 - x ^ 2) / (2 * x) := by field_simp; ring
        rw [e]; exact div_nonneg (by nlinarith [hx1, hx2]) (by positivity)
      linarith
    have hupper : log (log x) ≤ log (x - 1) := Real.log_le_log hlogx_pos hub
    have hlower : log (x - 1) - log 2 ≤ log (log x) := by
      have := Real.log_le_log (show (0:ℝ) < (x - 1) / 2 by positivity) hlb2
      rwa [Real.log_div (by linarith) (by norm_num)] at this
    have h2 : (0:ℝ) ≤ log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    exact ⟨by have := neg_abs_le (log (x - 1)); linarith,
          by have := le_abs_self (log (x - 1)); linarith⟩
  rw [E₂Λ_eq_on_Ioo ⟨hx1, hx2⟩]
  have htri : |(- log (log x) - γ)| ≤ |log (log x)| + |γ| := by
    have h := abs_sub (-log (log x)) γ
    rwa [abs_neg] at h
  linarith

private lemma abs_E₂Λ_le_const {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log 2 :=
  (E₂Λ.abs_le hx).trans <| div_le_div_of_nonneg_left (by positivity)
    (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hx)

private lemma integrableOn_log_sub_one_bound :
    IntegrableOn (fun x => |log (x - 1)| + log 2 + |γ|) (Set.Ioo 1 2) volume := by
  have hlog : IntegrableOn (fun x => |log (x - 1)|) (Set.Ioo 1 2) volume := by
    have h0 : IntervalIntegrable (fun x => log x) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'
    have h1 : IntervalIntegrable (fun x => log (x - 1)) volume (0 + 1) (1 + 1) :=
      h0.comp_sub_right 1
    norm_num at h1
    exact (h1.1.mono_set Set.Ioo_subset_Ioc_self).abs
  have hc : IntegrableOn (fun _ : ℝ => log 2 + |γ|) (Set.Ioo (1 : ℝ) 2) volume :=
    integrableOn_const (measure_Ioo_lt_top).ne (by finiteness)
  have hsum : IntegrableOn (fun x => |log (x - 1)| + (log 2 + |γ|)) (Set.Ioo 1 2) volume :=
    hlog.add hc
  exact hsum.congr_fun (fun x _ => by ring) measurableSet_Ioo

private lemma integrableOn_E₂Λ_Ioo {X : ℝ} (_hX : 2 ≤ X) :
    IntegrableOn E₂Λ (Set.Ioo 1 X) volume := by
  have hsub : Set.Ioo (1 : ℝ) X ⊆ Set.Ioo 1 2 ∪ Set.Icc 2 X := by
    intro x hx; simp only [Set.mem_Ioo, Set.mem_union, Set.mem_Icc] at *
    rcases lt_or_ge x 2 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2.le⟩
  apply IntegrableOn.mono_set _ hsub
  apply IntegrableOn.union
  · have hg := integrableOn_log_sub_one_bound
    refine Integrable.mono' hg measurable_E₂Λ.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_on_Ioo hx
  · refine Integrable.mono' (g := fun _ => (log 4 + 6) / log 2) ?_
      measurable_E₂Λ.aestronglyMeasurable ?_
    · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by finiteness)
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_const hx.1

private lemma sub_one_mul_integral_E₂Λ_tendsto :
    Filter.Tendsto (fun s : ℝ => (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
                                                                           
  obtain ⟨X₀, hX₀⟩ : ∃ X, ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := by
    have := E₂Λ.bound'.def (by positivity : (0:ℝ) < ε / 2)
    simp only [Real.norm_eq_abs, abs_one, mul_one] at this
    rw [Filter.eventually_atTop] at this; exact this
  set X := max X₀ 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXge : ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)
                                                     
  set B := ∫ x in Set.Ioo 1 X, |E₂Λ x| with hBdef
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioo (fun x _ => abs_nonneg _)
  refine ⟨min 1 (ε / 2 / (B + 1)), by positivity, ?_⟩
  intro s hs hdist
  simp only [Set.mem_Ioi] at hs
  rw [Real.dist_eq] at hdist
  have hs1 : s - 1 < min 1 (ε / 2 / (B + 1)) := by
    rw [abs_of_pos (by linarith)] at hdist; exact hdist
  have hsm1 : 0 < s - 1 := by linarith
                                                                  
  have hintAbs : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi 1) volume := by
    have h2 : IntegrableOn (fun x => |E₂Λ x * x ^ (-s)|) (Set.Ioi 1) volume :=
      (integrableOn_E₂Λ_mul_rpow s hs).abs
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x hx; simp only [Set.mem_Ioi] at hx
    change |E₂Λ x * x ^ (-s)| = |E₂Λ x| * x ^ (-s)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hintAbsIoc : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioc 1 X) volume :=
    hintAbs.mono_set Set.Ioc_subset_Ioi_self
  have hintAbsIoiX : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi X) volume :=
    hintAbs.mono_set (Set.Ioi_subset_Ioi (by linarith))
                                               
  have hsplit : ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) =
      (∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s)) + ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) := by
    have hu : Set.Ioi (1:ℝ) = Set.Ioc 1 X ∪ Set.Ioi X :=
      (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    rw [hu, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_left))
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_right))]
                                                                 
  have hp1 : ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ B := by
    rw [hBdef]
    have ha : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioo 1 X) volume := (integrableOn_E₂Λ_Ioo hX2).abs
    have habsIoc : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioc 1 X) volume :=
      ha.congr_set_ae (Ioo_ae_eq_Ioc).symm
    rw [← integral_Ioc_eq_integral_Ioo]
    apply setIntegral_mono_on hintAbsIoc habsIoc measurableSet_Ioc
    intro x hx
    have hx1 : (1:ℝ) ≤ x := by have := hx.1; linarith
    have hle1 : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc |E₂Λ x| * x ^ (-s) ≤ |E₂Λ x| * 1 := by gcongr
      _ = |E₂Λ x| := mul_one _
                                                                                
  have hp2 : ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ (ε / 2) * (X ^ (1 - s) / (s - 1)) := by
    have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi X) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X)
    have hval : ∫ x in Set.Ioi X, x ^ (-s) = X ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X),
        show -s + 1 = 1 - s by ring, show (1:ℝ) - s = -(s - 1) by ring]
      rw [div_neg, neg_div, neg_neg]
    rw [← hval, ← integral_const_mul]
    apply setIntegral_mono_on hintAbsIoiX (hrpow_int.const_mul (ε / 2)) measurableSet_Ioi
    intro x hx
    have hxpos : (0:ℝ) < x := by simp only [Set.mem_Ioi] at hx; linarith
    have hnn : 0 ≤ x ^ (-s) := Real.rpow_nonneg hxpos.le _
    have hb : |E₂Λ x| ≤ ε / 2 := hXge x (by simp only [Set.mem_Ioi] at hx; linarith)
    gcongr
  have hXpow : X ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
                                                     
  have hbound : (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B + ε / 2 := by
    rw [hsplit, mul_add]
    have ht2 : (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ ε / 2 := by
      calc (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s)
          ≤ (s - 1) * ((ε / 2) * (X ^ (1 - s) / (s - 1))) :=
            mul_le_mul_of_nonneg_left hp2 hsm1.le
        _ = (ε / 2) * X ^ (1 - s) := by
              have hne : s - 1 ≠ 0 := by linarith
              field_simp
        _ ≤ (ε / 2) * 1 := by gcongr
        _ = ε / 2 := mul_one _
    have ht1 : (s - 1) * ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B :=
      mul_le_mul_of_nonneg_left hp1 hsm1.le
    linarith
                                                  
  have habs_le : |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := by
    rw [abs_mul, abs_of_pos hsm1]
    gcongr
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Set.mem_Ioi] at hx
    change ‖E₂Λ x * x ^ (-s)‖ = |E₂Λ x| * x ^ (-s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  rw [Real.dist_eq, sub_zero]
                                                   
  have hfin : (s - 1) * B + ε / 2 < ε := by
    have hlt : s - 1 < ε / 2 / (B + 1) := lt_of_lt_of_le hs1 (min_le_right _ _)
    have hBp : 0 < B + 1 := by linarith
    have h1 : (s - 1) * B ≤ (s - 1) * (B + 1) := by nlinarith
    have h2 : (s - 1) * (B + 1) < (ε / 2 / (B + 1)) * (B + 1) := mul_lt_mul_of_pos_right hlt hBp
    have h3 : (ε / 2 / (B + 1)) * (B + 1) = ε / 2 := by field_simp
    linarith
  calc |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := habs_le
    _ ≤ (s - 1) * B + ε / 2 := hbound
    _ < ε := hfin

end

theorem deriv_gamma_add_γ_eq_zero : deriv Gamma 1 + γ = 0 := by
                                                                  
  have key : ∀ s : ℝ, 1 < s →
      (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s) = deriv Gamma 1 + γ := by
    intro s hs
    have h := log_zeta_eq s hs
    linarith
                                                                   
  have hconst : Filter.Tendsto
      (fun s : ℝ => (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (deriv Gamma 1 + γ)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (key s hs).symm
                                                                    
  have hlim := log_zeta_limit.sub sub_one_mul_integral_E₂Λ_tendsto
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hconst hlim

theorem γ.eq_eulerMascheroni : γ = eulerMascheroniConstant := by
  linarith [Real.eulerMascheroniConstant_eq_neg_deriv, deriv_gamma_add_γ_eq_zero]

theorem sum_mangoldt_div_log_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) = log (log x) + eulerMascheroniConstant + E₂Λ x := by
    grind [γ.eq_eulerMascheroni]

theorem sum_mangoldt_div_log_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x)| ≤ C := by
    use (log 4 + 6)/log 2 + |eulerMascheroniConstant|
    intro x hx
    rw [sum_mangoldt_div_log_eq]
    calc
      _ = |E₂Λ x + eulerMascheroniConstant| := by ring_nf
      _ ≤ (log 4 + 6)/log x + |eulerMascheroniConstant| := by grw [abs_add_le, E₂Λ.abs_le hx]
      _ ≤ _ := by gcongr

theorem sum_mangoldt_div_log_eq_log_log' : (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop]
    obtain ⟨ C, _ ⟩ := sum_mangoldt_div_log_eq_log_log
    use C, 2

theorem sum_mangoldt_div_log_eq_log_log'' : (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d)) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert! sum_mangoldt_div_log_eq_log_log' using 1

noncomputable def M : ℝ := (∫ t in Set.Ioi 2, E₁p t / (t * log t^2)) + 1 - log (log 2)

theorem M.le : M ≤ (log 4 + 4) / log 2 + 1 - log (log 2) := calc
    _ ≤ (∫ t in Set.Ioi 2, (log 4 + 4) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.le (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]

theorem M.ge : M ≥ (-2 - E₁) / log 2 + 1 - log (log 2) := calc
    _ ≥ (∫ t in Set.Ioi 2, (-2 - E₁) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.ge (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]

noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind


end Mertens
end Erdos970

-- Adapted from OpenAI/math@3344da59991ed94f9ba711217b29c1d760badfa6

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DelayConstruction

open MeasureTheory Filter
open scoped Topology

noncomputable def kernel (f : ℝ → ℝ) (t : ℝ) : ℝ := f (t - 1) / max 1 t

theorem kernel_continuous {f : ℝ → ℝ} (hf : Continuous f) : Continuous (kernel f) := by
  apply Continuous.div (hf.comp (continuous_id.sub continuous_const)) (continuous_const.max continuous_id)
  intro t
  change max (1 : ℝ) t ≠ 0
  have h := le_max_left (1 : ℝ) t
  linarith

noncomputable def stepApprox (σ : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun u => 1 + σ * ∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ n) t

theorem stepApprox_continuous (σ : ℝ) (n : ℕ) : Continuous (stepApprox σ n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      have hk := kernel_continuous ih
      have hInt : Continuous (fun u : ℝ => ∫ t in (1 : ℝ)..u, kernel (stepApprox σ n) t) :=
        (intervalIntegral.differentiable_integral_of_continuous hk).continuous
      exact continuous_const.add (continuous_const.mul (hInt.comp (continuous_const.max continuous_id)))

theorem stepApprox_initial (σ : ℝ) (n : ℕ) {u : ℝ} (hu : u ≤ 1) : stepApprox σ n u = 1 := by
  cases n <;> simp [stepApprox, max_eq_left hu]

theorem stepApprox_succ_stable (σ : ℝ) (n : ℕ) {u : ℝ} (hu : u ≤ (n : ℝ) + 1) :
    stepApprox σ (n + 1) u = stepApprox σ n u := by
  induction n generalizing u with
  | zero => simp only [Nat.cast_zero, zero_add] at hu; simp [stepApprox, max_eq_left hu]
  | succ n ih =>
      change 1 + σ * (∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ (n + 1)) t) =
        1 + σ * (∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ n) t)
      apply congrArg (fun I : ℝ => 1 + σ * I)
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (le_max_left (1 : ℝ) u)] at ht
      have hmax : max 1 u ≤ (n : ℝ) + 2 := by
        apply max_le
        · have hn0 := Nat.cast_nonneg (α := ℝ) n
          linarith
        · push_cast at hu
          linarith
      have htbound : t - 1 ≤ (n : ℝ) + 1 := by linarith [ht.2]
      unfold kernel
      rw [ih htbound]

theorem stepApprox_stable (σ : ℝ) {n m : ℕ} (hnm : n ≤ m) {u : ℝ}
    (hu : u ≤ (n : ℝ) + 1) : stepApprox σ m u = stepApprox σ n u := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      rw [stepApprox_succ_stable σ m, ih]
      have hcast : (n : ℝ) ≤ m := by exact_mod_cast hm
      linarith

noncomputable def delay (σ u : ℝ) : ℝ := stepApprox σ ⌈u⌉₊ u

theorem delay_eq_stepApprox (σ : ℝ) (n : ℕ) {u : ℝ} (hu : u ≤ (n : ℝ) + 1) :
    delay σ u = stepApprox σ n u := by
  unfold delay
  have hceil : u ≤ (⌈u⌉₊ : ℝ) + 1 := by have h := Nat.le_ceil u; linarith
  rcases le_total n ⌈u⌉₊ with h | h
  · exact stepApprox_stable σ h hu
  · exact (stepApprox_stable σ h hceil).symm

theorem delay_continuous (σ : ℝ) : Continuous (delay σ) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  let n := ⌈u⌉₊ + 1
  have hu : u < (n : ℝ) + 1 := by have h := Nat.le_ceil u; dsimp [n]; push_cast; linarith
  have heq : delay σ =ᶠ[𝓝 u] stepApprox σ n := by
    filter_upwards [Iio_mem_nhds hu] with x hx
    exact delay_eq_stepApprox σ n hx.le
  exact (continuousAt_congr heq).mpr (stepApprox_continuous σ n).continuousAt

theorem delay_initial (σ : ℝ) {u : ℝ} (hu : u ≤ 1) : delay σ u = 1 := by
  rw [delay_eq_stepApprox σ 0 (by simpa using hu)]
  rfl

theorem delay_integral (σ u : ℝ) :
    delay σ u = 1 + σ * ∫ t in (1 : ℝ)..max 1 u, kernel (delay σ) t := by
  let n := ⌈u⌉₊
  have hu : u ≤ (n : ℝ) := Nat.le_ceil u
  rw [delay_eq_stepApprox σ (n + 1) (by push_cast; linarith)]
  change 1 + σ * (∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ n) t) = _
  apply congrArg (fun I : ℝ => 1 + σ * I)
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (le_max_left (1 : ℝ) u)] at ht
  have hmax : max 1 u ≤ (n : ℝ) + 1 := max_le (by have hn0 := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith)
  have htbound : t - 1 ≤ (n : ℝ) + 1 := by linarith [ht.2]
  unfold kernel
  rw [delay_eq_stepApprox σ n htbound]

theorem delay_integral_of_one_le (σ : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    delay σ u = 1 + σ * ∫ t in (1 : ℝ)..u, delay σ (t - 1) / t := by
  rw [delay_integral σ u, max_eq_right hu]
  apply congrArg (fun I : ℝ => 1 + σ * I)
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hu] at ht
  simp only [kernel, max_eq_right ht.1]

theorem delay_hasDerivAt (σ : ℝ) {u : ℝ} (hu : 1 < u) :
    HasDerivAt (delay σ) (σ * delay σ (u - 1) / u) u := by
  have hk := kernel_continuous (delay_continuous σ)
  have hInt := intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable 1 u)
    hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  have hPrim := (hInt.const_mul σ).const_add 1
  have heq : delay σ =ᶠ[𝓝 u] (fun x => 1 + σ * ∫ t in (1 : ℝ)..x, kernel (delay σ) t) := by
    filter_upwards [Ioi_mem_nhds hu] with x hx
    rw [delay_integral σ x, max_eq_right hx.le]
  have hD := hPrim.congr_of_eventuallyEq heq
  simpa only [kernel, max_eq_right hu.le, mul_div_assoc] using hD

end NumberTheoryLean.DelayConstruction

end

section

namespace NumberTheoryLean.DelayUniqueness

theorem shifted_unique_upto (σ : ℝ) (F G : ℝ → ℝ)
    (hFinit : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → F u = 1)
    (hGinit : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → G u = 1)
    (hFrec : ∀ u : ℝ, 2 < u → F u = 1 + σ * ∫ t in (1 : ℝ)..u - 1, F t / t)
    (hGrec : ∀ u : ℝ, 2 < u → G u = 1 + σ * ∫ t in (1 : ℝ)..u - 1, G t / t)
    (n : ℕ) : ∀ u : ℝ, 1 ≤ u → u ≤ (n : ℝ) + 2 → F u = G u := by
  induction n with
  | zero =>
      intro u hu1 hu2
      have hu : u ≤ 2 := by simpa only [Nat.cast_zero, zero_add] using hu2
      rw [hFinit u hu1 hu, hGinit u hu1 hu]
  | succ n ih =>
      intro u hu1 hun
      by_cases hu2 : u ≤ 2
      · rw [hFinit u hu1 hu2, hGinit u hu1 hu2]
      · have hu : 2 < u := lt_of_not_ge hu2
        rw [hFrec u hu, hGrec u hu]
        apply congrArg (fun I : ℝ => 1 + σ * I)
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] at ht
        change F t / t = G t / t
        rw [ih t ht.1 (by push_cast at hun; linarith [ht.2])]

theorem shifted_unique (σ : ℝ) (F G : ℝ → ℝ)
    (hFinit : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → F u = 1)
    (hGinit : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → G u = 1)
    (hFrec : ∀ u : ℝ, 2 < u → F u = 1 + σ * ∫ t in (1 : ℝ)..u - 1, F t / t)
    (hGrec : ∀ u : ℝ, 2 < u → G u = 1 + σ * ∫ t in (1 : ℝ)..u - 1, G t / t)
    {u : ℝ} (hu : 1 ≤ u) : F u = G u := by
  apply shifted_unique_upto σ F G hFinit hGinit hFrec hGrec ⌈u⌉₊ u hu
  have h := Nat.le_ceil u
  linarith

end NumberTheoryLean.DelayUniqueness

end

section

namespace NumberTheoryLean.Dickman

open MeasureTheory Filter
open scoped Topology

noncomputable def rho : ℝ → ℝ := DelayConstruction.delay (-1)

theorem rho_continuous : Continuous rho := DelayConstruction.delay_continuous (-1)

theorem rho_initial {u : ℝ} (hu : u ≤ 1) : rho u = 1 := DelayConstruction.delay_initial (-1) hu

theorem rho_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt rho (-rho (u - 1) / u) u := by
  simpa only [rho, neg_one_mul] using DelayConstruction.delay_hasDerivAt (-1) hu

theorem rho_delay_equation {u : ℝ} (hu : 1 < u) : u * deriv rho u = -rho (u - 1) := by
  rw [(rho_hasDerivAt hu).deriv]
  field_simp

theorem rho_integral {u : ℝ} (hu : 1 ≤ u) :
    rho u = 1 - ∫ t in (1 : ℝ)..u, rho (t - 1) / t := by
  simpa only [rho, neg_one_mul, sub_eq_add_neg] using DelayConstruction.delay_integral_of_one_le (-1) hu

theorem rho_first_interval {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) : rho u = 1 - Real.log u := by
  rw [rho_integral hu1]
  have hInt : (∫ t in (1 : ℝ)..u, rho (t - 1) / t) = ∫ t in (1 : ℝ)..u, 1 / t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hu1] at ht
    change rho (t - 1) / t = 1 / t
    rw [rho_initial (by linarith [ht.2])]
  rw [hInt, integral_one_div_of_pos (by norm_num) (by linarith), div_one]

noncomputable def primitive (u : ℝ) : ℝ := ∫ t in (0 : ℝ)..u, rho t

theorem primitive_continuous : Continuous primitive :=
  (intervalIntegral.differentiable_integral_of_continuous rho_continuous).continuous

theorem primitive_hasDerivAt (u : ℝ) : HasDerivAt primitive (rho u) u :=
  intervalIntegral.integral_hasDerivAt_right (rho_continuous.intervalIntegrable 0 u)
    rho_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter rho_continuous.continuousAt

noncomputable def identityDifference (u : ℝ) : ℝ := u * rho u - (primitive u - primitive (u - 1))

theorem identityDifference_continuous : Continuous identityDifference :=
  (continuous_id.mul rho_continuous).sub (primitive_continuous.sub
    (primitive_continuous.comp (continuous_id.sub continuous_const)))

theorem identityDifference_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt identityDifference 0 u := by
  have hProd := (hasDerivAt_id u).mul (rho_hasDerivAt hu)
  have hShift := (primitive_hasDerivAt (u - 1)).comp u ((hasDerivAt_id u).sub_const 1)
  have hDiff := hProd.sub ((primitive_hasDerivAt u).sub hShift)
  have hvalue : (1 * rho u + id u * (-rho (u - 1) / u) - (rho u - rho (u - 1) * 1)) = 0 := by
    dsimp only [id_eq]
    field_simp
    ring
  rw [hvalue] at hDiff
  convert! hDiff using 1

theorem identityDifference_one : identityDifference 1 = 0 := by
  have hp1 : primitive 1 = 1 := by
    unfold primitive
    calc
      (∫ t in (0 : ℝ)..1, rho t) = ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        exact rho_initial ht.2
      _ = 1 := by simp
  have hp0 : primitive 0 = 0 := by simp [primitive]
  simp only [identityDifference, rho_initial (le_refl 1), one_mul, sub_self, hp1, hp0, sub_zero]

theorem rho_unit_integral {u : ℝ} (hu : 1 ≤ u) :
    u * rho u = ∫ t in u - 1..u, rho t := by
  have hzero : identityDifference u = 0 := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu
      identityDifference_continuous.continuousOn
      (fun x hx => identityDifference_hasDerivAt hx.1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 1 u)
    simpa only [intervalIntegral.integral_zero, identityDifference_one, sub_zero] using hFTC.symm
  have hInt := intervalIntegral.integral_add_adjacent_intervals
    (rho_continuous.intervalIntegrable (μ := volume) 0 (u - 1)) (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
  change primitive (u - 1) + (∫ t in u - 1..u, rho t) = primitive u at hInt
  unfold identityDifference at hzero
  linarith

theorem rho_antitone_segment (b : ℝ)
    (hprev : ∀ t : ℝ, 0 ≤ t → t ≤ b - 1 → 0 ≤ rho t) : AntitoneOn rho (Set.Icc 1 b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 1 b) rho_continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (rho_hasDerivAt hx.1).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(rho_hasDerivAt hx.1).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hprev (x - 1) (by linarith [hx.1])
      (by linarith [hx.2]))) (by linarith [hx.1])

theorem rho_nonneg_upto (n : ℕ) : ∀ u : ℝ, 0 ≤ u → u ≤ (n : ℝ) + 1 → 0 ≤ rho u := by
  induction n with
  | zero =>
      intro u _ hu
      rw [rho_initial (by simpa only [Nat.cast_zero, zero_add] using hu)]
      norm_num
  | succ n ih =>
      intro u hu0 hu
      have hub : u ≤ (n : ℝ) + 2 := by push_cast at hu; linarith
      have hmono : AntitoneOn rho (Set.Icc 1 ((n : ℝ) + 2)) :=
        rho_antitone_segment _ (fun t ht0 htb => ih t ht0 (by linarith))
      by_cases hu1 : u ≤ 1
      · rw [rho_initial hu1]; norm_num
      · have hu1' : 1 < u := lt_of_not_ge hu1
        have hpoint : ∀ t ∈ Set.Icc (u - 1) u, rho u ≤ rho t := by
          intro t ht
          by_cases ht1 : 1 ≤ t
          · exact hmono ⟨ht1, ht.2.trans hub⟩ ⟨hu1'.le, hub⟩ ht.2
          · rw [rho_initial (le_of_not_ge ht1)]
            have h := hmono ⟨le_rfl, by linarith⟩ ⟨hu1'.le, hub⟩ hu1'.le
            simpa only [rho_initial (le_refl 1)] using h
        have hint := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u)
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => rho u) volume (u - 1) u)
          (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u) hpoint
        have hconst : (∫ _t in u - 1..u, rho u) = rho u := by simp
        rw [hconst, ← rho_unit_integral hu1'.le] at hint
        have hprod : 0 ≤ (u - 1) * rho u := by nlinarith
        exact nonneg_of_mul_nonneg_right hprod (by linarith)

theorem rho_nonneg (u : ℝ) : 0 ≤ rho u := by
  by_cases hu : u ≤ 1
  · rw [rho_initial hu]; norm_num
  · apply rho_nonneg_upto ⌈u⌉₊ u (by linarith)
    have h := Nat.le_ceil u
    linarith

theorem rho_antitone : Antitone rho := by
  intro x y hxy
  by_cases hy : y ≤ 1
  · rw [rho_initial hy, rho_initial (hxy.trans hy)]
  · have hy1 : 1 < y := lt_of_not_ge hy
    have hmono := rho_antitone_segment y (fun t _ _ => rho_nonneg t)
    by_cases hx : x ≤ 1
    · rw [rho_initial hx]
      have h := hmono ⟨le_rfl, hy1.le⟩ ⟨hy1.le, le_rfl⟩ hy1.le
      simpa only [rho_initial (le_refl 1)] using h
    · exact hmono ⟨le_of_not_ge hx, hxy⟩ ⟨hy1.le, le_rfl⟩ hxy

theorem rho_half_step {u : ℝ} (hu : 1 ≤ u) : rho (u - 1 / 2) ≤ 2 * u * rho u := by
  have hconst := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u - 1 / 2)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => rho (u - 1 / 2)) volume (u - 1) (u - 1 / 2))
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) (u - 1 / 2))
    (fun t ht => rho_antitone ht.2)
  have hvalue : (∫ _t in u - 1..u - 1 / 2, rho (u - 1 / 2)) = (1 / 2 : ℝ) * rho (u - 1 / 2) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hvalue] at hconst
  have hsub := intervalIntegral.integral_mono_interval (μ := volume)
    (a := u - 1) (b := u - 1 / 2) (c := u - 1) (d := u)
    le_rfl (by linarith) (by linarith)
    (Filter.Eventually.of_forall (fun t => rho_nonneg t))
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
  rw [← rho_unit_integral hu] at hsub
  nlinarith

theorem rho_lower_comparison {u : ℝ} (hu : 2 ≤ u) : rho (u - 1) ≤ 4 * u ^ 2 * rho u := by
  have h1 := rho_half_step (u := u) (by linarith)
  have h2 := rho_half_step (u := u - 1 / 2) (by linarith)
  have harg : u - 1 / 2 - 1 / 2 = u - 1 := by ring
  rw [harg] at h2
  calc
    rho (u - 1) ≤ 2 * (u - 1 / 2) * rho (u - 1 / 2) := h2
    _ ≤ 2 * (u - 1 / 2) * (2 * u * rho u) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = (4 * u * (u - 1 / 2)) * rho u := by ring
    _ ≤ 4 * u ^ 2 * rho u := mul_le_mul_of_nonneg_right (by nlinarith) (rho_nonneg u)

theorem rho_pos_initial {u : ℝ} (hu : u ≤ 2) : 0 < rho u := by
  by_cases hu1 : u ≤ 1
  · rw [rho_initial hu1]; norm_num
  · have hu1' : 1 < u := lt_of_not_ge hu1
    rw [rho_first_interval hu1'.le hu]
    have hlog2 : Real.log 2 < 1 := by
      have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) Real.exp_one_gt_two
      simpa only [Real.log_exp] using h
    have hlogu := Real.log_le_log (show 0 < u by linarith) hu
    linarith

theorem rho_pos_upto (n : ℕ) : ∀ u : ℝ, u ≤ (n : ℝ) + 2 → 0 < rho u := by
  induction n with
  | zero => intro u hu; exact rho_pos_initial (by simpa only [Nat.cast_zero, zero_add] using hu)
  | succ n ih =>
      intro u hu
      by_cases hu2 : u ≤ 2
      · exact rho_pos_initial hu2
      · have hu2' : 2 < u := lt_of_not_ge hu2
        have hprev : 0 < rho (u - 1) := ih (u - 1) (by push_cast at hu; linarith)
        have hbound := rho_lower_comparison hu2'.le
        by_contra hnot
        have hnonpos : rho u ≤ 0 := le_of_not_gt hnot
        have hprod := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 4 * u ^ 2 by positivity) hnonpos
        linarith

theorem rho_pos (u : ℝ) : 0 < rho u := by
  apply rho_pos_upto ⌈u⌉₊ u
  have h := Nat.le_ceil u
  linarith

theorem rho_upper_comparison {u : ℝ} (hu : 1 ≤ u) : u * rho u ≤ rho (u - 1) := by
  have hInt := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u)
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => rho (u - 1)) volume (u - 1) u)
    (fun t ht => rho_antitone ht.1)
  have hconst : (∫ _t in u - 1..u, rho (u - 1)) = rho (u - 1) := by simp
  rw [hconst, ← rho_unit_integral hu] at hInt
  exact hInt

theorem rho_ratio_bounds {u : ℝ} (hu : 2 ≤ u) :
    1 / (4 * u ^ 2) ≤ rho u / rho (u - 1) ∧ rho u / rho (u - 1) ≤ 1 / u := by
  have hprev : 0 < rho (u - 1) := rho_pos _
  have hu0 : 0 < u := by linarith
  constructor
  · apply (div_le_div_iff₀ (show 0 < 4 * u ^ 2 by positivity) hprev).mpr
    have h := rho_lower_comparison hu
    nlinarith
  · apply (div_le_div_iff₀ hprev hu0).mpr
    have h := rho_upper_comparison (u := u) (by linarith)
    nlinarith

end NumberTheoryLean.Dickman

end

section

namespace NumberTheoryLean.DickmanDecay

open MeasureTheory Filter
open scoped Topology
open Dickman

noncomputable def hazard (u : ℝ) : ℝ := rho (u - 1) / (u * rho u)

theorem hazard_eq_neg_deriv {u : ℝ} (hu : 1 < u) : hazard u = -deriv rho u / rho u := by
  rw [(rho_hasDerivAt hu).deriv]
  unfold hazard
  field_simp

theorem hazard_ge_one {u : ℝ} (hu : 2 ≤ u) : 1 ≤ hazard u := by
  unfold hazard
  apply (le_div_iff₀ (mul_pos (show 0 < u by linarith) (rho_pos u))).mpr
  simpa only [one_mul] using rho_upper_comparison (u := u) (by linarith)

theorem deriv_le_of_hazard {u rate : ℝ} (hu : 1 < u) (hrate : rate ≤ hazard u) :
    deriv rho u ≤ -rate * rho u := by
  rw [hazard_eq_neg_deriv hu] at hrate
  have h := (le_div_iff₀ (rho_pos u)).mp hrate
  linarith

theorem rho_exponential_comparison (T rate a b : ℝ) (hT : 2 ≤ T)
    (htail : ∀ t : ℝ, T ≤ t → rate ≤ hazard t) (ha : T ≤ a) (hab : a ≤ b) :
    rho b ≤ rho a * Real.exp (-rate * (b - a)) := by
  let H : ℝ → ℝ := fun t => Real.exp (rate * t) * rho t
  have hCont : Continuous H :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul rho_continuous
  have hDeriv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt H (Real.exp (rate * t) * (deriv rho t + rate * rho t)) t := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have hExp := ((hasDerivAt_id t).const_mul rate).exp
    have hRho := (rho_hasDerivAt ht1).differentiableAt.hasDerivAt
    have hProd := hExp.mul hRho
    convert! hProd using 1
    simp only [id_eq, mul_one]
    ring
  have hMono : AntitoneOn H (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hCont.continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (hDeriv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hDeriv t ht).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have hd := deriv_le_of_hazard (u := t) (rate := rate) (by linarith [ht.1]) (htail t (by linarith [ht.1]))
      linarith
  have hHb : H b ≤ H a := hMono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hQ : rho b ≤ Real.exp (rate * a) * rho a / Real.exp (rate * b) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    dsimp [H] at hHb
    nlinarith
  calc
    rho b ≤ Real.exp (rate * a) * rho a / Real.exp (rate * b) := hQ
    _ = rho a * (Real.exp (rate * a) / Real.exp (rate * b)) := by ring
    _ = rho a * Real.exp (-rate * (b - a)) := by rw [← Real.exp_sub]; congr 1; congr 1; ring

theorem unit_exponential_integral (rate u : ℝ) (hrate : rate ≠ 0) :
    (∫ t in u - 1..u, Real.exp (-rate * (t - (u - 1)))) = (1 - Real.exp (-rate)) / rate := by
  rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => Real.exp (-rate * t)) (u - 1)]
  simp only [sub_self, sub_sub_cancel]
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hrate), integral_exp]
  simp only [mul_zero, mul_one, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

theorem hazard_bootstrap (T rate u : ℝ) (hT : 2 ≤ T) (hrate : 0 < rate)
    (htail : ∀ t : ℝ, T ≤ t → rate ≤ hazard t) (hu : T + 1 ≤ u) :
    rate / (1 - Real.exp (-rate)) ≤ hazard u := by
  have hu1 : 1 ≤ u := by linarith
  have hcomp : ∀ t ∈ Set.Icc (u - 1) u,
      rho t ≤ rho (u - 1) * Real.exp (-rate * (t - (u - 1))) := by
    intro t ht
    exact rho_exponential_comparison T rate (u - 1) t hT htail (by linarith) ht.1
  have hCont : Continuous (fun t : ℝ => rho (u - 1) * Real.exp (-rate * (t - (u - 1)))) := by fun_prop
  have hInt := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u)
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
    (hCont.intervalIntegrable (μ := volume) (u - 1) u) hcomp
  rw [← rho_unit_integral hu1, intervalIntegral.integral_const_mul,
    unit_exponential_integral rate u (ne_of_gt hrate)] at hInt
  have he : 0 < 1 - Real.exp (-rate) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  unfold hazard
  apply (div_le_div_iff₀ he (mul_pos (show 0 < u by linarith) (rho_pos u))).mpr
  rw [← mul_div_assoc] at hInt
  have hmul := (le_div_iff₀ hrate).mp hInt
  nlinarith

theorem bootstrap_uniform_gain (L rate : ℝ) (hrate1 : 1 ≤ rate) (hrateL : rate ≤ L) :
    rate + Real.exp (-L) ≤ rate / (1 - Real.exp (-rate)) := by
  have hrate0 : 0 < rate := by linarith
  have he0 : 0 < Real.exp (-rate) := Real.exp_pos _
  have hd0 : 0 < Real.exp (-L) := Real.exp_pos _
  have hle : Real.exp (-L) ≤ Real.exp (-rate) := Real.exp_le_exp.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-rate) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  apply (le_div_iff₀ hden).mpr
  nlinarith [mul_nonneg (show 0 ≤ rate - 1 by linarith) he0.le, mul_nonneg hd0.le he0.le]

theorem hazard_step_bound (L : ℝ) (hL : 1 ≤ L) (n : ℕ) :
    ∀ u : ℝ, (n : ℝ) + 2 ≤ u →
      min L (1 + (n : ℝ) * Real.exp (-L)) ≤ hazard u := by
  induction n with
  | zero =>
      intro u hu
      simp only [Nat.cast_zero, zero_mul, add_zero, min_eq_right hL]
      exact hazard_ge_one (by simpa only [Nat.cast_zero, zero_add] using hu)
  | succ n ih =>
      intro u hu
      let d := Real.exp (-L)
      let rate := min L (1 + (n : ℝ) * d)
      have hd : 0 < d := Real.exp_pos _
      have hr1 : 1 ≤ rate := le_min hL (by have hn := Nat.cast_nonneg (α := ℝ) n; nlinarith)
      have hrL : rate ≤ L := min_le_left _ _
      have htail : ∀ t : ℝ, (n : ℝ) + 2 ≤ t → rate ≤ hazard t := fun t ht => ih t ht
      have hboost := hazard_bootstrap ((n : ℝ) + 2) rate u
        (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith) htail
        (by push_cast at hu; linarith)
      have hgain := bootstrap_uniform_gain L rate hr1 hrL
      have hstep : min L (1 + ((n + 1 : ℕ) : ℝ) * d) ≤ rate + d := by
        by_cases hcase : L ≤ 1 + (n : ℝ) * d
        · have hr : rate = L := min_eq_left hcase
          rw [hr]
          exact (min_le_left _ _).trans (by linarith)
        · have hr : rate = 1 + (n : ℝ) * d := min_eq_right (le_of_not_ge hcase)
          rw [hr]
          have hm := min_le_right L (1 + ((n + 1 : ℕ) : ℝ) * d)
          push_cast at hm ⊢
          linarith
      exact hstep.trans (hgain.trans hboost)

theorem exists_hazard_tail (rate : ℝ) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ u : ℝ, T ≤ u → rate ≤ hazard u := by
  let L := max 1 rate
  let d := Real.exp (-L)
  have hL : 1 ≤ L := le_max_left _ _
  have hd : 0 < d := Real.exp_pos _
  obtain ⟨n, hn⟩ := exists_nat_ge ((L - 1) / d)
  have hreach : L ≤ 1 + (n : ℝ) * d := by
    have h := (div_le_iff₀ hd).mp hn
    linarith
  refine ⟨(n : ℝ) + 2, by have h := Nat.cast_nonneg (α := ℝ) n; linarith, ?_⟩
  intro u hu
  have h := hazard_step_bound L hL n u hu
  rw [min_eq_left hreach] at h
  exact (le_max_right 1 rate).trans h

theorem negative_logDeriv_tail (rate : ℝ) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ u : ℝ, T ≤ u → rate ≤ -deriv rho u / rho u := by
  obtain ⟨T, hT, htail⟩ := exists_hazard_tail rate
  refine ⟨T, hT, ?_⟩
  intro u hu
  rw [← hazard_eq_neg_deriv (by linarith : 1 < u)]
  exact htail u hu

theorem hazard_tendsto_atTop : Tendsto hazard atTop atTop := by
  apply tendsto_atTop.mpr
  intro rate
  obtain ⟨T, _, htail⟩ := exists_hazard_tail rate
  exact eventually_atTop.mpr ⟨T, htail⟩

theorem rho_exponential_majorant (rate : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 2 ≤ T ∧ ∀ u : ℝ, T ≤ u →
      rho u ≤ C * Real.exp (-rate * u) := by
  obtain ⟨T, hT, htail⟩ := exists_hazard_tail rate
  refine ⟨rho T * Real.exp (rate * T), mul_pos (rho_pos T) (Real.exp_pos _), T, hT, ?_⟩
  intro u hu
  have h := rho_exponential_comparison T rate T u hT htail le_rfl hu
  have heq : Real.exp (-rate * (u - T)) = Real.exp (rate * T) * Real.exp (-rate * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at h
  simpa only [mul_assoc] using h

theorem rho_faster_than_exponential (rate : ℝ) :
    Tendsto (fun u : ℝ => Real.exp (rate * u) * rho u) atTop (𝓝 0) := by
  obtain ⟨C, hC, T, _, hbound⟩ := rho_exponential_majorant (rate + 1)
  have hUpper : (fun u : ℝ => Real.exp (rate * u) * rho u) ≤ᶠ[atTop]
      (fun u => C * Real.exp (-u)) := by
    apply eventually_atTop.mpr
    refine ⟨T, ?_⟩
    intro u hu
    have h := mul_le_mul_of_nonneg_left (hbound u hu) (Real.exp_pos (rate * u)).le
    have heq : Real.exp (rate * u) * (C * Real.exp (-(rate + 1) * u)) = C * Real.exp (-u) := by
      calc
        _ = C * (Real.exp (rate * u) * Real.exp (-(rate + 1) * u)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 1; congr 1; ring
    rw [heq] at h
    exact h
  have hLower : (0 : ℝ → ℝ) ≤ᶠ[atTop] (fun u : ℝ => Real.exp (rate * u) * rho u) :=
    Filter.Eventually.of_forall (fun u => mul_nonneg (Real.exp_pos _).le (rho_nonneg u))
  have hLimit : Tendsto (fun u : ℝ => C * Real.exp (-u)) atTop (𝓝 0) := by
    simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  exact squeeze_zero' hLower hUpper hLimit

theorem rho_tendsto_zero : Tendsto rho atTop (𝓝 0) := by
  simpa only [zero_mul, Real.exp_zero, one_mul] using rho_faster_than_exponential 0

end NumberTheoryLean.DickmanDecay

end

section

namespace NumberTheoryLean.DickmanFiniteDecay

open Dickman

theorem rho_le_one (u : ℝ) : rho u ≤ 1 := by
  by_cases hu : u ≤ 1
  · rw [rho_initial hu]
  · have h := rho_antitone (le_of_lt (lt_of_not_ge hu))
    simpa only [rho_initial (le_refl (1:ℝ))] using h

theorem rho_step_power {t u : ℝ} (ht : 1 ≤ t) (htu : t ≤ u) (n : ℕ) :
    t^n*rho (u+(n:ℝ)) ≤ rho u := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have hh := rho_upper_comparison (u := u+(n:ℝ)+1) (by linarith)
    have hs : t*rho (u+(n:ℝ)+1) ≤ rho (u+(n:ℝ)) := by
      have hm := mul_le_mul_of_nonneg_right (show t ≤ u+(n:ℝ)+1 by linarith)
        (rho_nonneg (u+(n:ℝ)+1))
      simp only [add_sub_cancel_right] at hh
      exact hm.trans hh
    have hmul := mul_le_mul_of_nonneg_left hs (pow_nonneg (by linarith : 0 ≤ t) n)
    push_cast
    rw [pow_succ]
    simpa only [add_assoc,mul_assoc] using hmul.trans ih

theorem rho_half_power {u : ℝ} (hu : 2 ≤ u) :
    rho u ≤ 1/(u/2)^⌊u/2⌋₊ := by
  have hu0 : 0 < u := by linarith
  have hf := Nat.floor_le (by linarith : 0 ≤ u/2)
  have hh := rho_step_power (t := u/2) (u := u-(⌊u/2⌋₊:ℝ))
    (by linarith) (by linarith) ⌊u/2⌋₊
  simp only [sub_add_cancel] at hh
  apply (le_div_iff₀ (pow_pos (by linarith : 0 < u/2) _)).mpr
  rw [mul_comm]
  exact hh.trans (rho_le_one _)

theorem rho_log_decay {u : ℝ} (hu : 8 ≤ u) :
    rho u ≤ Real.exp (-(1/16:ℝ)*u*Real.log (u+2)) := by
  have hu0 : 0 < u := by linarith
  have ht0 : 0 < u/2 := by linarith
  have hn : u/4 ≤ (⌊u/2⌋₊:ℝ) := by
    have hf := Nat.lt_floor_add_one (u/2)
    linarith
  have hl0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hlh : Real.log u/2 ≤ Real.log (u/2) := by
    have hm := Real.log_le_log hu0 (show u ≤ (u/2)^2 by nlinarith)
    rw [Real.log_pow] at hm
    norm_num only [Nat.cast_ofNat] at hm
    linarith
  have hl2 : Real.log (u+2) ≤ 2*Real.log u := by
    have hm := Real.log_le_log (show 0 < u+2 by linarith) (show u+2 ≤ u^2 by nlinarith)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hm
  have hpow : (1/16:ℝ)*u*Real.log (u+2) ≤ (⌊u/2⌋₊:ℝ)*Real.log (u/2) := by
    have hm := mul_le_mul hn hlh (by linarith : 0 ≤ Real.log u/2) (Nat.cast_nonneg ⌊u/2⌋₊)
    nlinarith [mul_le_mul_of_nonneg_left hl2 hu0.le]
  calc
    _ ≤ 1/(u/2)^⌊u/2⌋₊ := rho_half_power (by linarith)
    _ = Real.exp (-(⌊u/2⌋₊:ℝ)*Real.log (u/2)) := by
      rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log ht0]
      exact one_div _
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

end NumberTheoryLean.DickmanFiniteDecay

end

end Erdos970

end OAI

namespace OAI

/-!
# The continuous Dickman distribution function

Continuity and endpoint behavior of the Dickman function determine its
continuous distribution function and the limiting order probabilities.
-/

namespace JointDickman

open Filter Erdos970.NumberTheoryLean
open scoped Topology

noncomputable def dickmanCDF (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else Dickman.rho (1 / t)

@[simp] theorem dickmanCDF_zero : dickmanCDF 0 = 0 := by simp [dickmanCDF]

theorem dickmanCDF_nonneg (t : ℝ) : 0 ≤ dickmanCDF t := by
  unfold dickmanCDF
  split_ifs
  · exact le_rfl
  · exact Dickman.rho_nonneg _

theorem dickmanCDF_le_one (t : ℝ) : dickmanCDF t ≤ 1 := by
  unfold dickmanCDF
  split_ifs
  · norm_num
  · exact DickmanFiniteDecay.rho_le_one _

theorem dickmanCDF_eq_one {t : ℝ} (ht : 1 ≤ t) : dickmanCDF t = 1 := by
  rw [dickmanCDF, if_neg (by linarith)]
  apply Dickman.rho_initial
  exact (div_le_one (by linarith : 0 < t)).mpr ht

theorem dickmanCDF_monotone : Monotone dickmanCDF := by
  intro a b hab
  by_cases ha : a ≤ 0
  · simpa [dickmanCDF, ha] using dickmanCDF_nonneg b
  have ha' : 0 < a := lt_of_not_ge ha
  have hb : 0 < b := ha'.trans_le hab
  simp only [dickmanCDF, if_neg ha, if_neg (not_le.mpr hb)]
  exact Dickman.rho_antitone (one_div_le_one_div_of_le ha' hab)

theorem dickmanCDF_continuousAt_zero : ContinuousAt dickmanCDF 0 := by
  have hl : Tendsto dickmanCDF (𝓝[≤] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≤ 0 := ht
    simp [dickmanCDF, ht']
  have hr : Tendsto dickmanCDF (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := DickmanDecay.rho_tendsto_zero.comp
      (tendsto_inv_nhdsGT_zero : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop)
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    simp [dickmanCDF, not_le.mpr ht', one_div]
  have h := hl.sup hr
  rw [nhdsLE_sup_nhdsGT] at h
  simpa [ContinuousAt] using h

theorem dickmanCDF_continuous : Continuous dickmanCDF := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 t] dickmanCDF := by
      filter_upwards [eventually_lt_nhds ht] with x hx
      simp [dickmanCDF, hx.le]
    have h : Tendsto dickmanCDF (𝓝 t) (𝓝 0) := tendsto_const_nhds.congr' heq
    simpa [ContinuousAt, dickmanCDF, ht.le] using h
  · exact dickmanCDF_continuousAt_zero
  · have heq : (fun x : ℝ => Dickman.rho (1 / x)) =ᶠ[𝓝 t] dickmanCDF := by
      filter_upwards [eventually_gt_nhds ht] with x hx
      simp [dickmanCDF, not_le.mpr hx]
    have hcomp : ContinuousAt (fun x : ℝ => Dickman.rho (1 / x)) t :=
      Dickman.rho_continuous.continuousAt.comp
        (continuousAt_const.div continuousAt_id (ne_of_gt ht))
    have h := hcomp.tendsto.congr' heq
    simpa [ContinuousAt, dickmanCDF, not_le.mpr ht] using h

end JointDickman

end OAI

-- OAI.NumberTheory.JointDickman.Amplification.ArithmeticInputs

namespace OAI

namespace JointDickman

open Filter Finset
open scoped Topology

namespace PublishedInputs

def PrimeReciprocalMertensInput : Prop :=
  ∃ M C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
    |(∑ p ∈ (Icc 2 ⌊x⌋₊).filter Nat.Prime, 1 / (p : ℝ)) -
      Real.log (Real.log x) - M| ≤ C / Real.log x

end PublishedInputs

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.MertensDischarge

namespace OAI

namespace JointDickman
open Finset Filter
open scoped Topology

theorem prime_filter_Icc_eq_Ioc (N : ℕ) :
    (Icc 2 N).filter Nat.Prime = (Ioc 0 N).filter Nat.Prime := by
  ext p
  simp only [mem_filter,mem_Icc,mem_Ioc]
  constructor
  · rintro ⟨⟨hp,hN⟩,hprime⟩
    exact ⟨⟨by omega,hN⟩,hprime⟩
  · rintro ⟨⟨_,hN⟩,hprime⟩
    exact ⟨⟨hprime.two_le,hN⟩,hprime⟩

theorem primeReciprocalMertensInput : PublishedInputs.PrimeReciprocalMertensInput := by
  refine ⟨Erdos970.Mertens.M,Real.log 4 + 6 + Erdos970.Mertens.E₁,?_,?_⟩
  · have hE := Erdos970.Mertens.E₁.nonneg
    positivity
  · intro x hx
    rw [prime_filter_Icc_eq_Ioc]
    exact Erdos970.Mertens.E₂p.abs_le hx

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.PrimeTupleBounds

namespace OAI

namespace JointDickman

open Filter
open scoped Topology BigOperators

def PrimeCountingUpperBound (C y : ℝ) : Prop :=
  ∀ t : ℝ, y ≤ t → (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ C * t / Real.log t

noncomputable def largePrimeSet (N y : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊N⌋₊).filter (fun p => y < (p : ℝ))

noncomputable def primeTupleCount (P : Finset ℕ) (h : ℕ) (N : ℝ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin h => P).filter
    (fun f => (∏ i, (f i : ℝ)) ≤ N)).card

private theorem card_filter_product_real {α β : Type*}
    [DecidableEq α] [DecidableEq β] (A : Finset α) (B : Finset β)
    (Q : α → β → Prop) [∀ a, DecidablePred (Q a)] :
    (((A.product B).filter (fun ab => Q ab.1 ab.2)).card : ℝ) =
      ∑ a ∈ A, ((B.filter (Q a)).card : ℝ) := by
  classical
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  exact Finset.sum_product' A B (fun a b => ((if Q a b then 1 else 0 : ℕ) : ℝ))

theorem prime_product_fiber_bound {P : Finset ℕ} {C y N r : ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ y < (p : ℝ)) (hC : 0 ≤ C)
    (hy : 1 < y) (hN : 0 ≤ N) (hr : 0 < r)
    (hcount : PrimeCountingUpperBound C y) :
    ((P.filter (fun p : ℕ => r * (p : ℝ) ≤ N)).card : ℝ) ≤
      (C * N / Real.log y) * (1 / r) := by
  classical
  have hlogy : 0 < Real.log y := Real.log_pos hy
  by_cases ht : y ≤ N / r
  · have hsub : P.filter (fun p : ℕ => r * (p : ℝ) ≤ N) ⊆ Nat.primesLE ⌊N / r⌋₊ := by
      intro p hp
      obtain ⟨hpP, hpN⟩ := Finset.mem_filter.mp hp
      apply Nat.mem_primesLE.mpr
      refine ⟨?_, (hP p hpP).1⟩
      apply Nat.le_floor
      exact (le_div_iff₀ hr).mpr (by simpa [mul_comm] using hpN)
    have hcard : ((P.filter (fun p : ℕ => r * (p : ℝ) ≤ N)).card : ℝ) ≤
        Nat.primeCounting ⌊N / r⌋₊ := by
      have hc := Finset.card_le_card hsub
      rw [Nat.primesLE_card_eq_primeCounting] at hc
      exact_mod_cast hc
    have hlog : Real.log y ≤ Real.log (N / r) :=
      Real.log_le_log (lt_trans zero_lt_one hy) ht
    calc
      _ ≤ (Nat.primeCounting ⌊N / r⌋₊ : ℝ) := hcard
      _ ≤ C * (N / r) / Real.log (N / r) := hcount _ ht
      _ ≤ C * (N / r) / Real.log y :=
        div_le_div_of_nonneg_left (mul_nonneg hC (div_nonneg hN hr.le)) hlogy hlog
      _ = _ := by ring
  · have hemp : P.filter (fun p : ℕ => r * (p : ℝ) ≤ N) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hpP, hpN⟩ := Finset.mem_filter.mp hp
      have hpupper : (p : ℝ) ≤ N / r :=
        (le_div_iff₀ hr).mpr (by simpa [mul_comm] using hpN)
      exact ht ((hP p hpP).2.le.trans hpupper)
    rw [hemp]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

private theorem primeTupleCount_le_fibers (P : Finset ℕ) (h : ℕ) (N : ℝ) :
    (primeTupleCount P (h + 1) N : ℝ) ≤
      ∑ f ∈ Fintype.piFinset (fun _ : Fin h => P),
        ((P.filter (fun p : ℕ => (∏ i, (f i : ℝ)) * (p : ℝ) ≤ N)).card : ℝ) := by
  classical
  let A : Finset (Fin (h + 1) → ℕ) := (Fintype.piFinset fun _ : Fin (h + 1) => P).filter
    (fun f : Fin (h + 1) → ℕ => (∏ i, (f i : ℝ)) ≤ N)
  let B : Finset ((Fin h → ℕ) × ℕ) :=
    ((Fintype.piFinset fun _ : Fin h => P).product P).filter
      (fun fp : (Fin h → ℕ) × ℕ => (∏ i, (fp.1 i : ℝ)) * (fp.2 : ℝ) ≤ N)
  have hmap : Set.MapsTo (fun f : Fin (h + 1) → ℕ => (Fin.tail f, f 0)) A B := by
    intro f hf
    obtain ⟨hfP, hfN⟩ := Finset.mem_filter.mp hf
    have hall := Fintype.mem_piFinset.mp hfP
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr (fun i => hall i.succ), hall 0⟩, ?_⟩
    change (∏ i : Fin h, (f i.succ : ℝ)) * (f 0 : ℝ) ≤ N
    have hprod := Fin.prod_univ_succ (fun i : Fin (h + 1) => (f i : ℝ))
    rw [hprod] at hfN
    simpa only [mul_comm] using hfN
  have hinj : (↑A : Set (Fin (h + 1) → ℕ)).InjOn
      (fun f => (Fin.tail f, f 0)) := by
    intro f hf g hg heq
    have htail := congrArg Prod.fst heq
    have hzero := congrArg Prod.snd heq
    ext i
    exact Fin.cases hzero (fun j => congrFun htail j) i
  have hc : (A.card : ℝ) ≤ B.card := by
    exact Nat.cast_le.mpr (Finset.card_le_card_of_injOn _ hmap hinj)
  calc
    _ = (A.card : ℝ) := rfl
    _ ≤ (B.card : ℝ) := hc
    _ = _ := card_filter_product_real (Fintype.piFinset fun _ : Fin h => P) P
      (fun (f : Fin h → ℕ) (p : ℕ) => (∏ i, (f i : ℝ)) * (p : ℝ) ≤ N)

theorem primeTupleCount_bound {P : Finset ℕ} {C y N : ℝ} (h : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ y < (p : ℝ)) (hC : 0 ≤ C)
    (hy : 1 < y) (hN : 0 ≤ N) (hcount : PrimeCountingUpperBound C y) :
    (primeTupleCount P (h + 1) N : ℝ) ≤
      (C * N / Real.log y) * (∑ p ∈ P, 1 / (p : ℝ)) ^ h := by
  classical
  calc
    _ ≤ ∑ f ∈ Fintype.piFinset (fun _ : Fin h => P),
        ((P.filter (fun p : ℕ => (∏ i, (f i : ℝ)) * (p : ℝ) ≤ N)).card : ℝ) :=
      primeTupleCount_le_fibers P h N
    _ ≤ ∑ f ∈ Fintype.piFinset (fun _ : Fin h => P),
        (C * N / Real.log y) * (1 / ∏ i, (f i : ℝ)) := by
      apply Finset.sum_le_sum
      intro f hf
      apply prime_product_fiber_bound hP hC hy hN _ hcount
      apply Finset.prod_pos
      intro i _
      exact lt_trans (lt_trans zero_lt_one hy)
        (hP (f i) (Fintype.mem_piFinset.mp hf i)).2
    _ = (C * N / Real.log y) * (∑ p ∈ P, 1 / (p : ℝ)) ^ h := by
      rw [← Finset.mul_sum, Finset.sum_pow']
      congr 1
      apply Finset.sum_congr rfl
      intro f _
      simp only [one_div, Finset.prod_inv_distrib]

theorem largePrimeTupleCount_bound {C y N : ℝ} (h : ℕ) (hC : 0 ≤ C)
    (hy : 1 < y) (hN : 0 ≤ N) (hcount : PrimeCountingUpperBound C y) :
    (primeTupleCount (largePrimeSet N y) (h + 1) N : ℝ) ≤
      (C * N / Real.log y) * (∑ p ∈ largePrimeSet N y, 1 / (p : ℝ)) ^ h := by
  apply primeTupleCount_bound h _ hC hy hN hcount
  intro p hp
  obtain ⟨hpP, hpy⟩ := Finset.mem_filter.mp hp
  exact ⟨(Nat.mem_primesLE.mp hpP).2, hpy⟩

theorem largePrimeTupleCount_density_tendsto_zero (h : ℕ) {c C K : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hcount : ∀ᶠ N : ℝ in atTop, PrimeCountingUpperBound C (N ^ c))
    (hrecip : ∀ᶠ N : ℝ in atTop,
      (∑ p ∈ largePrimeSet N (N ^ c), 1 / (p : ℝ)) ≤ K) :
    Tendsto (fun N : ℝ =>
      (primeTupleCount (largePrimeSet N (N ^ c)) (h + 1) N : ℝ) / N)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℝ => Real.log (N ^ c)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_rpow_atTop hc)
  have hlim : Tendsto (fun N : ℝ => C * K ^ h / Real.log (N ^ c)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · filter_upwards [hcount, hrecip, eventually_gt_atTop (1 : ℝ)] with N hCN hKN hN
    have hN0 : 0 < N := lt_trans zero_lt_one hN
    have hy : 1 < N ^ c := Real.one_lt_rpow hN hc
    have hlogpos : 0 < Real.log (N ^ c) := Real.log_pos hy
    have hsum0 : 0 ≤ ∑ p ∈ largePrimeSet N (N ^ c), 1 / (p : ℝ) := by
      apply Finset.sum_nonneg
      intro p hp
      positivity
    have hpowers := pow_le_pow_left₀ hsum0 hKN h
    have hbound := (largePrimeTupleCount_bound h hC hy hN0.le hCN).trans
      (mul_le_mul_of_nonneg_left hpowers (by positivity))
    calc
      _ ≤ ((C * N / Real.log (N ^ c)) * K ^ h) / N :=
        div_le_div_of_nonneg_right hbound hN0.le
      _ = C * K ^ h / Real.log (N ^ c) := by field_simp

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.PrimeIntervalSums

namespace OAI

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def primeReciprocalSum (x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)

theorem primesLE_eq_filter (N : ℕ) :
    Nat.primesLE N = (Icc 2 N).filter Nat.Prime := by
  apply Finset.ext
  intro p
  simp only [Nat.mem_primesLE, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hle, hp⟩
    exact ⟨⟨hp.two_le, hle⟩, hp⟩
  · rintro ⟨⟨_, hle⟩, hp⟩
    exact ⟨hle, hp⟩

theorem primeReciprocalSum_remainder_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ M : ℝ, Tendsto (fun x : ℝ => primeReciprocalSum x - Real.log (Real.log x))
      atTop (𝓝 M) := by
  obtain ⟨M, C, _, hC⟩ := hM
  refine ⟨M, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hlim : Tendsto (fun x : ℝ => C / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  simpa [Real.norm_eq_abs, primeReciprocalSum, primesLE_eq_filter] using hC x hx

theorem largePrimeSet_eq_sdiff {N y : ℝ} (hy : 0 ≤ y) :
    largePrimeSet N y = Nat.primesLE ⌊N⌋₊ \ Nat.primesLE ⌊y⌋₊ := by
  apply Finset.ext
  intro p
  rw [Finset.mem_sdiff]
  simp only [largePrimeSet, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpN, hp⟩, hpy⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    rintro ⟨hpy', _⟩
    exact (not_le_of_gt hpy) ((Nat.le_floor_iff hy).mp hpy')
  · rintro ⟨⟨hpN, hp⟩, hnot⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    by_contra h
    exact hnot ⟨Nat.le_floor (le_of_not_gt h), hp⟩

theorem largePrimeSet_reciprocal_eq {N y : ℝ} (hy : 0 ≤ y) (hyN : y ≤ N) :
    (∑ p ∈ largePrimeSet N y, 1 / (p : ℝ)) = primeReciprocalSum N - primeReciprocalSum y := by
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊N⌋₊ := by
    intro p hp
    obtain ⟨hpy, hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpy.trans (Nat.floor_mono hyN), hp⟩
  rw [largePrimeSet_eq_sdiff hy]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

theorem largePrimeSet_reciprocal_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun N : ℝ => ∑ p ∈ largePrimeSet N (N ^ c), 1 / (p : ℝ))
      atTop (𝓝 (-Real.log c)) := by
  obtain ⟨M, hrem⟩ := primeReciprocalSum_remainder_tendsto hM
  have hpower : Tendsto (fun N : ℝ => N ^ c) atTop atTop := tendsto_rpow_atTop hc
  have hlim := (hrem.sub (hrem.comp hpower)).sub_const (Real.log c)
  have heq : (fun N : ℝ =>
      (primeReciprocalSum N - Real.log (Real.log N)) -
      (primeReciprocalSum (N ^ c) - Real.log (Real.log (N ^ c))) - Real.log c) =ᶠ[atTop]
      (fun N : ℝ => ∑ p ∈ largePrimeSet N (N ^ c), 1 / (p : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := lt_trans zero_lt_one hN
    have hlog : 0 < Real.log N := Real.log_pos hN
    have hpN : N ^ c ≤ N := by
      simpa using Real.rpow_le_rpow_of_exponent_le hN.le hc1
    rw [largePrimeSet_reciprocal_eq (Real.rpow_nonneg hN0.le c) hpN,
      Real.log_rpow hN0, Real.log_mul hc.ne' hlog.ne']
    ring
  simpa using hlim.congr' heq

namespace PublishedInputs

def ChebyshevPrimeCountingInput : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ t →
    (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ C * t / Real.log t

end PublishedInputs

theorem largePrimeTupleCount_tendsto_of_published
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hCheb : PublishedInputs.ChebyshevPrimeCountingInput)
    (h : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun N : ℝ =>
      (primeTupleCount (largePrimeSet N (N ^ c)) (h + 1) N : ℝ) / N)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hcount⟩ := hCheb
  have hrecip := largePrimeSet_reciprocal_tendsto hM hc hc1
  apply largePrimeTupleCount_density_tendsto_zero h hc hC
  · filter_upwards [(tendsto_rpow_atTop hc).eventually (eventually_ge_atTop (2 : ℝ))] with N hN
    intro t ht
    exact hcount t (hN.trans ht)
  · have hb := hrecip.eventually (Iio_mem_nhds (lt_add_one (-Real.log c)))
    exact hb.mono (fun _ hh => hh.le)

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.PrimeLogIntervals

namespace OAI

namespace JointDickman
open Finset Filter
open scoped Topology

theorem prime_power_interval_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ => ∑ p ∈ largePrimeSet (x^b) (x^a), 1/(p : ℝ))
      atTop (𝓝 (Real.log b-Real.log a)) := by
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨M,hM⟩ := primeReciprocalSum_remainder_tendsto primeReciprocalMertensInput
  have hlim := ((hM.comp (tendsto_rpow_atTop hb)).sub
    (hM.comp (tendsto_rpow_atTop ha))).add_const (Real.log b-Real.log a)
  have heq : (fun x : ℝ =>
      (primeReciprocalSum (x^b)-Real.log (Real.log (x^b))) -
      (primeReciprocalSum (x^a)-Real.log (Real.log (x^a))) +
        (Real.log b-Real.log a)) =ᶠ[atTop]
      (fun x : ℝ => ∑ p ∈ largePrimeSet (x^b) (x^a), 1/(p : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hlog : 0 < Real.log x := Real.log_pos hx
    rw [largePrimeSet_reciprocal_eq (Real.rpow_nonneg hx0.le a)
      (Real.rpow_le_rpow_of_exponent_le hx.le hab),
      Real.log_rpow hx0,Real.log_rpow hx0,
      Real.log_mul hb.ne' hlog.ne',Real.log_mul ha.ne' hlog.ne']
    ring
  simpa only [sub_self,zero_add] using hlim.congr' heq

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.PrimeLogMeasure

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

noncomputable def finiteDirac (t : ℝ) : FiniteMeasure ℝ :=
  ⟨Measure.dirac t, inferInstance⟩

noncomputable def primeLogMeasure (c x : ℝ) : FiniteMeasure ℝ :=
  ∑ p ∈ largePrimeSet x (x^c),
    (Real.toNNReal (1/(p : ℝ))) • finiteDirac (Real.log p/Real.log x)

open Classical in
theorem primeLogMeasure_apply (c x : ℝ) (s : Set ℝ) :
    ((primeLogMeasure c x) s : ℝ) =
      ∑ p ∈ largePrimeSet x (x^c),
        if Real.log p/Real.log x ∈ s then 1/(p : ℝ) else 0 := by
  classical
  unfold primeLogMeasure
  induction largePrimeSet x (x^c) using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    simp only [sum_insert hp, FiniteMeasure.coeFn_add, Pi.add_apply,
      NNReal.coe_add, FiniteMeasure.smul_apply, smul_eq_mul, NNReal.coe_mul, ih]
    congr 1
    by_cases h : Real.log p/Real.log x ∈ s <;>
      simp [finiteDirac, Measure.dirac_apply, h]

theorem logPrimeLocation_mem_Ioc {x : ℝ} (hx : 1 < x) {p : ℕ}
    (hp : 0 < p) (a b : ℝ) :
    Real.log p/Real.log x ∈ Set.Ioc a b ↔ x^a < p ∧ (p : ℝ) ≤ x^b := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < Real.log x := Real.log_pos hx
  rw [Set.mem_Ioc, lt_div_iff₀ hlog, div_le_iff₀ hlog]
  constructor
  · rintro ⟨ha,hb⟩
    constructor
    · apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hx0 a) hp0).mp
      simpa only [Real.log_rpow hx0, mul_comm] using ha
    · apply (Real.log_le_log_iff hp0 (Real.rpow_pos_of_pos hx0 b)).mp
      simpa only [Real.log_rpow hx0, mul_comm] using hb
  · rintro ⟨ha,hb⟩
    constructor
    · have := (Real.log_lt_log_iff (Real.rpow_pos_of_pos hx0 a) hp0).mpr ha
      simpa only [Real.log_rpow hx0, mul_comm] using this
    · have := (Real.log_le_log_iff hp0 (Real.rpow_pos_of_pos hx0 b)).mpr hb
      simpa only [Real.log_rpow hx0, mul_comm] using this

theorem primeLogMeasure_Ioc {c x a b : ℝ} (hx : 1 < x)
    (hca : c ≤ a) (hb : b ≤ 1) :
    ((primeLogMeasure c x) (Set.Ioc a b) : ℝ) =
      ∑ p ∈ largePrimeSet (x^b) (x^a), 1/(p : ℝ) := by
  classical
  rw [primeLogMeasure_apply]
  trans ∑ p ∈ (largePrimeSet x (x^c)).filter (fun p : ℕ => Real.log p/Real.log x ∈ Set.Ioc a b), 1/(p : ℝ)
  · symm
    convert sum_filter (s := largePrimeSet x (x^c)) (p := fun p : ℕ => Real.log p/Real.log x ∈ Set.Ioc a b) (f := fun p => 1/(p : ℝ)) using 1
    congr 3
    funext p
    split_ifs <;> rfl
  apply sum_congr
  · ext p
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hcb : x^c ≤ x^a := Real.rpow_le_rpow_of_exponent_le hx.le hca
    have hbx : x^b ≤ x := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx.le hb
    simp only [mem_filter, largePrimeSet, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨hpN,hp⟩,hpc⟩,hloc⟩
      obtain ⟨hpa,hpb⟩ := (logPrimeLocation_mem_Ioc hx hp.pos a b).mp hloc
      exact ⟨⟨Nat.le_floor hpb,hp⟩,hpa⟩
    · rintro ⟨⟨hpN,hp⟩,hpa⟩
      have hpb : (p : ℝ) ≤ x^b := (Nat.le_floor_iff (Real.rpow_nonneg hx0.le b)).mp hpN
      exact ⟨⟨⟨Nat.le_floor (hpb.trans hbx),hp⟩,hcb.trans_lt hpa⟩,
        (logPrimeLocation_mem_Ioc hx hp.pos a b).mpr ⟨hpa,hpb⟩⟩
  · intros; rfl

theorem primeLogMeasure_interval_tendsto {c a b : ℝ}
    (ha : 0 < a) (hca : c ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun x => ((primeLogMeasure c x) (Set.Ioc a b) : ℝ))
      atTop (𝓝 (Real.log b-Real.log a)) := by
  apply (prime_power_interval_tendsto ha hab).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (primeLogMeasure_Ioc hx hca hb).symm

noncomputable def logIntervalVolume (c : ℝ) : FiniteMeasure ℝ :=
  ⟨volume.restrict (Set.Ioc (Real.log c) 0), inferInstance⟩

noncomputable def logarithmicPrimeMeasure (c : ℝ) : FiniteMeasure ℝ :=
  (logIntervalVolume c).map Real.exp

theorem logarithmicPrimeMeasure_Ioc {c a b : ℝ}
    (hc : 0 < c) (hca : c ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ((logarithmicPrimeMeasure c) (Set.Ioc a b) : ℝ) = Real.log b-Real.log a := by
  have ha : 0 < a := hc.trans_le hca
  have hb0 : 0 < b := ha.trans_le hab
  have hpre : Real.exp ⁻¹' Set.Ioc a b = Set.Ioc (Real.log a) (Real.log b) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioc, ← Real.log_lt_iff_lt_exp ha,
      ← Real.le_log_iff_exp_le hb0]
  have hsub : Set.Ioc (Real.log a) (Real.log b) ⊆ Set.Ioc (Real.log c) 0 := by
    intro t ht
    exact ⟨(Real.log_le_log hc hca).trans_lt ht.1,
      ht.2.trans (Real.log_nonpos hb0.le hb)⟩
  rw [logarithmicPrimeMeasure, FiniteMeasure.map_apply _ Real.measurable_exp measurableSet_Ioc,
    hpre, logIntervalVolume, FiniteMeasure.mk_apply, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr hsub, Real.volume_Ioc]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (Real.log_le_log ha hab))

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.PrimeMeasureSupport

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem primeLogMeasure_support (c : ℝ) {x : ℝ} (hx : 1 < x) :
    primeLogMeasure c x (Set.Ioc c 1)ᶜ = 0 := by
  apply NNReal.coe_injective
  rw [primeLogMeasure_apply, NNReal.coe_zero]
  apply sum_eq_zero
  intro p hp
  obtain ⟨hpm,hpc⟩ := mem_filter.mp hp
  obtain ⟨hpN,hp⟩ := Nat.mem_primesLE.mp hpm
  have hpx : (p : ℝ) ≤ x := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mp hpN
  have hloc := (logPrimeLocation_mem_Ioc hx hp.pos c 1).mpr
    (show x^c < p ∧ (p : ℝ) ≤ x^1 by simpa using And.intro hpc hpx)
  exact if_neg (by simpa only [Set.mem_compl_iff, not_not] using hloc)

theorem finiteMeasure_inter_of_support (μ : FiniteMeasure ℝ) {s : Set ℝ}
    (hμ : μ sᶜ = 0) {t : Set ℝ} (ht : MeasurableSet t) : μ (t ∩ s) = μ t := by
  have hnull : (μ : Measure ℝ) sᶜ = 0 := (μ.null_iff_toMeasure_null _).mp hμ
  have hr : (μ : Measure ℝ).restrict s = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    exact hnull
  apply (ENNReal.coe_inj).mp
  simp only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  rw [← Measure.restrict_apply ht, hr]

theorem finiteMeasure_Ioc_clip (μ : FiniteMeasure ℝ) {c : ℝ}
    (hμ : μ (Set.Ioc c 1)ᶜ = 0) (a b : ℝ) :
    μ (Set.Ioc a b) = μ (Set.Ioc (max a c) (min b 1)) := by
  rw [← Set.Ioc_inter_Ioc]
  exact (finiteMeasure_inter_of_support μ hμ measurableSet_Ioc).symm

theorem primeLogMeasure_mass (c x : ℝ) :
    ((primeLogMeasure c x).mass : ℝ) = ∑ p ∈ largePrimeSet x (x^c), 1/(p : ℝ) := by
  rw [FiniteMeasure.mass, primeLogMeasure_apply]
  simp

theorem logarithmicPrimeMeasure_support {c : ℝ} (hc : 0 < c) :
    logarithmicPrimeMeasure c (Set.Ioc c 1)ᶜ = 0 := by
  rw [logarithmicPrimeMeasure,
    FiniteMeasure.map_apply _ Real.measurable_exp measurableSet_Ioc.compl,
    logIntervalVolume, FiniteMeasure.mk_apply,
    Measure.restrict_apply (Real.measurable_exp measurableSet_Ioc.compl)]
  have he : (Real.exp ⁻¹' (Set.Ioc c 1)ᶜ) ∩ Set.Ioc (Real.log c) 0 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro t ⟨ht,htc,ht0⟩
    apply ht
    change c < Real.exp t ∧ Real.exp t ≤ 1
    exact ⟨(Real.log_lt_iff_lt_exp hc).mp htc, by simpa using Real.exp_le_exp.mpr ht0⟩
  rw [he]
  simp

theorem logarithmicPrimeMeasure_mass {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ((logarithmicPrimeMeasure c).mass : ℝ) = -Real.log c := by
  have he := finiteMeasure_inter_of_support (logarithmicPrimeMeasure c)
    (logarithmicPrimeMeasure_support hc) MeasurableSet.univ
  simp only [Set.univ_inter] at he
  rw [FiniteMeasure.mass, ← he,
    logarithmicPrimeMeasure_Ioc hc le_rfl hc1 le_rfl, Real.log_one, zero_sub]

theorem primeLogMeasure_mass_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun x => ((primeLogMeasure c x).mass : ℝ)) atTop
      (𝓝 ((logarithmicPrimeMeasure c).mass : ℝ)) := by
  rw [logarithmicPrimeMeasure_mass hc hc1]
  apply (largePrimeSet_reciprocal_tendsto primeReciprocalMertensInput hc hc1).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (primeLogMeasure_mass c x).symm

theorem primeLogMeasure_all_intervals_tendsto {c : ℝ} (hc : 0 < c)
    (a b : ℝ) :
    Tendsto (fun x => ((primeLogMeasure c x) (Set.Ioc a b) : ℝ)) atTop
      (𝓝 ((logarithmicPrimeMeasure c) (Set.Ioc a b) : ℝ)) := by
  have he : (fun x => ((primeLogMeasure c x) (Set.Ioc a b) : ℝ)) =ᶠ[atTop]
      (fun x => ((primeLogMeasure c x) (Set.Ioc (max a c) (min b 1)) : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact congrArg ((↑) : ℝ≥0 → ℝ)
      (finiteMeasure_Ioc_clip _ (primeLogMeasure_support c hx) a b)
  rw [finiteMeasure_Ioc_clip _ (logarithmicPrimeMeasure_support hc) a b]
  by_cases hab : max a c ≤ min b 1
  · rw [logarithmicPrimeMeasure_Ioc hc (le_max_right _ _) hab (min_le_right _ _)]
    exact (primeLogMeasure_interval_tendsto (hc.trans_le (le_max_right _ _))
      (le_max_right _ _) hab (min_le_right _ _)).congr' he.symm
  · have hempty : Set.Ioc (max a c) (min b 1) = ∅ := Set.Ioc_eq_empty_of_le (le_of_not_ge hab)
    have ht : Tendsto (fun x => ((primeLogMeasure c x) (Set.Ioc (max a c) (min b 1)) : ℝ))
        atTop (𝓝 ((logarithmicPrimeMeasure c) (Set.Ioc (max a c) (min b 1)) : ℝ)) := by
      simp only [hempty, FiniteMeasure.coeFn_def, measure_empty, ENNReal.toNNReal_zero, NNReal.coe_zero]
      exact tendsto_const_nhds
    exact ht.congr' he.symm

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.PrimeMeasureWeak

namespace OAI

namespace JointDickman
open Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem finiteMeasure_tendsto_of_Ioc {μ : ℝ → FiniteMeasure ℝ} {ν : FiniteMeasure ℝ}
    (hν : ν ≠ 0)
    (hm : Tendsto (fun x => (μ x).mass) atTop (𝓝 ν.mass))
    (hi : ∀ a b : ℝ, Tendsto (fun x => μ x (Set.Ioc a b)) atTop (𝓝 (ν (Set.Ioc a b)))) :
    Tendsto μ atTop (𝓝 ν) := by
  have hm0 : ν.mass ≠ 0 := ν.mass_nonzero_iff.mpr hν
  have hnz : ∀ᶠ x in atTop, μ x ≠ 0 := by
    filter_upwards [hm.eventually (eventually_ne_nhds hm0)] with x hx
    exact (μ x).mass_nonzero_iff.mp hx
  have hn : Tendsto (fun x => (μ x).normalize) atTop (𝓝 ν.normalize) := by
    apply (isPiSystem_Ioc (id : ℝ → ℝ) (id : ℝ → ℝ)).tendsto_probabilityMeasure_of_tendsto_of_mem
    · rintro s ⟨a,b,hab,rfl⟩
      exact measurableSet_Ioc
    · intro u hu x hx
      obtain ⟨a,b,hx',hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hu.mem_nhds hx)
      let b' := (x+b)/2
      have hxb : x < b' := by dsimp [b']; linarith [hx'.2]
      have hbb : b' < b := by dsimp [b']; linarith [hx'.2]
      refine ⟨Set.Ioc a b', ⟨a,b',hx'.1.trans hxb,rfl⟩, Ioc_mem_nhds hx'.1 hxb, ?_⟩
      intro y hy
      exact hsub ⟨hy.1,hy.2.trans_lt hbb⟩
    · rintro s ⟨a,b,hab,rfl⟩
      have ht := (hm.inv₀ hm0).mul (hi a b)
      rw [← ν.normalize_eq_of_nonzero hν] at ht
      apply ht.congr'
      filter_upwards [hnz] with x hx
      exact ((μ x).normalize_eq_of_nonzero hx _).symm
  exact (FiniteMeasure.tendsto_normalize_iff_tendsto hν).mp ⟨hn,hm⟩

theorem primeLogMeasure_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Tendsto (primeLogMeasure c) atTop (𝓝 (logarithmicPrimeMeasure c)) := by
  have hm0 : (logarithmicPrimeMeasure c).mass ≠ 0 := by
    intro h
    have hz := congrArg ((↑) : ℝ≥0 → ℝ) h
    rw [logarithmicPrimeMeasure_mass hc hc1.le, NNReal.coe_zero] at hz
    have : Real.log c < 0 := Real.log_neg hc hc1
    linarith
  apply finiteMeasure_tendsto_of_Ioc ((logarithmicPrimeMeasure c).mass_nonzero_iff.mp hm0)
  · exact NNReal.tendsto_coe.mp (primeLogMeasure_mass_tendsto hc hc1.le)
  · intro a b
    exact NNReal.tendsto_coe.mp (primeLogMeasure_all_intervals_tendsto hc a b)

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductMeasure

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem finiteMeasure_pi_mass_normalize {ι : Type*} [Fintype ι]
    (μ : ι → FiniteMeasure ℝ) :
    FiniteMeasure.pi μ = (∏ i, (μ i).mass) •
      (ProbabilityMeasure.pi (fun i => (μ i).normalize)).toFiniteMeasure := by
  apply FiniteMeasure.toMeasure_injective
  apply Measure.pi_eq
  intro s hs
  have he : (∏ i, (μ i).mass) * (∏ i, (μ i).normalize (s i)) = ∏ i, μ i (s i) := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl (fun i _ => ((μ i).self_eq_mass_mul_normalize (s i)).symm)
  simp only [FiniteMeasure.toMeasure_smul, ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    ProbabilityMeasure.toMeasure_pi, Measure.coe_nnreal_smul_apply, Measure.pi_pi,
    ← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact_mod_cast he

theorem primeLogProduct_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (h : ℕ) :
    Tendsto (fun x => FiniteMeasure.pi (fun _ : Fin h => primeLogMeasure c x)) atTop
      (𝓝 (FiniteMeasure.pi (fun _ : Fin h => logarithmicPrimeMeasure c))) := by
  have ht := primeLogMeasure_tendsto hc hc1
  have hm0 : logarithmicPrimeMeasure c ≠ 0 := by
    intro hz
    have hm := logarithmicPrimeMeasure_mass hc hc1.le
    rw [hz, FiniteMeasure.zero_mass, NNReal.coe_zero] at hm
    linarith [Real.log_neg hc hc1]
  have hn := FiniteMeasure.tendsto_normalize_of_tendsto ht hm0
  have hp : Tendsto (fun x => ProbabilityMeasure.pi (fun _ : Fin h => (primeLogMeasure c x).normalize))
      atTop (𝓝 (ProbabilityMeasure.pi (fun _ : Fin h => (logarithmicPrimeMeasure c).normalize))) :=
    ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (fun _ => hn))
  have hm := tendsto_finsetProd (univ : Finset (Fin h)) (fun _ _ => ht.mass)
  have hh := hm.smul (ProbabilityMeasure.toFiniteMeasure_continuous.continuousAt.tendsto.comp hp)
  simpa only [Function.comp_apply, ← finiteMeasure_pi_mass_normalize] using hh

theorem finiteMeasure_set_tendsto {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] [Nonempty Ω]
    {F : Filter ι} {μ : ι → FiniteMeasure Ω} {ν : FiniteMeasure Ω}
    (hμ : Tendsto μ F (𝓝 ν)) (hν : ν ≠ 0) {s : Set Ω}
    (hs : ν (frontier s) = 0) : Tendsto (fun x => μ x s) F (𝓝 (ν s)) := by
  have hs' : ν.normalize (frontier s) = 0 := by
    rw [ν.normalize_eq_of_nonzero hν, hs, mul_zero]
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    (FiniteMeasure.tendsto_normalize_of_tendsto hμ hν) hs'
  have hh := hμ.mass.mul ht
  simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using hh

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Amplification.AtomicProductMeasure

namespace OAI

namespace JointDickman
open Finset MeasureTheory
open scoped NNReal ENNReal

noncomputable def finitePointMeasure {Ω : Type*} [MeasurableSpace Ω] (t : Ω) : FiniteMeasure Ω :=
  ⟨Measure.dirac t, inferInstance⟩

open Classical in
theorem finitePointMeasure_apply {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (t : Ω) (s : Set Ω) : finitePointMeasure t s = if t ∈ s then 1 else 0 := by
  by_cases h : t ∈ s <;> simp [finitePointMeasure, Measure.dirac_apply, h]

theorem finiteMeasure_sum_apply {Ω β : Type*} [MeasurableSpace Ω]
    (P : Finset β) (μ : β → FiniteMeasure Ω) (s : Set Ω) :
    (∑ p ∈ P, μ p) s = ∑ p ∈ P, μ p s := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih => simp only [sum_insert hp, FiniteMeasure.coeFn_add, Pi.add_apply, ih]

noncomputable def finiteAtomicMeasure (P : Finset ℕ) (w : ℕ → ℝ≥0) (f : ℕ → ℝ) : FiniteMeasure ℝ :=
  ∑ p ∈ P, w p • finitePointMeasure (f p)

noncomputable def atomicTupleMeasure (P : Finset ℕ) (w : ℕ → ℝ≥0) (f : ℕ → ℝ) (h : ℕ) :
    FiniteMeasure (Fin h → ℝ) :=
  ∑ v ∈ Fintype.piFinset (fun _ : Fin h => P),
    (∏ i, w (v i)) • finitePointMeasure (fun i => f (v i))

open Classical in
theorem finiteAtomicMeasure_apply (P : Finset ℕ) (w : ℕ → ℝ≥0) (f : ℕ → ℝ) (s : Set ℝ) :
    finiteAtomicMeasure P w f s = ∑ p ∈ P, if f p ∈ s then w p else 0 := by
  rw [finiteAtomicMeasure, finiteMeasure_sum_apply]
  apply sum_congr rfl
  intro p hp
  rw [FiniteMeasure.smul_apply, smul_eq_mul, finitePointMeasure_apply]
  split_ifs <;> simp

open Classical in
theorem atomicTupleMeasure_apply (P : Finset ℕ) (w : ℕ → ℝ≥0) (f : ℕ → ℝ)
    (h : ℕ) (s : Set (Fin h → ℝ)) :
    atomicTupleMeasure P w f h s = ∑ v ∈ Fintype.piFinset (fun _ : Fin h => P),
      if (fun i => f (v i)) ∈ s then ∏ i, w (v i) else 0 := by
  rw [atomicTupleMeasure, finiteMeasure_sum_apply]
  apply sum_congr rfl
  intro v hv
  rw [FiniteMeasure.smul_apply, smul_eq_mul, finitePointMeasure_apply]
  split_ifs <;> simp

theorem finiteAtomicMeasure_pi (P : Finset ℕ) (w : ℕ → ℝ≥0) (f : ℕ → ℝ) (h : ℕ) :
    FiniteMeasure.pi (fun _ : Fin h => finiteAtomicMeasure P w f) = atomicTupleMeasure P w f h := by
  classical
  apply FiniteMeasure.toMeasure_injective
  apply Measure.pi_eq
  intro s hs
  have he : atomicTupleMeasure P w f h (Set.pi Set.univ s) =
      ∏ i, finiteAtomicMeasure P w f (s i) := by
    rw [atomicTupleMeasure_apply]
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
    calc
      _ = ∑ v ∈ Fintype.piFinset (fun _ : Fin h => P),
          ∏ i, if f (v i) ∈ s i then w (v i) else 0 := by
        apply sum_congr rfl
        intro v hv
        rw [Fintype.prod_ite_zero]
        split_ifs <;> rfl
      _ = ∏ i : Fin h, ∑ p ∈ P, if f p ∈ s i then w p else 0 :=
        by
          symm
          rw [prod_univ_sum]
      _ = _ := by simp only [finiteAtomicMeasure_apply]
  simp only [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact_mod_cast he

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Amplification.ChebyshevDischarge

namespace OAI

namespace JointDickman
open Finset Filter
open scoped Topology

theorem primeCounting_le_self (N : ℕ) : Nat.primeCounting N ≤ N := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  calc
    _ ≤ (Icc 1 N).card := card_le_card (fun p hp =>
      mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.one_le,(Nat.mem_primesLE.mp hp).1⟩)
    _ = N := by simp

theorem chebyshevPrimeCountingInput : PublishedInputs.ChebyshevPrimeCountingInput := by
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  let C : ℝ := max (Real.log 4+1) (Real.log (max 2 x₀))
  have hC : 0 ≤ C := (by positivity : (0 : ℝ) ≤ Real.log 4+1).trans (le_max_left _ _)
  refine ⟨C,hC,fun x hx => ?_⟩
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  by_cases hxx : x₀ ≤ x
  · exact (hx₀ x hxx).trans (by
      apply div_le_div_of_nonneg_right _ hlog.le
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  · have hpn : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast primeCounting_le_self ⌊x⌋₊
    have hp : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x :=
      hpn.trans (Nat.floor_le (by linarith))
    have hlC : Real.log x ≤ C :=
      (Real.log_le_log (by linarith) ((le_of_not_ge hxx).trans (le_max_right _ _))).trans
        (le_max_right _ _)
    apply (le_div_iff₀ hlog).mpr
    calc
      _ ≤ x * Real.log x := mul_le_mul_of_nonneg_right hp hlog.le
      _ ≤ x * C := mul_le_mul_of_nonneg_left hlC (by linarith)
      _ = _ := mul_comm _ _

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Amplification.FloorErrors

namespace OAI

namespace JointDickman

open Filter
open scoped Topology

theorem normalized_division_error {N d : ℕ} (hN : 0 < N) (hd : 0 < d) :
    |((N / d : ℕ) : ℝ) / N - 1 / (d : ℝ)| ≤ 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hmod : ((N % d : ℕ) : ℝ) + (d : ℝ) * (N / d : ℕ) = N := by
    exact_mod_cast Nat.mod_add_div N d
  have hsmall : ((N % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt N hd).le
  have heq : ((N / d : ℕ) : ℝ) / N - 1 / (d : ℝ) =
      -((N % d : ℕ) : ℝ) / ((N : ℝ) * d) := by
    field_simp
    nlinarith
  rw [heq, abs_div, abs_neg, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_pos (mul_pos hN' hd')]
  apply (div_le_div_iff₀ (mul_pos hN' hd') hN').mpr
  nlinarith

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.DivisorProductMean

namespace OAI

namespace JointDickman

open Finset

theorem primeProduct_dvd_iff (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (n : ℕ) :
    (∏ p ∈ D, p) ∣ n ↔ ∀ p ∈ D, p ∣ n := by
  refine ⟨fun h p hp => (dvd_prod_of_mem id hp).trans h, ?_⟩
  intro h
  by_cases hn : n = 0
  · simp [hn]
  have hsub : D ⊆ n.primeFactors := fun p hp => (hD p hp).mem_primeFactors (h p hp) hn
  exact (prod_dvd_prod_of_subset _ _ id hsub).trans (Nat.prod_primeFactors_dvd n)

open Classical in
theorem divisor_product_expansion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b : ℕ → ℝ) (n : ℕ) :
    (∏ p ∈ P, if p ∣ n then 1 + b p else 1) =
      ∑ D ∈ P.powerset, if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, b p else 0 := by
  have heq (p : ℕ) : (if p ∣ n then 1 + b p else 1) =
      1 + (if p ∣ n then b p else 0) := by split_ifs <;> simp
  simp_rw [heq]
  rw [prod_one_add]
  apply sum_congr rfl
  intro D hD
  rw [prod_ite_zero]
  simp only [primeProduct_dvd_iff D (fun p hp => hP p (mem_powerset.mp hD hp))]

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.PrimeGeneratingMean

namespace OAI

namespace JointDickman
open Finset

noncomputable def primeGeneratingAverage (P : Finset ℕ) (z : ℕ → ℝ) (N : ℕ) : ℝ := by
  classical
  exact (∑ n ∈ Ioc 0 N, ∏ p ∈ P, if p ∣ n then z p else 1)/(N : ℝ)

noncomputable def boundedPrimeSubsets (P : Finset ℕ) (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ N)

noncomputable def primeGeneratingModel (P : Finset ℕ) (z : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ D ∈ boundedPrimeSubsets P N, (∏ p ∈ D, (z p-1))/(∏ p ∈ D, p : ℕ)

theorem primeGeneratingAverage_floor (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ → ℝ) (N : ℕ) :
    primeGeneratingAverage P z N = ∑ D ∈ P.powerset,
      (∏ p ∈ D, (z p-1))*((N/(∏ p ∈ D, p) : ℕ) : ℝ)/(N : ℝ) := by
  classical
  have heq (n : ℕ) : (∏ p ∈ P, if p ∣ n then z p else 1) =
      ∑ D ∈ P.powerset, if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, (z p-1) else 0 := by
    convert divisor_product_expansion P hP (fun p => z p-1) n using 1
    simp
  simp only [primeGeneratingAverage,heq]
  rw [sum_comm,sum_div]
  apply sum_congr rfl
  intro D _
  rw [← sum_filter,sum_const,nsmul_eq_mul,Nat.Ioc_filter_dvd_card_eq_div]
  ring

theorem primeGeneratingAverage_truncated (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ → ℝ) (N : ℕ) :
    primeGeneratingAverage P z N = ∑ D ∈ boundedPrimeSubsets P N,
      (∏ p ∈ D, (z p-1))*((N/(∏ p ∈ D, p) : ℕ) : ℝ)/(N : ℝ) := by
  classical
  rw [primeGeneratingAverage_floor P hP]
  symm
  apply sum_subset (filter_subset _ _)
  intro D hD hnot
  have hbig : N < ∏ p ∈ D, p := by simpa only [boundedPrimeSubsets,mem_filter,hD,true_and,not_le] using hnot
  simp only [Nat.div_eq_of_lt hbig,Nat.cast_zero,mul_zero,zero_div]

theorem primeGeneratingModel_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ → ℝ) {N : ℕ} (hN : 0 < N) {C : ℝ} (hC : 0 ≤ C)
    (hcoef : ∀ D ∈ boundedPrimeSubsets P N, |∏ p ∈ D, (z p-1)| ≤ C) :
    |primeGeneratingAverage P z N - primeGeneratingModel P z N| ≤
      C * ((boundedPrimeSubsets P N).card : ℝ)/(N : ℝ) := by
  classical
  rw [primeGeneratingAverage_truncated P hP,primeGeneratingModel,← sum_sub_distrib]
  calc
    _ ≤ ∑ D ∈ boundedPrimeSubsets P N,
        |(∏ p ∈ D, (z p-1))*((N/(∏ p ∈ D, p) : ℕ) : ℝ)/(N : ℝ) -
          (∏ p ∈ D, (z p-1))/(∏ p ∈ D, p : ℕ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _D ∈ boundedPrimeSubsets P N, C/(N : ℝ) := by
      apply sum_le_sum
      intro D hD
      have hDP : D ⊆ P := mem_powerset.mp (mem_filter.mp hD).1
      have hd : 0 < ∏ p ∈ D, p := prod_pos (fun p hp => (hP p (hDP hp)).pos)
      have he := normalized_division_error hN hd
      calc
        _ = |∏ p ∈ D, (z p-1)| *
            |((N/(∏ p ∈ D, p) : ℕ) : ℝ)/(N : ℝ) - 1/(∏ p ∈ D, p : ℕ)| := by
          rw [← abs_mul]
          congr 1
          ring
        _ ≤ C*(1/(N : ℝ)) := mul_le_mul (hcoef D hD) he (abs_nonneg _) hC
        _ = C/(N : ℝ) := by ring
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.PrimeSubsetCount

namespace OAI

namespace JointDickman
open Finset

theorem boundedPrimeSubsets_fixed_card_le (P : Finset ℕ) (N h : ℕ) :
    ((boundedPrimeSubsets P N).filter (fun D => D.card = h)).card ≤
      primeTupleCount P h (N : ℝ) := by
  classical
  let S := (boundedPrimeSubsets P N).filter (fun D => D.card = h)
  let T := (Fintype.piFinset (fun _ : Fin h => P)).filter
    (fun f => (∏ i, (f i : ℝ)) ≤ N)
  let f : Finset ℕ → (Fin h → ℕ) := fun D =>
    if hD : D.card = h then D.orderEmbOfFin hD else fun _ => 0
  have hs (D : Finset ℕ) (hD : D ∈ S) : D ⊆ P ∧ (∏ p ∈ D, p) ≤ N ∧ D.card = h := by
    obtain ⟨hDP,hcard⟩ := mem_filter.mp hD
    obtain ⟨hDP,hprod⟩ := mem_filter.mp hDP
    exact ⟨mem_powerset.mp hDP,hprod,hcard⟩
  have hmap : Set.MapsTo f S T := by
    intro D hD
    obtain ⟨hDP,hprod,hcard⟩ := hs D hD
    simp only [f,dif_pos hcard]
    apply mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i => hDP (D.orderEmbOfFin_mem hcard i)),?_⟩
    have he : (∏ i : Fin h, D.orderEmbOfFin hcard i) = ∏ p ∈ D, p := by
      simpa only [prod_map,RelEmbedding.coe_toEmbedding] using congrArg (fun E : Finset ℕ => ∏ p ∈ E, p)
        (D.map_orderEmbOfFin_univ hcard)
    have her : (∏ i : Fin h, (D.orderEmbOfFin hcard i : ℝ)) = ((∏ p ∈ D, p : ℕ) : ℝ) := by
      exact_mod_cast he
    rw [her]
    exact_mod_cast hprod
  have hinj : (S : Set (Finset ℕ)).InjOn f := by
    intro D hD E hE hDE
    have hd := (hs D hD).2.2
    have he := (hs E hE).2.2
    have hiD : univ.image (f D) = D := by
      simpa only [f,dif_pos hd] using D.image_orderEmbOfFin_univ hd
    have hiE : univ.image (f E) = E := by
      simpa only [f,dif_pos he] using E.image_orderEmbOfFin_univ he
    rw [← hiD,← hiE,hDE]
  exact card_le_card_of_injOn f hmap hinj

theorem boundedPrimeSubsets_card_le (P : Finset ℕ) (N J : ℕ)
    (hcard : ∀ D ∈ boundedPrimeSubsets P N, D.card ≤ J) :
    (boundedPrimeSubsets P N).card ≤ ∑ h ∈ range (J+1), primeTupleCount P h (N : ℝ) := by
  classical
  rw [card_eq_sum_card_fiberwise (f := Finset.card)
    (t := range (J+1)) (fun D hD => mem_range.mpr (by have := hcard D hD; omega))]
  exact sum_le_sum (fun h _ => boundedPrimeSubsets_fixed_card_le P N h)

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.OrderedPrimeSubsets

namespace OAI

namespace JointDickman
open Finset

noncomputable def orderedPrimeTuples (P : Finset ℕ) (h : ℕ) : Finset (Fin h → ℕ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin h => P)).filter StrictMono

theorem orderedPrimeTuples_mem {P : Finset ℕ} {h : ℕ} {v : Fin h → ℕ} :
    v ∈ orderedPrimeTuples P h ↔ (∀ i, v i ∈ P) ∧ StrictMono v := by
  classical
  simp only [orderedPrimeTuples, mem_filter, Fintype.mem_piFinset]

theorem sum_powersetCard_eq_ordered_tuples (P : Finset ℕ) (h : ℕ)
    (f : Finset ℕ → ℝ) :
    (∑ D ∈ P.powersetCard h, f D) =
      ∑ v ∈ orderedPrimeTuples P h, f (univ.image v) := by
  classical
  symm
  apply sum_bij (fun v _ => univ.image v)
  · intro v hv
    obtain ⟨hvP,hvmono⟩ := orderedPrimeTuples_mem.mp hv
    apply mem_powersetCard.mpr
    constructor
    · intro p hp
      obtain ⟨i,_,rfl⟩ := mem_image.mp hp
      exact hvP i
    · rw [card_image_of_injective _ hvmono.injective, card_univ, Fintype.card_fin]
  · intro v hv w hw he
    have hvmono := (orderedPrimeTuples_mem.mp hv).2
    have hwmono := (orderedPrimeTuples_mem.mp hw).2
    have hcard : (univ.image v).card = h := by
      rw [card_image_of_injective _ hvmono.injective, card_univ, Fintype.card_fin]
    have hvord := orderEmbOfFin_unique hcard (fun i => mem_image.mpr ⟨i,mem_univ _,rfl⟩) hvmono
    have hword := orderEmbOfFin_unique hcard
      (fun i => by rw [he]; exact mem_image.mpr ⟨i,mem_univ _,rfl⟩) hwmono
    exact hvord.trans hword.symm
  · intro D hD
    obtain ⟨hDP,hcard⟩ := mem_powersetCard.mp hD
    refine ⟨D.orderEmbOfFin hcard, ?_, ?_⟩
    · exact orderedPrimeTuples_mem.mpr
        ⟨fun i => hDP (D.orderEmbOfFin_mem hcard i), (D.orderEmbOfFin hcard).strictMono⟩
    · exact D.image_orderEmbOfFin_univ hcard
  · intros; rfl

theorem ordered_tuple_prod {h : ℕ} {v : Fin h → ℕ} (hv : StrictMono v)
    (f : ℕ → ℝ) : (∏ p ∈ univ.image v, f p) = ∏ i, f (v i) :=
  prod_image hv.injective.injOn

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Amplification.GeneratingDegreeExpansion

namespace OAI

namespace JointDickman
open Finset

noncomputable def primeGeneratingDegree (P : Finset ℕ) (z : ℕ → ℝ) (N h : ℕ) : ℝ := by
  classical
  exact ∑ D ∈ P.powersetCard h,
    if (∏ p ∈ D, p) ≤ N then (∏ p ∈ D, (z p-1))/(∏ p ∈ D, p : ℕ) else 0

theorem primeGeneratingModel_sum_degree (P : Finset ℕ) (z : ℕ → ℝ) (N J : ℕ)
    (hcard : ∀ D ∈ boundedPrimeSubsets P N, D.card ≤ J) :
    primeGeneratingModel P z N = ∑ h ∈ range (J+1), primeGeneratingDegree P z N h := by
  classical
  have hf := sum_fiberwise_of_maps_to (g := Finset.card) (s := boundedPrimeSubsets P N)
    (t := range (J+1)) (fun D hD => mem_range.mpr (Nat.lt_succ_of_le (hcard D hD)))
    (fun D => (∏ p ∈ D, (z p-1))/(∏ p ∈ D, p : ℕ))
  rw [primeGeneratingModel, ← hf]
  apply sum_congr rfl
  intro h hh
  have he : (boundedPrimeSubsets P N).filter (fun D => D.card = h) =
      (P.powersetCard h).filter (fun D => (∏ p ∈ D, p) ≤ N) := by
    ext D
    simp only [boundedPrimeSubsets, mem_filter, mem_powersetCard, mem_powerset]
    tauto
  rw [he, sum_filter]
  rfl

open Classical in
theorem primeGeneratingDegree_ordered (P : Finset ℕ) (z : ℕ → ℝ) (N h : ℕ) :
    primeGeneratingDegree P z N h = ∑ v ∈ orderedPrimeTuples P h,
      if (∏ i, v i) ≤ N then (∏ i, (z (v i)-1))/(∏ i, v i : ℕ) else 0 := by
  classical
  rw [primeGeneratingDegree, sum_powersetCard_eq_ordered_tuples]
  apply sum_congr rfl
  intro v hv
  have hm := (orderedPrimeTuples_mem.mp hv).2
  have hp : (∏ p ∈ univ.image v, p : ℕ) = ∏ i, v i := prod_image hm.injective.injOn
  rw [hp, ordered_tuple_prod hm]

@[simp] theorem primeGeneratingDegree_zero (P : Finset ℕ) (z : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    primeGeneratingDegree P z N 0 = 1 := by
  classical
  simp [primeGeneratingDegree, hN.ne']

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Amplification.MarginalTupleDischarge

namespace OAI

namespace JointDickman
open Finset Filter
open scoped Topology

theorem largePrimeTupleCount_tendsto_zero (h : ℕ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun N : ℝ =>
      (primeTupleCount (largePrimeSet N (N^c)) (h+1) N : ℝ)/N)
      atTop (𝓝 0) :=
  largePrimeTupleCount_tendsto_of_published primeReciprocalMertensInput
    chebyshevPrimeCountingInput h hc hc1

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.BoundedPrimeSubsets

namespace OAI

namespace JointDickman
open Finset Filter
open scoped Topology

theorem generating_coefficient_le_one (z : ℕ → ℝ) (hz : ∀ p, 0 ≤ z p ∧ z p ≤ 1)
    (D : Finset ℕ) : |∏ p ∈ D, (z p-1)| ≤ 1 := by
  rw [abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun p _ => by
    rw [abs_le]
    constructor <;> linarith [(hz p).1,(hz p).2])

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Amplification.GeneratingFloorLimit

namespace OAI

namespace JointDickman
open Finset Filter
open scoped Topology

theorem primeTupleCount_zero_le_one (P : Finset ℕ) (N : ℝ) :
    primeTupleCount P 0 N ≤ 1 := by
  classical
  exact (card_filter_le _ _).trans_eq (by simp)

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Amplification.MovingMonotoneLimit

namespace OAI

namespace JointDickman
open Filter
open scoped Topology

theorem moving_monotone_tendsto {ι : Type*} {L : Filter ι}
    {F : ι → ℝ → ℝ} {G : ℝ → ℝ} {v : ι → ℝ} {u : ℝ}
    (hF : ∀ x, Monotone (F x)) (hlim : ∀ t, Tendsto (fun x => F x t) L (𝓝 (G t)))
    (hG : ContinuousAt G u) (hv : Tendsto v L (𝓝 u)) :
    Tendsto (fun x => F x (v x)) L (𝓝 (G u)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hg : ∀ᶠ t in 𝓝[<] u, a < G t :=
      nhdsWithin_le_nhds (hG.tendsto.eventually (eventually_gt_nhds ha))
    obtain ⟨t,htg,htu⟩ := (hg.and self_mem_nhdsWithin).exists
    filter_upwards [(hlim t).eventually (eventually_gt_nhds htg),
      hv.eventually (eventually_gt_nhds htu)] with x hxa hxt
    exact hxa.trans_le (hF x hxt.le)
  · intro b hb
    have hg : ∀ᶠ t in 𝓝[>] u, G t < b :=
      nhdsWithin_le_nhds (hG.tendsto.eventually (eventually_lt_nhds hb))
    obtain ⟨t,htg,hut⟩ := (hg.and self_mem_nhdsWithin).exists
    filter_upwards [(hlim t).eventually (eventually_lt_nhds htg),
      hv.eventually (eventually_lt_nhds hut)] with x hxb hxt
    exact (hF x hxt.le).trans_lt hxb

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductBoundary

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

instance logarithmicPrimeMeasure_nullSingletons (c : ℝ) :
    NullSingletonClass (logarithmicPrimeMeasure c : Measure ℝ) := by
  constructor
  intro t
  change (Measure.map Real.exp (volume.restrict (Set.Ioc (Real.log c) 0))) {t} = 0
  rw [Measure.map_apply Real.measurable_exp (measurableSet_singleton t),
    Measure.restrict_apply (Real.measurable_exp (measurableSet_singleton t))]
  apply measure_mono_null (t := {Real.log t}) _ (measure_singleton _)
  rintro y ⟨hy,_⟩
  have he : Real.exp y = t := hy
  simpa only [Real.log_exp, Set.mem_singleton_iff] using (congrArg Real.log he)

theorem pi_sum_level_null (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) (a : ℝ) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) {t | ∑ i, t i = a} = 0 := by
  let E : Set (ℝ × (Fin n → ℝ)) := {t | t.1 + ∑ i, t.2 i = a}
  have hE : MeasurableSet E := by
    apply isClosed_eq _ continuous_const |>.measurableSet
    exact continuous_fst.add (continuous_finsetSum _ (fun i _ => (continuous_apply i).comp continuous_snd))
  have he : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0) ⁻¹' E =
      {t | ∑ i, t i = a} := by
    ext t
    change t 0 + ∑ i : Fin n, t ((0 : Fin (n+1)).succAbove i) = a ↔ ∑ i, t i = a
    rw [Fin.sum_univ_succAbove t 0]
  rw [← he, (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).measure_preimage hE.nullMeasurableSet,
    Measure.prod_apply_symm hE]
  have hf : ∀ t : Fin n → ℝ, (fun x : ℝ => (x,t)) ⁻¹' E = {a - ∑ i, t i} := by
    intro t
    ext x
    change x + ∑ i, t i = a ↔ x = a - ∑ i, t i
    constructor <;> intro h <;> linarith
  simp only [hf, measure_singleton, lintegral_zero]

theorem pi_sum_sublevel_null_frontier (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) (a : ℝ) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) (frontier {t | ∑ i, t i ≤ a}) = 0 := by
  have hcont : Continuous (fun t : Fin (n+1) → ℝ => ∑ i, t i) :=
    continuous_finsetSum _ (fun i _ => continuous_apply i)
  apply measure_mono_null (t := {t | ∑ i, t i = a}) _ (pi_sum_level_null μ n a)
  intro t ht
  have hh := hcont.frontier_preimage_subset (Set.Iic a) ht
  change ∑ i, t i = a
  simpa only [frontier_Iic, Set.mem_preimage, Set.mem_singleton_iff] using hh

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.PrimeBoxBoundary

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem null_frontier_finset_inter {Ω ι : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i ∈ s, μ (frontier (E i)) = 0) :
    μ (frontier (⋂ i ∈ s, E i)) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [mem_insert, forall_eq_or_imp] at hE
    rw [show (⋂ j ∈ insert i s, E j) = E i ∩ ⋂ j ∈ s, E j by ext x; simp]
    exact null_frontier_inter hE.1 (ih hE.2)

theorem pi_box_null_frontier (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (h : ℕ) (a b : Fin h → ℝ) :
    (Measure.pi (fun _ : Fin h => μ))
      (frontier (Set.pi Set.univ (fun i => Set.Ioc (a i) (b i)))) = 0 := by
  have hsingle (i : Fin h) : μ (frontier (Set.Ioc (a i) (b i))) = 0 := by
    by_cases hab : a i < b i
    · rw [frontier_Ioc hab]
      exact Set.Countable.measure_zero (Set.Finite.countable (Set.toFinite ({a i, b i} : Set ℝ))) μ
    · rw [Set.Ioc_eq_empty_of_le (le_of_not_gt hab)]
      simp
  have hi (i : Fin h) : (Measure.pi (fun _ : Fin h => μ))
      (frontier ((fun t : Fin h → ℝ => t i) ⁻¹' Set.Ioc (a i) (b i))) = 0 := by
    apply measure_mono_null ((continuous_apply i).frontier_preimage_subset _) _
    exact Measure.pi_eval_preimage_null _ (hsingle i)
  have he : Set.pi Set.univ (fun i => Set.Ioc (a i) (b i)) =
      ⋂ i ∈ (univ : Finset (Fin h)), (fun t : Fin h → ℝ => t i) ⁻¹' Set.Ioc (a i) (b i) := by
    ext t
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_iInter, mem_univ,
      Set.mem_preimage]
  rw [he]
  exact null_frontier_finset_inter _ _ _ (fun i _ => hi i)

noncomputable def primeBoxCutoff (h : ℕ) (a b : Fin h → ℝ) (u : ℝ) : Set (Fin h → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ioc (a i) (b i)) ∩ {t | ∑ i, t i ≤ u}

theorem primeBoxCutoff_null_frontier (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) (a b : Fin (n+1) → ℝ) (u : ℝ) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) (frontier (primeBoxCutoff (n+1) a b u)) = 0 :=
  null_frontier_inter (pi_box_null_frontier μ (n+1) a b) (pi_sum_sublevel_null_frontier μ n u)

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Amplification.SublevelContinuity

namespace OAI

namespace JointDickman
open Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem sublevel_measure_continuousAt {Ω : Type*} [MeasurableSpace Ω]
    (μ : FiniteMeasure Ω) {R : Set Ω} (hR : MeasurableSet R)
    {f : Ω → ℝ} (hf : Measurable f) {u : ℝ}
    (hu : (μ : Measure Ω) {t | f t = u} = 0) :
    ContinuousAt (fun v : ℝ => (μ (R ∩ {t | f t ≤ v}) : ℝ)) u := by
  classical
  let g (v : ℝ) : Ω → ℝ := (R ∩ {t | f t ≤ v}).indicator 1
  have hgmeas (v : ℝ) : AEStronglyMeasurable (g v) (μ : Measure Ω) :=
    (measurable_const.indicator (hR.inter (hf measurableSet_Iic))).aestronglyMeasurable
  have hbound (v : ℝ) (t : Ω) : ‖g v t‖ ≤ 1 := by
    simp only [g, Set.indicator_apply, Pi.one_apply]
    split_ifs <;> norm_num
  have hne : ∀ᵐ t ∂(μ : Measure Ω), f t ≠ u := by
    rw [ae_iff]
    simpa only [not_not] using hu
  have hlim : ∀ᵐ t ∂(μ : Measure Ω), Tendsto (fun v => g v t) (𝓝 u) (𝓝 (g u t)) := by
    filter_upwards [hne] with t ht
    by_cases htR : t ∈ R
    · rcases lt_or_gt_of_ne ht with htu | hut
      · have he : (fun _ : ℝ => (1 : ℝ)) =ᶠ[𝓝 u] (fun v => g v t) := by
          filter_upwards [eventually_gt_nhds htu] with v hv
          simp [g, htR, hv.le]
        simpa [g, htR, htu.le] using tendsto_const_nhds.congr' he
      · have he : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 u] (fun v => g v t) := by
          filter_upwards [eventually_lt_nhds hut] with v hv
          simp [g, htR, not_le.mpr hv]
        simpa [g, htR, not_le.mpr hut] using tendsto_const_nhds.congr' he
    · simp [g, htR]
  have h := tendsto_integral_filter_of_dominated_convergence (μ := (μ : Measure Ω))
    (fun _ => (1 : ℝ)) (.of_forall hgmeas)
    (.of_forall (fun v => .of_forall (hbound v))) (integrable_const 1) hlim
  have he (v : ℝ) : (∫ t, g v t ∂(μ : Measure Ω)) = (μ (R ∩ {t | f t ≤ v}) : ℝ) := by
    exact integral_indicator_one (hR.inter (hf measurableSet_Iic))
  simpa only [ContinuousAt, he] using h

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Analysis.MellinSieveRemainder

namespace OAI

namespace JointDickman
open Finset
open scoped Classical ComplexConjugate

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.DickmanReciprocalIntegral

namespace OAI

namespace JointDickman
open MeasureTheory Set Erdos970.NumberTheoryLean

 theorem dickman_reciprocal_integral {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Dickman.rho (1/c) = 1 - ∫ s in c..1, Dickman.rho (1/s-1)/s := by
  have hu : 1 ≤ 1/c := (le_div_iff₀ hc).mpr (by simpa using hc1)
  rw [Dickman.rho_integral hu]
  congr 1
  rw [intervalIntegral.integral_of_le hu, intervalIntegral.integral_of_le hc1,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  have he : (fun s : ℝ => s⁻¹) '' Icc c 1 = Icc 1 (1/c) := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs0 : 0 < s := hc.trans_le hs.1
      exact ⟨by simpa only [one_div, inv_one] using (one_div_le_one_div_of_le hs0 hs.2),
        by simpa only [one_div] using one_div_le_one_div_of_le hc hs.1⟩
    · intro ht
      have ht0 : 0 < t := zero_lt_one.trans_le ht.1
      refine ⟨t⁻¹, ⟨?_, ?_⟩, inv_inv t⟩
      · have := one_div_le_one_div_of_le ht0 ht.2
        simpa only [one_div, inv_inv] using this
      · simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one ht.1
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (fun s (hs : s ∈ Icc c 1) => (hasDerivAt_inv (ne_of_gt (hc.trans_le hs.1))).hasDerivWithinAt)
    inv_injective.injOn (fun t => Dickman.rho (t-1)/t)
  rw [he] at hj
  rw [hj]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  have hs0 : 0 < s := hc.trans_le hs.1
  simp only [abs_neg, abs_inv, abs_of_nonneg (sq_nonneg s), smul_eq_mul, one_div]
  field_simp

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.PrimeTupleDiagonals

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem pi_coordinate_diagonal_null (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {n : ℕ} (i j : Fin (n+1)) (hij : i ≠ j) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) {t | t i = t j} = 0 := by
  obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hij.symm
  let E : Set (ℝ × (Fin n → ℝ)) := {t | t.1 = t.2 k}
  have hE : MeasurableSet E := by
    have h1 : Continuous (fun t : ℝ × (Fin n → ℝ) => t.1) := continuous_fst
    have h2 : Continuous (fun t : ℝ × (Fin n → ℝ) => t.2 k) :=
      (continuous_apply k).comp continuous_snd
    exact (isClosed_eq h1 h2).measurableSet
  have he : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i) ⁻¹' E =
      {t | t i = t (i.succAbove k)} := by
    ext t
    rfl
  rw [← he, (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).measure_preimage hE.nullMeasurableSet,
    Measure.prod_apply_symm hE]
  have hf (t : Fin n → ℝ) : (fun x : ℝ => (x,t)) ⁻¹' E = {t k} := rfl
  simp only [hf, measure_singleton, lintegral_zero]

noncomputable def tupleDiagonal (n : ℕ) : Set (Fin n → ℝ) :=
  {t | ¬Function.Injective t}

theorem tupleDiagonal_eq_union (n : ℕ) :
    tupleDiagonal n = ⋃ i : Fin n, ⋃ j : Fin n,
      if i = j then ∅ else {t | t i = t j} := by
  classical
  ext t
  simp only [tupleDiagonal, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro ht
    obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp ht
    exact ⟨i,j,by simp [hne,hij]⟩
  · rintro ⟨i,j,ht⟩
    by_cases hij : i = j
    · simp [hij] at ht
    · simp only [hij, ite_false, Set.mem_ofPred_eq] at ht
      exact fun hinj => hij (hinj ht)

theorem pi_tupleDiagonal_null (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) : (Measure.pi (fun _ : Fin (n+1) => μ)) (tupleDiagonal (n+1)) = 0 := by
  classical
  rw [tupleDiagonal_eq_union]
  apply measure_iUnion_null
  intro i
  apply measure_iUnion_null
  intro j
  split_ifs with hij
  · exact measure_empty
  · exact pi_coordinate_diagonal_null μ i j hij

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.PrimeTupleIntegral

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

open Classical in
theorem primeLogProduct_apply (c x : ℝ) (h : ℕ) (s : Set (Fin h → ℝ)) :
    ((FiniteMeasure.pi (fun _ : Fin h => primeLogMeasure c x)) s : ℝ) =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin h => largePrimeSet x (x^c)),
        if (fun i => Real.log (v i)/Real.log x) ∈ s then
          ∏ i, 1/(v i : ℝ) else 0 := by
  have he : primeLogMeasure c x = finiteAtomicMeasure (largePrimeSet x (x^c))
      (fun p => Real.toNNReal (1/(p : ℝ))) (fun p => Real.log p/Real.log x) := rfl
  simp only [he, finiteAtomicMeasure_pi, atomicTupleMeasure_apply, NNReal.coe_sum]
  apply sum_congr rfl
  intro v hv
  split_ifs <;> simp

theorem logPrimeTuple_sum_le {x : ℝ} (hx : 1 < x) {h : ℕ}
    (v : Fin h → ℕ) (hv : ∀ i, 0 < v i) (u : ℝ) :
    (∑ i, Real.log (v i)/Real.log x) ≤ u ↔ (∏ i, (v i : ℝ)) ≤ x^u := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hp : ∀ i, (0 : ℝ) < v i := fun i => by exact_mod_cast hv i
  have hprod : 0 < ∏ i, (v i : ℝ) := prod_pos (fun i _ => hp i)
  rw [← sum_div, div_le_iff₀ (Real.log_pos hx)]
  rw [← Real.log_prod (fun i _ => (hp i).ne')]
  rw [← Real.log_rpow hx0, Real.log_le_log_iff hprod (Real.rpow_pos_of_pos hx0 u)]

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.MovingPrimeTuple

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem log_scaled_ratio_tendsto {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ => Real.log (A*x)/Real.log x) atTop (𝓝 1) := by
  have ht := (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop :
    Tendsto (fun x : ℝ => Real.log A/Real.log x) atTop (𝓝 0)).const_add 1
  apply (show Tendsto (fun x : ℝ => 1+Real.log A/Real.log x) atTop (𝓝 1) by simpa using ht).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Real.log_mul hA.ne' (zero_lt_one.trans hx).ne']
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp
  ring

theorem rpow_log_ratio {x y : ℝ} (hx : 1 < x) (hy : 0 < y) :
    x^(Real.log y/Real.log x) = y := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx)]
  have he : Real.log x*(Real.log y/Real.log x) = Real.log y := by
    field_simp [(Real.log_pos hx).ne']
  rw [he, Real.exp_log hy]

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.OrderedPrimeBoundary

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem strictMono_isOpen (n : ℕ) : IsOpen {t : Fin n → ℝ | StrictMono t} := by
  classical
  have he : {t : Fin n → ℝ | StrictMono t} =
      ⋂ i : Fin n, ⋂ j : Fin n, if i < j then {t | t i < t j} else Set.univ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro ht i j
      split_ifs with hij
      · exact ht hij
      · exact Set.mem_univ _
    · intro ht i j hij
      simpa only [hij, ite_true, Set.mem_ofPred_eq] using ht i j
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  split_ifs
  · exact isOpen_lt (continuous_apply i) (continuous_apply j)
  · exact isOpen_univ

theorem strictMono_frontier_subset (n : ℕ) :
    frontier {t : Fin n → ℝ | StrictMono t} ⊆ tupleDiagonal n := by
  have hcl : closure {t : Fin n → ℝ | StrictMono t} ⊆ {t | Monotone t} :=
    closure_minimal (fun _ ht => ht.monotone) isClosed_monotone
  intro t ht hinj
  have hm : Monotone t := hcl (frontier_subset_closure ht)
  have hs := hm.strictMono_of_injective hinj
  have hnot : t ∉ interior {t : Fin n → ℝ | StrictMono t} := ht.2
  exact hnot (by rw [(strictMono_isOpen n).interior_eq]; exact hs)

theorem orderedPrimeRegion_null_frontier (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) : (Measure.pi (fun _ : Fin (n+1) => μ))
      (frontier {t | StrictMono t}) = 0 :=
  measure_mono_null (strictMono_frontier_subset (n+1)) (pi_tupleDiagonal_null μ n)

noncomputable def orderedPrimeBox (h : ℕ) (a b : Fin h → ℝ) (u : ℝ) : Set (Fin h → ℝ) :=
  {t | StrictMono t} ∩ primeBoxCutoff h a b u

theorem orderedPrimeBox_null_frontier (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) (a b : Fin (n+1) → ℝ) (u : ℝ) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) (frontier (orderedPrimeBox (n+1) a b u)) = 0 :=
  null_frontier_inter (orderedPrimeRegion_null_frontier μ n)
    (primeBoxCutoff_null_frontier μ n a b u)

theorem orderedPrimeBox_measure_continuous {c : ℝ} (n : ℕ)
    (a b : Fin (n+1) → ℝ) :
    Continuous (fun u : ℝ => ((FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
      (orderedPrimeBox (n+1) a b u) : ℝ)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have he (u : ℝ) : orderedPrimeBox (n+1) a b u =
      ({t | StrictMono t} ∩ Set.pi Set.univ (fun i => Set.Ioc (a i) (b i))) ∩
        {t | ∑ i, t i ≤ u} := by
    exact (Set.inter_assoc _ _ _).symm
  simp only [he]
  apply sublevel_measure_continuousAt _
    ((strictMono_isOpen (n+1)).measurableSet.inter (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)))
    (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
  exact pi_sum_level_null _ n u

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.OrderedSimplex

namespace OAI

namespace JointDickman
open Finset MeasureTheory
open scoped ENNReal

noncomputable def orderedTupleRegion (n : ℕ) (u : ℝ) : Set (Fin n → ℝ) :=
  {t | StrictMono t} ∩ {t | ∑ i, t i ≤ u}

theorem orderedTupleRegion_measurable (n : ℕ) (u : ℝ) :
    MeasurableSet (orderedTupleRegion n u) :=
  (strictMono_isOpen n).measurableSet.inter
    (measurableSet_le (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)) measurable_const)

theorem orderedTupleRegion_cons (n : ℕ) (s u : ℝ) (t : Fin n → ℝ) :
    Fin.cons s t ∈ orderedTupleRegion (n+1) u ↔
      t ∈ orderedTupleRegion n (u-s) ∩ Set.pi Set.univ (fun _ => Set.Ioi s) := by
  simp only [orderedTupleRegion, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Fin.strictMono_cons, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ioi]
  constructor
  · rintro ⟨⟨hmin, hmono⟩, hsum⟩
    exact ⟨⟨hmono, by linarith⟩, hmin⟩
  · rintro ⟨⟨hmono, hsum⟩, hmin⟩
    exact ⟨⟨hmin, hmono⟩, by linarith⟩

noncomputable def orderedSimplexMass (μ : Measure ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (Measure.pi (fun _ : Fin n => μ)).real (orderedTupleRegion n u)

theorem orderedSimplexMass_succ (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (u : ℝ) :
    orderedSimplexMass μ (n+1) u =
      ∫ s, orderedSimplexMass (μ.restrict (Set.Ioi s)) n (u-s) ∂μ := by
  let E : Set (ℝ × (Fin n → ℝ)) :=
    (fun z => Fin.cons z.1 z.2) ⁻¹' orderedTupleRegion (n+1) u
  have hcons : Measurable (fun z : ℝ × (Fin n → ℝ) =>
      (Fin.cons z.1 z.2 : Fin (n+1) → ℝ)) := by
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_fst
    · exact (measurable_pi_apply j).comp measurable_snd
  have hE : MeasurableSet E := (orderedTupleRegion_measurable _ _).preimage hcons
  have he : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0) ⁻¹' E =
      orderedTupleRegion (n+1) u := by
    ext t
    change (Fin.cons (t 0) (fun i : Fin n => t i.succ) : Fin (n+1) → ℝ) ∈ orderedTupleRegion (n+1) u ↔ t ∈ orderedTupleRegion (n+1) u
    have ht : (Fin.cons (t 0) (fun i : Fin n => t i.succ) : Fin (n+1) → ℝ) = t := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [ht]
  unfold orderedSimplexMass
  rw [measureReal_def, ← he,
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).measure_preimage hE.nullMeasurableSet,
    Measure.prod_apply hE]
  rw [← integral_toReal (measurable_measure_prodMk_left hE).aemeasurable]
  · apply integral_congr_ae
    filter_upwards [] with s
    change ((Measure.pi (fun _ : Fin n => μ)) ((fun t => (s,t)) ⁻¹' E)).toReal = _
    have hs : (fun t => (s,t)) ⁻¹' E =
        orderedTupleRegion n (u-s) ∩ Set.pi Set.univ (fun _ => Set.Ioi s) := by
      ext t
      exact orderedTupleRegion_cons n s u t
    rw [hs, ← Measure.restrict_apply (orderedTupleRegion_measurable _ _), Measure.restrict_pi_pi]
    rfl
  · filter_upwards [] with s
    exact measure_lt_top _ _

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicMeasureCalculus

namespace OAI

namespace JointDickman
open MeasureTheory Set

 theorem logarithmicPrimeMeasure_restrict_Ioi {c s : ℝ}
    (hc : 0 < c) (hcs : c ≤ s) :
    (logarithmicPrimeMeasure c : Measure ℝ).restrict (Ioi s) =
      (logarithmicPrimeMeasure s : Measure ℝ) := by
  have hs : 0 < s := hc.trans_le hcs
  change (Measure.map Real.exp (volume.restrict (Ioc (Real.log c) 0))).restrict (Ioi s) =
    Measure.map Real.exp (volume.restrict (Ioc (Real.log s) 0))
  rw [Measure.restrict_map Real.measurable_exp measurableSet_Ioi, Measure.restrict_restrict]
  · congr 2
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_Ioc, ← Real.log_lt_iff_lt_exp hs]
    constructor
    · rintro ⟨hst, hct, ht⟩
      exact ⟨hst, ht⟩
    · rintro ⟨hst, ht⟩
      exact ⟨hst, (Real.log_le_log hc hcs).trans_lt hst, ht⟩
  · exact Real.measurable_exp measurableSet_Ioi

 theorem logarithmicPrimeMeasure_integral {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (f : ℝ → ℝ) :
    (∫ t, f t ∂(logarithmicPrimeMeasure c : Measure ℝ)) = ∫ t in c..1, f t / t := by
  change (∫ t, f t ∂Measure.map Real.exp (volume.restrict (Ioc (Real.log c) 0))) = _
  rw [Real.isOpenEmbedding_exp.measurableEmbedding.integral_map]
  rw [intervalIntegral.integral_of_le hc1]
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun t (_ : t ∈ Ioc (Real.log c) 0) => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn (fun t => f t / t)
  rw [Real.image_exp_Ioc, Real.exp_log hc, Real.exp_zero] at hj
  rw [hj]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [abs_of_pos (Real.exp_pos t), smul_eq_mul]
  field_simp

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicMeasureScaling

namespace OAI

namespace JointDickman
open MeasureTheory Set

 theorem logarithmicPrimeMeasure_restrict_Iic {c u : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) :
    (logarithmicPrimeMeasure c : Measure ℝ).restrict (Iic u) =
      Measure.map Real.exp (volume.restrict (Ioc (Real.log c) (Real.log u))) := by
  change (Measure.map Real.exp (volume.restrict (Ioc (Real.log c) 0))).restrict (Iic u) = _
  rw [Measure.restrict_map Real.measurable_exp measurableSet_Iic, Measure.restrict_restrict]
  · congr 2
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioc, ← Real.le_log_iff_exp_le hu]
    constructor
    · rintro ⟨htu, hct, _⟩
      exact ⟨hct, htu⟩
    · rintro ⟨hct, htu⟩
      exact ⟨htu, hct, htu.trans (Real.log_nonpos hu.le hu1)⟩
  · exact Real.measurable_exp measurableSet_Iic

 theorem logarithmicPrimeMeasure_scale {c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) (hu1 : u ≤ 1) :
    Measure.map (fun t : ℝ => t/u)
      ((logarithmicPrimeMeasure c : Measure ℝ).restrict (Iic u)) =
        (logarithmicPrimeMeasure (c/u) : Measure ℝ) := by
  rw [logarithmicPrimeMeasure_restrict_Iic hu hu1,
    Measure.map_map (by fun_prop : Measurable (fun t : ℝ => t/u)) Real.measurable_exp]
  have hp : (fun t : ℝ => t-Real.log u) ⁻¹' Ioc (Real.log (c/u)) 0 =
      Ioc (Real.log c) (Real.log u) := by
    ext t
    simp only [mem_preimage, mem_Ioc, Real.log_div hc.ne' hu.ne']
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have hm := (measurePreserving_sub_right (volume : Measure ℝ) (Real.log u)).restrict_preimage
    (s := Ioc (Real.log (c/u)) 0) measurableSet_Ioc
  rw [hp] at hm
  change Measure.map (fun t : ℝ => Real.exp t/u) _ =
    Measure.map Real.exp (volume.restrict (Ioc (Real.log (c/u)) 0))
  rw [← hm.map_eq, Measure.map_map Real.measurable_exp (by fun_prop : Measurable (fun t : ℝ => t-Real.log u))]
  congr 1
  funext t
  simp [Real.exp_sub, Real.exp_log hu]

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicSimplexScaling

namespace OAI

namespace JointDickman
open Finset MeasureTheory Filter

 theorem orderedSimplexMass_restrict_upper (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (n : ℕ) (u : ℝ) :
    orderedSimplexMass (μ.restrict (Set.Iic u)) n u = orderedSimplexMass μ n u := by
  unfold orderedSimplexMass
  rw [← Measure.restrict_pi_pi, measureReal_def, measureReal_def,
    Measure.restrict_apply (orderedTupleRegion_measurable _ _)]
  congr 1
  apply measure_congr
  have hp : ∀ᵐ t : Fin n → ℝ ∂Measure.pi (fun _ : Fin n => μ), ∀ i, 0 ≤ t i :=
    eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae (i := i)).eventually hμ)
  filter_upwards [hp] with t ht
  apply propext
  constructor
  · exact And.left
  · intro hr
    refine ⟨hr, ?_⟩
    intro i _
    exact (single_le_sum (fun j _ => ht j) (mem_univ i)).trans hr.2

 theorem orderedTupleRegion_div {u : ℝ} (hu : 0 < u) (n : ℕ) :
    (fun t : Fin n → ℝ => fun i => t i/u) ⁻¹' orderedTupleRegion n 1 =
      orderedTupleRegion n u := by
  ext t
  have hm : StrictMono (fun i => t i/u) ↔ StrictMono t := by
    constructor
    · intro h i j hij
      exact (div_lt_div_iff_of_pos_right hu).mp (h hij)
    · intro h i j hij
      exact (div_lt_div_iff_of_pos_right hu).mpr (h hij)
  simp only [orderedTupleRegion, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
    hm, ← sum_div, div_le_one hu]

 theorem logarithmicSimplexMass_scale {c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) (hu1 : u ≤ 1) (n : ℕ) :
    orderedSimplexMass (logarithmicPrimeMeasure c) n u =
      orderedSimplexMass (logarithmicPrimeMeasure (c/u)) n 1 := by
  have hμ : ∀ᵐ t ∂(logarithmicPrimeMeasure c : Measure ℝ), 0 ≤ t := by
    have hs : ∀ᵐ t ∂(logarithmicPrimeMeasure c : Measure ℝ), t ∈ Set.Ioc c 1 := by
      rw [ae_iff]
      exact (FiniteMeasure.null_iff_toMeasure_null _ _).mp (logarithmicPrimeMeasure_support hc)
    exact hs.mono (fun t ht => (hc.trans ht.1).le)
  rw [← orderedSimplexMass_restrict_upper _ hμ n u]
  have hm : Measure.map (fun t : Fin n → ℝ => fun i => t i/u)
      (Measure.pi (fun _ : Fin n => (logarithmicPrimeMeasure c : Measure ℝ).restrict (Set.Iic u))) =
      Measure.pi (fun _ : Fin n => (logarithmicPrimeMeasure (c/u) : Measure ℝ)) := by
    rw [Measure.pi_map_pi (fun _ => (by fun_prop : Measurable (fun t : ℝ => t/u)).aemeasurable)]
    congr 1
    funext i
    exact logarithmicPrimeMeasure_scale hc hu hu1
  unfold orderedSimplexMass
  rw [measureReal_def, measureReal_def, ← hm,
    Measure.map_apply (by fun_prop) (orderedTupleRegion_measurable _ _), orderedTupleRegion_div hu]

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.OrderedSimplexIntegrable

namespace OAI

namespace JointDickman
open MeasureTheory Filter

 theorem orderedSimplexMass_succ_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (u : ℝ) :
    Integrable (fun s => orderedSimplexMass (μ.restrict (Set.Ioi s)) n (u-s)) μ := by
  let E : Set (ℝ × (Fin n → ℝ)) :=
    (fun z => (Fin.cons z.1 z.2 : Fin (n+1) → ℝ)) ⁻¹' orderedTupleRegion (n+1) u
  have hcons : Measurable (fun z : ℝ × (Fin n → ℝ) =>
      (Fin.cons z.1 z.2 : Fin (n+1) → ℝ)) := by
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_fst
    · exact (measurable_pi_apply j).comp measurable_snd
  have hE : MeasurableSet E := (orderedTupleRegion_measurable _ _).preimage hcons
  have he (s : ℝ) : orderedSimplexMass (μ.restrict (Set.Ioi s)) n (u-s) =
      (Measure.pi (fun _ : Fin n => μ)).real ((fun t => (s,t)) ⁻¹' E) := by
    unfold orderedSimplexMass
    rw [← Measure.restrict_pi_pi, measureReal_def,
      Measure.restrict_apply (orderedTupleRegion_measurable _ _)]
    congr 2
    ext t
    exact (orderedTupleRegion_cons n s u t).symm
  simp_rw [he]
  apply Integrable.of_bound (measurable_measure_prodMk_left hE).ennreal_toReal.aestronglyMeasurable
    ((Measure.pi (fun _ : Fin n => μ)).real Set.univ)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact measureReal_mono (Set.subset_univ _)

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicMeasureIntegrable

namespace OAI

namespace JointDickman
open MeasureTheory Set

 theorem logarithmicPrimeMeasure_integrable_iff {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (f : ℝ → ℝ) :
    Integrable f (logarithmicPrimeMeasure c : Measure ℝ) ↔
      IntervalIntegrable (fun t => f t / t) volume c 1 := by
  change Integrable f (Measure.map Real.exp (volume.restrict (Ioc (Real.log c) 0))) ↔ _
  rw [Real.isOpenEmbedding_exp.measurableEmbedding.integrable_map_iff,
    intervalIntegrable_iff_integrableOn_Ioc_of_le hc1]
  have hj := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc
    (fun t (_ : t ∈ Ioc (Real.log c) 0) => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn (fun t => f t / t)
  rw [Real.image_exp_Ioc, Real.exp_log hc, Real.exp_zero] at hj
  rw [hj]
  unfold IntegrableOn
  have he : (fun x : ℝ => |Real.exp x| • (f (Real.exp x) / Real.exp x)) = f ∘ Real.exp := by
    funext t
    simp only [Function.comp_apply, abs_of_pos (Real.exp_pos t), smul_eq_mul]
    field_simp
  rw [he]

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicSimplexRecurrence

namespace OAI

namespace JointDickman
open MeasureTheory Set

noncomputable def logarithmicSimplex (n : ℕ) (c : ℝ) : ℝ :=
  orderedSimplexMass (logarithmicPrimeMeasure c) n 1

 theorem logarithmicSimplex_slice {c s : ℝ} (hc : 0 < c) (hcs : c ≤ s) (hs : s < 1)
    (n : ℕ) :
    orderedSimplexMass ((logarithmicPrimeMeasure c : Measure ℝ).restrict (Ioi s)) n (1-s) =
      logarithmicSimplex n (s/(1-s)) := by
  rw [logarithmicPrimeMeasure_restrict_Ioi hc hcs]
  exact logarithmicSimplexMass_scale (hc.trans_le hcs) (by linarith) (by linarith [hc.trans_le hcs]) n

 theorem logarithmicSimplex_succ {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (n : ℕ) :
    logarithmicSimplex (n+1) c =
      ∫ s in c..1, logarithmicSimplex n (s/(1-s))/s := by
  rw [logarithmicSimplex, orderedSimplexMass_succ, logarithmicPrimeMeasure_integral hc hc1]
  apply intervalIntegral.integral_congr_Ioo_of_le hc1
  intro s hs
  dsimp only
  rw [logarithmicSimplex_slice hc hs.1.le hs.2]

 theorem logarithmicSimplex_integrable {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (n : ℕ) :
    IntervalIntegrable (fun s => logarithmicSimplex n (s/(1-s))/s) volume c 1 := by
  have hi := (logarithmicPrimeMeasure_integrable_iff hc hc1 _).mp
    (orderedSimplexMass_succ_integrable (logarithmicPrimeMeasure c) n 1)
  apply hi.congr_uIoo
  intro s hs
  rw [uIoo_of_le hc1] at hs
  dsimp only
  rw [logarithmicSimplex_slice hc hs.1.le hs.2]

 theorem logarithmicSimplex_zero (c : ℝ) : logarithmicSimplex 0 c = 1 := by
  have he : orderedTupleRegion 0 1 = Set.univ := by
    ext t
    simp [orderedTupleRegion, StrictMono]
  simp [logarithmicSimplex, orderedSimplexMass, he, measureReal_def]

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicSimplexCutoff

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory

 theorem logarithmicSimplex_eq_zero {c : ℝ} (hc : 0 < c) (n : ℕ)
    (hnc : 1 ≤ ((n+1 : ℕ) : ℝ)*c) : logarithmicSimplex (n+1) c = 0 := by
  have hs : ∀ᵐ t ∂(logarithmicPrimeMeasure c : Measure ℝ), c < t := by
    have hs' : ∀ᵐ t ∂(logarithmicPrimeMeasure c : Measure ℝ), t ∈ Set.Ioc c 1 := by
      rw [ae_iff]
      exact (FiniteMeasure.null_iff_toMeasure_null _ _).mp (logarithmicPrimeMeasure_support hc)
    exact hs'.mono (fun _ ht => ht.1)
  have hp : ∀ᵐ t : Fin (n+1) → ℝ ∂Measure.pi (fun _ : Fin (n+1) =>
      (logarithmicPrimeMeasure c : Measure ℝ)), ∀ i, c < t i :=
    eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae (i := i)).eventually hs)
  have hz : (Measure.pi (fun _ : Fin (n+1) => (logarithmicPrimeMeasure c : Measure ℝ)))
      (orderedTupleRegion (n+1) 1) = 0 := by
    have ha : ∀ᵐ t : Fin (n+1) → ℝ ∂Measure.pi (fun _ : Fin (n+1) =>
        (logarithmicPrimeMeasure c : Measure ℝ)), t ∉ orderedTupleRegion (n+1) 1 := by
      filter_upwards [hp] with t ht hmem
      have hh := sum_lt_sum_of_nonempty (s := (univ : Finset (Fin (n+1))))
        univ_nonempty (fun i _ => ht i)
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
      exact (not_lt_of_ge hnc) (hh.trans_le hmem.2)
    simpa only [not_not, Set.ofPred_mem_eq] using (ae_iff.mp ha)
  simp only [logarithmicSimplex, orderedSimplexMass, measureReal_def, hz, ENNReal.toReal_zero]

noncomputable def logarithmicAvoidance (N : ℕ) (c : ℝ) : ℝ :=
  ∑ n ∈ range (N+1), (-1 : ℝ)^n * logarithmicSimplex n c

 theorem logarithmicAvoidance_zero (c : ℝ) : logarithmicAvoidance 0 c = 1 := by
  simp [logarithmicAvoidance, logarithmicSimplex_zero]

 theorem logarithmicAvoidance_initial {c : ℝ} (hc : 1 ≤ c) (N : ℕ) :
    logarithmicAvoidance N c = 1 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  induction N with
  | zero => exact logarithmicAvoidance_zero c
  | succ N ih =>
    rw [logarithmicAvoidance, sum_range_succ]
    change logarithmicAvoidance N c + _ = 1
    rw [ih, logarithmicSimplex_eq_zero hc0 N, mul_zero, add_zero]
    have hN : (1 : ℝ) ≤ (N+1 : ℕ) := by exact_mod_cast (Nat.succ_pos N)
    exact hc.trans (le_mul_of_one_le_left hc0.le hN)

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicAvoidanceRecurrence

namespace OAI

namespace JointDickman
open Finset MeasureTheory

 theorem logarithmicAvoidance_succ {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (N : ℕ) :
    logarithmicAvoidance (N+1) c =
      1 - ∫ s in c..1, logarithmicAvoidance N (s/(1-s))/s := by
  have hi (n : ℕ) : IntervalIntegrable
      (fun s => (-1 : ℝ)^n * (logarithmicSimplex n (s/(1-s))/s)) volume c 1 :=
    (logarithmicSimplex_integrable hc hc1 n).const_mul _
  have hs : (∫ s in c..1, logarithmicAvoidance N (s/(1-s))/s) =
      ∑ n ∈ range (N+1), (-1 : ℝ)^n * logarithmicSimplex (n+1) c := by
    simp only [logarithmicAvoidance, sum_div]
    simp_rw [mul_div_assoc]
    rw [intervalIntegral.integral_finsetSum (fun n _ => hi n)]
    apply sum_congr rfl
    intro n _
    rw [intervalIntegral.integral_const_mul, ← logarithmicSimplex_succ hc hc1]
  rw [hs, logarithmicAvoidance, sum_range_succ']
  simp only [pow_zero, logarithmicSimplex_zero, one_mul]
  have he : (∑ k ∈ range (N+1), (-1 : ℝ)^(k+1)*logarithmicSimplex (k+1) c) =
      -(∑ k ∈ range (N+1), (-1 : ℝ)^k*logarithmicSimplex (k+1) c) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k _
    rw [pow_succ]
    ring
  rw [he]
  ring

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicAvoidanceDickman

namespace OAI

namespace JointDickman
open MeasureTheory Erdos970.NumberTheoryLean

 theorem logarithmicAvoidance_eq_dickman (N : ℕ) {c : ℝ} (hc : 0 < c)
    (hN : 1/c ≤ (N : ℝ)+1) :
    logarithmicAvoidance N c = Dickman.rho (1/c) := by
  induction N generalizing c with
  | zero =>
    rw [logarithmicAvoidance_zero, Dickman.rho_initial (by simpa using hN)]
  | succ N ih =>
    by_cases hc1 : 1 ≤ c
    · rw [logarithmicAvoidance_initial hc1, Dickman.rho_initial]
      exact (div_le_one hc).mpr hc1
    · have hc1' : c ≤ 1 := (lt_of_not_ge hc1).le
      rw [logarithmicAvoidance_succ hc hc1', dickman_reciprocal_integral hc hc1']
      congr 1
      apply intervalIntegral.integral_congr_Ioo_of_le hc1'
      intro s hs
      dsimp only
      have hs0 : 0 < s := hc.trans hs.1
      have hd : 0 < 1-s := sub_pos.mpr hs.2
      have he : 1/(s/(1-s)) = 1/s-1 := by
        field_simp
      have hb : 1/(s/(1-s)) ≤ (N : ℝ)+1 := by
        rw [he]
        have hinv := one_div_le_one_div_of_le hc hs.1.le
        push_cast at hN
        linarith
      rw [ih (div_pos hs0 hd) hb, he]

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.OrderedPrimeTupleLimit

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem orderedPrimeLogProduct_box_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (n : ℕ) (a b : Fin (n+1) → ℝ) {v : ℝ → ℝ} {u : ℝ}
    (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun x => ((FiniteMeasure.pi (fun _ : Fin (n+1) => primeLogMeasure c x))
      (orderedPrimeBox (n+1) a b (v x)) : ℝ)) atTop
      (𝓝 ((FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
        (orderedPrimeBox (n+1) a b u) : ℝ)) := by
  have hm0 : (logarithmicPrimeMeasure c).mass ≠ 0 := by
    intro h
    have he := congrArg ((↑) : ℝ≥0 → ℝ) h
    rw [logarithmicPrimeMeasure_mass hc hc1.le, NNReal.coe_zero] at he
    linarith [Real.log_neg hc hc1]
  have hne : (FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c)) ≠ 0 := by
    apply (FiniteMeasure.mass_nonzero_iff _).mp
    rw [FiniteMeasure.mass_pi]
    exact prod_ne_zero_iff.mpr (fun _ _ => hm0)
  apply moving_monotone_tendsto
    (F := fun x t => ((FiniteMeasure.pi (fun _ : Fin (n+1) => primeLogMeasure c x))
      (orderedPrimeBox (n+1) a b t) : ℝ)) _ _
    (orderedPrimeBox_measure_continuous (c := c) n a b).continuousAt hv
  · intro x s t hst
    apply NNReal.coe_le_coe.mpr
    apply FiniteMeasure.apply_mono
    rintro y ⟨hym,hyb,hys⟩
    exact ⟨hym,hyb,hys.trans hst⟩
  · intro t
    apply NNReal.tendsto_coe.mpr
    apply finiteMeasure_set_tendsto (primeLogProduct_tendsto hc hc1 (n+1)) hne
    apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
    exact orderedPrimeBox_null_frontier _ n a b t

theorem strictMono_logPrimeTuple_iff {x : ℝ} (hx : 1 < x) {h : ℕ}
    (v : Fin h → ℕ) (hv : ∀ i, 0 < v i) :
    StrictMono (fun i => Real.log (v i)/Real.log x) ↔ StrictMono v := by
  have he (i j : Fin h) : Real.log (v i)/Real.log x < Real.log (v j)/Real.log x ↔ v i < v j := by
    rw [div_lt_div_iff_of_pos_right (Real.log_pos hx),
      Real.log_lt_log_iff (by exact_mod_cast hv i) (by exact_mod_cast hv j)]
    exact_mod_cast (Iff.rfl : v i < v j ↔ v i < v j)
  constructor <;> intro hm i j hij
  · exact (he i j).mp (hm hij)
  · exact (he i j).mpr (hm hij)

open Classical in
theorem orderedPrimeLogProduct_box_apply {c x : ℝ} (hx : 1 < x) (h : ℕ)
    (a b : Fin h → ℝ) (u : ℝ) :
    ((FiniteMeasure.pi (fun _ : Fin h => primeLogMeasure c x)) (orderedPrimeBox h a b u) : ℝ) =
      ∑ v ∈ orderedPrimeTuples (largePrimeSet x (x^c)) h,
        if (∀ i, x^(a i) < v i ∧ (v i : ℝ) ≤ x^(b i)) ∧
            (∏ i, (v i : ℝ)) ≤ x^u then ∏ i, 1/(v i : ℝ) else 0 := by
  rw [primeLogProduct_apply, orderedPrimeTuples, sum_filter]
  apply sum_congr rfl
  intro v hv
  have hp : ∀ i, 0 < v i := by
    intro i
    have hvi := Fintype.mem_piFinset.mp hv i
    exact (Nat.mem_primesLE.mp (mem_filter.mp hvi).1).2.pos
  have hm := strictMono_logPrimeTuple_iff hx v hp
  have hb : (fun i => Real.log (v i)/Real.log x) ∈ primeBoxCutoff h a b u ↔
      (∀ i, x^(a i) < v i ∧ (v i : ℝ) ≤ x^(b i)) ∧
        (∏ i, (v i : ℝ)) ≤ x^u := by
    simp only [primeBoxCutoff, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_ofPred_eq, logPrimeLocation_mem_Ioc hx (hp _),
      logPrimeTuple_sum_le hx v hp u]
  simp only [orderedPrimeBox, Set.mem_inter_iff, Set.mem_ofPred_eq, hm, hb]
  split_ifs <;> simp_all

open Classical in
theorem orderedReciprocalPrimeTuple_scaled_box_tendsto {c A : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (hA : 0 < A) (n : ℕ) (a b : Fin (n+1) → ℝ) :
    Tendsto (fun x : ℝ =>
      ∑ v ∈ orderedPrimeTuples (largePrimeSet x (x^c)) (n+1),
        if (∀ i, x^(a i) < v i ∧ (v i : ℝ) ≤ x^(b i)) ∧
            (∏ i, (v i : ℝ)) ≤ A*x then ∏ i, 1/(v i : ℝ) else 0) atTop
      (𝓝 ((FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
        (orderedPrimeBox (n+1) a b 1) : ℝ)) := by
  apply (orderedPrimeLogProduct_box_tendsto hc hc1 n a b (log_scaled_ratio_tendsto hA)).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [orderedPrimeLogProduct_box_apply hx, rpow_log_ratio hx (mul_pos hA (zero_lt_one.trans hx))]

end JointDickman

end OAI
-- OAI.NumberTheory.JointDickman.Arithmetic.PrimeAvoidanceDegreeLimit

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology

 theorem orderedPrimeBox_full_mass {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ((FiniteMeasure.pi (fun _ : Fin n => logarithmicPrimeMeasure c))
      (orderedPrimeBox n (fun _ => c) (fun _ => 1) 1) : ℝ) = logarithmicSimplex n c := by
  have hs : ∀ᵐ t ∂(logarithmicPrimeMeasure c : Measure ℝ), t ∈ Set.Ioc c 1 := by
    rw [ae_iff]
    exact (FiniteMeasure.null_iff_toMeasure_null _ _).mp (logarithmicPrimeMeasure_support hc)
  have hp : ∀ᵐ t : Fin n → ℝ ∂Measure.pi (fun _ : Fin n =>
      (logarithmicPrimeMeasure c : Measure ℝ)), t ∈ Set.pi Set.univ (fun _ => Set.Ioc c 1) := by
    have ht := eventually_all.mpr (fun i : Fin n => (Measure.tendsto_eval_ae_ae (i := i)).eventually hs)
    exact ht.mono (fun t ht i _ => ht i)
  have he : orderedPrimeBox n (fun _ => c) (fun _ => 1) 1 =
      Set.pi Set.univ (fun _ => Set.Ioc c 1) ∩ orderedTupleRegion n 1 := by
    ext t
    simp only [orderedPrimeBox, primeBoxCutoff, orderedTupleRegion, Set.mem_inter_iff]
    tauto
  change ((Measure.pi (fun _ : Fin n => (logarithmicPrimeMeasure c : Measure ℝ)))
    (orderedPrimeBox n (fun _ => c) (fun _ => 1) 1)).toReal = _
  rw [he, Measure.measure_inter_eq_of_ae hp]
  rfl

 theorem primeAvoidanceDegree_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (n : ℕ) :
    Tendsto (fun x => primeGeneratingDegree (largePrimeSet x (x^c)) (fun _ => 0) ⌊x⌋₊ (n+1))
      atTop (𝓝 ((-1 : ℝ)^(n+1)*logarithmicSimplex (n+1) c)) := by
  have ht := (orderedReciprocalPrimeTuple_scaled_box_tendsto hc hc1 zero_lt_one n
    (fun _ => c) (fun _ => 1)).const_mul ((-1 : ℝ)^(n+1))
  rw [orderedPrimeBox_full_mass hc] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [primeGeneratingDegree_ordered, mul_sum]
  apply sum_congr rfl
  intro v hv
  have hb (i : Fin (n+1)) : x^c < v i ∧ (v i : ℝ) ≤ x := by
    obtain ⟨hp,hlo⟩ := mem_filter.mp ((orderedPrimeTuples_mem.mp hv).1 i)
    obtain ⟨hpx,_⟩ := Nat.mem_primesLE.mp hp
    exact ⟨hlo,(Nat.le_floor_iff (zero_lt_one.trans hx).le).mp hpx⟩
  have hbd : (∏ i, v i) ≤ ⌊x⌋₊ ↔ (∏ i, (v i : ℝ)) ≤ x := by
    rw [Nat.le_floor_iff (zero_lt_one.trans hx).le]
    norm_cast
  have hi : (∀ i, x^c < v i ∧ (v i : ℝ) ≤ x^1) := by simpa using hb
  have hden : (∏ i, 1/(v i : ℝ)) = 1/(∏ i, v i : ℕ) := by
    push_cast
    simp [one_div, prod_inv_distrib]
  simp only [hi, true_and, one_mul, hbd, zero_sub, prod_const, card_univ, Fintype.card_fin]
  split_ifs <;> simp_all [div_eq_mul_inv]

end JointDickman

end OAI

namespace OAI

/-! # Fixed-cutoff smooth counts have the Dickman limit -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem fixedSmooth_iff_avoids {N n : ℕ} {a : ℝ} (hn : n ∈ Icc 1 N) :
    (((n.primeFactors.sup id : ℕ) : ℝ) ≤ (N : ℝ)^a) ↔
      ∀ p ∈ largePrimeSet N ((N : ℝ)^a), ¬p ∣ n := by
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  constructor
  · intro hs p hp hpn
    obtain ⟨hpm, hpc⟩ := mem_filter.mp hp
    have hpp := (Nat.mem_primesLE.mp hpm).2
    have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpn, by omega⟩
    have hle : p ≤ n.primeFactors.sup id := Finset.le_sup (f := id) hmem
    have : (p : ℝ) ≤ ((n.primeFactors.sup id : ℕ) : ℝ) := by exact_mod_cast hle
    linarith
  · intro ha
    by_contra hs
    have hpos : 0 < n.primeFactors.sup id := by
      have h0 : (0 : ℝ) ≤ (N : ℝ)^a := Real.rpow_nonneg (Nat.cast_nonneg N) a
      have : (0 : ℝ) < ((n.primeFactors.sup id : ℕ) : ℝ) := by linarith [not_le.mp hs]
      exact_mod_cast this
    have hne : n.primeFactors.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he] at hpos
      simp at hpos
    obtain ⟨p, hp, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
    obtain ⟨hpp, hpn, _⟩ := Nat.mem_primeFactors.mp hp
    apply ha p _ hpn
    refine mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨?_, hpp⟩, ?_⟩
    · rw [Nat.floor_natCast]
      exact (Nat.le_of_dvd (by omega) hpn).trans hnN
    · rw [hsup] at hs
      simpa using not_le.mp hs

theorem fixedSmooth_count_eq_average (N : ℕ) (a : ℝ) :
    (((Icc 1 N).filter (fun n : ℕ =>
      ((n.primeFactors.sup id : ℕ) : ℝ) ≤ (N : ℝ)^a)).card : ℝ) / N =
      primeGeneratingAverage (largePrimeSet N ((N : ℝ)^a)) (fun _ => 0) N := by
  classical
  have hI : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc, mem_Ioc]; omega
  rw [primeGeneratingAverage, Finset.natCast_card_filter]
  congr 1
  rw [← hI]
  apply sum_congr rfl
  intro n hn
  rw [if_congr (fixedSmooth_iff_avoids hn) rfl rfl]
  by_cases h : ∀ p ∈ largePrimeSet N ((N : ℝ)^a), ¬p ∣ n
  · rw [if_pos h]
    exact (prod_eq_one fun p hp => by simp [h p hp]).symm
  · rw [if_neg h]
    push Not at h
    obtain ⟨p, hp, hpn⟩ := h
    exact (prod_eq_zero hp (by simp [hpn])).symm

theorem fixedSmooth_subset_card {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 2 ≤ N) :
    ∀ D ∈ boundedPrimeSubsets (largePrimeSet N ((N : ℝ)^a)) N, D.card ≤ ⌈1/a⌉₊ := by
  intro D hD
  obtain ⟨hDP, hDN⟩ := mem_filter.mp hD
  have hDP := mem_powerset.mp hDP
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  let q : ℝ := (N : ℝ)^a
  have hq : 1 ≤ q := Real.one_le_rpow hNr.le ha.le
  have hpow : q^D.card ≤ ((∏ p ∈ D, p : ℕ) : ℝ) := by
    rw [← prod_const]
    push_cast
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro p hp
    exact (mem_filter.mp (hDP hp)).2.le
  by_contra hcard
  have hJ : 1/a ≤ (⌈1/a⌉₊ : ℝ) := Nat.le_ceil _
  have hc : ((⌈1/a⌉₊ + 1 : ℕ) : ℝ) ≤ D.card := by exact_mod_cast (show ⌈1/a⌉₊ + 1 ≤ D.card by omega)
  have hgt : 1 < a * D.card := by
    have h1 : 1 ≤ a * ⌈1/a⌉₊ := by
      have := mul_le_mul_of_nonneg_left hJ ha.le
      rwa [mul_one_div_cancel ha.ne'] at this
    push_cast at hc
    nlinarith
  have hqD : q^D.card = (N : ℝ)^(a * D.card) := by
    simp only [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  have hbig : (N : ℝ) < q^D.card := by
    rw [hqD]
    simpa using Real.rpow_lt_rpow_of_exponent_lt hNr hgt
  have hle : ((∏ p ∈ D, p : ℕ) : ℝ) ≤ N := by exact_mod_cast hDN
  linarith

theorem fixedSmooth_count_tendsto {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter (fun n : ℕ =>
      ((n.primeFactors.sup id : ℕ) : ℝ) ≤ (N:ℝ)^a)).card : ℝ) / N)
      atTop (𝓝 (dickmanCDF a)) := by
  classical
  let J := ⌈1/a⌉₊
  let P : ℕ → Finset ℕ := fun N => largePrimeSet N ((N : ℝ)^a)
  have hP (N : ℕ) : ∀ p ∈ P N, p.Prime := fun p hp =>
    (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hdeg (h : ℕ) : Tendsto (fun N : ℕ => primeGeneratingDegree (P N) (fun _ => 0) N h)
      atTop (𝓝 ((-1 : ℝ)^h * logarithmicSimplex h a)) := by
    cases h with
    | zero =>
      simp only [pow_zero, logarithmicSimplex_zero, mul_one]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (primeGeneratingDegree_zero _ _ hN).symm
    | succ n =>
      have ht := (primeAvoidanceDegree_tendsto ha ha1 n).comp hnat
      simpa only [Function.comp_def, Nat.floor_natCast, P] using ht
  have hmodel : Tendsto (fun N : ℕ => primeGeneratingModel (P N) (fun _ => 0) N)
      atTop (𝓝 (dickmanCDF a)) := by
    have ht := tendsto_finsetSum (range (J+1)) (fun h _ => hdeg h)
    have hv : (∑ h ∈ range (J+1), (-1 : ℝ)^h * logarithmicSimplex h a) = dickmanCDF a := by
      change logarithmicAvoidance J a = _
      rw [logarithmicAvoidance_eq_dickman J ha]
      · simp only [dickmanCDF, not_le.mpr ha, ite_false]
      · have : 1/a ≤ (J : ℝ) := Nat.le_ceil _
        linarith
    rw [hv] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact (primeGeneratingModel_sum_degree _ _ _ J (fixedSmooth_subset_card ha hN)).symm
  have htuple (h : ℕ) : Tendsto (fun N : ℕ => (primeTupleCount (P N) h (N : ℝ) : ℝ)/N)
      atTop (𝓝 0) := by
    cases h with
    | zero =>
      apply squeeze_zero (fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (fun N => div_le_div_of_nonneg_right
          (show (primeTupleCount (P N) 0 (N : ℝ) : ℝ) ≤ 1 by
            exact_mod_cast primeTupleCount_zero_le_one (P N) (N : ℝ)) (Nat.cast_nonneg _))
      exact tendsto_const_nhds.div_atTop hnat
    | succ h =>
      simpa only [Function.comp_def, P] using
        (largePrimeTupleCount_tendsto_zero h ha ha1.le).comp hnat
  have herr : Tendsto (fun N : ℕ => ((boundedPrimeSubsets (P N) N).card : ℝ)/N)
      atTop (𝓝 0) := by
    have hlim := tendsto_finsetSum (range (J+1)) (fun h _ => htuple h)
    simp only [sum_const_zero] at hlim
    apply squeeze_zero' (Eventually.of_forall fun _ =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hlim
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [← sum_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast boundedPrimeSubsets_card_le (P N) N J (fixedSmooth_subset_card ha hN)
  have hdiff : Tendsto (fun N : ℕ => primeGeneratingAverage (P N) (fun _ => 0) N -
      primeGeneratingModel (P N) (fun _ => 0) N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ herr
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    simpa only [one_mul] using primeGeneratingModel_error (P N) (hP N) (fun _ => 0) hN
      zero_le_one (fun D _ => generating_coefficient_le_one _ (fun _ => by norm_num) D)
  have hfin := hmodel.add hdiff
  simp only [add_zero, add_sub_cancel] at hfin
  apply hfin.congr'
  exact Eventually.of_forall fun N => (fixedSmooth_count_eq_average N a).symm

end JointDickman

end OAI

-- Moving-threshold sandwich adapted from OpenAI/math@3344da59991ed94f9ba711217b29c1d760badfa6.
namespace Marginal371
open Filter Topology Finset
noncomputable def count (P : ℕ → Prop) (N : ℕ) : ℕ := by
  classical exact ((Icc 1 N).filter P).card
noncomputable def density (P : ℕ → Prop) (N : ℕ) : ℝ := (count P N : ℝ) / N
abbrev Fixed (p : ℕ → ℝ) (F : ℝ → ℝ) := ∀ a : ℝ, 0 < a → a < 1 →
  Tendsto (fun N : ℕ => density (fun n => p n ≤ (N:ℝ)^a) N) atTop (𝓝 (F a))
theorem eventually_power_lower {δ a c : ℝ} (hδ : 0 < δ) (hca : c < a) :
    ∀ᶠ x : ℝ in atTop, x ^ c ≤ (δ * x) ^ a := by
  have ht : Tendsto (fun x : ℝ => x ^ (c - a)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hca)
  filter_upwards [ht.eventually (gt_mem_nhds (Real.rpow_pos_of_pos hδ a)), eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  rw [Real.rpow_sub hxpos] at hx
  rw [Real.mul_rpow hδ.le hxpos.le]
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hxpos a)).mp hx).le

theorem moving {p : ℕ → ℝ} {F : ℝ → ℝ} (hc : Continuous F) (h : Fixed p F)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun N : ℕ => density (fun n => p n ≤ (n:ℝ)^a) N) atTop (𝓝 (F a)) := by
  classical
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have he : ∀ᶠ c in 𝓝[<] a, b < F c ∧ 0 < c :=
      ((hc.continuousAt.tendsto.eventually (lt_mem_nhds hb)).and (eventually_gt_nhds ha)).filter_mono nhdsWithin_le_nhds
    obtain ⟨c, ⟨hbc,hc0⟩, hca⟩ := (he.and self_mem_nhdsWithin).exists
    have hca' : c < a := hca
    let δ := (F c - b)/2
    have hd : 0 < δ := by dsimp [δ]; linarith
    filter_upwards [(tendsto_order.mp (h c hc0 (hca'.trans ha1))).1 (b+δ) (by dsimp [δ]; linarith),
      tendsto_natCast_atTop_atTop.eventually (eventually_power_lower hd hca'), eventually_gt_atTop (0:ℕ)] with N hfix hpow hN
    have hsub : (Icc 1 N).filter (fun n : ℕ => p n ≤ (N:ℝ)^c) ⊆
        (Icc 1 N).filter (fun n : ℕ => p n ≤ (n:ℝ)^a) ∪ Icc 1 ⌊δ*(N:ℝ)⌋₊ := by
      intro n hn
      obtain ⟨hm,hp⟩ := mem_filter.mp hn
      by_cases hs : (n:ℝ) ≤ δ*N
      · exact mem_union_right _ (mem_Icc.mpr ⟨(mem_Icc.mp hm).1,Nat.le_floor hs⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨hm,hp.trans (hpow.trans (Real.rpow_le_rpow
          (mul_nonneg hd.le (Nat.cast_nonneg N)) (le_of_not_ge hs) ha.le))⟩)
    have hh := (card_le_card hsub).trans (card_union_le _ _)
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hh
    have hcast : (count (fun n => p n ≤ (N:ℝ)^c) N : ℝ) ≤ (count (fun n => p n ≤ (n:ℝ)^a) N : ℝ) + ⌊δ*(N:ℝ)⌋₊ := by exact_mod_cast hh
    have hfloor := Nat.floor_le (mul_nonneg hd.le (Nat.cast_nonneg N))
    have hp : (0:ℝ) < N := by exact_mod_cast hN
    unfold density at *
    rw [lt_div_iff₀ hp] at hfix ⊢
    linarith
  · intro b hb
    filter_upwards [(tendsto_order.mp (h a ha ha1)).2 b hb] with N hN
    refine lt_of_le_of_lt (div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card ?_)) (Nat.cast_nonneg N)) hN
    intro n hn
    obtain ⟨hm,hp⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hm,hp.trans (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast (mem_Icc.mp hm).2) ha.le)⟩
theorem count_succ (P : ℕ → Prop) (N : ℕ) [DecidablePred P] :
    count P (N+1) = count P N + (if P (N+1) then 1 else 0) := by
  classical
  have he : Icc 1 (N+1) = insert (N+1) (Icc 1 N) := by ext i; simp; omega
  unfold count
  rw [he, filter_insert]
  split_ifs <;> simp_all

theorem count_shift (P : ℕ → Prop) (N : ℕ) [DecidablePred P] :
    count (fun n => P (n+1)) N + (if P 1 then 1 else 0) =
    count P N + (if P (N+1) then 1 else 0) := by
  induction N with
  | zero => simp [count]
  | succ N ih => rw [count_succ, count_succ P]; omega

theorem shiftFixed {p : ℕ → ℝ} {F : ℝ → ℝ} (h : Fixed p F) : Fixed (fun n => p (n+1)) F := by
  classical
  intro a ha ha1
  have hz : Tendsto (fun N : ℕ => 1 / (N:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim := h a ha ha1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hlim.sub hz) (by simpa using hlim.add hz)
  all_goals
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    let P := fun n => p n ≤ (N:ℝ)^a
    have hh := count_shift P N
    have h₁ : count P N ≤ count (fun n => P (n+1)) N + 1 := by split_ifs at hh <;> omega
    have h₂ : count (fun n => P (n+1)) N ≤ count P N + 1 := by split_ifs at hh <;> omega
    have hp : (0:ℝ) < N := by exact_mod_cast hN
    simp only [density, ← one_div]
    first
    | rw [← sub_div, div_le_div_iff_of_pos_right hp]; exact sub_le_iff_le_add.mpr (by exact_mod_cast h₁)
    | rw [← add_div, div_le_div_iff_of_pos_right hp]; exact_mod_cast h₂
end Marginal371
namespace Marginal371
open OAI.JointDickman
theorem h1_of_fixed (h : Fixed (fun n : ℕ => ((n.primeFactors.sup id : ℕ) : ℝ)) dickmanCDF) : OMA.R_erdos_371_R1.H1 := by
  refine ⟨dickmanCDF, dickmanCDF_continuous.continuousOn, dickmanCDF_zero, dickmanCDF_eq_one le_rfl, ?_⟩
  intro a ha ha1
  exact ⟨moving dickmanCDF_continuous h ha ha1, moving dickmanCDF_continuous (shiftFixed h) ha ha1⟩
end Marginal371

theorem OMA.solution : OMA.R_erdos_371_R1.H1 :=
  Marginal371.h1_of_fixed (fun _ ha ha1 => OAI.JointDickman.fixedSmooth_count_tendsto ha ha1)
