import OMAStatements.S_mo_142880
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Bases

-- BrownianContinuousMartingale
section
open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace BrownianContinuous

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The exponential of the drifted height, normalized to have mean one. -/
noncomputable def capital (d : ℝ) (t : ℝ≥0) (y : ℝ) := exp (2*d*(y - d*t))

theorem integral_capital (hB : IsPreBrownianReal B P) (d : ℝ) (t : ℝ≥0) :
    (∫ ω, capital d t (B t ω) ∂P) = 1 := by
  have hfactor (ω : Ω) : capital d t (B t ω) =
      exp (-(2*d^2*(t:ℝ))) * exp ((2*d)*B t ω) := by
    rw [capital, ← exp_add]
    congr 1
    ring
  simp_rw [hfactor]
  rw [integral_const_mul, ← mgf, mgf_gaussianReal (hB.hasLaw_eval t).map_eq, ← exp_add]
  convert exp_zero using 2
  ring

/-- The drift-normalized exponential has the martingale test-integral
identity against every measurable function of countably many past coordinates at a deterministic time. -/
theorem past_weighted_capital {ι : Type*} [Countable ι] (hB : IsPreBrownianReal B P) (d : ℝ) (s r : ℝ≥0)
    (times : ι → Iic s) (F : (ι → ℝ) → ℝ) (hF : Measurable F) :
    (∫ ω, capital d (s+r) (B (s+r) ω) * F (fun i => B (times i) ω) ∂P) =
      ∫ ω, capital d s (B s ω) * F (fun i => B (times i) ω) ∂P := by
  let f : (ℝ≥0 → ℝ) → ℝ := fun path => capital d r (path r)
  let g : (Iic s → ℝ) → ℝ := fun path => capital d s (path ⟨s, show s ≤ s from le_rfl⟩) * F (fun i => path (times i))
  have hfactor (ω : Ω) : capital d (s+r) (B (s+r) ω) * F (fun i => B (times i) ω) =
      f (fun t => B (s+t) ω - B s ω) * g (fun u => B u ω) := by
    dsimp [f,g,capital]
    rw [← mul_assoc, ← exp_add]
    congr 2
    ring
  have hf : Measurable f := by dsimp [f,capital]; fun_prop
  have hg : Measurable g := by dsimp [g,capital]; fun_prop
  have hpath : AEMeasurable (fun ω i => B (times i) ω) P :=
    aemeasurable_pi_lambda _ (fun i => hB.aemeasurable (times i))
  have hweight := hF.comp_aemeasurable hpath
  have hX : AEMeasurable (fun ω => f (fun t => B (s+t) ω - B s ω)) P := by
    dsimp [f,capital]
    have h1 := hB.aemeasurable (s+r)
    have h2 := hB.aemeasurable s
    fun_prop
  have hY : AEMeasurable (fun ω => g (fun t => B t ω)) P := by
    have h1 := hB.aemeasurable s
    apply AEMeasurable.mul _ hweight
    dsimp [capital]
    fun_prop
  simp_rw [hfactor]
  trans (∫ ω, f (fun t => B (s+t) ω - B s ω) ∂P) * ∫ ω, g (fun t => B t ω) ∂P
  · exact ((hB.indepFun_shift s).comp hf hg).integral_fun_mul_eq_mul_integral
      hX.aestronglyMeasurable hY.aestronglyMeasurable
  change (∫ ω, capital d r (B (s+r) ω - B s ω) ∂P) * _ = _
  rw [integral_capital (hB.shift s), one_mul]

end BrownianContinuous
end

-- BrownianContinuousMaximal
section
open MeasureTheory ProbabilityTheory Set Real Finset
open scoped NNReal ENNReal

namespace BrownianContinuous
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- On any increasing deterministic grid, the exponential of a Brownian path with
drift is a martingale in the natural filtration of measurable versions of the samples. -/
theorem grid_capital_martingale (hB : IsPreBrownianReal B P) (d : ℝ) (t : ℕ → ℝ≥0)
    (ht : Monotone t) (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable (Y i))
    (hversion : ∀ i, B (t i) =ᵐ[P] Y i) :
    Martingale (fun n ω => capital d (t n) (Y n ω)) (Filtration.natural Y hY) P := by
  have hall : ∀ᵐ ω ∂P, ∀ i, B (t i) ω = Y i ω := ae_all_iff.mpr hversion
  have hmean (n : ℕ) : (∫ ω, capital d (t n) (Y n ω) ∂P) = 1 := by
    rw [← integral_capital hB d (t n)]
    apply integral_congr_ae
    filter_upwards [hversion n] with ω he using congrArg (capital d (t n)) he.symm
  apply martingale_of_setIntegral_eq_succ
  · intro n
    exact ((show Continuous (capital d (t n)) by unfold capital; fun_prop).comp_stronglyMeasurable
      (Filtration.stronglyAdapted_natural hY n))
  · intro n
    exact integrable_of_integral_eq_one (hmean n)
  · intro n U hU
    rw [Filtration.natural_eq_comap] at hU
    obtain ⟨V,hV,rfl⟩ := hU
    let F : (Set.Iic n → ℝ) → ℝ := V.indicator (fun _ => 1)
    let times : Set.Iic n → Set.Iic (t n) := fun j => ⟨t j, ht j.property⟩
    have htest := past_weighted_capital hB d (t n) (t (n+1)-t n) times F
      (measurable_const.indicator hV)
    rw [add_tsub_cancel_of_le (ht (Nat.le_succ n))] at htest
    have htransfer (k : ℕ) :
        (∫ ω, capital d (t k) (B (t k) ω) * F (fun j => B (times j) ω) ∂P) =
          ∫ ω in (fun ω (j : Set.Iic n) => Y j ω) ⁻¹' V, capital d (t k) (Y k ω) ∂P := by
      have hpre : MeasurableSet ((fun ω (j : Set.Iic n) => Y j ω) ⁻¹' V) :=
        (measurable_pi_lambda _ (fun j : Set.Iic n => (hY j).measurable)) hV
      rw [← integral_indicator hpre]
      apply integral_congr_ae
      filter_upwards [hall] with ω hω
      have hcoords : (fun j => B (times j) ω) = (fun j : Set.Iic n => Y j ω) :=
        funext fun j => hω j
      rw [hcoords,hω]
      by_cases hmem : (fun j : Set.Iic n => Y j ω) ∈ V <;> simp [F,hmem]
    exact (htransfer n).symm.trans (htest.symm.trans (htransfer (n+1)))

/-- Doob's inequality bounds every finite grid by the same threshold. -/
theorem grid_crossing_bound (hB : IsPreBrownianReal B P) (d : ℝ) (t : ℕ → ℝ≥0)
    (ht : Monotone t) (a : ℝ≥0) (N : ℕ) :
    (a:ℝ≥0∞) * P {ω | ∃ k ≤ N, (a:ℝ) ≤ capital d (t k) (B (t k) ω)} ≤ 1 := by
  let Y : ℕ → Ω → ℝ := fun k => (hB.aemeasurable (t k)).mk _
  have hY (k : ℕ) : StronglyMeasurable (Y k) := (hB.aemeasurable (t k)).measurable_mk.stronglyMeasurable
  have hversions (k : ℕ) : B (t k) =ᵐ[P] Y k := (hB.aemeasurable (t k)).ae_eq_mk
  have hm := grid_capital_martingale hB d t ht Y hY hversions
  let Z : ℕ → Ω → ℝ := fun k ω => capital d (t k) (Y k ω)
  have hZ : 0 ≤ Z := fun k ω => (Real.exp_pos _).le
  have hdoob := maximal_ineq hm.submartingale hZ (ε := a) N
  have hall : ∀ᵐ ω ∂P, ∀ k, B (t k) ω = Y k ω := ae_all_iff.mpr hversions
  have hmass : P {ω | ∃ k ≤ N, (a:ℝ) ≤ capital d (t k) (B (t k) ω)} =
      P {ω | (a:ℝ) ≤ (range (N+1)).sup' nonempty_range_add_one (fun k => Z k ω)} := by
    apply measure_congr
    filter_upwards [hall] with ω hw
    apply propext
    change (∃ k ≤ N, _) ↔ (a:ℝ) ≤ _
    simp only [le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff, Z, hw]
  rw [hmass]
  apply hdoob.trans
  have hu := setIntegral_le_integral (s := {ω | (a:ℝ) ≤ (range (N+1)).sup' nonempty_range_add_one
    (fun k => Z k ω)}) (hm.integrable N) (Filter.Eventually.of_forall (hZ N))
  apply le_trans (ENNReal.ofReal_le_ofReal hu)
  have he : ∫ ω, Z N ω ∂P = 1 := by
    rw [← integral_capital hB d (t N)]
    apply integral_congr_ae
    filter_upwards [hversions N] with ω hω using congrArg (capital d (t N)) hω.symm
  change ENNReal.ofReal (∫ ω, Z N ω ∂P) ≤ 1
  rw [he, ENNReal.ofReal_one]

end BrownianContinuous
end

-- BrownianContinuousHitting
section
open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace BrownianContinuous
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

theorem sequence_crossing_bound (hB : IsPreBrownianReal B P) (d : ℝ) (v : ℕ → ℝ≥0)
    (a : ℝ≥0) :
    (a : ℝ≥0∞) * P {ω | ∃ i, (a : ℝ) ≤ capital d (v i) (B (v i) ω)} ≤ 1 := by
  let E (N : ℕ) := {ω | ∃ i ≤ N, (a : ℝ) ≤ capital d (v i) (B (v i) ω)}
  have hm : Monotone E := by
    intro n k h ω
    rintro ⟨i,hi,hw⟩
    exact ⟨i,hi.trans h,hw⟩
  have hu : {ω | ∃ i, (a : ℝ) ≤ capital d (v i) (B (v i) ω)} = ⋃ N, E N := by
    ext ω
    constructor
    · rintro ⟨i,hi⟩
      exact mem_iUnion.mpr ⟨i,i,le_rfl,hi⟩
    · intro hw
      obtain ⟨N,i,_,hi⟩ := mem_iUnion.mp hw
      exact ⟨i,hi⟩
  rw [hu, hm.measure_iUnion, ENNReal.mul_iSup]
  apply iSup_le
  intro N
  let v₀ : Fin (N+1) → ℝ≥0 := fun i => v i
  let clip (i : ℕ) : Fin (N+1) := ⟨min i N, by omega⟩
  have hc : Monotone clip := by intro i j hij; exact min_le_min_right N hij
  let grid := (v₀ ∘ Tuple.sort v₀) ∘ clip
  have hgrid : Monotone grid := (Tuple.monotone_sort v₀).comp hc
  apply le_trans _ (grid_crossing_bound hB d grid hgrid a N)
  apply mul_le_mul_right
  apply measure_mono
  intro ω
  rintro ⟨i,hi,hw⟩
  let j := (Tuple.sort v₀).symm ⟨i,by omega⟩
  have hj : (j:ℕ) ≤ N := by have hj' := j.isLt; omega
  have hcj : clip j = j := Fin.ext (min_eq_left hj)
  use j, hj
  simpa [grid, Function.comp_apply, hcj, j, v₀] using hw

/-- Every strict crossing of a continuous Brownian arm is seen by a fixed
countable dense set of times. Ville's bound therefore applies on the whole half-line. -/
theorem continuous_capital_crossing_bound (hB : IsBrownianReal B P) (d : ℝ) (a : ℝ≥0) :
    (a : ℝ≥0∞) * P {ω | ∃ t, (a:ℝ) < capital d t (B t ω)} ≤ 1 := by
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  apply le_trans _ (sequence_crossing_bound hB.toIsPreBrownianReal d v a)
  apply mul_le_mul_right
  apply measure_mono_ae
  filter_upwards [hB.cont] with ω hw
  rintro ⟨t,ht⟩
  have hcont : Continuous (fun u => capital d u (B u ω)) := by unfold capital; fun_prop
  obtain ⟨i,hi⟩ := hv.exists_mem_open (hcont.isOpen_preimage _ isOpen_Ioi) ⟨t,ht⟩
  exact ⟨i,hi.le⟩

/-- An unconditional upper bound on the chance of ever clearing a positive-height
barrier for a Brownian arm of negative drift. -/
theorem drifted_hitting_upper (hB : IsBrownianReal B P) {d : ℝ} (hd : 0 < d) (z : ℝ) :
    P {ω | ∃ t : ℝ≥0, z < B t ω - d * t} ≤ ENNReal.ofReal (exp (-(2*d*z))) := by
  let a : ℝ≥0 := ⟨exp (2*d*z), (exp_pos _).le⟩
  have hm := continuous_capital_crossing_bound hB d a
  have hset : {ω | ∃ t : ℝ≥0, z < B t ω - d * t} = {ω | ∃ t, (a:ℝ) < capital d t (B t ω)} := by
    ext ω
    change (∃ t:ℝ≥0, z < B t ω - d*t) ↔ ∃ t:ℝ≥0, exp (2*d*z) < exp (2*d*(B t ω - d*t))
    simp only [exp_lt_exp, mul_lt_mul_iff_right₀ (by positivity : 0 < 2*d)]
  rw [hset]
  calc
    _ = ENNReal.ofReal (exp (-(2*d*z))) * ((a:ℝ≥0∞) * P {ω | ∃ t, (a:ℝ) < capital d t (B t ω)}) := by
      rw [← mul_assoc]
      have ha : (a:ℝ≥0∞) = ENNReal.ofReal (exp (2*d*z)) := by
        exact ENNReal.coe_nnreal_eq a
      rw [ha, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
      simp
    _ ≤ _ := by simpa using mul_le_mul_right hm (ENNReal.ofReal (exp (-(2*d*z))))

end BrownianContinuous
end

-- BrownianContinuousOvershoot
section
open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

namespace BrownianContinuous
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- Square root of the terminal capital has an exponentially decreasing mean. -/
theorem integral_half_capital (hB : IsPreBrownianReal B P) (d : ℝ) (t : ℝ≥0) :
    (∫ ω, exp (d*(B t ω-d*t)) ∂P) = exp (-(d^2*(t:ℝ))/2) := by
  have h (ω : Ω) : exp (d*(B t ω -d*t)) = exp (-(d^2*(t:ℝ))) * exp (d*B t ω) := by
    rw [← exp_add]; congr 1; ring
  simp_rw [h]
  rw [integral_const_mul, ← mgf, mgf_gaussianReal (hB.hasLaw_eval t).map_eq, ← exp_add]
  congr 1
  ring

/-- Mean of the exponential penalty used to control large one-step overshoots. -/
theorem integral_increment (hB : IsPreBrownianReal B P) (s t : ℝ≥0) (c : ℝ) :
    (∫ ω, exp (c*(B (s+t) ω-B s ω)) ∂P) = exp ((t:ℝ)*c^2/2) := by
  rw [← mgf, mgf_gaussianReal ((hB.shift s).hasLaw_eval t).map_eq]
  simp

/-- The first sampled crossing, stopped no later than a fixed grid index, has
expected capital one. -/
theorem stopped_mean (hB : IsPreBrownianReal B P) (d : ℝ) (t : ℕ → ℝ≥0)
    (ht : Monotone t) (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable (Y i))
    (hversion : ∀ i, B (t i) =ᵐ[P] Y i) (a : ℝ) (N : ℕ) :
    let Z := fun k ω => capital d (t k) (Y k ω)
    let τ := hittingBtwn Z (Ioi a) 0 N
    (∫ ω, Z (τ ω) ω ∂P) = 1 := by
  intro Z τ
  let F := Filtration.natural Y hY
  have hm : Martingale Z F P := grid_capital_martingale hB d t ht Y hY hversion
  have hs : IsStoppingTime F (fun ω => (τ ω : ℕ∞)) :=
    hm.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ioi
  have hb (ω : Ω) : (τ ω : ℕ∞) ≤ (N : ℕ∞) := by exact_mod_cast (hittingBtwn_le (u:=Z) (s:=Ioi a) (n:=0) (m:=N) ω)
  have he := hm.stoppedValue_ae_eq_condExp_of_le_const hs hb
  change (∫ ω, stoppedValue Z (fun ω => (τ ω : ℕ∞)) ω ∂P) = 1
  rw [integral_congr_ae he, integral_condExp hs.measurableSpace_le, ← integral_capital hB d (t N)]
  apply integral_congr_ae
  filter_upwards [hversion N] with ω hω using congrArg (capital d (t N)) hω.symm

/-- A deterministic bound on the first strictly crossing sample. An overshooting
step carries the additional exponential penalty with parameter `r`. -/
theorem overshoot_path (y : ℕ → ℝ) {d u z e r : ℝ} (hd : 0 < d) (hu : 0 ≤ u)
    (hz : 0 ≤ z) (hr : 0 ≤ r) (hy : y 0 = 0) (N : ℕ) :
    let x (k : ℕ) := y k - d*(k*u)
    let Z (k : ℕ) (_ : Unit) := exp (2*d*x k)
    let τ := hittingBtwn Z (Ioi (exp (2*d*z))) 0 N ()
    Z τ () ≤ (if ∃ i ≤ N, z < x i then exp (2*d*(z+e)) else 0) +
      exp (d*z) * exp (d*x N) +
      exp (2*d*z) * exp (-(r*e)) * ∑ k ∈ Finset.range N, exp ((2*d+r)*(y (k+1)-y k)) := by
  classical
  intro x Z τ
  let a := exp (2*d*z)
  have hexp : 0 < 2*d := by positivity
  have hcommon : 0 ≤ exp (2*d*z) * exp (-(r*e)) * ∑ k ∈ Finset.range N, exp ((2*d+r)*(y (k+1)-y k)) := by positivity
  by_cases hc : ∃ i ≤ N, z < x i
  · rw [if_pos hc]
    have hτ : τ ≤ N := hittingBtwn_le ()
    have hτpos : 0 < τ := by
      have ⟨i,hi,hxi⟩ := hc
      have hevent : ∃ j ∈ Icc 0 N, Z j () ∈ Ioi a :=
        ⟨i,⟨Nat.zero_le _,hi⟩, exp_lt_exp.mpr (mul_lt_mul_of_pos_left hxi hexp)⟩
      have hit := hittingBtwn_mem_set hevent
      by_contra!
      have heq : τ = 0 := by omega
      change a < Z τ () at hit
      rw [heq] at hit
      simp [x, Z, a, hy] at hit
      exact (not_lt_of_ge (mul_nonneg hexp.le hz)) hit
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hτpos.ne'
    have hbefore : x k ≤ z := by
      have hn := notMem_of_lt_hittingBtwn (u:=Z) (s:=Ioi a) (n:=0) (m:=N) (ω:=())
        (k:=k) (by change k < τ; omega) (Nat.zero_le _)
      change ¬exp (2*d*z) < exp (2*d*x k) at hn
      simpa only [exp_lt_exp, mul_lt_mul_iff_right₀ hexp, not_lt] using hn
    have hx : x τ = x k + (y (k+1)-y k) - d*u := by rw [hk]; simp [x]; ring
    by_cases hstep : y (k+1)-y k ≤ e
    · have hup : Z τ () ≤ exp (2*d*(z+e)) := by
        apply exp_le_exp.mpr
        gcongr
        linarith [mul_nonneg hd.le hu]
      exact le_trans hup (by linarith [mul_nonneg (exp_pos (d*z)).le (exp_pos (d*x N)).le])
    · have hpen : Z τ () ≤ exp (2*d*z) * exp (-(r*e)) * exp ((2*d+r)*(y (k+1)-y k)) := by
        rw [← exp_add, ← exp_add]
        apply exp_le_exp.mpr
        rw [hx]
        nlinarith [mul_nonneg (sub_nonneg.mpr hbefore) hd.le, mul_nonneg hr (sub_nonneg.mpr (not_le.mp hstep).le), mul_nonneg (sq_nonneg d) hu]
      have hterm := Finset.single_le_sum (fun (i:ℕ) (_:i ∈ Finset.range N) => (exp_pos ((2*d+r)*(y (i+1)-y i))).le)
        (show k ∈ Finset.range N by simp; omega)
      have hmul := mul_le_mul_of_nonneg_left hterm (show 0 ≤ exp (2*d*z) * exp (-(r*e)) by positivity)
      exact hpen.trans (by linarith [exp_pos (2*d*(z+e)), mul_nonneg (exp_pos (d*z)).le (exp_pos (d*x N)).le])
  · rw [if_neg hc, zero_add]
    have hn (i : ℕ) (hi : i ≤ N) : x i ≤ z := le_of_not_gt (fun h => hc ⟨i,hi,h⟩)
    have hnone : ¬∃ i ∈ Icc 0 N, Z i () ∈ Ioi a := by
      rintro ⟨i,hi,he⟩
      exact not_lt_of_ge (exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hn i hi.2) hexp.le)) he
    have heq : τ = N := by
      change hittingBtwn Z (Ioi a) 0 N () = N
      rw [hittingBtwn, if_neg hnone]
    rw [heq]
    have hZ : Z N () ≤ exp (d*z)*exp (d*x N) := by
      rw [← exp_add]
      exact exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left (hn N le_rfl) hd.le])
    linarith

end BrownianContinuous
end

-- BrownianContinuousLower
section
open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace BrownianContinuous

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

theorem grid_hitting_lower (hB : IsPreBrownianReal B P) {d z r : ℝ} (hd : 0 < d)
    (hz : 0 ≤ z) (hr : 0 ≤ r) (e : ℝ) (u : ℝ≥0) (N : ℕ) :
    1 ≤ exp (2*d*(z+e)) * P.real {ω | ∃ t:ℝ≥0, z < B t ω - d*t} +
      exp (d*z)*exp (-(d^2*(N*(u:ℝ)))/2) +
      exp (2*d*z)*exp (-(r*e)) * (N*exp ((u:ℝ)*(2*d+r)^2/2)) := by
  classical
  let t (k : ℕ) : ℝ≥0 := k*u
  have ht : Monotone t := by intro i j h; dsimp [t]; gcongr
  let Y (k : ℕ) := (hB.aemeasurable (t k)).mk _
  have hY (k : ℕ) : StronglyMeasurable (Y k) := (hB.aemeasurable (t k)).measurable_mk.stronglyMeasurable
  have hv (k : ℕ) : B (t k) =ᵐ[P] Y k := (hB.aemeasurable (t k)).ae_eq_mk
  have hall : ∀ᵐ ω ∂P, ∀ k, B (t k) ω = Y k ω := ae_all_iff.mpr hv
  let Z (k : ℕ) (ω : Ω) := capital d (t k) (Y k ω)
  let τ := hittingBtwn Z (Ioi (exp (2*d*z))) 0 N
  have hstop : (∫ ω, Z (τ ω) ω ∂P) = 1 := stopped_mean hB d t ht Y hY hv _ N
  let A := {ω | ∃ i ≤ N, z < Y i ω -d*(i*(u:ℝ))}
  have hA : MeasurableSet A := by
    have heq : A = ⋃ i : Fin (N+1), {ω | z < Y i ω -d*((i:ℕ)*(u:ℝ))} := by
      ext ω
      simp only [A,mem_iUnion,mem_ofPred_eq, Fin.exists_iff, Nat.lt_succ_iff]
      tauto
    rw [heq]
    exact MeasurableSet.iUnion (fun i => measurableSet_lt measurable_const ((hY i).measurable.sub measurable_const))
  let l (ω : Ω) := exp (d*(Y N ω-d*(N*(u:ℝ))))
  have hl : (∫ ω, l ω ∂P) = exp (-(d^2*(N*(u:ℝ)))/2) := by
    convert (integral_half_capital hB d (t N)) using 1
    · apply integral_congr_ae
      filter_upwards [hv N] with ω hw
      simp [l,t,hw]
    · simp [t]
  let W (k : ℕ) (ω : Ω) := exp ((2*d+r)*(Y (k+1) ω-Y k ω))
  have hW (k : ℕ) : (∫ ω, W k ω ∂P) = exp ((u:ℝ)*(2*d+r)^2/2) := by
    rw [← integral_increment hB (t k) u (2*d+r)]
    apply integral_congr_ae
    filter_upwards [hv k,hv (k+1)] with ω h1 h2
    have hnext : t (k+1) = t k + u := by simp [t,add_mul]
    simp [W,←hnext,h1,h2]
  have il : Integrable l P := Integrable.of_integral_ne_zero (by rw [hl]; positivity)
  have iW (k : ℕ) : Integrable (W k) P := Integrable.of_integral_ne_zero (by rw [hW k]; positivity)
  have isum : Integrable (fun ω => ∑ k ∈ Finset.range N, W k ω) P :=
    integrable_finsetSum _ (fun k _ => iW k)
  have hzero : ∀ᵐ ω ∂P, Y 0 ω = 0 := by
    filter_upwards [hv 0,hB.eval_zero_ae_eq_zero] with ω h1 h2
    simpa [t,h2] using h1.symm
  let b := exp (2*d*(z+e))
  let c := exp (2*d*z)*exp (-(r*e))
  have bound : (fun ω => Z (τ ω) ω) ≤ᵐ[P] (fun ω =>
      A.indicator (fun _ => b) ω + exp (d*z)*l ω + c*(∑ k ∈ Finset.range N, W k ω)) := by
    filter_upwards [hzero] with ω hω
    have h := overshoot_path (fun k => Y k ω) hd u.property hz hr hω N (e := e)
    have hidx : τ ω = hittingBtwn (fun k (_ : Unit) => exp (2*d*(Y k ω-d*(k*(u:ℝ)))))
        (Ioi (exp (2*d*z))) 0 N () := by
      simp only [τ, hittingBtwn, Z, capital, t, NNReal.coe_mul, NNReal.coe_natCast]
    dsimp only at h
    simp only [Z, capital, t, NNReal.coe_mul, NNReal.coe_natCast, hidx, A, Set.indicator, Set.mem_ofPred_eq, b,l,c,W]
    exact h
  have ib : Integrable (A.indicator (fun _ : Ω => b)) P := (integrable_const b).indicator hA
  have icomp := integral_mono_ae (integrable_of_integral_eq_one hstop)
    ((ib.add (il.const_mul (exp (d*z)))).add (isum.const_mul c)) bound
  rw [hstop] at icomp
  have hmass : P.real A ≤ P.real {ω | ∃ t:ℝ≥0, z < B t ω - d*t} := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hall] with ω hw
    rintro ⟨i,_,h⟩
    use t i
    simpa [t,hw] using h
  have hI : (∫ ω, A.indicator (fun _ => b) ω ∂P) = b * P.real A := by
    rw [integral_indicator hA, setIntegral_const]
    simp [smul_eq_mul, mul_comm]
  change 1 ≤ (∫ ω, (A.indicator (fun _ => b) ω + exp (d*z)*l ω) + c*(∑ k ∈ Finset.range N, W k ω) ∂P) at icomp
  rw [integral_add (show Integrable (fun ω => A.indicator (fun _ => b) ω + exp (d*z)*l ω) P from ib.add (il.const_mul _)) (isum.const_mul _),
    integral_add ib (il.const_mul _), hI, integral_const_mul, hl,
    integral_const_mul, integral_finsetSum _ (fun k _ => iW k)] at icomp
  simp only [hW,Finset.sum_const, Finset.card_range, nsmul_eq_mul] at icomp
  exact icomp.trans (by dsimp [b,c]; gcongr)

end BrownianContinuous
end

-- BrownianContinuousLaw
section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal Topology

namespace BrownianContinuous
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- Every continuous drifted Brownian arm has exactly the classical exponential
barrier-crossing law. The lower estimate uses overshoot control on refining
deterministic grids and the vanishing mean of the square root of terminal capital. -/
theorem drifted_hitting_law (hB : IsBrownianReal B P) {d z : ℝ} (hd : 0 < d) (hz : 0 ≤ z) :
    P.real {ω | ∃ t:ℝ≥0, z < B t ω - d*t} = exp (-(2*d*z)) := by
  let p := P.real {ω | ∃ t:ℝ≥0, z < B t ω - d*t}
  have hp (e : ℝ) (he : 0 < e) : 1 ≤ exp (2*d*(z+e))*p := by
    let L := exp (2*d*(z+e))*p
    let C := exp (2*d*z)*exp ((2*d+1)^2/2)
    have hseq (m : ℕ) (hm : 1 ≤ m) :
        1 ≤ L + exp (d*z)*exp (-(d^2/2)*(m:ℝ)) +
          C*((m:ℝ)^3 * exp (-e*m)) := by
      have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
      have hmpos : (0:ℝ) < m := by linarith
      let u : ℝ≥0 := ⟨1/(m:ℝ)^2,by positivity⟩
      have ht := grid_hitting_lower hB.toIsPreBrownianReal hd hz hmpos.le e u (m^3)
      simp only [Nat.cast_pow] at ht
      have htime : (m:ℝ)^3*(u:ℝ) = m := by change (m:ℝ)^3*(1/(m:ℝ)^2) = m; field_simp
      have htilt : (u:ℝ)*(2*d+m)^2/2 ≤ (2*d+1)^2/2 := by
        change (1/(m:ℝ)^2)*(2*d+m)^2/2 ≤ _
        have hlt : 2*d+m ≤ (2*d+1)*m := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hm')]
        have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2*d+(m:ℝ)) hlt 2
        apply (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)).mpr
        rw [one_div, inv_mul_le_iff₀ (by positivity)]
        nlinarith only [hsq]
      rw [htime] at ht
      calc
        1 ≤ _ := ht
        _ ≤ L + exp (d*z)*exp (-(d^2/2)*(m:ℝ)) +
              exp (2*d*z)*exp (-((m:ℝ)*e))*((m:ℝ)^3*exp ((2*d+1)^2/2)) := by
                dsimp [L,p]
                have : -(d^2*(m:ℝ))/2 = -(d^2/2)*m := by ring
                rw [this]
                gcongr
        _ = _ := by dsimp [C]; rw [show -e*(m:ℝ) = -(m*e) by ring]; ring
    have hdec : Tendsto (fun m : ℕ => exp (-(d^2/2)*(m:ℝ))) atTop (𝓝 0) := by
      have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (d^2/2) (by positivity)).comp
        (tendsto_natCast_atTop_atTop (R:=ℝ))
      simpa [Function.comp_def] using h
    have htail : Tendsto (fun m : ℕ => (m:ℝ)^3 * exp (-e*m)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 e he).comp
        (tendsto_natCast_atTop_atTop (R:=ℝ))
      simpa [Function.comp_def] using h
    have hlim : Tendsto (fun m : ℕ => L + exp (d*z)*exp (-(d^2/2)*(m:ℝ)) + C*((m:ℝ)^3 * exp (-e*m)))
        atTop (𝓝 L) := by
      simpa using (tendsto_const_nhds (x:=L)).add (hdec.const_mul (exp (d*z))) |>.add (htail.const_mul C)
    exact ge_of_tendsto hlim (eventually_atTop.2 ⟨1,hseq⟩)
  have hlim : Tendsto (fun e : ℝ => exp (2*d*(z+e))*p) (𝓝[>] 0) (𝓝 (exp (2*d*z)*p)) := by
    have hc : Continuous (fun e : ℝ => exp (2*d*(z+e))*p) := by fun_prop
    have hh : Tendsto (fun e : ℝ => exp (2*d*(z+e))*p) (𝓝[>] 0) (𝓝 (exp (2*d*(z+0))*p)) :=
      (hc.continuousAt (x:=0)).continuousWithinAt
    simpa using hh
  have hlow := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hp)
  have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top (drifted_hitting_upper hB hd z)
  rw [ENNReal.toReal_ofReal (exp_pos _).le] at hu
  apply le_antisymm hu
  change exp (-(2*d*z)) ≤ p
  rw [Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (exp_pos _)).mpr
  simpa [mul_comm] using hlow

end BrownianContinuous
end

-- BrownianContinuousMaximum
section
open MeasureTheory ProbabilityTheory Set Real Filter TopologicalSpace
open scoped NNReal ENNReal Topology

namespace BrownianContinuous

/-- A measurable functional of sampled paths. On continuous paths the
strict level sets coincide with crossing events on the whole time axis. -/
noncomputable def maximumE (d : ℝ) (f : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (f (denseSeq ℝ≥0 n)-d*(denseSeq ℝ≥0 n : ℝ≥0))

noncomputable def maximum (d : ℝ) (f : ℝ≥0 → ℝ) : ℝ := (maximumE d f).toReal

theorem measurable_maximumE (d : ℝ) : Measurable (maximumE d) := by
  unfold maximumE
  fun_prop

theorem measurable_maximum (d : ℝ) : Measurable (maximum d) :=
  ENNReal.measurable_toReal.comp (measurable_maximumE d)

theorem maximumE_gt {f : ℝ≥0 → ℝ} (hf : Continuous f) (d : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    ENNReal.ofReal z < maximumE d f ↔ ∃ t:ℝ≥0, z < f t-d*t := by
  rw [maximumE, lt_iSup_iff]
  simp only [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hz]
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨_,hn⟩
  · rintro ⟨t,ht⟩
    have ho : IsOpen {t:ℝ≥0 | z < f t -d*t} :=
      isOpen_lt continuous_const (by fun_prop)
    exact (denseRange_denseSeq ℝ≥0).exists_mem_open ho ⟨t,ht⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}

theorem aemeasurable_path_maximum (hB : IsPreBrownianReal B P) (d : ℝ) :
    AEMeasurable (fun ω => maximum d (fun t => B t ω)) P := by
  apply ENNReal.measurable_toReal.comp_aemeasurable
  change AEMeasurable (fun ω => ⨆ n, ENNReal.ofReal (B (denseSeq ℝ≥0 n) ω - d*(denseSeq ℝ≥0 n : ℝ≥0))) P
  exact AEMeasurable.iSup (fun n => ENNReal.measurable_ofReal.comp_aemeasurable
    ((hB.aemeasurable _).sub aemeasurable_const))

theorem maximumE_tail (hB : IsBrownianReal B P) {d z : ℝ} (hd : 0 < d) (hz : 0 ≤ z) :
    P.real {ω | ENNReal.ofReal z < maximumE d (fun t => B t ω)} = exp (-(2*d*z)) := by
  rw [← drifted_hitting_law hB hd hz]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hB.cont] with ω hw
  exact propext (maximumE_gt hw d hz)

theorem maximumE_finite (hB : IsBrownianReal B P) {d : ℝ} (hd : 0 < d) :
    ∀ᵐ ω ∂P, maximumE d (fun t => B t ω) ≠ ⊤ := by
  rw [ae_iff]
  simp only [not_not]
  apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
  apply le_antisymm _ measureReal_nonneg
  have hlim : Tendsto (fun z : ℝ => exp (-(2*d*z))) atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (2*d) (by positivity)
    simpa [neg_mul] using h
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (0:ℝ)] with z hz
  rw [← maximumE_tail hB hd hz]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  change maximumE d (fun t => B t ω) = ⊤ at hω
  change ENNReal.ofReal z < maximumE d _
  rw [hω]
  exact ENNReal.ofReal_lt_top

theorem hasLaw_maximum (hB : IsBrownianReal B P) {d : ℝ} (hd : 0 < d) :
    HasLaw (fun ω => maximum d (fun t => B t ω)) (expMeasure (2*d)) P := by
  let M := fun ω => maximum d (fun t => B t ω)
  have hm : AEMeasurable M P := aemeasurable_path_maximum hB.toIsPreBrownianReal d
  let : IsProbabilityMeasure (P.map M) := Measure.isProbabilityMeasure_map hm
  let : IsProbabilityMeasure (expMeasure (2*d)) := isProbabilityMeasure_expMeasure (by positivity)
  refine ⟨hm,?_⟩
  change P.map M = expMeasure (2*d)
  rw [← measure_cdf (P.map M), ← measure_cdf (expMeasure (2*d))]
  congr 1
  ext x
  rw [cdf_expMeasure_eq (by positivity),cdf_eq_real]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, ← compl_Ioi, probReal_compl_eq_one_sub measurableSet_Ioi,
      map_measureReal_apply_of_aemeasurable hm measurableSet_Ioi, ← maximumE_tail hB hd hx]
    congr 1
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [maximumE_finite hB hd] with ω hfin
    apply propext
    change x < (maximumE d (fun t => B t ω)).toReal ↔ _
    nth_rw 1 [← ENNReal.toReal_ofReal hx]
    exact ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfin
  · rw [if_neg hx, map_measureReal_apply_of_aemeasurable hm measurableSet_Iic]
    have hn : M ⁻¹' Iic x = ∅ := by
      ext ω
      exact iff_false_intro (fun he => hx (le_trans ENNReal.toReal_nonneg he))
    simp [hn]

end BrownianContinuous
end

-- BrownianArms
section
open MeasureTheory ProbabilityTheory Set Real TopologicalSpace
open scoped ENNReal NNReal
namespace BrownianComparison
open BrownianContinuous OMA.S_mo_142880
noncomputable section

def pastGap (d : ℝ) (t : ℝ≥0) (f : Iic t → ℝ) : ℝ :=
  (⨆ n : ℕ, ENNReal.ofReal (f (denseSeq (Iic t) n) - d*((denseSeq (Iic t) n).val:ℝ) -
    (f ⟨t,by simp⟩ - d*t))).toReal

theorem measurable_pastGap (d : ℝ) (t : ℝ≥0) : Measurable (pastGap d t) := by
  unfold pastGap
  fun_prop

/-- The sampled drawdown equals the greatest height difference on the compact prefix. -/
theorem pastGap_isMax (d : ℝ) (t : ℝ≥0) (f : Iic t → ℝ) (hf : Continuous f) :
    ∃ s : Iic t, pastGap d t f = f s-d*(s.val:ℝ)-(f ⟨t,by simp⟩-d*t) ∧
      ∀ u : Iic t, f u-d*(u.val:ℝ)-(f ⟨t,by simp⟩-d*t) ≤ pastGap d t f := by
  let g (s : Iic t) := f s-d*(s.val:ℝ)-(f ⟨t,by simp⟩-d*t)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hc : IsCompact (Iic t) := by
    rw [show Iic t = Icc 0 t by ext; simp]
    exact isCompact_Icc
  letI : CompactSpace (Iic t) := isCompact_iff_compactSpace.mp hc
  obtain ⟨s,_,hs⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty (α:=Iic t)) hg.continuousOn
  have hx (u : Iic t) : g u ≤ g s := hs (mem_univ u)
  have hpos : 0 ≤ g s := by simpa [g] using hx ⟨t,by simp⟩
  have he : (⨆ n : ℕ, ENNReal.ofReal (g (denseSeq _ n))) = ENNReal.ofReal (g s) := by
    apply le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (hx _))
    by_contra! h
    have hfin := h.trans ENNReal.ofReal_lt_top
    let a := (⨆ n : ℕ, ENNReal.ofReal (g (denseSeq _ n))).toReal
    have ha : a < g s := by
      simpa [a, ENNReal.toReal_ofReal hpos] using (ENNReal.toReal_lt_toReal hfin.ne ENNReal.ofReal_ne_top).mpr h
    obtain ⟨i,hi⟩ := (denseRange_denseSeq (Iic t)).exists_mem_open (hg.isOpen_preimage (Ioi a) isOpen_Ioi) ⟨s,ha⟩
    have hi' : ENNReal.ofReal a < ENNReal.ofReal (g (denseSeq _ i)) :=
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg |>.mpr hi
    rw [show ENNReal.ofReal a = _ from ENNReal.ofReal_toReal hfin.ne] at hi'
    exact not_lt_of_ge (le_iSup (fun n => ENNReal.ofReal (g (denseSeq _ n))) i) hi'
  have he' : pastGap d t f = g s := by
    change (⨆ n : ℕ, ENNReal.ofReal (g (denseSeq _ n))).toReal = g s
    rw [he, ENNReal.toReal_ofReal hpos]
  exact ⟨s,he',fun u => he' ▸ hx u⟩

lemma maximum_gt_iff {f : ℝ≥0 → ℝ} (hf : Continuous f) (d : ℝ) (hfin : maximumE d f ≠ ⊤)
    {z : ℝ} (hz : 0 ≤ z) : z < maximum d f ↔ ∃ u:ℝ≥0, z < f u-d*u := by
  rw [← maximumE_gt hf d hz]
  change z < (maximumE d f).toReal ↔ _
  nth_rw 1 [← ENNReal.toReal_ofReal hz]
  exact ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfin

lemma le_maximum {f : ℝ≥0 → ℝ} (hf : Continuous f) (d : ℝ) (hfin : maximumE d f ≠ ⊤)
    (u : ℝ≥0) : f u-d*u ≤ maximum d f := by
  by_contra! h
  have hx := (maximum_gt_iff hf d hfin (z:=maximum d f) ENNReal.toReal_nonneg).mpr ⟨u,h⟩
  exact lt_irrefl _ hx

end
end BrownianComparison
end

-- BrownianArmsPath
section
open MeasureTheory ProbabilityTheory Set Real TopologicalSpace
open scoped ENNReal NNReal
namespace BrownianComparison
open BrownianContinuous OMA.S_mo_142880
noncomputable section

def gapAt (d : ℝ) (t : ℝ≥0) (f : ℝ≥0 → ℝ) := pastGap d t (fun u => f u.val)
def futureAt (d : ℝ) (t : ℝ≥0) (f : ℝ≥0 → ℝ) := maximum d (fun u => f (t+u)-f t)

theorem measurable_gapAt (d : ℝ) (t : ℝ≥0) : Measurable (gapAt d t) :=
  (measurable_pastGap d t).comp (by fun_prop)
theorem measurable_futureAt (d : ℝ) (t : ℝ≥0) : Measurable (futureAt d t) :=
  (measurable_maximum d).comp (by fun_prop)

theorem selector_upper_path {B : ℝ → ℝ} {d x : ℝ} {t : ℝ≥0}
    (hc : Continuous (fun u : ℝ≥0 => B (u:ℝ)))
    (hf : maximumE d (fun u : ℝ≥0 => B ((t+u : ℝ≥0):ℝ)-B t) ≠ ⊤)
    (hm : ∀ s : ℝ, B s-d*|s| ≤ B x-d*|x|) (hx : t < x) :
    gapAt d t (fun u => B u) ≤ futureAt d t (fun u => B u) := by
  let f (u : ℝ≥0) := B (u:ℝ)
  have hc' : Continuous (fun u : Iic t => f u.val) := hc.comp continuous_subtype_val
  obtain ⟨s,hs,_⟩ := pastGap_isMax d t _ hc'
  let v : ℝ≥0 := ⟨x-t, by linarith⟩
  have he : ((t+v : ℝ≥0):ℝ) = x := by change (t:ℝ)+(x-t)=x; ring
  have hcf : Continuous (fun u => f (t+u)-f t) := (hc.comp (continuous_const.add continuous_id)).sub continuous_const
  have hh := le_maximum hcf d hf v
  change B ((t+v:ℝ≥0):ℝ)-B t-d*(x-t) ≤ futureAt d t _ at hh
  rw [he] at hh
  have hp := hm (s.val:ℝ)
  simp only [NNReal.abs_eq, abs_of_nonneg (t.property.trans hx.le)] at hp
  change pastGap d t _ ≤ _
  rw [hs]
  dsimp only [f]
  linarith

theorem selector_lower_path {B : ℝ → ℝ} {d x : ℝ} {t : ℝ≥0}
    (hc : Continuous (fun u : ℝ≥0 => B (u:ℝ)))
    (hl : Continuous (fun u : ℝ≥0 => B (-(u:ℝ))))
    (h₀ : B 0 = 0)
    (hf : maximumE d (fun u : ℝ≥0 => B ((t+u : ℝ≥0):ℝ)-B t) ≠ ⊤)
    (ho : maximumE d (fun u : ℝ≥0 => B (-(u:ℝ))) ≠ ⊤)
    (hm : ∀ s : ℝ, B s-d*|s| ≤ B x-d*|x|)
    (hop : maximum d (fun u : ℝ≥0 => B (-(u:ℝ))) ≤ 1)
    (hwin : gapAt d t (fun u => B u) + 1 < futureAt d t (fun u => B u)) : (t:ℝ) < x := by
  let f (u : ℝ≥0) := B (u:ℝ)
  have hc' : Continuous (fun u : Iic t => f u.val) := hc.comp continuous_subtype_val
  obtain ⟨_,_,hs⟩ := pastGap_isMax d t _ hc'
  have hcf : Continuous (fun u => f (t+u)-f t) := (hc.comp (continuous_const.add continuous_id)).sub continuous_const
  have hg : 0 ≤ gapAt d t f := ENNReal.toReal_nonneg
  obtain ⟨v,hv⟩ := (maximum_gt_iff hcf d hf (show 0 ≤ gapAt d t f + 1 by linarith)).mp hwin
  have hglobal := hm ((t+v:ℝ≥0):ℝ)
  simp only [NNReal.abs_eq] at hglobal
  change gapAt d t f + 1 < B ((t+v:ℝ≥0):ℝ)-B t-d*(v:ℝ) at hv
  simp only [NNReal.coe_add] at hv hglobal
  by_contra! hx
  by_cases hn : 0 ≤ x
  · let u : ℝ≥0 := ⟨x,hn⟩
    have h := hs ⟨u,hx⟩
    change B x-d*x-(B t-d*(t:ℝ)) ≤ gapAt d t f at h
    rw [abs_of_nonneg hn] at hglobal
    linarith
  · let u : ℝ≥0 := ⟨-x,by linarith⟩
    have hneg := (le_maximum hl d ho u).trans hop
    change B (- -x)-d*(-x) ≤ 1 at hneg
    rw [neg_neg] at hneg
    have h := hs ⟨0,by simp⟩
    change B 0-d*0-(B t-d*(t:ℝ)) ≤ gapAt d t f at h
    rw [h₀] at h
    rw [abs_of_neg (lt_of_not_ge hn)] at hglobal
    linarith

end
end BrownianComparison
end

-- BrownianArmsProbability
section
open MeasureTheory ProbabilityTheory Set Real TopologicalSpace
open scoped ENNReal NNReal
namespace BrownianComparison
open BrownianContinuous OMA.S_mo_142880
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem gapAt_aemeasurable {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (d : ℝ) (t : ℝ≥0) :
    AEMeasurable (fun ω => gapAt d t (fun u => B u ω)) P := by
  apply ENNReal.measurable_toReal.comp_aemeasurable
  change AEMeasurable (fun ω => ⨆ n : ℕ, ENNReal.ofReal _) P
  exact AEMeasurable.iSup fun n => ENNReal.measurable_ofReal.comp_aemeasurable
    (((hB.aemeasurable _).sub aemeasurable_const).sub ((hB.aemeasurable _).sub aemeasurable_const))

theorem gapAt_indep_futureAt {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (d : ℝ) (t : ℝ≥0) :
    IndepFun (fun ω => gapAt d t (fun u => B u ω)) (fun ω => futureAt d t (fun u => B u ω)) P :=
  (hB.indepFun_shift t).symm.comp (measurable_pastGap d t) (measurable_maximum d)

theorem selector_probability_sandwich (B : ℝ → Ω → ℝ) (d : ℝ) (hd : 0 < d) (t : ℝ≥0)
    (hR : IsBrownianReal (fun u : ℝ≥0 => B (u:ℝ)) P)
    (hL : IsBrownianReal (fun u : ℝ≥0 => B (-(u:ℝ))) P)
    (hi : IndepFun (fun ω (u:ℝ≥0) => B (u:ℝ) ω) (fun ω (u:ℝ≥0) => B (-(u:ℝ)) ω) P)
    (T : Ω → ℝ) (hT : ∀ᵐ ω ∂P, ∀ s : ℝ, height B d s ω ≤ height B d (T ω) ω) :
    let G := fun ω => gapAt d t (fun u => B (u:ℝ) ω)
    let F := fun ω => futureAt d t (fun u => B (u:ℝ) ω)
    P.real {ω | G ω + 1 < F ω} * (1-exp (-(2*d))) ≤ P.real {ω | (t:ℝ) < T ω} ∧
    P.real {ω | (t:ℝ) < T ω} ≤ P.real {ω | G ω ≤ F ω} := by
  let R (ω : Ω) (u : ℝ≥0) := B (u:ℝ) ω
  let L (ω : Ω) (u : ℝ≥0) := B (-(u:ℝ)) ω
  let A := {f : ℝ≥0 → ℝ | gapAt d t f + 1 < futureAt d t f}
  let H := {f : ℝ≥0 → ℝ | maximum d f ≤ 1}
  have hA : MeasurableSet A := measurableSet_lt ((measurable_gapAt d t).add measurable_const) (measurable_futureAt d t)
  have hH : MeasurableSet H := measurableSet_le (measurable_maximum d) measurable_const
  have hprod : P (R ⁻¹' A ∩ L ⁻¹' H) = P (R ⁻¹' A)*P (L ⁻¹' H) := hi.measure_inter_preimage_eq_mul A H hA hH
  have hmass : P.real (L ⁻¹' H) = 1-exp (-(2*d)) := by
    have he := (hasLaw_maximum hL hd).measureReal_eq (p := (· ≤ (1:ℝ))) measurableSet_Iic
    letI : IsProbabilityMeasure (expMeasure (2*d)) := isProbabilityMeasure_expMeasure (by positivity)
    have hh := cdf_expMeasure_eq (show 0<2*d by positivity) 1
    rw [cdf_eq_real] at hh
    change (expMeasure (2*d)).real (Iic 1) = _ at hh
    exact he.trans (show (expMeasure (2*d)).real (Iic 1) = _ by simpa using hh)
  have hu : {ω | (t:ℝ) < T ω} ≤ᵐ[P] {ω | gapAt d t (R ω) ≤ futureAt d t (R ω)} := by
    filter_upwards [hR.cont, maximumE_finite (hR.shift t) hd, hT] with ω hc hf hm hx
    exact selector_upper_path (B := fun s => B s ω) (d := d) (t := t) (x := T ω) hc hf hm hx
  have hl : (R ⁻¹' A ∩ L ⁻¹' H : Set Ω) ≤ᵐ[P] {ω | (t:ℝ) < T ω} := by
    filter_upwards [hR.cont,hL.cont,hR.eval_zero_ae_eq_zero,maximumE_finite (hR.shift t) hd,
      maximumE_finite hL hd,hT] with ω hc hcl h₀ hf ho hm hw
    exact selector_lower_path (B := fun s => B s ω) (d := d) (t := t) (x := T ω) hc hcl h₀ hf ho hm hw.2 hw.1
  constructor
  · change P.real (R ⁻¹' A) * _ ≤ _
    rw [← hmass, measureReal_def, measureReal_def, ← ENNReal.toReal_mul, ← hprod]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hl)
  · exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hu)

end
end BrownianComparison
end

-- BrownianContinuousReflection
section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace BrownianContinuous
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- Reflecting the endpoint about the current position leaves its joint law
with any countable family of past evaluations unchanged. -/
theorem reflect_endpoint {ι : Type*} [Countable ι] (hB : IsPreBrownianReal B P)
    (s r : ℝ≥0) (times : ι → Iic s) (o : ι) (ho : (times o:ℝ≥0) = s) :
    IdentDistrib (fun ω => (fun i => B (times i) ω, B (s+r) ω))
      (fun ω => (fun i => B (times i) ω, 2*B s ω - B (s+r) ω)) P P := by
  let X := fun ω (i:ι) => B (times i) ω
  let Y := fun ω => B (s+r) ω - B s ω
  have hx : AEMeasurable X P := aemeasurable_pi_lambda _ (fun i => hB.aemeasurable (times i))
  have hy : HasLaw Y (gaussianReal 0 r) P := (hB.shift s).hasLaw_eval r
  have hneg : HasLaw (-Y) (gaussianReal 0 r) P := by simpa using gaussianReal_neg hy
  have hsym : IdentDistrib Y (-Y) P P :=
    ⟨hy.aemeasurable,hneg.aemeasurable,hy.map_eq.trans hneg.map_eq.symm⟩
  have hind : IndepFun X Y P := (hB.indepFun_shift s).symm.comp
    (show Measurable (fun f : Iic s → ℝ => fun i => f (times i)) by fun_prop)
    (measurable_pi_apply r)
  have hprod := (IdentDistrib.refl hx).prodMk hsym hind (hind.comp measurable_id measurable_neg)
  let F : ((ι → ℝ) × ℝ) → ((ι → ℝ) × ℝ) := fun v => (v.1,v.1 o+v.2)
  have h := hprod.comp (show Measurable F by dsimp [F]; fun_prop)
  convert h using 1
  · ext ω
    · rfl
    · change B (s+r) ω = B (times o) ω + (B (s+r) ω - B s ω)
      rw [ho]; ring
  · ext ω
    · rfl
    · change 2*B s ω-B (s+r) ω = B (times o) ω + -(B (s+r) ω - B s ω)
      rw [ho]; ring

/-- Endpoint reflection on the event the grid first exceeds the level at a given index. -/
theorem reflected_first_crossing (hB : IsPreBrownianReal B P) (t : ℕ → ℝ≥0)
    (ht : Monotone t) {k N : ℕ} (hk : k ≤ N) (m : ℝ) (E : Set ℝ) (hE : MeasurableSet E) :
    P {ω | (∀ j < k, B (t j) ω ≤ m) ∧ m < B (t k) ω ∧ B (t N) ω ∈ E} =
      P {ω | (∀ j < k, B (t j) ω ≤ m) ∧ m < B (t k) ω ∧ 2*B (t k) ω-B (t N) ω ∈ E} := by
  let tt : Fin (k+1) → Iic (t k) := fun j => ⟨t j,ht (Nat.le_of_lt_succ j.isLt)⟩
  have h := reflect_endpoint hB (t k) (t N-t k) tt (Fin.last k) rfl
  rw [add_tsub_cancel_of_le (ht hk)] at h
  let G := {v : (Fin (k+1) → ℝ) × ℝ | (∀ j : Fin k, v.1 j.castSucc ≤ m) ∧ m < v.1 (Fin.last k) ∧ v.2 ∈ E}
  have hG : MeasurableSet G := by
    have h1 : MeasurableSet {v : (Fin (k+1) → ℝ) × ℝ | ∀ j : Fin k, v.1 j.castSucc ≤ m} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun j => measurableSet_le ((measurable_pi_apply j.castSucc).comp measurable_fst) measurable_const)
    have h2 : MeasurableSet {v : (Fin (k+1) → ℝ) × ℝ | m < v.1 (Fin.last k)} :=
      measurableSet_lt measurable_const ((measurable_pi_apply _).comp measurable_fst)
    exact h1.inter (h2.inter (measurable_snd hE))
  have heq := h.measure_mem_eq hG
  have hpred (ω : Ω) : (∀ j : Fin k, B (tt j.castSucc) ω ≤ m) ↔ (∀ j < k, B (t j) ω ≤ m) :=
    ⟨fun h j hj => h ⟨j,hj⟩, fun h j => h j j.isLt⟩
  convert heq using 2 <;> ext ω <;> simp only [mem_ofPred_eq, G, Set.mem_preimage, hpred] <;> rfl

end BrownianContinuous
end

-- BrownianContinuousGridReflection
section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace BrownianContinuous
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

def firstAt (v : ℕ → Ω → ℝ) (m : ℝ) (k : ℕ) :=
  {ω | (∀ j < k, v j ω ≤ m) ∧ m < v k ω}

private theorem exists_firstAt (v : ℕ → Ω → ℝ) (m : ℝ) (N : ℕ) (ω : Ω)
    (h : ∃ j ≤ N, m < v j ω) : ∃ k ≤ N, ω ∈ firstAt v m k := by
  classical
  obtain ⟨j,hj,hv⟩ := h
  have hex : ∃ j,m < v j ω := ⟨j,hv⟩
  refine ⟨Nat.find hex,(Nat.find_min' hex hv).trans hj, ?_, Nat.find_spec hex⟩
  intro i hi
  exact le_of_not_gt (Nat.find_min hex hi)

private theorem firstAt_m (v : ℕ → Ω → ℝ) (hv : ∀ k, AEMeasurable (v k) P) (m : ℝ) (k : ℕ) :
    NullMeasurableSet (firstAt v m k) P := by
  have heq : firstAt v m k = (⋂ j : Fin k, {ω | v j ω ≤ m}) ∩ {ω | m < v k ω} := by
    ext ω
    simp only [firstAt,mem_ofPred_eq, mem_inter_iff, mem_iInter, Fin.forall_iff]
  rw [heq]
  exact (NullMeasurableSet.iInter (fun j : Fin k => nullMeasurableSet_le (hv j) aemeasurable_const)).inter
    (nullMeasurableSet_lt aemeasurable_const (hv k))

private theorem firstAt_disjoint (v : ℕ → Ω → ℝ) (m : ℝ) {k j : ℕ} (h : k ≠ j) :
    Disjoint (firstAt v m k) (firstAt v m j) := by
  apply disjoint_left.mpr
  intro ω hk hj
  rcases lt_or_gt_of_ne h with hlt|hgt
  · exact hk.2.not_ge (hj.1 k hlt)
  · exact hj.2.not_ge (hk.1 j hgt)

theorem reflect_grid (hB : IsPreBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (m : ℝ) (N : ℕ) (E : Set ℝ) (hE : MeasurableSet E) :
    P {ω | (∃ j ≤ N, m < B (t j) ω) ∧ B (t N) ω ∈ E} =
      P {ω | ∃ k ≤ N, ω ∈ firstAt (B ∘ t) m k ∧ 2*B (t k) ω - B (t N) ω ∈ E} := by
  let S := Finset.range (N+1)
  let A (k:ℕ) := firstAt (B ∘ t) m k ∩ (B (t N) ⁻¹' E)
  let C (k:ℕ) := firstAt (B ∘ t) m k ∩ ((fun ω => 2*B (t k) ω - B (t N) ω) ⁻¹' E)
  have ha : {ω | (∃ j ≤ N, m < B (t j) ω) ∧ B (t N) ω ∈ E} = ⋃ k ∈ S,A k := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, S, Finset.mem_range, Nat.lt_succ_iff, A, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hj,he⟩
      obtain ⟨k,hk,hcur⟩ := exists_firstAt (B ∘ t) m N ω hj
      exact ⟨k,hk,hcur,he⟩
    · rintro ⟨k,hk,hfirst,he⟩
      exact ⟨⟨k,hk,hfirst.2⟩,he⟩
  have hc : {ω | ∃ k ≤ N, ω ∈ firstAt (B ∘ t) m k ∧ 2*B (t k) ω - B (t N) ω ∈ E} = ⋃ k ∈ S,C k := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, S,Finset.mem_range, Nat.lt_succ_iff, C,mem_inter_iff,mem_preimage, exists_prop]
  have hm := firstAt_m (B ∘ t) (fun k => hB.aemeasurable (t k)) m
  have hmA (k : ℕ) : NullMeasurableSet (A k) P :=
    (hm k).inter ((hB.aemeasurable (t N)).nullMeasurable hE)
  have hmC (k : ℕ) : NullMeasurableSet (C k) P :=
    (hm k).inter (((aemeasurable_const.mul (hB.aemeasurable (t k))).sub (hB.aemeasurable (t N))).nullMeasurable hE)
  rw [ha,hc,measure_biUnion_finset₀ (fun i _ j _ hij =>
    ((firstAt_disjoint (B ∘ t) m hij).mono inter_subset_left inter_subset_left).aedisjoint) (fun k _ => hmA k),
    measure_biUnion_finset₀ (fun i _ j _ hij =>
    ((firstAt_disjoint (B ∘ t) m hij).mono inter_subset_left inter_subset_left).aedisjoint) (fun k _ => hmC k)]
  apply Finset.sum_congr rfl
  intro k hk
  have he := reflected_first_crossing hB t ht (by simpa [S] using hk : k ≤ N) m E hE
  convert he using 2 <;> ext ω <;> simp only [A,C,firstAt,mem_inter_iff,mem_preimage,mem_ofPred_eq,Function.comp_apply] <;> tauto

end BrownianContinuous
end

-- BrownianContinuousBarrierReflection
section
open MeasureTheory ProbabilityTheory Set Real Filter TopologicalSpace
open scoped NNReal ENNReal Topology

namespace BrownianContinuous
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- Upper half of the reflection identity on an arbitrary finite observation grid. -/
theorem grid_reflection_upper (hB : IsPreBrownianReal B P) (t : ℕ → ℝ≥0)
    (ht : Monotone t) (m y : ℝ) (N : ℕ) :
    P {ω | (∃ j ≤ N, m < B (t j) ω) ∧ B (t N) ω < y} ≤ P {ω | 2*m-y < B (t N) ω} := by
  have h := reflect_grid hB t ht m N (Iio y) measurableSet_Iio
  apply h.le.trans
  apply measure_mono
  rintro ω ⟨k,_,hfirst,hterm⟩
  have hgt := hfirst.2
  change m < B (t k) ω at hgt
  change 2*B (t k) ω-B (t N) ω < y at hterm
  change 2*m-y < B (t N) ω
  linarith

/-- A finite dense sample of the past can be sorted and completed by its terminal time. -/
theorem dense_reflection_upper (hB : IsBrownianReal B P) (T : ℝ≥0) (m y : ℝ) :
    P {ω | (∃ t ≤ T, m < B t ω) ∧ B T ω < y} ≤ P {ω | 2*m-y < B T ω} := by
  let v := denseSeq (Iic T)
  let E (N : ℕ) := {ω | (∃ j ≤ N, m < B (v j) ω) ∧ B T ω < y}
  have hm : Monotone E := by
    intro i j hij ω
    rintro ⟨⟨k,hk,hlt⟩,he⟩
    exact ⟨⟨k,hk.trans hij,hlt⟩,he⟩
  apply le_trans (b := P (⋃ n, E n))
  · apply measure_mono_ae
    filter_upwards [hB.cont] with ω hω
    rintro ⟨⟨t,ht,hm⟩,hy⟩
    have hc : Continuous (fun u : Iic T => B u ω) := hω.comp continuous_subtype_val
    have ⟨i,hi⟩ := (denseRange_denseSeq (Iic T)).exists_mem_open
      (hc.isOpen_preimage (Ioi m) isOpen_Ioi) ⟨⟨t,ht⟩,hm⟩
    exact mem_iUnion.mpr ⟨i,⟨i,le_rfl,hi⟩,hy⟩
  rw [hm.measure_iUnion]
  apply iSup_le
  intro N
  let f : Fin (N+1) → ℝ≥0 := fun i => v i
  let grid (k : ℕ) : ℝ≥0 := if h : k ≤ N then f (Tuple.sort f ⟨k,by omega⟩) else T
  have hgrid : Monotone grid := by
    intro i j hij
    by_cases hj : j ≤ N
    · have hi := hij.trans hj
      simpa [grid,hi,hj] using (Tuple.monotone_sort f) (a:=⟨i,by omega⟩) (b:=⟨j,by omega⟩) hij
    · simp [grid,hj]
      split <;> first | exact (v _).property | rfl
  have hl := grid_reflection_upper hB.toIsPreBrownianReal grid hgrid m y (N+1)
  have hlast : grid (N+1) = T := by simp [grid]
  rw [hlast] at hl
  apply le_trans (measure_mono ?_) hl
  rintro ω ⟨⟨j,hj,hm⟩,hy⟩
  let k := (Tuple.sort f).symm ⟨j,by omega⟩
  have hk : (k:ℕ) ≤ N := Nat.le_of_lt_succ k.isLt
  refine ⟨⟨k,hk.trans (Nat.le_succ _),?_⟩,hy⟩
  simpa [grid,hk,k,f,v] using hm

end BrownianContinuous
end

-- BrownianContinuousReflectionLaw
section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal Topology

namespace BrownianContinuous
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- A uniform mesh approximates endpoint reflection with an explicit Gaussian error. -/
theorem reflection_lower_mesh (hB : IsPreBrownianReal B P) (u : ℝ≥0) (N : ℕ)
    {m y e r : ℝ} (hm : 0 ≤ m) (hy : y ≤ m) (he : 0 < e) (hr : 0 ≤ r) :
    P.real {ω | 2*m-y+2*e < B (N*u) ω} ≤
      P.real {ω | (∃ t ≤ (N:ℝ≥0)*u, m < B t ω) ∧ B (N*u) ω < y} +
        N*exp (-(r*e)+(u:ℝ)*r^2/2) := by
  classical
  let t (k:ℕ) : ℝ≥0 := k*u
  have ht : Monotone t := fun i j h => mul_le_mul_of_nonneg_right (show (i:ℝ≥0) ≤ (j:ℝ≥0) by exact_mod_cast h) (show (0:ℝ≥0) ≤ u by positivity)
  let A := {ω | ∃ k ≤ N, ω ∈ firstAt (B ∘ t) m k ∧ 2*B (t k) ω-B (t N) ω < y}
  let G (i:ℕ) := {ω | e ≤ B (t (i+1)) ω - B (t i) ω}
  have hcover : P.real {ω | 2*m-y+2*e < B (N*u) ω} ≤ P.real (A ∪ ⋃ i ∈ Finset.range N,G i) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hzero
    intro hlast
    change 2*m-y+2*e < B (t N) ω at hlast
    have hevent : ∃ i, m < B (t i) ω := ⟨N,by linarith⟩
    let k := Nat.find hevent
    have hk : k ≤ N := Nat.find_min' hevent (by linarith : m < B (t N) ω)
    have hhigh : m < B (t k) ω := Nat.find_spec hevent
    have hfirst : ω ∈ firstAt (B ∘ t) m k :=
      ⟨fun j hj => le_of_not_gt (Nat.find_min hevent hj),hhigh⟩
    by_cases hclose : B (t k) ω ≤ m+e
    · exact Or.inl ⟨k,hk,hfirst,by linarith⟩
    · right
      have hk0 : k ≠ 0 := by
        intro h
        rw [h] at hhigh
        simp [t,hzero] at hhigh
        linarith
      obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hprev := hfirst.1 j (by omega)
      refine mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨by simp; omega,?_⟩⟩
      change e ≤ B (t (j+1)) ω - B (t j) ω
      change B (t j) ω ≤ m at hprev
      rw [show j+1 = k from hj.symm]
      linarith
  have hA : P.real A ≤ P.real {ω | (∃ s ≤ (N:ℝ≥0)*u, m < B s ω) ∧ B (N*u) ω < y} := by
    have hrfl := reflect_grid hB t ht m N (Iio y) measurableSet_Iio
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    rw [show P A = _ from hrfl.symm]
    apply measure_mono
    rintro ω ⟨⟨j,hj,hv⟩,hend⟩
    exact ⟨⟨t j,ht hj,hv⟩,hend⟩
  have hG (i : ℕ) : P.real (G i) ≤ exp (-(r*e)+(u:ℝ)*r^2/2) := by
    let X := fun ω => B (t (i+1)) ω - B (t i) ω
    have hnext : t (i+1) = t i+u := by simp [t,add_mul]
    have hlaw : HasLaw X (gaussianReal 0 u) P := by
      dsimp [X]
      rw [hnext]
      exact ((hB.shift (t i)).hasLaw_eval u)
    have hmgf := mgf_gaussianReal hlaw.map_eq r
    have hint : Integrable (fun ω => exp (r*X ω)) P := (mgf_pos_iff).mp (hmgf ▸ exp_pos _)
    calc
      _ ≤ _ := measure_ge_le_exp_mul_mgf e hr hint
      _ = _ := by rw [hmgf,← exp_add]; congr 1; ring
  apply hcover.trans
  apply (measureReal_union_le _ _).trans
  apply add_le_add hA
  apply (measureReal_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ _i ∈ Finset.range N, exp (-(r*e)+(u:ℝ)*r^2/2) := Finset.sum_le_sum (fun i _ => hG i)
    _ = _ := by simp

/-- Reflection principle in its joint running-maximum and endpoint form. -/
theorem barrier_reflection (hB : IsBrownianReal B P) (T : ℝ≥0) {m y : ℝ}
    (hm : 0 ≤ m) (hy : y ≤ m) :
    P {ω | (∃ t ≤ T, m < B t ω) ∧ B T ω < y} = P {ω | 2*m-y < B T ω} := by
  apply le_antisymm (dense_reflection_upper hB T m y)
  let p := P.real {ω | (∃ t ≤ T, m < B t ω) ∧ B T ω < y}
  have hlow (e : ℝ) (he : 0 < e) : P.real {ω | 2*m-y+2*e < B T ω} ≤ p := by
    have hseq (k : ℕ) (hk : 1 ≤ k) :
        P.real {ω | 2*m-y+2*e < B T ω} ≤ p + exp ((T:ℝ)/2)*((k:ℝ)^2 * exp (-e*k)) := by
      have hk' : (0:ℝ≥0) < k := by exact_mod_cast (show 0 < k by omega)
      let u : ℝ≥0 := T / (k:ℝ≥0)^2
      have hh := reflection_lower_mesh hB.toIsPreBrownianReal u (k^2) hm hy he (r:=(k:ℝ)) (by positivity)
      simp only [Nat.cast_pow] at hh
      have heq : (k:ℝ≥0)^2*u = T := by dsimp [u]; field_simp
      rw [heq] at hh
      apply hh.trans_eq
      dsimp [p,u]
      push_cast
      have ht : (T:ℝ)/(k:ℝ)^2*(k:ℝ)^2 = T := by field_simp
      rw [ht, exp_add]
      ring_nf
    have htail : Tendsto (fun k : ℕ => (k:ℝ)^2 * exp (-e*k)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 e he).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
      simpa [Function.comp_def] using h
    have hlim : Tendsto (fun k : ℕ => p + exp ((T:ℝ)/2)*((k:ℝ)^2*exp (-e*k))) atTop (𝓝 p) := by
      simpa using (htail.const_mul (exp ((T:ℝ)/2))).const_add p
    exact ge_of_tendsto hlim (eventually_atTop.2 ⟨1,hseq⟩)
  let E (n : ℕ) := {ω | 2*m-y+2*((n:ℝ)+1)⁻¹ < B T ω}
  have hmono : Monotone E := by
    intro i j hij ω hi
    change 2*m-y+2*((i:ℝ)+1)⁻¹ < B T ω at hi
    change 2*m-y+2*((j:ℝ)+1)⁻¹ < B T ω
    apply lt_of_le_of_lt _ hi
    gcongr
  have hset : {ω | 2*m-y < B T ω} = ⋃ n,E n := by
    ext ω
    constructor
    · intro h
      change 2*m-y < B T ω at h
      obtain ⟨n,hn⟩ := exists_nat_one_div_lt (show 0 < (B T ω-(2*m-y))/2 by linarith)
      refine mem_iUnion.mpr ⟨n,?_⟩
      change 2*m-y+2*((n:ℝ)+1)⁻¹ < B T ω
      rw [one_div] at hn
      linarith
    · intro h
      obtain ⟨n,hn⟩ := mem_iUnion.mp h
      change 2*m-y+2*((n:ℝ)+1)⁻¹ < B T ω at hn
      change 2*m-y < B T ω
      linarith [inv_pos.mpr (show 0 < (n:ℝ)+1 by positivity)]
  rw [hset,hmono.measure_iUnion]
  apply iSup_le
  intro n
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp (hlow _ (inv_pos.mpr (by positivity)))

end BrownianContinuous
end

-- BrownianContinuousBridge
section
open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

namespace BrownianContinuous
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- Centering Brownian paths by their linear interpolation to the endpoint creates an
independent bridge. This is the finite-horizon change-of-drift construction. -/
theorem bridge_independent {ι : Type*} (hB : IsPreBrownianReal B P) {T : ℝ≥0} (hT : 0 < T)
    (s : ι → Iic T) :
    IndepFun (fun ω i => B (s i) ω - ((s i : ℝ≥0):ℝ)/T*B T ω) (B T) P := by
  let X (i:ι) (ω:Ω) := B (s i) ω - ((s i : ℝ≥0):ℝ)/T*B T ω
  let Y (_:Unit) (ω:Ω) := B T ω
  have joint : IsGaussianProcess (Sum.elim X Y) P := by
    apply hB.isGaussianProcess.of_isGaussianProcess
    rintro (i | u)
    · refine ⟨{(s i:ℝ≥0),T}, { toFun := fun v => v ⟨s i,by simp⟩-((s i : ℝ≥0):ℝ)/T*v ⟨T,by simp⟩
                               map_add' := by intro a b; simp; ring
                               map_smul' := by intro c v; simp; ring },by simp [X]⟩
    · exact ⟨{T},{toFun := fun v => v ⟨T,by simp⟩
                  map_add' := by simp
                  map_smul' := by simp},by simp [Y]⟩
  have mx (i : ι) : AEMeasurable (X i) P := (hB.aemeasurable _).sub (aemeasurable_const.mul (hB.aemeasurable T))
  have my (u : Unit) : AEMeasurable (Y u) P := hB.aemeasurable T
  have hind := joint.indepFun_of_covariance_eq_zero mx my (fun i _ => ?_)
  · exact hind.comp measurable_id (measurable_pi_apply ())
  · dsimp [X,Y]
    rw [covariance_fun_sub_left, covariance_const_mul_left, hB.covariance_fun_eval, hB.covariance_fun_eval]
    · rw [min_self,min_eq_left]
      · field_simp <;> ring
      · exact_mod_cast (s i).property
    · exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    · exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.const_mul _
    · exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

/-- Density of constant drift relative to a centered terminal Gaussian. -/
noncomputable def driftDensity (c : ℝ) (T : ℝ≥0) (y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (exp (c*y-c^2*T/2))

theorem gaussian_drift_measure (c : ℝ) {T : ℝ≥0} (hT : 0 < T) :
    gaussianReal (c*T) T = (gaussianReal 0 T).withDensity (driftDensity c T) := by
  rw [gaussianReal_of_var_ne_zero _ hT.ne', gaussianReal_of_var_ne_zero _ hT.ne',
    ← withDensity_mul _ (measurable_gaussianPDF _ _)
      (show Measurable (driftDensity c T) by unfold driftDensity; fun_prop)]
  congr 1
  ext y
  unfold gaussianPDF driftDensity
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal,sub_zero,mul_assoc,←exp_add]
  congr 2
  have ht : (T:ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp
  ring

end BrownianContinuous
end

-- BrownianContinuousDrift
section
open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

namespace BrownianContinuous
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- Finite-horizon Cameron–Martin formula for a constant drift. Any measurable
functional of countably many observations of the path and its endpoint is allowed. -/
theorem drift_lintegral {ι : Type*} [Countable ι] (hB : IsPreBrownianReal B P) {T : ℝ≥0}
    (hT : 0 < T) (s : ι → Iic T) (c : ℝ) {G : ((ι → ℝ) × ℝ) → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ ω, G (fun i => B (s i) ω+c*((s i : ℝ≥0):ℝ), B T ω+c*T) ∂P) =
      ∫⁻ ω, driftDensity c T (B T ω) * G (fun i => B (s i) ω, B T ω) ∂P := by
  let X := fun ω (i:ι) => B (s i) ω-((s i:ℝ≥0):ℝ)/T*B T ω
  have mX : AEMeasurable X P := aemeasurable_pi_lambda _ (fun i =>
    (hB.aemeasurable _).sub (aemeasurable_const.mul (hB.aemeasurable T)))
  have hX : HasLaw X (P.map X) P := ⟨mX,rfl⟩
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map mX
  have hind : IndepFun X (B T) P := bridge_independent hB hT s
  have hbase := hind.hasLaw_prod hX (hB.hasLaw_eval T)
  have hshift : HasLaw (fun ω => B T ω+c*T) (gaussianReal (c*T) T) P := by
    simpa only [zero_add] using gaussianReal_add_const (hB.hasLaw_eval T) (c*T)
  have hshiftInd : IndepFun X (fun ω => B T ω + c*T) P :=
    hind.comp measurable_id (show Measurable (fun x:ℝ => x+c*T) by fun_prop)
  have hdrift := hshiftInd.hasLaw_prod hX hshift
  let F (v : (ι → ℝ) × ℝ) := G (fun i => v.1 i+((s i:ℝ≥0):ℝ)/T*v.2, v.2)
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hw : Measurable (driftDensity c T) := by unfold driftDensity; fun_prop
  let H (v : (ι → ℝ) × ℝ) := driftDensity c T v.2 * F v
  have hH : Measurable H := (hw.comp measurable_snd).mul hF
  have horig (ω : Ω) : F (X ω,B T ω) = G (fun i => B (s i) ω,B T ω) := by
    unfold F X
    simp
  have htilt (ω : Ω) : F (X ω,B T ω+c*T) =
      G (fun i => B (s i) ω+c*((s i:ℝ≥0):ℝ),B T ω+c*T) := by
    unfold F X
    congr 2
    funext i
    have ht' : (T:ℝ) ≠ 0 := by exact_mod_cast hT.ne'
    field_simp
    ring
  calc
    _ = ∫⁻ ω, F (X ω,B T ω+c*T) ∂P := lintegral_congr (fun ω => (htilt ω).symm)
    _ = ∫⁻ v, F v ∂(P.map X).prod (gaussianReal (c*T) T) := hdrift.lintegral_comp hF.aemeasurable
    _ = ∫⁻ v, H v ∂(P.map X).prod (gaussianReal 0 T) := by
      rw [gaussian_drift_measure c hT, prod_withDensity_right hw]
      exact lintegral_withDensity_eq_lintegral_mul _ (hw.comp measurable_snd) hF
    _ = ∫⁻ ω, H (X ω,B T ω) ∂P := (hbase.lintegral_comp hH.aemeasurable).symm
    _ = _ := lintegral_congr (fun ω => congrArg (driftDensity c T (B T ω) * ·) (horig ω))

end BrownianContinuous
end

-- BrownianContinuousDriftReflection
section
open MeasureTheory ProbabilityTheory Set Real TopologicalSpace
open scoped NNReal ENNReal Topology

namespace BrownianContinuous
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- Restricting to crossings whose endpoint lies below a fixed barrier gives,
upon reflection, an ordinary Gaussian upper-tail measure. -/
theorem reflected_endpoint_measure (hB : IsBrownianReal B P) {T : ℝ≥0} (hT : 0 < T)
    {m y : ℝ} (hm : 0 ≤ m) (hy : y ≤ m) :
    (P.restrict {ω | (∃ t ≤ T, m < B t ω) ∧ B T ω < y}).map (B T) =
      (P.restrict {ω | 2*m-y < B T ω}).map (fun ω => 2*m-B T ω) := by
  let L := {ω | (∃ t ≤ T, m < B t ω) ∧ B T ω < y}
  let R := {ω | 2*m-y < B T ω}
  have hb := hB.aemeasurable T
  have hr : AEMeasurable (fun ω => 2*m-B T ω) P := aemeasurable_const.sub hb
  have hn (x : ℝ) : ∀ᵐ ω ∂P, B T ω ≠ x := by
    rw [ae_iff]
    simp only [not_not]
    have : NullSingletonClass (gaussianReal 0 T) := nullSingletonClass_gaussianReal hT.ne'
    rw [(hB.hasLaw_eval T).measure_eq (p:=fun v => v=x) (measurableSet_singleton x)]
    exact measure_singleton x
  apply Measure.ext_of_Iic
  intro x
  change (Measure.map (B T) (P.restrict L)) _ = (Measure.map _ (P.restrict R)) _
  rw [Measure.map_apply_of_aemeasurable hb.restrict measurableSet_Iic,
    Measure.map_apply_of_aemeasurable hr.restrict measurableSet_Iic,
    Measure.restrict_apply₀ (hb.restrict.nullMeasurable measurableSet_Iic),
    Measure.restrict_apply₀ (hr.restrict.nullMeasurable measurableSet_Iic)]
  calc
    _ = P {ω | (∃ t ≤ T, m < B t ω) ∧ B T ω < min x y} := by
      apply measure_congr
      filter_upwards [hn x] with ω hh
      apply propext
      change (B T ω ≤ x ∧ ((∃ t ≤ T, m < B t ω) ∧ B T ω < y)) ↔ _
      simp only [mem_ofPred_eq,lt_min_iff]
      exact ⟨fun h => ⟨h.2.1,lt_of_le_of_ne h.1 hh,h.2.2⟩,fun h => ⟨h.2.1.le,h.1,h.2.2⟩⟩
    _ = P {ω | 2*m-min x y < B T ω} := barrier_reflection hB T hm ((min_le_right x y).trans hy)
    _ = _ := by
      apply measure_congr
      filter_upwards [hn (2*m-x)] with ω hh
      apply propext
      change (2*m-min x y < B T ω) ↔ ((2*m-B T ω ≤ x) ∧ 2*m-y < B T ω)
      have he : 2*m-min x y = max (2*m-x) (2*m-y) := by
        rcases le_total x y with hx|hx
        · rw [min_eq_left hx,max_eq_left (by linarith)]
        · rw [min_eq_right hx,max_eq_right (by linarith)]
      rw [he, max_lt_iff]
      constructor <;> rintro ⟨h1,h2⟩
      · exact ⟨by linarith,h2⟩
      · exact ⟨lt_of_le_of_ne (by linarith) hh.symm,h2⟩

/-- Constant drift on a finite-horizon barrier event introduces only the
terminal normal likelihood ratio. -/
theorem drift_crossing (hB : IsBrownianReal B P) {T : ℝ≥0} (hT : 0 < T) (c m y : ℝ) :
    P {ω | (∃ t ≤ T, m < B t ω+c*t) ∧ B T ω+c*T < y} =
      ∫⁻ ω in {ω | (∃ t ≤ T, m < B t ω) ∧ B T ω < y}, driftDensity c T (B T ω) ∂P := by
  let s := denseSeq (Iic T)
  let U := {v : (ℕ → ℝ) × ℝ | (∃ n, m < v.1 n) ∧ v.2 < y}
  have hU : MeasurableSet U := by
    have h1 : MeasurableSet {v : (ℕ → ℝ) × ℝ | ∃ n, m < v.1 n} := by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion (fun n => measurableSet_lt measurable_const ((measurable_pi_apply n).comp measurable_fst))
    exact h1.inter (measurableSet_lt measurable_snd measurable_const)
  let G := U.indicator (fun _ => (1:ℝ≥0∞))
  have hG : Measurable G := measurable_const.indicator hU
  have h := drift_lintegral hB.toIsPreBrownianReal hT s c hG
  let A (b:ℝ) := {ω | (∃ t ≤ T, m < B t ω+b*t) ∧ B T ω+b*T < y}
  let V (b:ℝ) := fun ω => (fun n => B (s n) ω+b*((s n:ℝ≥0):ℝ), B T ω+b*T)
  let E (b:ℝ) := V b ⁻¹' U
  have mV (b:ℝ) : AEMeasurable (V b) P := (aemeasurable_pi_lambda _ (fun n =>
    (hB.aemeasurable _).add aemeasurable_const)).prodMk ((hB.aemeasurable _).add aemeasurable_const)
  have mE (b:ℝ) : NullMeasurableSet (E b) P := (mV b).nullMeasurable hU
  have hdense (b:ℝ) : A b =ᵐ[P] E b := by
    filter_upwards [hB.cont] with ω hw
    apply propext
    change ((∃ t ≤ T, m < B t ω+b*t) ∧ _) ↔ ((∃ n, m < B (s n) ω+b*((s n:ℝ≥0):ℝ)) ∧ _)
    apply and_congr_left
    intro _
    constructor
    · rintro ⟨t,ht,hh⟩
      have hc : Continuous (fun t : Iic T => B t ω+b*((t:ℝ≥0):ℝ)) := by fun_prop
      exact (denseRange_denseSeq (Iic T)).exists_mem_open (hc.isOpen_preimage (Ioi m) isOpen_Ioi) ⟨⟨t,ht⟩,hh⟩
    · rintro ⟨n,hn⟩
      exact ⟨s n,(s n).property,hn⟩
  have hleft (ω : Ω) : G (V c ω) = (E c).indicator (fun _ => (1:ℝ≥0∞)) ω := by
    by_cases h : V c ω ∈ U
    · simp [G,E,h]
    · simp [G,E,h]
  have hright (ω:Ω) : driftDensity c T (B T ω)*G (fun i => B (s i) ω,B T ω) =
      (E 0).indicator (fun ω => driftDensity c T (B T ω)) ω := by
    have heq : (fun i => B (s i) ω,B T ω) = V 0 ω := by simp [V]
    rw [heq]
    by_cases hv : V 0 ω ∈ U <;> simp [G,E,hv]
  change P (A c) = _
  rw [measure_congr (hdense c)]
  calc
    P (E c) = ∫⁻ ω, G (V c ω) ∂P := by simp_rw [hleft]; rw [lintegral_indicator₀ (mE c)]; simp
    _ = _ := h
    _ = ∫⁻ ω in E 0, driftDensity c T (B T ω) ∂P := by simp_rw [hright]; rw [lintegral_indicator₀ (mE 0)]
    _ = _ := by
      rw [← Measure.restrict_congr_set (hdense 0)]
      simp [A]

/-- The drifted reflection formula before differentiating in the barrier.
The right-hand side is a one-dimensional Gaussian integral. -/
theorem drift_barrier_reflection (hB : IsBrownianReal B P) {T : ℝ≥0} (hT : 0 < T)
    (c : ℝ) {m y : ℝ} (hm : 0 ≤ m) (hy : y ≤ m) :
    P {ω | (∃ t ≤ T, m < B t ω+c*t) ∧ B T ω+c*T < y} =
      ∫⁻ w in Ioi (2*m-y), driftDensity c T (2*m-w) ∂(gaussianReal 0 T) := by
  rw [drift_crossing hB hT]
  let L := {ω | (∃ t ≤ T, m < B t ω) ∧ B T ω<y}
  let R := {ω | 2*m-y < B T ω}
  have hw : Measurable (driftDensity c T) := by unfold driftDensity; fun_prop
  have hb := hB.aemeasurable T
  have hr : AEMeasurable (fun ω => 2*m-B T ω) P := aemeasurable_const.sub hb
  have hmeas := reflected_endpoint_measure hB hT hm hy
  calc
    _ = ∫⁻ w, driftDensity c T w ∂(P.restrict L).map (B T) := (lintegral_map' hw.aemeasurable hb.restrict).symm
    _ = ∫⁻ ω in R, driftDensity c T (2*m-B T ω) ∂P := by rw [hmeas]; exact lintegral_map' hw.aemeasurable hr.restrict
    _ = _ := by
      rw [← (hB.hasLaw_eval T).map_eq, Measure.restrict_map_of_aemeasurable hb measurableSet_Ioi]
      exact (lintegral_map' (f:=fun w : ℝ => driftDensity c T (2*m-w)) (hw.comp (measurable_const.sub measurable_id)).aemeasurable hb.restrict).symm

end BrownianContinuous
end

-- BrownianContinuousKilled
section
open MeasureTheory ProbabilityTheory Real Set TopologicalSpace
open scoped NNReal ENNReal Topology

namespace BrownianContinuous
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

def below (B : ℝ≥0 → Ω → ℝ) (c : ℝ) (T : ℝ≥0) (m : ℝ) :=
  {ω | ∀ s ≤ T, B s ω+c*s ≤ m}

theorem nullMeasurable_below (hB : IsBrownianReal B P) (c : ℝ) (T : ℝ≥0) (m : ℝ) :
    NullMeasurableSet (below B c T m) P := by
  let s := denseSeq (Iic T)
  let E := ⋂ n, {ω | B (s n) ω+c*((s n:ℝ≥0):ℝ) ≤ m}
  have hE : NullMeasurableSet E P := NullMeasurableSet.iInter (fun n =>
    nullMeasurableSet_le ((hB.aemeasurable (s n)).add aemeasurable_const) aemeasurable_const)
  apply hE.congr
  filter_upwards [hB.cont] with ω hw
  apply propext
  change ω ∈ E ↔ ω ∈ below B c T m
  simp only [E,mem_iInter,mem_ofPred_eq,below]
  constructor
  · intro hall t ht
    have hc : Continuous (fun u:Iic T => B u ω+c*((u:ℝ≥0):ℝ)) := (hw.comp continuous_subtype_val).add (by fun_prop)
    by_contra! he
    have ⟨i,hi⟩ := (denseRange_denseSeq (Iic T)).exists_mem_open
      (hc.isOpen_preimage (Ioi m) isOpen_Ioi) ⟨⟨t,ht⟩,he⟩
    exact (not_lt_of_ge (hall i)) hi
  · exact fun h n => h (s n) (s n).property

/-- Image method for the probability that the running maximum stays below m. -/
theorem below_integral (hB : IsBrownianReal B P) {T : ℝ≥0} (hT : 0 < T) (c : ℝ)
    {m : ℝ} (hm : 0 ≤ m) :
    P.real (below B c T m) = ∫ w in Iio m,
      gaussianPDFReal (c*T) T w - exp (2*c*m)*gaussianPDFReal (2*m+c*T) T w := by
  let S := below B c T m
  let U := {ω | B T ω+c*T < m}
  let A := {ω | (∃ t ≤ T, m < B t ω+c*t) ∧ B T ω+c*T < m}
  have hlaw : HasLaw (fun ω => B T ω+c*T) (gaussianReal (c*T) T) P := by
    simpa using gaussianReal_add_const (hB.hasLaw_eval T) (c*T)
  have hU : NullMeasurableSet U P := nullMeasurableSet_lt hlaw.aemeasurable aemeasurable_const
  have hAc : A = Sᶜ ∩ U := by ext ω; simp [A,S,below,U]
  have hA : NullMeasurableSet A P := hAc ▸ (nullMeasurable_below hB c T m).compl.inter hU
  have hatom : ∀ᵐ ω ∂P, B T ω+c*T ≠ m := by
    rw [ae_iff]
    simp only [not_not]
    let : NullSingletonClass (gaussianReal (c*T) T) := nullSingletonClass_gaussianReal hT.ne'
    rw [hlaw.measure_eq (p:=fun v => v=m) (measurableSet_singleton m)]
    exact measure_singleton _
  have hdiff : S =ᵐ[P] (U \ A : Set Ω) := by
    filter_upwards [hatom] with ω hw
    apply propext
    change ω ∈ S ↔ ω ∈ U \ A
    rw [hAc,mem_sdiff,mem_inter_iff,mem_compl_iff]
    constructor
    · intro hs
      exact ⟨lt_of_le_of_ne (hs T le_rfl) hw,fun h => h.1 hs⟩
    · exact fun h => Classical.byContradiction (fun hn => h.2 ⟨hn,h.1⟩)
  have hmeas : P S = P U - P A := by
    rw [measure_congr hdiff]
    exact measure_sdiff (show A ⊆ U from fun ω h => h.2) hA (measure_ne_top _ _)
  have hprob : P.real S = P.real U - P.real A := by
    change (P S).toReal = _-_
    rw [hmeas, ENNReal.toReal_sub_of_le (measure_mono (show A ⊆ U from fun ω h => h.2)) (measure_ne_top _ _)]
    rfl
  have hGauss (q:ℝ) : (gaussianReal q T).real (Iio m) = ∫ w in Iio m, gaussianPDFReal q T w := by
    rw [measureReal_def,gaussianReal_apply_eq_integral _ hT.ne', ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg _ _))]
  have hUprob : P.real U = (gaussianReal (c*T) T).real (Iio m) :=
    hlaw.measureReal_eq (p:=fun q => q<m) measurableSet_Iio
  have href := drift_barrier_reflection hB hT c hm le_rfl
  change P A = _ at href
  have weight (w:ℝ) : driftDensity c T (2*m-w) =
      ENNReal.ofReal (exp (2*c*m)) * driftDensity (-c) T w := by
    unfold driftDensity
    rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
    congr 2
    ring
  have hreflLaw : HasLaw (fun w : ℝ => 2*m-w) (gaussianReal (2*m+c*T) T) (gaussianReal ((-c)*T) T) := by
    have h0 : HasLaw (fun w : ℝ=>w) (gaussianReal ((-c)*T) T) (gaussianReal ((-c)*T) T) := ⟨measurable_id.aemeasurable,Measure.map_id⟩
    convert gaussianReal_const_add (gaussianReal_neg h0) (2*m) using 1
    · ext; simp; ring
    · congr 1; ring
  have hreflect : gaussianReal ((-c)*T) T (Ioi m) = gaussianReal (2*m+c*T) T (Iio m) := by
    trans (gaussianReal ((-c)*T) T) {w | 2*m-w < m}
    swap
    · exact hreflLaw.measure_eq (p:=fun w=>w<m) measurableSet_Iio
    congr 1
    ext w
    change m < w ↔ 2*m-w<m
    constructor <;> intro <;> linarith
  have hweight : P A = ENNReal.ofReal (exp (2*c*m)) * gaussianReal (2*m+c*T) T (Iio m) := by
    rw [href,show 2*m-m = m by ring]
    simp_rw [weight]
    rw [lintegral_const_mul'' _ (by unfold driftDensity; fun_prop : Measurable (driftDensity (-c) T)).aemeasurable]
    rw [← hreflect,gaussian_drift_measure (-c) hT,withDensity_apply _ measurableSet_Ioi]
  rw [show P.real (below B c T m) = P.real S from rfl, hprob,hUprob,hGauss]
  change _ - (P A).toReal = _
  rw [hweight,ENNReal.toReal_mul,ENNReal.toReal_ofReal (exp_pos _).le,
    ← measureReal_def, hGauss, integral_sub (integrable_gaussianPDFReal _ _).restrict ((integrable_gaussianPDFReal _ _).const_mul _).restrict,
    integral_const_mul]

end BrownianContinuous
end

-- BrownianContinuousFinite
section
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped NNReal

namespace BrownianContinuous

noncomputable def finiteMax (c : ℝ) (T : ℝ≥0) (f : ℝ≥0 → ℝ) : ℝ :=
  ⨆ n : ℕ, f (denseSeq (Iic T) n)+c*((denseSeq (Iic T) n : Iic T):ℝ≥0)

theorem finiteMax_measurable (c : ℝ) (T : ℝ≥0) : Measurable (finiteMax c T) := by
  unfold finiteMax
  exact Measurable.iSup fun n => (measurable_pi_apply _).add measurable_const

theorem finiteMax_le_iff {f : ℝ≥0 → ℝ} (hf : Continuous f) (c : ℝ) (T : ℝ≥0) (m : ℝ) :
    finiteMax c T f ≤ m ↔ ∀ s ≤ T, f s+c*s ≤ m := by
  let g (s : Iic T) := f s+c*((s:ℝ≥0):ℝ)
  have hc : Continuous g := by dsimp [g]; fun_prop
  have hcomp : IsCompact (Iic T) := by
    have heq : Iic T = Icc 0 T := by ext t; simp
    rw [heq]
    exact isCompact_Icc
  letI : CompactSpace (Iic T) := isCompact_iff_compactSpace.mp hcomp
  have hb : BddAbove (Set.range (fun n => g (denseSeq (Iic T) n))) :=
    (isCompact_range hc).bddAbove.mono (by rintro _ ⟨i,rfl⟩; exact ⟨_,rfl⟩)
  change (⨆ n : ℕ, g (denseSeq (Iic T) n)) ≤ m ↔ _
  constructor
  · intro h s hs
    by_contra! hlt
    obtain ⟨i,hi⟩ := (denseRange_denseSeq (Iic T)).exists_mem_open (hc.isOpen_preimage (Ioi m) isOpen_Ioi)
      ⟨⟨s,hs⟩,hlt⟩
    exact (not_lt_of_ge ((le_ciSup hb i).trans h)) hi
  · intro h
    exact ciSup_le (fun n => h _ (denseSeq (Iic T) n).property)

theorem aemeasurable_finiteMax {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (c : ℝ) (T : ℝ≥0) :
    AEMeasurable (fun ω => finiteMax c T (fun s => B s ω)) P := by
  unfold finiteMax
  exact AEMeasurable.iSup fun n => (hB.aemeasurable _).add aemeasurable_const

end BrownianContinuous
end

-- BrownianContinuousTail
section
open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace BrownianContinuous
noncomputable def pref (d t : ℝ) := (sqrt (2*π*t))⁻¹*exp (-(d^2*t)/2)
noncomputable def tailScale (d t : ℝ) := pref d t/t
noncomputable def images (d m : ℝ) (t : ℝ≥0) (w : ℝ) :=
  gaussianPDFReal (d*t) t w-exp (2*d*m)*gaussianPDFReal (2*m+d*t) t w

theorem factor_images (d m : ℝ) {t:ℝ≥0} (ht:0<t) (w:ℝ) :
    images d m t w = pref d t * (exp (d*w)*exp (-w^2/(2*t)) * (1-exp (-(2*m*(m-w)/(t:ℝ))))) := by
  have ht' : (t:ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have h1 : exp (-(w-d*t)^2/(2*(t:ℝ))) =
      exp (-(d^2*t)/2)*exp (d*w)*exp (-w^2/(2*(t:ℝ))) := by
    rw [← exp_add,← exp_add]; congr 1; field_simp; ring
  have h2 : exp (2*d*m)*exp (-(w-(2*m+d*t))^2/(2*(t:ℝ))) =
      exp (-(w-d*t)^2/(2*(t:ℝ)))*exp (-(2*m*(m-w)/(t:ℝ))) := by
    rw [←exp_add,←exp_add]; congr 1; field_simp; ring
  unfold images pref gaussianPDFReal
  have hw := congrArg (fun y => (sqrt (2*π*(t:ℝ)))⁻¹*y) h2
  rw [h1] at hw ⊢
  linarith only [hw]

theorem images_nonneg {d m w : ℝ} {t:ℝ≥0} (ht:0<t) (hm:0≤m) (hw:w≤m) : 0 ≤ images d m t w := by
  rw [factor_images _ _ ht]
  have : exp (-(2*m*(m-w)/(t:ℝ))) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  unfold pref
  positivity

theorem images_integrable (d m : ℝ) (t:ℝ≥0) : Integrable (images d m t) :=
  (integrable_gaussianPDFReal _ _).sub ((integrable_gaussianPDFReal _ _).const_mul _)

/-- An integrable majorant for the difference of the original and image heat kernels. -/
theorem images_upper {d m w : ℝ} {t:ℝ≥0} (hd:0<d) (ht:0<t) (hm:0≤m) (hw:w≤m) :
    images d m t w ≤ (tailScale d t*(4*m/d)*exp (d*m/2)) *exp ((d/2)*w) := by
  let u := 2*m*(m-w)/(t:ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have h1 : 1-exp (-u) ≤ u := by linarith [Real.add_one_le_exp (-u)]
  have h2 : 0 ≤ 1-exp (-u) := sub_nonneg.mpr (exp_le_one_iff.mpr (neg_nonpos.mpr hu))
  have h3 : exp (-w^2/(2*(t:ℝ))) ≤ 1 := exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  have h4 : exp (d*w)*(m-w) ≤ (2/d)*exp (d*m/2)*exp ((d/2)*w) := by
    have hA := Real.add_one_le_exp (d*(m-w)/2)
    have hB : m-w ≤ 2/d*exp (d*(m-w)/2) := by
      rw [div_mul_eq_mul_div,le_div_iff₀ hd]
      linarith
    calc
      _ ≤ exp (d*w)*(2/d*exp (d*(m-w)/2)) := mul_le_mul_of_nonneg_left hB (exp_pos _).le
      _ = _ := by
        rw [mul_left_comm (exp (d*w)),←exp_add, mul_assoc,←exp_add]
        congr 2
        ring
  have hP : 0 ≤ pref d t := by unfold pref; positivity
  rw [factor_images d m ht]
  calc
    _ ≤ pref d t*(exp (d*w)*1*u) := by
      apply mul_le_mul_of_nonneg_left _ hP
      exact mul_le_mul (mul_le_mul_of_nonneg_left h3 (exp_pos _).le) h1 h2 (by positivity)
    _ = (pref d t*(2*m/(t:ℝ)))*(exp (d*w)*(m-w)) := by dsimp [u]; ring
    _ ≤ (pref d t*(2*m/(t:ℝ)))*((2/d)*exp (d*m/2)*exp ((d/2)*w)) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by unfold tailScale; ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

theorem below_upper (hB : IsBrownianReal B P) {d m : ℝ} {t:ℝ≥0} (hd:0<d) (ht:0<t) (hm:0≤m) :
    P.real (below B d t m) ≤ tailScale d t*(8*m/d^2)*exp (d*m) := by
  let K := tailScale d t*(4*m/d)*exp (d*m/2)
  have hdi : 0 < d/2 := by linarith
  rw [below_integral hB ht d hm]
  calc
    _ ≤ ∫ w in Iio m,K*exp ((d/2)*w) := by
      apply setIntegral_mono_on (images_integrable d m t).restrict
        (((integrableOn_exp_mul_Iic hdi m).mono_set Iio_subset_Iic_self).const_mul K) measurableSet_Iio
      exact fun w hw => images_upper hd ht hm hw.le
    _ = _ := by
      rw [integral_const_mul, ← integral_Iic_eq_integral_Iio,integral_exp_mul_Iic hdi]
      dsimp [K]
      rw [show (d/2)*m = d*m/2 by ring]
      have he : exp (d*m/2)*exp (d*m/2) = exp (d*m) := by rw [←exp_add]; congr 1; ring
      rw [← he]
      ring

/-- The image kernel on a fixed rectangle supplies the matching lower power of time. -/
theorem images_lower {d w : ℝ} {t:ℝ≥0} (hd:0≤d) (ht:1≤t) (hw:0≤w) (hw' : w≤1/2) :
    tailScale d t * exp (-3) ≤ images d 1 t w := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have htpos : 0<t := lt_of_lt_of_le zero_lt_one ht
  let u := 2*(1-w)/(t:ℝ)
  have hu : 0 ≤ u := div_nonneg (by linarith) (by positivity)
  have hsmall : (1:ℝ)/t ≤ u := by dsimp [u]; gcongr; linarith
  have hbig : u ≤ 2 := by dsimp [u]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hdiff : (1:ℝ)/t*exp (-2) ≤ 1-exp (-u) := by
    have h0 : 1+u ≤ exp u := by linarith [Real.add_one_le_exp u]
    have h1 := mul_le_mul_of_nonneg_right h0 (exp_pos (-u)).le
    rw [← exp_add,add_neg_cancel,exp_zero] at h1
    have := mul_le_mul hsmall (exp_le_exp.mpr (neg_le_neg hbig)) (exp_pos _).le hu
    linarith
  have hgauss : exp (-1) ≤ exp (-w^2/(2*(t:ℝ))) := by
    apply exp_le_exp.mpr
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hw (sub_nonneg.mpr hw'),sq_nonneg w]
  have h0 : 1 ≤ exp (d*w) := one_le_exp_iff.mpr (mul_nonneg hd hw)
  have h1 := mul_le_mul h0 hgauss (exp_pos _).le (exp_pos _).le
  rw [one_mul] at h1
  have h2 := mul_le_mul h1 hdiff (by positivity) (by positivity)
  have hP : 0 ≤ pref d t := by unfold pref; positivity
  have h3 := mul_le_mul_of_nonneg_left h2 hP
  rw [factor_images _ _ htpos]
  rw [show 2*(1:ℝ)*(1-w)/(t:ℝ) = u by dsimp [u]; ring]
  have he : exp (-3) = exp (-1)*exp (-2) := by rw [←exp_add]; norm_num
  rw [he]
  unfold tailScale
  calc
    _ = pref d t*(exp (-1)*(1/(t:ℝ)*exp (-2))) := by ring
    _ ≤ _ := h3

theorem below_lower (hB : IsBrownianReal B P) {d : ℝ} {t:ℝ≥0} (hd:0≤d) (ht:1≤t) :
    tailScale d t*(exp (-3)/2) ≤ P.real (below B d t 1) := by
  have htpos : 0<t := lt_of_lt_of_le zero_lt_one ht
  rw [below_integral hB htpos d zero_le_one]
  change _ ≤ ∫ w in Iio 1, images d 1 t w
  calc
    _ = ∫ _w in Ioc (0:ℝ) (1/2), tailScale d t*exp (-3) := by norm_num; ring
    _ ≤ ∫ w in Ioc (0:ℝ) (1/2), images d 1 t w := by
      apply setIntegral_mono_on (integrableOn_const (by simp)) (images_integrable _ _ _).restrict measurableSet_Ioc
      exact fun w hw => images_lower hd ht hw.1.le hw.2
    _ ≤ _ := by
      apply setIntegral_mono_set (images_integrable _ _ _).restrict
      · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Iio] with w hw
        exact images_nonneg htpos zero_le_one hw.le
      · exact (show Ioc (0:ℝ) (1/2) ⊆ Iio 1 by intro w hw; exact lt_of_le_of_lt hw.2 (by norm_num)).eventuallyLE

end BrownianContinuous
end

-- BrownianDiscrete
section
noncomputable section

namespace BrownianDiscrete

/-- Polynomial weight in the exponentially tilted Gaussian record probabilities. -/
def weight (n : ℕ) : ℝ := (n : ℝ) ^ (-(3 / 2 : ℝ))

theorem weight_nonneg (n : ℕ) : 0 ≤ weight n :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

@[simp] theorem weight_zero : weight 0 = 0 := by
  norm_num [weight, Real.zero_rpow]

theorem weight_summable : Summable weight := Real.summable_nat_rpow.mpr (by norm_num)

def convolution (v w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), v k * w (n - k)

def halfFactor : ℝ := 2 ^ (3 / 2 : ℝ)

theorem halfFactor_pos : 0 < halfFactor := Real.rpow_pos_of_pos (by norm_num) _

theorem weight_le_of_twice {n k : ℕ} (hn : 0 < n) (h : n ≤ 2 * k) :
    weight k ≤ halfFactor * weight n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hk' : (n : ℝ) ≤ 2 * k := by exact_mod_cast h
  calc
    weight k ≤ ((n : ℝ) / 2) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    _ = halfFactor * weight n := by
      rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num)]
      simp [halfFactor, weight, div_eq_mul_inv, mul_comm]

def convolutionConstant : ℝ := 2 * halfFactor * ∑' k, weight k

theorem convolutionConstant_nonneg : 0 ≤ convolutionConstant :=
  mul_nonneg (mul_nonneg (by norm_num) halfFactor_pos.le) (tsum_nonneg weight_nonneg)

/-- Splitting at half the index controls the full discrete convolution with a uniform constant. -/
theorem convolution_weight_le (n : ℕ) :
    convolution weight weight n ≤ convolutionConstant * weight n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [convolution]
  have hhalf : 0 ≤ halfFactor * weight n := mul_nonneg halfFactor_pos.le (weight_nonneg n)
  have href : ∑ k ∈ Finset.range (n + 1), weight (n - k) =
      ∑ k ∈ Finset.range (n + 1), weight k := by
    simpa using Finset.sum_range_reflect weight (n + 1)
  have hs := weight_summable.sum_le_tsum (Finset.range (n + 1)) (fun i _ => weight_nonneg i)
  calc
    convolution weight weight n ≤ ∑ k ∈ Finset.range (n+1),
        (halfFactor * weight n) * (weight k + weight (n-k)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := by simpa using hk
      by_cases h : n ≤ 2 * k
      · have hprod := mul_le_mul_of_nonneg_right (weight_le_of_twice hn h) (weight_nonneg (n-k))
        calc
          _ ≤ (halfFactor * weight n) * weight (n-k) := hprod
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (weight_nonneg k)) hhalf
      · have h' : n ≤ 2 * (n - k) := by omega
        calc
          _ = weight (n-k) * weight k := mul_comm _ _
          _ ≤ (halfFactor * weight n) * weight k :=
            mul_le_mul_of_nonneg_right (weight_le_of_twice hn h') (weight_nonneg k)
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (weight_nonneg (n-k))) hhalf
    _ = (halfFactor * weight n) * (2 * ∑ k ∈ Finset.range (n+1), weight k) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, href, two_mul]
    _ ≤ (halfFactor * weight n) * (2 * ∑' k, weight k) := by gcongr
    _ = _ := by unfold convolutionConstant; ring

/-- Powers indexed from one, so that the zeroth term here is the linear term in exp. -/
def convolutionPower (v : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => v
  | j+1 => convolution v (convolutionPower v j)

theorem convolutionPower_nonneg {v : ℕ → ℝ} (hv : ∀ n, 0 ≤ v n) (j n : ℕ) :
    0 ≤ convolutionPower v j n := by
  induction j generalizing n with
  | zero => exact hv n
  | succ j ih =>
    rw [convolutionPower, convolution]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hv k) (ih (n-k))

theorem convolutionPower_le {v : ℕ → ℝ} {U : ℝ} (hU : 0 ≤ U)
    (hv : ∀ n, 0 ≤ v n) (hub : ∀ n, v n ≤ U * weight n) (j n : ℕ) :
    convolutionPower v j n ≤ U * (U * convolutionConstant) ^ j * weight n := by
  have hK := convolutionConstant_nonneg
  induction j generalizing n with
  | zero => simpa [convolutionPower] using hub n
  | succ j ih =>
    calc
      convolutionPower v (j+1) n ≤ ∑ k ∈ Finset.range (n+1),
          U * (U * (U * convolutionConstant) ^ j) * (weight k * weight (n-k)) := by
        rw [convolutionPower, convolution]
        apply Finset.sum_le_sum
        intro k _
        exact (mul_le_mul (hub k) (ih (n-k)) (convolutionPower_nonneg hv j (n-k))
          (mul_nonneg hU (weight_nonneg k))).trans_eq (by ring)
      _ = U * (U * (U * convolutionConstant) ^ j) * convolution weight weight n :=
        (Finset.mul_sum ..).symm
      _ ≤ U * (U * (U * convolutionConstant) ^ j) * (convolutionConstant * weight n) := by
        exact mul_le_mul_of_nonneg_left (convolution_weight_le n) (by positivity)
      _ = _ := by rw [pow_succ]; ring

end BrownianDiscrete
end
end

-- BrownianDiscreteTail
section
noncomputable section
open MeasureTheory
namespace BrownianDiscrete

/-- The common continuous envelope of the two tails in the comparison. -/
def envelope (q t : ℝ) : ℝ := Real.exp (-q * t) * (1+t) ^ (-(3/2 : ℝ))

/-- Decomposing the right tail of an integer law into its positive lattice atoms. -/
theorem measure_integer_tail (μ : Measure ℤ) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 ≤ t) :
    μ.real {i : ℤ | t < (i : ℝ)} =
      ∑' j : ℕ, μ.real {(↑(⌊t⌋₊ + 1 + j) : ℤ)} := by
  let m := ⌊t⌋₊ + 1
  have hmt : t < (m : ℝ) := by simpa [m] using Nat.lt_floor_add_one t
  have hmle : (m : ℝ) ≤ t+1 := by
    dsimp [m]
    push_cast
    linarith [Nat.floor_le ht]
  have hset : {i : ℤ | t < (i : ℝ)} = ⋃ j : ℕ, ({(↑(m+j) : ℤ)} : Set ℤ) := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro hi
      have hmi : (m : ℤ) ≤ i := by
        by_contra! h
        have h' : i + 1 ≤ (m : ℤ) := by omega
        have h'' : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h'
        linarith
      refine ⟨(i - m).toNat, ?_⟩
      omega
    · rintro ⟨j, rfl⟩
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) j]
  have hd : Pairwise (Function.onFun Disjoint (fun j : ℕ => ({(↑(m+j) : ℤ)} : Set ℤ))) := by
    intro i j hij
    simpa [Function.onFun] using (show (↑(m+i) : ℤ) ≠ ↑(m+j) by omega)
  rw [measureReal_def, hset, measure_iUnion hd (fun _ => measurableSet_singleton _),
    ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  rfl

/-- Sharp transfer from two-sided local lattice mass bounds to two-sided right-tail bounds.
The constants include the floor correction and the full geometric sum. -/
theorem tail_of_atom_bounds (μ : Measure ℤ) [IsFiniteMeasure μ] {q A B : ℝ}
    (hq : 0 < q) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlow : ∀ n : ℕ, 0 < n → A * weight n * Real.exp (-q * n) ≤ μ.real {(n : ℤ)})
    (hupp : ∀ n : ℕ, 0 < n → μ.real {(n : ℤ)} ≤ B * weight n * Real.exp (-q * n))
    {t : ℝ} (ht : 0 ≤ t) :
    A * Real.exp (-q) * envelope q t ≤ μ.real {i : ℤ | t < (i : ℝ)} ∧
    μ.real {i : ℤ | t < (i : ℝ)} ≤
      halfFactor * B / (1 - Real.exp (-q)) * envelope q t := by
  let m := ⌊t⌋₊ + 1
  have hm : 0 < m := Nat.zero_lt_succ _
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have ht_m : t < (m : ℝ) := by simpa [m] using Nat.lt_floor_add_one t
  have hm_t : (m : ℝ) ≤ 1+t := by
    dsimp [m]
    push_cast
    linarith [Nat.floor_le ht]
  let C := halfFactor * B * envelope q t
  have henv : 0 ≤ envelope q t := mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg halfFactor_pos.le hB) henv
  have hgeom : Real.exp (-q) < 1 := by simpa using (neg_neg_of_pos hq)
  have hs := (summable_geometric_of_lt_one (Real.exp_pos (-q)).le hgeom).mul_left C
  have hu (j : ℕ) : μ.real {(↑(m+j) : ℤ)} ≤ C * Real.exp (-q) ^ j := by
    have hw : weight (m+j) ≤ halfFactor * (1+t) ^ (-(3/2:ℝ)) := by
      calc
        _ ≤ ((1+t)/2) ^ (-(3/2 : ℝ)) := by
          apply Real.rpow_le_rpow_of_nonpos (by positivity)
          · push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]
          · norm_num
        _ = _ := by
          rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num)]
          simp [halfFactor, div_eq_mul_inv, mul_comm]
    have he : Real.exp (-q * (m+j : ℕ)) ≤ Real.exp (-q*t) * Real.exp (-q)^j := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
      push_cast
      nlinarith
    calc
      _ ≤ B * weight (m+j) * Real.exp (-q * (m+j : ℕ)) := hupp _ (by omega)
      _ ≤ (B * (halfFactor * (1+t)^(-(3/2:ℝ)))) * (Real.exp (-q*t) * Real.exp (-q)^j) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hw hB) he (Real.exp_pos _).le
          (mul_nonneg hB (mul_nonneg halfFactor_pos.le (Real.rpow_nonneg (by linarith) _)))
      _ = _ := by unfold C envelope; ring
  have hmass := Summable.of_nonneg_of_le (fun j => measureReal_nonneg) hu hs
  rw [measure_integer_tail μ ht]
  change _ ≤ ∑' j : ℕ, μ.real {(↑(m+j) : ℤ)} ∧ (∑' j : ℕ, μ.real {(↑(m+j) : ℤ)}) ≤ _
  constructor
  · have hw : (1+t) ^ (-(3/2:ℝ)) ≤ weight m :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hm_t (by norm_num)
    have he : Real.exp (-q) * Real.exp (-q*t) ≤ Real.exp (-q*m) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith
    calc
      _ = A * ((1+t) ^ (-(3/2:ℝ))) * (Real.exp (-q) * Real.exp (-q*t)) := by unfold envelope; ring
      _ ≤ A * weight m * Real.exp (-q*m) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hw hA) he (by positivity) (mul_nonneg hA (weight_nonneg m))
      _ ≤ μ.real {(m : ℤ)} := hlow m hm
      _ ≤ _ := by simpa using hmass.le_tsum 0 (fun j _ => measureReal_nonneg)
  · calc
      _ ≤ ∑' j : ℕ, C * Real.exp (-q) ^ j := hmass.tsum_le_tsum hu hs
      _ = C * (1-Real.exp (-q))⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hgeom]
      _ = _ := by unfold C; ring

end BrownianDiscrete
end
end

-- BrownianDiscreteComparison
section
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace BrownianDiscrete

lemma envelope_translate {q c C L y z : ℝ} (hq : 0<q) (hc : 0<c) (_hC : 0≤C)
    (hy : 0≤y) (hyz : y≤z) (hgap : y+L≤z) (hcost : C ≤ c*Real.exp (q*L)) :
    C*envelope q z ≤ c*envelope q y := by
  have hw : (1+z)^(-(3/2:ℝ)) ≤ (1+y)^(-(3/2:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  have hex : Real.exp (q*L)*Real.exp (-q*z) ≤ Real.exp (-q*y) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left hgap hq.le]
  have hg : C*Real.exp (-q*z) ≤ c*Real.exp (-q*y) := by
    calc
      _ ≤ (c*Real.exp (q*L))*Real.exp (-q*z) := mul_le_mul_of_nonneg_right hcost (Real.exp_pos _).le
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hex hc.le
  simpa [envelope, mul_assoc] using mul_le_mul hg hw (Real.rpow_nonneg (by linarith) _) (by positivity)

/-- Upper and lower bounds for the two directed tails imply stochastic order after a finite
translation. The unit offset turns weak left-tail events into strict ones at every atom. -/
theorem translation_of_tail_bounds {q cX cY CX CY : ℝ}
    (hq : 0<q) (hcX : 0<cX) (hcY : 0<cY) (hCX : 0<CX) (hCY : 0<CY) :
    ∃ b : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X Y : Ω → ℝ), AEMeasurable X P → AEMeasurable Y P →
      (∀ t : ℝ, 0≤t → P.real {ω | t<X ω} ≤ CX * envelope q t) →
      (∀ t : ℝ, 0≤t → cY * envelope q t ≤ P.real {ω | t<Y ω}) →
      (∀ t : ℝ, 0≤t → cX * envelope q t ≤ P.real {ω | t< -X ω}) →
      (∀ t : ℝ, 0≤t → P.real {ω | t< -Y ω} ≤ CY * envelope q t) →
      ∀ x : ℝ, P {ω | x<X ω} ≤ P {ω | x<Y ω+b} := by
  let M := max (CX/cY) (CY/cX)
  let L := M/q
  have hM : 0<M := lt_of_lt_of_le (div_pos hCX hcY) (le_max_left ..)
  have hL : 0<L := div_pos hM hq
  have hqL : q*L=M := by dsimp [L]; field_simp
  have hC₁ : CX ≤ cY*Real.exp (q*L) := by
    have ha := (div_le_iff₀ hcY).mp (show CX/cY ≤ M from le_max_left ..)
    rw [hqL]
    nlinarith [mul_le_mul_of_nonneg_left (Real.add_one_le_exp M) hcY.le]
  have hC₂ : CY ≤ cX*Real.exp (q*L) := by
    have ha := (div_le_iff₀ hcX).mp (show CY/cX ≤ M from le_max_right ..)
    rw [hqL]
    nlinarith [mul_le_mul_of_nonneg_left (Real.add_one_le_exp M) hcX.le]
  let b := 2*L+1
  refine ⟨b, ?_⟩
  intro Ω mΩ P hP X Y hmX hmY hXr hYr hXl hYl x
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change P.real {ω | x<X ω} ≤ P.real {ω | x<Y ω+b}
  by_cases hx : L ≤ x
  · let y := max 0 (x-b)
    have hy : 0≤y := le_max_left .. 
    have hyL : y+L≤x := by dsimp [y,b]; rcases le_total 0 (x-(2*L+1)) with h|h <;> simp [max_eq_left h, max_eq_right h] <;> linarith
    calc
      _ ≤ CX*envelope q x := hXr x (hL.le.trans hx)
      _ ≤ cY*envelope q y := envelope_translate hq hcY hCX.le hy (by linarith) hyL hC₁
      _ ≤ P.real {ω | y<Y ω} := hYr y hy
      _ ≤ _ := measureReal_mono (h₂:=measure_ne_top _ _) (by
        intro ω hw
        change y<Y ω at hw
        change x < Y ω+b
        linarith [le_max_right (0:ℝ) (x-b)])
  · let y := max 0 (-x)
    let z := b-x-1
    have hy : 0≤y := le_max_left ..
    have hyz : y+L≤z := by
      dsimp [y,z,b]
      by_cases h : 0 ≤ -x
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left (by linarith)]; linarith
    have hle : P.real {ω | x<Y ω+b}ᶜ ≤ P.real {ω | x<X ω}ᶜ := by
      calc
        _ ≤ P.real {ω | z < -Y ω} := measureReal_mono (h₂:=measure_ne_top _ _) (by
          intro ω hw
          change ¬x<Y ω+b at hw
          change z < -Y ω
          dsimp [z]; linarith)
        _ ≤ CY*envelope q z := hYl z (by linarith)
        _ ≤ cX*envelope q y := envelope_translate hq hcX hCY.le hy (by linarith) hyz hC₂
        _ ≤ P.real {ω | y < -X ω} := hXl y hy
        _ ≤ _ := measureReal_mono (h₂:=measure_ne_top _ _) (by
          intro ω hw
          change y < -X ω at hw
          change ¬x<X ω
          linarith [le_max_right (0:ℝ) (-x)])
    have hm1 : NullMeasurableSet {ω | x < Y ω+b} P :=
      nullMeasurableSet_lt aemeasurable_const (hmY.add aemeasurable_const)
    have hm2 : NullMeasurableSet {ω | x < X ω} P :=
      nullMeasurableSet_lt aemeasurable_const hmX
    rw [probReal_compl_eq_one_sub₀ hm1, probReal_compl_eq_one_sub₀ hm2] at hle
    linarith

end BrownianDiscrete
end
end

-- BrownianDiscreteComparisonJoin
section
noncomputable section
open MeasureTheory ProbabilityTheory Set OMA.S_mo_142880
open scoped NNReal
namespace BrownianDiscrete

/-- Right-tail envelope estimates for the integer maximizing selector, uniform over all
admissible realizations of the signed process. -/
def DiscreteEnvelope (d c C : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ → Ω → ℝ), IsBrownianReal (fun t : ℝ≥0 => B (t:ℝ)) P →
    IsBrownianReal (fun t : ℝ≥0 => B (-(t:ℝ))) P →
    IndepFun (fun ω (t : ℝ≥0) => B (t:ℝ) ω) (fun ω (t : ℝ≥0) => B (-(t:ℝ)) ω) P →
    ∀ (D : Ω → ℤ), AEMeasurable D P →
    (∀ᵐ ω ∂P, ∀ k : ℤ, height B d k ω ≤ height B d (D ω) ω) →
    ∀ t : ℝ, 0≤t → c*envelope (d^2/2) t ≤ P.real {ω | t < (D ω : ℝ)} ∧
      P.real {ω | t < (D ω : ℝ)} ≤ C*envelope (d^2/2) t

/-- Right-tail envelope estimates for the real maximizing selector under the same quantifiers. -/
def ContinuousEnvelope (d c C : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ → Ω → ℝ), IsBrownianReal (fun t : ℝ≥0 => B (t:ℝ)) P →
    IsBrownianReal (fun t : ℝ≥0 => B (-(t:ℝ))) P →
    IndepFun (fun ω (t : ℝ≥0) => B (t:ℝ) ω) (fun ω (t : ℝ≥0) => B (-(t:ℝ)) ω) P →
    ∀ (T : Ω → ℝ), AEMeasurable T P →
    (∀ᵐ ω ∂P, ∀ t : ℝ, height B d t ω ≤ height B d (T ω) ω) →
    ∀ t : ℝ, 0≤t → c*envelope (d^2/2) t ≤ P.real {ω | t < T ω} ∧
      P.real {ω | t < T ω} ≤ C*envelope (d^2/2) t

/-- Reflection turns any maximizing selector of one process into a maximizing selector of
the reflected process. The tail estimates therefore imply the exact platform declaration. -/
theorem comparison_from_envelopes
    (hDEnv : ∀ d : ℝ, 0<d → ∃ c C : ℝ, 0<c ∧ 0<C ∧ DiscreteEnvelope d c C)
    (hTEnv : ∀ d : ℝ, 0<d → ∃ c C : ℝ, 0<c ∧ 0<C ∧ ContinuousEnvelope d c C) :
    type_of% @OMA.S_mo_142880.main := by
  intro d hd
  obtain ⟨cD, CD, hcD, hCD, dEnv⟩ := hDEnv d hd
  obtain ⟨cT, CT, hcT, hCT, tEnv⟩ := hTEnv d hd
  obtain ⟨b, hb⟩ := translation_of_tail_bounds (q:=d^2/2) (by positivity) hcD hcT hCD hCT
  refine ⟨1,b,zero_lt_one,?_⟩
  intro Ω mΩ P hP B hR hL hindep D T hmD hmT hD hT
  let rev (t : ℝ) := B (-t)
  have hR' : IsBrownianReal (fun t : ℝ≥0 => rev (t:ℝ)) P := hL
  have hL' : IsBrownianReal (fun t : ℝ≥0 => rev (-(t:ℝ))) P := by simpa [rev] using hR
  have hi' : IndepFun (fun ω (t : ℝ≥0) => rev (t:ℝ) ω) (fun ω (t : ℝ≥0) => rev (-(t:ℝ)) ω) P := by
    simpa [rev] using hindep.symm
  have hd' : ∀ᵐ ω ∂P, ∀ k : ℤ, height rev d k ω ≤ height rev d (-D ω) ω := by
    filter_upwards [hD] with ω hω k
    simpa [rev, height] using hω (-k)
  have ht' : ∀ᵐ ω ∂P, ∀ t : ℝ, height rev d t ω ≤ height rev d (-T ω) ω := by
    filter_upwards [hT] with ω hω t
    simpa [rev, height] using hω (-t)
  have h₁ := dEnv Ω P B hR hL hindep D hmD hD
  have h₂ := tEnv Ω P B hR hL hindep T hmT hT
  have h₃ := dEnv Ω P rev hR' hL' hi' (fun ω => -D ω) hmD.neg (by simpa only [Int.cast_neg] using hd')
  have h₄ := tEnv Ω P rev hR' hL' hi' (fun ω => -T ω) hmT.neg ht'
  intro x
  simpa only [one_mul] using hb Ω P (fun ω => (D ω:ℝ)) T (by fun_prop) hmT
    (fun t h => (h₁ t h).2) (fun t h => (h₂ t h).1)
    (fun t h => by simpa using (h₃ t h).1) (fun t h => (h₄ t h).2) x

end BrownianDiscrete
end
end

-- BrownianContinuousNormalize
section
noncomputable section
open MeasureTheory ProbabilityTheory Set Real BrownianContinuous BrownianDiscrete
open scoped NNReal
namespace BrownianComparison

theorem tailScale_eq {t : ℝ} (ht : 0<t) (d : ℝ) :
    tailScale d t = (√(2*π))⁻¹ * Real.exp (-(d^2/2)*t) * t^(-(3/2:ℝ)) := by
  have h : t^(3/2:ℝ) = t*√t := by
    rw [Real.sqrt_eq_rpow, show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add ht, Real.rpow_one]
  unfold tailScale pref
  rw [Real.sqrt_mul (by positivity), Real.rpow_neg ht.le, h,
    show -(d^2*t)/2 = -(d^2/2)*t by ring]
  simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

lemma envelope_pos {q t : ℝ} (ht : 0≤t) : 0 < envelope q t :=
  mul_pos (exp_pos _) (Real.rpow_pos_of_pos (by linarith) _)

lemma envelope_antitone {q t u : ℝ} (hq : 0≤q) (ht : 0≤t) (htu : t≤u) :
    envelope q u ≤ envelope q t := by
  exact mul_le_mul (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left htu hq]))
    (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num))
    (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le

/-- Any probability tail between fixed multiples of the heat-kernel scale for t≥1
lies between fixed multiples of the desired envelope on the entire positive half-line. -/
theorem normalize_continuous_tail {d l u : ℝ} (hd : 0<d) (hl : 0<l) (hu : 0<u) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ p : ℝ → ℝ, Antitone p → (∀ t, p t ≤ 1) →
      (∀ t : ℝ, 1≤t → l*tailScale d t ≤ p t ∧ p t ≤ u*tailScale d t) →
      ∀ t : ℝ, 0≤t → c*envelope (d^2/2) t ≤ p t ∧ p t ≤ C*envelope (d^2/2) t := by
  let q := d^2/2
  let r := (√(2*π))⁻¹
  let c := min (l*r) (l*tailScale d 1)
  let C := max (u*r*halfFactor) (envelope q 1)⁻¹
  have hq : 0≤q := by dsimp [q]; positivity
  have hr : 0<r := by dsimp [r]; positivity
  have hc : 0<c := lt_min (mul_pos hl hr) (mul_pos hl (by rw [tailScale_eq zero_lt_one]; positivity))
  have hC : 0<C := (mul_pos (mul_pos hu hr) halfFactor_pos).trans_le (le_max_left ..)
  refine ⟨c,C,hc,hC,?_⟩
  intro p hanti hcap hlarge t ht
  have he : 0≤envelope q t := (envelope_pos ht).le
  by_cases h1 : 1≤t
  · have ht' : 0<t := by linarith
    obtain ⟨hp₁,hp₂⟩ := hlarge t h1
    rw [tailScale_eq ht'] at hp₁ hp₂
    have hw₁ : (1+t)^(-(3/2:ℝ)) ≤ t^(-(3/2:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos ht' (by linarith) (by norm_num)
    have hw₂ : t^(-(3/2:ℝ)) ≤ halfFactor*(1+t)^(-(3/2:ℝ)) := by
      calc
        _ ≤ ((1+t)/2)^(-(3/2:ℝ)) := Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
        _ = _ := by
          rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
          simp [halfFactor, div_eq_mul_inv, mul_comm]
    constructor
    · calc
        _ ≤ (l*r)*envelope q t := mul_le_mul_of_nonneg_right (min_le_left ..) he
        _ = (l*r*exp (-q*t))*(1+t)^(-(3/2:ℝ)) := by unfold envelope; ring
        _ ≤ (l*r*exp (-q*t))*t^(-(3/2:ℝ)) := mul_le_mul_of_nonneg_left hw₁ (by positivity)
        _ ≤ _ := by simpa [q,r,mul_assoc] using hp₁
    · calc
        _ ≤ (u*r*exp (-q*t))*t^(-(3/2:ℝ)) := by simpa [q,r,mul_assoc] using hp₂
        _ ≤ (u*r*exp (-q*t))*(halfFactor*(1+t)^(-(3/2:ℝ))) := mul_le_mul_of_nonneg_left hw₂ (by positivity)
        _ = (u*r*halfFactor)*envelope q t := by unfold envelope; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left ..) he
  · have ht1 : t≤1 := by linarith
    have htop : envelope q t ≤ 1 := by simpa [envelope] using envelope_antitone hq (le_refl 0) ht
    have hbot : envelope q 1 ≤ envelope q t := envelope_antitone hq ht ht1
    have he1 := envelope_pos (q:=q) zero_le_one
    constructor
    · calc
        _ ≤ c*1 := mul_le_mul_of_nonneg_left htop hc.le
        _ ≤ l*tailScale d 1 := by rw [mul_one]; exact min_le_right ..
        _ ≤ p 1 := (hlarge 1 le_rfl).1
        _ ≤ _ := hanti ht1
    · calc
        _ ≤ 1 := hcap t
        _ = (envelope q 1)⁻¹*envelope q 1 := (inv_mul_cancel₀ he1.ne').symm
        _ ≤ (envelope q 1)⁻¹*envelope q t := mul_le_mul_of_nonneg_left hbot (inv_nonneg.mpr he1.le)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) he

/-- The input to the final, uniform normalization. Factors are written with tailScale
first to match the estimates from the competing-arm calculation. -/
def ContinuousLargeEnvelope (d l u : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ → Ω → ℝ), IsBrownianReal (fun t : ℝ≥0 => B (t:ℝ)) P →
    IsBrownianReal (fun t : ℝ≥0 => B (-(t:ℝ))) P →
    IndepFun (fun ω (t : ℝ≥0) => B (t:ℝ) ω) (fun ω (t : ℝ≥0) => B (-(t:ℝ)) ω) P →
    ∀ (T : Ω → ℝ), AEMeasurable T P →
    (∀ᵐ ω ∂P, ∀ t : ℝ, OMA.S_mo_142880.height B d t ω ≤ OMA.S_mo_142880.height B d (T ω) ω) →
    ∀ t : ℝ≥0, 1≤t →
      tailScale d t*l ≤ P.real {ω | (t:ℝ)<T ω} ∧ P.real {ω | (t:ℝ)<T ω} ≤ tailScale d t*u

theorem continuous_envelope_of_large {d : ℝ} (hd : 0<d)
    (H : ∃ l u : ℝ, 0<l ∧ 0<u ∧ ContinuousLargeEnvelope d l u) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ BrownianDiscrete.ContinuousEnvelope d c C := by
  obtain ⟨l,u,hl,hu,he⟩ := H
  obtain ⟨c,C,hc,hC,hnorm⟩ := normalize_continuous_tail hd hl hu
  refine ⟨c,C,hc,hC,?_⟩
  intro Ω mΩ P hP B hR hL hi T hm hT
  let p (x : ℝ) := P.real {ω | x<T ω}
  apply hnorm p
  · intro x y hxy
    exact measureReal_mono (h₂:=measure_ne_top _ _) fun _ h => lt_of_le_of_lt hxy h
  · exact fun _ => measureReal_le_one
  · intro x hx
    let t : ℝ≥0 := ⟨x,by linarith⟩
    have ht : 1≤t := hx
    obtain ⟨hl',hu'⟩ := he Ω P B hR hL hi T hm hT t ht
    exact ⟨(mul_comm l _).le.trans hl', hu'.trans (mul_comm _ u).le⟩

end BrownianComparison
end
end

-- BrownianDiscreteReversal
section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace BrownianComparison

/-- Reverse increments on [0,T] and extend by Brownian increments from time T.
The intervals whose increments are used are nested and have length s. -/
def reverseAt {Ω : Type*} (T : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) :=
  B (T-s) ω - B (max T s) ω

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem reverseAt_preBrownian (T : ℝ≥0) (hB : IsPreBrownianReal B P) :
    IsPreBrownianReal (reverseAt T B) P := by
  have hGauss : IsGaussianProcess (reverseAt T B) P := by
    apply hB.isGaussianProcess.of_isGaussianProcess
    intro s
    refine ⟨{T-s, max T s}, {
      toFun := fun x => x ⟨T-s, by simp⟩-x ⟨max T s,by simp⟩
      map_add' := by intro a b; simp; ring
      map_smul' := by intro c x; simp; ring },by simp [reverseAt]⟩
  apply hGauss.isPreBrownianReal_of_covariance
  · intro t
    exact (integral_sub (hB.integrable_eval _) (hB.integrable_eval _)).trans
      (by simp [hB.integral_eval])
  · intro s t hst
    have := hB.isGaussianProcess.isProbabilityMeasure
    have ha : T-t ≤ T-s := tsub_le_tsub_left hst _
    have hb : max T s ≤ max T t := max_le_max_left _ hst
    have h₁ : T-s ≤ max T t := (tsub_le_self : T-s ≤ T).trans (le_max_left ..)
    have h₂ : T-t ≤ max T s := (tsub_le_self : T-t ≤ T).trans (le_max_left ..)
    unfold reverseAt
    rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right,
      hB.covariance_eval, hB.covariance_eval, hB.covariance_eval, hB.covariance_eval,
      min_eq_right ha, min_eq_left h₁, min_eq_right h₂, min_eq_left hb]
    · rcases le_total s T with h | h
      · rw [max_eq_left h, NNReal.coe_sub h]
        ring
      · rw [max_eq_right h, tsub_eq_zero_of_le h]; simp
    all_goals first | exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
                    | exact (hB.isGaussianProcess.hasGaussianLaw_sub).memLp_two

theorem reverseAt_brownian (T : ℝ≥0) (hB : IsBrownianReal B P) : IsBrownianReal (reverseAt T B) P where
  toIsPreBrownianReal := reverseAt_preBrownian T hB.toIsPreBrownianReal
  cont := by
    filter_upwards [hB.cont] with ω h
    unfold reverseAt
    exact (h.comp (continuous_const.sub continuous_id)).sub (h.comp (continuous_const.max continuous_id))

end BrownianComparison
end
end

-- BrownianDrawdown
section
noncomputable section
open MeasureTheory ProbabilityTheory Set BrownianContinuous
open scoped NNReal ENNReal
namespace BrownianComparison

theorem pastGap_eq_reversed_max {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (d : ℝ) (T : ℝ≥0)
    (ω : Ω) (hB : Continuous (fun s => B s ω)) :
    pastGap d T (fun s => B s.val ω) = finiteMax d T (fun s => reverseAt T B s ω) := by
  have hcont : Continuous (fun s => reverseAt T B s ω) :=
    (hB.comp (continuous_const.sub continuous_id)).sub (hB.comp (continuous_const.max continuous_id))
  obtain ⟨s, hvalue, hmax⟩ := pastGap_isMax d T (fun s => B s.val ω) (hB.comp continuous_subtype_val)
  have hrev (u : ℝ≥0) (hu : u≤T) :
      reverseAt T B u ω + d*u = B (T-u) ω-d*((T-u:ℝ≥0):ℝ) - (B T ω-d*T) := by
    rw [reverseAt, max_eq_left hu, NNReal.coe_sub hu]
    ring
  have hsub (u : ℝ≥0) : T-u ≤ T := tsub_le_self
  apply le_antisymm
  · have hx := (finiteMax_le_iff hcont d T _).mp le_rfl (T-s.val) (hsub _)
    rw [hrev _ (hsub _), tsub_tsub_cancel_of_le s.property] at hx
    exact hvalue.trans_le hx
  · apply (finiteMax_le_iff hcont d T _).mpr
    intro u hu
    rw [hrev _ hu]
    exact hmax ⟨T-u,hsub _⟩

theorem pastGap_ae_reversed_max {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (d : ℝ) (T : ℝ≥0) :
    (fun ω => pastGap d T (fun s => B s.val ω)) =ᵐ[P]
      (fun ω => finiteMax d T (fun s => reverseAt T B s ω)) :=
  hB.cont.mono fun ω hω => pastGap_eq_reversed_max d T ω hω

end BrownianComparison
end
end

-- BrownianRandomBarrier
section
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace BrownianComparison

theorem expMeasure_Ioi {r a : ℝ} (hr : 0<r) (ha : 0≤a) :
    expMeasure r (Ioi a) = ENNReal.ofReal (Real.exp (-r*a)) := by
  let : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have h := cdf_expMeasure_eq hr a
  rw [if_pos ha, cdf_eq_real, ← compl_Ioi, probReal_compl_eq_one_sub measurableSet_Ioi] at h
  rw [← ENNReal.ofReal_toReal (measure_ne_top (expMeasure r) (Ioi a))]
  congr 1
  change (expMeasure r).real (Ioi a) = _
  rw [neg_mul]
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {A F : Ω → ℝ}

/-- Crossing an independent random barrier with an exponential overshoot. Strict crossing
after an additional fixed displacement factors into an ordinary Laplace transform. -/
theorem independent_exponential_barrier {r b : ℝ} (hr : 0<r) (hb : 0≤b)
    (hA : AEMeasurable A P) (hn : ∀ᵐ ω ∂P, 0≤A ω)
    (hF : HasLaw F (expMeasure r) P) (hi : IndepFun A F P) :
    P.real {ω | A ω + b < F ω} = Real.exp (-r*b) * ∫ ω, Real.exp (-r*A ω) ∂P := by
  let : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  let Q := P.map A
  have hLA : HasLaw A Q P := ⟨hA,rfl⟩
  have hposQ : ∀ᵐ a ∂Q, 0≤a := (hLA.ae_iff (p:=fun y : ℝ => 0≤y) (by fun_prop)).mp hn
  let E : Set (ℝ×ℝ) := {x | x.1+b<x.2}
  have hE : MeasurableSet E := measurableSet_lt (measurable_fst.add measurable_const) measurable_snd
  have hprod := (hi.hasLaw_prod hLA hF).measure_eq (p:=(·∈E)) hE
  change P {ω | A ω+b<F ω} = (Q.prod (expMeasure r)) E at hprod
  have hint : (∫⁻ a, expMeasure r (Prod.mk a ⁻¹' E) ∂Q) =
      ∫⁻ a, ENNReal.ofReal (Real.exp (-r*(a+b))) ∂Q := by
    apply lintegral_congr_ae
    filter_upwards [hposQ] with a ha
    exact expMeasure_Ioi hr (add_nonneg ha hb)
  rw [measureReal_def, hprod, Measure.prod_apply hE, hint]
  change (∫⁻ a, ENNReal.ofReal (Real.exp (-r*(a+b))) ∂P.map A).toReal = _
  rw [lintegral_map' (by fun_prop) hA]
  have he (ω : Ω) : Real.exp (-r*(A ω+b)) = Real.exp (-r*b)*Real.exp (-r*A ω) := by
    rw [← exp_add]; congr 1; ring
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => (Real.exp_pos _).le) (by fun_prop)]
  simp_rw [he]
  rw [integral_const_mul]

/-- Weak and strict independent comparisons agree, including barriers with atoms. -/
theorem independent_exponential_barrier_le {r : ℝ} (hr : 0<r)
    (hA : AEMeasurable A P) (hn : ∀ᵐ ω ∂P, 0≤A ω)
    (hF : HasLaw F (expMeasure r) P) (hi : IndepFun A F P) :
    P.real {ω | A ω ≤ F ω} = ∫ ω, Real.exp (-r*A ω) ∂P := by
  let : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  let : NullSingletonClass (expMeasure r) := by unfold expMeasure gammaMeasure; infer_instance
  let Q := P.map A
  have hLA : HasLaw A Q P := ⟨hA,rfl⟩
  let E : Set (ℝ×ℝ) := {x | x.1≤x.2}
  let E' : Set (ℝ×ℝ) := {x | x.1<x.2}
  have hE : MeasurableSet E := measurableSet_le measurable_fst measurable_snd
  have hE' : MeasurableSet E' := measurableSet_lt measurable_fst measurable_snd
  have hp := hi.hasLaw_prod hLA hF
  have hle := hp.measure_eq (p:=(·∈E)) hE
  have hlt := hp.measure_eq (p:=(·∈E')) hE'
  change P {ω | A ω≤F ω} = (Q.prod (expMeasure r)) E at hle
  change P {ω | A ω<F ω} = (Q.prod (expMeasure r)) E' at hlt
  have he : P {ω | A ω≤F ω} = P {ω | A ω<F ω} := by
    rw [hle, hlt, Measure.prod_apply hE, Measure.prod_apply hE']
    apply lintegral_congr
    intro a
    exact (measure_congr (μ := expMeasure r) (Ioi_ae_eq_Ici (a:=a))).symm
  calc
    _ = P.real {ω | A ω<F ω} := congrArg ENNReal.toReal he
    _ = _ := by simpa using independent_exponential_barrier (b:=0) hr le_rfl hA hn hF hi

end BrownianComparison
end
end

-- BrownianContinuousLaplace
section
open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace BrownianContinuous

noncomputable def laplaceUpper (d : ℝ) : ℝ :=
  (8/d^2*exp d)*(∑' n:ℕ, ((n:ℝ)+1)*(exp (-d))^n)

noncomputable def laplaceLower (d : ℝ) : ℝ := exp (-(2*d))*exp (-3)/2

theorem laplaceLower_pos (d:ℝ) : 0 < laplaceLower d := by unfold laplaceLower; positivity

private theorem geom_summable {d : ℝ} (hd:0<d) :
    Summable (fun n : ℕ => ((n:ℝ)+1)*(exp (-d))^n) := by
  have hr : ‖exp (-d)‖ < 1 := by rw [Real.norm_eq_abs,abs_of_pos (exp_pos _),exp_lt_one_iff]; linarith
  simpa only [add_mul,pow_one,one_mul] using
    (summable_pow_mul_geometric_of_norm_lt_one 1 hr).add (summable_geometric_of_norm_lt_one hr)

theorem laplaceUpper_pos {d:ℝ} (hd:0<d) : 0 < laplaceUpper d := by
  apply mul_pos (by positivity)
  exact (geom_summable hd).tsum_pos (fun n => by positivity) (i:=0) (by simp)

theorem tailScale_pos (d:ℝ) {t:ℝ≥0} (ht:0<t) : 0 < tailScale d t := by unfold tailScale pref; positivity

/-- Two-sided bounds on the Laplace transform of the positive-drift running maximum.
The variable `t` is the fixed observation time. -/
theorem finiteMax_laplace {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {d:ℝ} (hd:0<d) {t:ℝ≥0} (ht:1≤t) :
    tailScale d t*laplaceLower d ≤ ∫ ω, exp (-(2*d*finiteMax d t (fun s => B s ω))) ∂P ∧
     (∫ ω, exp (-(2*d*finiteMax d t (fun s => B s ω))) ∂P) ≤ tailScale d t*laplaceUpper d := by
  classical
  have htpos : 0<t := zero_lt_one.trans_le ht
  let M := fun ω => finiteMax d t (fun s => B s ω)
  let W := fun ω => exp (-(2*d*M ω))
  have hM : AEMeasurable M P := aemeasurable_finiteMax hB.toIsPreBrownianReal d t
  have mW : AEMeasurable W P := by dsimp [W]; fun_prop
  have hnon : 0 ≤ᵐ[P] M := by
    filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hcont hzero
    have hall := (finiteMax_le_iff hcont d t (M ω)).mp le_rfl
    simpa [hzero] using hall 0 (show (0:ℝ≥0)≤t by positivity)
  have iW : Integrable W P := by
    apply Integrable.mono' (integrable_const (1:ℝ)) mW.aestronglyMeasurable
    filter_upwards [hnon] with ω hw
    change ‖exp (-(2*d*M ω))‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_pos (exp_pos _),exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg (by positivity) hw)
  let E := fun (x:ℝ) => {ω | M ω ≤ x}
  have mE (x:ℝ) : NullMeasurableSet (E x) P := nullMeasurableSet_le hM aemeasurable_const
  have hE (x:ℝ) : P.real (E x) = P.real (below B d t x) := by
    apply measureReal_congr
    filter_upwards [hB.cont] with ω hc
    exact propext (finiteMax_le_iff hc d t x)
  constructor
  · have hbound := below_lower hB hd.le ht
    rw [← hE] at hbound
    let a := exp (-(2*d))
    have hpoint (ω:Ω) (hw:ω∈E 1) : a ≤ W ω := by
      apply exp_le_exp.mpr
      change M ω ≤ 1 at hw
      nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hw)]
    calc
      _ ≤ a * P.real (E 1) := by
        have := mul_le_mul_of_nonneg_left hbound (exp_pos (-(2*d))).le
        dsimp [laplaceLower,a] at *
        linarith
      _ = ∫ ω in E 1, a ∂P := by rw [setIntegral_const]; simp [smul_eq_mul,mul_comm]
      _ ≤ ∫ ω in E 1, W ω ∂P := by
        apply integral_mono_ae (integrable_const a) iW.restrict
        filter_upwards [ae_restrict_mem₀ (mE 1)] with ω hw using hpoint ω hw
      _ ≤ _ := setIntegral_le_integral iW (Filter.Eventually.of_forall (fun _ => (exp_pos _).le))
  · let Z (n:ℕ) := ENNReal.ofReal (exp (-(2*d*n)))
    let A (n:ℕ) := (E (n+1)).indicator (fun _ => Z n)
    have hA (n:ℕ) : AEMeasurable (A n) P := aemeasurable_const.indicator₀ (mE _)
    have hpoint : (fun ω => ENNReal.ofReal (W ω)) ≤ᵐ[P] (fun ω => ∑' n:ℕ, A n ω) := by
      filter_upwards [hnon] with ω hw
      let n := ⌊M ω⌋₊
      have hn : (n:ℝ) ≤ M ω := Nat.floor_le hw
      have hn' : M ω ≤ (n:ℝ)+1 := (Nat.lt_floor_add_one (M ω)).le
      apply le_trans (b:=A n ω) _ (ENNReal.le_tsum n)
      rw [show A n ω = Z n from Set.indicator_of_mem (show ω ∈ E ((n:ℝ)+1) from hn') _]
      apply ENNReal.ofReal_le_ofReal
      apply exp_le_exp.mpr
      nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hn)]
    let K := tailScale d t*(8/d^2*exp d)
    have hK : 0 ≤ K := mul_nonneg (tailScale_pos d htpos).le (by positivity)
    have hmass (n:ℕ) : (∫⁻ ω, A n ω ∂P) ≤ ENNReal.ofReal (K*(((n:ℝ)+1)*(exp (-d))^n)) := by
      rw [show ∫⁻ ω, A n ω ∂P = Z n * P (E (n+1)) by rw [show A n = _ from rfl,lintegral_indicator₀ (mE _),setLIntegral_const]]
      rw [← ofReal_measureReal (μ:=P), ← ENNReal.ofReal_mul (exp_pos _).le, hE]
      apply ENNReal.ofReal_le_ofReal
      apply (mul_le_mul_of_nonneg_left (below_upper hB hd htpos (by positivity : 0 ≤ (n:ℝ)+1)) (exp_pos _).le).trans_eq
      have hExp : exp (-(2*d*n))*exp (d*((n:ℝ)+1))=exp d*(exp (-d))^n := by
        rw [←exp_nat_mul,←exp_add,←exp_add]; congr 1; ring
      dsimp [K]
      linear_combination (tailScale d t * (8*((n:ℝ)+1)/d^2)) * hExp
    have hu : ENNReal.ofReal (∫ ω,W ω ∂P) ≤ ENNReal.ofReal (tailScale d t*laplaceUpper d) := by
      rw [ofReal_integral_eq_lintegral_ofReal iW (ae_of_all _ (fun _ => (exp_pos _).le))]
      apply (lintegral_mono_ae hpoint).trans
      rw [lintegral_tsum hA]
      apply (ENNReal.tsum_le_tsum hmass).trans_eq
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hK (by positivity)) ((geom_summable hd).mul_left K),tsum_mul_left]
      congr 1
      unfold laplaceUpper K
      ring
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (tailScale_pos d htpos).le (laplaceUpper_pos hd).le)).mp hu

end BrownianContinuous
end

-- BrownianContinuousAssembly
section
open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal
namespace BrownianComparison
open BrownianContinuous OMA.S_mo_142880

theorem continuous_large (d : ℝ) (hd : 0<d) :
    ∃ l u : ℝ, 0<l ∧ 0<u ∧ ContinuousLargeEnvelope d l u := by
  let a := exp (-(2*d))
  have ha : 0<a := exp_pos _
  have hab : 0<1-a := sub_pos.mpr (exp_lt_one_iff.mpr (by linarith))
  refine ⟨laplaceLower d * a * (1-a), laplaceUpper d,
    mul_pos (mul_pos (laplaceLower_pos d) ha) hab, laplaceUpper_pos hd, ?_⟩
  intro Ω mΩ P hP B hR hL hi T _hTm hT t ht
  let R (ω : Ω) (s : ℝ≥0) := B (s:ℝ) ω
  let G (ω : Ω) := gapAt d t (R ω)
  let F (ω : Ω) := futureAt d t (R ω)
  have hg : AEMeasurable G P := gapAt_aemeasurable hR.toIsPreBrownianReal d t
  have hgn : ∀ᵐ ω ∂P, 0≤G ω := ae_of_all _ (fun _ => ENNReal.toReal_nonneg)
  have hf : HasLaw F (expMeasure (2*d)) P := hasLaw_maximum (hR.shift t) hd
  have hind : IndepFun G F P := gapAt_indep_futureAt hR.toIsPreBrownianReal d t
  have h1 := independent_exponential_barrier (r := 2*d) (b := 1) (by positivity) (by norm_num) hg hgn hf hind
  have h2 := independent_exponential_barrier_le (r := 2*d) (by positivity) hg hgn hf hind
  let J := ∫ ω, exp (-(2*d*G ω)) ∂P
  have h1' : P.real {ω | G ω+1<F ω} = a*J := by simpa only [a,J,mul_one,neg_mul] using h1
  have h2' : P.real {ω | G ω≤F ω} = J := by simpa only [J,neg_mul] using h2
  obtain ⟨hlo,hup⟩ := selector_probability_sandwich (d := d) (B := B) (t := t) hd hR hL hi T hT
  change P.real {ω | G ω+1<F ω}*(1-a) ≤ _ at hlo
  change _ ≤ P.real {ω | G ω≤F ω} at hup
  rw [h1'] at hlo
  rw [h2'] at hup
  have hiJ : J = ∫ ω, exp (-(2*d * finiteMax d t (fun s => reverseAt t (fun u : ℝ≥0 => B (u:ℝ)) s ω))) ∂P := by
    apply integral_congr_ae
    filter_upwards [pastGap_ae_reversed_max hR d t] with ω h
    change exp (-(2*d * pastGap d t _)) = _
    rw [h]
  obtain ⟨hjl,hju⟩ := finiteMax_laplace (reverseAt_brownian t hR) hd ht
  rw [← hiJ] at hjl hju
  constructor
  · calc
      _ = (a*(tailScale d t*laplaceLower d))*(1-a) := by ring
      _ ≤ (a*J)*(1-a) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hjl ha.le) hab.le
      _ ≤ _ := hlo
  · exact hup.trans hju

end BrownianComparison
end

-- BrownianDiscreteGaussian
section
noncomputable section
open MeasureTheory Set ProbabilityTheory Real
open scoped NNReal
namespace BrownianDiscrete

/-- Exponentially tilted positive-increment probabilities divided by the time index.
This is the logarithmic series in the Sparre Andersen identity. -/
def tiltedIncrement {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (d : ℝ) (n : ℕ) : ℝ :=
  exp (d^2/2*n) * P.real {ω | 0 < B n ω - d*n} / n

def gaussianKernel (d n y : ℝ) : ℝ := exp (-d*y - y^2/(2*n))

private theorem normalization (n : ℕ) (hn : 0 < n) :
    (√(2*π*(n : ℝ)))⁻¹ / n = (√(2*π))⁻¹ * weight n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have h : (n : ℝ) * √(n : ℝ) = (n : ℝ) ^ (3/2 : ℝ) := by
    rw [sqrt_eq_rpow, show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hn', Real.rpow_one]
  rw [weight, Real.rpow_neg hn'.le, ← h, Real.sqrt_mul (by positivity)]
  field_simp

theorem tiltedIncrement_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (d : ℝ) {n : ℕ} (hn : 0 < n) :
    tiltedIncrement P B d n = (√(2*π))⁻¹ * weight n *
      ∫ y : ℝ in Ioi 0, gaussianKernel d n y := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn'' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hprob := (gaussianReal_sub_const (hB.hasLaw_eval (n : ℝ≥0)) (d*n)).measure_eq
    (p := fun x : ℝ => 0 < x) measurableSet_Ioi
  have hlaw : P.real {ω | 0 < B n ω - d*n} =
      ∫ y : ℝ in Ioi 0, gaussianPDFReal (-(d*n)) n y := by
    rw [measureReal_def, hprob, gaussianReal_apply_eq_integral _ hn'', ENNReal.toReal_ofReal]
    · simp [Set.Ioi]
    · exact integral_nonneg (fun y => gaussianPDFReal_nonneg _ _ _)
  have hex (y : ℝ) : exp (d^2/2*n) * gaussianPDFReal (-(d*n)) n y =
      (√(2*π*(n:ℝ)))⁻¹ * gaussianKernel d n y := by
    rw [gaussianPDFReal, gaussianKernel]
    push_cast
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    field_simp
    ring
  calc
    tiltedIncrement P B d n = (∫ y : ℝ in Ioi 0, exp (d^2/2*n) * gaussianPDFReal (-(d*n)) n y) / n := by
      rw [integral_const_mul, ← hlaw]; rfl
    _ = (√(2*π*(n:ℝ)))⁻¹ / n * ∫ y : ℝ in Ioi 0, gaussianKernel d n y := by
      simp_rw [hex]
      rw [integral_const_mul]
      ring
    _ = _ := by rw [normalization n hn]

theorem gaussianKernel_integral_bounds {d n : ℝ} (hd : 0 < d) (hn : 1 ≤ n) :
    exp (-d-1/2) ≤ ∫ y : ℝ in Ioi 0, gaussianKernel d n y ∧
    (∫ y : ℝ in Ioi 0, gaussianKernel d n y) ≤ 1/d := by
  have hn' : 0 < n := by linarith
  have hopen := integrableOn_exp_mul_Ioi (neg_neg_of_pos hd) 0
  have hk : ∀ y : ℝ, gaussianKernel d n y ≤ exp (-d*y) := fun y =>
    Real.exp_le_exp.mpr (sub_le_self _ (by positivity))
  have hi : IntegrableOn (gaussianKernel d n) (Ioi 0) := by
    apply hopen.mono'
    · unfold gaussianKernel
      fun_prop
    · exact ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ gaussianKernel d n y from (Real.exp_pos _).le)]; exact hk y
  constructor
  · have hsub : Ioc (0:ℝ) 1 ⊆ Ioi 0 := fun _ h => h.1
    calc
      _ = ∫ _y in Ioc (0:ℝ) 1, exp (-d-1/2) := by norm_num
      _ ≤ ∫ y in Ioc (0:ℝ) 1, gaussianKernel d n y := by
        apply setIntegral_mono_on (integrableOn_const (by simp)) (hi.mono_set hsub) measurableSet_Ioc
        intro y hy
        have hy0 := hy.1.le
        have hy1 := hy.2
        have hsq : y^2/(2*n) ≤ 1/2 := by
          apply (div_le_iff₀ (by positivity)).mpr
          nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
        exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hy1)])
      _ ≤ _ := setIntegral_mono_set hi (ae_of_all _ fun _ => (Real.exp_pos _).le) hsub.eventuallyLE
  · calc
      _ ≤ ∫ y : ℝ in Ioi 0, exp (-d*y) := integral_mono hi hopen hk
      _ = _ := by rw [integral_exp_mul_Ioi (neg_neg_of_pos hd)]; simp [one_div]

/-- The lower and upper bounds use the exact constants from the paper. -/
theorem tiltedIncrement_bounds {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {d : ℝ} (hd : 0 < d) (n : ℕ) :
    exp (-d-1/2) / √(2*π) * weight n ≤ tiltedIncrement P B d n ∧
      tiltedIncrement P B d n ≤ (1 / (d*√(2*π))) * weight n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [tiltedIncrement]
  have h := gaussianKernel_integral_bounds hd (show 1 ≤ (n : ℝ) by exact_mod_cast hn)
  have hmul : 0 ≤ (√(2*π))⁻¹ * weight n := mul_nonneg (by positivity) (weight_nonneg n)
  rw [tiltedIncrement_eq_integral hB d hn]
  constructor
  · exact (by ring : exp (-d-1/2)/√(2*π)*weight n = ((√(2*π))⁻¹*weight n)*exp (-d-1/2)) ▸
      mul_le_mul_of_nonneg_left h.1 hmul
  · exact (mul_le_mul_of_nonneg_left h.2 hmul).trans_eq (by simp [div_eq_mul_inv]; ring)

end BrownianDiscrete
end
end

-- BrownianDiscreteCycle
section
noncomputable section
open MeasureTheory ProbabilityTheory Set Fin.NatCast
namespace BrownianDiscrete

/-- Partial sums of the periodic extension of a finite increment vector. -/
def prefixSum {n : ℕ} [NeZero n] (v : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, v (j : Fin n)

theorem prefixSum_add {n : ℕ} [NeZero n] (v : Fin n → ℝ) (i k : ℕ) :
    prefixSum v (i+k) = prefixSum v i + prefixSum (fun s => v ((i : Fin n) + s)) k := by
  induction k with
  | zero => simp [prefixSum]
  | succ k ih =>
    simp only [Nat.add_succ, prefixSum] at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← add_assoc, ← ih, Nat.cast_add]

theorem prefixSum_period {n : ℕ} [NeZero n] (v : Fin n → ℝ) (k : ℕ) :
    prefixSum v (n+k) = prefixSum v n + prefixSum v k := by
  simpa using prefixSum_add v n k

def recordSet (n : ℕ) [NeZero n] : Set (Fin n → ℝ) :=
  {v | ∀ k < n, prefixSum v k < prefixSum v n}

theorem measurableSet_recordSet (n : ℕ) [NeZero n] : MeasurableSet (recordSet n) := by
  rw [show recordSet n = ⋂ k : Fin n, {v | prefixSum v k.val < prefixSum v n} by
    ext v
    simp only [Set.mem_iInter, Set.mem_setOf_eq, recordSet]
    exact ⟨fun h k => h k.val k.isLt, fun h k hk => h ⟨k,hk⟩⟩]
  apply MeasurableSet.iInter
  intro k
  apply measurableSet_lt <;> unfold prefixSum <;> fun_prop

/-- For a vector with positive total, some cyclic permutation has a strict record at its
last time. Maximize the prefixSum sums after subtracting the line between the endpoints. -/
theorem exists_rotated_record {n : ℕ} [NeZero n] (v : Fin n → ℝ) (H : 0 < prefixSum v n) :
    ∃ i : Fin n, (fun s => v (i+s)) ∈ recordSet n := by
  have hn : 0 < n := NeZero.pos n
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let c := prefixSum v n / n
  have hc : 0 < c := div_pos H hn'
  have hnc : (n : ℝ) * c = prefixSum v n := by dsimp [c]; field_simp
  obtain ⟨i, _, hi⟩ := (Finset.univ : Finset (Fin n)).exists_max_image
    (fun i : Fin n => prefixSum v i - (i : ℕ) * c) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  have rot (k : ℕ) : prefixSum (fun s => v (i+s)) k = prefixSum v (i.val+k) - prefixSum v i := by
    have h := prefixSum_add v i.val k
    simpa using (eq_sub_of_add_eq' h.symm)
  have rot_n : prefixSum (fun s => v (i+s)) n = prefixSum v n := by
    rw [rot, Nat.add_comm, prefixSum_period]; ring
  intro k hk
  rw [rot_n, rot]
  have hk' : (k : ℝ)*c < (n : ℝ)*c := by exact mul_lt_mul_of_pos_right (by exact_mod_cast hk) hc
  by_cases h : i.val+k < n
  · let j : Fin n := ⟨i.val+k, h⟩
    have hh := hi j (Finset.mem_univ _)
    dsimp [j] at hh
    push_cast at hh
    linarith
  · let r := i.val+k-n
    have hr : r<n := by dsimp [r]; omega
    have hnr : i.val+k = n+r := by dsimp [r]; omega
    have h2 : (i.val : ℝ)+k = n+(r:ℝ) := by exact_mod_cast hnr
    have hh := hi (⟨r,hr⟩ : Fin n) (Finset.mem_univ _)
    rw [hnr, prefixSum_period]
    dsimp only at hh
    nlinarith [congrArg (fun x : ℝ => x*c) h2]

end BrownianDiscrete
end
end

-- BrownianDiscreteRecord
section
noncomputable section
open MeasureTheory ProbabilityTheory Set Fin.NatCast
open scoped NNReal
namespace BrownianDiscrete

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A positive total in any prescribed Borel set is attained as a record under at least one
cyclic shift. Exchangeable independent increments make all shifts equiprobable. -/
theorem cyclic_record_bound {n : ℕ} [NeZero n] {X : Fin n → Ω → ℝ} {ν : Measure ℝ}
    (hi : iIndepFun X P) (hl : ∀ i, HasLaw (X i) ν P) (A : Set ℝ)
    (hA : MeasurableSet A) (hpos : A ⊆ Ioi 0) :
    P.real {ω | prefixSum (fun i => X i ω) n ∈ A} ≤
    n * P.real {ω | (fun i => X i ω) ∈ recordSet n ∧ prefixSum (fun i => X i ω) n ∈ A} := by
  let F : Set (Fin n → ℝ) := recordSet n ∩ (fun v => prefixSum v n) ⁻¹' A
  have hF : MeasurableSet F := (measurableSet_recordSet n).inter <| hA.preimage (by unfold prefixSum; fun_prop)
  let Z (i : Fin n) (ω : Ω) (s : Fin n) := X (i+s) ω
  have hZ (i : Fin n) : HasLaw (Z i) (Measure.pi (fun _ : Fin n => ν)) P :=
    (hi.precomp (g := fun s : Fin n => i+s) (fun _ _ h => add_left_cancel h)).hasLaw_pi
      (fun s => hl (i+s))
  have hprob (i : Fin n) : P.real (Z i ⁻¹' F) =
      P.real {ω | (fun i => X i ω) ∈ recordSet n ∧ prefixSum (fun i => X i ω) n ∈ A} := by
    exact ((hZ i).measureReal_eq (p := (· ∈ F)) hF).trans
      ((hi.hasLaw_pi hl).measureReal_eq (p := (· ∈ F)) hF).symm
  have hsub : {ω | prefixSum (fun i => X i ω) n ∈ A} ⊆ ⋃ i : Fin n, Z i ⁻¹' F := by
    intro ω hω
    obtain ⟨i, hi⟩ := exists_rotated_record (fun i => X i ω) (hpos hω)
    refine Set.mem_iUnion.mpr ⟨i, hi, ?_⟩
    have he := prefixSum_add (fun i => X i ω) i.val n
    rw [Nat.add_comm, prefixSum_period] at he
    change prefixSum (fun s => X (i+s) ω) n ∈ A
    have hs : prefixSum (fun s => X (i+s) ω) n = prefixSum (fun i => X i ω) n := by
      simpa using (add_left_cancel (show prefixSum (fun i => X i ω) i.val +
        prefixSum (fun s => X (i+s) ω) n = prefixSum (fun i => X i ω) i.val +
        prefixSum (fun i => X i ω) n by simpa [add_comm] using he.symm) )
    rwa [hs]
  calc
    _ ≤ P.real (⋃ i : Fin n, Z i ⁻¹' F) := measureReal_mono hsub
    _ ≤ ∑ i : Fin n, P.real (Z i ⁻¹' F) := measureReal_iUnion_fintype_le _
    _ = _ := by simp [hprob]

/-- Drifted increments over the finite lattice interval have an iid normal product law. -/
def increment (B : ℝ≥0 → Ω → ℝ) (d : ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  B (i+1) ω - B i ω - d

theorem increment_iid {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (d : ℝ) (n : ℕ) :
    iIndepFun (fun i : Fin n => increment B d i.val) P ∧
    ∀ i : Fin n, HasLaw (increment B d i.val) (gaussianReal (-d) 1) P := by
  constructor
  · have h := hB.hasIndepIncrements.nat (t := fun k : ℕ => (k : ℝ≥0)) (fun i j hij => by dsimp; exact_mod_cast hij)
    have h' := h.precomp (g := fun i : Fin n => i.val) Fin.val_injective
    change iIndepFun (fun (i : Fin n) (ω : Ω) => B ((i.val : ℝ≥0)+1) ω - B i.val ω - d) P
    simpa [Function.comp_def] using h'.comp (fun _ x => x-d) (fun _ => measurable_id.sub measurable_const)
  · intro i
    have hh := gaussianReal_sub_const (hB.hasLaw_sub ((i.val : ℝ≥0)+1) (i.val : ℝ≥0)) d
    convert hh using 1 <;> simp [Pi.sub_apply]
    congr 1
    apply congrArg (gaussianReal (-d))
    apply NNReal.eq
    simp [Real.dist_eq]

omit [MeasurableSpace Ω] in
theorem prefixSum_increment {B : ℝ≥0 → Ω → ℝ} {d : ℝ} {n : ℕ} [NeZero n]
    {k : ℕ} (hk : k ≤ n) (ω : Ω) :
    prefixSum (fun i : Fin n => increment B d i.val ω) k =
      B k ω - B 0 ω - d*k := by
  induction k with
  | zero => simp [prefixSum]
  | succ k ih =>
    have hkn : k < n := Nat.lt_of_succ_le hk
    have hval : (k : Fin n).val = k := Nat.mod_eq_of_lt hkn
    rw [prefixSum, Finset.sum_range_succ]
    rw [show (∑ j ∈ Finset.range k, increment B d (j : Fin n).val ω) = _ from ih hkn.le]
    rw [hval, increment]
    push_cast
    ring

/-- The probability that a drifted Brownian arm sets a strict lattice record at time n
is at least its one-time positive probability divided by n. -/
theorem drifted_record_lower {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (d : ℝ)
    {n : ℕ} (hn : 0 < n) :
    P.real {ω | 0 < B n ω - d*n} / n ≤
      P.real {ω | ∀ k < n, B k ω - d*k < B n ω - d*n} := by
  let : NeZero n := ⟨hn.ne'⟩
  let X (i : Fin n) := increment B d i.val
  obtain ⟨hi, hl⟩ := increment_iid hB d n
  have h := cyclic_record_bound (X := X) hi hl (Ioi 0) measurableSet_Ioi Subset.rfl
  have hL : P.real {ω | prefixSum (fun i => X i ω) n ∈ Ioi 0} =
      P.real {ω | 0 < B n ω - d*n} := by
    apply measureReal_congr
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    apply propext
    change (0 < prefixSum (fun i : Fin n => increment B d i.val ω) n) ↔ (0 < B n ω - d*n)
    simp [prefixSum_increment le_rfl, hω]
  have hR : {ω | (fun i => X i ω) ∈ recordSet n ∧ prefixSum (fun i => X i ω) n ∈ Ioi 0} ⊆
      {ω | ∀ k < n, B k ω - d*k < B n ω - d*n} := by
    intro ω hω k hk
    have he := hω.1 k hk
    change prefixSum (fun i : Fin n => increment B d i.val ω) k <
        prefixSum (fun i : Fin n => increment B d i.val ω) n at he
    rw [prefixSum_increment hk.le, prefixSum_increment le_rfl] at he
    linarith
  rw [hL] at h
  apply (div_le_iff₀ (by exact_mod_cast hn)).mpr
  calc
    _ ≤ _ := h
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (measureReal_mono hR) (by positivity)

end BrownianDiscrete
end
end

-- BrownianDiscreteTilt
section
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal
namespace BrownianDiscrete

/-- Product density of a finite iid sample of unit-variance normal increments. -/
theorem gaussianProduct_density (n : ℕ) (u : ℝ) :
    Measure.pi (fun _ : Fin n => gaussianReal u 1) =
    (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).withDensity
      (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal u 1 (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hi : Integrable (fun x : Fin n → ℝ => ∏ i, gaussianPDFReal u 1 (x i))
      (Measure.pi (fun i => (volume : Measure ℝ).restrict (s i))) :=
    Integrable.fintype_prod (fun i => (integrable_gaussianPDFReal u 1).restrict)
  have hnn : ∀ x : Fin n → ℝ, 0 ≤ ∏ i, gaussianPDFReal u 1 (x i) :=
    fun x => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hnn),
    integral_fintype_prod_eq_prod (fun _ : Fin n => gaussianPDFReal u 1)]
  simp_rw [gaussianReal_apply_eq_integral _ (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => gaussianPDFReal_nonneg _ _ _))

/-- The Radon–Nikodym derivative for adding drift to a finite Gaussian random walk
depends only on its endpoint and the number of steps. -/
theorem gaussianProduct_drift (n : ℕ) (d : ℝ) :
    Measure.pi (fun _ : Fin n => gaussianReal (-d) 1) =
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(d^2/2)*n - d*∑ i, x i))) := by
  have h1 (x : ℝ) : gaussianPDFReal (-d) 1 x =
      gaussianPDFReal 0 1 x * Real.exp (-(d^2/2)-d*x) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, sub_neg_eq_add]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hmeas : Measurable (fun x : Fin n → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) :=
    ENNReal.measurable_ofReal.comp <| Finset.measurable_prod _ (fun i _ => (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply _))
  rw [gaussianProduct_density n (-d), gaussianProduct_density n 0, ← withDensity_mul _ hmeas (by fun_prop)]
  apply withDensity_congr_ae
  apply ae_of_all
  intro x
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp_rw [h1, Finset.prod_mul_distrib]
  rw [← Real.exp_sum]
  congr 2
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum]
  ring

end BrownianDiscrete
end
end

-- BrownianDiscreteMiddle
section
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal
namespace BrownianDiscrete

/-- A unit interval has uniformly bounded mass under a centered Gaussian, independently
of its location. This extracts the middle-block factor in the record estimate. -/
theorem gaussian_unit_interval_le {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    gaussianReal 0 v (Ioc t (t+1)) ≤ ENNReal.ofReal (Real.sqrt (2*Real.pi*v))⁻¹ := by
  rw [gaussianReal_apply 0 hv]
  calc
    _ ≤ ∫⁻ _ : ℝ in Ioc t (t+1), ENNReal.ofReal (Real.sqrt (2*Real.pi*v))⁻¹ := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      show gaussianPDFReal 0 v x ≤ _
      rw [gaussianPDFReal]
      exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)))
    _ = _ := by simp [Real.volume_Ioc]

/-- A middle Gaussian block may be integrated out uniformly in a measurable shift
determined by both exterior blocks. -/
theorem middle_block_interval {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set α) (B : Set β) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (offset : α × β → ℝ) (hoff : Measurable offset) {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    ((μ.prod ν).prod (gaussianReal 0 v))
      {z | z.1.1 ∈ A ∧ z.1.2 ∈ B ∧ offset z.1 + z.2 ∈ Ioc t (t+1)} ≤
      (μ A * ν B) * ENNReal.ofReal (Real.sqrt (2*Real.pi*v))⁻¹ := by
  let E : Set ((α × β) × ℝ) := {z | z.1.1 ∈ A ∧ z.1.2 ∈ B ∧ offset z.1+z.2 ∈ Ioc t (t+1)}
  have hE : MeasurableSet E := (hA.preimage (measurable_fst.comp measurable_fst)).inter
    ((hB.preimage (measurable_snd.comp measurable_fst)).inter
      (measurableSet_Ioc.preimage ((hoff.comp measurable_fst).add measurable_snd)))
  change ((μ.prod ν).prod (gaussianReal 0 v)) E ≤ _
  rw [Measure.prod_apply hE]
  let c := ENNReal.ofReal (Real.sqrt (2*Real.pi*v))⁻¹
  calc
    _ ≤ ∫⁻ x : α×β, (A ×ˢ B).indicator (fun _ => c) x ∂μ.prod ν := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ A ×ˢ B
      · rw [Set.indicator_of_mem hx]
        apply le_trans _ (gaussian_unit_interval_le hv (t-offset x))
        apply measure_mono
        intro y hy
        rcases hy with ⟨_, _, h1, h2⟩
        exact ⟨by linarith, by linarith⟩
      · change gaussianReal 0 v (Prod.mk x ⁻¹' E) ≤ _
        rw [Set.indicator_of_notMem hx, show Prod.mk x ⁻¹' E = ∅ by
              ext y
              simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
              exact fun hy => hx ⟨hy.1, hy.2.1⟩]
        simp
    _ = _ := by rw [lintegral_indicator (hA.prod hB), setLIntegral_const, Measure.prod_prod, mul_comm]

end BrownianDiscrete
end
end

-- BrownianDiscreteBlocks
section
noncomputable section
open MeasureTheory ProbabilityTheory Set Fin.NatCast
open scoped NNReal ENNReal
namespace BrownianDiscrete

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem disjoint_samples {α β : Type*} [Fintype α] [Fintype β]
    {X : ℕ → Ω → ℝ} (hX : iIndepFun X P) (hm : ∀ i, AEMeasurable (X i) P)
    (f : α → ℕ) (g : β → ℕ) (hd : ∀ i j, f i ≠ g j) :
    IndepFun (fun ω i => X (f i) ω) (fun ω j => X (g j) ω) P := by
  let S := Finset.univ.image f
  let T := Finset.univ.image g
  have hs : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    rintro n hi hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j, _, e⟩ := Finset.mem_image.mp hj
    exact hd i j e.symm
  let F (v : S → ℝ) (i : α) := v ⟨f i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let G (v : T → ℝ) (j : β) := v ⟨g j, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  exact (hX.indepFun_finset₀ S T hs hm).comp (show Measurable F by fun_prop)
    (show Measurable G by fun_prop)

def centeredBlock (k : ℕ) : Measure (Fin k → ℝ) := Measure.pi fun _ => gaussianReal 0 1

instance (k : ℕ) : IsProbabilityMeasure (centeredBlock k) := by unfold centeredBlock; infer_instance

/-- Split n=k+b+k into two outer blocks and a middle block. The first block is negated,
the last reversed, and the middle recorded only through its displacement. -/
def firstBlock (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) (i : Fin k) := -X i.val ω
def lastBlock (X : ℕ → Ω → ℝ) (k b : ℕ) (ω : Ω) (i : Fin k) :=
  X (k+b+(k-1-i.val)) ω
def middleSum (X : ℕ → Ω → ℝ) (k b : ℕ) (ω : Ω) := ∑ i : Fin b, X (k+i.val) ω

omit [MeasurableSpace Ω] in
theorem middleSum_eq (B : ℝ≥0 → Ω → ℝ) (k b : ℕ) (ω : Ω) :
    middleSum (increment B 0) k b ω = B (k+b : ℕ) ω - B k ω := by
  unfold middleSum
  rw [Fin.sum_univ_eq_sum_range (fun i => increment B 0 (k+i) ω)]
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih]
    simp [increment, add_assoc]

theorem three_block_law [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (k b : ℕ) :
    HasLaw (fun ω => ((firstBlock (increment B 0) k ω, lastBlock (increment B 0) k b ω),
      middleSum (increment B 0) k b ω)) (((centeredBlock k).prod (centeredBlock k)).prod (gaussianReal 0 b)) P := by
  let X := increment B 0
  have hind : iIndepFun X P := by
    have h := hB.hasIndepIncrements.nat (t := fun i : ℕ => (i : ℝ≥0)) (fun i j h => by dsimp; exact_mod_cast h)
    change iIndepFun (fun (i : ℕ) (ω : Ω) => B ((i:ℝ≥0)+1) ω - B i ω - 0) P
    simpa using h
  have hX (i : ℕ) : HasLaw (X i) (gaussianReal 0 1) P := by
    simpa [X] using (increment_iid hB 0 (i+1)).2 (⟨i,by omega⟩ : Fin (i+1))
  let f (i : Fin k) := i.val
  let g (i : Fin k) := k+b+(k-1-i.val)
  let m (i : Fin b) := k+i.val
  have hfm (i : Fin k) (j : Fin b) : f i ≠ m j := by dsimp [f,m]; omega
  have hgm (i : Fin k) (j : Fin b) : g i ≠ m j := by dsimp [g,m]; omega
  have hfg (i j : Fin k) : f i ≠ g j := by dsimp [f,g]; omega
  have hgi : Function.Injective g := by intro i j h; apply Fin.ext; dsimp [g] at h; omega
  have hfirst : HasLaw (firstBlock X k) (centeredBlock k) P := by
    apply ((hind.precomp (g := f) Fin.val_injective).comp (fun _ x => -x) (fun _ => measurable_neg)).hasLaw_pi
    intro i
    change HasLaw (-X (f i)) (gaussianReal 0 1) P
    simpa using gaussianReal_neg (hX (f i))
  have hlast : HasLaw (lastBlock X k b) (centeredBlock k) P :=
    (hind.precomp hgi).hasLaw_pi (fun i => hX (g i))
  have hmid : HasLaw (middleSum X k b) (gaussianReal 0 b) P := by
    have hl := hB.hasLaw_sub (k+b : ℕ) k
    have hvar : nndist ((↑(k+b : ℕ) : ℝ≥0) : ℝ) ((k : ℝ≥0) : ℝ) = (b : ℝ≥0) := by
      apply NNReal.eq
      simp
    rw [show middleSum X k b = B (k+b : ℕ)-B k by ext ω; apply middleSum_eq, ← hvar]
    exact hl
  have hi₁ : IndepFun (firstBlock X k) (lastBlock X k b) P :=
    (disjoint_samples hind (fun i => (hX i).aemeasurable) f g hfg).comp
      (show Measurable (fun (x : Fin k → ℝ) i => -x i) by fun_prop) measurable_id
  let out := Sum.elim f g
  have him : ∀ i j, out i ≠ m j := by intro i j; cases i with | inl i => exact hfm i j | inr i => exact hgm i j
  have hi₂ : IndepFun (fun ω => (firstBlock X k ω,lastBlock X k b ω)) (middleSum X k b) P :=
    (disjoint_samples hind (fun i => (hX i).aemeasurable) out m him).comp
      (show Measurable (fun (v : (Fin k ⊕ Fin k) → ℝ) =>
        ((fun i => -v (.inl i)), (fun i => v (.inr i)))) by fun_prop)
      (show Measurable (fun v : Fin b → ℝ => ∑ i, v i) by fun_prop)
  exact hi₂.hasLaw_prod (hi₁.hasLaw_prod hfirst hlast) hmid

end BrownianDiscrete
end
end

-- BrownianDiscreteWindow
section
noncomputable section
open MeasureTheory ProbabilityTheory Set Fin.NatCast
open scoped NNReal ENNReal
namespace BrownianDiscrete

def aboveLevel (k : ℕ) [NeZero k] (h : ℝ) : Set (Fin k → ℝ) :=
  {v | ∀ i : Fin k, h < prefixSum v (i.val+1)}

theorem aboveLevel_measurable (k : ℕ) [NeZero k] (h : ℝ) : MeasurableSet (aboveLevel k h) := by
  rw [show aboveLevel k h = ⋂ i : Fin k, {v | h < prefixSum v (i.val+1)} by ext v; simp [aboveLevel]]
  apply MeasurableSet.iInter
  intro i
  apply measurableSet_lt measurable_const
  unfold prefixSum
  fun_prop

theorem firstBlock_prefix {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {k j : ℕ} [NeZero k] (hj : j ≤ k) (ω : Ω) :
    prefixSum (firstBlock (increment B 0) k ω) j = -(B j ω - B 0 ω) := by
  calc
    _ = -prefixSum (fun i : Fin k => increment B 0 i.val ω) j := by
      simp [prefixSum, firstBlock, Finset.sum_neg_distrib]
    _ = _ := by rw [prefixSum_increment hj]; ring

theorem lastBlock_prefix {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {k j : ℕ} [NeZero k] (hj : j ≤ k)
    (b : ℕ) (ω : Ω) :
    prefixSum (lastBlock (increment B 0) k b ω) j =
      B (k+b+k : ℕ) ω - B (k+b+k-j : ℕ) ω := by
  let a := k+b+k-j
  have haj : a+j = k+b+k := by dsimp [a]; omega
  calc
    _ = middleSum (increment B 0) a j ω := by
      unfold prefixSum middleSum
      rw [Fin.sum_univ_eq_sum_range (fun i => increment B 0 (a+i) ω),
        ← Finset.sum_range_reflect (fun i => increment B 0 (a+i) ω) j]
      apply Finset.sum_congr rfl
      intro i hi
      have hij := Finset.mem_range.mp hi
      have hcast : (i : Fin k).val = i := Fin.val_cast_of_lt (hij.trans_le hj)
      simp only [lastBlock, hcast]
      rw [show k+b+(k-1-i) = a+(j-1-i) by dsimp [a]; omega]
    _ = _ := by rw [middleSum_eq, haj]

/-- For n=k+b+k, localize the endpoint in a unit interval. The first k times obey
the shifted barrier, the final reversed k increments obey the zero barrier, and the
independent middle displacement has Gaussian density bounded by (2π b)^(-1/2). -/
theorem centered_record_window {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (k b : ℕ) [NeZero k] (hb : 0<b) [NeZero (k+b+k)] (t : ℝ) :
    centeredBlock (k+b+k) (recordSet (k+b+k) ∩
      (fun v => prefixSum v (k+b+k)) ⁻¹' Ioc t (t+1)) ≤
      (centeredBlock k (aboveLevel k (-(t+1))) * centeredBlock k (aboveLevel k 0)) *
        ENNReal.ofReal (Real.sqrt (2*Real.pi*(b:ℝ)))⁻¹ := by
  let n := k+b+k
  let X := increment B 0
  let W (ω : Ω) (i : Fin n) := X i.val ω
  let F := firstBlock X k
  let G := lastBlock X k b
  let M := middleSum X k b
  let A := aboveLevel k (-(t+1))
  let C := aboveLevel k 0
  let off (x : (Fin k → ℝ) × (Fin k → ℝ)) := -prefixSum x.1 k + prefixSum x.2 k
  have hmoff : Measurable off := by unfold off prefixSum; fun_prop
  let E := recordSet n ∩ (fun v => prefixSum v n) ⁻¹' Ioc t (t+1)
  have hmE : MeasurableSet E := (measurableSet_recordSet _).inter
    (measurableSet_Ioc.preimage (by unfold prefixSum; fun_prop))
  let H : Set (((Fin k → ℝ) × (Fin k → ℝ)) × ℝ) :=
    {z | z.1.1 ∈ A ∧ z.1.2 ∈ C ∧ off z.1 + z.2 ∈ Ioc t (t+1)}
  have hH : MeasurableSet H := ((aboveLevel_measurable _ _).preimage (measurable_fst.comp measurable_fst)).inter
    (((aboveLevel_measurable _ _).preimage (measurable_snd.comp measurable_fst)).inter
      (measurableSet_Ioc.preimage ((hmoff.comp measurable_fst).add measurable_snd)))
  have hW : HasLaw W (centeredBlock n) P := by
    obtain ⟨h₁,h₂⟩ := increment_iid hB 0 n
    simpa [W,X,centeredBlock] using h₁.hasLaw_pi h₂
  have hs : W ⁻¹' E ⊆ (fun ω => ((F ω,G ω), M ω)) ⁻¹' H := by
    intro ω hω
    have hp (j : ℕ) (hj : j≤n) : prefixSum (W ω) j = B j ω - B 0 ω := by
      simpa [W,X] using prefixSum_increment (B:=B) (d:=0) hj ω
    have hwe := hω.2
    change prefixSum (W ω) n ∈ Ioc t (t+1) at hwe
    rw [hp _ le_rfl] at hwe
    have hr (j : ℕ) (hj : j<n) : B j ω - B 0 ω < B n ω - B 0 ω := by
      have hh := hω.1 j hj
      change prefixSum (W ω) j < prefixSum (W ω) n at hh
      rwa [hp _ hj.le, hp _ le_rfl] at hh
    refine ⟨?_, ?_, ?_⟩
    · intro i
      change -(t+1) < prefixSum (firstBlock (increment B 0) k ω) (i.val+1)
      rw [firstBlock_prefix B i.isLt]
      have h := hr (i.val+1) (by dsimp [n]; omega)
      linarith [hwe.2]
    · intro i
      change 0 < prefixSum (lastBlock (increment B 0) k b ω) (i.val+1)
      rw [lastBlock_prefix B i.isLt]
      have h := hr (n-(i.val+1)) (by dsimp [n]; omega)
      dsimp [n] at h
      linarith
    · change -prefixSum (firstBlock X k ω) k + prefixSum (lastBlock X k b ω) k + middleSum X k b ω ∈ _
      dsimp [X]
      rw [firstBlock_prefix B le_rfl, lastBlock_prefix B le_rfl, middleSum_eq,
        show k+b+k-k = k+b by omega]
      convert hwe using 1 <;> dsimp [n] <;> ring
  calc
    _ = P (W ⁻¹' E) := (hW.measure_eq (p:=(·∈E)) hmE).symm
    _ ≤ P ((fun ω => ((F ω,G ω), M ω)) ⁻¹' H) := measure_mono hs
    _ = _ := (three_block_law hB k b).measure_eq (p:=(·∈H)) hH
    _ ≤ _ := middle_block_interval (centeredBlock k) (centeredBlock k) A C
      (aboveLevel_measurable _ _) (aboveLevel_measurable _ _) off hmoff
      (show (b:ℝ≥0) ≠ 0 by exact_mod_cast hb.ne') t

end BrownianDiscrete
end
end

-- BrownianDiscreteRecordUpper
section
noncomputable section
open MeasureTheory ProbabilityTheory Set Fin.NatCast
open scoped ENNReal NNReal
namespace BrownianDiscrete

def endpointWindow (n : ℕ) [NeZero n] (j : ℕ) : Set (Fin n → ℝ) :=
  recordSet n ∩ (fun v => prefixSum v n) ⁻¹' Ioc (j : ℝ) (j+1)

theorem endpointWindow_measurable (n j : ℕ) [NeZero n] : MeasurableSet (endpointWindow n j) :=
  (measurableSet_recordSet n).inter (measurableSet_Ioc.preimage (by unfold prefixSum; fun_prop))

theorem measure_drifted_record_le (n : ℕ) [NeZero n] {d : ℝ} (hd : 0 < d) :
    (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)) (recordSet n) ≤
      ENNReal.ofReal (Real.exp (-(d^2/2)*n)) *
        ∑' j : ℕ, ENNReal.ofReal (Real.exp (-d*j)) * centeredBlock n (endpointWindow n j) := by
  have hsum (v : Fin n → ℝ) : (∑ i, v i) = prefixSum v n := by
    unfold prefixSum
    simpa using Fin.sum_univ_eq_sum_range (fun i => v (i : Fin n)) n
  have hsub : recordSet n ⊆ ⋃ j : ℕ, endpointWindow n j := by
    intro v hv
    have hp : 0 < prefixSum v n := by simpa [prefixSum] using hv 0 (NeZero.pos n)
    let j := ⌈prefixSum v n⌉₊-1
    have hj : j+1 = ⌈prefixSum v n⌉₊ := Nat.sub_add_cancel (Nat.one_le_ceil_iff.mpr hp)
    have hl : j < ⌈prefixSum v n⌉₊ := by omega
    have hu : prefixSum v n ≤ (j:ℝ)+1 := by
      simpa only [← hj, Nat.cast_add, Nat.cast_one] using Nat.le_ceil (prefixSum v n)
    exact mem_iUnion.mpr ⟨j, hv, Nat.lt_ceil.mp hl, hu⟩
  rw [← ENNReal.tsum_mul_left]
  refine (measure_mono hsub).trans ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => ?_))
  rw [gaussianProduct_drift, withDensity_apply _ (endpointWindow_measurable n j)]
  let c := ENNReal.ofReal (Real.exp (-(d^2/2)*n - d*j))
  calc
    _ ≤ ∫⁻ _ in endpointWindow n j, c ∂centeredBlock n := by
      apply setLIntegral_mono measurable_const
      intro v hv
      change ENNReal.ofReal (Real.exp _) ≤ ENNReal.ofReal (Real.exp _)
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      rw [hsum]
      nlinarith [mul_pos hd (sub_pos.mpr hv.2.1)]
    _ = c * centeredBlock n (endpointWindow n j) := setLIntegral_const _ _
    _ = _ := by
      unfold c
      rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
      simp [neg_mul, mul_assoc]

/-- A positive signed maximum time is a strict record on the sampled positive arm.
Gaussian increments have no atoms, so the weak maximizing hypothesis suffices. -/
theorem signed_atom_le_record {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ → Ω → ℝ} (hB : IsPreBrownianReal (fun t : ℝ≥0 => B (t:ℝ)) P)
    {d : ℝ} (D : Ω → ℤ)
    (hD : ∀ᵐ ω ∂P, ∀ k : ℤ, OMA.S_mo_142880.height B d k ω ≤ OMA.S_mo_142880.height B d (D ω) ω)
    (n : ℕ) [NeZero n] :
    P {ω | D ω = n} ≤ (Measure.pi fun _ : Fin n => gaussianReal (-d) 1) (recordSet n) := by
  let R (t : ℝ≥0) := B (t:ℝ)
  let W (ω : Ω) (i : Fin n) := increment R d i.val ω
  obtain ⟨hi,hm⟩ := increment_iid hB d n
  have hW : HasLaw W (Measure.pi fun _ : Fin n => gaussianReal (-d) 1) P := hi.hasLaw_pi hm
  have hdiff (i : Fin n) : ∀ᵐ ω ∂P, R n ω - R i.val ω ≠ d*n - d*i.val := by
    let v := nndist ((n:ℝ≥0):ℝ) ((i.val:ℝ≥0):ℝ)
    have hv : v ≠ 0 := by
      dsimp [v]
      rw [nndist_eq_zero]
      exact_mod_cast i.isLt.ne'
    let : NullSingletonClass (gaussianReal 0 v) := nullSingletonClass_gaussianReal hv
    have hl := hB.hasLaw_sub (n : ℝ≥0) (i.val : ℝ≥0)
    exact (hl.ae_iff (p := fun x : ℝ => x ≠ d*n-d*i.val) (by fun_prop)).mpr
      ((gaussianReal 0 v).ae_ne _)
  apply le_trans _ (hW.measure_eq (p := (·∈ recordSet n)) (measurableSet_recordSet n)).le
  apply measure_mono_ae
  filter_upwards [hD, ae_all_iff.mpr hdiff] with ω hmax hne he
  intro j hj
  change D ω = n at he
  specialize hmax (j:ℤ)
  rw [he] at hmax
  have hle : R j ω - d*j ≤ R n ω - d*n := by simpa [R, OMA.S_mo_142880.height] using hmax
  have hne' := hne (⟨j,hj⟩ : Fin n)
  change R n ω-R j ω ≠ d*n-d*j at hne'
  change prefixSum (fun i : Fin n => increment R d i.val ω) j <
    prefixSum (fun i : Fin n => increment R d i.val ω) n
  rw [prefixSum_increment hj.le, prefixSum_increment le_rfl]
  exact lt_of_le_of_ne (by linarith) (by intro hh; apply hne'; linarith)

end BrownianDiscrete
end
end

-- BrownianDiscreteUpperJoin
section
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal
namespace BrownianDiscrete

theorem weight_eq_inv_sqrt {n : ℕ} (hn : 0<n) : weight n = ((n:ℝ)*√(n:ℝ))⁻¹ := by
  have h : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [weight, Real.rpow_neg h.le, Real.sqrt_eq_rpow,
    show (3/2:ℝ) = 1+1/2 by norm_num, Real.rpow_add h, Real.rpow_one]

theorem block_factor {n k b : ℕ} (hn : 0<n) (hk : n ≤ 3*(k+1)) (hb : n ≤ 3*b) :
    1/(((k:ℝ)+1)*√(2*Real.pi*b)) ≤ 6*weight n := by
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn
  have hb' : 0<(b:ℝ) := by exact_mod_cast (show 0<b by omega)
  have hk' : (n:ℝ) ≤ 3*((k:ℝ)+1) := by exact_mod_cast hk
  have hn3 : (n:ℝ) ≤ 3*b := by exact_mod_cast hb
  have hs : √(n:ℝ) ≤ 2*√(2*Real.pi*b) := by
    have hp : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
    have h1 : (n:ℝ) ≤ 4*(2*Real.pi*b) := by nlinarith [mul_le_mul_of_nonneg_right hp hb'.le]
    rw [← Real.sqrt_sq (show 0 ≤ 2*√(2*Real.pi*b) by positivity)]
    apply Real.sqrt_le_sqrt
    nlinarith [Real.sq_sqrt (show 0 ≤ 2*Real.pi*b by positivity)]
  rw [weight_eq_inv_sqrt hn, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h := mul_le_mul hk' hs (Real.sqrt_nonneg _) (by positivity)
  nlinarith

def windowWeight (d : ℝ) (j : ℕ) := Real.exp (-d*j) * ((j:ℝ)+2)^2

theorem windowWeight_summable {d : ℝ} (hd : 0<d) : Summable (windowWeight d) := by
  let r := Real.exp (-d)
  have hr : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hd)
  have h₂ := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have h₁ := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h₀ := summable_geometric_of_lt_one (Real.exp_pos (-d)).le (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hd))
  apply ((h₂.add (h₁.mul_left 4)).add (h₀.mul_left 4)).congr
  intro j
  dsimp [windowWeight, r]
  rw [show -d*(j:ℝ)=(j:ℝ)*(-d) by ring, Real.exp_nat_mul]
  ring

theorem centered_window_large {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {C : ℝ} (hC : 0≤C)
    (hzero : ∀ (k : ℕ) [NeZero k], (centeredBlock k).real (aboveLevel k 0) ≤ 1/√((k:ℝ)+1))
    (hbar : ∀ (k : ℕ) [NeZero k] (j : ℕ), (centeredBlock k).real (aboveLevel k (-(j+1:ℝ))) ≤
      C*((j:ℝ)+2)^2/√((k:ℝ)+1)) {n : ℕ} [NeZero n] (hn : 3≤n) (j : ℕ) :
    centeredBlock n (endpointWindow n j) ≤ ENNReal.ofReal (6*C*((j:ℝ)+2)^2*weight n) := by
  let k := n/3
  let b := n-2*k
  have hk : 0<k := by dsimp [k]; omega
  let : NeZero k := ⟨hk.ne'⟩
  have hb : 0<b := by dsimp [b,k]; omega
  have hkb : n=k+b+k := by dsimp [b,k]; omega
  have h₀ := hzero k
  have h₁ := hbar k j
  have hf := block_factor (n := n) (k := k) (b := b) (by omega) (by dsimp [k]; omega) (by dsimp [b,k]; omega)
  have hfirst : centeredBlock k (aboveLevel k (-(j+1:ℝ))) ≤ ENNReal.ofReal (C*((j:ℝ)+2)^2/√((k:ℝ)+1)) := by
    rwa [← ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_le_ofReal_iff (by positivity)]
  have hlast : centeredBlock k (aboveLevel k 0) ≤ ENNReal.ofReal (1/√((k:ℝ)+1)) := by
    rwa [← ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_le_ofReal_iff (by positivity)]
  let : NeZero (k+b+k) := ⟨by omega⟩
  have hwin := centered_record_window hB k b hb (j:ℝ)
  change centeredBlock (k+b+k) (endpointWindow (k+b+k) j) ≤ _ at hwin
  have hrepl (s m : ℕ) [NeZero s] [NeZero m] (h : s=m) :
      centeredBlock s (endpointWindow s j) = centeredBlock m (endpointWindow m j) := by subst m; rfl
  rw [hrepl n (k+b+k) hkb]
  apply hwin.trans
  apply le_trans (b := ENNReal.ofReal (C*((j:ℝ)+2)^2/√((k:ℝ)+1)) * ENNReal.ofReal (1/√((k:ℝ)+1)) * ENNReal.ofReal (√(2*Real.pi*(b:ℝ)))⁻¹)
  · gcongr
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he : (C*((j:ℝ)+2)^2/√((k:ℝ)+1) * (1/√((k:ℝ)+1))) * (√(2*Real.pi*b))⁻¹ =
        C*((j:ℝ)+2)^2 * (1/(((k:ℝ)+1)*√(2*Real.pi*b))) := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by positivity : 0 ≤ (k:ℝ)+1)]
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [he]
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left hf (by positivity)
    _ = _ := by ring

end BrownianDiscrete
end
end

-- BrownianBarrier
section
open MeasureTheory ProbabilityTheory Set
open OMA.S_mo_142880

namespace BrownianComparison

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Chernoff's bound for crossing a line at one fixed time. -/
theorem eval_barrier {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : NNReal) {d : ℝ} (hd : 0 ≤ d) (z : ℝ) :
    P.real {ω | z + d * (t : ℝ) ≤ B t ω} ≤ Real.exp (-d*z - (d^2/2)*t) := by
  have hm := mgf_gaussianReal (hB.hasLaw_eval t).map_eq d
  have hi : Integrable (fun ω => Real.exp (d * B t ω)) P := by
    rw [← mgf_pos_iff, hm]
    exact Real.exp_pos _
  calc
    _ ≤ _ := measure_ge_le_exp_mul_mgf (z + d * (t : ℝ)) hd hi
    _ = _ := by rw [hm, ← Real.exp_add]; congr 1; ring

/-- A union bound over all lattice observations starting at N. -/
theorem discrete_barrier {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {d : ℝ} (hd : 0 < d) (z : ℝ) (N : ℕ) :
    P (⋃ k : ℕ, {ω | z + d * (N + k : ℕ) ≤ B (N + k : ℕ) ω}) ≤
      ENNReal.ofReal (Real.exp (-d*z - (d^2/2)*N) / (1 - Real.exp (-(d^2/2)))) := by
  let r := Real.exp (-(d^2/2))
  let A := Real.exp (-d*z - (d^2/2)*N)
  have hr₀ : 0 ≤ r := (Real.exp_pos _).le
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [sq_pos_of_pos hd])
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hsum : Summable (fun k : ℕ => A * r ^ k) := (summable_geometric_of_lt_one hr₀ hr₁).mul_left A
  calc
    _ ≤ _ := measure_iUnion_le _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (A * r^k) := by
      apply ENNReal.tsum_le_tsum
      intro k
      rw [← ofReal_measureReal (μ := P)]
      apply ENNReal.ofReal_le_ofReal
      have he := eval_barrier hB ((N+k : ℕ) : NNReal) hd.le z
      calc
        _ ≤ Real.exp (-d*z - (d^2/2)*((N : ℝ) + k)) := by simpa using he
        _ = _ := by
          change _ = Real.exp _ * Real.exp _ ^ k
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          ring
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hA (pow_nonneg hr₀ k)) hsum,
        tsum_mul_left, tsum_geometric_of_lt_one hr₀ hr₁, div_eq_mul_inv]

/-- An unconditional exponential upper bound for the signed lattice argmax. -/
theorem discrete_argmax_upper {B : ℝ → Ω → ℝ} {d : ℝ} (hd : 0 < d)
    (hB : IsPreBrownianReal (fun t : NNReal => B (t : ℝ)) P)
    {D : Ω → ℤ}
    (hD : ∀ᵐ ω ∂P, ∀ n : ℤ, height B d n ω ≤ height B d (D ω) ω) (N : ℕ) :
    P {ω | (N : ℤ) ≤ D ω} ≤ ENNReal.ofReal
      (Real.exp (-(d^2/2)*(N : ℝ)) / (1 - Real.exp (-(d^2/2)))) := by
  apply le_trans (measure_mono_ae (t := ⋃ k : ℕ,
    {ω | 0 + d * (N + k : ℕ) ≤ B ((N + k : ℕ) : ℝ) ω}) ?_)
  · simpa using discrete_barrier hB hd 0 N
  filter_upwards [hD, hB.eval_zero_ae_eq_zero] with ω hω hzero
  intro hN
  change (N : ℤ) ≤ D ω at hN
  have heq : D ω = (↑(N + ((D ω).toNat - N)) : ℤ) := by omega
  refine mem_iUnion.mpr ⟨(D ω).toNat - N, ?_⟩
  have hx := hω 0
  have hz : B 0 ω = 0 := hzero
  rw [heq] at hx
  simpa [height, hz, sub_nonneg, abs_of_nonneg (show 0 ≤ (N : ℝ) + ((D ω).toNat - N : ℕ) by positivity)] using hx

end BrownianComparison
end

-- BrownianSurvival
section
open MeasureTheory ProbabilityTheory Set

namespace BrownianComparison

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A measurable event on path space, specified only at lattice times. -/
def belowLine (z d : ℝ) : Set (NNReal → ℝ) :=
  ⋂ k : ℕ, {f | f (k : NNReal) < z + d * (k : ℝ)}

theorem belowLine_measurable (z d : ℝ) : MeasurableSet (belowLine z d) :=
  MeasurableSet.iInter fun k => measurableSet_lt (measurable_pi_apply (k : NNReal)) measurable_const

theorem exists_buffer {d : ℝ} (hd : 0 < d) :
    ∃ z : ℝ, ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : NNReal → Ω → ℝ), IsPreBrownianReal B P →
      (1/2 : ENNReal) ≤ P ((fun ω t => B t ω) ⁻¹' belowLine z d) := by
  let r := Real.exp (-(d^2 / 2))
  have hr : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [sq_pos_of_pos hd])
  let z := -(Real.log ((1 - r) / 2)) / d
  have ez : Real.exp (-d * z) = (1-r)/2 := by
    dsimp only [z]
    rw [show -d * (-Real.log ((1-r)/2) / d) = Real.log ((1-r)/2) by field_simp]
    exact Real.exp_log (by linarith)
  refine ⟨z, ?_⟩
  intro Ω m P hP B hB
  let A : Set Ω := ⋃ k : ℕ, {ω | z + d * (k : ℝ) ≤ B (k : NNReal) ω}
  have hA : NullMeasurableSet A P :=
    NullMeasurableSet.iUnion fun k => nullMeasurableSet_le aemeasurable_const (hB.aemeasurable _)
  have hbound : P A ≤ ENNReal.ofReal ((1-r) / 2 / (1-r)) := by
    have ez' : Real.exp (-(d*z)) = (1-r)/2 := by simpa using ez
    simpa [A, ez', r] using discrete_barrier hB hd z 0
  have hh : (1-r)/2/(1-r) = (1/2 : ℝ) := by field_simp [ne_of_gt (sub_pos.mpr hr)]
  rw [hh] at hbound
  have hhalf : P A ≤ (1/2 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_one,
      show ENNReal.ofReal (2 : ℝ) = 2 by norm_num] at hbound
    exact hbound
  have hcompl : ((fun ω t => B t ω) ⁻¹' belowLine z d) = Aᶜ := by
    ext ω
    simp [A, belowLine]
  rw [hcompl, prob_compl_eq_one_sub₀ hA]
  calc
    (1/2 : ENNReal) = 1 - 1/2 := by norm_num
    _ ≤ _ := tsub_le_tsub_left hhalf _

/-- A strictly positive lower bound, uniform over versions, for the probability
that every positive integer observation of a negatively drifted arm is negative. -/
theorem discrete_survival_uniform {d : ℝ} (hd : 0 < d) :
    ∃ p : ENNReal, 0 < p ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : NNReal → Ω → ℝ), IsPreBrownianReal B P →
        p ≤ P {ω | ∀ k : ℕ, B (k + 1) ω < d * ((k : ℝ) + 1)} := by
  obtain ⟨z, hz⟩ := exists_buffer hd
  let c := gaussianReal 0 1 (Iio (d-z))
  have hc : 0 < c := by
    apply pos_iff_ne_zero.mpr
    intro h
    have hv := gaussianReal_absolutelyContinuous' 0 (one_ne_zero : (1 : NNReal) ≠ 0) h
    simp at hv
  refine ⟨(1/2) * c, ENNReal.mul_pos (by norm_num) hc.ne', ?_⟩
  intro Ω m P hP B hB
  let X := fun ω (t : NNReal) => B (1+t) ω - B 1 ω
  let Y := fun ω (t : Iic (1 : NNReal)) => B t ω
  let F : Set (Iic (1 : NNReal) → ℝ) := {f | f ⟨1, by simp⟩ < d-z}
  have hF : MeasurableSet F := measurableSet_lt (measurable_pi_apply _) measurable_const
  have hmass : P (Y ⁻¹' F) = c :=
    (hB.hasLaw_eval 1).measure_eq (p := fun x => x < d-z) measurableSet_Iio
  have hprod : P (X ⁻¹' belowLine z d ∩ Y ⁻¹' F) =
      P (X ⁻¹' belowLine z d) * P (Y ⁻¹' F) :=
    (hB.indepFun_shift 1).measure_inter_preimage_eq_mul _ _ (belowLine_measurable _ _) hF
  calc
    _ ≤ P (X ⁻¹' belowLine z d) * P (Y ⁻¹' F) := by
      rw [hmass]
      simpa only [mul_comm c] using mul_le_mul_right (hz Ω P _ (hB.shift 1)) c
    _ = _ := hprod.symm
    _ ≤ _ := by
      apply measure_mono
      intro ω hw k
      have h1 : B 1 ω < d-z := hw.2
      have h2 := Set.mem_iInter.mp hw.1 k
      change B (1 + (k : NNReal)) ω - B 1 ω < z + d * (k : ℝ) at h2
      rw [add_comm] at h2
      linarith

end BrownianComparison
end

-- BrownianDiscreteAtoms
section
noncomputable section
open MeasureTheory ProbabilityTheory Set OMA.S_mo_142880
open scoped NNReal ENNReal
namespace BrownianDiscrete

def survives (d : ℝ) : Set (ℝ≥0 → ℝ) :=
  {f | ∀ k : ℕ, f (k+1) < d*((k:ℝ)+1)}

theorem measurable_survives (d : ℝ) : MeasurableSet (survives d) := by
  rw [show survives d = ⋂ k : ℕ, {f | f (k+1) < d*((k:ℝ)+1)} by ext f; simp [survives]]
  exact MeasurableSet.iInter (fun _ => measurableSet_lt (measurable_pi_apply _) measurable_const)

def recordOnPast (d : ℝ) (n : ℕ) : Set (Iic (n : ℝ≥0) → ℝ) :=
  {f | ∀ k : Fin n,
    f ⟨(k.val : ℝ≥0), by change (k.val : ℝ≥0) ≤ (n : ℝ≥0); exact_mod_cast k.isLt.le⟩ - d*k.val < f ⟨(n : ℝ≥0), Set.mem_Iic.mpr le_rfl⟩ - d*n}

theorem measurable_recordOnPast (d : ℝ) (n : ℕ) : MeasurableSet (recordOnPast d n) := by
  rw [show recordOnPast d n = ⋂ k : Fin n, {f | f ⟨(k.val : ℝ≥0), by change (k.val : ℝ≥0) ≤ (n : ℝ≥0); exact_mod_cast k.isLt.le⟩ -
      d*k.val < f ⟨(n : ℝ≥0), Set.mem_Iic.mpr le_rfl⟩ - d*n} by ext f; simp [recordOnPast]]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_lt ((measurable_pi_apply _).sub measurable_const)
    ((measurable_pi_apply _).sub measurable_const)

def winsArm (d : ℝ) (n : ℕ) : Set (ℝ≥0 → ℝ) :=
  (fun f t => f (n+t)-f n) ⁻¹' survives d ∩
    (fun f (t : Iic (n : ℝ≥0)) => f t.val) ⁻¹' recordOnPast d n

theorem measurable_winsArm (d : ℝ) (n : ℕ) : MeasurableSet (winsArm d n) :=
  ((measurable_survives d).preimage (by fun_prop)).inter
    ((measurable_recordOnPast d n).preimage (by fun_prop))

theorem winsArm_mass {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {R : ℝ≥0 → Ω → ℝ} (hR : IsPreBrownianReal R P) (d : ℝ) (n : ℕ) :
    P.real ((fun ω t => R t ω) ⁻¹' winsArm d n) =
    P.real ((fun ω t => R (n+t) ω-R n ω) ⁻¹' survives d) *
      P.real {ω | ∀ k < n, R k ω - d*k < R n ω - d*n} := by
  have h := (hR.indepFun_shift n).measure_inter_preimage_eq_mul _ _
    (measurable_survives d) (measurable_recordOnPast d n)
  let future := (fun ω (t : ℝ≥0) => R (n+t) ω-R n ω) ⁻¹' survives d
  let past := (fun ω (t : Iic (n : ℝ≥0)) => R t.val ω) ⁻¹' recordOnPast d n
  change (P (future ∩ past)).toReal = _
  change P (future ∩ past) = P future * P past at h
  rw [h, ENNReal.toReal_mul]
  have hset : past = {ω | ∀ k<n, R k ω-d*k < R n ω-d*n} := by
    ext ω
    change (∀ k : Fin n, R k.val ω - d*k.val < R n ω - d*n) ↔ _
    exact ⟨fun h k hk => h ⟨k,hk⟩, fun h k => h k.val k.isLt⟩
  rw [hset]
  rfl

theorem winner_eq {Ω : Type*} {B : ℝ → Ω → ℝ} {d : ℝ} {n : ℕ} (hn : 0<n) {ω : Ω} {D : ℤ}
    (h0 : B 0 ω = 0)
    (hwin : (fun t : ℝ≥0 => B t ω) ∈ winsArm d n)
    (hneg : (fun t : ℝ≥0 => B (-(t:ℝ)) ω) ∈ survives d)
    (hmax : ∀ k : ℤ, height B d k ω ≤ height B d D ω) : D = n := by
  have hprev (k : ℕ) (hk : k<n) : B k ω - d*k < B n ω - d*n := by
    exact hwin.2 (⟨k,hk⟩ : Fin n)
  have hnext (k : ℕ) : B ((n : ℝ)+(k+1)) ω - B n ω < d*((k:ℝ)+1) := by
    simpa using hwin.1 k
  have hnpos : 0 < B n ω - d*n := by simpa [h0] using hprev 0 hn
  specialize hmax (n : ℤ)
  cases D with
  | ofNat k =>
    have hm : B n ω-d*n ≤ B k ω-d*k := by simpa [height] using hmax
    rcases lt_trichotomy k n with h | h | h
    · exact False.elim (not_lt_of_ge hm (hprev k h))
    · simp [h]
    · let j := k-n-1
      have hj : k = n+(j+1) := by dsimp [j]; omega
      have hj' : (k:ℝ) = n+((j:ℝ)+1) := by exact_mod_cast hj
      have hh := hnext j
      rw [← hj'] at hh
      nlinarith [congrArg (fun x : ℝ => d*x) hj']
  | negSucc k =>
    have hneg' : B (-(k+1:ℝ)) ω < d*((k:ℝ)+1) := by simpa using hneg k
    have hm : B n ω - d*n ≤ B (-(k+1:ℝ)) ω - d*((k:ℝ)+1) := by
      simpa [height, Int.cast_negSucc, abs_of_nonpos (show -1 + -(k:ℝ) ≤ 0 by linarith [Nat.cast_nonneg (α:=ℝ) k])] using hmax
    linarith

/-- Uniform lower local mass of the signed discrete maximizer, with the sharp
power and exponential rate. The proof uses cyclic shifts and two survival events. -/
theorem signed_atom_lower {d : ℝ} (hd : 0 < d) :
    ∃ c : ℝ, 0<c ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ → Ω → ℝ),
      IsPreBrownianReal (fun t : ℝ≥0 => B t) P →
      IsPreBrownianReal (fun t : ℝ≥0 => B (-(t:ℝ))) P →
      IndepFun (fun ω (t : ℝ≥0) => B t ω) (fun ω (t : ℝ≥0) => B (-(t:ℝ)) ω) P →
      ∀ D : Ω → ℤ, (∀ᵐ ω ∂P, ∀ k : ℤ, height B d k ω ≤ height B d (D ω) ω) →
      ∀ n : ℕ, 0<n → c*weight n*Real.exp (-(d^2/2)*n) ≤ P.real {ω | D ω = n} := by
  obtain ⟨p, hp, hsurv⟩ := BrownianComparison.discrete_survival_uniform hd
  let a := (min p 1).toReal
  have ha : 0<a := ENNReal.toReal_pos (lt_min hp zero_lt_one).ne' (lt_of_le_of_lt (min_le_right ..) ENNReal.one_lt_top).ne
  let L := Real.exp (-d-1/2)/Real.sqrt (2*Real.pi)
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨a^2*L, by positivity, ?_⟩
  intro Ω mΩ P hP B hR hLft hindep D hD n hn
  let R := fun (t : ℝ≥0) => B t
  let E := fun (t : ℝ≥0) => B (-(t:ℝ))
  have hpr (Y : ℝ≥0 → Ω → ℝ) (hY : IsPreBrownianReal Y P) :
      a ≤ P.real ((fun ω t => Y t ω) ⁻¹' survives d) :=
    ENNReal.toReal_mono (measure_ne_top _ _) ((min_le_left ..).trans (hsurv Ω P Y hY))
  have hleft := hpr E hLft
  have hfuture := hpr _ (hR.shift n)
  let recMass := P.real {ω | ∀ k<n, R k ω-d*k < R n ω-d*n}
  have rec_nonneg : 0 ≤ recMass := measureReal_nonneg
  have hrec : L*weight n*Real.exp (-(d^2/2)*n) ≤ recMass := by
    have h₁ := (tiltedIncrement_bounds hR hd n).1
    have h₂ := drifted_record_lower hR d hn
    have hex : Real.exp (d^2/2*n)*Real.exp (-(d^2/2)*n) = 1 := by rw [← Real.exp_add]; ring_nf; simp
    calc
      _ ≤ tiltedIncrement P R d n * Real.exp (-(d^2/2)*n) :=
        mul_le_mul_of_nonneg_right h₁ (Real.exp_pos _).le
      _ = P.real {ω | 0 < R n ω - d*n}/n := by
        unfold tiltedIncrement
        calc
          _ = (Real.exp (d^2/2*n)*Real.exp (-(d^2/2)*n))*(P.real {ω | 0 < R n ω - d*n}/n) := by ring
          _ = _ := by rw [hex, one_mul]
      _ ≤ _ := h₂
  have hwin : a*recMass ≤ P.real ((fun ω t => R t ω) ⁻¹' winsArm d n) := by
    rw [winsArm_mass hR]
    exact mul_le_mul_of_nonneg_right hfuture rec_nonneg
  have hprod := hindep.measure_inter_preimage_eq_mul _ _ (measurable_winsArm d n) (measurable_survives d)
  have hsubset : ∀ᵐ ω ∂P, ω ∈ ((fun ω t => R t ω) ⁻¹' winsArm d n ∩ (fun ω t => E t ω) ⁻¹' survives d) → D ω = n := by
    filter_upwards [hD, hR.eval_zero_ae_eq_zero] with ω hw h0 hω
    exact winner_eq hn h0 hω.1 hω.2 hw
  calc
    _ = a*(L*weight n*Real.exp (-(d^2/2)*n))*a := by ring
    _ ≤ (a*recMass)*a := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrec ha.le) ha.le
    _ ≤ P.real ((fun ω t => R t ω) ⁻¹' winsArm d n) * P.real ((fun ω t => E t ω) ⁻¹' survives d) :=
      mul_le_mul hwin hleft ha.le measureReal_nonneg
    _ = P.real ((fun ω t => R t ω) ⁻¹' winsArm d n ∩ (fun ω t => E t ω) ⁻¹' survives d) := by
      simp only [measureReal_def, ← ENNReal.toReal_mul]
      exact congrArg ENNReal.toReal hprod.symm
    _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)

/-- The right tail of the discrete maximizer has the sharp lower envelope uniformly
over all versions admitted by the platform statement, including nonintegral thresholds. -/
theorem signed_tail_lower {d : ℝ} (hd : 0 < d) :
    ∃ c : ℝ, 0<c ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ → Ω → ℝ), IsPreBrownianReal (fun t : ℝ≥0 => B (t : ℝ)) P →
      IsPreBrownianReal (fun t : ℝ≥0 => B (-(t:ℝ))) P →
      IndepFun (fun ω (t : ℝ≥0) => B (t:ℝ) ω) (fun ω (t : ℝ≥0) => B (-(t:ℝ)) ω) P →
      ∀ (D : Ω → ℤ), (∀ᵐ ω ∂P, ∀ k : ℤ, height B d k ω ≤ height B d (D ω) ω) →
      ∀ t : ℝ, 0≤t → c * envelope (d^2/2) t ≤ P.real {ω | t < (D ω : ℝ)} := by
  obtain ⟨a, ha, hatom⟩ := signed_atom_lower hd
  let q := d^2/2
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨a*Real.exp (-q), by positivity, ?_⟩
  intro Ω mΩ P hP B hR hL hindep D hD t ht
  let m := ⌊t⌋₊+1
  have hm : 0<m := Nat.zero_lt_succ _
  have hm' : 0<(m : ℝ) := by exact_mod_cast hm
  have ht_m : t < (m : ℝ) := by simpa [m] using Nat.lt_floor_add_one t
  have hm_t : (m : ℝ) ≤ 1+t := by dsimp [m]; push_cast; linarith [Nat.floor_le ht]
  have hw : (1+t)^(-(3/2:ℝ)) ≤ weight m := Real.rpow_le_rpow_of_nonpos hm' hm_t (by norm_num)
  have he : Real.exp (-q) * Real.exp (-q*t) ≤ Real.exp (-q*m) := by
    rw [← Real.exp_add, Real.exp_le_exp]; nlinarith
  calc
    _ = (a*((1+t)^(-(3/2:ℝ))))*(Real.exp (-q)*Real.exp (-q*t)) := by unfold envelope q; ring
    _ ≤ a*weight m*Real.exp (-q*m) := mul_le_mul (mul_le_mul_of_nonneg_left hw ha.le) he
      (by positivity) (mul_nonneg ha.le (weight_nonneg m))
    _ ≤ P.real {ω | D ω = m} := hatom Ω P B hR hL hindep D hD m hm
    _ ≤ _ := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro ω hω
      change t < (D ω : ℝ)
      change D ω = m at hω
      simpa [hω] using ht_m

end BrownianDiscrete
end
end

-- BrownianDiscreteUpper
section
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal
namespace BrownianDiscrete

def upperConstant (C d : ℝ) :=
  max (4*Real.exp (2*(d^2/2))) (6*C*∑' j : ℕ, Real.exp (-d*j)*((j:ℝ)+2)^2)

theorem upperConstant_pos (C d : ℝ) : 0 < upperConstant C d :=
  (show 0 < 4*Real.exp (2*(d^2/2)) by positivity).trans_le (le_max_left ..)

theorem signed_atom_upper_of_persistence {d C : ℝ} (hd : 0<d) (hC : 0≤C)
    (hzero : ∀ (k : ℕ) [NeZero k], (centeredBlock k).real (aboveLevel k 0) ≤ 1/√((k:ℝ)+1))
    (hbar : ∀ (k : ℕ) [NeZero k] (j : ℕ), (centeredBlock k).real (aboveLevel k (-(j+1:ℝ))) ≤
      C*((j:ℝ)+2)^2/√((k:ℝ)+1))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ → Ω → ℝ}
    (hB : IsPreBrownianReal (fun t : ℝ≥0 => B (t:ℝ)) P) (D : Ω → ℤ)
    (hD : ∀ᵐ ω ∂P, ∀ k : ℤ, OMA.S_mo_142880.height B d k ω ≤ OMA.S_mo_142880.height B d (D ω) ω)
    {n : ℕ} (hn : 0<n) :
    P.real {ω | D ω = n} ≤ upperConstant C d * weight n * Real.exp (-(d^2/2)*n) := by
  let : NeZero n := ⟨hn.ne'⟩
  let q := d^2/2
  have hq : 0<q := by dsimp [q]; positivity
  by_cases hn3 : 3≤n
  · let f (j : ℕ) := Real.exp (-d*j)*((j:ℝ)+2)^2
    have hf : ∀ j, 0 ≤ f j := by intro j; dsimp [f]; positivity
    have hc : 0 ≤ 6*C*weight n := mul_nonneg (by positivity) (weight_nonneg n)
    have he (j : ℕ) : ENNReal.ofReal (Real.exp (-d*j)) * centeredBlock n (endpointWindow n j) ≤
        ENNReal.ofReal ((6*C*weight n)*f j) := by
      refine (mul_le_mul_of_nonneg_left (centered_window_large hB hC hzero hbar hn3 j) (show 0 ≤ ENNReal.ofReal (Real.exp (-d*j)) from zero_le)).trans_eq ?_
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      dsimp [f]; ring
    have hsum := (windowWeight_summable hd).mul_left (6*C*weight n)
    have hbound : P {ω | D ω = n} ≤ ENNReal.ofReal (Real.exp (-q*n) * ((6*C*weight n)*∑' j, f j)) := by
      apply (signed_atom_le_record hB D hD n).trans
      refine (measure_drifted_record_le n hd).trans ?_
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      gcongr
      calc
        _ ≤ ∑' j : ℕ, ENNReal.ofReal ((6*C*weight n)*f j) := ENNReal.tsum_le_tsum he
        _ = _ := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg hc (hf j)) hsum, tsum_mul_left]
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (mul_nonneg hc (tsum_nonneg hf)))] at hh
    calc
      _ ≤ Real.exp (-q*n)*((6*C*weight n)*∑' j, f j) := hh
      _ = (6*C*∑' j, f j)*weight n*Real.exp (-q*n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (weight_nonneg n)) (Real.exp_pos _).le
  · have hn2 : (n:ℝ) ≤ 2 := by exact_mod_cast (show n≤2 by omega)
    have hn' : 0<(n:ℝ) := by exact_mod_cast hn
    have hw : 1 ≤ 4*weight n := by
      rw [weight_eq_inv_sqrt hn, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have hs : √(n:ℝ) ≤ 2 := by rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by linarith⟩
      nlinarith [mul_le_mul hn2 hs (Real.sqrt_nonneg _) (by norm_num: (0:ℝ)≤2)]
    have he : 1 ≤ Real.exp (2*q)*Real.exp (-q*n) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]; nlinarith [mul_le_mul_of_nonneg_left hn2 hq.le]
    calc
      _ ≤ 1 := measureReal_le_one
      _ ≤ (4*weight n)*(Real.exp (2*q)*Real.exp (-q*n)) := by simpa using mul_le_mul hw he zero_le_one (by linarith)
      _ = (4*Real.exp (2*q))*weight n*Real.exp (-q*n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left ..) (weight_nonneg n)) (Real.exp_pos _).le

theorem signed_tail_upper_of_persistence {d C : ℝ} (hd : 0<d) (hC : 0≤C)
    (hzero : ∀ (k : ℕ) [NeZero k], (centeredBlock k).real (aboveLevel k 0) ≤ 1/√((k:ℝ)+1))
    (hbar : ∀ (k : ℕ) [NeZero k] (j : ℕ), (centeredBlock k).real (aboveLevel k (-(j+1:ℝ))) ≤
      C*((j:ℝ)+2)^2/√((k:ℝ)+1)) :
    ∃ K : ℝ, 0<K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ → Ω → ℝ), IsPreBrownianReal (fun t : ℝ≥0 => B (t:ℝ)) P →
      ∀ (D : Ω → ℤ), AEMeasurable D P →
      (∀ᵐ ω ∂P, ∀ k : ℤ, OMA.S_mo_142880.height B d k ω ≤ OMA.S_mo_142880.height B d (D ω) ω) →
      ∀ t : ℝ, 0≤t → P.real {ω | t < (D ω : ℝ)} ≤ K * envelope (d^2/2) t := by
  let q := d^2/2
  have hq : 0<q := by dsimp [q]; positivity
  have hr : 0 < 1-Real.exp (-q) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hq))
  refine ⟨halfFactor * upperConstant C d / (1-Real.exp (-q)),
    div_pos (mul_pos halfFactor_pos (upperConstant_pos ..)) hr, ?_⟩
  intro Ω mΩ P hP B hB D hm hD t ht
  let μ := P.map D
  have hupper (n : ℕ) (hn : 0<n) : μ.real {(n:ℤ)} ≤ upperConstant C d * weight n * Real.exp (-q*n) := by
    change (P.map D).real {(n:ℤ)} ≤ _
    rw [map_measureReal_apply_of_aemeasurable hm (measurableSet_singleton _)]
    exact signed_atom_upper_of_persistence hd hC hzero hbar hB D hD hn
  have hlower (n : ℕ) (_ : 0<n) : (0:ℝ)*weight n*Real.exp (-q*n) ≤ μ.real {(n:ℤ)} := by
    simpa using measureReal_nonneg (μ:=μ) (s:={(n:ℤ)})
  have h := (tail_of_atom_bounds μ hq le_rfl (upperConstant_pos ..).le hlower hupper ht).2
  change (P.map D).real {i : ℤ | t < (i:ℝ)} ≤ _ at h
  rwa [map_measureReal_apply_of_aemeasurable hm (MeasurableSet.of_discrete (s:={i : ℤ | t < (i:ℝ)}))] at h

end BrownianDiscrete
end
end

-- BrownianPersistence
section
open MeasureTheory ProbabilityTheory Set

namespace BrownianComparison
noncomputable section

open Fin.NatCast

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def positivePath (n : ℕ) [NeZero n] : Set (Fin n → ℝ) :=
  {v | ∀ j : Fin n, 0 < BrownianDiscrete.prefixSum v (j.val + 1)}

lemma positivePath_measurable (n : ℕ) [NeZero n] : MeasurableSet (positivePath n) := by
  rw [show positivePath n = ⋂ j : Fin n, {v | 0 < BrownianDiscrete.prefixSum v (j.val+1)}
      by ext; simp [positivePath]]
  apply MeasurableSet.iInter
  intro j
  apply measurableSet_lt measurable_const
  unfold BrownianDiscrete.prefixSum
  fun_prop

def pastIndex (n k : ℕ) (i : Fin n) : ℕ := k + (n - 1 - i.val)
def futureIndex (n k : ℕ) (i : Fin n) : ℕ := k + n + i.val

lemma peak_indices_disjoint (n k : ℕ) :
    Disjoint (Finset.univ.image (pastIndex n k)) (Finset.univ.image (futureIndex n k)) := by
  apply Finset.disjoint_left.mpr
  intro m hm hm'
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨j, _, e⟩ := Finset.mem_image.mp hm'
  dsimp [pastIndex, futureIndex] at e
  omega

def leftVec (X : ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) (i : Fin n) : ℝ :=
  X (pastIndex n k i) ω

def rightVec (X : ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) (i : Fin n) : ℝ :=
  -X (futureIndex n k i) ω

def peak (X : ℕ → Ω → ℝ) (n k : ℕ) [NeZero n] : Set Ω :=
  leftVec X n k ⁻¹' positivePath n ∩ rightVec X n k ⁻¹' positivePath n

lemma peak_disjoint {X : ℕ → Ω → ℝ} {n k l : ℕ} [NeZero n] (hkl : k < l) (hl : l ≤ k+n) :
    Disjoint (peak X n k) (peak X n l) := by
  apply Set.disjoint_left.mpr
  intro ω hk hm
  let m := l-k
  have hpos : 0 < m := by dsimp [m]; omega
  have hmn : m ≤ n := by dsimp [m]; omega
  let j : Fin n := ⟨m-1, by omega⟩
  have hjv : j.val = m-1 := rfl
  have hj : j.val+1 = m := by dsimp [j]; omega
  have a := hk.2 j
  have b := hm.1 j
  change 0 < BrownianDiscrete.prefixSum (rightVec X n k ω) (j.val+1) at a
  change 0 < BrownianDiscrete.prefixSum (leftVec X n l ω) (j.val+1) at b
  rw [hj] at a b
  have hflip : BrownianDiscrete.prefixSum (leftVec X n l ω) m =
      ∑ i ∈ Finset.range m, X (k+n+i) ω := by
    unfold BrownianDiscrete.prefixSum
    rw [← Finset.sum_range_reflect (fun i => X (k+n+i) ω) m]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hcast : (i : Fin n).val = i := Fin.val_cast_of_lt (hi'.trans_le hmn)
    simp only [leftVec, pastIndex, hcast]
    apply congrArg (fun t => X t ω)
    change l + (n - 1 - i) = k + n + (m - 1 - i)
    omega
  have hright : BrownianDiscrete.prefixSum (rightVec X n k ω) m =
      -(∑ i ∈ Finset.range m, X (k+n+i) ω) := by
    unfold BrownianDiscrete.prefixSum
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hcast : (i : Fin n).val = i := Fin.val_cast_of_lt (hi'.trans_le hmn)
    simp [rightVec, futureIndex, hcast]
  linarith

/-- A centered Gaussian walk stays strictly positive through time n with
probability at most 1/√(n+1). The proof packs n+1 disjoint strict local peaks. -/
theorem centered_persistence {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (n : ℕ) [NeZero n] :
    ((Measure.pi fun _ : Fin n => gaussianReal 0 1).real (positivePath n)) ^ 2 *
      (n+1 : ℕ) ≤ 1 := by
  let p := (Measure.pi fun _ : Fin n => gaussianReal 0 1) (positivePath n)
  have hm (k : ℕ) : P (peak X n k) = p*p := by
    let S := Finset.univ.image (pastIndex n k)
    let T := Finset.univ.image (futureIndex n k)
    let f (v : S → ℝ) (i : Fin n) := v ⟨pastIndex n k i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
    let g (v : T → ℝ) (i : Fin n) := -v ⟨futureIndex n k i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
    have hi := hind.indepFun_finset₀ S T (peak_indices_disjoint n k) fun i => (hX i).aemeasurable
    have hi' : IndepFun (leftVec X n k) (rightVec X n k) P :=
      hi.comp (show Measurable f by fun_prop) (show Measurable g by fun_prop)
    have hli : Function.Injective (pastIndex n k) := by
      intro i j h
      apply Fin.ext
      dsimp [pastIndex] at h
      omega
    have hri : Function.Injective (futureIndex n k) := by
      intro i j h
      apply Fin.ext
      dsimp [futureIndex] at h
      omega
    have hL : HasLaw (leftVec X n k) (Measure.pi fun _ : Fin n => gaussianReal 0 1) P :=
      (hind.precomp hli).hasLaw_pi fun i => hX _
    have hR : HasLaw (rightVec X n k) (Measure.pi fun _ : Fin n => gaussianReal 0 1) P := by
      apply ((hind.precomp hri).comp (fun _ => Neg.neg) (fun _ => measurable_neg)).hasLaw_pi
      intro i
      simpa [Function.comp_def, Pi.neg_def, neg_zero] using gaussianReal_neg (hX (futureIndex n k i))
    rw [peak, hi'.measure_inter_preimage_eq_mul _ _ (positivePath_measurable _) (positivePath_measurable _)]
    exact congrArg₂ (· * ·) (hL.measure_eq (p := fun x => x ∈ positivePath n) (positivePath_measurable n))
      (hR.measure_eq (p := fun x => x ∈ positivePath n) (positivePath_measurable n))
  have hd : (Finset.range (n+1) : Set ℕ).PairwiseDisjoint (fun k => peak X n k) := by
    intro k hk l hl hkl
    have hk' := Finset.mem_range.mp hk
    have hl' := Finset.mem_range.mp hl
    rcases lt_or_gt_of_ne hkl with hh | hh
    · exact peak_disjoint hh (by omega)
    · exact (peak_disjoint hh (by omega)).symm
  have hnmeas (k : ℕ) : NullMeasurableSet (peak X n k) P :=
    ((aemeasurable_pi_lambda _ fun i => (hX _).aemeasurable).nullMeasurableSet_preimage
      (positivePath_measurable n)).inter
    ((aemeasurable_pi_lambda _ fun i => (hX _).aemeasurable.neg).nullMeasurableSet_preimage
      (positivePath_measurable n))
  have hsum : ∑ k ∈ Finset.range (n+1), P (peak X n k) ≤ 1 := by
    rw [← measure_biUnion_finset₀ hd.aedisjoint fun k _ => hnmeas k]
    exact prob_le_one
  simp only [hm, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  rw [Nat.cast_add_one] at hsum
  rw [show (Measure.pi fun _ : Fin n => gaussianReal 0 1).real (positivePath n) = p.toReal by rfl]
  have h := ENNReal.toReal_mono (by simp) hsum
  simpa [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_natCast, measure_ne_top, p, pow_two, mul_comm, mul_left_comm, mul_assoc] using h

end
end BrownianComparison
end

-- BrownianPadding
section
open MeasureTheory ProbabilityTheory Set Fin.NatCast Finset
open scoped ENNReal

namespace BrownianComparison
open BrownianDiscrete
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma positivePath_eq (n : ℕ) [NeZero n] : positivePath n = aboveLevel n 0 := rfl

/-- Reversing increments turns a terminal strict record into positive prefix sums. -/
lemma reverse_positive_iff {n : ℕ} [NeZero n] (v : Fin n → ℝ) :
    (fun i => v (Fin.rev i)) ∈ positivePath n ↔ v ∈ recordSet n := by
  have hr (j : ℕ) (hj : j ≤ n) :
      prefixSum (fun i => v (Fin.rev i)) j = prefixSum v n - prefixSum v (n-j) := by
    have hs := prefixSum_add v (n-j) j
    rw [Nat.sub_add_cancel hj] at hs
    unfold prefixSum at hs ⊢
    simp only [← Nat.cast_add] at hs
    rw [← Finset.sum_range_reflect (fun i => v ((n-j+i : ℕ) : Fin n)) j] at hs
    have eq : (∑ i ∈ range j, v ((n-j+(j-1-i) : ℕ) : Fin n)) = ∑ i ∈ range j, v (Fin.rev (i : Fin n)) := by
      refine sum_congr rfl fun i hi => congrArg v (Fin.ext ?_)
      have hij := mem_range.mp hi
      have hle : n-j+(j-1-i) < n := by omega
      simp only [Fin.val_cast_of_lt hle, Fin.val_rev, Fin.val_cast_of_lt (hij.trans_le hj)]
      omega
    rw [eq] at hs
    linarith
  constructor
  · intro hv k hk
    have h := hv (⟨n-k-1, by omega⟩ : Fin n)
    change 0 < prefixSum _ (n-k-1+1) at h
    rw [show n-k-1+1 = n-k by omega, hr _ (by omega), Nat.sub_sub_self hk.le] at h
    linarith
  · intro hv j
    change 0 < prefixSum _ (j.val+1)
    rw [hr _ j.isLt, sub_pos]
    exact hv _ (by omega)

/-- The lower bound is for the joint event of surviving m steps and finishing above y. -/
theorem positive_terminal_lower {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (m : ℕ) [NeZero m] (y : ℝ) (hy : 0 ≤ y) :
    (gaussianReal 0 m).real (Ioi y) ≤ m * ((centeredBlock m).real
      (positivePath m ∩ (fun v => prefixSum v m) ⁻¹' Ioi y)) := by
  let Q := centeredBlock m
  let X (i : Fin m) (v : Fin m → ℝ) := v i
  have hi : iIndepFun X Q := by simpa [X, Q, centeredBlock] using
    (iIndepFun_pi (μ := fun _ : Fin m => gaussianReal 0 1) (X := fun _ x => x) (fun _ => aemeasurable_id))
  have hl (i : Fin m) : HasLaw (X i) (gaussianReal 0 1) Q :=
    (measurePreserving_eval (μ := fun _ : Fin m => gaussianReal 0 1) i).hasLaw
  have h := cyclic_record_bound hi hl (Ioi y) measurableSet_Ioi (Ioi_subset_Ioi hy)
  let W (ω : Ω) (i : Fin m) := increment B 0 i.val ω
  have hlawW : HasLaw W Q P := by
    obtain ⟨hi', hl'⟩ := increment_iid hB 0 m
    simpa [W, Q, centeredBlock] using hi'.hasLaw_pi hl'
  have hSw : HasLaw (fun ω => prefixSum (W ω) m) (gaussianReal 0 m) P := by
    apply (hB.hasLaw_eval (m : NNReal)).congr
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    simp [W, prefixSum_increment le_rfl, hω]
  have hs : HasLaw (fun v : Fin m → ℝ => prefixSum v m) (gaussianReal 0 m) Q :=
    HasLaw.comp_of_hasLaw_comp (f := fun v : Fin m → ℝ => prefixSum v m) (by apply Measurable.aemeasurable; unfold prefixSum; fun_prop) hlawW HasLaw.id hSw
  let A := positivePath m ∩ (fun v => prefixSum v m) ⁻¹' Ioi y
  have hrev : (fun v i => v (Fin.rev i)) ⁻¹' A =
      recordSet m ∩ (fun v => prefixSum v m) ⁻¹' Ioi y := by
    ext v
    simp only [A, Set.mem_preimage, mem_inter_iff, reverse_positive_iff]
    have hg : prefixSum (fun i => v (Fin.rev i)) m = prefixSum v m := by
      unfold prefixSum
      calc
        _ = ∑ i : Fin m, v (Fin.revPerm i) := by simpa using (Fin.sum_univ_eq_sum_range (fun j : ℕ => v (Fin.rev (j : Fin m))) m).symm
        _ = ∑ i : Fin m, v i := Equiv.sum_comp Fin.revPerm v
        _ = _ := by simpa using Fin.sum_univ_eq_sum_range (fun j : ℕ => v (j : Fin m)) m
    rw [hg]
  have hpres : HasLaw (fun (v : Fin m → ℝ) i => v (Fin.rev i)) Q Q := (hi.precomp Fin.revPerm.injective).hasLaw_pi fun i => hl (Fin.rev i)
  have heq := hs.measureReal_eq (p := fun x : ℝ => y < x) measurableSet_Ioi
  have hF : MeasurableSet A := (positivePath_measurable _).inter (measurableSet_Ioi.preimage (by unfold prefixSum; fun_prop))
  change (gaussianReal 0 m).real {x | y < x} ≤ m * Q.real A
  rw [← heq]
  have he : Q ((fun (v : Fin m → ℝ) i => v (Fin.rev i)) ⁻¹' A) = Q A := hpres.measure_eq (p := (· ∈ A)) hF
  rw [hrev] at he
  unfold Measure.real
  rw [← he]
  exact h

end
end BrownianComparison
end

-- BrownianPaddingJoin
section
open MeasureTheory ProbabilityTheory Set Fin.NatCast
open scoped NNReal ENNReal
namespace BrownianComparison
noncomputable section
open BrownianDiscrete
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def segment (X : ℕ → Ω → ℝ) (a k : ℕ) (ω : Ω) (i : Fin k) := X (a+i.val) ω

lemma segment_prefix (X : ℕ → Ω → ℝ) (a k : ℕ) [NeZero k] (ω : Ω) {j : ℕ} (hj : j ≤ k) :
    prefixSum (segment X a k ω) j = ∑ i ∈ Finset.range j, X (a+i) ω := by
  unfold prefixSum segment
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fin.val_cast_of_lt ((Finset.mem_range.mp hi).trans_le hj)]

lemma segment_law (X : ℕ → Ω → ℝ) (hind : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (a k : ℕ) :
    HasLaw (segment X a k) (centeredBlock k) P :=
  (hind.precomp (g := fun i : Fin k => a+i.val) (fun i j h => Fin.ext (Nat.add_left_cancel h))).hasLaw_pi fun i => hX _

theorem concatenate_persistence {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (m k : ℕ) [NeZero m] [NeZero k] (y : ℝ) :
    ((centeredBlock m).real (positivePath m ∩ (fun v => prefixSum v m) ⁻¹' Ioi y)) *
      (centeredBlock k).real (aboveLevel k (-y)) ≤ (centeredBlock (m+k)).real (positivePath (m+k)) := by
  let A := positivePath m ∩ (fun v => prefixSum v m) ⁻¹' Ioi y
  let D := aboveLevel k (-y)
  have hA : MeasurableSet A := (positivePath_measurable m).inter (measurableSet_Ioi.preimage (by unfold prefixSum; fun_prop))
  have hD : MeasurableSet D := aboveLevel_measurable _ _
  have hi : IndepFun (segment X 0 m) (segment X m k) P :=
    disjoint_samples hind (fun i => (hX i).aemeasurable) (fun i : Fin m => 0+i.val) (fun j : Fin k => m+j.val)
      (by intro i j; omega)
  have hprod := hi.measure_inter_preimage_eq_mul A D hA hD
  have hl := (segment_law X hind hX 0 m).measure_eq (p := (· ∈ A)) hA
  have hr := (segment_law X hind hX m k).measure_eq (p := (· ∈ D)) hD
  have hfull := (segment_law X hind hX 0 (m+k)).measure_eq (p := (· ∈ positivePath (m+k))) (positivePath_measurable _)
  have hle : (segment X 0 m ⁻¹' A ∩ segment X m k ⁻¹' D) ⊆ segment X 0 (m+k) ⁻¹' positivePath (m+k) := by
    intro ω hw i
    have hfirst := hw.1.1
    have hend : y < prefixSum (segment X 0 m ω) m := hw.1.2
    have hright := hw.2
    change 0 < prefixSum (segment X 0 (m+k) ω) (i.val+1)
    rw [segment_prefix _ _ _ _ (by omega)]
    by_cases h : i.val < m
    · have hp := hfirst (⟨i.val,h⟩ : Fin m)
      change 0 < prefixSum (segment X 0 m ω) (i.val+1) at hp
      rwa [segment_prefix _ _ _ _ h] at hp
    · let j := i.val - m
      have hj : j < k := by dsimp [j]; omega
      have hp := hright (⟨j,hj⟩ : Fin k)
      change -y < prefixSum (segment X m k ω) (j+1) at hp
      rw [segment_prefix _ _ _ _ hj] at hp
      rw [segment_prefix _ _ _ _ le_rfl] at hend
      rw [show i.val+1 = m+(j+1) by dsimp [j]; omega, Finset.sum_range_add]
      simp only [zero_add] at hend ⊢
      linarith
  have hm : P _ ≤ P _ := measure_mono hle
  change P (segment X 0 m ⁻¹' A) = _ at hl
  change P (segment X m k ⁻¹' D) = _ at hr
  change P (segment X 0 (m+k) ⁻¹' positivePath (m+k)) = _ at hfull
  rw [hprod,hl,hr,hfull] at hm
  simpa [Measure.real, ENNReal.toReal_mul] using ENNReal.toReal_mono (measure_ne_top _ _) hm

lemma persistence_sqrt {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (n : ℕ) [NeZero n] :
    (centeredBlock n).real (positivePath n) ≤ 1/Real.sqrt ((n:ℝ)+1) := by
  have h := centered_persistence hind hX n
  have hn : 0 < (n:ℝ)+1 := by positivity
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hn)).mpr
  apply le_of_pow_le_pow_left₀ two_ne_zero (by norm_num : (0:ℝ) ≤ 1)
  rw [mul_pow, Real.sq_sqrt hn.le, one_pow]
  simpa only [Nat.cast_add_one, centeredBlock] using h

end
end BrownianComparison
end

-- BrownianDiscreteEnvelope
section
noncomputable section
open MeasureTheory ProbabilityTheory Set Real BrownianComparison
open scoped ENNReal NNReal
namespace BrownianDiscrete

def normalTailOne : ℝ := (gaussianReal 0 1).real (Ioi 1)

theorem normalTailOne_pos : 0 < normalTailOne := by
  apply ENNReal.toReal_pos _ (measure_ne_top _ _)
  intro h
  have hv := gaussianReal_absolutelyContinuous' 0 (one_ne_zero : (1:ℝ≥0) ≠ 0) h
  simpa using hv

theorem square_time_tail (j : ℕ) : (gaussianReal 0 (((j+1)^2 : ℕ) : ℝ≥0)).real
    (Ioi ((j:ℝ)+1)) = normalTailOne := by
  let s := (j:ℝ)+1
  have hs : 0<s := by dsimp [s]; positivity
  have h := gaussianReal_const_mul (HasLaw.id (μ:=gaussianReal 0 1)) s
  have hvar : (⟨s^2,sq_nonneg _⟩:ℝ≥0) * 1 = (((j+1)^2 : ℕ) : ℝ≥0) := by ext; simp [s]
  have h' : HasLaw (fun x : ℝ => s*x) (gaussianReal 0 (((j+1)^2 : ℕ):ℝ≥0)) (gaussianReal 0 1) := by
    convert h using 1 <;> simp [s]
    apply congrArg (gaussianReal 0)
    apply NNReal.eq
    simp
  have he := h'.measureReal_eq (p := fun y : ℝ => s < y) measurableSet_Ioi
  have hset : {x : ℝ | s < s*x} = Ioi (1:ℝ) := by
    ext x
    change s < s*x ↔ 1<x
    simpa only [mul_one] using (mul_lt_mul_iff_of_pos_left hs : s*1 < s*x ↔ 1<x)
  rw [hset] at he
  exact he.symm

theorem persistence_bounds {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    (∀ (k : ℕ) [NeZero k], (centeredBlock k).real (aboveLevel k 0) ≤ 1/√((k:ℝ)+1)) ∧
    (∀ (k : ℕ) [NeZero k] (j : ℕ), (centeredBlock k).real (aboveLevel k (-(j+1:ℝ))) ≤
      normalTailOne⁻¹*((j:ℝ)+2)^2/√((k:ℝ)+1)) := by
  let X := increment B 0
  have hi : iIndepFun X P := by
    have h := hB.hasIndepIncrements.nat (t := fun i : ℕ => (i:ℝ≥0)) (fun i j h => by dsimp; exact_mod_cast h)
    change iIndepFun (fun (i:ℕ) (ω:Ω) => B ((i:ℝ≥0)+1) ω-B i ω-0) P
    simpa using h
  have hX (i : ℕ) : HasLaw (X i) (gaussianReal 0 1) P := by
    simpa [X] using (increment_iid hB 0 (i+1)).2 (⟨i,by omega⟩ : Fin (i+1))
  refine ⟨fun k _ => persistence_sqrt hi hX k, ?_⟩
  intro k hk j
  let m := (j+1)^2
  let : NeZero m := ⟨by dsimp [m]; positivity⟩
  let y := (j:ℝ)+1
  have hy : 0 ≤ y := by dsimp [y]; positivity
  let D := (centeredBlock k).real (aboveLevel k (-y))
  let A := (centeredBlock m).real (positivePath m ∩ (fun v => prefixSum v m) ⁻¹' Ioi y)
  have hterminal : normalTailOne ≤ m*A := by
    simpa only [m,y,A,square_time_tail] using positive_terminal_lower hB m y hy
  have hcat : A*D ≤ (centeredBlock (m+k)).real (positivePath (m+k)) :=
    concatenate_persistence hi hX m k y
  have hb := persistence_sqrt hi hX (m+k)
  have hr : 1/√((m+k:ℕ)+1:ℝ) ≤ 1/√((k:ℝ)+1) := by
    apply one_div_le_one_div_of_le (by positivity)
    apply Real.sqrt_le_sqrt
    push_cast
    linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hscale : normalTailOne*D ≤ m*(1/√((k:ℝ)+1)) := by
    calc
      _ ≤ (m*A)*D := mul_le_mul_of_nonneg_right hterminal measureReal_nonneg
      _ ≤ m*(1/√((k:ℝ)+1)) := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hcat.trans (hb.trans hr)) (Nat.cast_nonneg _)
  have hm : (m:ℝ) ≤ ((j:ℝ)+2)^2 := by dsimp [m]; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) j]
  have hfinal := hscale.trans (mul_le_mul_of_nonneg_right hm (by positivity))
  change D ≤ _
  calc
    D = normalTailOne⁻¹*(normalTailOne*D) := by rw [← mul_assoc, inv_mul_cancel₀ normalTailOne_pos.ne', one_mul]
    _ ≤ normalTailOne⁻¹*(((j:ℝ)+2)^2*(1/√((k:ℝ)+1))) :=
      mul_le_mul_of_nonneg_left hfinal (inv_nonneg.mpr normalTailOne_pos.le)
    _ = _ := by ring

/-- Complete two-sided (upper and lower) sharp envelope for the right tail of the signed
integer maximizer under the original Brownian hypotheses. -/
theorem discrete_envelope (d : ℝ) (hd : 0<d) : ∃ c C : ℝ, 0<c ∧ 0<C ∧ DiscreteEnvelope d c C := by
  classical
  by_cases H : (∀ (k : ℕ) [NeZero k], (centeredBlock k).real (aboveLevel k 0) ≤ 1/√((k:ℝ)+1)) ∧
    (∀ (k : ℕ) [NeZero k] (j : ℕ), (centeredBlock k).real (aboveLevel k (-(j+1:ℝ))) ≤
      normalTailOne⁻¹*((j:ℝ)+2)^2/√((k:ℝ)+1))
  · obtain ⟨C,hC,hu⟩ := signed_tail_upper_of_persistence hd (inv_nonneg.mpr normalTailOne_pos.le) H.1 H.2
    obtain ⟨c,hc,hl⟩ := signed_tail_lower hd
    refine ⟨c,C,hc,hC,?_⟩
    intro Ω mΩ P hP B hR hL hi D hm hD t ht
    exact ⟨hl Ω P B hR.toIsPreBrownianReal hL.toIsPreBrownianReal hi D hD t ht,
      hu Ω P B hR.toIsPreBrownianReal D hm hD t ht⟩
  · refine ⟨1,1,zero_lt_one,zero_lt_one,?_⟩
    intro Ω mΩ P hP B hR
    exact False.elim (H (persistence_bounds hR.toIsPreBrownianReal))

end BrownianDiscrete
end
end

-- BrownianSubmission
section
theorem OMA.solution : type_of% @OMA.S_mo_142880.main :=
  BrownianDiscrete.comparison_from_envelopes BrownianDiscrete.discrete_envelope
    (fun d hd => BrownianComparison.continuous_envelope_of_large hd (BrownianComparison.continuous_large d hd))
end
