import FormalConjectures.ErdosProblems.«241»
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds

/-! A Fourier certificate for White's improved upper bound for B₃ sets. The argument uses an explicit rational linear spline on the circle of period two. Half-angle identities certify its cosine intervals; upward-rounded integer bounds certify the sum of Fourier coefficient powers. Pairing against a smoothed indicator on the unit interval transfers the estimate to finite B₃ sets. The general Fourier-duality proof credits the earlier Green 35 contribution below. -/
namespace OMA.Energy241
open MeasureTheory in
def UnitDensity (f : ℝ → ℝ) : Prop :=
  Integrable f ∧ (∀ x, 0 ≤ f x) ∧ Function.support f ⊆ Set.Icc (0 : ℝ) 1 ∧ ∫ x, f x = 1
end OMA.Energy241


/- Integer jumps for a dyadic spline testing the White autoconvolution bound. -/

namespace OMA.White241

abbrev M : ℕ := 32768
abbrev H : ℕ := 56522894924763181

/-- The first component is the grid distance from the midpoint; the second is
  twice the change of slope at that distance, with the center collected once. -/
def J : List (ℕ × ℤ) :=
  [(16384, 1627262170365952),
    (16383, -953271288266752),
    (16382, -156848943071232),
    (16381, -81195779424256),
    (16380, -51891562938368),
    (16379, -36862281908224),
    (16378, -27934027481088),
    (16377, -22116664803328),
    (16376, -25642670718976),
    (16374, -26072827854848),
    (16372, -19758960836608),
    (16370, -15644969992192),
    (16368, -18140535029760),
    (16364, -18446536441856),
    (16360, -13981056106496),
    (16356, -11071326224384),
    (16352, -12839211843584),
    (16344, -13058180128768),
    (16336, -9899332411392),
    (16328, -7840853663744),
    (16320, -9095536541696),
    (16304, -9254032666624),
    (16288, -7018583781376),
    (16272, -5561619656704),
    (16256, -6455308048384),
    (16224, -6572548753408),
    (16192, -4989289961472),
    (16160, -3957078134784),
    (16128, -4598166843392),
    (16064, -4688344010752),
    (16000, -3565186086912),
    (15936, -2832491711488),
    (15872, -3298687667712),
    (15744, -3372664632832),
    (15616, -2573333429760),
    (15488, -2051257861120),
    (15360, -2398970120192),
    (15104, -2465580177152),
    (14848, -1893123575040),
    (14592, -1518369964544),
    (14336, -1789650325760),
    (13824, -1857039312000),
    (13312, -1442437540736),
    (12800, -1170073433344),
    (12288, -1399334275328),
    (11264, -1478968537984),
    (10240, -1175800879808),
    (9216, -977478596288),
    (8192, -1211044062848),
    (6144, -1347936117824),
    (4096, -1157896473888),
    (2048, -1061454591264),
    (0, -515873447680)]

theorem jumps_zero : (J.map Prod.snd).sum = 0 := by decide

theorem jumps_moment : (J.map (fun z => z.2 * (z.1 : ℤ)^2)).sum = 2*M*(H:ℤ) := by decide

theorem offset_le (z) (hz : z ∈ J) : z.1 ≤ M/2 := by
  exact of_decide_eq_true (List.all_eq_true.mp
    (show J.all (fun z => decide (z.1 ≤ M/2)) = true by decide) z hz)

end OMA.White241


/- Exact Fourier coefficients of a signed linear combination of centered tents. -/
namespace OMA.WhiteSpline
open MeasureTheory Finset
open scoped Real
noncomputable section

private instance : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
private abbrev center : ℝ := 3/2
private def hat (a x : ℝ) : ℝ := max 0 (a - |x-center|)
private lemma hat_cont (a : ℝ) : Continuous (hat a) := by unfold hat; fun_prop

private lemma hat_left {a x : ℝ} (hx : x ≤ center-a) (ha : 0 ≤ a) : hat a x = 0 := by
  rw [hat,abs_of_nonpos (by linarith),max_eq_left (by linarith)]
private lemma hat_right {a x : ℝ} (hx : center+a ≤ x) (ha : 0 ≤ a) : hat a x = 0 := by
  rw [hat,abs_of_nonneg (by linarith),max_eq_left (by linarith)]

private lemma split_integral {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/2)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ x in (0:ℝ)..2, f x * (hat a x : ℂ)) =
      (∫ x in (center-a)..center, f x * ((x:ℂ) - ((center-a:ℝ):ℂ))) +
      ∫ x in center..(center+a), f x * (((center+a:ℝ):ℂ) - (x:ℂ)) := by
  let g (x : ℝ) := f x * (hat a x:ℂ)
  have hg : Continuous g := hf.mul (Complex.continuous_ofReal.comp (hat_cont a))
  change (∫ x in (0:ℝ)..2, g x) = _
  rw [←intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable 0 (center-a))
    (hg.intervalIntegrable (center-a) 2),
    ←intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable (center-a) center)
      (hg.intervalIntegrable center 2),
    ←intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable center (center+a))
      (hg.intervalIntegrable (center+a) 2)]
  have hleft : (∫ x in (0:ℝ)..(center-a), g x)=0 := by
    calc _ = ∫ _x in (0:ℝ)..(center-a), (0:ℂ) := intervalIntegral.integral_congr fun x hx => by
          rw [Set.uIcc_of_le (by dsimp [center]; linarith)] at hx
          simp [g,hat_left hx.2 ha]
         _ = _ := by simp
  have hright : (∫ x in (center+a)..2, g x)=0 := by
    calc _ = ∫ _x in (center+a)..2, (0:ℂ) := intervalIntegral.integral_congr fun x hx => by
          rw [Set.uIcc_of_le (by dsimp [center]; linarith)] at hx
          simp [g,hat_right hx.1 ha]
         _ = _ := by simp
  rw [hleft,hright,zero_add,add_zero]
  congr 1
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    dsimp only [g,hat]
    rw [abs_of_nonpos (by linarith [hx.2]),max_eq_right (by linarith [hx.1])]
    push_cast
    ring
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    dsimp only [g,hat]
    rw [abs_of_nonneg (by linarith [hx.1]),max_eq_right (by linarith [hx.2])]
    push_cast
    ring

private lemma affine_integral (s t : ℂ) (a b : ℝ) :
    (∫ x in a..b, s*(x:ℂ)+t) =
      (s*(b:ℂ)^2/2+t*b) - (s*(a:ℂ)^2/2+t*a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro x _
  have h₀ : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have hd := ((h₀.pow 2).const_mul s).div_const 2
  have h := hd.add (h₀.const_mul t)
  convert h using 1
  · rfl
  · norm_num
    ring

private lemma hat_mass {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/2) :
    (∫ x in (0:ℝ)..2, (hat a x:ℂ)) = (a:ℂ)^2 := by
  have hh := split_integral ha ha' (fun _ => 1) continuous_const
  simp only [one_mul] at hh
  rw [hh]
  have h₁ := affine_integral 1 (-((center-a:ℝ):ℂ)) (center-a) center
  have h₂ := affine_integral (-1) ((center+a:ℝ):ℂ) center (center+a)
  simp only [one_mul,←sub_eq_add_neg] at h₁
  simp only [neg_one_mul,neg_add_eq_sub] at h₂
  rw [h₁,h₂]
  push_cast
  ring

private lemma exponential_affine {b : ℂ} (hb : b≠0) (s t : ℂ) (l r : ℝ) :
    (∫ x in l..r, Complex.exp (b*x)*(s*(x:ℂ)+t)) =
      Complex.exp (b*r)*(s*r+t-s/b)/b - Complex.exp (b*l)*(s*l+t-s/b)/b := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro x _
  have h₀ : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have he := (h₀.const_mul b).cexp
  have hl := ((h₀.const_mul s).add_const t).sub_const (s/b)
  have hd := (he.mul hl).div_const b
  have deriv_eq : (Complex.exp (b*x)*(b*1)*(s*x+t-s/b) + Complex.exp (b*x)*(s*1))/b =
      Complex.exp (b*x)*(s*x+t) := by field_simp; ring
  rw [←deriv_eq]
  exact hd

private lemma hat_exp {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/2) {b : ℂ} (hb : b≠0) :
    (∫ x in (0:ℝ)..2, Complex.exp (b*x)*(hat a x:ℂ)) =
      Complex.exp (b*center)*(Complex.exp (-(b*a)) - 2 + Complex.exp (b*a)) / b^2 := by
  rw [split_integral ha ha' _ (by fun_prop)]
  have h₁ := exponential_affine hb 1 (-((center-a:ℝ):ℂ)) (center-a) center
  have h₂ := exponential_affine hb (-1) ((center+a:ℝ):ℂ) center (center+a)
  simp only [one_mul,←sub_eq_add_neg] at h₁
  simp only [neg_one_mul,neg_add_eq_sub] at h₂
  rw [h₁,h₂]
  push_cast
  have hminus : Complex.exp (b*(3/2-(a:ℂ))) = Complex.exp (b*(3/2))*Complex.exp (-(b*a)) := by
    rw [←Complex.exp_add]; congr 1; ring
  have hplus : Complex.exp (b*(3/2+(a:ℂ))) = Complex.exp (b*(3/2))*Complex.exp (b*a) := by
    rw [←Complex.exp_add]; congr 1; ring
  rw [hminus,hplus]
  field_simp
  ring

private def freq (n : ℤ) : ℂ := -(Real.pi*(n:ℂ))*Complex.I
private def wave (n : ℤ) (x : ℝ) := Complex.exp (freq n*x)
private lemma wave_cont (n : ℤ) : Continuous (wave n) := by unfold wave; fun_prop
private lemma freq_ne {n : ℤ} (hn : n ≠ 0) : freq n ≠ 0 := by simp [freq,hn,Real.pi_ne_zero]

private lemma wave_integral {n : ℤ} (hn : n≠0) : (∫ x in (0:ℝ)..2, wave n x) = 0 := by
  have hh := exponential_affine (freq_ne hn) 0 1 0 2
  have he : Complex.exp (freq n*2) = 1 := by
    rw [show freq n*2 = ((-n:ℤ):ℂ)*(2*Real.pi*Complex.I) by simp [freq]; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  simpa [wave,he] using hh

private lemma hat_wave {n : ℤ} (hn : n ≠ 0) {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/2) :
    (∫ x in (0:ℝ)..2, wave n x*(hat a x:ℂ)) =
      (wave n center) * (2 / ((Real.pi*(n:ℝ))^2 : ℝ)) *
        ((1 - Real.cos (Real.pi*(n:ℝ)*a) : ℝ) : ℂ) := by
  rw [show (fun x => wave n x*(hat a x:ℂ)) = (fun x : ℝ => Complex.exp (freq n*x)*(hat a x:ℂ)) from rfl,
    hat_exp ha ha' (freq_ne hn)]
  let t : ℂ := ((Real.pi*(n:ℝ)*a:ℝ):ℂ)
  have h₁ : -(freq n*(a:ℂ)) = t*Complex.I := by dsimp [t,freq]; push_cast; ring
  have h₂ : freq n*(a:ℂ) = -t*Complex.I := by dsimp [t,freq]; push_cast; ring
  have h₃ : freq n ^ 2 = -(((Real.pi*(n:ℝ))^2:ℝ):ℂ) := by
    simp [freq,mul_pow,Complex.I_sq]
  have hcos : Complex.exp (t*Complex.I) - 2 + Complex.exp (-t*Complex.I) =
      2 * (((Real.cos (Real.pi*(n:ℝ)*a) : ℝ):ℂ)-1) := by
    rw [Complex.ofReal_cos,Complex.cos]
    dsimp only [t]; ring
  rw [h₁,h₂,h₃,hcos]
  dsimp only [wave]
  push_cast
  ring

private def raw {ι : Type*} [Fintype ι] (a c : ι→ℝ) (I x : ℝ) : ℂ :=
  1 - ∑ i, ((c i:ℂ)/I)*(hat (a i) x:ℂ)

private lemma raw_cont {ι : Type*} [Fintype ι] (a c : ι→ℝ) (I : ℝ) :
    Continuous (raw a c I) := by
  unfold raw
  exact continuous_const.sub (continuous_finsetSum _ (fun i _ =>
    continuous_const.mul (Complex.continuous_ofReal.comp (hat_cont _))))

private lemma raw_integral {ι : Type*} [Fintype ι] (a c : ι→ℝ) (I : ℝ)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ x in (0:ℝ)..2, f x * raw a c I x) =
      (∫ x in (0:ℝ)..2, f x) - ∑ i, ((c i:ℂ)/I)*
        ∫ x in (0:ℝ)..2, f x*(hat (a i) x:ℂ) := by
  have hg (i : ι) : Continuous (fun x : ℝ => ((c i:ℂ)/I)*(f x*(hat (a i) x:ℂ))) :=
    continuous_const.mul (hf.mul (Complex.continuous_ofReal.comp (hat_cont _)))
  have he (x : ℝ) : f x * raw a c I x =
      f x - ∑ i, ((c i:ℂ)/I)*(f x*(hat (a i) x:ℂ)) := by
    rw [raw,mul_sub,mul_one,mul_sum]; congr 1
    apply sum_congr rfl; intro i _; ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
    ((continuous_finsetSum _ (fun i _ => hg i)).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun i _ => (hg i).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul]

theorem witness {ι : Type*} [Fintype ι] (a c : ι → ℝ) (I : ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1/2) (hI : 0 < I) (hmass : ∑ i, c i*(a i)^2 = 2*I) :
    ∃ U : C(AddCircle (2 : ℝ), ℂ), (∀ x ∈ Set.Icc (0:ℝ) 1, U x=1) ∧
      fourierCoeff U 0 = 0 ∧ ∀ n : ℤ, n ≠ 0 → ‖fourierCoeff U n‖ =
        |∑ i, c i*(Real.cos (Real.pi*(n.natAbs:ℝ)*a i)-1)| /
          (I*Real.pi^2*(n.natAbs:ℝ)^2) := by
  have h_one {x : ℝ} (hx : x ≤ 1) : raw a c I x = 1 := by
    have h (i : ι) : hat (a i) x=0 := hat_left (by dsimp [center]; linarith [(ha i).2]) (ha i).1
    simp [raw,h]
  have h_two : raw a c I 2=1 := by
    have h (i : ι) : hat (a i) 2=0 := hat_right (by dsimp [center]; linarith [(ha i).2]) (ha i).1
    simp [raw,h]
  let U : C(AddCircle (2 : ℝ),ℂ) :=
    ⟨AddCircle.liftIco 2 0 (raw a c I), AddCircle.liftIco_zero_continuous
      ((h_one (by norm_num : (0:ℝ) ≤1)).trans h_two.symm) (raw_cont a c I).continuousOn⟩
  have hcoe {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 2) : U x = raw a c I x := by
    by_cases hlt : x < 2
    · change AddCircle.liftIco 2 0 (raw a c I) x = _
      exact AddCircle.liftIco_zero_coe_apply ⟨hx.1,hlt⟩
    · obtain rfl : x=2 := by linarith [hx.2]
      have he : ((2:ℝ) : AddCircle (2:ℝ))=0 := by
        rw [AddCircle.coe_eq_zero_iff]
        exact ⟨1,by norm_num⟩
      rw [he,←QuotientAddGroup.mk_zero]
      change AddCircle.liftIco 2 0 (raw a c I) ((0:ℝ):AddCircle (2:ℝ))=_
      rw [AddCircle.liftIco_zero_coe_apply (by constructor <;> norm_num),h_one (by norm_num),h_two]
  have hcoeff (n : ℤ) : fourierCoeff U n =
      (1/2 : ℂ)*((∫ x in (0:ℝ)..2, wave n x) - ∑ i, ((c i:ℂ)/I)*
        ∫ x in (0:ℝ)..2, wave n x*(hat (a i) x:ℂ)) := by
    rw [← raw_integral _ _ _ _ (wave_cont n),fourierCoeff_eq_intervalIntegral U n 0,zero_add]
    rw [Complex.real_smul]
    push_cast
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤2)] at hx
    change (@fourier 2 (-n) (x : AddCircle (2:ℝ))) * U x = wave n x * raw a c I x
    have hf : @fourier 2 (-n) (x : AddCircle (2:ℝ)) = wave n x := by
      rw [fourier_coe_apply]
      unfold wave
      congr 1
      dsimp [freq]
      push_cast
      ring
    rw [hf,hcoe hx]
  refine ⟨U,fun x hx => (hcoe ⟨hx.1,by linarith [hx.2]⟩).trans (h_one hx.2),?_,?_⟩
  · rw [hcoeff]
    have he (x : ℝ) : wave 0 x=1 := by simp [wave,freq]
    simp_rw [he,one_mul,hat_mass (ha _).1 (ha _).2]
    have hs : ∑ i, ((c i:ℂ)/I)*(a i:ℂ)^2 = (2:ℂ) := by
      have hmass' : (∑ i, (c i:ℂ)*(a i:ℂ)^2) = (2:ℂ)*I := by exact_mod_cast hmass
      simp only [div_mul_eq_mul_div,←sum_div]
      rw [hmass',mul_div_cancel_right₀ _ (by exact_mod_cast hI.ne')]
    rw [hs]; norm_num
  · intro n hn
    rw [hcoeff,wave_integral hn,zero_sub]
    simp_rw [hat_wave hn (ha _).1 (ha _).2]
    let s := ∑ i, c i*(Real.cos (Real.pi*(n:ℝ)*a i)-1)
    have hs : ((1/2:ℂ) * -∑ i, ((c i:ℂ)/I) * (wave n center * (2 / ((Real.pi*(n:ℝ))^2 : ℝ)) *
        ((1 - Real.cos (Real.pi*(n:ℝ)*a i) : ℝ) : ℂ))) =
        wave n center * (((s/(I*Real.pi^2*(n:ℝ)^2)):ℝ):ℂ) := by
      dsimp only [s]
      push_cast
      simp only [←sum_neg_distrib,mul_sum,sum_div,mul_div_assoc']
      apply sum_congr rfl
      intro i _
      ring
    rw [hs,norm_mul]
    have hw : ‖wave n center‖ = 1 := by
      rw [wave,show freq n*(center:ℂ) = ((-(Real.pi*n*center):ℝ):ℂ)*Complex.I by
        dsimp [freq]; push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [hw,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos (by positivity :
      0<I*Real.pi^2*(n:ℝ)^2)]
    have hnabs : (n.natAbs:ℝ)=|(n:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
    rw [hnabs,sq_abs]
    dsimp only [s]
    by_cases h : (0:ℝ) ≤ n
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]
      simp_rw [mul_neg,neg_mul,Real.cos_neg]

end
end OMA.WhiteSpline


/- Instantiation of the continuous spline with the certified dyadic jumps. -/
namespace OMA.White241
open Finset
open scoped Real
noncomputable section

private instance : Fact (0 < (2:ℝ)) := ⟨by norm_num⟩

private theorem sum_gets {α β : Type*} [AddCommMonoid β] (l : List α) (g : α → β) :
    (∑ i : Fin l.length, g (l.get i)) = (l.map g).sum := by
  rw [←List.sum_ofFn]
  congr 1
  conv_rhs => rw [←List.ofFn_get l]
  simp

theorem spline :
    ∃ U : C(AddCircle (2:ℝ),ℂ), (∀ x ∈ Set.Icc (0:ℝ) 1, U x=1) ∧
      fourierCoeff U 0=0 ∧ ∀ n : ℤ, n≠0 → ‖fourierCoeff U n‖ =
        (M:ℝ)*|(J.map (fun z => (z.2:ℝ)*Real.cos (Real.pi*(n.natAbs:ℝ)*z.1/M))).sum| /
          ((H:ℝ)*Real.pi^2*(n.natAbs:ℝ)^2) := by
  let a (i : Fin J.length) : ℝ := (J.get i).1 / (M:ℝ)
  let c (i : Fin J.length) : ℝ := (J.get i).2
  have hm : (0:ℝ) < M := by norm_num [M]
  have hh : (0:ℝ) < H := by norm_num [H]
  have ha (i) : 0 ≤ a i ∧ a i ≤ 1/2 := by
    have h := offset_le (J.get i) (List.get_mem _ _)
    dsimp [a]
    exact ⟨by positivity, (div_le_iff₀ hm).mpr (by norm_num [M]; exact h)⟩
  have hint : (∑ i : Fin J.length, (J.get i).2 * ((J.get i).1 : ℤ)^2) = 2*M*(H:ℤ) := by
    exact (sum_gets J _).trans jumps_moment
  have hzero : (∑ i : Fin J.length, (J.get i).2) = 0 := (sum_gets J _).trans jumps_zero
  have hcr : (∑ i, c i) = 0 := by dsimp [c]; exact_mod_cast hzero
  have hmass : ∑ i, c i * a i ^ 2 = 2 * ((H:ℝ)/M) := by
    have hr : (∑ i, c i * ((J.get i).1:ℝ)^2) = 2*(M:ℝ)*H := by dsimp [c]; exact_mod_cast hint
    simp only [a,div_pow,←mul_div_assoc,←sum_div,hr]
    field_simp
  obtain ⟨U,hU,h0,hs⟩ := WhiteSpline.witness a c ((H:ℝ)/M) ha (div_pos hh hm) hmass
  refine ⟨U,hU,h0,?_⟩
  intro n hn
  rw [hs n hn]
  have rearrange :
      (∑ i, c i * (Real.cos (Real.pi*(n.natAbs:ℝ)*a i)-1)) =
      (J.map (fun z => (z.2:ℝ)*Real.cos (Real.pi*(n.natAbs:ℝ)*z.1/M))).sum := by
    simp only [mul_sub,mul_one,sum_sub_distrib,hcr,sub_zero]
    simpa only [a,c,←mul_div_assoc] using
      sum_gets J (fun z => (z.2:ℝ)*Real.cos (Real.pi*(n.natAbs:ℝ)*z.1/M))
  rw [rearrange]
  field_simp

end
end OMA.White241


/- Four equivalent frequency classes for a piecewise linear cosine witness. -/

namespace OMA.WhiteFold241

open Finset Real

theorem cos_left {M r : ℕ} (hM : 0 < M) (hr : r ≤ M) (j : ℕ) :
    cos (π * ((M-r : ℕ):ℝ) * j / M) =
      (-1 : ℝ)^j * cos (π * (r:ℝ) * j / M) := by
  rw [Nat.cast_sub hr, ← Real.cos_nat_mul_pi_sub]
  congr 1
  field_simp

theorem cos_right {M r : ℕ} (hM : 0 < M) (j : ℕ) :
    cos (π * ((M+r : ℕ):ℝ) * j / M) =
      (-1 : ℝ)^j * cos (π * (r:ℝ) * j / M) := by
  rw [Nat.cast_add, ← Real.cos_add_nat_mul_pi]
  congr 1
  field_simp
  ring

theorem cos_period_left {M r : ℕ} (hM : 0 < M) (hr : r ≤ 2*M) (j : ℕ) :
    cos (π * ((2*M-r : ℕ):ℝ) * j / M) = cos (π * (r:ℝ) * j / M) := by
  rw [Nat.cast_sub hr, Nat.cast_mul, Nat.cast_ofNat]
  rw [← Real.cos_nat_mul_two_pi_sub (π * (r:ℝ) * j / M) j]
  congr 1
  field_simp

theorem cos_add_period {M : ℕ} (hM : 0 < M) (n k j : ℕ) :
    cos (π * ((n+k*(2*M) : ℕ):ℝ) * j / M) =
      cos (π * (n:ℝ) * j / M) := by
  rw [← Real.cos_add_nat_mul_two_pi (π * (n:ℝ) * j / M) (k*j)]
  congr 1
  push_cast
  field_simp

private theorem reflect_block {α : Type*} [AddCommMonoid α] (F : ℕ → α) (a m : ℕ) :
    (∑ i ∈ range m, F (a+i+1)) = ∑ i ∈ range m, F (a+m+1-(i+1)) := by
  rw [← sum_range_reflect (fun i => F (a+i+1)) m]
  apply sum_congr rfl
  intro i hi
  have := mem_range.mp hi
  congr 1
  omega

theorem four_blocks {α : Type*} [AddCommMonoid α] (F : ℕ → α) (m : ℕ) :
    (∑ i ∈ range (4*(m+1)), F (i+1)) =
      F (m+1) + F (2*(m+1)) + F (3*(m+1)) + F (4*(m+1)) +
      ∑ i ∈ range m, (F (i+1) + F (2*(m+1)-(i+1)) +
        F (2*(m+1)+(i+1)) + F (4*(m+1)-(i+1))) := by
  let h := m+1
  have split (a : ℕ) :
      (∑ i ∈ range h, F (a+i+1)) = (∑ i ∈ range m, F (a+i+1)) + F (a+m+1) :=
    sum_range_succ _ _
  have total : (∑ i ∈ range (4*h), F (i+1)) =
      (∑ i ∈ range h, F (0+i+1)) + (∑ i ∈ range h, F (h+i+1)) +
      (∑ i ∈ range h, F (2*h+i+1)) + (∑ i ∈ range h, F (3*h+i+1)) := by
    rw [show 4*h=3*h+h by omega, sum_range_add,
      show 3*h=2*h+h by omega, sum_range_add, show 2*h=h+h by omega, sum_range_add]
    simp
  rw [total,split,split,split,split,reflect_block F h m,reflect_block F (3*h) m]
  simp only [sum_add_distrib,zero_add]
  have h2 : h+m+1=2*h := by dsimp [h]; omega
  have h3 : 2*h+m+1=3*h := by dsimp [h]; omega
  have h4 : 3*h+m+1=4*h := by dsimp [h]; omega
  rw [h2,h3,h4]
  simp only [Nat.add_assoc]
  abel

end OMA.WhiteFold241


/- Bounds a periodic quadratic Fourier majorant by splitting it into residue classes. -/

namespace OMA.WhiteTail241

open Filter MeasureTheory Set Finset

private theorem power_tail :
    ∑' k : ℕ, ((k + 2 : ℕ) : ℝ) ^ (-8 / 3 : ℝ) ≤ 7 / 20 := by
  let f (x : ℝ) := x ^ (-8 / 3 : ℝ)
  have ha : AntitoneOn f (Ici (2 : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by have := mem_Ici.mp hx; linarith) hxy (by norm_num)
  have hi : IntegrableOn f (Ioi 2) := integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := f) 2 (by simpa using ha)
    (by simpa using hi) (by intro t ht; exact Real.rpow_nonneg (by simpa using (le_of_lt ht).trans' (by norm_num : (0:ℝ) ≤ (2:ℕ))) _)
  change ∑' n : ℕ, f (n + 2 + 1 : ℕ) ≤ ∫ x in Ioi (2:ℝ), x ^ (-8/3:ℝ) at htail
  rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num), Real.rpow_add (by norm_num : (0:ℝ)<2), Real.rpow_one] at htail
  have hc : ((2:ℝ) ^ (-8/3:ℝ)) ^ 3 = 1 / 256 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hb : (2:ℝ) ^ (-8/3:ℝ) ≤ 7/44 := by
    by_contra! hh
    have h := pow_lt_pow_left₀ hh (by norm_num : 0 ≤ (7:ℝ)/44) (by decide : 3 ≠ 0)
    rw [hc] at h
    norm_num at h
  have hs := (summable_nat_add_iff 2).2 (Real.summable_nat_rpow.mpr (by norm_num : (-8/3:ℝ)< -1))
  rw [hs.tsum_eq_zero_add]
  change (2:ℝ)^(-8/3:ℝ) + (∑' n : ℕ, f (n + 1 + 2 : ℕ)) ≤ _
  change (2:ℝ)^(-8/3:ℝ) + (∑' n : ℕ, f (n + 2 + 1 : ℕ)) ≤ _
  rw [show -(2^(-8/3:ℝ)*2) / (-8/3+1) = (6/5:ℝ)*2^(-8/3:ℝ) by ring] at htail
  linarith only [htail, hb]

private lemma div_sq_rpow (a x p : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    (a / x^2)^p = a^p * x^(-(2*p)) := by
  rw [Real.div_rpow ha (sq_nonneg _), ←Real.rpow_natCast x 2, ←Real.rpow_mul hx,
    Real.rpow_neg hx, div_eq_mul_inv]
  norm_num

private lemma majorant_summable {Q : ℕ} (hq : 0 < Q) (B : ℕ → ℝ) (a : Fin Q → ℝ)
    (hB : ∀ n, 0 ≤ B n) (ha : ∀ r, 0 ≤ a r)
    (bound : ∀ (r : Fin Q) (k : ℕ), B (r.val+1+k*Q) ≤
      a r / ((r.val+1+k*Q : ℕ):ℝ)^2)
    (p : ℝ) (hp : 1 ≤ p) : Summable (fun n : ℕ => B (n+1)^p) := by
  let A := ∑ r, a r
  have hA : 0 ≤ A := sum_nonneg fun i _ => ha i
  have hmax (n : ℕ) : B (n+1) ≤ A / ((n+1:ℕ):ℝ)^2 := by
    let r : Fin Q := ⟨n%Q, Nat.mod_lt n hq⟩
    have he : r.val + 1 + n / Q * Q = n + 1 := by
      have := Nat.div_add_mod' n Q
      dsimp [r]
      omega
    have h := bound r (n/Q)
    rw [he] at h
    exact h.trans (div_le_div_of_nonneg_right (single_le_sum (fun i _ => ha i) (mem_univ r)) (sq_nonneg _))
  have hs := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr (by linarith : -(2*p) < -1))
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (hB _) _) (fun n => ?_) (hs.mul_left (A^p))
  exact (Real.rpow_le_rpow (hB _) (hmax n) (by linarith)).trans_eq (div_sq_rpow _ _ _ hA (by positivity))

/-- Sum positive modes of a quadratic majorant with periodic numerator. -/
theorem period_total {Q : ℕ} (hq : 0 < Q) (B : ℕ → ℝ) (a : Fin Q → ℝ)
    (hB : ∀ n, 0 ≤ B n) (ha : ∀ r, 0 ≤ a r)
    (bound : ∀ (r : Fin Q) (k : ℕ), B (r.val+1+k*Q) ≤
      a r / ((r.val+1+k*Q : ℕ):ℝ)^2) :
    Summable (fun n : ℕ => B (n+1)) ∧ Summable (fun n : ℕ => B (n+1)^(4/3:ℝ)) ∧
      ∑' n : ℕ, B (n+1)^(4/3:ℝ) ≤ ∑ r : Fin Q,
        ((a r / ((r.val+1:ℕ):ℝ)^2)^(4/3:ℝ) +
         (a r / ((r.val+1+Q:ℕ):ℝ)^2)^(4/3:ℝ) +
         (7/20)*(a r/(Q:ℝ)^2)^(4/3:ℝ)) := by
  have hs := majorant_summable hq B a hB ha bound (4/3) (by norm_num)
  refine ⟨by simpa using majorant_summable hq B a hB ha bound 1 (by norm_num), hs, ?_⟩
  let : NeZero Q := ⟨hq.ne'⟩
  let e : Fin Q × ℕ ≃ ℕ := (Equiv.prodComm _ _).trans (Nat.divModEquiv Q).symm
  let f (p : Fin Q × ℕ) := B (e p + 1)^(4/3:ℝ)
  have hsf : Summable f := e.summable_iff.mpr hs
  rw [←e.tsum_eq (fun n => B (n+1)^(4/3:ℝ))]
  change ∑' p, f p ≤ _
  rw [hsf.tsum_prod, tsum_fintype]
  apply sum_le_sum
  intro r _
  have hf (k : ℕ) : f (r,k) = B (r.val + 1 + k*Q)^(4/3:ℝ) := by
    change B (k*Q+r.val+1) ^ _ = _
    congr 2; omega
  have hsfr := hsf.prod_factor r
  let C := (a r/(Q:ℝ)^2)^(4/3:ℝ)
  have hC : 0 ≤ C := Real.rpow_nonneg (div_nonneg (ha _) (sq_nonneg _)) _
  have htail (k : ℕ) : f (r,k+2) ≤ C * ((k+2:ℕ):ℝ)^(-8/3:ℝ) := by
    rw [hf]
    have hn : (0:ℝ) < (k+2:ℕ) * Q := by exact_mod_cast Nat.mul_pos (by omega) hq
    have hden : (((k+2:ℕ):ℝ) * Q)^2 ≤ ((r.val+1+(k+2)*Q:ℕ):ℝ)^2 := by
      gcongr
      exact_mod_cast Nat.le_add_left _ _
    calc
      _ ≤ (a r / ((r.val+1+(k+2)*Q:ℕ):ℝ)^2)^(4/3:ℝ) :=
        Real.rpow_le_rpow (hB _) (bound _ _) (by norm_num)
      _ ≤ (a r / ((((k+2:ℕ):ℝ)*Q)^2))^(4/3:ℝ) :=
        Real.rpow_le_rpow (div_nonneg (ha _) (sq_nonneg _))
          (div_le_div_of_nonneg_left (ha _) (sq_pos_of_pos hn) hden) (by norm_num)
      _ = C * ((k+2:ℕ):ℝ)^(-8/3:ℝ) := by
        rw [mul_pow, mul_comm (((k+2:ℕ):ℝ)^2), ←div_div, div_sq_rpow]
        · norm_num [C]
        · exact div_nonneg (ha _) (sq_nonneg _)
        · positivity
  have ht := ((summable_nat_add_iff 2).2 hsfr).tsum_le_tsum htail
    (((summable_nat_add_iff 2).2 (Real.summable_nat_rpow.mpr (by norm_num : (-8/3:ℝ)< -1))).mul_left C)
  rw [tsum_mul_left] at ht
  have hd := ht.trans (mul_le_mul_of_nonneg_left power_tail hC)
  rw [←hsfr.sum_add_tsum_nat_add 2]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [hf, hf]
  simp only [zero_mul, add_zero, one_mul]
  have h0 := Real.rpow_le_rpow (hB _) (bound r 0) (by norm_num : (0:ℝ) ≤ 4/3)
  have h1 := Real.rpow_le_rpow (hB _) (bound r 1) (by norm_num : (0:ℝ) ≤ 4/3)
  simp only [zero_mul, add_zero, one_mul] at h0 h1
  simpa [C, mul_comm C] using add_le_add (add_le_add h0 h1) hd

end OMA.WhiteTail241

/-
# A Fourier dual bound for additive energy

This proof generalizes the pairing and Bessel argument from this repository's
Green 35 proof (PR 1718, commit 1b5477c2) to any even coefficient profile.
-/

namespace OMA.WhiteDual241

open MeasureTheory Filter Topology
open scoped Convolution ENNReal Real

private instance : Fact ((0 : ℝ) < 2) := ⟨by norm_num⟩

/- ## Elementary helpers for `fourier` on `AddCircle (2 : ℝ)` -/

private lemma fourier2_coe (n : ℤ) (x : ℝ) :
    @fourier 2 n (x : AddCircle (2 : ℝ)) = Complex.exp (Real.pi * Complex.I * n * x) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast; ring

private lemma fourier2_norm (n : ℤ) (x : ℝ) :
    ‖@fourier 2 n (x : AddCircle (2 : ℝ))‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

private lemma fourier2_zero (x : ℝ) :
    @fourier 2 0 (x : AddCircle (2 : ℝ)) = 1 := by
  simp

private lemma fourier2_add (n : ℤ) (x y : ℝ) :
    @fourier 2 n ((x + y : ℝ) : AddCircle (2 : ℝ)) =
      @fourier 2 n (x : AddCircle (2 : ℝ)) * @fourier 2 n (y : AddCircle (2 : ℝ)) := by
  rw [fourier2_coe, fourier2_coe, fourier2_coe, ← Complex.exp_add]
  congr 1; push_cast; ring

private lemma fourier2_mul_conj (n m : ℤ) (x : ℝ) :
    @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * starRingEnd ℂ (@fourier 2 (-m) (x : AddCircle (2 : ℝ))) =
      @fourier 2 (m - n) (x : AddCircle (2 : ℝ)) := by
  rw [← fourier_neg, neg_neg, fourier2_coe, fourier2_coe, fourier2_coe, ← Complex.exp_add]
  congr 1; push_cast; ring

private lemma intervalIntegral_fourier2 (k : ℤ) :
    ∫ x in (0 : ℝ)..2, @fourier 2 k (x : AddCircle (2 : ℝ)) = if k = 0 then (2 : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp_rw [fourier2_zero]
    simp
  · simp_rw [fourier2_coe]
    let c : ℂ := Real.pi * Complex.I * (k : ℂ)
    have hc : c ≠ 0 := by
      simp only [c, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, Real.pi_ne_zero,
        Complex.I_ne_zero, Int.cast_eq_zero, hk, or_self, not_false_eq_true]
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 2,
        HasDerivAt (fun t : ℝ => Complex.exp (c * t) / c) (Complex.exp (c * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) (c * 1) x :=
        (Complex.ofRealCLM.hasDerivAt).const_mul c
      rw [mul_one] at h1
      have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)))
          (Complex.exp (c * (x : ℂ)) * c) x := h1.cexp
      have h3 := h2.div_const c
      rwa [mul_div_cancel_right₀ _ hc] at h3
    have hint : IntervalIntegrable (fun x : ℝ => Complex.exp (c * (x : ℂ))) volume 0 2 :=
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
    have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hrew : (fun x : ℝ => Complex.exp (Real.pi * Complex.I * (k : ℂ) * (x : ℂ))) =
        (fun x : ℝ => Complex.exp (c * (x : ℂ))) := rfl
    rw [hrew, hval]
    have hexp2 : Complex.exp (c * (2 : ℂ)) = 1 := by
      have : c * (2 : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by simp only [c]; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    simp [hexp2]


/- ## Main Fourier-analytic lower bound for unit-interval densities -/

private lemma convolution_support_subset {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (0 : ℝ) 1) :
    Function.support (f ⋆ f) ⊆ Set.Icc (0 : ℝ) 2 := by
  intro z hz
  by_contra hnot
  apply hz
  rw [convolution_lsmul]
  have hzero : ∀ t : ℝ, f t * f (z - t) = 0 := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · have hzt : z - t ∉ Set.Icc (0 : ℝ) 1 := by
        intro hzt
        exact hnot ⟨by linarith [ht.1, hzt.1], by linarith [ht.2, hzt.2]⟩
      have hfz : f (z - t) = 0 := by
        by_contra hne
        exact hzt (hsupp hne)
      rw [hfz, mul_zero]
    · have hft : f t = 0 := by
        by_contra hne
        exact ht (hsupp hne)
      rw [hft, zero_mul]
  simp [hzero]

private lemma fourier_coeff_conv {f : ℝ → ℝ} (hfi : Integrable f)
    (hsupp : Function.support f ⊆ Set.Icc (0 : ℝ) 1) (n : ℤ) :
    ∫ z in Set.Ioc (0 : ℝ) 2, ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) =
      (∫ x, (f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ))) ^ 2 := by
  have hgsupp := convolution_support_subset hsupp
  have hIoc : ∫ z in Set.Ioc (0 : ℝ) 2, ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) =
      ∫ z, ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine integral_congr_ae ?_
    have hne0 : ∀ᵐ z : ℝ ∂volume, z ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [hne0] with z hz0
    by_cases hz : z ∈ Set.Ioc (0 : ℝ) 2
    · simp [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz]
      have hnotIcc : z ∉ Set.Icc (0 : ℝ) 2 := by
        intro h; exact hz ⟨lt_of_le_of_ne h.1 hz0.symm, h.2⟩
      have hg0 : (f ⋆ f) z = 0 := by
        by_contra hne
        exact hnotIcc (hgsupp hne)
      simp [hg0]
  rw [hIoc]
  let φ : ℝ → ℂ := fun x => (f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ))
  have hφ_int : Integrable φ := by
    refine Integrable.mono' hfi.norm ?_ ?_
    · have hcont : Continuous (fun x : ℝ => @fourier 2 n (x : AddCircle (2 : ℝ))) := by
        simp_rw [fourier2_coe]; fun_prop
      exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hfi.aestronglyMeasurable).mul
        hcont.aestronglyMeasurable
    · filter_upwards with x
      simp only [φ, norm_mul, Complex.norm_real, fourier2_norm, mul_one, le_refl]
  have hconv_eq : ∀ z : ℝ,
      ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) =
        (φ ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] φ) z := by
    intro z
    rw [convolution_lsmul, convolution_def]
    simp only [ContinuousLinearMap.mul_apply', φ]
    have hofReal : ((∫ t : ℝ, f t * f (z - t) : ℝ) : ℂ) = ∫ t : ℝ, ((f t * f (z - t) : ℝ) : ℂ) := by
      simp_rw [← Complex.coe_algebraMap]
      exact (integral_ofReal (𝕜 := ℂ)).symm
    simp only [smul_eq_mul]
    rw [hofReal, ← integral_mul_const]
    congr 1; funext t
    have hsplit : @fourier 2 n (z : AddCircle (2 : ℝ)) =
        @fourier 2 n (t : AddCircle (2 : ℝ)) * @fourier 2 n ((z - t : ℝ) : AddCircle (2 : ℝ)) := by
      have : z = t + (z - t) := by ring
      conv_lhs => rw [this]
      exact fourier2_add n t (z - t)
    rw [hsplit]
    push_cast; ring
  simp_rw [hconv_eq]
  rw [integral_convolution (ContinuousLinearMap.mul ℝ ℂ) hφ_int hφ_int]
  simp only [ContinuousLinearMap.mul_apply', sq, φ]

private lemma bessel_Ioc_two {g : ℝ → ℝ} (hgi : Integrable g)
    (hg_sq : Integrable (fun z => (g z) ^ 2))
    (c : ℤ → ℂ)
    (hc : ∀ n : ℤ, ∫ z in Set.Ioc (0 : ℝ) 2, (g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) = c n)
    (F : Finset ℤ) :
    (1 / 2 : ℝ) * ∑ n ∈ F, ‖c n‖ ^ 2 ≤ ∫ z in Set.Ioc (0 : ℝ) 2, (g z) ^ 2 := by
  let S : ℝ → ℂ := fun z => (1 / 2 : ℂ) * ∑ n ∈ F, c n * @fourier 2 (-n) (z : AddCircle (2 : ℝ))
  have hS_cont : Continuous S := by
    simp only [S]
    refine continuous_const.mul (continuous_finsetSum F fun n _ => ?_)
    simp_rw [fourier2_coe]; fun_prop
  have hS2_int : IntegrableOn (fun z => ‖S z‖ ^ 2) (Set.Ioc (0 : ℝ) 2) volume :=
    (hS_cont.norm.pow 2).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hg2_int : IntegrableOn (fun z => (g z) ^ 2) (Set.Ioc (0 : ℝ) 2) volume :=
    hg_sq.integrableOn
  have hcross_int : IntegrableOn (fun z => (g z : ℂ) * starRingEnd ℂ (S z))
      (Set.Ioc (0 : ℝ) 2) volume := by
    refine Integrable.mono' (hg2_int.add hS2_int) ?_ ?_
    · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
        hgi.aestronglyMeasurable.restrict).mul
        (Complex.continuous_conj.comp hS_cont).aestronglyMeasurable
    · filter_upwards with z
      simp only [Pi.add_apply]
      rw [norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_eq_abs]
      nlinarith [sq_nonneg (|g z| - ‖S z‖), sq_abs (g z)]
  have hcross_re_int : IntegrableOn (fun z => ((g z : ℂ) * starRingEnd ℂ (S z)).re)
      (Set.Ioc (0 : ℝ) 2) volume :=
    Complex.reCLM.integrable_comp hcross_int
  have hexpand : ∀ z : ℝ,
      ‖(g z : ℂ) - S z‖ ^ 2 =
        (g z) ^ 2 - 2 * ((g z : ℂ) * starRingEnd ℂ (S z)).re + ‖S z‖ ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hnonneg : 0 ≤ ∫ z in Set.Ioc (0 : ℝ) 2, ‖(g z : ℂ) - S z‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  simp_rw [hexpand] at hnonneg
  have hsplit_int :
      ∫ z in Set.Ioc (0 : ℝ) 2,
          ((g z) ^ 2 - 2 * ((g z : ℂ) * starRingEnd ℂ (S z)).re + ‖S z‖ ^ 2) =
        (∫ z in Set.Ioc (0 : ℝ) 2, (g z) ^ 2) -
        2 * (∫ z in Set.Ioc (0 : ℝ) 2, ((g z : ℂ) * starRingEnd ℂ (S z)).re) +
        (∫ z in Set.Ioc (0 : ℝ) 2, ‖S z‖ ^ 2) := by
    have hadd := integral_add (hg2_int.sub (hcross_re_int.const_mul 2)) hS2_int
    have hsub := integral_sub hg2_int (hcross_re_int.const_mul 2)
    have hmul := integral_const_mul (μ := volume.restrict (Set.Ioc (0 : ℝ) 2))
      (2 : ℝ) (fun z => ((g z : ℂ) * starRingEnd ℂ (S z)).re)
    dsimp only [Pi.add_apply, Pi.sub_apply] at hadd hsub
    rw [hadd, hsub, hmul]
  rw [hsplit_int] at hnonneg
  have hcross_val :
      ∫ z in Set.Ioc (0 : ℝ) 2, ((g z : ℂ) * starRingEnd ℂ (S z)).re =
        (1 / 2 : ℝ) * ∑ n ∈ F, ‖c n‖ ^ 2 := by
    have hre : ∫ z in Set.Ioc (0 : ℝ) 2, ((g z : ℂ) * starRingEnd ℂ (S z)).re =
        (∫ z in Set.Ioc (0 : ℝ) 2, (g z : ℂ) * starRingEnd ℂ (S z)).re :=
      Complex.reCLM.integral_comp_comm hcross_int
    rw [hre]
    have hpt : (fun z : ℝ => (g z : ℂ) * starRingEnd ℂ (S z)) =
        fun z : ℝ => (1 / 2 : ℂ) * ∑ n ∈ F,
          starRingEnd ℂ (c n) * ((g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ))) := by
      funext z
      simp only [S, map_mul, map_div₀, map_one, map_ofNat, map_sum, ← fourier_neg, neg_neg,
        Finset.mul_sum]
      ring_nf
    rw [hpt, integral_const_mul, integral_finsetSum]
    · have hterm : ∀ n ∈ F,
          ∫ z in Set.Ioc (0 : ℝ) 2,
            starRingEnd ℂ (c n) * ((g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ))) =
          starRingEnd ℂ (c n) * c n := by
        intro n _
        rw [integral_const_mul, hc n]
      rw [Finset.sum_congr rfl hterm]
      have hdiv : ((1 / 2 : ℂ) * ∑ n ∈ F, starRingEnd ℂ (c n) * c n).re =
          (1 / 2 : ℝ) * (∑ n ∈ F, starRingEnd ℂ (c n) * c n).re := by
        simp [Complex.mul_re]
      rw [hdiv, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
    · intro n _
      have hcont : Continuous (fun z : ℝ => @fourier 2 n (z : AddCircle (2 : ℝ))) := by
        simp_rw [fourier2_coe]; fun_prop
      have hgn : IntegrableOn (fun z : ℝ => (g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)))
          (Set.Ioc (0 : ℝ) 2) volume := by
        refine Integrable.mono' hgi.norm.integrableOn ?_ ?_
        · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
            hgi.aestronglyMeasurable.restrict).mul hcont.aestronglyMeasurable
        · filter_upwards with z
          simp only [norm_mul, Complex.norm_real, fourier2_norm, mul_one, le_refl]
      exact hgn.const_mul _
  have hS2_val :
      ∫ z in Set.Ioc (0 : ℝ) 2, ‖S z‖ ^ 2 = (1 / 2 : ℝ) * ∑ n ∈ F, ‖c n‖ ^ 2 := by
    have hpt : (fun z : ℝ => ‖S z‖ ^ 2) = fun z : ℝ => (S z * starRingEnd ℂ (S z)).re := by
      funext z; rw [Complex.sq_norm]; simp [Complex.normSq_apply]
    rw [hpt]
    have hSS_int : IntegrableOn (fun z : ℝ => S z * starRingEnd ℂ (S z))
        (Set.Ioc (0 : ℝ) 2) volume :=
      (hS_cont.mul (Complex.continuous_conj.comp hS_cont)).continuousOn.integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self
    have hre2 : ∫ z in Set.Ioc (0 : ℝ) 2, (S z * starRingEnd ℂ (S z)).re =
        (∫ z in Set.Ioc (0 : ℝ) 2, S z * starRingEnd ℂ (S z)).re :=
      Complex.reCLM.integral_comp_comm hSS_int
    rw [hre2]
    have hexp : (fun z : ℝ => S z * starRingEnd ℂ (S z)) =
        fun z : ℝ => (1 / 4 : ℂ) * ∑ n ∈ F, ∑ m ∈ F,
          (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) := by
      funext z
      simp only [S, map_mul, map_div₀, map_one, map_ofNat, map_sum]
      calc (1 / 2 : ℂ) * (∑ n ∈ F, c n * @fourier 2 (-n) (z : AddCircle (2 : ℝ))) *
            ((1 / 2 : ℂ) * ∑ m ∈ F, starRingEnd ℂ (c m) *
              starRingEnd ℂ (@fourier 2 (-m) (z : AddCircle (2 : ℝ))))
          = (1 / 4 : ℂ) * ((∑ n ∈ F, c n * @fourier 2 (-n) (z : AddCircle (2 : ℝ))) *
              (∑ m ∈ F, starRingEnd ℂ (c m) *
                starRingEnd ℂ (@fourier 2 (-m) (z : AddCircle (2 : ℝ))))) := by ring
        _ = (1 / 4 : ℂ) * ∑ n ∈ F, ∑ m ∈ F,
              (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) := by
            congr 1
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [← fourier2_mul_conj n m z]; ring
    rw [hexp, integral_const_mul, integral_finsetSum]
    · have hinner : ∀ n ∈ F,
          ∫ z in Set.Ioc (0 : ℝ) 2, ∑ m ∈ F,
            (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) =
          (c n * starRingEnd ℂ (c n)) * (2 : ℂ) := by
        intro n hn
        rw [integral_finsetSum]
        · have hterm : ∀ m ∈ F,
              ∫ z in Set.Ioc (0 : ℝ) 2,
                (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) =
              if m = n then (c n * starRingEnd ℂ (c m)) * (2 : ℂ) else 0 := by
            intro m _
            rw [integral_const_mul, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
              intervalIntegral_fourier2 (m - n)]
            by_cases hmn : m = n
            · subst hmn; simp
            · have : m - n ≠ 0 := sub_ne_zero.mpr hmn
              simp [hmn, this]
          rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' F n, if_pos hn]
        · intro m _
          have hcont : Continuous (fun z : ℝ =>
              (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ))) := by
            simp_rw [fourier2_coe]; fun_prop
          exact hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      rw [Finset.sum_congr rfl hinner]
      have hdiv : ((1 / 4 : ℂ) * ∑ n ∈ F, c n * starRingEnd ℂ (c n) * 2).re =
          (1 / 2 : ℝ) * (∑ n ∈ F, c n * starRingEnd ℂ (c n)).re := by
        rw [← Finset.sum_mul, show (1 / 4 : ℂ) * ((∑ n ∈ F, c n * starRingEnd ℂ (c n)) * 2) =
            (1 / 2 : ℂ) * ∑ n ∈ F, c n * starRingEnd ℂ (c n) by ring]
        simp [Complex.mul_re]
      rw [hdiv, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
    · intro n _
      have hcont : Continuous (fun z : ℝ => ∑ m ∈ F,
          (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ))) := by
        refine continuous_finsetSum F fun m _ => ?_
        simp_rw [fourier2_coe]; fun_prop
      exact hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  linarith

theorem dual (U : C(AddCircle (2:ℝ),ℂ)) (pHat : ℕ → ℝ)
    (U_coe_of_mem_Icc01 : ∀ x ∈ Set.Icc (0:ℝ) 1, U (x : AddCircle (2:ℝ)) = 1)
    (fourierCoeff_U_zero : fourierCoeff U 0 = 0)
    (norm_fourierCoeff_U : ∀ n : ℤ, n ≠ 0 → ‖fourierCoeff U n‖ = pHat n.natAbs / 2)
    (hhat : ∀ n, 0 ≤ pHat n)
    (summable_fourierCoeff_U : Summable (fourierCoeff U))
    (summable_pHat_rpow : Summable (fun r : ℕ => pHat (r+1) ^ (4/3:ℝ)))
    {K : ℝ} (hK : 0 < K)
    (hS3 : (∑' r : ℕ, pHat (r+1) ^ (4/3:ℝ))^3 ≤ K)
    {f : ℝ → ℝ} (hf : OMA.Energy241.UnitDensity f)
    (hgi : Integrable (f ⋆ f))
    (hgsq : Integrable (fun z => ((f ⋆ f) z)^2)) :
    1/2 + 1/K ≤ ∫ z, ((f ⋆ f) z)^2 := by
  obtain ⟨hfi, hf0, hfsupp, hf1⟩ := hf
  let c : ℤ → ℂ := fun n => ∫ x, (f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ))
  have hc0 : c 0 = 1 := by
    simp only [c, fourier2_zero, mul_one]
    have h1 : ∫ x : ℝ, (f x : ℂ) = ((∫ x : ℝ, f x : ℝ) : ℂ) :=
      Complex.ofRealCLM.integral_comp_comm hfi
    rw [h1, hf1, Complex.ofReal_one]
  have hc_neg : ∀ n : ℤ, ‖c (-n)‖ = ‖c n‖ := by
    intro n
    have hconj : c (-n) = starRingEnd ℂ (c n) := by
      simp only [c]
      rw [← integral_conj]
      congr 1; funext x
      rw [map_mul, Complex.conj_ofReal, fourier_neg]
    rw [hconj, Complex.norm_conj]
  -- Step 1: Bessel inequality for c n ^ 2 via f ⋆ f
  have hg_Ioc : ∫ z in Set.Ioc (0 : ℝ) 2, ((f ⋆ f) z) ^ 2 = ∫ z, ((f ⋆ f) z) ^ 2 := by
    have hgsupp := convolution_support_subset hfsupp
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine integral_congr_ae ?_
    have hne0 : ∀ᵐ z : ℝ ∂volume, z ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne0] with z hz0
    by_cases hz : z ∈ Set.Ioc (0 : ℝ) 2
    · simp [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz]
      have hnotIcc : z ∉ Set.Icc (0 : ℝ) 2 := fun h => hz ⟨lt_of_le_of_ne h.1 hz0.symm, h.2⟩
      have hg0 : (f ⋆ f) z = 0 := by by_contra hne; exact hnotIcc (hgsupp hne)
      simp [hg0]
  have hbessel_partial : ∀ N : ℕ,
      ∑ r ∈ Finset.range N, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 ≤ (∫ z, ((f ⋆ f) z) ^ 2) - 1 / 2 := by
    intro N
    let F : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
    have hb := bessel_Ioc_two hgi hgsq (fun n => c n ^ 2) (fourier_coeff_conv hfi hfsupp) F
    rw [hg_Ioc] at hb
    have hsum_F : ∑ n ∈ F, ‖c n ^ 2‖ ^ 2 = 1 + 2 * ∑ r ∈ Finset.range N, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 := by
      have hF_eq : F = insert (0 : ℤ)
          ((Finset.range N).image (fun r : ℕ => ((r + 1 : ℕ) : ℤ)) ∪
           (Finset.range N).image (fun r : ℕ => -((r + 1 : ℕ) : ℤ))) := by
        ext n
        simp only [F, Finset.mem_Icc, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
          Finset.mem_range]
        constructor
        · intro ⟨h1, h2⟩
          by_cases hn0 : n = 0
          · exact Or.inl hn0
          · right
            by_cases hpos : 0 < n
            · left; exact ⟨(n - 1).toNat, by omega, by omega⟩
            · right; exact ⟨(-n - 1).toNat, by omega, by omega⟩
        · rintro (rfl | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) <;> omega
      rw [hF_eq, Finset.sum_insert (by
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
        rintro (⟨r, _, hr⟩ | ⟨r, _, hr⟩) <;> omega)]
      have hdisj : Disjoint ((Finset.range N).image (fun r : ℕ => ((r + 1 : ℕ) : ℤ)))
          ((Finset.range N).image (fun r : ℕ => -((r + 1 : ℕ) : ℤ))) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finset.mem_image] at hx1 hx2
        obtain ⟨a, _, rfl⟩ := hx1
        obtain ⟨b, _, hb⟩ := hx2
        omega
      rw [Finset.sum_union hdisj,
        Finset.sum_image (by intro a _ b _ h; dsimp at h; omega),
        Finset.sum_image (by intro a _ b _ h; dsimp at h; omega)]
      simp only [hc0, one_pow, norm_one, norm_pow]
      have hpow4 : ∀ z : ℂ, (‖z‖ ^ 2) ^ 2 = ‖z‖ ^ 4 := fun z => by ring
      simp_rw [hpow4, hc_neg]
      ring
    rw [hsum_F] at hb
    have hsimp : (1 / 2 : ℝ) * (1 + 2 * ∑ r ∈ Finset.range N, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4) =
        1 / 2 + ∑ r ∈ Finset.range N, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 := by ring
    linarith
  have hc_summable : Summable (fun r : ℕ => ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4) :=
    summable_of_sum_range_le (fun _ => by positivity) hbessel_partial
  have hc_tsum_le : ∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 ≤ (∫ z, ((f ⋆ f) z) ^ 2) - 1 / 2 :=
    hc_summable.tsum_le_of_sum_range_le hbessel_partial
  -- Step 2: Pair f with the Fourier series of U
  have hpair : (1 : ℂ) = ∑' n : ℤ, fourierCoeff U n * c n := by
    have hF_int : ∀ n : ℤ,
        Integrable (fun x : ℝ => (f x : ℂ) * (fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ)))) := by
      intro n
      have hcont : Continuous (fun x : ℝ => fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ))) := by
        simp_rw [fourier2_coe]; fun_prop
      refine Integrable.mono' (hfi.norm.const_mul ‖fourierCoeff U n‖) ?_ ?_
      · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hfi.aestronglyMeasurable).mul
          hcont.aestronglyMeasurable
      · filter_upwards with x
        rw [norm_mul, norm_mul, Complex.norm_real, fourier2_norm, mul_one, mul_comm]
    have hF_norm_eq : ∀ n : ℤ,
        ∫ x : ℝ, ‖(f x : ℂ) * (fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ)))‖ =
          ‖fourierCoeff U n‖ := by
      intro n
      have hpt : (fun x : ℝ => ‖(f x : ℂ) * (fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ)))‖) =
          (fun x : ℝ => ‖fourierCoeff U n‖ * f x) := by
        funext x
        rw [norm_mul, norm_mul, fourier2_norm, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (hf0 x), mul_comm]
      rw [hpt, integral_const_mul, hf1, mul_one]
    have hF_sum : Summable (fun n : ℤ =>
        ∫ x : ℝ, ‖(f x : ℂ) * (fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ)))‖) := by
      simp_rw [hF_norm_eq]
      exact summable_fourierCoeff_U.norm
    have hhas := hasSum_integral_of_summable_integral_norm hF_int hF_sum
    have htsum_pt : ∀ x : ℝ,
        (∑' n : ℤ, (f x : ℂ) * (fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ)))) =
          (f x : ℂ) := by
      intro x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
      · have hU := has_pointwise_sum_fourier_series_of_summable summable_fourierCoeff_U
            (x : AddCircle (2 : ℝ))
        rw [U_coe_of_mem_Icc01 _ hx] at hU
        have hmul := hU.mul_left (f x : ℂ)
        simpa [smul_eq_mul] using hmul.tsum_eq
      · have hfx : f x = 0 := by by_contra hne; exact hx (hfsupp hne)
        simp [hfx]
    simp_rw [htsum_pt] at hhas
    have hint1 : ∫ x : ℝ, (f x : ℂ) = 1 := by
      have h1 : ∫ x : ℝ, (f x : ℂ) = ((∫ x : ℝ, f x : ℝ) : ℂ) :=
        Complex.ofRealCLM.integral_comp_comm hfi
      rw [h1, hf1, Complex.ofReal_one]
    rw [hint1] at hhas
    have hterm_eq : ∀ n : ℤ,
        ∫ x : ℝ, (f x : ℂ) * (fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ))) =
          fourierCoeff U n * c n := by
      intro n
      have : (fun x : ℝ => (f x : ℂ) * (fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ)))) =
          (fun x : ℝ => fourierCoeff U n * ((f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ)))) := by
        funext x; ring
      rw [this, integral_const_mul]
    simp_rw [hterm_eq] at hhas
    exact hhas.tsum_eq.symm
  -- Step 3: Triangle inequality and fold ℤ into ℕ
  have hnorm_sum : Summable (fun n : ℤ => ‖fourierCoeff U n * c n‖) := by
    have hcn_le : ∀ n : ℤ, ‖c n‖ ≤ 1 := by
      intro n
      calc ‖c n‖ ≤ ∫ x, ‖(f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ))‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ x, f x := by
            congr 1; funext x
            rw [norm_mul, fourier2_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (hf0 x)]
        _ = 1 := hf1
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ summable_fourierCoeff_U.norm
    intro n
    rw [norm_mul]
    calc ‖fourierCoeff U n‖ * ‖c n‖ ≤ ‖fourierCoeff U n‖ * 1 := by gcongr; exact hcn_le n
      _ = ‖fourierCoeff U n‖ := mul_one _
  have h1_le_int : (1 : ℝ) ≤ ∑' n : ℤ, ‖fourierCoeff U n‖ * ‖c n‖ := by
    calc (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
      _ = ‖∑' n : ℤ, fourierCoeff U n * c n‖ := by rw [hpair]
      _ ≤ ∑' n : ℤ, ‖fourierCoeff U n * c n‖ := norm_tsum_le_tsum_norm hnorm_sum
      _ = ∑' n : ℤ, ‖fourierCoeff U n‖ * ‖c n‖ := by simp_rw [norm_mul]
  have hfold : ∑' n : ℤ, ‖fourierCoeff U n‖ * ‖c n‖ =
      ∑' r : ℕ, pHat (r + 1) * ‖c ((r + 1 : ℕ) : ℤ)‖ := by
    let g_int : ℤ → ℝ := fun n => ‖fourierCoeff U n‖ * ‖c n‖
    have hs_int : Summable g_int := by simpa [g_int, norm_mul] using hnorm_sum
    have hs_nat : Summable (fun n : ℕ => g_int n) := hs_int.comp_injective Int.ofNat_injective
    have hs_neg : Summable (fun n : ℕ => g_int (-((n : ℤ) + 1))) :=
      hs_int.comp_injective (by intro a b h; dsimp at h; omega)
    change ∑' n : ℤ, g_int n = _
    rw [tsum_of_nat_of_neg_add_one hs_nat hs_neg]
    have hnat_succ : ∑' n : ℕ, g_int n = ∑' r : ℕ, g_int ((r + 1 : ℕ) : ℤ) := by
      rw [hs_nat.tsum_eq_zero_add]
      simp [g_int, fourierCoeff_U_zero]
    rw [hnat_succ]
    have hneg_eq : (fun r : ℕ => g_int (-((r : ℤ) + 1))) =
        (fun r : ℕ => g_int ((r + 1 : ℕ) : ℤ)) := by
      funext r
      have hcast : -((r : ℤ) + 1) = -((r + 1 : ℕ) : ℤ) := by push_cast; ring
      simp only [g_int, hcast, hc_neg]
      rw [norm_fourierCoeff_U (-((r + 1 : ℕ) : ℤ)) (by omega),
        norm_fourierCoeff_U ((r + 1 : ℕ) : ℤ) (by omega), Int.natAbs_neg]
    rw [hneg_eq, ← two_mul, ← tsum_mul_left]
    congr 1; funext r
    simp only [g_int]
    rw [norm_fourierCoeff_U ((r + 1 : ℕ) : ℤ) (by omega)]
    simp only [Int.natAbs_natCast]
    ring
  have h1_le_nat : (1 : ℝ) ≤ ∑' r : ℕ, pHat (r + 1) * ‖c ((r + 1 : ℕ) : ℤ)‖ := by
    linarith
  -- Step 4: Hölder's inequality with exponents (4/3, 4)
  have hconj : Real.HolderConjugate (4 / 3 : ℝ) 4 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h4eq : (fun r : ℕ => ‖c ((r + 1 : ℕ) : ℤ)‖ ^ (4 : ℝ)) =
      fun r : ℕ => ‖c ((r + 1 : ℕ) : ℤ)‖ ^ (4 : ℕ) := by
    funext r
    exact Real.rpow_natCast _ 4
  have hc_summable_rpow : Summable (fun r : ℕ => ‖c ((r + 1 : ℕ) : ℤ)‖ ^ (4 : ℝ)) := by
    rw [h4eq]; exact hc_summable
  have hholder := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hconj
    (fun r => hhat _) (fun r => norm_nonneg _) summable_pHat_rpow hc_summable_rpow
  have h1_le_prod : (1 : ℝ) ≤
      (∑' r : ℕ, pHat (r + 1) ^ (4 / 3 : ℝ)) ^ (1 / (4 / 3 : ℝ)) *
      (∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) :=
    h1_le_nat.trans hholder
  have hS_nn : 0 ≤ ∑' r : ℕ, pHat (r + 1) ^ (4 / 3 : ℝ) :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (hhat _) _)
  have hC_nn : 0 ≤ ∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ (4 : ℝ) :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hpow4 : (1 : ℝ) ≤
      (∑' r : ℕ, pHat (r + 1) ^ (4 / 3 : ℝ)) ^ 3 * (∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4) := by
    have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h1_le_prod 4
    rw [one_pow, mul_pow,
      ← Real.rpow_natCast (_ ^ (1 / (4 / 3 : ℝ))) 4, ← Real.rpow_mul hS_nn,
      ← Real.rpow_natCast (_ ^ (1 / (4 : ℝ))) 4, ← Real.rpow_mul hC_nn] at h4
    have e1 : 1 / (4 / 3 : ℝ) * (4 : ℕ) = ((3 : ℕ) : ℝ) := by norm_num
    have e2 : 1 / (4 : ℝ) * (4 : ℕ) = 1 := by norm_num
    rw [e1, e2, Real.rpow_natCast, Real.rpow_one, h4eq] at h4
    exact h4
  have hC_nn4 : 0 ≤ ∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 := tsum_nonneg (fun _ => by positivity)
  have h1_le_K : (1 : ℝ) ≤ K * ((∫ z, ((f ⋆ f) z) ^ 2) - 1 / 2) := by
    calc (1 : ℝ) ≤ (∑' r : ℕ, pHat (r + 1) ^ (4 / 3 : ℝ)) ^ 3 *
            (∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4) := hpow4
      _ ≤ K * (∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4) :=
          mul_le_mul_of_nonneg_right hS3 hC_nn4
      _ ≤ K * ((∫ z, ((f ⋆ f) z) ^ 2) - 1 / 2) :=
          mul_le_mul_of_nonneg_left hc_tsum_le hK.le
  have hx : 1/K ≤ (∫ z, ((f ⋆ f) z)^2) - 1/2 :=
    (div_le_iff₀ hK).mpr (by linarith [mul_comm K ((∫ z, ((f ⋆ f) z)^2) - 1/2)])
  linarith


/-- Use the usual normalization in which both positive and negative coefficient
masses contribute to D. The factor two is retained in the final energy bound. -/
theorem normalized (U : C(AddCircle (2:ℝ),ℂ)) (B : ℕ → ℝ)
    (hU : ∀ x ∈ Set.Icc (0:ℝ) 1, U (x : AddCircle (2:ℝ)) = 1)
    (hz : fourierCoeff U 0 = 0)
    (hcoef : ∀ n : ℤ, n ≠ 0 → ‖fourierCoeff U n‖ = B n.natAbs)
    (hb : ∀ n, 0 ≤ B n)
    (hsum : Summable (fun r : ℕ => B (r+1)))
    (hrp : Summable (fun r : ℕ => B (r+1) ^ (4/3:ℝ)))
    {D : ℝ} (hd : 0 < D) (bound : 2 * (∑' r : ℕ, B (r+1) ^ (4/3:ℝ)) ≤ D)
    {f : ℝ → ℝ} (hf : OMA.Energy241.UnitDensity f)
    (hgi : Integrable (f ⋆ f)) (hgsq : Integrable (fun x => ((f ⋆ f) x)^2)) :
    1/2 + 1/(2*D^3) ≤ ∫ x, ((f ⋆ f) x)^2 := by
  have hsNat : Summable (fun n : ℕ => ‖fourierCoeff U (n : ℤ)‖) := by
    apply (summable_nat_add_iff 1).mp
    have he (n : ℕ) : ‖fourierCoeff U ((n+1:ℕ):ℤ)‖ = B (n+1) := by
      rw [hcoef _ (by omega), Int.natAbs_natCast]
    simpa only [he] using hsum
  have hsNeg : Summable (fun n : ℕ => ‖fourierCoeff U (-((n:ℤ)+1))‖) := by
    convert hsum using 1
    funext n
    rw [hcoef _ (by omega)]
    congr 1
  have hsCoeff := Summable.of_norm (Summable.of_nat_of_neg_add_one hsNat hsNeg)
  let A := ∑' r : ℕ, B (r+1) ^ (4/3:ℝ)
  have hA : 0 ≤ A := tsum_nonneg (fun _ => Real.rpow_nonneg (hb _) _)
  have normeq (n : ℕ) : (2 * B n) ^ (4/3:ℝ) = (2:ℝ) ^ (4/3:ℝ) * B n ^ (4/3:ℝ) :=
    Real.mul_rpow (by norm_num) (hb _)
  apply dual U (fun n => 2*B n) hU hz
    (fun n hn => by rw [hcoef n hn]; ring) (fun n => mul_nonneg (by norm_num) (hb n))
    hsCoeff _ (by positivity : 0 < 2*D^3) _ hf hgi hgsq
  · simp_rw [normeq]
    exact hrp.mul_left _
  · simp_rw [normeq, tsum_mul_left]
    change ((2:ℝ)^(4/3:ℝ) * A)^3 ≤ _
    rw [mul_pow, ← Real.rpow_natCast ((2:ℝ) ^ (4/3:ℝ)), ← Real.rpow_mul (by norm_num)]
    norm_num
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 2*A) bound 3
    nlinarith only [h]

end OMA.WhiteDual241


/- Transfer a unit-interval autoconvolution bound to integer sample counts. -/

namespace OMA.Energy241

open MeasureTheory Finset Set
open scoped Convolution

noncomputable def box (h : ℝ) (i : ℕ) (x : ℝ) : ℝ :=
  (Ico ((i:ℝ)*h) (((i:ℝ)+1)*h)).indicator 1 x

private lemma box_cases (h : ℝ) (i : ℕ) (x : ℝ) : box h i x = 0 ∨ box h i x = 1 := by
  classical
  simp only [box, indicator, Pi.one_apply]
  split <;> simp

private lemma box_nonneg (h : ℝ) (i : ℕ) (x : ℝ) : 0 ≤ box h i x := by
  rcases box_cases h i x with he | he <;> simp [he]

private lemma box_int (h : ℝ) (i : ℕ) : Integrable (box h i) := by
  apply (integrable_indicator_iff measurableSet_Ico).mpr
  exact integrableOn_const (by simp)

private lemma integral_box {h : ℝ} (hh : 0 < h) (i : ℕ) : ∫ x, box h i x = h := by
  unfold box
  rw [integral_indicator_one measurableSet_Ico, Real.volume_real_Ico_of_le (by linarith)]
  ring

private lemma box_add (h : ℝ) (i j : ℕ) (x : ℝ) :
    box h (i+j) x = box h j (x-i*h) := by
  classical
  simp only [box, indicator, Set.mem_Ico, Nat.cast_add, Pi.one_apply]
  congr 1
  apply propext
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

private lemma box_section (h : ℝ) (i j : ℕ) (x : ℝ) :
    Integrable (fun y => box h i y * box h j (x-y)) := by
  apply (box_int h i).mul_bdd (c := 1)
  · exact ((box_int h j).comp_sub_left x).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by
      rcases box_cases h j (x-y) with he | he <;> simp [he]

noncomputable def weight (h : ℝ) (z : ℕ) : ℝ → ℝ := box h 0 ⋆ box h z

private lemma weight_int (h : ℝ) (z : ℕ) : Integrable (weight h z) :=
  (box_int h 0).integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (box_int h z)

private lemma weight_mass {h : ℝ} (hh : 0 < h) (z : ℕ) : ∫ x, weight h z x = h^2 := by
  dsimp only [weight]
  rw [integral_convolution _ (box_int h 0) (box_int h z), integral_box hh, integral_box hh]
  change h*h = h^2
  ring

private lemma weight_nonneg (h : ℝ) (z : ℕ) (x : ℝ) : 0 ≤ weight h z x :=
  integral_nonneg fun y => mul_nonneg (box_nonneg h 0 y) (box_nonneg h z (x-y))

private lemma box_conv (h : ℝ) (i j : ℕ) (x : ℝ) :
    (∫ y, box h i y * box h j (x-y)) = weight h (i+j) x := by
  change _ = ∫ y, box h 0 y * box h (i+j) (x-y)
  rw [← integral_add_right_eq_self (fun y => box h i y * box h j (x-y)) ((i:ℝ)*h)]
  apply integral_congr_ae
  filter_upwards [] with y
  have hi := box_add h i 0 (y+i*h)
  rw [Nat.add_zero, add_sub_cancel_right] at hi
  rw [hi, box_add]
  congr 2
  ring

private lemma sum_box_le_one {h : ℝ} (hh : 0 < h) (T : Finset ℕ) (x : ℝ) :
    ∑ z ∈ T, box h z x ≤ 1 := by
  classical
  by_cases hx : ∃ z ∈ T, box h z x ≠ 0
  · obtain ⟨z,hz,hpos⟩ := hx
    have hxmem : x ∈ Set.Ico ((z:ℝ)*h) (((z:ℝ)+1)*h) := Set.mem_of_indicator_ne_zero hpos
    rw [Finset.sum_eq_single z]
    · rcases box_cases h z x with he | he <;> simp [he]
    · intro i _ hne
      apply Set.indicator_of_notMem
      intro hi
      obtain ⟨hzlo,hzhi⟩ := hxmem
      obtain ⟨hilo,hihi⟩ := hi
      rcases lt_or_gt_of_ne hne with hil | hil
      · have ha : (i:ℝ)+1 ≤ z := by exact_mod_cast hil
        nlinarith [mul_le_mul_of_nonneg_right ha hh.le]
      · have ha : (z:ℝ)+1 ≤ i := by exact_mod_cast hil
        nlinarith [mul_le_mul_of_nonneg_right ha hh.le]
    · simp [hz]
  · push Not at hx
    rw [Finset.sum_eq_zero hx]
    norm_num

private lemma sum_weight {h : ℝ} (hh : 0 < h) (T : Finset ℕ) (x : ℝ) :
    ∑ z ∈ T, weight h z x ≤ h := by
  change ∑ z ∈ T, (∫ y, box h 0 y * box h z (x-y)) ≤ h
  rw [← integral_finsetSum _ (fun z _ => box_section h 0 z x)]
  apply le_trans _ (integral_box hh 0).le
  apply integral_mono (integrable_finsetSum _ (fun z _ => box_section h 0 z x)) (box_int h 0)
  intro y
  change (∑ z ∈ T, box h 0 y * box h z (x-y)) ≤ _
  rw [← Finset.mul_sum]
  simpa using mul_le_mul_of_nonneg_left (sum_box_le_one hh T (x-y)) (box_nonneg h 0 y)


noncomputable def mass {ι : Type*} (B : Finset ι) (f : ι → ℕ) (h x : ℝ) : ℝ :=
  ∑ i ∈ B, box h (f i) x

def count {ι : Type*} (B : Finset ι) (f : ι → ℕ) (z : ℕ) : ℕ :=
  ((B ×ˢ B).filter fun p => f p.1 + f p.2 = z).card

private lemma mass_int {ι : Type*} (B : Finset ι) (f : ι → ℕ) (h : ℝ) :
    Integrable (mass B f h) := integrable_finsetSum B (fun i _ => box_int h (f i))

private lemma conv_mass {ι : Type*} (B : Finset ι) (f : ι → ℕ) (L : ℕ)
    (hf : ∀ i ∈ B, f i < L) (h x : ℝ) :
    ((mass B f h) ⋆ (mass B f h)) x =
      ∑ z ∈ range (2*L), (count B f z : ℝ) * weight h z x := by
  classical
  let P := B ×ˢ B
  let s (p : ι × ι) := f p.1 + f p.2
  have hs : ∀ p ∈ P, s p ∈ range (2*L) := by
    intro p hp
    obtain ⟨hp₁,hp₂⟩ := mem_product.mp hp
    exact mem_range.mpr (by dsimp [s]; have := hf _ hp₁; have := hf _ hp₂; omega)
  change (∫ y, mass B f h y * mass B f h (x-y)) = _
  have hm (y : ℝ) : mass B f h y * mass B f h (x-y) =
      ∑ p ∈ P, box h (f p.1) y * box h (f p.2) (x-y) := by
    simp [mass, P, Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  simp_rw [hm]
  rw [integral_finsetSum P (fun p _ => box_section h (f p.1) (f p.2) x)]
  simp_rw [box_conv]
  change (∑ p ∈ P, weight h (s p) x) = _
  rw [← Finset.sum_fiberwise_of_maps_to hs]
  apply Finset.sum_congr rfl
  intro z _
  calc
    _ = ∑ _p ∈ P.filter (fun p => s p = z), weight h z x := by
      apply sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    _ = _ := by simp [count, P, s]

/-- The convolution of two boxes depends only on the sum of their indices.
Weighted Cauchy–Schwarz and the partition of the line by boxes turn the
squared continuum convolution into a discrete additive energy. -/
theorem transfer {ι : Type*} (B : Finset ι) (f : ι → ℕ) {L : ℕ} (hL : 0 < L)
    (hf : ∀ i ∈ B, f i < L) {γ : ℝ}
    (lower : ∀ g : ℝ → ℝ, OMA.Energy241.UnitDensity g →
      Integrable (g ⋆ g) → Integrable (fun x => ((g ⋆ g) x)^2) →
      γ ≤ ∫ x, ((g ⋆ g) x)^2) :
    γ * (B.card:ℝ)^4 ≤ L * ∑ z ∈ range (2*L), (count B f z : ℝ)^2 := by
  classical
  by_cases hB : B.card = 0
  · simp [hB, mul_nonneg, Finset.sum_nonneg, sq_nonneg]
  have hn : (0:ℝ) < B.card := by exact_mod_cast Nat.pos_of_ne_zero hB
  have hl : (0:ℝ) < L := by exact_mod_cast hL
  let h : ℝ := 1/L
  have hh : 0 < h := by dsimp [h]; positivity
  let a : ℝ := (L:ℝ)/B.card
  let g := a • mass B f h
  let T := range (2*L)
  let q (z : ℕ) : ℝ := count B f z
  let major (x : ℝ) := a^4*h*∑ z ∈ T, q z^2 * weight h z x
  have ha : 0 < a := div_pos hl hn
  have Hgi : Integrable g := (mass_int B f h).const_mul a
  have Hg0 : ∀ x, 0 ≤ g x := fun x => mul_nonneg ha.le (sum_nonneg fun i _ => box_nonneg h (f i) x)
  have Hsupp : Function.support g ⊆ Icc (0:ℝ) 1 := by
    intro x hx
    by_contra hout
    apply hx
    change a * (∑ i ∈ B, box h (f i) x) = 0
    apply mul_eq_zero_of_right
    apply sum_eq_zero
    intro i hi
    apply Set.indicator_of_notMem
    rintro ⟨hx₁,hx₂⟩
    apply hout
    have hc : (f i : ℝ)+1 ≤ L := by exact_mod_cast hf i hi
    have hLh : (L:ℝ)*h = 1 := by dsimp [h]; field_simp
    exact ⟨le_trans (by positivity) hx₁, hx₂.le.trans ((mul_le_mul_of_nonneg_right hc hh.le).trans hLh.le)⟩
  have Htotal : ∫ x, g x = 1 := by
    change (∫ x, a * (∑ i ∈ B, box h (f i) x)) = 1
    rw [integral_const_mul, integral_finsetSum B (fun i _ => box_int h (f i))]
    simp_rw [integral_box hh]
    simp [a, h, field]
  have Hcov : ∀ x, (g ⋆ g) x = a^2 * ∑ z ∈ T, q z * weight h z x := by
    intro x
    dsimp only [g]
    rw [smul_convolution, convolution_smul]
    change a * (a * (((mass B f h) ⋆ (mass B f h)) x)) = _
    rw [conv_mass B f L hf]
    dsimp [q,T]
    ring
  have Hbound (x : ℝ) : ((g ⋆ g) x)^2 ≤ major x := by
    have Hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul T
      (r := fun z => q z * weight h z x) (f := fun z => weight h z x)
      (g := fun z => q z^2 * weight h z x)
      (fun z _ => weight_nonneg h z x) (fun z _ => mul_nonneg (sq_nonneg _) (weight_nonneg h z x))
      (fun z _ => by ring_nf; rfl)
    have Hm := mul_le_mul_of_nonneg_right (sum_weight hh T x)
      (sum_nonneg (fun z (_ : z ∈ T) => mul_nonneg (sq_nonneg (q z)) (weight_nonneg h z x)))
    rw [Hcov, mul_pow]
    dsimp [major]
    calc
      _ ≤ (a^2)^2 * (h * ∑ z ∈ T, q z^2 * weight h z x) :=
        mul_le_mul_of_nonneg_left (Hc.trans Hm) (sq_nonneg _)
      _ = _ := by ring
  have Hmi : Integrable major := (integrable_finsetSum T (fun z _ =>
    (weight_int h z).const_mul (q z ^ 2))).const_mul (a^4*h)
  have Hci := Hgi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) Hgi
  have Hci2 : Integrable (fun x => ((g ⋆ g) x)^2) :=
    Hmi.mono_nonneg (Hci.aestronglyMeasurable.pow 2) (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall Hbound)
  have hres := (lower g ⟨Hgi,Hg0,Hsupp,Htotal⟩ Hci Hci2).trans (integral_mono Hci2 Hmi Hbound)
  have havg : (∫ x, major x) = a^4*h^3 * ∑ z ∈ T, q z^2 := by
    unfold major
    rw [integral_const_mul, integral_finsetSum T (fun z _ => (weight_int h z).const_mul (q z^2))]
    simp_rw [integral_const_mul, weight_mass hh]
    rw [← sum_mul]
    ring
  rw [havg] at hres
  have norm : a^4*h^3 = (L:ℝ)/(B.card:ℝ)^4 := by
    dsimp [a,h]
    field_simp
  rw [norm, div_mul_eq_mul_div] at hres
  exact (le_div_iff₀ (pow_pos hn 4)).mp hres

end OMA.Energy241


/- Local multiplicity and smoothed additive energy of a B₃ set. -/
namespace OMA.B3Energy241
open Finset
open scoped Classical

def B3 (A : Finset ℕ) := ∀ m₁ m₂ : Multiset ℕ, m₁.card = 3 → m₂.card = 3 →
  (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) → m₁.sum = m₂.sum → m₁=m₂

private def triple (a b c : ℕ) : Multiset ℕ := a ::ₘ b ::ₘ c ::ₘ 0

private lemma three_eq {A : Finset ℕ} (h : B3 A) {a b c d e f : ℕ}
    (ha : a∈A) (hb : b∈A) (hc : c∈A) (hd : d∈A) (he : e∈A) (hf : f∈A)
    (hs : a+b+c=d+e+f) : triple a b c = triple d e f := by
  apply h <;> simp_all [triple]
  omega

private lemma pair_eq {a b d e : ℕ}
    (h : a ::ₘ b ::ₘ (0 : Multiset ℕ) = d ::ₘ e ::ₘ 0) :
    (a=d ∧ b=e) ∨ (a=e ∧ b=d) := by
  have ha : a ∈ d ::ₘ e ::ₘ (0 : Multiset ℕ) := h ▸ Multiset.mem_cons_self _ _
  simp only [Multiset.mem_cons,Multiset.notMem_zero,or_false] at ha
  rcases ha with rfl | rfl
  · exact Or.inl ⟨rfl,(Multiset.cons_inj_left _).mp ((Multiset.cons_inj_right _).mp h)⟩
  · rw [Multiset.cons_swap d a] at h
    exact Or.inr ⟨rfl,(Multiset.cons_inj_left _).mp ((Multiset.cons_inj_right _).mp h)⟩

private abbrev Trip := ℕ × ℕ × ℕ
private def value (q : Trip) : ℤ := q.1+q.2.1-(q.2.2:ℤ)
private def trips (A : Finset ℕ) := A ×ˢ (A ×ˢ A)
private def fiber (A : Finset ℕ) (z : ℤ) := (trips A).filter (fun q => value q =z)
private lemma mem_fiber (A : Finset ℕ) (z : ℤ) (a b c : ℕ) :
    (a,b,c) ∈ fiber A z ↔ a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ (a:ℤ)+b-c=z := by
  rw [fiber,mem_filter,trips,mem_product,mem_product]
  simp [value,and_assoc]

private lemma fiber_le_two {A : Finset ℕ} (h : B3 A) {z : ℤ}
    (hz : z ∉ A.image (fun n : ℕ => (n:ℤ))) : (fiber A z).card ≤ 2 := by
  obtain h₀ | ⟨⟨d,e,f⟩,hw⟩ := (fiber A z).eq_empty_or_nonempty
  · simp [h₀]
  obtain ⟨hd,he,hf,hs⟩ := (mem_fiber ..).mp hw
  apply le_trans (card_le_card (t:={(d,e,f),(e,d,f)}) ?_) card_le_two
  rintro ⟨a,b,c⟩ habc
  obtain ⟨ha,hb,hc,hs'⟩ := (mem_fiber ..).mp habc
  have hm := three_eq h hf ha hb hc hd he (by omega)
  have hmem : c ∈ triple f a b := hm.symm ▸ Multiset.mem_cons_self _ _
  simp only [triple,Multiset.mem_cons,Multiset.notMem_zero,or_false] at hmem
  have hcf : c=f := by
    rcases hmem with hcf | hca | hcb
    · exact hcf
    · exact (hz (mem_image.mpr ⟨b,hb,by omega⟩)).elim
    · exact (hz (mem_image.mpr ⟨a,ha,by omega⟩)).elim
  subst c
  rcases pair_eq ((Multiset.cons_inj_right _).mp hm) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

private lemma fiber_at_member {A : Finset ℕ} (h : B3 A) {x : ℕ} (hx : x ∈ A) :
    (fiber A (x:ℤ)).card ≤ 2*A.card := by
  let opts (c : ℕ) : Finset Trip := {(x,c,c),(c,x,c)}
  calc (fiber A (x:ℤ)).card ≤ (A.biUnion opts).card := by
         apply card_le_card
         rintro ⟨a,b,c⟩ hq
         obtain ⟨ha,hb,hc,hs⟩ := (mem_fiber ..).mp hq
         have hm := three_eq h hx ha hb hx hx hc (by omega)
         obtain ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ := pair_eq ((Multiset.cons_inj_right _).mp hm)
         all_goals exact mem_biUnion.mpr ⟨_,hc,by simp [opts]⟩
       _ ≤ ∑ c ∈ A, (opts c).card := card_biUnion_le
       _ ≤ ∑ _c ∈ A, 2 := sum_le_sum fun _ _ => card_le_two
       _ = _ := by simp [Nat.mul_comm]

private lemma fiber_window (A : Finset ℕ) (h : B3 A) (z : ℤ) (u : ℕ) :
    ∑ i ∈ range u, (fiber A (z+(i:ℤ))).card ≤ 2*u+2*A.card^2 := by
  let B := A.image (fun n : ℕ => (n:ℤ))
  let E := (range u).filter (fun i : ℕ => z+(i:ℤ) ∈ B)
  have hfew : E.card ≤ A.card := by
    refine le_trans (card_le_card_of_injOn (fun i : ℕ => z+(i:ℤ)) (t:=B) ?_ ?_) card_image_le
    · intro i hi
      exact (mem_filter.mp hi).2
    · intro i _ j _ he
      change z+(i:ℤ)=z+(j:ℤ) at he
      omega
  calc ∑ i ∈ range u, (fiber A (z+(i:ℤ))).card ≤
      ∑ i ∈ range u, (2 + if z+(i:ℤ) ∈ B then 2*A.card else 0) := by
        apply sum_le_sum
        intro i _
        split_ifs with hi
        · obtain ⟨x,hx,he⟩ := mem_image.mp hi
          rw [←he]
          exact (fiber_at_member h hx).trans (by omega)
        · simpa using fiber_le_two h hi
    _ = 2*u+ E.card*(2*A.card) := by simp [sum_add_distrib,←sum_filter,E,Nat.mul_comm]
    _ ≤ _ := by nlinarith [Nat.mul_le_mul_right (2*A.card) hfew]

theorem coarse (A : Finset ℕ) (h : B3 A) (N : ℕ) (hN : A ⊆ Icc 1 N) :
    A.card^3 ≤ 6*N+2*A.card^2+2 := by
  let index (q : Trip) := (value q + N).toNat
  have hlo (q : Trip) (hq : q ∈ trips A) : -(N:ℤ) ≤ value q ∧ value q ≤ 2*N := by
    obtain ⟨a,b,c⟩ := q
    obtain ⟨ha,hb,hc⟩ : a∈A ∧ b∈A ∧ c∈A := by simpa [trips] using hq
    have := (mem_Icc.mp (hN ha)).2
    have := (mem_Icc.mp (hN hb)).2
    have := (mem_Icc.mp (hN hc)).2
    dsimp [value]
    omega
  have hkeys := card_eq_sum_card_fiberwise (s:=trips A) (t:=range (3*N+1)) (f:=index)
    (by intro q hq; have := hlo q hq; simp [index]; omega)
  have hsum := fiber_window A h (-(N:ℤ)) (3*N+1)
  have hc : (trips A).card ≤ ∑ i ∈ range (3*N+1), (fiber A (-(N:ℤ)+i)).card := by
    rw [hkeys]
    apply sum_le_sum
    intro i _
    apply card_le_card
    intro q hq
    obtain ⟨hq,hi⟩ := mem_filter.mp hq
    have := hlo q hq
    dsimp [index] at hi
    exact mem_filter.mpr ⟨hq,by omega⟩
  have hc' : (trips A).card = A.card^3 := by simp [trips]; ring
  rw [hc'] at hc
  omega

private abbrev Block := ℕ × ℕ
private abbrev Quad := (Block × Block) × (Block × Block)
private abbrev Key := ℕ × ℕ × ℕ × ℕ
private def blockVal (b : Block) := b.1+b.2
private def pairVal (b : Block × Block) := blockVal b.1+blockVal b.2
private def key (q : Quad) : Key := (q.2.2.1,q.1.1.2,q.1.2.2,q.2.1.2)
private def last (q : Quad) := q.2.2.2
private def abc (q : Quad) : Trip := (q.1.1.1,q.1.2.1,q.2.1.1)
private def blocks (A : Finset ℕ) (u : ℕ) := A ×ˢ range u
private def quads (B : Finset Block) :=
  ((B ×ˢ B) ×ˢ (B ×ˢ B)).filter (fun q => pairVal q.1 = pairVal q.2)

private lemma quad_spec {A : Finset ℕ} {u : ℕ} {q : Quad} (hq : q ∈ quads (blocks A u)) :
    q.1.1.1 ∈ A ∧ q.1.2.1 ∈ A ∧ q.2.1.1 ∈ A ∧ q.2.2.1 ∈ A ∧
    q.1.1.2 < u ∧ q.1.2.2 < u ∧ q.2.1.2 < u ∧ q.2.2.2 < u ∧
    q.1.1.1+q.1.1.2+(q.1.2.1+q.1.2.2)=q.2.1.1+q.2.1.2+(q.2.2.1+q.2.2.2) := by
  rw [quads,mem_filter] at hq
  obtain ⟨hmem,he⟩ := hq
  simp only [blocks,mem_product,mem_range] at hmem
  dsimp [pairVal,blockVal] at he
  tauto

private lemma quads_le (A : Finset ℕ) (h : B3 A) (u : ℕ) :
    (quads (blocks A u)).card ≤ 2*A.card*u^3*(u+A.card^2) := by
  let Q := quads (blocks A u)
  let Ks := A ×ˢ (range u ×ˢ (range u ×ˢ range u))
  have hkey : (Q : Set Quad).MapsTo key Ks := by
    intro q hq
    obtain ⟨_,_,_,hd,hi,hj,hk,_,_⟩ := quad_spec hq
    simpa [Ks,key] using And.intro hd ⟨hi,hj,hk⟩
  have hbd (v : Key) : (Q.filter (fun q => key q = v)).card ≤ 2*u+2*A.card^2 := by
    obtain ⟨d,i,j,k⟩ := v
    let D := Q.filter (fun q => key q=(d,i,j,k))
    let offset : ℤ := (d:ℤ)+k-i-j
    have hl : (D : Set Quad).MapsTo last (range u) := fun q hq =>
      mem_range.mpr (quad_spec (mem_filter.mp hq).1).2.2.2.2.2.2.2.1
    refine (card_eq_sum_card_fiberwise hl).trans_le ?_
    apply le_trans _ (fiber_window A h offset u)
    apply sum_le_sum
    intro l _
    apply card_le_card_of_injOn abc
    · intro q hq
      obtain ⟨hq,hl⟩ := mem_filter.mp hq
      obtain ⟨hq,hv⟩ := mem_filter.mp hq
      obtain ⟨ha,hb,hc,_,_,_,_,_,hs⟩ := quad_spec hq
      apply (mem_fiber ..).mpr
      refine ⟨ha,hb,hc,?_⟩
      simp only [key,Prod.mk.injEq] at hv
      dsimp [last] at hl
      dsimp [abc,offset]
      omega
    · rintro ⟨⟨⟨a,i₁⟩,⟨b,j₁⟩⟩,⟨⟨c,k₁⟩,⟨d₁,l₁⟩⟩⟩ hx ⟨⟨⟨a',i₂⟩,⟨b',j₂⟩⟩,⟨⟨c',k₂⟩,⟨d₂,l₂⟩⟩⟩ hy he
      obtain ⟨_,hxk,hxl⟩ : _ ∧ key _=(d,i,j,k) ∧ last _=l :=
        ⟨(mem_filter.mp (mem_filter.mp hx).1).1,(mem_filter.mp (mem_filter.mp hx).1).2,(mem_filter.mp hx).2⟩
      obtain ⟨_,hyk,hyl⟩ : _ ∧ key _=(d,i,j,k) ∧ last _=l :=
        ⟨(mem_filter.mp (mem_filter.mp hy).1).1,(mem_filter.mp (mem_filter.mp hy).1).2,(mem_filter.mp hy).2⟩
      simp only [abc,key,last,Prod.mk.injEq] at *
      exact ⟨⟨⟨he.1,hxk.2.1.trans hyk.2.1.symm⟩,⟨he.2.1,hxk.2.2.1.trans hyk.2.2.1.symm⟩⟩,
        ⟨⟨he.2.2,hxk.2.2.2.trans hyk.2.2.2.symm⟩,⟨hxk.1.trans hyk.1.symm,hxl.trans hyl.symm⟩⟩⟩
  calc Q.card = ∑ v ∈ Ks, (Q.filter (fun q => key q=v)).card := card_eq_sum_card_fiberwise hkey
       _ ≤ ∑ _v ∈ Ks, (2*u+2*A.card^2) := sum_le_sum fun v _ => hbd v
       _ = _ := by simp [Ks]; ring

private lemma discrete_energy (A : Finset ℕ) (N u : ℕ) (hN : A ⊆ Icc 1 N) :
    let B := blocks A u
    (∑ z ∈ range (2*(N+u)), ((B×ˢB).filter (fun v => pairVal v=z)).card^2) =
      (quads B).card := by
  let B := blocks A u
  have maps : (quads B : Set Quad).MapsTo (fun q => pairVal q.1) (range (2*(N+u))) := by
    intro q hq
    obtain ⟨ha,hb,_,_,hi,hj,_,_,_⟩ := quad_spec hq
    have := (mem_Icc.mp (hN ha)).2
    have := (mem_Icc.mp (hN hb)).2
    apply mem_range.mpr
    dsimp [pairVal,blockVal]
    omega
  change (∑ z ∈ range (2*(N+u)), ((B×ˢB).filter (fun v => pairVal v=z)).card^2) = (quads B).card
  rw [card_eq_sum_card_fiberwise maps]
  apply sum_congr rfl
  intro z _
  let T := (B×ˢB).filter (fun q => pairVal q=z)
  have he : (quads B).filter (fun q => pairVal q.1=z)=T×ˢT := by
    ext q
    constructor
    · intro hq
      obtain ⟨hq,hz⟩ := mem_filter.mp hq
      obtain ⟨hq,he⟩ := mem_filter.mp hq
      obtain ⟨h₁,h₂⟩ := mem_product.mp hq
      exact mem_product.mpr ⟨mem_filter.mpr ⟨h₁,hz⟩,mem_filter.mpr ⟨h₂,he.symm.trans hz⟩⟩
    · intro hq
      obtain ⟨h₁,h₂⟩ := mem_product.mp hq
      obtain ⟨hx,hx'⟩ := mem_filter.mp h₁
      obtain ⟨hy,hy'⟩ := mem_filter.mp h₂
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hx,hy⟩,hx'.trans hy'.symm⟩,hx'⟩
  rw [he,card_product,pow_two]

theorem finite_count {γ : ℝ}
    (energy : ∀ (B : Finset (ℕ × ℕ)) (f : (ℕ × ℕ) → ℕ) {L : ℕ}, 0 < L →
      (∀ i ∈ B, f i < L) → γ * (B.card:ℝ)^4 ≤ (L:ℝ) *
        ∑ z ∈ range (2*L), (((B×ˢB).filter (fun q => f q.1 + f q.2 = z)).card:ℝ)^2)
    (N : ℕ) (hN : 1 ≤ N) :
    let k := Erdos241.f N 3
    k^3 ≤ 6*N+2*k^2+2 ∧ ∀ u : ℕ, 1 ≤ u →
      γ*(k:ℝ)^3*u ≤ 2*((N:ℝ)+u)*((u:ℝ)+(k:ℝ)^2) := by
  let Cs := (Icc 1 N).powerset.filter B3
  have hCs : Cs.Nonempty := by
    refine ⟨∅,mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),?_⟩⟩
    intro m₁ m₂ _ _ h₁ h₂ _
    simp only [notMem_empty] at h₁ h₂
    exact (Multiset.eq_zero_of_forall_notMem h₁).trans (Multiset.eq_zero_of_forall_notMem h₂).symm
  obtain ⟨A,hAC,hmax⟩ := sup_mem_of_nonempty (f:=Finset.card) hCs
  have hk : A.card = Erdos241.f N 3 := hmax
  obtain ⟨hp,hA⟩ := mem_filter.mp hAC
  have hs := mem_powerset.mp hp
  dsimp only
  rw [←hk]
  refine ⟨coarse A hA N hs,?_⟩
  intro u hu
  let B := blocks A u
  have hE := energy B blockVal (L:=N+u) (by omega) (by
    rintro ⟨a,i⟩ h
    have hi := mem_range.mp (mem_product.mp h).2
    have ha := (mem_Icc.mp (hs (mem_product.mp h).1)).2
    dsimp [blockVal]
    omega)
  have hquad := (discrete_energy A N u hs).trans_le (quads_le A hA u)
  change (∑ z ∈ range (2*(N+u)), ((B×ˢB).filter (fun q => blockVal q.1+blockVal q.2=z)).card^2)
    ≤ 2*A.card*u^3*(u+A.card^2) at hquad
  have hqr : (∑ z ∈ range (2*(N+u)), (((B×ˢB).filter
      (fun q => blockVal q.1+blockVal q.2=z)).card : ℝ)^2) ≤
      2*(A.card:ℝ)*(u:ℝ)^3*((u:ℝ)+(A.card:ℝ)^2) := by exact_mod_cast hquad
  have hb : B.card=A.card*u := by simp [B,blocks]
  rw [hb,Nat.cast_mul,Nat.cast_add] at hE
  have he := hE.trans (mul_le_mul_of_nonneg_left hqr (by positivity))
  by_cases hzero : A.card=0
  · simp [hzero]; positivity
  · have hp : 0 < (A.card:ℝ)*(u:ℝ)^3 := by
      have : 0 < (A.card:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hzero
      have : 0 < (u:ℝ) := by exact_mod_cast hu
      positivity
    apply le_of_mul_le_mul_right (a := (A.card:ℝ)*(u:ℝ)^3) _ hp
    nlinarith only [he]

end OMA.B3Energy241


/- Optimizing the smoothing length in Green's upper bound for distinct triple sums. -/

open Filter Asymptotics
open scoped Topology

namespace OMA.Green241

/-- The sixth root is the natural scale: the smoothing length is its fifth power,
    rounded up. In particular the error term after normalization is O(N^(-1/6)). -/
theorem asymptotic_upper {γ : ℝ} (hγ : 0 < γ)
    (hcount : ∀ N : ℕ, 1 ≤ N →
      let k := Erdos241.f N 3
      k ^ 3 ≤ 6 * N + 2 * k ^ 2 + 2 ∧
        ∀ u : ℕ, 1 ≤ u → γ * (k : ℝ)^3 * u ≤
          2 * ((N : ℝ) + u) * ((u : ℝ) + (k : ℝ)^2)) :
    ∃ ε : ℕ → ℝ, ε =o[atTop] (fun _ ↦ (1 : ℝ)) ∧ ∀ᶠ N : ℕ in atTop,
      (Erdos241.f N 3 : ℝ) ≤ ((2/γ)^((1:ℝ)/3) + ε N) * (N : ℝ)^((1:ℝ)/3) := by
  let c := (2/γ)^((1:ℝ)/3)
  let root (N : ℕ) := (N:ℝ)^((1:ℝ)/6)
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  have hc3 : c^3 = 2/γ := by
    dsimp [c]
    simpa [one_div] using Real.rpow_inv_natCast_pow (x := 2/γ) (by positivity) (by decide : 3 ≠ 0)
  refine ⟨fun N => (16*c) / root N, ?_, ?_⟩
  · apply (isLittleO_one_iff ℝ).mpr
    have hr : Tendsto root atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : 0 < (1:ℝ)/6)).comp tendsto_natCast_atTop_atTop
    exact tendsto_const_nhds.div_atTop hr
  filter_upwards [eventually_ge_atTop 1] with N hN
  let b := root N
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hb : 1 ≤ b := Real.one_le_rpow hN1 (by norm_num)
  have hb0 : 0 < b := by linarith
  have hb6 : b^6 = N := by
    dsimp [b,root]
    simpa [one_div] using Real.rpow_inv_natCast_pow (x := (N:ℝ)) (by positivity) (by decide : 6 ≠ 0)
  have hb2 : (N:ℝ)^((1:ℝ)/3) = b^2 := by
    dsimp [b,root]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  let k : ℝ := Erdos241.f N 3
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  obtain ⟨hcrude,henergy⟩ := hcount N hN
  have h0 : k^3 ≤ 6*(N:ℝ) + 2*k^2 + 2 := by
    dsimp [k]
    exact_mod_cast hcrude
  have hk : k ≤ 4*b^2 := by
    by_cases h4 : k ≤ 4
    · nlinarith [sq_nonneg (b-1)]
    have hk3 : k^3 ≤ 64*(N:ℝ) := by
      nlinarith [mul_nonneg (show 0 ≤ k-4 by linarith) (sq_nonneg k)]
    apply le_of_not_gt
    intro h
    have := pow_lt_pow_left₀ h (by positivity : 0 ≤ 4*b^2) (by decide : 3 ≠ 0)
    nlinarith only [this,hk3,hb6]
  let u := ⌈b^5⌉₊
  have hur : b^5 ≤ (u:ℝ) := Nat.le_ceil _
  have h5 : 1 ≤ b^5 := one_le_pow₀ hb
  have hu1 : 1 ≤ u := by exact_mod_cast (h5.trans hur)
  have hub : (u:ℝ) ≤ 2*b^5 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ b^5 by positivity)
    change (⌈b^5⌉₊ : ℝ) ≤ _
    linarith
  have hk2 : b*k^2 ≤ 16*(u:ℝ) := by
    have hsq := pow_le_pow_left₀ hk0 hk 2
    nlinarith only [mul_le_mul_of_nonneg_left hsq hb0.le, hur]
  have he : γ*k^3*(u:ℝ) ≤ 2*((N:ℝ)+(u:ℝ))*((u:ℝ)+k^2) := henergy u hu1
  have hu0 : 0 < (u:ℝ) := by exact_mod_cast (show 0 < u by omega)
  have he' : γ*k^3*b ≤ 2*(b^6+2*b^5)*(b+16) := by
    apply le_of_mul_le_mul_right (a := (u:ℝ)) _ hu0
    calc
      γ*k^3*b*u = (γ*k^3*u)*b := by ring
      _ ≤ (2*((N:ℝ)+u)*(u+k^2))*b := by gcongr
      _ = 2*((N:ℝ)+u)*(b*u+b*k^2) := by ring
      _ ≤ 2*(b^6+2*b^5)*(b*u+16*u) := by rw [hb6]; gcongr
      _ = (2*(b^6+2*b^5)*(b+16))*u := by ring
  have hpoly : γ*k^3 ≤ 2*(b*(b+16))^3 := by
    apply le_of_mul_le_mul_right (a := b) _ hb0
    calc
      γ*k^3*b ≤ _ := he'
      _ = (2*b^4*(b+16))*(b*(b+2)) := by ring
      _ ≤ (2*b^4*(b+16))*(b+16)^2 := by gcongr; nlinarith
      _ = (2*(b*(b+16))^3)*b := by ring
  have hcube : k^3 ≤ (c*(b*(b+16)))^3 := by
    rw [mul_pow,hc3,div_mul_eq_mul_div]
    apply (le_div_iff₀ hγ).mpr
    linarith only [hpoly]
  have hfinal : k ≤ c*(b*(b+16)) := by
    by_contra! h
    exact (not_lt_of_ge hcube) (pow_lt_pow_left₀ h (by positivity) (by decide))
  change k ≤ (c + 16*c/b) * _
  rw [hb2]
  convert hfinal using 1
  field_simp

end OMA.Green241

/- From the finite cosine certificate to the asymptotic bound. -/
namespace OMA.WhiteBridge241

open MeasureTheory OMA.White241
open scoped Convolution Real
noncomputable section

private instance : Fact (0 < (2:ℝ)) := ⟨by norm_num⟩

def modeAmp (n : ℕ) : ℝ :=
  (M:ℝ) * |(J.map (fun z => (z.2:ℝ) * Real.cos (Real.pi*(n:ℝ)*z.1/M))).sum| /
    ((H:ℝ) * Real.pi^2)

def finiteBound : Prop :=
  (∑ r : Fin (2*M),
    ((modeAmp (r.val+1) / ((r.val+1:ℕ):ℝ)^2)^(4/3:ℝ) +
    (modeAmp (r.val+1) / ((r.val+1+2*M:ℕ):ℝ)^2)^(4/3:ℝ) +
    (7/20) * (modeAmp (r.val+1) / ((2*M:ℕ):ℝ)^2)^(4/3:ℝ))) ≤
      278195042329380884410 / (295147905179352825856:ℝ)

private theorem amp_period (n k : ℕ) : modeAmp (n+k*(2*M)) = modeAmp n := by
  have he : (J.map (fun z => (z.2:ℝ) * Real.cos (Real.pi*((n+k*(2*M):ℕ):ℝ)*z.1/M))) =
      J.map (fun z => (z.2:ℝ) * Real.cos (Real.pi*(n:ℝ)*z.1/M)) := by
    apply List.map_congr_left
    intro z _
    rw [OMA.WhiteFold241.cos_add_period (by decide) n k z.1]
  simp only [modeAmp, he]

theorem energy (cert : finiteBound) {g : ℝ → ℝ} (hg : OMA.Energy241.UnitDensity g)
    (hi : Integrable (g ⋆ g)) (hs : Integrable (fun x => ((g ⋆ g) x)^2)) :
    (0.574636066:ℝ) ≤ ∫ x, ((g ⋆ g) x)^2 := by
  obtain ⟨U,hU,hzero,hcoef⟩ := OMA.White241.spline
  let B (n : ℕ) := modeAmp n / (n:ℝ)^2
  have hA (n) : 0 ≤ modeAmp n := by unfold modeAmp; positivity
  have hB (n) : 0 ≤ B n := div_nonneg (hA n) (sq_nonneg _)
  have hcoeff (n : ℤ) (hn : n ≠ 0) : ‖fourierCoeff U n‖ = B n.natAbs := by
    rw [hcoef n hn]
    simp only [B,modeAmp,div_div,mul_assoc]
  obtain ⟨hsum,hrp,hmass⟩ := OMA.WhiteTail241.period_total (Q:=2*M) (by decide)
    B (fun r => modeAmp (r.val+1)) hB (fun r => hA _) (by
      intro r k
      dsimp only [B]
      rw [amp_period])
  have hd : 2 * (∑' n : ℕ, B (n+1) ^ (4/3:ℝ)) ≤
      556390084658761768820 / (295147905179352825856:ℝ) := by
    have h := hmass.trans cert
    linarith only [h]
  exact le_trans (by norm_num : (0.574636066:ℝ) ≤
    1/2 + 1/(2*(556390084658761768820/(295147905179352825856:ℝ))^3))
    (OMA.WhiteDual241.normalized U B hU hzero hcoeff hB hsum hrp (by norm_num) hd hg hi hs)

theorem upper (cert : finiteBound) : type_of% @Erdos241.erdos_241.variants.upper_bound_white := by
  exact OMA.Green241.asymptotic_upper (γ:=0.574636066) (by norm_num)
    (OMA.B3Energy241.finite_count (fun B f {_} hL hf =>
      OMA.Energy241.transfer B f hL hf (fun _ hg hi hs => energy cert hg hi hs)))

end
end OMA.WhiteBridge241


namespace OMA.White241
def P : ℕ := 2^90
def negBounds (v : ℤ × ℤ) : ℤ × ℤ := (-v.2, -v.1)
def Encloses (v : ℤ × ℤ) (x : ℝ) : Prop := (v.1:ℝ) ≤ x ∧ x ≤ (v.2:ℝ)
end OMA.White241


/- The quarter-period table uses an angle-addition predictor at the two
  base-128 digits of each index. The residual and interval width are stored
  exactly. The half-angle check certifies the decoded intervals directly. -/

namespace OMA.White241

private def coarse0_2 (k : ℕ) : ℕ := if k < 1 then 0x7dd6668e8481dd84f31d7422edbb3bca17e628eaf77621f8764fa714ba93564acef18af10a22459fe32a63feef17e5fe49324266a1d51f115a28aaed62527cb3b5e976fb5fa7557f08a516a17d5cd7b0964083747309d113000a877ed5e5c6575d048dfd639ca2273e19db5eaed56e5e596dfc26470e19fd347b219a3b07d59395aa5cc38d13823947f3857f5b699eb511483e781c3785c79ec2d4f5863106dfd88da3d125259e082721d8645e9af0a6d0af87639cb57f872bf2f56c24688f8c80a15f6d00a9aa418c17fba5edfe9cdad01883a1521ecd0c04b54824b3867d732fbbab77fc2559639c6b501a8ce18a0fb2b73cfc106ff68f0a0d9ff621e3796d7de3a843d1d8323ecbe21bb027cdda85e07fe9cbbffbdd7274b32324c096c32baca2ae68b437b2d9ffd886084cd0cbb2acaeaa0192155f7a3667df938a7377ffd885a6e4b6d5dda3c81e03243a3f9bd8f08cc3c75ce000000000000000000000000000000000000000000000 else 0x76d94988e2826b2908c0a8a5f0ea4c477339c0668fc875ddb13b6ccc23c60f0df18397088530fa459eaed3987dd77fab988b6f8aaaeb1577bc5931f774fc9f184434ad295e212104f686e4bface24fb158f9a75ab1fdcfe1023f297909a92caf05f9a8738897453478909e39da8920b90c39e6288ec48e111ee94a90d794135c941766014325f12be7a05eead33443317a80cbca4d50430b860546c34ffd065e9f4156c62dda5d82c78b89294062ed59f05a8b5c974d7aef63237c2dd0e364630ae474d10fd336cf746f95f1f1ed740e76849633d058f23e9111d262b1f6776093082ac7bc5e28f91cf096310a67fe413ee038dff6b7fd7da6491f0a7efb9230d72a58f5b8d0f8cfcbd90af8d57a4221dc7c894bddd8eb66df347e3723b269fca8a8622badc913b5f38f3ac64e588c508a095b8e05c1353f27b17e50ebc607d3980ec2cbcb3388ff0cb43505404b6008a13c37d0011f6297cff75cb02ac42e5468c7c5c1e34d3055b25cc8bf
private def coarse2_2 (k : ℕ) : ℕ := if k < 3 then 0x6b4af278875442b8041f8408b9a6b1ef6da450221a6671b090a581501ff9b64973fba23d66a8369645086e24b296cf934fbd55c461494740ec864b826aec4c74e58504321b728345196e3d90e58336c20e70f3245ffdb2d2ff5e5b6e96a99cd643497ea4e370680e7e43a61f5b6cb5ca183dbd7c0ac6f95299f69633549f8ba4dbf89ab9fb44f80f870231099c95524362affb007b70654bbde35622f083cbdc38b2f180bdb0d23e9d1501e2b5d3806f63b1e0d891d3719e2cd221ce6c761b2b1f075e5dd6e1b8e25550ec87b9c954b213411f4f68244f0b1cc66e9931c45e16850e59b7307c3cff3f170f2bb09db270492760047b9a7ec5544adced7af43cc772f0c24a2521b5d1009e15cc02b66c5972745f9dd0f8d76fddfc4b9566a9b20adb4ff262a0ef9115d4134d14dc939ac42b5a8b19ef7943a8ed8a2db50252075a585cf279a2b0b9cf1ce264dca98ef24f5cb4218cf25d906bcf328d4628afcc204187de2a6aea962d1a624585 else 0x5b9d1153aaa2ba243fc37acb2c8c92f83c1eb87ac9f7e572d0837efff964353bc3c62c216eaa3a59bdb6b932b3e5dc79d7c0dc984ae7e746beae3bddf3280c620d3d538157b5df226aafaede1590a63aafad26919d93f4546fb3695fe3b38d5c5dc263727316aa99414951aacae5ed14762183b0e0bff976dd217be0e229cd9577c7cbd2278527db861f1003ee8bafad2543f3bea4d224dcd849c5b023d25198bc806b151740b4e87b44ba899e64a123bac300ed459e63ef328fbe5033a481598dc9ff6ca9a2ab6a26d22cc11593a22499263fb4f5066a48275ff45240a17278f8978e465ddfbd31f5d06eab865dbe9b02c58832cf95c0698b94d9b3e047f38740b3c475e63261feff9c2e069c20673b2067bd0fbca6be50d8efe5b0095f6d92fd79f4fbad9f8e15a29a7a0462781ddae89fd424da0a99ba25bd512c5e086698c246c0beb870b77756ec90d3ccc99f5ac58b09d1071a9b66290ea1a3033ec61d1238e76735cd190d92ee933f
private def coarse0_4 (k : ℕ) : ℕ := if k < 2 then coarse0_2 k else coarse2_2 k
private def coarse4_2 (k : ℕ) : ℕ := if k < 5 then 0x4869e664cfad62c584e8838d31848d817d70e16eeeadd926d054cdd12dea8962f04334534f408c4f03bb5d13fa84afb6c97ebcfa7dd6cfc70acf7a1f794d7ca1b1dfcb60130ff7fce17034e10339d903367c08fe70e816788ebcc64d8162c41967cae034c5ca6cbbbf7a63eba0dd570cbb7d3affa292050b93c7c4bc723274449324c7f69ea0cd4904ffb654d155b5136916608ac7de651f7ca0674902b31b944cf325091dd618076a2cf317900d62a2e8169d0f68975269126e6c24e2d811e928cc3e2007dd175f5a4a87e77d4e6cabbe3e5e913c293edc30761c17ff2edba42f7c1c454ca0a4a8d56572f68a3b10bfc7671ab8bb84c6e4e62d557d69348cec9fa2a37d9b4af6bbe44d55f5dbc2b214c7571deef9940631069ea9c0abb8f3af81b93095cfce8d7d610b7551d2cdedb5c9959f2e5a106fdfff2c86a77878c59646497c1e0f5c3d64fbf2b73a22a7554574487f86f596a09e667f3bcc908b2fb132d413cccfe779921165f626 else 0x326e54c77927ae5a10c6792eb4b0b9e4f34561739e39c4cf7bca1d476c516da812903a8269a29b927358856b516354d9056da7f9315077c88ae8bf3ba1f1aedfbbf8972acdae8804f0ae6015b362cb939daf5e8798ee5e184944a4382493b0023dcd3f62aa256e60f879fe7e2e1e57613b64e63374c98e22f0b42872cdb92a96426823e9ed0489e163af2eeb70dc712aa87643dce33c59a4439cd8ec36563e0f15ae9c037b1d8f06c48e9b87165e3017b61a47d3a2a03db832a5def1ab117841e5ee046213392aa486c55ff600fc5d26dfc4d5cfda27c07c37af8158df2a533ed2c66a94073f21d30fadb65ae50c1edd2d5339ac8692fd49c6e0d073879922ffed9697faf2db6e5068a32dc7b21cb066d84325c13576263a72c282190d9f269f7aab88c2928e81d911eb3541b4b22843712594b61214b02a03ff36c92e7f745cd358f7b6d228110d3338d695e4f10ea88570083f0811c73b39ae68c86c977499fb536cc521d4346067d8c3a2
private def coarse7_2 (k : ℕ) : ℕ := if k < 8 then 0x1921d1fcdec784661e3ae6fffb10b4dc96dabbb47903c0c90aafbd1b33efc9c539bbffb10c1099a19765595d5404b6195d65157345a1bd96cffd3977ff7bae4e96646498191f65f10dd813e6ed42f03fec43c6f2dafbc75087a3b07d95b9e7e0837fb478506cff84ab2c738d6a03519c31425aa41259c33eb997ddd5bbfd39b5a0310742a43d9a180afb68054d520c60bfdd2f6ff0e57e5ead848d11f19014322f4d78536857c3b1ce5abfb11b47a24a4b3c104e43b0e1bc2e3cf616a7ac318836fe70afeb6d33d6a22907cf03eac9cad52e61c689c11ca3f84c8e1c33fa68f64334761139f0cedaf576ab72f2cb6fdabcb8caeba091bfac73944b2041ba3984e889800543bf4eaafe114a2d42fab9af6145576b1293e59daf4bb7dafcbfc926484cd43aa3e22b4578851122cff19531ff778bf0ec9f4e297526ac959de3176dd9de50bf314757bbb10fbaccd1d0903bb09e63ae8463e2e0f1a6982ad92e645fbec52f9feeb96055885ca8d else 0x40000000000000000000000
private def coarse6_3 (k : ℕ) : ℕ := if k < 7 then 0x1a82a025b004509e1be8008fa7301d8597966711fe1968702e09a9f93d8bf2875e303e71e758c9cb118a11412b71d934fe54543115d6e489daf91297bbb1d6cdbe68fc6e47c67e5ec857c6abd2110ee3e14fdf72461ae54b1eb71a209f701c6ffb5bfebed3248f78bc51f239e12c6214cffc888e93158fb3bb049841563dae81ced092c67a0b1e47d23a6887e99b67ba37caf8f8f5dec646f85ba1c6c8c615c94a03176acf82d45ae4ba6bd3e82ad8c5bb4bb058f17126a82185c302a361a7fe832f40bdd5a6688662f5019794a09ae4a0bb300a192f895f3cc511d891c223dd29521af29a3c484f1ced44905c861cf21352595e0bf350e7112e8ac7cd3ad58fee7f0811f94bc424209ed0dc97f59c49f62c98fbba7e4f8c221a5694aeff573116df1555d62aef78b8442987d22cf5769cc3eebbb6276d998478c1e1be3072f8752623b99ce03347e43aedb29311c504d6521181514c3ef1535754b168d3122c2bb20d79e651a8c515f98408 else coarse7_2 k
private def coarse4_5 (k : ℕ) : ℕ := if k < 6 then coarse4_2 k else coarse6_3 k
private def coarse0_9 (k : ℕ) : ℕ := if k < 4 then coarse0_4 k else coarse4_5 k
private def coarseWords (k : ℕ) : ℕ := coarse0_9 k
private def coarse (k : ℕ) : ℕ :=
  (coarseWords (k/16) >>> (182*(k%16))) % (2^182)

private def fine0_2 (k : ℕ) : ℕ := if k < 1 then 0x7ffff75356e26ce4980b246005e3f6c5af76e1043e2ffdffffe1c63b3736943c557a0015fdbb7af33fbb38186977ffff97c097d8f38e7ff19a0051ae6f6f11dc16f6dbb49ffffe9cb1bc6221fd3f4688012d97c396f8496eba34377ffffb55c72993854dedeac00451d7250c9ae8a1ff9111fffff094289634bd417eea000fb53cec4b2f5ccbaac5b7ffffce08fe5558f9f95c3800388c7507df4be962f5749fffff62161a33eec9234e0000c90fd957659b030ec27b7ffffe1c63afe1d20e01b86002bfb779c131aceaffa2c5fffffa72c6e9d3ff41c54180096cbe36e11d3a6e3d6aa7fffff094288757b261ffce001f6a7a152581e97b8ab6dfffffd8858674a183c6ae28006487ed27b93a99e8944a7fffffa72c6e7e6dd13a1140012d97c7ad6e7f9f672075ffffff621619ba2be091108003243f6a35d6af72c8daa7ffffff621619b41554ee2e0006487ed4e7b3cc45aa476000000000000000000000000000000000000000000000 else 0x7fffdaf35130e4e41592a1400c2c749021641f80da0e8dffff753572dabea20b2976002f1fb2fbef74a1686d3e37fffdf93ab050ac016f715800b6364ec053e4105857401ffff8718f06e71793938ee002bfb745d3420cc7c7b5d57fffe3e50ffa0dc1ea114da00a9a5540e2bbc88842f175ffff97c09a802cd3c26cdc8028d735a357672d94f93477fffe7e7800d440cad6d396009d1458f35e3061aea84b9ffffa72c7105aaa6c4ed6e8025b2f6d049610d3128c4d7fffeb9afb3c3477d1f86460090835d77aba4dd824e6a1ffffb55c73f567b8ab856580228eb7e5fa27c35a8c8ce7fffeeff8184968f1c888700083f261a2d47f796ea4d45ffffc250a346a3a1338044801f6a78e659d4b672e2a1c7ffff21512e45292a7440a8007761657c9925e9e01438dffffce08fef160c9721050001c4639d358815a021fedd7ffff4dbaf598176e2ec844006ad0690cb9fe1577d66f1ffffd88586ee646bd93c5c801921faaee6472d846b46f
private def fine2_2 (k : ℕ) : ℕ := if k < 3 then 0x7fffaad614ad374be68817001274f079fa9e02c577ef91fffeb9afcdc25132c5af94004841a3388c00a0b67224c7fffb1ee1503bc655c937a6011abe11f823df01b9a26f9fffed571e598945470385500451d65b89f607a44015f27fffb8b7209746e667e118e010e2d1ba234f77faf4591dfffeeff82a5a75bbf073c88041f9280e109304bf3441b7fffbf313763a74fd8f182601019c24a59d8bf6caf0009ffff09429bf798d50b084b803ed4ea3acfb0e14ca10767fffc55c5964ded6c238d0800f50b2d0a1dff1e6cc7949ffff21513a6063dc916739003bb0ac40ccd2ca2b4348f7fffcb3886971f647a9590800e87a34d776b40ffa7ed61ffff38240585ffe06b6c7c00388c6e21f8119182778cb7fffd0c5bef6cb969fa9a0200dbe93c15680e421743179ffff4dbafd5a58bfa085ec0035682fe04186202ff6d4d7fffd604028076bf181501400cf5842cbb27183dbaa409ffff621621d01d2a606286803243f17d99497495d2033 else 0x7fff66fba8c2dd0411e73ce018bd698b2ec02c157888ddfffdaf3568d900cce316e18061638850973b3b52869e97fff708b4e83b482d006b28017f45a995bad14c70ac079fffdd4d616a9faf763bc5c805e3f4c6b7f6ee7bf102037fff79cbffa9e6ba972be4c0172b4b98c1db7ae3b3e25dfffdf93af204dd6a43ba4b805b1b104c44b4531ccb75e7fff82bdbc2fbe8a8f0900c016623c89dd51454ba7a7c9fffe1c63fad3350a7423ab8057f6d3f4d7232ab48c2597fff8b60840fb7860952e96015992d6d2a1463affbde5dfffe3e5130ff518d94f3d68054d2976726d33e79ac2b27fff93b457447df4852877c014d01e43242ace462774f9fffe5f029474457a026f718051ae5aa523dc7fd807fd77fff9bb935c8eed1b25bb1c014070f0c479a857b817e45fffe7e78251de626e20d32004e8a1db0be570081fabec7fffa36f1f9817cd749cf4e0133dffc9106991a8c0335dfffe9cb1e2e8cbbc2ee66f804b65e08be65af13e5a14f
private def fine0_4 (k : ℕ) : ℕ := if k < 2 then fine0_2 k else fine2_2 k
private def fine4_2 (k : ℕ) : ℕ := if k < 5 then 0x7fff0f6417e892aba0df7da01f05decbb1d69a721f5781fffc55c66d36ef2a339481007a855e63e133da42be2e87fff1b6b619a4754baa65aa01e3cd06185878aca1c704dfffc8545ab35258455f1a38077612495a41c22fbbe3617fff2723b6e5d911c9225b401d73c1e4b24c22c7c904edfffcb389178c42510763fc80743cea7dc35e2fcbee3537fff328d17c40d212c8a50001caab355b429f802286bb1fffce090b21fbbf1dbb1c1807118b01e2f106d9f6db927fff3da7842dd9754fa42aa01be1a4b50726ab4526e3f9fffd0c5c7ad3cb98999be4806df47578d749759cfe65f7fff4872fc1c64b4ac1c97001b1896032747e84518d0e9fffd36ec718d6d474c0060006ad03a8fac200bf400e9a7fff52ef7f890639cec089001a4f87409093655239efc9fffd604096325fd052845c0067abff649dab1eaa71af87fff5d1d0e6d46135b98bfa01986786dbf0ee30c2c85f5fffd8858e8a924d671c620806487c3f99c01c46ae59fa else 0x7ffea40f6fa056fb868f01e0254e4f437883eb17bfc749fffaad63102146e18a510e8093a721923c4acf5c9ae477ffeb28e5b680b6b852727e02485417ff45b0413a4e415fffae6c0d6f99ddfa05a69009082ea56df76029cddaa47ffec0be530a4c4bc314efc023bc33a5e91acf4a325571fffb1ee2cd2a8d822f8d4c808d5eb2c25e4e5a43724de7ffece9f567e593af67cb80022f325b5d2c87de90bf339fffb55c8f29175abd5015d808a3a7ad6a8e8b65f0478c7ffedc3165bba28bb91bb200222a17b02d694eb6c397bdfffb8b73470c790ec6d0718087164295af5a2cc8f6d3d7ffee97480b9c9448d8fd1802161099575028dc6589961fffbbfe1ca7a7d2ce8fa378083f20a0161b807f360d1f7ffef668a7709f1fe481b2202097fb662599942ab7398dfffbf3147cbb2a57e1cfb78080cdd11bb017c5b70c70c7fff030dd9d8268c21b071601fceed22bb33c7aa380b7dfffc250b5daeebb12de6a3807da997e68a8f162173b5a
private def fine6_2 (k : ℕ) : ℕ := if k < 7 then 0x7ffe24fdc07768b15bddbfa02b96b9fa782799e3b02d61fff8b60b930a332fb7c3fb80acc8cdfb7dca56e358d8e7ffe35f44c18d7a578efd8a02acdacfc9d6d4928372141fff8f947d9e3efb4c40bf400a9a499cf06612784ffa2c7ffe469be3e1af5d853ff0402a049fe45b742e97f49c55fff93b485146aaf07f6fe380a6806539ea063c0a317267ffe56f487c7a9d9e65e9700293b92b22e4103d70d5a3dfff97c0cf909ae4be74e0700a35c303e18cc9b23a35737ffe66fe37c0b1ceb6fc2dc02872856691d89286971ad5fff9bb95d10505feda036c00a037fadd82c78adccdfdc7ffe76b8f3c2e2a3cd212aa027a97802023fb3f818618dfff9f9e2d91181102f90f3009d13c51a180a8f69ec9357ffe8624bbc48874c048556026e06a84fb7b50e1082e51fffa36f41108b155d1c8290099ef8ef5c8a969f5fb92c7ffe95418fbc2010ef5af78026175ceff990610e4da9a5fffa72c978c4eb74d3fff30096cb587284b81770b766b else 0x7ffd922f1e064401efcacba031df1df8a704419d1c7d9dfff66fc04390d5dfd5c13c80c5ea5fbf7e7f98b33203c7ffda59d46e3c0b055d31be0311611df76e2796eecd4bdfff6bcdb000d9e9acb71b080c2c62f1df131fe11638dc7ffdb8bc7c41af61e5f38d20304d05a7ff5e7db8c32f39fff708b9ee747fd000e14580bfa1fe043e63ea01454607ffdcb8cbe14447a4abd09e02f83f952bc7c7d7537fd31fff7535d0e96ac751b001780bc7dcc7456263d555bf9c7ffdde0e0c4fe510ade49ce02ebaece02a40b9ffd53c3dfff79cc460461a4dc9aefb00b9599a70288a21caf2deb7ffdf04066e926efbf6c0be02df1e050c4af86c8968ce1fff7e4efe35581ebe425d800b63567f9a5a108d81bcc37ffe0223cdd4d095bcac68002d28d3a507cd4907693b69fff82bdf97985eaf84e1d680b3113512bd7caa79af4c87ffe13b84107d934774294002c5fc6dd6f9e776fac3f55fff871937ce2eec7251b6080afed01bd602f04014c801
private def fine4_4 (k : ℕ) : ℕ := if k < 6 then fine4_2 k else fine6_2 k
private def fine0_8 (k : ℕ) : ℕ := if k < 4 then fine0_4 k else fine4_4 k
private def fineWords (k : ℕ) : ℕ := fine0_8 k
private def fine (k : ℕ) : ℕ :=
  (fineWords (k/16) >>> (182*(k%16))) % (2^182)

private def correction0_2 (k : ℕ) : ℕ := if k < 1 then 0x8000006000001800000a00000180000060000028000006000001800000a000001800000600000180000060000018000006000002800000600000180000060000018000006000002800000a00000280000060000018000006000001800000a000002800000a00000180000060000018000006000001800000a000001800000a00000180000060000018000006000001800000a000001800000a00000180000060000028000006000001800000a000002800000a000002800000600000180000060000028000006000002800000a000001800000600000180000060000018000006000002800000a000002800000a000001800000a0000028000006000001800000a0000028000006000001800000a000001800000a0000028000006000001800000600000280000060000018000006000001800000a0000018000006000001800000a00000180000060000028000006000001800000a0000018000006000002800000600000180000060000018000006000001800000a0000028000006000002800000a0000018000006000001800000a00000180000060000018000006000000 else 0x800400600100180080060010018000006001001800400600200180080060020018008006001002800000a002001800000a0010028008006001001800400600100180040060020018008006001001800400a00000280040060010018004006002001800400a0020018004006001001800400600100180040060000018004006000002800400600100180040060010018008006000002800400600100180040060020018008006001001800400a001002800400a0020018004006000002800000a002001800800600100180040060010018004006001001800400a001001800400600100280080060010018004006002001800400a001002800400a0010018004006001002800000a00000280080060010018004006001002800000a000002800000a0020018004006000001800400600000280040060010028004006001002800400600000180040060010017ffc00a00000180080060010017ffc0060010017ffc009fff002800400600100180000060000017ffc0060010017ffc005ffe0017ffc0060010017ff4009ffb0017fec0060000017ff4005ffd0017fa0006000001
private def correction2_2 (k : ℕ) : ℕ := if k < 3 then 0x800000a00100180080060000018000006001002800400600100180040060010018004006001001800000600100180000060000018004006000001800000a0000018000006001001800000a001002800000a000002800400600100180040060010018004006001002800000a000001800000a00000280040060000028004006000001800400600100180000060000018004006000002800400600000280000060010018004006001001800000a001001800400600100180040060000018000006001001800000a00100180040060010028000006000002800000600100280040060010028008006000001800400600000280000060000028000006000002800000a0010028000006001001800000600000180000060000027ffc0060010017ffc0060010027ffc009fff0028000009fff001800000600100180040060000018000005fff0018000005fff0027ff8009fff0018004005fff0017ff400a0000017ff8005fff00180000060010017ffc009ffe0027ff0005ffe0027ff4005ffb0017ff00060000017fe8005ff50027fcc009ffe0017fe0005ff80017f3800a000001 else 0x800400600000280080060000028000006001001800000a000002800400a001001800400a0010028000006001002800000a00100180040060000018004006001001800000a002001800000a001001800000a0000028000006001001800000a001001800400a001002800000a001001800000a00000280000060000018004006000002800000a001001800000a000002800400a0010018004006000001800000a002001800000a001002800000a00100180000060010018004005fff002800000a0010028004006000001800000a0020018000006001001800000a001001800000a0020018008006000001800000600100180000060000017ffc00a00000180000060010027ffc00a001001800000600000180000060010017ffc0060010017ffc0060020017ff8009fff0018000005fff0017ffc00600100280000060010017ff8009ffe0028000005fff0017ff8005ffd0018004005fff0017ff0005fff0027ff4005ffe00180000060010017ffc005ffd0017fe8005ffd0027fec005ff80027fe8005fff0027fd8009ff00017fb0005ffc0017fd0009ff30017ed800a000001
private def correction0_4 (k : ℕ) : ℕ := if k < 2 then correction0_2 k else correction2_2 k
private def correction4_2 (k : ℕ) : ℕ := if k < 5 then 0x800000600100180080060000017ffc0060000018000006000001800000a000002800400600100280000060010017ffc006000001800000a0000018000009fff0028000006001002800000600100180000060000018000006000002800000600100280040060010018000005fff0027ffc0060000028000009fff0018000005fff0027ffc0060000027ffc00a000001800000a00000180000060000017ffc00600100180000060000028000009fff0027ffc00a0010028000005fff00280000060000018000009fff00180040060010017ffc005fff0017ffc0060000017ffc00a0010018000009fff0017ffc00a0000018000005ffe0027ffc005fff00280000060010017ff8009fff0028000005fff0018000005fff0027ff800a0000017ff80060010017ff4005ffe0017ffc005ffe0017ff80060000027ffc00a0000017ff4005ffd0017ffc005ffd0017ff4005ffc0028000005ffe0017fe8005ffd0027fec005ffc0017ff80060000027ff4005ffc0017fdc005ffb0027fe0005ff40027fd8005ffe0027fcc005fe90027f94005ffa0017fc0005fef0017e74006000001 else 0x7ffc00a0000018000009fff0017ffc0060000018000005fff0028004006000001800000a0000027ff800a0010017ffc005fff0028004005fff0018000005fff0017ffc0060010018000005fff0028000005fff0017ffc00a0000017ffc00600000280040060000017ffc005fff0017ffc00a0000018000005ffe0028000005ffe0027ffc00a0000027ffc005fff0018000009fff0017ff8005fff0027ff800a000002800000a0000018000005fff0027ffc0060010017ffc005fff00180000060000018000005fff001800000a0010017ff8009ffe0027ffc0060000017ffc00a0000028004005ffd0027ffc005fff0017ffc005ffe0017ff8009ffe0027ffc0060010017ff8005fff0017ff8009fff0017ff8009fff0017ff4005fff0027ff40060000017ff0005ffc0027ff8005ffd0017ff000a0010017ffc005fff0017fec009ffb0017ff8009ffc0017fec005ffa0017ffc005ffc0017fe4005ffc0017fe0009ffa0027ff80060010017ff0009ffb0017fcc009ff90027fd8005ff10017fd0005ffe0017fbc009fe30017f74009ff80027fac005fea0017e10006000001
private def correction6_2 (k : ℕ) : ℕ := if k < 7 then 0x800000a0010018008005fff00180000060000028000006000001800400600100180040060020017ffc00a00100180000060000028000009fff002800000a000001800000600100180000060000018000006000001800000a0000018000006001002800400600100180000060000017ffc00a0010017ffc009fff0018004009fff00180000060000027ffc005fff0018004005fff0027ffc005fff0017ffc00a001002800000a00100180000060000017ffc00a0010017ffc005fff00180000060010018000009fff00180000060010027ffc009fff0017ffc00a00100180000060010028004005ffe0027ff800a0000017ff8009ffe0017ff8005fff0027ff800a0000017ff80060000017ffc009fff0017ffc005fff0017ff4009fff0027ff40060000027ff0005ffc0017ff8009ffd0017ff00060000027ffc009fff0017ff0005ffa0027ff8005ffb0017fec009ffa0017ffc005ffd0017fe0005ffc0017fe0005ffa0017ff400a0010027ff0005ffa0017fc4009ff90017fd0005fee0027fc8005ffe0017fb0005fdd0017f5c005ff70027f9c005fe60017dac006000001 else 0x7ffc00e0000018004005fff0017ff800a0000018000005fff0018000006000002800000a0010017ffc0060000017ffc009fff0028004005ffe0028000005ffe0027ff800a0000027ffc005fff0028000005fff0017ffc00a0000027ffc00600000180040060010017ffc005fff0017ff800a0000017ffc005ffe0018004005ffe0017ff800a0000017ff8009ffe0027ffc009fff0027ff8005ffe0017ff800a00000280000060000027ffc005fff0017ff800a0010017ffc005ffd0027ffc00a0000018000005ffe00280000060000027ff8005ffe0027ff80060000017ffc0060000028004005ffc0027ff8005fff0017ff4009ffd0017ff4005ffe0027ff400a0000017ff4009ffe0027ff8005ffe0017ff4009fff0027ff0005fff0017fec00a0000027fe8005ffa0027ff4005ffb0017fe80060000017ff8005fff0027fe8005ff90027ff4005ff90027fe8005ff80017ff8005ffb0017fd4005ffa0027fd8005ff80027ff000a0000017fe8009ff80027fb8005ff60027fc8009feb0027fb8005ffc0027fa0009fd70017f3c005ff50017f88009fe10017d48006000001
private def correction4_4 (k : ℕ) : ℕ := if k < 6 then correction4_2 k else correction6_2 k
private def correction0_8 (k : ℕ) : ℕ := if k < 4 then correction0_4 k else correction4_4 k
private def correction8_2 (k : ℕ) : ℕ := if k < 9 then 0x8004006000001800400a0000017ffc00a0000017ffc00a0000018004006000001800000a0010027ffc0060010017ffc0060000018004005fff0028000009fff0017ffc0060020017ffc00a000002800000a0000017ffc00a0000027ffc00a00100180040060010027ffc00a0000017ffc0060000028000005ffe0018004005ffe0017ffc0060000027ff8009fff0018004005fff0027ffc005fff0017ff800a001001800000a0000028000005fff0027ff80060010028000005ffe00180000060010018000005ffe00180000060010017ff8009ffe0027ffc00600100180000060020018004005ffd0017ff80060000017ff4009ffd0017ff4005fff0017ff80060010017ff4009fff0017ffc005ffe0017ff8005fff0027ff4005fff0027fec0060010017fe8005ffb0017ff4009ffb0017fe400a0010017ff8005fff0017fe4009ff90017ff4009ffa0017fe4005ff70017ff8009ffb0027fd4005ff90027fd4005ff70017ff00060010027fe8005ff80017fb0009ff50027fc0009fe90017fb0005ffd0017f94009fd20017f20009ff40017f78009fdd0027ce000e000002 else 0x800000a0000028004009fff0017ffc005fff0017ffc009fff002800000600000180040060010027ff800a0010017ffc005fff0028000009ffe0028000009ffe0017ffc0060010017ffc0060000017ffc005fff0017ffc0060000017ff800a00000180040060000027ff8009fff0017ff80060000017ffc005ffe0028000009ffd0017ff800a0000017ff8005ffe0028000005fff0027ff4005ffe0017ff800600000280000060000017ffc005ffe0017ff80060010017ff8009ffd0027ffc00a0000018000005ffd0027ffc00a0010017ff8005ffd0027ff4009fff0027ffc0060010018004005ffb0027ff4005ffe0027ff4005ffc0017ff0005ffe0017ff40060000027ff0009fff0017ff4009ffe0017ff4009ffe0027fec00a0000017fe80060000017fe4005ff90017ff0009ffa0017fe40060000027ff4005ffe0017fe0009ff80017ff4005ff90017fe0005ff60027ff8005ffa0027fcc005ff90017fc8009ff60017fec0060000027fe4005ff70017fa8005ff40017fb8009fe50017fa4005ffc0017f84009fcc0017f04005ff20017f68005fd80027c84006000001
private def correction10_2 (k : ℕ) : ℕ := if k < 11 then 0x8000005fff0028004005ffe0017ff8005fff0017ff8009ffe001800000600000180000060000027ff80060000027ffc005fff0018000009ffe0028000005ffe0017ffc0060000017ff8009ffe0027ffc005ffe0027ffc0060000017ff800600000180040060000017ff8005fff0017ff400a0000017ff8009ffd0028000005ffc0017ff4009fff0027ff0009ffe0017ffc005ffe0027ff0009ffe0017ff40060000017ffc0060000017ff8009ffd0027ff000a0000017ff8005ffd0017ffc005fff0017ffc005ffd0017ffc0060010017ff4005ffd0017ff400a0000017ffc0060000018000009ffa0027ff0009fff0017ff0005ffb0017ff0005ffe0017ff0005fff0017fec009ffe0017ff4005ffd0017ff4005ffe0017fec005ffe0027fe4005fff0027fe0005ff80017ff0005ff80017fdc0060000017ff4009ffe0027fdc005ff60027ff0005ff60027fdc005ff50017ff4009ff90017fc0009ff80017fc4005ff40017fe80060010017fe0009ff50027f98005ff20017fb0005fe10027f98005ffb0017f78005fc60017ee4009ff00017f54005fd40017c1c006000001 else 0x800000a0000028008005ffe0027ff8009fff0017ffc009fff002800000600000180000060010017ff80060010017ffc005ffe0028004005fff0018000009ffe0017ff800a0010027ff8009fff0028000005fff0027ffc0060000027ff8006000001800000a0000027ff8005fff0027ff800a0000027ff8005ffd0018000005ffd0017ff80060000017ff4009ffe0017ffc005fff0027ff0009ffd0027ff400a00100180000060000017ffc009ffe0017ff40060010017ff8009ffc0027ffc009fff0028000005ffe0017ffc00a0010017ff4005ffd0027ff40060000017ffc00a0010028004005ffb0017ff0009fff0017ff0005ffb0017fec005ffe0017ff0005fff0027ff0005ffe0017ff4005ffd0027ff0005ffe0017fec005ffe0027fe000a0000017fdc005ff80017fec009ff80017fdc0060000027ff8005ffe0017fdc005ff50027ff0005ff60027fd8005ff40017ff4005ff90017fbc005ff70017fc0005ff40017fe80060010017fe0009ff40027f90005ff10027fa8009fdf0017f8c009ffb0017f6c009fc00017ecc005fef0017f48005fd00017bbc006000002
private def correction8_4 (k : ℕ) : ℕ := if k < 10 then correction8_2 k else correction10_2 k
private def correction12_2 (k : ℕ) : ℕ := if k < 13 then 0x7ffc009fff0028000009ffe0017ff8005fff0017ff8005ffe0018000005fff0017ffc0060000027ff40060000017ff8009ffd0028000009ffe0018000005ffd0017ff800a0000017ff8005ffe0027ffc005ffe0027ff400a0000017ff400a00000180000060000017ff8005ffe0017ff4009fff0017ff4009ffc0027ffc005ffc0017ff4005fff0027ff0005ffd0017ff8009ffe0017ff0009ffc0017ff000a0000017ffc009fff0027ff4009ffd0017ff00060000017ff8005ffc0017ffc005fff0017ffc005ffc0027ffc0060000017ff0005ffc0027ff0009fff0017ff80060000028000009ffa0017fec005ffe0017fec005ff90017fec005ffd0017fe8005fff0027fe8009ffd0017ff0009ffc0027fec005ffd0017fe8005ffe0017fdc005fff0017fd4009ff60017fec005ff60027fd40060000017ff0009ffd0027fd4005ff40017fec005ff50017fd0009ff20017fec009ff80017fb8005ff60017fb8005ff20017fe40060000027fd8005ff30017f84005fef0017fa0005fdb0017f84005ff90017f5c005fba0017eac009fec0027f30009fcb0017b58006000001 else 0x7ffc009fff0018000009ffd0027ff4009ffe0027ff8009ffe0017ffc005fff0017ffc0060000027ff40060000017ff4009ffd0018000005ffd0028000005ffc0027ff80060000027ff4005ffe0017ffc005ffe0027ff4009fff0027ff40060000018000009fff0027ff4005ffe0017ff4005fff0017ff4005ffc0017ffc005ffb0027ff0009fff0017ff0005ffc0017ff8009ffe0017ff0005ffc0017ff000a0000017ffc005fff0017ff8005ffc0027fec00a0000017ff8005ffb0017ff8005fff0017ff8005ffb0027ff800a0000017fec009ffb0027ff0009fff0017ff800a0000028000005ff90017fec005ffe0017fe8005ff80017fe8005ffc0027fe8005fff0017fe4009ffd0017fec009ffc0017fec005ffc0017fe0009ffd0027fd8005fff0017fd4005ff50027fe8005ff60017fd0005fff0017ff0005ffd0017fd0005ff20027fe8009ff40017fd0005ff10017fec005ff60027fb0005ff40017fac009ff10017fe00060000017fd8005ff20017f78009fed0017f98005fd80017f78009ff80027f50005fb30027e90009feb0017f20005fc60017af4006000001
private def correction14_2 (k : ℕ) : ℕ := if k < 15 then 0x7ffc00a0000028004005ffe0017ff4009ffe0027ff8009ffe0017ffc00a000002800000a0010027ff400a0010017ff8009ffe0028000009ffe0018000009ffe0017ffc0060000027ff4005ffe0027ffc005fff0017ff4009fff0027ff400600000180000060000027ff8005fff0017ff000a0000017ff4009ffc0028000005ffc0017ff40060000017ff0009ffc0027ffc005ffe0017fec005ffd0017ff40060010017ffc005fff0027ff8005ffd0017fec00a0000017ff8005ffc0017ff8009fff0017ffc005ffc0017ffc00a0000027ff0005ffc0027ff0005fff0027ffc0060010028004005ff90027fe8009ffe0027fe8009ff90017fe8005ffd0017fe8005fff0027fe8005ffd0017fec009ffc0017fec005ffc0027fe4005ffe0027fd8005fff0027fd4005ff50027fe8009ff50027fd0005fff0027ff0009ffe0017fd0009ff30017fec005ff30017fd0005ff00027fec009ff70017fa8009ff40027fac005ff00017fe00060010017fd4005ff10017f70009fed0017f90005fd60017f6c009ff90017f44005faf0027e74009fe90027f14005fc30017a94006000002 else 0x7ff8025fff0057ff801dffd0037ff0011ffd0037ff400dffd0027ffc009fff0037ff800e0010027ff000a0000027ff400dffd0027ffc009ffd0027ffc00dffc0027ff400a0000027ff0009ffe0017ff8009ffe0017ff0009fff0017ff4005fff00280000060000027ff0009ffd0027ff0009fff0017ff4009ffb0017ffc009ffa0027ff0009fff0027fec005ffb0027ff8009ffd0027fec009ffb0027fec009fff0027ffc005fff0017ff4009ffc0017fec0060000027ff4009ffb0017ff8009fff0017ff8009ffb0017ff80060000017fec009ffb0027fec009ffe0027ff80060000028000009ff80017fe8005ffd0027fe4009ff80017fe4009ffc0017fe4009fff0017fe4005ffc0027fec005ffb0017fe8005ffd0017fe0009ffe0017fd0009fff0017fcc005ff40017fe4009ff50017fcc005fff0027fec009ffc0027fcc005ff10027fe4005ff20017fc8009fee0027fec005ff60017fa4005ff20027fa4009fee0017fdc0060000017fd0009ff00017f64005feb0017f88005fd20017f60009ff70027f34005fa90017e58005fe70027f00005fbe0027a30006000001
private def correction12_4 (k : ℕ) : ℕ := if k < 14 then correction12_2 k else correction14_2 k
private def correction8_8 (k : ℕ) : ℕ := if k < 12 then correction8_4 k else correction12_4 k
private def correction0_16 (k : ℕ) : ℕ := if k < 8 then correction0_8 k else correction8_8 k
private def correction16_2 (k : ℕ) : ℕ := if k < 17 then 0x7ffc009fff0018004005ffd0017ff4005ffd0017ff4009ffd0017ff8009fff0027ffc00a0010017ff000a0000027ff4009ffd0018000009ffd0018000009ffc0017ff40060000017ff0005ffd0027ff8005ffe0027ff0009fff0027ff000a00000180000060010017ff0009ffe0017fec009fff0027ff0009ffb0027ffc005ffa0017ff0005fff0017fec005ffc0017ff8009ffd0027fe8005ffb0017fec0060000027ffc005ffe0027ff4005ffb0027fec0060000017ff0009ffa0027ff8005ffe0017ff8009ffb0027ff400a0000017fe8009ffa0027fe8009fff0017ff400a0000027ffc009ff80017fe4009ffd0017fe4005ff60027fe0009ffc0017fe0009ffe0017fe0005ffc0027fec005ffb0017fe4005ffc0027fe0005ffd0027fd0009ffe0027fc8009ff30027fe0009ff40017fc4009fff0027fec009ffc0027fc4009ff00027fe4005ff00027fc4005fed0027fe8005ff50027f9c009ff10027f9c009fed0017fd4009fff0027fcc009fee0027f58009fe80027f7c00dfce0037f58009ff60037f20011fa20027e3400dfe40047ee001dfb600679b0026000001 else 0x7ffc009fff0028000009ffd0017ff4005ffd0017ff4009ffd0017ffc00a0000017ffc00a0010017ff00060000017ff4005ffd0017ffc009ffe0018000009ffc0017ff400a0000017ff0009ffd0027ff8009ffd0027ff4005ffe0027fec00a00000180000060000027ff4005ffe0017fec005fff0017ff0005ffb0017ff8009ff90027ff00060000017fe8009ffb0017ff8009ffd0027fe8005ffb0027fec005fff0027ffc005fff0017ff4009ffb0027fe8009fff0027ff4005ffa0017ff4009ffe0027ff8005ffa0017ff40060000027fe8005ffb0017fe8005fff0017ff400a0010017ffc009ff60027fe4005ffd0017fe4005ff60017fe4005ffc0017fe0009ffe0017fe0009ffc0017fe8005ffa0027fe4009ffc0017fdc009ffd0017fcc009fff0017fc8005ff30017fe0009ff30017fc4005fff0027fe8009ffc0027fc0005fef0017fe0005ff00017fc0005fec0017fe8005ff50017f98005ff10017f98005fec0027fd4005fff0027fc8009fed0017f50005fe80017f74009fcc0027f4c009ff60027f18009f9d0017e20005fe40017edc005fb5002796c00a000001
private def correction18_2 (k : ℕ) : ℕ := if k < 19 then 0x80000060000018004005ffd0017ff4009ffd0027ff8005ffd0027ffc005fff0027ffc00a0010017ff000a0000027ff4009ffd0028000009ffe0018000009ffb0027ff80060000027ff0009ffe0017ff8009ffe0027ff400a0000017ff000600000180040060000027ff0009ffe0017fec009fff0027ff4005ffa0027ffc009ffa0027ff00060000027fec005ffb0027ff8005ffe0017fe4009ffb0017fec00a0000017ffc005fff0017ff4009ffc0017fec0060000017ff4005ffb0017ff8005ffe0017ffc005ffb0017ff80060000027fe8005ffb0017fe8009fff0017ff400a0010028004005ff70017fe4009ffd0027fe4005ff60017fe0009ffc0017fe0009fff0017fe0005ffc0017fec005ffb0017fe4005ffc0017fdc005ffe0017fcc005fff0017fc4009ff20017fe0005ff20027fc0009fff0027fec005ffc0017fc0009fef0017fe0009ff00017fc0005feb0017fe4009ff40017f94005ff00017f94005feb0017fd40060000027fc8009fec0027f48005fe70017f70009fc90027f44005ff60017f0c009f980017e08005fe20027ecc009fb2001790800a000002 else 0x7ff8009ffe0028000009ffc0027ff0005ffd0017ff0009ffc0017ff4009ffe0027ffc0060000017fec0060000017ff0005ffc0017ffc009ffc0027ffc009ffa0027ff0009fff0027fec005ffd0017ff4009ffd0017ff0005ffe0017fec005fff0017ffc005fff0027ff0005ffc0027fe8005ffe0027ff0005ff90017ff8005ff80027fec005fff0017fe4005ffa0027ff4005ffd0017fe0009ff90027fe8005fff0017ff8005ffe0027ff0005ffb0017fe0009fff0017ff0005ff90027ff0009ffd0017ff4009ff90017ff0009fff0017fe4009ffa0017fe4005ffe0017ff000a0000017ffc005ff50027fdc009ffc0017fdc005ff40027fdc005ffb0017fd8005ffe0017fd8009ffb0017fe4005ff90017fdc009ffa0017fd4009ffc0027fc4005ffd0027fbc009ff00027fdc005ff00017fbc005ffe0027fe4005ffc0017fbc005fec0027fdc005fee0017fb8009fea0017fe4005ff30017f88005fee0027f8c005fe90017fcc00a0000017fc0005fea0027f38009fe40027f64009fc60017f34009ff40027efc005f910027de8005fe00017eb8005fac00178a400a000001
private def correction16_4 (k : ℕ) : ℕ := if k < 18 then correction16_2 k else correction18_2 k
private def correction20_2 (k : ℕ) : ℕ := if k < 21 then 0x7ffc005fff0028000009ffc0027ff4005ffd0027ff4009ffc0027ff8005fff0017ffc0060010017ff00060000027ff0009ffc0028000005ffc0028000005ffb0027ff40060010017ff0005ffd0017ff8005ffe0017ff0005fff0017fe8009fff00180000060000027ff0009ffe0017fe8009ffe0027ff0005ffa0017ff8009ff80027fec009fff0017fe4009ffa0027ff4005ffd0017fe4009ffa0027fe80060000017ff8009ffe0027ff0009ffb0027fe80060000017ff0009ff90017ff4009ffe0017ff8005ff90017ff40060000027fe4009ffa0017fe4009ffe0027ff400a0000028000005ff50027fe0005ffd0017fe0005ff40017fdc005ffb0027fdc005ffe0027fdc009ffb0027fe4005ff90027fe0005ffa0027fd4009ffd0027fc4005ffe0027fbc005ff00017fdc005ff00027fb8005fff0017fe8005ffb0027fb8005fec0027fe0005fed0027fb4009fe80027fe4005ff20027f84009fee0017f88005fe90017fcc00a0000017fbc009fea0017f30005fe40017f5c009fc20027f30005ff50017ef4005f8c0017dcc009fdf0027ea8005fa8001784400a000001 else 0x7ffc005fff0018000005ffb0017ff0009ffc0017ff4005ffb0027ff8005fff0017ff800a0000017fec0060000017ff0005ffc0017ffc005ffc0027ffc005ffa0027ff000a0000017fe8009ffc0017ff4009ffd0027fec005ffe0027fe8005fff0017ffc005fff0027fec005ffc0017fe8005ffe0027fe8009ff90017ff8005ff80017fec005ffe0027fe0009ff90027ff4009ffb0027fdc005ff90017fe4005fff0017ff8005ffe0027fec009ffa0017fe0005fff0027fec005ff90017ff0009ffd0017ff4009ff90017ff000a0000017fe4005ff90017fe0009ffd0027ff000a0000017ffc009ff40017fdc005ffc0027fd8009ff20027fd8005ffa0027fd4009ffd0027fd8005ffa0027fe0005ff80017fd8009ff90027fd0009ffc0027fbc009ffd0027fb8005fee0027fd8005fef0017fb0005fff0017fe4005ffb0027fb0009fea0027fd4009feb0027fb0005fe70027fe0005ff10027f7c005fec0027f80005fe60027fc80060000017fbc005fe90017f20009fe20017f54005fbf0017f20009ff30017ee0009f860017db0005fdc0027e94009fa300177e400a000001
private def correction22_2 (k : ℕ) : ℕ := if k < 23 then 0x7ffc005fff0018000009ffb0017fec009ffb0027ff0009ffb0027ff8009ffe0027ffc0060000017fe80060000017ff0005ffb0027ffc009ffc0027ffc009ffa0017ff000a0000017fe8009ffc0017ff4005ffd0017fec005ffe0017fe8009fff00180000060000017fec005ffc0017fe4005ffe0027fec005ff90017ff8005ff70027fe8005fff0017fe0005ff90017ff4005ffc0017fdc005ff80027fe4005fff0017ff8005ffe0017ff0005ffa0017fe0009fff0017fe8009ff80017ff4005ffc0027ff4009ff80027ff4005fff0027fe0005ff90017fe0009ffd0017ff000a0000017ffc005ff30027fd8009ffc0017fd8005ff20017fd8005ffa0027fd4005ffd0017fd4009ffa0027fe0009ff80027fd8009ff90017fd0005ffc0027fc0005ffd0027fb0009fee0017fd4009fee0027fb0005fff0017fe0009ffa0027fb0005fea0027fd8005feb0017fb0005fe50027fe0005ff00027f78005fec0017f74009fe60017fc8005fff0017fb8005fe80017f1c005fe00017f50005fbc0017f18005ff30017ed8005f800017d90009fdc0017e84009f9f002778400a000001 else 0x7ffc011fff0038000009ffb0027fec00dffc0017ff0009ffb0027ff8009ffe0027ff800a0000027fe800a0000017ff0009ffb0027ffc009ffb0027ffc009ff90027ff0005fff0027fe8009ffd0017ff4009ffd0027fe8009ffe0017fe8005fff0017ffc005fff0027fec005ffd0017fe8005ffe0017fe8009ff90017ff8009ff70027fe8009fff0027fe0005ffa0017ff4009ffb0027fdc005ff90017fe4005fff0027ff8005ffe0017fec009ff90027fe0005fff0027fec005ff80027ff4005ffd0017ff4005ff70027ff0009fff0027fdc009ff80017fe0005ffd0027ff40060000028000005ff30027fd8005ffc0017fd4009ff20017fd4009ffa0027fd4005ffd0017fd4005ffa0027fe0005ff80027fd8005ff90027fd0005ffc0027fbc005ffd0017fb0005fed0027fd4009fed0027fa8009ffe0027fe0005ffb0017fac009fe80027fd8005fea0017fac005fe50027fdc009ff00027f70005feb0017f74005fe50017fc40060000017fb4005fe60027f10005fde0027f48005fb90017f0c009ff30017ecc005f7a0027d78005fda0017e78005f9c001772400a000001
private def correction20_4 (k : ℕ) : ℕ := if k < 22 then correction20_2 k else correction22_2 k
private def correction16_8 (k : ℕ) : ℕ := if k < 20 then correction16_4 k else correction20_4 k
private def correction24_2 (k : ℕ) : ℕ := if k < 25 then 0x7ffc009fff0028000009ffb0017ff0009ffc0017ff4005ffc0017ff8005fff0017ffc0060010017fe800a0000017ff0005ffb0017ffc009ffc0028000009ffa0017ff4005fff0027fe8005ffc0017ff8005ffd0027fec005ffe0027fe8009fff0017ffc00a0000027fec005ffd0017fe4009ffe0017fec005ff90017ff8005ff70027fe8005fff0017fe0005ff90017ff4009ffc0017fdc009ff80027fe000a0000017ff8005ffe0027fec009ffa0017fe0009fff0027fec009ff80017ff0009ffd0017ff4009ff80027ff40060000027fe0009ff80027fe0009ffd0027ff40060000017ffc009ff30017fd8005ffb0027fd4009ff20017fd8005ffa0027fd4005ffe0017fd0009ffa0027fdc009ff80027fd4009ffa0017fcc009ffc0017fb8005ffe0017fb0005fed0017fd0009fed0027fa8009fff0027fe0009ffb0017fa8005fe90017fd4009fe90027fa8009fe40017fdc009ff00027f6c009fea0027f6c009fe40027fc4009fff0027fb4009fe50027f04009fde0017f40009fb70027f04009ff20027ec0009f740027d5c00dfd80027e6400df9600376bc012000002 else 0x7ff8009ffe0027ffc009ffa0027fe8009ffb0027ff0005ffa0027ff4005ffe0027ff400a0000017fe4009fff0027fec005ffa0017ff8009ffb0027ffc009ff90017fec005fff0027fe4009ffb0027ff4005ffc0017fe8005ffe0017fe0009ffe0027ff8009fff0027fe4009ffc0017fe0009ffd0017fe4009ff70017ff4009ff60017fe4009ffe0027fdc005ff90017ff0005ffb0027fd4009ff70017fdc005fff0017ff0009ffd0027fec005ff80027fd8009ffe0017fe8009ff60027ff0005ffb0027ff0005ff70017fec009fff0027fdc009ff70017fdc005ffc0027fec009fff0027ffc005ff20017fd4005ffb0017fd0005ff00027fcc009ff90017fcc005ffc0017fcc009ff90017fd8009ff70017fd0005ff80017fc8009ffb0017fb4009ffc0027fa8009feb0027fd0005feb0027fa0005ffe0017fdc009ffa0017fa0005fe70017fd0005fe70027fa4005fe20017fd8005fee0017f64005fe80027f64005fe10027fbc009ffe0027fac009fe40017efc005fdb0017f34009fb30017ef4009ff10027eac005f6f0017d3c009fd60027e54009f93001766400a000001
private def correction26_2 (k : ℕ) : ℕ := if k < 27 then 0x7ffc005ffe0028000005ffa0017fe8009ffb0027ff0005ffb0017ff4005ffe0027ff800a0000027fe8005fff0017fe8009ffb0017ffc009ffb0027ffc009ff90027fec009fff0027fe4009ffb0017ff0009ffc0027fe4009ffd0027fe4005fff0017ffc005fff0027fe8005ffb0027fe0005ffe0017fe8005ff70027ff4009ff50027fe4009fff0017fdc005ff80017ff0005ffb0027fd8005ff70027fdc009ffe0027ff4009ffd0017fe8005ff80017fdc005ffe0027fe8009ff60027fec009ffc0017ff4005ff60027fec009fff0027fd8009ff70017fd8009ffd0017ff00060000027ffc009ff20017fd4005ffb0017fd0009ff00017fcc005ffa0017fc8009ffc0017fcc009ff90027fd8009ff60027fd0005ff80017fc8005ffc0017fb0005ffc0027fa4009feb0017fcc009feb0017fa0005ffd0027fe0005ffa0017fa0005fe60017fcc009fe70027fa0005fe10027fd8005fed0027f5c009fe80017f60005fe10027fbc005fff0017fa8009fe30027ef0009fda0017f2c009fb00027ef0005ff00027ea0009f690027d24005fd50017e44005f8e0027608006000001 else 0x7ff400dffe0027ffc009ffa0027fe8005ffb0017fec005ffa0027ff0009ffe0017ff800a0000017fe4009fff0027fec005ffa0027ff8009ffb0017ffc009ff80027fec009fff0017fe0009ffa0027ff0009ffc0027fe4005ffd0027fe0009ffe0027ff8009fff0017fe4009ffc0017fdc009ffd0027fe4009ff70027ff0009ff50027fe0009ffe0017fd8009ff70027ff0005ffb0017fd0009ff70017fdc005ffe0027ff4005ffd0027fe8005ff80027fd8005ffe0017fe8005ff60027fec005ffb0017ff0005ff50027fec009fff0027fd8009ff60027fdc005ffc0017fec00a0000017ffc005ff10017fd0005ffb0017fcc009fef0017fc8009ff90017fc4009ffc0017fcc005ff80017fd8005ff60017fcc009ff70027fc4009ffa0027fb0005ffc0027fa0005fea0017fcc005fea0017f98005ffd0027fdc005ff90027f98009fe50017fcc005fe60017f9c005fe00017fd4005fed0017f58005fe60027f58009fdf0027fb8009fff0027fa8005fe20017ee4009fd80027f24009fad0017ee4005ff00017e94005f630027d08009fd30027e30009f8a00275a8006000001
private def correction24_4 (k : ℕ) : ℕ := if k < 26 then correction24_2 k else correction26_2 k
private def correction28_2 (k : ℕ) : ℕ := if k < 29 then 0x7ff8009fff0018000009ffa0017fec005ffa0027ff0005ffa0027ff8005ffe0027ff800a0000027fe4005fff0027fec005ffa0027ffc005ffb0028000005ff80027fec009fff0027fe4009ffb0027ff0009ffc0017fe8005ffe0017fe0005ffe0017ffc0060000017fe8009ffc0017fdc009ffe0027fe4005ff70017ff8005ff60017fe4009fff0027fd8009ff80017ff0005ffb0017fd4005ff70017fdc005ffe0027ff0009ffd0027fe8009ff80017fd8005ffe0027fe4009ff60027ff0005ffb0027ff0009ff60027ff0005fff0027fd8005ff60027fd8009ffd0017ff00060000027ffc009ff00027fd0009ffb0017fcc009fef0017fcc009ff90027fc8009ffc0027fcc005ff90017fd4009ff60017fcc009ff80027fc4009ffb0027fac005ffd0017fa0005fea0017fcc005fea0017f98005ffe0017fdc005ffa0017f98005fe40027fcc005fe60017f98005fdf0017fd4005fed0017f50005fe60027f54005fde0027fb8005fff0027fa4005fe10017ee0005fd70027f24005faa0027ed8009fef0027e88009f5e0017cf0009fd20017e20009f86001754800a000002 else 0x7ffc009ffe0028000005ff90027fe8009ffb0017fec009ffb0017ff4009ffe0027ff80060000027fe4009fff0017fec005ffa0027ffc009ffb0027ffc005ff80027fec005fff0027fe4005ffb0027ff4005ffc0027fe4009ffe0027fe0005ffe0027ffc009fff0027fe4009ffb0027fdc009ffd0027fe4005ff70027ff4005ff50017fe4005fff0017fd8009ff80017ff0005ffb0017fd4005ff70017fd8009fff0017ff0009ffd0027fe8009ff80027fd8005fff0027fe8005ff60027ff0005ffb0027ff0009ff60017ff0005fff0027fd8009ff70017fd8009ffc0027fec00a0000017ffc009ff00017fcc009ffb0027fc8009fee0027fc8005ff90027fc4009ffc0017fc8009ff90017fd4009ff60017fcc009ff70027fc0009ffb0017fac005ffc0027f9c009fe90017fc8009fe80027f94009ffe0017fdc005ff90027f94009fe30027fc8009fe40027f94009fde0027fd0009fec0027f4c009fe50027f4c009fdd0027fb8009fff0017fa0009fe00017ed4005fd60017f18009fa70027ed0009fee0027e7c009f590017cd4009fd00017e14005f8200274ec00a000002
private def correction30_2 (k : ℕ) : ℕ := if k < 31 then 0x7ff8009fff0028004005ffa0027fe8009ffa0027ff0009ffa0027ff4009ffe0027ff800a0000037fe0009fff0027fe8009ffa0027ffc009ffb0028000009ff80027fec00a0000027fe4009ffb0027ff0009ffc0017fe4009ffe0027fe0005ffe0027ffc00a0000027fe8005ffc0027fe0005ffe0027fe000dff70017ff4009ff50017fe4005fff0027fd8009ff80017ff0009ffb0027fd0009ff60027fdc009fff0027ff0009ffe0027fe8009ff80027fd8005fff0027fe4009ff50027fec009ffc0027ff0009ff60027fec00a0000027fd8009ff60027fd8005ffd0027ff0009fff0037ffc009fef0027fd0005ffb0017fc8009fee0027fc8009ff80027fc4009ffc0027fc8009ff90017fd4009ff60027fc8009ff80017fc0009ffb0027fa8009ffd0027f9c009fe80027fc8009fe80027f94005ffd0027fd8009ff90027f94009fe30027fc8009fe40017f94009fde0017fd4005feb0027f48005fe40027f48009fdd0027fb4009fff0017fa0009fe00017ecc009fd40027f14005fa50027ec8005fee0027e70009f530027cbc009fcf0027e04009f7f002749000a000002 else 0x7fc4101ffa0207fd0059ffa0117fcc039ff10167fd004dff90097fdc03dffc0087fec01e0000067fd002dffb00a7fe8019ffa0057ff8015ffa0057ff8015ff50087fe401dffd0077fdc011ffa0047ff0011ffb0047fdc019ffc0037fdc011ffd0067ff800dfff0047fe000dffb0037fd800dffd0047fe000dff50057ff400dff20057fe000dffe0047fd400dff60047fe8015ffb0037fd0009ff70027fd4011fff0037ff400dffd0037fe000dff60047fd000dffe0027fe8009ff60027fe8011ffb0047ff000dff50027fec00dfff0027fd400dff50037fd400dffc0037fe800e0000027ffc009fee0037fc8011ffb0027fc800dfed0027fc4009ff80027fc0009ffc0027fc8009ff80027fd4009ff50027fc400dff70027fbc00dffb0027fa4009ffc0037f9400dfe80027fc400dfe80027f8800dffe0027fd8009ff90027f90009fe10027fc8009fe30027f9000dfdb0037fd0009feb0027f44005fe40027f44009fdc0027fb0009fff0027f9c009fdf0027ec0009fd40027f0c005fa20027ebc009fee0027e64005f4e0027ca0009fcd0027df4009f7a002743000a000002
private def correction28_4 (k : ℕ) : ℕ := if k < 30 then correction28_2 k else correction30_2 k
private def correction24_8 (k : ℕ) : ℕ := if k < 28 then correction24_4 k else correction28_4 k
private def correction16_16 (k : ℕ) : ℕ := if k < 24 then correction16_8 k else correction24_8 k
private def correction0_32 (k : ℕ) : ℕ := if k < 16 then correction0_16 k else correction16_16 k
private def correction32_2 (k : ℕ) : ℕ := if k < 33 then 0x7ff8009ffd0038000009ff90027fe4009ff90027fec009ff90037ff0009ffd0027ff400a0000027fe0009fff0027fe8009ff90027ffc009ffa0037ffc009ff70027fec009fff0027fdc00dffa0037fec00dffb0027fe000dffc0037fd8009ffe0027ffc009fff0027fe4009ffa0037fd8009ffd0027fe0009ff50037ff0009ff30027fdc00dffe0027fd000dff70027fe800dff90037fcc009ff50027fd4009ffe0027ff0009ffd0027fe000dff60027fcc00dffe0037fe0009ff50027fec009ffa0037ff000dff30037fe4011fff0027fcc011ff50037fd4009ffb0037fe800dfff0037ff800dfed0037fc800dff90037fc400dfeb0037fc000dff70027fb8011ffa0037fc000dff60037fcc011ff30057fc400dff50047fb800dff90057f9c00dffa0057f9000dfe50037fc000dfe50047f8400dffc0037fd400dff60067f80011fe00037fbc019fe10037f84011fd80047fc4011fe80077f2c01dfdf0077f30015fd70057fa4015ffb0057f8c015fd900a7ea4031fcf0067ef801df9a0087e9403dfe60097e2c04df3d0167c70039fbc0117dbc059f5c0207310102000001 else 0x7ff4009ffe0027ffc009ff90017fe4009ff90027fec009ff90027ff4005ffd0027ff400a0000027fdc009fff0017fe4009ff90027ffc005ffa0027ffc009ff60027fe8005fff0027fdc009ffa0027ff0005ffb0027fe0009ffd0027fd8009ffd0027ff8009fff0027fe0009ffb0027fd8009ffc0027fdc00dff50027ff0009ff30027fdc009ffe0017fd000dff60027fe8009ffa0017fcc009ff50027fd4005ffe0027fec009ffc0027fe4005ff60027fd0005ffe0027fe0009ff40017fec005ffa0027fec009ff30027fe8009fff0027fd0009ff40027fd4009ffc0027fec009fff0037ff8009fed0027fc8005ff90027fc0009feb0027fc0009ff70027fbc009ffb0027fc0009ff70027fcc009ff40027fc0009ff60017fb8009ffa0027f9c009ffb0027f90009fe50027fc0009fe60017f84009ffd0027fd4009ff70027f84009fde0037fc4009fe00027f88009fd90027fc8009fea0027f34009fe10037f3400dfd80037fa8009ffe0027f94005fdb0027ea800dfcf0037ef8009f9b0027ea4009fec0027e48005f430027c68009fc90027dd0005f71002737800a000002
private def correction34_2 (k : ℕ) : ℕ := if k < 35 then 0x7ff4009ffe0027ffc009ff90017fe8009ff90017fec009ff90027ff0009ffd0027ff400a0000017fe0009fff0027fe4009ff80027ffc009ffa0018000005ff60027fe8009fff0017fdc009ffa0027ff0009ffc0017fe0005ffe0017fdc005ffd0027ff8009fff0017fe0009ffb0027fd4009ffc0027fdc009ff50027ff4009ff30027fdc009ffe0027fd0009ff60017fec009ff90027fcc005ff50017fd4009ffe0027ff0009ffd0027fe4005ff60027fcc009ffe0027fe0009ff30027fec009ffa0027ff0005ff40017fe8009ffe0027fd0009ff40027fd0005ffb0037fe8009fff0027ff8009fed0017fc4009ff90027fc0009feb0027fc0009ff70027fbc005ffb0017fc0009ff60027fcc005ff40027fc0009ff50027fb8009ff90027f9c005ffc0027f8c009fe40027fc0009fe40027f80009ffd0027fd0009ff70027f80009fde0027fc0009fe00017f84009fd80027fc8009fe90027f2c009fe00027f30005fd70037fa8009ffe0027f90009fdb0017ea0009fcf0017ef4005f990017ea0005fec0017e3c005f3d0027c4c009fc80027dc0009f6d002731c00a000002 else 0x7ff8009ffe0027ffc009ff80027fe0009ff90027fec005ff90027ff0009ffd0027ff400a0000017fdc009fff0027fe8009ff80027ffc009ffa0027ffc009ff70017fe8005fff0027fd8009ffa0027ff0009ffb0027fe0005ffd0017fd8005ffe0017ff8009fff0017fe0005ffb0027fd8005ffd0017fe0005ff50017ff4005ff30017fdc009ffe0027fd0005ff60017fec009ffa0027fc8009ff50027fd0009ffe0027fec009ffd0017fe4005ff60017fcc009ffe0027fe0009ff30027fe8009ffa0027fec009ff30027fe8009fff0027fcc009ff40027fcc009ffc0017fec0060000017ffc005fed0017fc4005ffa0017fc0005feb0017fc0005ff70027fb8009ffb0017fbc009ff70027fcc009ff30027fc0005ff50027fb4009ffa0017f98009ffc0017f8c005fe40027fc0009fe40027f7c009ffd0027fd4005ff80017f80005fde0017fc4005fdf0027f80005fd70027fc8009fe80027f2c005fe00027f28009fd70027fa4009fff0017f90009fd90027e98009fce0027eec009f960027e94005feb0027e30009f380017c38005fc60027db0009f6a00172c000a000002
private def correction32_4 (k : ℕ) : ℕ := if k < 34 then correction32_2 k else correction34_2 k
private def correction36_2 (k : ℕ) : ℕ := if k < 37 then 0x7ff8009fff0018000005ff80027fe4005ff90027fec005ff90027ff4005ffe0017ff800a0010017fe000a0000017fe8009ff90017ffc009ffb0018000005ff60027fec005fff0027fdc005ffa0017fec009ffb0027fe0009ffd0017fd4009ffe0027ff8009fff0017fe4005ffb0027fd8005ffd0017fdc009ff50017ff4005ff30027fdc005ffe0027fd0005ff60017fe8009ffa0027fcc005ff50027fd4005fff0017ff0009ffd0027fe4009ff60017fd0005fff0017fe0009ff30027fe8009ffa0027fec009ff30027fe8009fff0027fd0009ff50017fd0005ffc0017fec005fff0027ffc009fed0017fc4009ff90027fbc009feb0017fbc009ff80027fb8009ffc0017fbc009ff70027fcc005ff40017fc0009ff50027fb4009ffa0017f98005ffc0017f84009fe40017fbc009fe40017f7c009ffd0027fd4005ff80027f7c009fdd0017fc0005fde0027f80005fd70017fc8005fe80027f20009fdf0027f24009fd60017fa8005ffe0027f8c005fda0017e90005fcc0027ee4009f930017e8c009feb0027e24009f320027c1c009fc50027da0009f65002726800a000002 else 0x7ff8009ffe0028000009ff90017fe8005ff90017fe8009ff90017ff0009ffe0027ff400a0010017fdc009fff0027fe4009ff80027ffc009ffa0018000005ff60017fe8009fff0027fd8009ffa0017fec009ffb0027fe0009ffd0027fd4009ffd0027ffc005fff0027fdc009ffa0027fd4009ffd0017fdc005ff40027ff4009ff20027fdc005ffe0017fcc009ff50017fec005ffa0017fc8005ff40017fd0009ffe0027ff0005ffd0027fe0009ff60027fcc005ffe0027fe0005ff30027fe8009ffa0027ff0009ff30017fe8005fff0027fcc009ff30027fcc009ffc0027fe8009fff0027ff8009fec0017fc0005ff90027fc0005fe90027fbc005ff70027fb8009ffb0027fb8009ff60027fcc005ff30027fc0005ff60017fb4009ffa0017f94005ffc0017f80009fe30027fbc005fe30017f78009ffd0017fd0005ff70027f78005fdb0027fc0005fdd0027f7c009fd60017fc8009fe80017f1c009fdf0017f20005fd50027fa0009fff0027f88009fd80027e88005fcb0017edc009f910017e84005feb0017e18009f2d0027c04005fc40017d94009f62002720c00a000002
private def correction38_2 (k : ℕ) : ℕ := if k < 39 then 0x7ff4009ffe0017ffc009ff80017fe0009ff80027fe4009ff80017fec009ffc0027ff400a0000027fdc009fff0017fe0009ff70027ff8009ff90027ffc005ff50027fe4009ffe0027fd8005ff90017fec009ffb0027fdc009ffc0027fd4005ffd0017ffc005fff0017fdc005ff90027fd4009ffc0017fd8009ff40027ff0005ff20017fd8009ffe0027fcc005ff40027fe8005ff90027fc4005ff30027fcc009ffe0017fec005ffc0027fdc009ff50027fc8009ffe0027fdc009ff30017fe4009ffa0017fe8009ff20017fe4005ffe0027fc8009ff30017fc8009ffc0017fe4009fff0027ff8005fea0027fbc009ff90017fb8009fe90017fb8005ff70017fb4005ffa0027fb4009ff60027fc4009ff20017fb8009ff50017fb0009ff90027f8c009ffb0017f80005fe20017fb8005fe10027f70009ffd0017fcc009ff70027f74005fda0017fb8009fdc0027f74009fd30027fc4005fe60017f14009fdd0027f14009fd30027f9c009ffe0027f88005fd70017e7c005fc90027ed4005f8d0017e74009fe90027e0c005f280017be4009fc10027d80009f5d00171b400a000001 else 0x7ff4019ffd0047ffc00dff70037fe000dff80027fe4009ff80027fec00dffc0037ff000e0000027fd8009fff0017fe4009ff70027ff8009ff90027ffc005ff50027fe4009fff0017fd8005ff90017fe8009ffa0027fdc009ffc0027fd0009ffd0027ff8009fff0027fdc005ffa0027fd0009ffc0017fd8005ff30027fec009ff00027fd4009ffd0027fc8009ff40027fe4009ff90017fc0009ff30027fcc005ffd0027fec009ffc0027fdc009ff50017fc8005ffe0017fdc009ff20027fe8005ff90027fec005ff20027fe4009ffe0027fc8009ff30027fc8009ffb0027fe4009fff0027ff8009fea0027fbc009ff80027fb8005fe80017fb8005ff60027fb0009ffa0027fb4005ff60027fc4005ff20017fb4009ff40017fac009ff90027f88009ffb0027f7c009fe10017fb8005fe10017f70005ffc0027fc8009ff70027f70009fd90027fb8005fda0027f70009fd30027fc0009fe60017f10009fdc0017f10009fd20027f9c009ffe0017f80009fd50027e74009fc80027ecc009f8a0027e6c005fe90027dfc005f220027bcc009fc00017d70009f59002715c006000001
private def correction36_4 (k : ℕ) : ℕ := if k < 38 then correction36_2 k else correction38_2 k
private def correction32_8 (k : ℕ) : ℕ := if k < 36 then correction32_4 k else correction36_4 k
private def correction40_2 (k : ℕ) : ℕ := if k < 41 then 0x7ff4009ffe0028000005ff70027fe0009ff80017fe8005ff80027ff0005ffd0027ff000a0000017fd8009fff0017fe4009ff70027ff8009ff90017ffc009ff50017fe4005fff0017fd4009ff90017fec009ffb0017fdc009ffc0027fd0009ffd0027ff8009fff0027fdc005ffa0017fd0009ffc0027fd8005ff30017fec009ff00027fd4009ffe0017fc8009ff40017fe8009ff80027fc0005ff30027fc8009ffe0017fec009ffc0027fdc005ff50017fc4009ffe0027fd8009ff20027fe4009ff90027fec005ff20017fe4009ffe0027fc8009ff20027fc8005ffb0017fe4009fff0027ff8005fe90027fb8009ff80027fb4009fe70027fb4009ff60027fac009ff90027fb0009ff50027fc0009ff10027fb4009ff40027fac009ff80027f88009ffb0027f7c005fe00017fb4009fe00017f6c005ffd0017fc8009ff60027f6c009fd80027fb8009fda0027f6c009fd20017fc0009fe40027f0c009fdb0027f0c005fd20017f9800dffe0017f7c00dfd40027e6400dfc60027ec8009f870037e60009fe80027df0009f1c0037bb000dfbe0027d6000df5300470f001a000001 else 0x7ff4009ffd0027ffc009ff80017fe0009ff80027fe4009ff80027fec009ffc0027ff40060000027fd8009fff0027fe4005ff70027ff8005ff90017ffc009ff50017fe4009fff0017fd4009ff90017fec005ffa0017fdc005ffc0027fd0009ffd0027ff8009fff0027fd8009ffa0017fd0005ffc0027fd4009ff30017ff0005ff00027fd8005ffd0027fc8005ff30027fe8005ff90017fbc009ff30027fcc005ffe0017fec005ffc0027fd8009ff40027fc4009ffe0017fd8009ff20017fe4009ff90027fe8005ff10017fe0009fff0017fc8005ff20027fc4009ffb0027fe4005fff0027ff4009fe90027fb8005ff80017fb8005fe70027fb4009ff60017fac009ff90027fb0009ff50027fc0009ff20017fb4009ff40017fac005ff90027f84009ffb0017f74009fe00017fb4005fdf0027f68009ffc0027fc8009ff60027f68009fd70027fb8005fd90027f6c009fd10027fc0005fe40027f08005fda0027f08009fd00017f98005ffe0017f7c009fd30027e5c009fc50027ec0009f850027e58009fe80027de8005f180017b9c005fbd0017d54009f5100270a800a000002
private def correction42_2 (k : ℕ) : ℕ := if k < 43 then 0x7ff4009ffe0017ffc009ff70017fe0005ff70027fe8005ff70027fec009ffd0017ff40060000017fd8005ffe0027fe4005ff60027ff8009ff80027ffc005ff50027fe4009fff0017fd0009ff80027fec005ffa0027fd8005ffc0017fd0009ffc0027ff8009fff0027fd8005ff90027fcc009ffb0027fd4009ff30017ff0005ff00017fd4009ffd0027fc4009ff30027fe4005ff80017fbc005ff30017fc8005ffd0027fe8009ffb0027fd8009ff40027fc0009ffd0027fd8009ff10017fe4009ff80027fe8009ff00027fe0009fff0017fc4009ff10027fc4009ffb0017fe4009fff0027ff4009fe80027fb8005ff70027fb0009fe60027fb0009ff50027fa8009ff90027fb0009ff40027fc0009ff10027fb4009ff30027fa8005ff80027f84009ffa0017f70009fdf0027fb0005fde0027f64009ffc0017fc8005ff60027f64009fd60027fb4005fd80027f68009fd00017fbc005fe40017efc009fd90017f00009fcf0027f94009ffe0017f78005fd20027e54009fc40027eb8005f820017e50009fe70017dd8005f130017b80009fbc0017d44009f4d002705000a000001 else 0x7ff400dffd0027ffc009ff70027fdc009ff60027fe4009ff70017fec009ffc0027ff00060000017fd400dffe0027fe0009ff60027ff8005ff90017ff8009ff40027fe4005ffe0027fd0009ff80017fe8009ffa0027fd8009ffc0017fcc009ffd0017ff4009ffe0027fd8005ff90027fcc009ffc0027fd4009ff20017fec005fef0027fd4005ffe0017fc0009ff30027fe4009ff80017fbc005ff20017fc8009ffe0017fe8009ffb0027fd8009ff30017fc0009ffd0027fd4009ff00027fe0009ff80027fe4009ff00027fe0009ffe0027fc0009ff10017fc4005ffa0027fe0009fff0017ff4009fe80017fb4005ff70027fb0009fe60017fb0009ff50027fa8009ffa0017fac009ff50017fc0005ff00027fb0009ff30027fa4009ff80027f7c009ffa0027f6c009fdd0027fb0005fdd0027f60009ffb0027fc4009ff50027f64005fd60017fb0005fd70027f64009fce0027fbc009fe30027ef8005fd80027efc009fce0017f90009ffd0027f74009fd20017e4c009fc20027eb0009f7f0027e44009fe70017dcc005f0d0027b64009fba0017d34009f490026ffc006000001
private def correction40_4 (k : ℕ) : ℕ := if k < 42 then correction40_2 k else correction42_2 k
private def correction44_2 (k : ℕ) : ℕ := if k < 45 then 0x7ff0009ffe0017ffc009ff60027fdc009ff70027fe0009ff70027fec005ffc0027ff0009fff0027fd4005ffe0017fe0005ff60027ff8009ff90027ffc005ff40027fe4005ffe0027fd0009ff80017fe8009ff90027fd4009ffc0017fcc005ffd0017ff8005fff0027fd8005ff80027fc8009ffc0017fd0009ff20027fec009fef0027fd4009ffd0027fc4005ff20027fe4005ff70027fbc005ff20017fc8005ffd0027fec005ffb0017fdc005ff40017fbc009ffd0027fd4009ff00027fe4009ff90017fe8005fef0027fe0009fff0017fc0009ff10027fc4005ffa0027fe0009fff0027ff8005fe70027fb4009ff70027fb0005fe50017fac005ff50027fa4009ffa0017fac005ff40027fbc005ff00027fb0009ff30027fa4009ff80027f7c005ffa0017f68009fdd0027fac005fdd0027f5c009ffb0027fc4009ff50027f5c009fd50027fb0005fd60017f60009fcd0027fb8009fe20027ef4005fd80017ef4009fcd0027f90005ffd0027f74005fd10027e44005fc10027ea8009f7c0027e3c009fe60027dc0005f080027b50009fb80027d24009f450026fa000e000002 else 0x7ff4009ffd0027ffc009ff60027fe0005ff60027fe4005ff60027fec009ffd0017ff400a0000017fd4009ffe0027fe0005ff60027ff8009ff80027ffc009ff40027fe0009ffe0027fd4005ff80027fec009ffa0017fd4009ffd0017fcc009ffd0017ff8009fff0027fd8009ff90027fc8009ffc0017fd4009ff20027fec005fef0027fd0009ffe0027fc4009ff30027fe4009ff80027fb8009ff10027fc4009ffd0027fe8009ffc0017fd8009ff30027fc0005ffd0027fd8009ff10017fe4009ff80027fe8005ff00017fe0009fff0017fc0009ff10027fc4009ffb0017fe4005fff0027ff8005fe70027fb4009ff80017fac009fe50017fac009ff50027fa8005ff90027fa8009ff40027fbc009ff00027fb0005ff20027fa4009ff80027f7c005ffb0017f68009fdd0027fac009fdd0017f5c005ffc0017fc4009ff60017f60005fd40027fb0009fd60017f60009fcd0017fb8009fe20027ef0005fd70027ef0009fcc0027f8c009ffe0027f74005fd00027e3c009fc10017ea4005f7a0017e34009fe60027db4009f040027b3c005fb70027d18005f420016f5000a000002
private def correction46_2 (k : ℕ) : ℕ := if k < 47 then 0x7ff4009ffd0027ffc009ff70017fdc005ff60027fe4009ff70027fe8009ffd0017ff000a0000027fd4009fff0027fdc009ff60027ff8005ff90017ff8009ff40027fe0009ffe0027fcc009ff70027fe8009ffa0027fd8005ffc0017fcc009ffc0027ff8009fff0017fd8005ff90017fc8009ffc0027fd0009ff20017fec009fee0027fd0009ffe0017fc0009ff20017fe0009ff80027fb8005ff10027fc4009ffd0017fec005ffb0027fd8009ff30017fbc009ffd0027fd4009ff00027fe4005ff80027fe4009fef0027fe0009ffe0027fc0009ff00027fc0009ffa0027fe0009fff0027ff4009fe60027fb0009ff70017fac005fe40027fac009ff40027fa4009ff90027fa8009ff30027fb8009ff00027fac009ff20017fa0009ff80027f78009ff90027f64009fdc0027fa8009fdb0027f54009ffc0027fc4009ff50027f58009fd30027fac009fd50017f5c009fcc0027fb4009fe10027eec005fd60027eec009fcb0027f8c009ffe0017f70009fcf0017e30009fbf0027e9c005f770027e28009fe50027da8009efe0027b20009fb60027d08009f3e0026efc00a000002 else 0x7fe4061ffd00d7fdc045ff60077fd8019ff50057fd4021ff60047fe4015ff90077fe401a0000037fcc00dffc0037fd8015ff50037ff400dff70037ff4015ff20047fdc011ffc0047fcc00dff70027fe8009ff80047fd000dffb0027fc400dffc0037ff0009ffe0027fd000dff80027fc400dffb0027fcc00dff10027fec009fed0027fcc009ffc0027fbc00dff10027fe0009ff70027fb4009ff10027fc000dffc0037fe8009ffa0027fd000dff20027fb800dffc0027fd4009fef0027fe0005ff70027fe4009fee0027fdc009ffe0027fb800dfef0027fbc009ffa0017fdc009ffe0027ff8005fe60027fac009ff60037fa400dfe30027fa8009ff40027fa0009ff80027fa8005ff30027fb8009fef0027fa8005ff10027f9c009ff70027f74009ff90027f60009fdb0027fa400dfdb0027f54009ffb0027fbc009ff50017f54009fd20027fac005fd30027f5400dfca0027fb4005fe00027ee4009fd50027ee4009fca0017f88009ffd0027f68009fcd0027e28009fbd0027e94009f740027e20009fe40027da0005ef90027b08005fb40027cf8009f3a0026ea800a000002
private def correction44_4 (k : ℕ) : ℕ := if k < 46 then correction44_2 k else correction46_2 k
private def correction40_8 (k : ℕ) : ℕ := if k < 44 then correction40_4 k else correction44_4 k
private def correction32_16 (k : ℕ) : ℕ := if k < 40 then correction32_8 k else correction40_8 k
private def correction48_2 (k : ℕ) : ℕ := if k < 49 then 0x7ff4009ffd0027ffc009ff60027fd8009ff60027fe0009ff60027fe8009ffb0027ff00060000027fd0009ffe0027fdc009ff50027ff4009ff80027ffc005ff30027fdc009ffe0017fcc009ff70017fe8009ffa0017fd0009ffc0027fc400dffb0027ff4009ffe0027fd000dff80027fc4009ffb0027fcc00dff00037fec005fed0027fcc009ffd0027fbc009ff10027fe0009ff70027fb4009ff00027fc0009ffc0027fe8005ffb0017fd400dff20027fb8009ffd0017fd4009fee0037fe0009ff80027fe4009fee0027fdc009ffe0027fb8009fef0037fbc009ff90027fe0009ffe0027ff4009fe50027fa800dff60037fa800dfe20027fa8005ff40027f9c00dff80027fa000dff30027fb4009fef0027fa8009ff20027f9c009ff80027f70009ff90027f5c00dfda0027fa4009fda0037f5000dffb0037fc0009ff30047f50009fd10037fa4011fd20037f5000dfc90037fb0009fdf0037ed8011fd40047ed8015fc80037f8400dffd0037f60011fcd0037e1c00dfba0047e88019f700067e10011fe20047d88021ef20057ae0019fae0087ccc041f2c00d6e08062000002 else 0x7ff4009ffd0027ffc009ff50027fd8009ff60027fe0009ff60017fe8009ffc0027ff0005fff0027fd0009ffe0017fdc009ff50027ff8009ff80017ff8009ff30027fe0005ffd0027fc8009ff70027fe4009ff90027fd4009ffc0027fc4009ffc0027ff8005fff0017fd0009ff80027fc4009ffb0027fd0005ff00027fe8009fed0027fcc009ffe0017fbc009ff10027fdc009ff70017fb4005ff00017fc0009ffd0027fe8009ffa0027fd4009ff20017fb8005ffc0027fd0009fee0027fdc009ff80027fe4009fee0027fdc009ffe0027fbc009fef0027fbc005ff90027fe0009ffe0027ff4009fe40027fac009ff60027fa4009fe20027fa4005ff40017f9c009ff80027fa0009ff20027fb4009fef0027fa8005ff10027f9c005ff70027f70005ff90027f5c009fda0027fa4009fd90027f4c009ffc0017fbc009ff40027f4c009fd00027fa8009fd20027f50009fc80027fb4009fdf0027ed8009fd30027edc005fc70027f84005ffd0027f64009fcc0027e14009fbb0027e88009f6f0027e0c009fe30027d84009eef0027ad4009fb10027cdc009f320036e0000a000002
private def correction50_2 (k : ℕ) : ℕ := if k < 51 then 0x7fec009ffd0027ff8009ff50027fd8009ff50027fdc009ff60017fe4009ffc0027ff0005fff0027fcc009ffd0027fd8009ff40027ff4005ff70027ff8009ff20027fdc005ffd0027fc8005ff70027fe4009ff80027fd0009ffb0027fc4009ffb0027ff0009ffd0027fd0009ff80027fc4005ffb0027fcc005ff00027fe8009fec0027fcc005ffc0027fb8005ff10017fdc009ff70027fac009fef0027fbc009ffc0027fe4009ffa0027fd0009ff10027fb4009ffc0027fcc009fee0027fe0009ff70027fe0009fed0027fd8009ffe0017fb8009fef0017fb8009ff90027fdc009ffe0017ff4005fe30027fa4009ff60027fa4009fe10027fa0005ff30027f98009ff80017f9c009ff20017fb4009fed0027fa0009ff00027f98009ff70027f6c009ff80027f5c005fd90017fa0009fd90017f48009ffb0027fbc009ff40027f48005fcf0027fa4009fd00027f4c009fc70027fac009fde0027ed0009fd30017ed4009fc70027f80009ffd0027f60009fca0027e0c005fb90027e80009f6c0027e04009fe20027d78009eea0027abc009fb00027ccc009f2f0026dac00e000001 else 0x7ff000dffd0037ffc009ff50027fd8009ff60027fe0009ff50037fe8005ffb0027ff000a0000027fd0009ffe0027fd8009ff50027ff4009ff80017ffc005ff20027fe0005ffe0017fc8009ff70027fe4009ff90027fd0009ffb0027fc4009ffc0017ff8005ffe0027fd4005ff70027fc4009ffb0027fcc009ff00027fe8009fed0027fcc009ffd0027fbc009ff10027fe0009ff60027fb0005fef0027fbc009ffd0027fe8009ffb0017fd4009ff10027fb4009ffc0027fd0009fee0027fdc009ff70027fe4009fee0017fdc009ffe0027fb8005fee0027fbc009ffa0017fe0005fff0027ff4009fe30027fa8009ff60027fa4009fe10017fa0009ff40027f9c009ff80027fa0005ff30027fb4009fef0017fa0009ff10027f98009ff70017f68009ff90027f58009fd80027fa4005fd80027f48009ffb0027fbc009ff30027f48009fcf0027fa4009fd10027f48009fc60027fb0005fde0027ed0005fd20027ed0009fc60017f84005ffd0027f5c009fca0027e04009fb80027e78009f6a0017e00005fe30017d74005ee60027aa8009fae0027cc0009f2c0026d5c00a000002
private def correction48_4 (k : ℕ) : ℕ := if k < 50 then correction48_2 k else correction50_2 k
private def correction52_2 (k : ℕ) : ℕ := if k < 53 then 0x7ff4009ffe0017ffc009ff50027fdc005ff60017fe0009ff60027fe8009ffc0027ff000a0000027fd0005ffe0027fdc009ff50017ff8009ff80017ffc005ff30017fdc009ffe0027fc8009ff70027fe8009ff90027fd0009ffc0027fc4009ffc0027ff4009ffe0027fd0009ff80027fc4005ffb0027fd0005ff00027fec005fed0027fcc009ffd0027fbc009ff10027fe0005ff70027fac009ff00027fc0009ffd0027fe8009ffb0027fd4009ff20027fb4009ffd0027fd0009fee0027fe0009ff80027fe4009fed0027fdc009ffe0027fb8009fef0017fbc009ffa0017fe0005ffe0027ff4009fe40027fa8009ff60027fa4005fe10027fa4009ff30027f9c005ff80027fa0005ff30017fb4009fee0027fa4009ff10027f94009ff70027f68009ff90027f54009fd80027fa0009fd80027f44005ffc0017fbc009ff40027f48009fce0027fa4009fd00027f48009fc60027fb0009fde0027ecc009fd20027ed0005fc50027f7c009ffd0027f5c009fca0027e00005fb70027e74009f680027df8009fe20027d64009ee10027a94009fad0027cb4009f280026d0800e000002 else 0x7ff0009ffd0027ff8009ff50027fd8005ff50017fdc009ff50017fe8005ffb0027fec00a0000027fcc009ffd0027fd8009ff40027ff4009ff70027ff8009ff10027fdc005ffe0027fc8005ff60027fe4009ff90017fd0009ffb0027fc4005ffb0027ff4009ffe0027fcc009ff80027fc0009ffb0017fc8009fef0027fe8009feb0027fc8009ffc0027fb8005ff00027fe0005ff60027fac009fee0027fbc009ffc0027fe4009ffa0027fd0009ff00027fb4005ffc0027fd0009fee0027fdc009ff70027fe0009fec0027fd8009ffe0027fb4009fee0027fb4009ff90027fdc009ffe0027ff0009fe20027fa4009ff50027fa0009fdf0027f9c009ff20027f94005ff80017f98009ff20027fb0009fee0017f9c009ff00027f94009ff60027f64005ff90017f50009fd70017fa0005fd60027f40009ffb0017fb8005ff30027f40009fcd0027fa0009fce0027f44009fc50017fac005fdc0027ec4005fd00027ec8005fc40027f7c009ffd0017f58005fc80027df0009fb60027e6c009f650027de8009fe10027d58009edd0017a78009fab0027ca4009f240026cbc00a000002
private def correction54_2 (k : ℕ) : ℕ := if k < 55 then 0x7ff0009ffc0027ff8009ff40027fd4009ff40017fd8009ff40027fe4005ffa0027fec005fff0027fc8009ffd0017fd8009ff30027ff4009ff60027ff8009ff00027fd8009ffd0027fc4005ff60017fe0009ff80027fcc009ffa0027fc0009ffa0027ff4009ffd0027fcc005ff70017fc0005ff90027fc8005fef0017fe4009feb0027fc8009ffc0027fb4009ff00027fdc009ff50027fa8009fee0027fb8009ffc0027fe0009ffa0027fd0005fef0027fac009ffc0027fc8009fed0017fdc009ff60027fdc009fec0027fd8009ffd0027fb0009fee0027fb4009ff90027fdc009ffe0027ff4009fe20017fa0009ff40027f9c005fde0027f9c005ff20027f90009ff70027f98009ff00037fac009fec0027f9c009fef0027f8c009ff60027f60009ff80027f4c009fd60027f98009fd50027f3c009ffa0027fb4009ff30017f38009fcb0027f9c009fcd0027f40009fc30027fa8009fdc0027ebc009fcf0027ec0009fc20037f78009ffc0027f5400dfc60027de8009fb40027e60009f620027de0005fe00027d4c009ed70027a60009fa90027c94009f200026c6c00a000001 else 0x7fec025ffc0057ff8011ff50037fd4011ff50037fdc009ff40037fe8009ffb0037fec00dfff0037fc800dffd0027fd800dff40027ff400dff60037ffc009ff20027fdc009ffd0037fc4009ff60037fe4009ff80037fcc009ffb0027fc0009ffc0027ff4009ffe0027fd0009ff70027fc000dffb0027fc8009fee0037fe8009feb0027fc8009ffd0027fb4009fef0027fdc009ff60027fac009fee0027fb8009ffd0027fe4009ffb0027fcc00dff00027fb0009ffc0027fcc00dfed0027fe0009ff60027fe0009fec0027fd8005ffe0027fb4009fed0027fb4009ff90027fdc009fff0027ff4009fe10037fa0009ff50027f9c009fde0027f98009ff30027f90009ff80027f9c009ff10027fac009fed0027f9c005fef0027f8c009ff60027f60009ff80037f4c009fd60027f9c005fd50037f38009ffa0027fb800dff30027f3800dfcc0027f9c009fcd0027f40009fc20027fa8009fdc0027ebc009fcf0017ec0005fc20027f78009ffd0027f54009fc60027de4005fb40027e60009f600027ddc005fe00027d44009ed30027a50005fa90027c88005f1d0026c2000a000002
private def correction52_4 (k : ℕ) : ℕ := if k < 54 then correction52_2 k else correction54_2 k
private def correction48_8 (k : ℕ) : ℕ := if k < 52 then correction48_4 k else correction52_4 k
private def correction56_2 (k : ℕ) : ℕ := if k < 57 then 0x7fec009ffc0027ff400dff30027fd0009ff40027fd8009ff40027fe4009ffb0027fec009fff0027fc8009ffc0037fd8005ff30027ff4009ff60027ff8009ff00027fd4009ffd0017fc0009ff50027fe0009ff70027fc800dffb0027fbc009ffa0037ff0009ffd0027fc8009ff60037fb8009ff90027fc4009fee0027fe4009feb0017fc4009ffc0027fb4005fef0027fd8009ff50027fa4009fed0037fb4009ffb0027fe0009ffa0027fcc005ff00017fa8009ffb0027fcc009fec0027fd800dff50037fdc00dfeb0027fd4009ffd0027fac00dfed0027fb000dff80027fd800dffd0027ff0009fe00027f9c009ff40027f94009fdd0027f98009ff20027f8c009ff60027f94009ff00037fa8009fec0027f98005fee0027f8c009ff50027f5800dff80027f44009fd40027f94009fd30027f34009ffa0027fb4009ff20027f34009fca0027f98009fcc0027f38009fc10027fa4009fda0027eb0009fcd0027eb4009fc00027f6c00dffc0027f4c00dfc40027dd8009fb20027e5400df5c0047dcc00dfdf0037d38009ecd0037a2c015fa60037c70011f170056bb4026000002 else 0x7ff0009ffd0027ff8009ff40037fd4009ff40027fd8009ff40037fe8009ffb0027fec00e0000027fc8009ffd0027fd8009ff40027ff4009ff60027ffc009ff10037fdc009ffd0037fc4009ff50037fe4009ff80027fcc009ffc0027fc0009ffb0027ff4009ffe0027fcc009ff70027fc0009ffa0027fc400dfef0017fe8005fea0027fc400dffd0027fb4009fef0027fd800dff60017fa8009fee0027fb8009ffc0027fe4009ffb0027fcc009ff00017fb0009ffc0037fcc009fed0027fdc009ff60027fe0009fec0027fd400dffe0027fb0009fed0037fb0009ff90027fdc009ffe0027ff4009fe00037fa0009ff50027f98009fde0027f98009ff20027f8c009ff80027f98005ff10027fac009fed0027f98009fef0027f8c009ff60027f5800dff90017f44009fd50027f9400dfd40027f34009ffb0027fb4009ff30027f38009fca0027f9c009fcc0027f3c009fc10027fa4009fdb0027eb0009fce0017eb0009fc00017f74009ffd0027f50009fc50027dd0009fb20027e54009f5b0027dc8009fdf0027d30009eca0027a2000dfa60027c6c009f170026b8400a000002
private def correction58_2 (k : ℕ) : ℕ := if k < 59 then 0x7ff0009ffc0027ff8009ff40027fd4009ff40027fdc00dff40027fe4009ffc0027fec00e0000027fcc009ffd0037fd400dff30037ff4009ff60027ffc009ff00037fd800dffd0037fc000dff60027fe4009ff90017fcc00dffb0027fbc009ffa0037ff400dffe0027fcc00dff80027fbc009ffb0027fc8009fee0037fe4009fea0027fc8009ffd0027fb0009fef0027fdc009ff60027fa400dfee0017fb8009ffc0037fe4009ffa0027fcc009ff00027fac009ffc0027fc800dfec0027fdc00dff60027fe4009feb0027fd8009ffe0027fb0009fed0027fb0009ff90027fdc009ffe0037ff000dfe00027fa0009ff50037f9800dfde0027f98005ff20037f90009ff70037f9400dff10027fac009fec0037f98009fef0027f8c00dff60027f58009ff80027f44009fd40027f98009fd30037f34009ffb0027fb4009ff30027f34009fc90027f9c009fcb0027f3400dfc00027fa400dfdb0027eac009fcd0027eac009fbf0037f70009ffd0037f4c009fc40037dc8009fb10017e4c009f580037dc4009fdf0027d24009ec50027a0c009fa50037c6000df130036b3800e000003 else 0x7fec011ffc0047ff800dff30037fd000dff30037fd800dff30037fe000dffb0037fec009fff0027fc400dffe0027fd8009ff30027ff400dff70027ff800dff00027fd8009ffd0027fbc00dff40037fe000dff70037fc8009ffa0027fb8009ffb0027ff4009ffe0027fc8009ff60037fbc009ffa0037fc4009fed0027fe8009fe90037fc400dffd0027fb000dfee0037fd8009ff50037fa0009fed0037fb000dffb0037fe4009ff90037fc8009fef0037fa8009ffb0037fc800dfeb0037fd8009ff60037fe0009feb0027fd4009ffd0037fac00dfed0027fac00dff80037fd8009ffe0027ff4009fdf0037f9c009ff50027f94009fdd0027f94009ff10027f8800dff70027f90009ff00027fa8009feb0027f9400dfee0037f8400dff50027f58009ff80027f3c00dfd30037f90009fd20037f30009ffa0027fb4009ff20037f30009fc80027f9800dfca0027f3400dfbe0037fa0009fda0037ea4009fcc0027ea400dfbe0027f6c009ffd0027f48009fc30027dc0009faf0027e48009f560037db800dfde0037d1c009ec100279f4009fa40027c54009f100026af000a000002
private def correction56_4 (k : ℕ) : ℕ := if k < 58 then correction56_2 k else correction58_2 k
private def correction60_2 (k : ℕ) : ℕ := if k < 61 then 0x7fe8011ffc0037ff8009ff30037fd4009ff30037fd800dff30037fe000dffb0037fe8011ffe0047fc400dffd0027fd8009ff30037ff4009ff60027ff8011ff00027fd8009ffd0037fbc00dff50037fe0009ff80037fcc009ff90047fb800dffa0037ff4009ffd0027fc8009ff60047fb800dffa0027fc4009fed0037fe400dfe90037fc0011ffc0047fac009fee0027fd8009ff50037fa400dfed0037fb4009ffc0027fe000dffa0027fc800dfef0037fa800dffb0037fc800dfeb0037fd8011ff60037fdc011feb0027fd400dffd0037fac00dfec0037fb0009ff80027fd800dffd0037ff4009fdf0047f9800dff40037f9000dfdb0037f9000dff10037f84011ff60037f94009ff10027fa4011feb0027f9000dfee0037f88009ff50037f5400dff70037f3c009fd20037f9000dfd20027f28009ffb0027fb000dff10047f2c009fc80027f9400dfc80037f3000dfbd0037fa4009fd90027ea0009fcb0027ea4009fbd0027f6800dffc0037f44009fc10047db8009fae0037e3c00df540037db000dfde0037d1000debd00279dc00dfa20037c4000df0c0036a9c012000002 else 0x7ff000dffd0037ff8015ff30047fd0015ff50027fdc00dff30047fe400dffb0047fec00dfff0047fc400dffe0037fd400dff30037ff4009ff40057ff8015ff00037fdc00dffc0037fc0011ff50057fdc015ff70047fc800dffb0037fb4015ffb0037ff000dffe0037fc800dff70037fbc00dffa0047fc8009fed0047fe400dfe80057fc800dffc0037fb0009fee0047fdc00dff50047fa0011fed0027fb400dffc0037fe400dffa0027fc8011fef0037fac00dffc0047fcc00dfec0037fdc00dff50057fdc011fea0047fd8009ffd0037fac00dfec0027fb000dff80037fd800dffe0027ff0011fde0037f9c00dff40047f9400dfdd0027f9400dff10047f8800dff70037f9000dff10027fac009feb0037f9400dfef0037f88009ff70027f54009ff70047f3c00dfd20037f90011fd20027f2800dffa0037fb0009ff20027f28011fc70027f9400dfc90037f2c011fbd0047fa400dfd80047e9c011fca0047ea000dfbd0027f6c00dffd0037f44011fc20027db4009fad0047e3c00df530027da8011fdd0047d04011eb800479cc009fa10047c3c009f090046a58012000003
private def correction62_2 (k : ℕ) : ℕ := if k < 63 then 0x7ff4011ffb0087ff4021ff10087fc8021ff10087fdc015ff30087fe0015ffa0057fec0160000047fc0021ffe0047fdc011ff20057ff8015ff40087ff401dff00057fd8011ffc0087fb8021ff50047fe001dff70057fc401dffb0047fb401dffb0047ff0011ffe0047fc401dff70047fb401dffa0047fc0011fee0047fe8011fe90047fc001dffb0077fac011fee0047fd8011ff40077fa4011fec0047fb8011ffd0047fe8011ff90077fd0011fee0067fac011ffd0037fcc00dfea0067fd8011ff60067fd801dfe80077fd40120000037fac019fec0047fac011ff80067fdc00dfff0047ff0019fde0067f9c011ff50057f9400dfdd0047f9400dff10067f8800dff60057f90011ff10037fa800dfeb0047f9800dfee0037f88011ff60047f54011ff90037f38011fd10057f9000dfd20037f28011ffb0037fb000dff20057f28015fc70037f90015fc90047f2c015fbd0037fa0015fda0037e98011fca0047ea000dfbc0057f6c00dffd0057f4800dfc10037dac011fad0037e34015f510037da400dfdd0047cfc011eb300579b4015fa00057c3000df070036a1800e000005 else 0x7df4739fcc0e87d544d5fe20757e6c2e9fc904e7f5c10dff303b7f5c0d5fe00307fa00adfde04e7f58121fe10447fbc081ff101e7f980ddfdf0357fec069fec0187fb405dff40167fa4055ff20147fc8051fe60257fb404dfeb0227fb8045ff80117fd0041ffe00f7fa003dff300f7f9403dff900f7fa4035feb00d7fe0035fe00197fb4031ff50177fac031fe40167fb8055ff300b7f9002dfed00b7fac029ffa00b7fd4029ff500a7fc8029fe70127f98029ff60097fc8029fec00a7fd4025ff10107fc8041fe50087fd4025ffc0097fa4021fea0087f9c03dff60087fc8021ffb0087ff0021fdd0087f80039ff20087f8801dfd600e7f7c039ff20077f70035ff200d7f8401dfef0077fa801dfe600d7f8c01dfed0077f74031ff100c7f4801dff300c7f34019fd20067f8c019fd00067f24019ffb0067fac019fee00b7f1802dfc60067f8402dfc90067f1c029fb900a7f98019fd50067e90015fc700a7e98019fb90057f60019ffb0067f38029fc00057d9c025fac0067e28025f4b00a7d98025fdb00a7cf0015eb000579a4011f9e0057c1c021f0200969c4026000005
private def correction60_4 (k : ℕ) : ℕ := if k < 62 then correction60_2 k else correction62_2 k
private def correction56_8 (k : ℕ) : ℕ := if k < 60 then correction56_4 k else correction60_4 k
private def correction48_16 (k : ℕ) : ℕ := if k < 56 then correction48_8 k else correction56_8 k
private def correction32_32 (k : ℕ) : ℕ := if k < 48 then correction32_16 k else correction48_16 k
private def correction0_64 (k : ℕ) : ℕ := if k < 32 then correction0_32 k else correction32_32 k
private def correction64_2 (k : ℕ) : ℕ := if k < 65 then 0x7fdc025ff80097fe4025ff30057fc8015ff00057fd4015fef0097fcc025ff70097fdc029ffc0067fb0025ffa0067fc0029ff10067ff0019ff50057ff0015fea00a7fcc019ffc0067fb8019ff000a7fcc02dff30067fb8029ff70067fa402dff600b7fe8019ffa0067fb401dff40067fac01dff50077fb401dfe900b7fdc01dfe400c7fa8035ffa0077fa001dfe800d7fc401dff20077f9401dfe700c7f98035ff70077fc8035ff300e7fc001dfeb0087f8c039ff70097fb0021fe90087fd0021ff20097fbc03dfe50087fc4025ff90097f90025feb0087f88045fef0117fc4025ff600a7fd8025fdc00a7f88025feb0137f7002dfd800a7f7c029feb00a7f6c029fee00b7f7802dfe900b7f74059fe10177f6c031fe10177f6c035fe80187f24039fef00e7f28039fc500f7f8403dfc800f7f1403dfed0107f9c041fe60117ee8045fb50237f68049fb60267efc051fad0147f70055fcd0167e6005dfb70197e40069f9f0357ef00ddfe301e7ee4081f9b0437cf4121f8004e7dd40b1f3902f7d540d5fa503b7c6410de8a04e78142e9f3c07579f04d5e4a0e8645073a000001 else 0x7fec00dffc0047ff800dff20057fc8019ff20057fd4015ff40047fe0011ffa0047fe4019fff0037fc0015ffe0037fd400dff10067ff400dff40067ff800dff00037fd800dffd0037fb8015ff50037fdc019ff70047fc0019ff90047fb4015ffa0057ff4011ffe0047fc400dff60047fb4011ff80067fc000dfec0047fe0011fe80037fbc011ffd0047fa800dfed0047fd800dff40047f9c011fea0067fb0011ffa0067fe000dff80047fc800dfec0067fa000dffa0067fc0019fea0047fd8011ff40067fdc011fe90047fcc019ffc0047fa4011fea0067fa4019ff50077fd8011ffc0067ff0011fdc0047f90011ff30067f8c011fd80077f88011ff10037f7c011ff60047f84011fed0077fa4011fea0047f90011feb0077f78019ff60047f48011ff60057f30015fcf0057f8401dfce0047f14021ffa0047fac011ff10047f1801dfc40047f84021fc50057f1c01dfb90057f94021fd40087e88015fc70057e84021fb70077f5c015ffd0057f34011fbd0047d88021fa80057e20015f490057d8c015fd90097cd8015ea60087974021f9a0087bf8025efa0096934012000005
private def correction66_2 (k : ℕ) : ℕ := if k < 67 then 0x7ff0011ffd0047ffc009ff20047fd000dff30047fd800dff30047fe0011ffb0037fec009fff0047fc400dffe0037fd0011ff20037ff800dff60037ffc009fef0047fd4011ffd0047fbc00dff40047fdc011ff80037fc800dffb0027fb4011ffb0037ff400dffd0047fc800dff70027fb4011ffa0037fc000dfec0047fe8009fe70037fc000dffd0027fac00dfee0027fd8009ff50027f9c009fec0037fb0009ffb0047fe000dff90037fcc009fed0047fa400dffc0037fc4015feb0037fdc00dff50037fdc00dfea0037fd400dffe0037fa800dfea0057fa8011ff80047fd8009ffe0037ff4009fdc0057f9400dff40037f8c015fd90037f8c00dff10037f8400dff60037f84015fee0047fa400dfea0047f9000dfee0037f8000dff50047f48011ff70047f3000dfce0057f8c00dfcf0037f18011ffa0037fb000dff20037f1c015fc30037f9000dfc50057f20011fb80057f98015fd70037e8400dfc70037e84015fb70057f6400dffc0037f3c00dfbd0037d90009fa80037e1c011f460057d8800dfdc0037cd8009ea3003795c015f9a0057bf8015efa00368f4012000005 else 0x7fec011ffc0037ff800dff20037fc800dff20027fd4009ff10037fdc009ff90047fe400dffe0047fc0009ffc0047fd0009ff10037ff000dff50027ff8009fee0027fd4009ffc0037fb800dff40037fdc00dff60037fc0011ff90027fb000dffa0037fec011ffd0037fc0009ff50027fac011ff80047fbc00dfea0047fdc011fe60037fbc009ffc0027fa400dfec0027fd000dff30037f9400dfea0047fa8011ffb0037fdc009ff80037fc400dfec0047f9c011ffa0037fc000dfe80047fd0011ff40037fdc009fe80037fcc011ffc0037fa0011fea0037fa0011ff60037fcc011ffd0037fec011fdb0047f9000dff20047f88009fd80027f88009fef0037f7c009ff50027f84009fee0037f9c00dfe90027f88009feb0047f78011ff30037f4000dff60037f2800dfce0027f88009fcc0047f14009ff90037fa8009ff00027f1400dfc10047f88009fc30037f1c00dfb70037f98009fd50027e80009fc50037e7c011fb70027f5c00dffb0037f34009fbc0027d8000dfa50037e10011f440027d7c009fda0037cc400de9e0027950009f990047be800def600268ac012000002
private def correction64_4 (k : ℕ) : ℕ := if k < 66 then correction64_2 k else correction66_2 k
private def correction68_2 (k : ℕ) : ℕ := if k < 69 then 0x7fe800dffc0027ff4009ff20027fcc00dff10027fd4009ff10047fdc00dffa0037fe800dfff0037fc000dffd0027fd0009ff00027ff4009ff50027ff400dfee0027fd4009ffc0037fb400dff30037fdc00dff60027fc000dffa0027fb000dff90037ff0009ffd0027fc0009ff50037fb4009ff80037fb8011feb0027fe0009fe60037fbc00dffc0037fa000dfec0027fd000dff40027f98009fea0037fa800dffb0027fe0009ff80037fc4009fed0027f9c009ffb0037fc4009fe90027fd4009ff40037fd8009fe70027fcc00dffc0047fa4009fea0027fa400dff70027fd4009ffd0037fec011fda0037f8c009ff30037f8800dfd80037f88009fef0037f7800dff50037f84009fed0047f9c009fe90027f84011fec0027f78009ff30037f40009ff60027f28009fcc0047f84009fcd0037f1000dff90027fa8009ff10027f18009fc10027f8800dfc20047f18011fb70027f94011fd50027e7c009fc50027e7c00dfb60027f5c009ffc0027f30009fbb0027d7800dfa50027e10009f410037d7400dfd90037cbc011e9a003793800df980037bdc011ef10056868016000002 else 0x7fec00dffc0037ff8009ff20037fc800dff20027fd8009ff20037fe000dffa0037fe800e0000027fc0009ffc0037fd4009ff10037ff000dff50037ffc009fee0027fd400dffc0037fb400dff40027fdc00dff60037fc4009ffa0027fb000dffb0027ff0009ffe0027fc4009ff60027fb4009ff90037fbc009feb0027fe0009fe70027fbc00dffc0037fa4009fec0037fd000dff40027f9800dfea0037fac009ffb0037fdc009ff90027fc400dfec0037fa0009ffc0027fc400dfe90027fd8009ff50027fdc009fe80027fd4009ffd0027fa4009fea0037fa8009ff80027fd400dffe0027ff000dfdb0037f8c00dff30027f88009fd80027f88009fef0037f7c009ff60017f8000dfef0027f9c00dfe90037f88009fec0027f7800dff50027f4000dff70027f2400dfcd0037f88009fcd0027f1000dff90037fa800dff00037f14009fc10037f8800dfc20027f1c009fb60037f9400dfd40037e7800dfc40037e7c00dfb60027f5c009ffc0037f3000dfbb0037d74009fa40037e0c00df400037d70009fda0027cb800de970027928009f980027bd8009ef1002682c00e000002
private def correction70_2 (k : ℕ) : ℕ := if k < 71 then 0x7fec00dffd0027ff8009ff20037fcc00dff20037fd400dff30027fe000dffa0027fe800dfff0027fc000dffd0027fd4005ff20027ff4009ff50027ffc005fef0027fd4009ffd0037fbc005ff40027fe0009ff70027fc000dffb0027fb000dffb0027ff000dffe0027fc4009ff60027fb400dffa0027fbc009fec0027fe000dfe70037fc0005ffc0037fa8009fec0027fd400dff40037f98009fea0037fac009ffb0037fe0009ff90027fc400dfee0017fa0009ffb0037fc4009fe90037fd8009ff50027fdc009fe80027fd0009ffe0027fa400dfea0027fa8009ff80027fd4009ffe0027ff0009fdb0037f8c009ff30027f8c009fd80027f8400dff00027f7c009ff50037f8400dfef0027f9c00dfe90027f88009fec0027f7800dff50027f40009ff70027f28009fcd0037f84009fcc0037f0c00dffa0027fa8009ff00037f14009fc00037f8c009fc30027f1400dfb50037f98009fd40037e7400dfc50037e7800dfb50037f5c009ffc0037f3000dfba0037d70009fa40027e0400df3e0027d68009fda0037cb000de93002791800df960037bcc00deee00367e800e000003 else 0x7fe8029ffb0067ff4011ff20047fc4019ff10037fcc00dff10047fdc00dff80047fe4011ffe0037fbc00dffd0027fcc011ff00037ff000dff40037ff800dfee0027fd0009ffd0027fb400dff30027fd800dff60037fc4009ff90037fac00dffa0027fec009ffd0037fc0009ff50027fb000dff90037fb800dfeb0027fe000dfe70027fbc009ffc0027fa4009feb0027fd4009ff30037f94009fe90037fa8009ffb0027fdc009ff80037fc400dfec0027f9c009ffb0027fc4009fe80027fd400dff40027fd8009fe60037fcc00dffc0037fa000dfe90027fa0009ff60037fd000dffe0027fec00dfdb0027f8c009ff30027f84009fd70027f8400dfef0037f7400dff50027f8000dfee0027f98009fe80027f84005feb0027f78009ff40027f3c009ff60027f20009fcb0037f80009fcb0027f0c009ff90027fa4009fef0037f0c009fbf0037f8400dfc10037f14009fb40027f94009fd30027e70009fc40027e70009fb30037f5400dffb0037f2c009fb90027d64009fa20037e04009f3c0027d60009fd90027ca8009e8f002790000df950027bbc00deea00367a800a000003
private def correction68_4 (k : ℕ) : ℕ := if k < 70 then correction68_2 k else correction70_2 k
private def correction64_8 (k : ℕ) : ℕ := if k < 68 then correction64_4 k else correction68_4 k
private def correction72_2 (k : ℕ) : ℕ := if k < 73 then 0x7fec009ffc0027ff8009ff20037fcc009ff20027fd4009ff20027fe0009ffb0017fe8009fff0027fc0009ffd0027fd0009ff10027ff4009ff50027ffc005fee0027fd000dffd0027fb8009ff40027fdc009ff60037fc4009ffa0027fb000dffa0037ff0009ffe0027fc0009ff50037fb4005ffa0027fb800dfeb0037fe0009fe70027fbc00dffc0037fa4009fec0027fd400dff40027f94009fea0027fa8009ffc0027fe0009ff90027fc4009fec0037f9c009ffc0027fc0009fe80037fd4009ff50027fdc009fe70027fd000dffe0027fa0009fea0027fa4009ff80027fd000dffe0027ff000dfdb0027f88009ff30027f8400dfd70027f8000dff00027f78009ff60027f84009fee0027f9c009fe80037f8400dfec0027f7400dff40027f3c009ff60037f2000dfcc0027f8000dfcb0027f0c009ff90037fa8009fef0037f0c00dfc00027f8400dfc00037f1000dfb30037f94009fd30037e6c00dfc30027e7000dfb30037f5400dffc0037f2c00dfb90037d5c00dfa10037dfc011f390047d5800dfd90037ca000de8b00478f0015f930047bb0011ee5006674c02a000003 else 0x7fe800dffc0027ff400dff20027fcc009ff10027fd0009ff10037fdc009ffa0027fe400dffe0037fb800dffd0027fcc00dff00027ff0009ff40037ff8005fed0027fd4005ffd0027fb4009ff30027fdc00dff60027fc0009ff90027fac00dff90027ff0009ffd0027fc0009ff50027fac009ff90027fb8009feb0017fdc009fe60027fb8009ffc0027fa0009feb0027fd0009ff30027f90009fe90037fa8009ffb0027fd8009ff90027fc4009fec0027f9c009ffb0017fbc009fe70037fd0009ff30037fd8009fe60037fc800dffd0027f9c009fe90017fa0009ff70027fd0009ffd0027fec00dfd90027f88009ff20037f84005fd60027f80009fee0037f74009ff40037f7c009fed0027f94009fe80027f80009feb0017f70009ff40017f3400dff60027f20009fcb0027f7c009fcb0017f08009ff90027fa000dfef0027f08009fbe0027f84009fc00027f10009fb20027f90009fd20037e68009fc20027e6c009fb20027f5000dffc0027f2400dfb80017d58009fa10027df4009f380027d50009fd80027c94009e8700278e0009f920037ba8009ee4003672800a000002
private def correction74_2 (k : ℕ) : ℕ := if k < 75 then 0x7fec009ffc0027ff8009ff10037fc8009ff10027fd4009ff10027fdc009ff90037fe8009fff0027fbc009ffd0027fd0009ff10027ff4009ff40027ff8009fee0027fd0009ffd0027fb4009ff30027fdc005ff60027fc0009ff90027fac009ffa0027ff0009ffe0027fc0009ff40037fb0005ff90027fb400dfea0037fe0009fe50027fb8009ffc0027fa0009fec0027fd0009ff30027f90009fea0017fa4009ffb0027fdc009ff90027fc000dfeb0037f9c009ffb0027fbc00dfe80027fd0009ff40027fd8009fe60027fcc009ffd0027fa0009fe80037fa0009ff60037fd4005ffd0027fec00dfd90037f8400dff20027f80009fd50037f80009fef0027f74009ff50027f7c00dfee0027f98009fe70027f80009feb0027f74009ff40027f3400dff60027f1c009fca0027f7c009fc90037f04009ff90027fa4009fef0027f08009fbd0027f84009fc00027f0c00dfb20027f90009fd20027e68005fc20027e68009fb20027f50009ffc0027f28005fb70037d54009f9f0037df000df360027d48009fd80017c8c00de8400278cc009f920027b9c009ee200366ec00a000002 else 0x7fe8011ffc0027ff400dff10027fc400dff00037fcc009ff10027fdc009ff90027fe4009fff0027fb8009ffc0027fcc009ff00027ff0009ff40027ff4009fec0037fd0009ffc0037fb0009ff20027fdc009ff60027fc0009ff80027fac009ff90027fec009ffc0037fc0005ff40037fac005ff80027fb8009fe90027fdc009fe50017fb8009ffb0027f9c009fea0027fd0009ff20027f90009fe80027fa4009ffa0037fd8009ff80027fc0009feb0037f98009ffa0037fbc009fe70027fcc00dff30027fd4009fe60017fc8009ffc0027f9800dfe70037f9c009ff60027fd0009ffc0027fec009fd80027f84009ff20027f7c009fd50027f7c009fee0037f6c009ff40027f78009fed0027f94009fe60027f7c009fea0037f70009ff30027f3000dff50027f18009fc90027f7c005fc80027efc009ff80027fa000dfee0027f04009fbc0027f80009fbf0027f08009fb10027f90009fd20027e5c009fc10027e64005fb00027f4c009ffb0027f24009fb60027d4c005f9e0027de800df330027d3c00dfd60037c80009e7f00378b8009f900027b9000dedf00266ac00a000002
private def correction72_4 (k : ℕ) : ℕ := if k < 74 then correction72_2 k else correction74_2 k
private def correction76_2 (k : ℕ) : ℕ := if k < 77 then 0x7fec009ffc0027ff8009ff10027fc8009ff10017fd0009ff10037fdc009ff90037fe4009fff0027fbc009ffd0027fcc00dff00027ff0005ff40027ff8009fec0037fd0005ffc0027fb4009ff20027fdc009ff60027fc0009ff90027fac009ffa0017fec00dffd0027fbc009ff50017fac009ff80027fb4009fea0027fdc009fe50027fb8009ffc0027f9c009fea0027fd0009ff30027f8c009fe80027fa4009ffa0037fd8009ff90017fc0009feb0027f98009ffa0027fbc00dfe70027fd4005ff30037fd8009fe50027fc8009ffd0027f98009fe80027f9800dff70027fd0009ffd0027fec009fd80027f84009ff10037f7c009fd50027f7c009fee0027f70009ff50027f7c005fec0037f9400dfe70027f7c009fea0037f70009ff30027f30009ff50027f1400dfc90027f7c009fc80027efc009ff80027fa0009fef0027f00009fbc0027f80009fbe0027f08009fb00037f8c009fd10027e5c009fc00037e60005fb00027f4c009ffc0027f20009fb60027d44009f9d0027de8009f310037d3c009fd60037c7c009e7d00278a800df8f0037b8400dedc003666c012000002 else 0x7fec009ffc0037ff4009ff10027fcc009ff00037fd4009ff20027fdc00dffa0037fe400dfff0037fbc009ffd0027fcc009ff00027ff0009ff40027ff800dfed0027fd0009ffd0027fb0009ff30027fdc009ff60027fc0009ff90027fac009ffa0027fec00dffd0027fc0005ff50027fac00dff80027fb8009fea0017fdc009fe50027fb8009ffc0027f9c00dfea0037fd0009ff30027f90009fe90027fa4009ffb0027fdc009ff80037fc0009feb0027f98009ffb0037fc0009fe70027fd4009ff40027fd8009fe60017fcc005ffd0027f9c009fe90027f9c00dff60027fd0009ffd0037fec00dfd80027f84009ff20027f80009fd50027f7c009fee0037f70009ff50027f7c005fed0027f94009fe70027f80005feb0027f70009ff30027f34005ff60027f18009fc90027f7c009fc80027efc009ff80037fa0009fef0027f00009fbb0027f84009fbd0027f08009fb00027f90009fd20027e5c005fc00037e5c009faf0037f4c009ffc0027f24009fb50037d40009f9d0027de4009f300027d38009fd70027c78009e7a0027898009f8f0027b7c00deda003663800a000002
private def correction78_2 (k : ℕ) : ℕ := if k < 79 then 0x7fe400dffb0027ff4005ff00027fc4009fef0027fcc009ff00027fd8009ff80027fe000dffe0027fb400dffb0037fc8009fef0027fec009ff20037ff4009feb0037fcc009ffb0027fa800dff10027fd8009ff50027fb8009ff80027fa8009ff80027fe800dffb0037fb8009ff30027fa400dff70037fb0009fe90017fd8009fe30027fb0009ffa0027f98009fe90027fc8009ff10037f88009fe70027f9c00dffa0027fd8009ff70027fb8009fea0027f94009ff90027fb400dfe60017fcc009ff20027fd0009fe40027fc4009ffc0027f98009fe70027f9400dff60027fcc009ffd0027fec009fd70027f7c009ff00027f78009fd30027f78009fed0037f68009ff40027f74009fec0027f8c009fe60027f78009fe90027f68009ff20027f28009ff40027f10005fc70027f74009fc60037ef400dff80017f9c009fed0037ef8009fba0027f7800dfbc0037f00009fae0037f88009fd00027e50009fbe0037e54009fad0027f48009ffa0027f18009fb30027d34009f9b0027dd8009f2e0027d2c009fd50027c68009e740027884009f8d0027b70009ed700265f800a000001 else 0x7fd0091ffb0137fc8065fef00a7fc0025fee0087fbc02dff00067fd8015ff60097fd4021ffe0057fb0011ffa0037fc001dfee0047fe8011ff20047fec019fea0057fc4015ffa0057fac00dff10037fd4011ff40047fb4011ff70037fa800dff80047fe800dffc0027fb4011ff30047fa400dff70037fb000dfe80027fd800dfe30037fb4009ffb0027f9400dfe90037fc800dff20037f8800dfe80027f9c011ff90037fd8009ff70027fb800dfe90037f9000dff90037fbc009fe60027fcc00dff20037fd000dfe40037fc8009ffc0037f9400dfe70027f98009ff50037fcc009ffc0037fe800dfd70027f7c00dff10027f7400dfd20037f78009fed0037f6800dff30037f74009feb0027f90009fe60027f78009fe90027f6c009ff20037f2c009ff40037f0c00dfc70027f7400dfc70037ef400dff70037f9c00dfed0037ef400dfb90027f7800dfbb0037efc00dfae0027f88009fcf0037e4c009fbe0027e54005fad0027f48009ffb0027f18009fb20037d30009f9a0027dd8009f2c0027d28009fd50027c60009e710027874009f8c0037b68009ed400365c400a000002
private def correction76_4 (k : ℕ) : ℕ := if k < 78 then correction76_2 k else correction78_2 k
private def correction72_8 (k : ℕ) : ℕ := if k < 76 then correction72_4 k else correction76_4 k
private def correction64_16 (k : ℕ) : ℕ := if k < 72 then correction64_8 k else correction72_8 k
private def correction80_2 (k : ℕ) : ℕ := if k < 81 then 0x7fe400dffb0027ff400dff00027fc4009fef0027fcc009ff00027fd8009ff90027fe4009ffe0037fb4009ffc0027fc8009fee0027fec009ff20037ff4009fec0027fcc009ffb0027fac009ff20027fd400dff50037fb8009ff80037fa4009ff90027fec009ffc0037fb8009ff30037fa400dff70037fb0009fe70037fd8009fe30037fb4009ffb0027f98005fe90027fc800dff20027f88009fe70027f9c00dffa0037fd8009ff70027fb800dfea0027f8c00dffa0027fb8009fe60027fcc00dff20027fd4009fe40027fc400dffb0037f9400dfe70027f98009ff50047fcc009ffd0027fe800dfd50037f7c00dff10027f7400dfd20047f74009fed0037f64011ff30037f7000dfeb0037f8c00dfe50037f78009fea0027f6400dff20037f2400dff40037f0800dfc70037f7400dfc50047eec011ff80037f9c00dfec0047ef0011fb80047f78011fba0057efc00dfac0037f8400dfce0057e44015fbc0057e44019fab0047f44011ffa0047f10019fb20047d28015f970057dc8021f260097d14019fd10067c48031e6b0087850025f8400a7b30061ec20136518092000001 else 0x7fec00dffc0027ff4009ff10027fc8009ff00017fd0009ff00037fdc009ffa0027fe4009ffe0037fb8009ffc0027fcc009ff00027ff0009ff40027ff8009fec0027fcc009ffc0027fb0009ff20027fd8009ff50027fc0005ff90027fa8009ff90027ff0009ffd0037fbc009ff50027fa8009ff90027fb4009fe90027fdc00dfe40027fb8005ffc0027f9c009fea0027fcc009ff20037f88009fe80027fa0009ffa0037fd8009ff80027fc0005fea0027f94009ffb0027fbc009fe60037fd0009ff30027fd4009fe50027fc8009ffc0037f98009fe70037f9c009ff60027fd0009ffd0027ff0005fd70027f8000dff20027f7800dfd20027f78009fee0027f68009ff40027f78009fec0027f90009fe60027f78009fea0027f6c009ff20027f2800dff60027f0c00dfc70027f78009fc60027ef4009ff80027fa0009fee0027ef4009fb90027f7c009fbb0027f00009fae0017f88009fcf0037e4c009fbe0027e4800dfad0027f48009ffb0037f18009fb30027d28009f990027dd0009f290027d1c00dfd50027c5400de6d0017858009f8c0017b58009ed1002655400a000003
private def correction82_2 (k : ℕ) : ℕ := if k < 83 then 0x7fe8009ffc0017ff4009ff00027fc4009fef0027fcc009ff00027fd8009ff90027fe4009fff0027fb8009ffc0027fc8009fef0027ff0009ff30027ff8009fec0027fcc009ffc0027fac009ff20027fd8009ff50027fbc009ff90027fa8009ff90027fec009ffd0027fb8009ff40027fa4009ff80027fb000dfe80027fd8009fe30027fb4009ffb0027f98005fea0017fd0009ff20027f88005fe70037f9c009ffa0027fd8009ff70027fbc009fe90037f90009ffa0027fb8009fe60027fcc009ff20027fd4009fe40027fc8009ffc0027f98009fe60037f98009ff60027fcc009ffd0027fec009fd60027f80009ff20027f78009fd10027f74009fed0027f68009ff30027f7000dfeb0027f90005fe60027f74009fe90027f68009ff20027f28005ff50027f0c009fc60027f74009fc50027ef0009ff80027f9c009fee0027ef4009fb80027f7c009fba0027efc009fac0027f88009fcf0027e44009fbd0027e48009fac0027f44009ffb0027f18005fb20027d20009f980027dc800df260027d14009fd40037c4c009e680037848009f890027b4c009ecd003651c00e000002 else 0x7fe800dffb0037ff400dfef0027fc0009fee0037fcc009fef0027fd400dff90027fe0009ffe0027fb4009ffb0037fc8009fee0027fec009ff30027ff000dfeb0027fcc009ffc0017fa8009ff10027fd8009ff50027fb8009ff90027fa4009ff80027fec009ffc0027fb8009ff30027fa4009ff70027fb0009fe70027fd8009fe20027fb000dffb0027f94009fe80027fc8009ff10027f84009fe70027f9c009ffa0027fd8009ff60027fb8009fe90027f8c009ffa0017fb8009fe50027fcc00dff20027fd0009fe30027fc8009ffc0027f94009fe50037f94009ff60017fc8009ffc0027fe8009fd50027f7c009ff10027f74009fd20027f74009fed0027f64009ff30027f70009feb0027f8800dfe50027f70009fe80027f60009ff20027f20009ff50027f08009fc50027f6c009fc40027eec009ff70027f9c009fed0027eec009fb70027f78009fb90027ef8009fab0027f84009fcd0027e40009fbc0027e44009faa0037f40009ffb0027f10009fb00027d18009f970027dc4009f250027d0c009fd30027c40009e650027838009f880027b40009eca00264e400e000002
private def correction80_4 (k : ℕ) : ℕ := if k < 82 then correction80_2 k else correction82_2 k
private def correction84_2 (k : ℕ) : ℕ := if k < 85 then 0x7fe8009ffc0027ff4009ff00027fc4009ff00027fcc009ff00027fdc009ff90027fe4009ffe0027fb4009ffc0027fcc009fef0027ff0009ff30027ff8009feb0027fcc009ffc0027fac009ff20027fd8009ff50027fb8009ff90027fa4009ff90027ff0009ffd0027fb8009ff40027fa4009ff80027fb0009fe80027fdc009fe30027fb4009ffc0027f98009fe90027fcc009ff20027f84009fe70027fa0005ffb0027fd8009ff70027fbc009fe90027f90009ffa0027fb8009fe60027fd0009ff30027fd4009fe40027fc8009ffd0027f98009fe70027f9400dff60027fcc009ffd0027fec009fd50037f7c009ff10027f74009fd10027f74009fed0027f64009ff40027f70009fec0027f8c00dfe60027f74009fe90027f68009ff20027f24009ff50027f08009fc50027f74009fc50027eec009ff80037f9c009fed0027eec00dfb70027f78009fba0027ef400dfab0037f8400dfce0027e40009fbc0027e44009fab0027f44009ffb0027f1000dfb00027d1400df970027dc4009f240027d0c009fd40027c40009e630027828009f870037b3c009ec800364ac016000002 else 0x7fe400dffa0037ff0009fef0027fc0009fef0027fcc009fef0027fd4009ff80027fe0009ffe0027fb0009ffc0027fc8009fed0037fec009ff20027ff0009fea0027fc8009ffb0027fa8009ff00027fd4009ff40027fb4009ff80027fa0009ff80027fe8009ffc0027fb4009ff30027fa0009ff70027fac009fe70027fd8009fe20027fb0009ffb0027f90009fe80027fc8009ff10027f80009fe60027f98009ff90027fd4009ff70027fb8009fe90027f8c009ffa0027fb4009fe50027fcc009ff10027fd0009fe30027fc4009ffb0027f90009fe60027f90009ff50037fcc009ffc0027fec009fd40027f74009ff00027f70009fd10027f6c009fed0027f60009ff30027f6c009fea0027f88009fe50027f70009fe80027f60009ff10027f1c009ff30027f04009fc40027f70009fc30027ee4009ff70027f98009fed0027eec009fb60027f74009fb80027ef4009faa0027f80009fcd0027e34009fbb0027e3c009fa90027f3c009ffa0027f10009faf0027d0c009f950027dbc009f220027d04009fd20037c34009e5f0027818009f860027b30009ec6002648000a000002
private def correction86_2 (k : ℕ) : ℕ := if k < 87 then 0x7fe400dffb0027ff4009ff00027fc4009fef0027fcc009ff00027fd8009ff90027fe0009fff0027fb4009ffc0027fc8009fef0027ff0009ff20027ff8009feb0027fcc009ffc0027fac009ff10027fd4009ff50027fb8009ff80027fa0009ff80027fe800dffc0027fb4009ff40027fa4009ff80027fb0009fe80027fd8009fe20027fb0009ffc0017f94009fe80027fcc009ff20027f84009fe70027f9c009ffa0027fd8009ff70027fb8009fe90027f8c009ffa0027fb8009fe50027fd0009ff20027fd4009fe30027fc4009ffc0027f94009fe60027f94009ff50027fc8009ffd0027fec009fd40027f7800dff10027f74009fd00027f70009fed0027f64009ff40027f6c009feb0027f8c009fe50027f70009fe80027f60009ff20027f20009ff40027f00009fc40027f70009fc40017ee8009ff80027f9c009fed0027eec009fb70017f74009fb90027ef4009faa0027f84009fcd0027e34009fbb0027e3c009fa90027f40009ffb0027f10009faf0027d08009f940027dbc009f200027d00009fd30027c30009e5c002780c009f860027b28009ec5002645000e000002 else 0x7fe802dffb0077ff0015fef0047fc0015fef0037fc800dfef0037fd400dff80037fe0011ffe0037fb0011ffc0037fc4011fee0037fec00dff20027ff8009feb0027fc800dffc0027fa800dff10027fd8009ff40047fb8009ff90027fa4009ff80037fe800dffd0027fb8009ff40027fa4009ff80027fac009fe70027fd800dfe20027fb0009ffb0027f94009fe90027fc800dff10037f8000dfe60037f9c009ff90037fd400dff70027fb8009fe90027f8c00dffa0027fb8009fe40037fcc009ff20027fd4009fe30027fc8009ffc0037f94009fe60017f94005ff50027fcc009ffc0027fe8009fd40027f78009ff10027f70009fd00027f70009fed0027f64009ff40027f6c009fea0027f88009fe50027f74009fe80037f64009ff20027f20009ff40037f00009fc40027f70009fc40027ee400dff80027f98009fed0027ee800dfb60027f78009fb80027ef000dfaa0027f8000dfcd0027e34009fba0027e38009fa80027f3c009ffb0037f0c009faf0027d04009f940027db8009f1f0027cfc009fd30027c2c009e5900377fc00df850037b24005ec2002642400a000002
private def correction84_4 (k : ℕ) : ℕ := if k < 86 then correction84_2 k else correction86_2 k
private def correction80_8 (k : ℕ) : ℕ := if k < 84 then correction80_4 k else correction84_4 k
private def correction88_2 (k : ℕ) : ℕ := if k < 89 then 0x7fe4009ffa0027ff4009fef0027fc0009fee0027fcc009fef0037fd8009ff80037fe0009ffe0037fb000dffb0027fc4009fee0017fec00dff30027ff4009fea0027fc8009ffb0027fa8009ff10027fd400dff40027fb8009ff80027fa0009ff80027fe8009ffd0027fb4009ff30027fa0009ff70027fac009fe70027fd4009fe20027fac00dffb0027f94009fe80027fc8009ff10037f80009fe50037f98009ff90027fd4009ff60027fb4009fe80027f8800dff90037fb400dfe40027fcc009ff10027fd0009fe30027fc4009ffb0027f8c00dfe50027f9000dff40027fc8009ffc0027fe800dfd30027f78009ff00027f6c00dfcf0027f6c00dfec0027f60009ff30027f6800dfea0037f8400dfe40027f70009fe70027f5c00dff10027f1800dff40037f00009fc30027f6c009fc20027ee4009ff70037f9400dfec0037ee8009fb50037f7000dfb70027eec00dfa80027f7c00dfcc0027e30009fb90037e34009fa70037f3800dffb0027f0800dfad0037cf8011f920037db000df1d0037cf000dfd20037c24009e5500477e8019f820047b10015ebc00663cc02e000002 else 0x7fe800dffa0037ff000dfef0037fc000dfee0037fcc009fef0027fd4009ff80037fe0009ffe0027fb4009ffc0027fc8009fed0027ff0009ff20027ff8009fea0027fc800dffc0027fa400dff00027fd8009ff50027fb400dff80027fa0009ff80037fe8009ffc0037fb4009ff20037fa0009ff70037fac009fe70027fd8009fe20027fb0009ffb0027f90009fe80027fc8009ff10027f80005fe60027f98009ffa0027fd4009ff70027fb4009fe90027f8c009ffa0027fb4009fe40027fcc009ff10027fd0009fe20027fc000dffc0027f90009fe60027f90009ff50027fc8009ffc0027fe800dfd40027f7400dfef0037f70009fcf0027f6c009fec0037f5c00dff30027f6c009feb0027f88009fe40027f70009fe80027f5c009ff10037f1800dff30037f00009fc30027f6800dfc30027ee0009ff70027f98009fed0027ee4009fb40027f74009fb70027eec009fa70027f80009fcc0027e30009fba0027e34005fa70027f3800dffa0037f08009fae0027cf8009f930027db0009f1c0027cec00dfd20027c1c009e5300277e000df830037b0c00debd00263c000e000002
private def correction90_2 (k : ℕ) : ℕ := if k < 91 then 0x7fe8009ffb0027ff4009fef0027fc4009fee0037fc800dff00027fd400dff90027fe4009ffe0027fb000dffc0027fc8009fee0027ff000dff20027ff4009fea0037fc8009ffb0027fa8009ff00027fd4009ff40037fb4009ff80037fa0009ff80027fec009ffc0037fb8009ff30027fa0009ff70037fa800dfe60027fd8009fe20017fac00dffb0027f90009fe80027fc8009ff10027f7c00dfe60027f98009ffa0027fd4009ff70027fb8009fe80037f8c009ffa0027fb4009fe40027fcc009ff10027fd0009fe20037fc400dffc0027f90009fe60027f8c00dff40037fcc009ffc0027fe8009fd30037f78009ff00027f6c009fcf0027f6c009fed0027f60009ff30027f6c009fea0027f88009fe50027f6c009fe80027f60009ff20027f1800dff40027efc009fc30027f6c009fc20027edc00dff80027f98005fed0027ee0009fb40037f70009fb60027ee800dfa70027f80009fcc0027e2c009fba0017e30009fa70027f3800dffb0037f08009fad0027cf4009f920027da800df1a0037cec009fd20027c18009e5100277d8009f830027b0400debc002639400a000002 else 0x7fe4011ffa0047fec011fee0037fbc00dfee0037fc400dfee0037fd000dff80027fdc00dffe0037fb000dffb0037fc000dfec0037fec009ff20027ff400dfea0027fc8009ffa0037fa8009ff00027fd4009ff40037fb000dff70027f9c009ff80027fe8009ffc0027fb0009ff20037fa0009ff60037fa8009fe60027fd8009fe10027fac009ffa0027f8c00dfe70027fc4009ff10027f7c00dfe50027f9400dff90027fd000dff60027fb4009fe70027f84009ff90027fb0009fe30027fc8005ff10027fcc009fe10037fc4009ffb0027f8c00dfe40037f90009ff40027fc8009ffb0027fe8005fd30027f7000dff00027f6800dfce0037f68009fec0027f5800dff30027f68005fe90027f84009fe40017f6c005fe70037f5c009ff10027f14009ff40027ef800dfc30027f6c009fc00037edc009ff70027f9000dfec0037edc00dfb30027f6c00dfb50027ee8009fa70027f7c009fcb0027e28009fb80027e28009fa60027f34009ffa0027f04009fac0027cec009f910027da4009f190027ce400dfd10027c0c009e4e00377c8009f810037b00009eb9003636400e000002
private def correction88_4 (k : ℕ) : ℕ := if k < 90 then correction88_2 k else correction90_2 k
private def correction92_2 (k : ℕ) : ℕ := if k < 93 then 0x7fe4009ffa0037ff4009fee0037fc0009fed0037fc800dfef0027fd400dff80037fe000dffe0037fb000dffb0037fc400dfed0027fec00dff10037ff400dfe90037fc400dffb0027fa4009ff00037fd4009ff40037fb4009ff70037f9c009ff80027fe8009ffc0037fb0009ff20037fa000dff60037fac005fe60037fd400dfe10027fac009ffa0037f9000dfe60037fc8009ff10027f7c009fe50027f94009ff90037fd4009ff60037fb400dfe80027f88009ff90027fb4009fe40027fc8009ff00027fcc00dfe10037fc000dffb0037f8800dfe50027f8c009ff40027fc4009ffc0037fe8009fd30037f7000dfef0027f6c009fce0027f68009feb0037f5800dff20037f6400dfea0027f84009fe30037f6c009fe70027f5800dff10037f1400dff30037ef8009fc20027f6400dfc10027ed800dff70027f94009feb0037edc00dfb30027f70009fb50027ee8009fa60037f7800dfcb0027e24009fb70027e28009fa40037f34009ffa0037f04009fab0037cec009f910027da000df170027ce000dfd10037c08009e4b00377b8011f800037af400deb60046334016000002 else 0x7fe4015ffb0037ff400dfef0027fc000dfef0027fc800dfef0027fd8009ff90027fe0009fff0027fac011ffc0037fc4009fee0027fec00dff20037ff8009fea0037fc8009ffb0037fa400dff00037fd400dff40037fb4009ff80037fa0009ff80027fec009ffc0047fb4009ff30037fa0009ff70037fac009fe60037fd8009fe10037fac00dffb0027f9000dfe70037fc8009ff10037f80009fe50027f9800dff90027fd8009ff70027fb400dfe80037f8800dffa0027fb000dfe30037fcc009ff10047fd0009fe20027fc4009ffc0027f8c009fe50027f90009ff50027fc800dffc0037fec009fd30027f74009ff00037f6c009fce0027f6c009fec0037f5c009ff30037f68009fea0037f8400dfe30027f6c009fe70027f5c009ff20027f1400dff40027ef8009fc20037f6c009fc10027edc00dff70027f94009fec0037ee0009fb30027f7000dfb50027ee8009fa60037f80009fca0037e2000dfb80027e28009fa50037f38009ffb0027f04009fac0027ce8009f910027da000df160027cdc00dfd10037c0400de4a00277b000df800037af4009eb7002631000e000003
private def correction94_2 (k : ℕ) : ℕ := if k < 95 then 0x7fe8009ffa0057ff400dfee0037fbc011fed0037fc800dfef0027fd4011ff80037fe000dffe0047fac011ffc0037fc400dfee0037ff000dff10047ff4011fe90047fc800dffa0047fa4011ff00037fd400dff50037fb000dff70047fa000dff70047fe8011ffc0037fb000dff30027f9c00dff70037fa8011fe60037fd800dfe10037fac009ffb0027f90009fe70037fc4011ff10037f7c00dfe40047f9400dff90027fd000dff70037fb0011fe70037f8800dff90037fb000dfe30047fc800dff00047fcc011fe20037fc0011ffc0037f90009fe40037f8c00dff40037fc800dffc0037fe800dfd20037f7000dfef0037f6c009fce0037f6800dfeb0047f5c009ff20037f6400dfea0027f8400dfe30037f6800dfe80027f5800dff10027f1400dff40027ef400dfc10037f6800dfc10037ed800dff70037f9000dfec0037ed8011fb20037f6c00dfb50037ee400dfa40047f7c009fcb0027e2000dfb80037e2400dfa50037f38009ffa0037f04009fac0027ce000df8f0037d9800df150027cd8009fd00037bfc00de4600477a400df7f0037ae800deb400362e800e000003 else 0x7f68265ff004e7f880d1fee0287f7c07dfd80347f800b5fee0147f98091ff60127fc8041ffc00e7f84065ff10187fbc031fed00c7fe002dff100b7ff0029fe40117fb0041ff40107fa0021ff10087fd401dff20077fa0039ff50077fa0021ff500c7fdc019ffb0077fac01dff10077f94019ff60077fa4019fe300b7fd8019fde0097fa8019ff800a7f8c019fe40097fbc021ff10057f7c015fe60057f8c021ffa0057fd4015ff50087fb0015fe60087f84011ff80057fb4015fe40057fc401dff00077fd0011fe10047fc001dffc0047f88019fe40067f88019ff40067fc4011ffd0047fec011fd10047f70015ff00047f68019fce0047f64015fec0047f58011ff30037f68011fe90047f84011fe20047f68015fe60047f58015ff10047f1800dff30057ef4011fc20047f64015fc00057ed8011ff80047f9400dfec0057edc00dfb20057f6c015fb50047ee0015fa40057f7c011fca0047e1c011fb70037e2400dfa40057f3800dffb0047f04011fab0047ce0011f900037d9c00df150027cd8011fd00057bfc00de45003779c011f7f0037ae4011eb200462c0012000004
private def correction92_4 (k : ℕ) : ℕ := if k < 94 then correction92_2 k else correction94_2 k
private def correction88_8 (k : ℕ) : ℕ := if k < 92 then correction88_4 k else correction92_4 k
private def correction80_16 (k : ℕ) : ℕ := if k < 88 then correction80_8 k else correction88_8 k
private def correction64_32 (k : ℕ) : ℕ := if k < 80 then correction64_16 k else correction80_16 k
private def correction96_2 (k : ℕ) : ℕ := if k < 97 then 0x7fe000dff90047fe8015fed0047fb800dfed0037fc400dfed0047fc8015ff70047fd800dffd0037fa8011ffa0037fbc015fec0037fe800dfef0057ff000dfe70047fc400dffa0047fa000dfee0047fc8019ff20037fa8011ff60057f94011ff60057fe4011ffb0037fa8019fef0057f98015ff50037fa0015fe30057fd000dfdf0047fa0019ffa0047f84015fe60047fbc011fef0037f70011fe40047f8c011ff80047fd0011ff50047fa8019fe50057f7801dff80047fac011fe20037fc4011fee0067fc401dfdf0077fb4019ffa0047f8001dfe30047f84011ff10077fb8021ff90057fe0011fd10057f6c015fec0087f68015fc90087f58015fe80057f48021ff00057f5c015fe60057f74025fdf0097f5c019fe200a7f4c019fed0097f04015fee00b7ee8019fbe0067f60019fbe0067ec801dff40077f8c019fe500c7ec401dfb10067f54035fb10087ecc021f9e0097f64021fc30107df4041fac0127e08025f9c00a7f1c029ff200b7edc035fa00177cac065f8400f7d7c03df060117c8808dfbf0157b940b5e26034775c081f590287a840d1e7104d60c0266000001 else 0x7fe800dffb0037ff000dfee0037fc000dfee0037fc800dfee0037fd400dffa0027fe4009fff0037fb0011ffc0027fc4011fed0027ff0009ff20037ff800dfe90037fc800dffc0027fa400dff10037fd400dff50037fb000dff80047f9c011ff90027fec00dffd0037fb000dff30037f9c00dff80037fa800dfe60027fd8009fe10037fb000dffb0037f8c011fe80037fc800dff10037f78011fe50027f9400dffa0047fd400dff70037fb800dfe70037f88009ffa0037fb400dfe30047fcc00dff10037fcc00dfe10037fc000dffd0037f8c011fe40047f8c011ff40047fc800dffc0047fec009fd20037f74009ff00047f68011fcd0047f6400dfec0027f5800dff30037f6400dfea0037f8400dfe30027f6800dfe70037f5c009ff20037f0c011ff40037ef0011fc10037f68009fc00037ed800dff70037f90011fec0047ed800dfb10037f7000dfb40027ee400dfa40037f78011fca0047e1800dfb60047e1c00dfa20047f3000dffa0037f0000dfaa0037cd800df8d0047d9800df120037ccc015fd00037bec00de400047780011f7e0037ad8009eaf003627400e000004
private def correction98_2 (k : ℕ) : ℕ := if k < 99 then 0x7fe400dffb0037ff000dfee0027fbc00dfee0027fc800dfee0037fd400dff90027fe0009ffe0027fb0009ffc0037fc4009fed0037fec00dff10037ff400dfe90027fc400dffb0037fa4009fef0037fd400dff40027fb000dff80027f9c00dff80037fe800dffc0037fb4009ff30027fa0009ff70037fa800dfe60027fd4011fe10027fac00dffb0027f8c009fe70037fc800dff10027f7800dfe50027f9400dffa0027fd4009ff60027fb400dfe70037f84009ff90037fac011fe30037fc8009ff10027fcc009fe10027fc000dffc0037f8800dfe40037f8c009ff50037fc4011ffc0027fe800dfd10037f6c00dff00027f6800dfcd0037f6400dfeb0037f5400dff20037f6000dfe90037f80009fe30027f6400dfe70037f58009ff10037f10009ff30027ef0009fc00037f64009fbf0037ed000dff60037f90009feb0037ed400dfb00047f6800dfb20037edc00dfa30037f7800dfca0037e1400dfb60037e1c009fa20037f30011ffb0027efc009faa0027cd0011f8d0037d90009f110027cc4009fcf0037be800de3e002777800df7d0047acc00dead003624c012000003 else 0x7fe4011ffb0037ff000dfee0037fbc011fee0027fc800dfee0037fd400dff90027fe0009ffe0037fb0009ffb0037fc4009fed0027fec00dff20027ff4009fe90037fc8009ffb0027fa000dff00037fd4009ff40027fb4009ff80027f9c009ff70037fe800dffc0037fb000dff20037f9c009ff70027fac005fe50027fd400dfe00037fa800dffb0027f8800dfe70027fc400dff10027f7800dfe40037f9000dff90037fd4009ff60037fb4009fe70037f8400dff90037fb000dfe20037fc8009ff00037fcc00dfe10027fc0009ffc0027f88009fe30037f8c009ff50037fc800dffb0037fe800dfd20027f70009ff00017f68009fcc0037f64009fec0037f5400dff20027f6000dfe90027f80009fe30027f6400dfe60027f5400dff00037f10009ff30037eec00dfc00037f64009fbf0027ed000dff70027f90009fec0027ed400dfb00037f6c009fb20037edc00dfa30037f7c009fca0027e14009fb60027e18005fa20027f30009ffa0037efc009fa90027cd0009f8c0037d8c00df0f0037cc8009fcf0037be4009e3b0037770009f7c0037acc009eab003622c00e000003
private def correction96_4 (k : ℕ) : ℕ := if k < 98 then correction96_2 k else correction98_2 k
private def correction100_2 (k : ℕ) : ℕ := if k < 101 then 0x7fe8009ffb0027ff0009fef0027fbc00dfee0027fc800dfee0037fd400dff80027fe000dffe0027fac00dffc0027fc4009fec0037ff0009ff20027ff8009fe80037fc400dffb0037fa400dff00037fd400dff40027fb000dff80027f9c009ff70037fe8009ffd0027fb000dff30027f9c009ff70027fa8009fe60027fd400dfe00037fac009ffa0037f8c009fe70037fc8009ff10027f78009fe40037f94009ffa0027fd4009ff60027fb4009fe80027f8400dffa0027fb4009fe20037fc8009ff10037fd0005fe10027fc000dffc0027f8c00dfe30037f8800dff40037fc8009ffc0027fe8009fd10037f70009ff00027f6400dfcc0037f64009feb0027f5400dff20037f6400dfe90037f8000dfe20037f6400dfe70027f58009ff10027f0c009ff30037ef0009fc00037f60009fbf0027ed000dff60037f90009feb0037ed4009fb00037f6c009fb20037edc00dfa20037f7800dfc90037e10009fb50037e14011fa10037f2c00dffb0027ef800dfa90027cc8011f8b0037d88011f0e0027cc000dfd00027be000de39003776400df7c0037ac000dea90046204016000002 else 0x7fe400dffb0027ff000dfee0037fbc00dfed0037fc400dfee0037fd000dff80037fe0009ffe0037fb0009ffb0027fc4009fec0027fec009ff10027ff4009fe90037fc400dffb0037fa4009ff00027fd000dff40027fb000dff70037f9c009ff70027fe8009ffc0037fac00dff20027f9800dff70037fa8009fe40037fd400dfdf0037fa800dffb0027f8c00dfe60027fc400dff00027f7800dfe40037f90009ff90037fd400dff60037fac00dfe70027f80009ff90027fb0009fe20037fc400dff00027fd0005fe10037fc0009ffb0037f88009fe40027f88009ff40037fc4009ffc0027fe8009fd10027f6c009fef0027f64009fcc0027f64009feb0027f5400dff30017f6000dfe90027f80005fe20037f6000dfe60027f54009ff00027f0c009ff20037eec00dfbf0037f6000dfbf0027ed0009ff60037f90009feb0037ed0009faf0037f6800dfb20027edc009fa20027f7400dfc80037e10009fb50037e10009fa20027f2c009ffa0037ef800dfa70037cc8005f8b0037d88009f0d0027cb800dfcf0027bd800de37003775c009f7b0027ac0005ea900261e400e000002
private def correction102_2 (k : ℕ) : ℕ := if k < 103 then 0x7fe000dffa0027fec00dfed0037fbc009fec0037fc400dfed0037fd0009ff80017fdc009ffd0037fa800dffa0037fc0009feb0037fe8009ff10027ff4009fe70037fc000dffa0037fa0005fef0017fcc00dff30037fac009ff70037f98009ff70037fe8009ffc0027fac00dff20037f9800dff60037fa4009fe50027fd000dfdf0027fa8009ffa0027f8800dfe50037fc0009fef0027f7400dfe30037f8c00dff80037fd000dff50027fac00dfe60027f7c009ff80037fac00dfe20027fc400dff00027fc800dfe00037fb800dffb0027f8400dfe20037f88009ff30027fc4009ffb0037fe400dfcf0037f6c005fee0037f6000dfcb0037f60009fea0037f5000dff10037f5c00dfe80027f7800dfe20027f60009fe60017f50009fef0037f0400dff30027ee800dfbf0027f5c00dfbe0017ecc00dff50037f8c009fea0037ecc00dfaf0037f6400dfb10027ed8009fa10037f7000dfc70037e0800dfb30037e0c00dfa00037f2800dff90037ef4009fa70027cc000df8a0027d84009f0b0037cb8005fce0037bd000de340037750009f7a0037ab000dea600361c400e000002 else 0x7fe4031ffa0077ff0015fee0057fb4019fec0057fc0011fed0047fcc011ff70047fdc011ffe0037fa8011ffa0047fbc015fec0047fe8011ff10027ff400dfe80037fc000dffb0027f9c00dfef0037fd4009ff40027fb000dff70037f9800dff80027fe400dffc0037fb0009ff20027f9800dff70027fa400dfe60017fd8009fdf0037fa8009ffb0027f8800dfe60027fc0011ff00027f7400dfe30037f9000dff80037fd0009ff60027fb0009fe60037f8000dff80037fb000dfe10037fc8009ff00027fcc00dfe00027fbc00dffc0027f84011fe40027f88009ff40037fc400dffc0027fe400dfd00037f6800dfef0037f6400dfcc0037f6000dfeb0037f5000dff20027f60009fe80037f7c009fe20037f6000dfe50037f5000dff00037f0c009ff20037eec009fbf0037f6000dfbe0027ec800dff60037f8c009fea0037ed000dfaf0027f68009fb10037ed800dfa10027f78009fc90027e0c005fb40037e10009fa00037f2800dffa0027ef800dfa70027cc000df8a0037d84009f0a0037cb4009fce0037bd0009e340037748009f7a0027ab000dea600361a800e000002
private def correction100_4 (k : ℕ) : ℕ := if k < 102 then correction100_2 k else correction102_2 k
private def correction96_8 (k : ℕ) : ℕ := if k < 100 then correction96_4 k else correction100_4 k
private def correction104_2 (k : ℕ) : ℕ := if k < 105 then 0x7fe400dffa0037ff400dfee0027fc000dfed0037fcc009fef0027fd400dff80037fdc00dffe0037fb0009ffc0037fc000dfec0037ff0009ff10037ff800dfe90037fc8009ffb0037fa4009ff00027fd8009ff40037fb4009ff70037f9800dff80037fec009ffd0027fac00dff30027f9c00dff80027fa8009fe50037fd8009fdf0037fa800dffc0027f8c009fe60037fc8009ff00037f78009fe50017f9400dffa0027fd400dff60037fb000dfe60037f84005ffa0037fb0009fe20027fcc009ff00037fd0009fe10017fc000dffc0037f8400dfe40037f88009ff40037fc400dffd0037fe800dfd10027f70005ff00027f6400dfcc0037f6000dfeb0037f54009ff20037f6000dfe90037f80009fe20037f6400dfe60037f5400dff10037f0c00dff40027ee800dfbf0027f6000dfbe0027ecc00dff70037f9000dfeb0037ed000dfaf0037f6800dfb20027ed4011fa10037f7800dfc90027e0c00dfb40037e1000dfa10037f2c009ffb0037ef400dfa80037cbc015f8a0037d80015f0a0047cb4011fce0047bd000de31004773801df790047aa4019ea10076168036000003 else 0x7fe8009ffb0037ff000dfee0027fc000dfec0037fc400dfee0037fd4009ff90027fdc00dffe0037fb0009ffb0037fc400dfec0037fe800dff20037ff8009fe80037fc400dffb0037fa000dff00027fd4009ff40017fb000dff70037f9800dff80037fe800dffc0027fb000dff20027f9800dff70037fa4009fe60017fd4009fdf0027fa800dffb0037f8800dfe50037fc400dff00027f7800dfe30037f90009ffa0027fd000dff60027fb0009fe60037f7c00dff90037fb0009fe20037fc8009ff00037fcc00dfe00037fc0009ffc0037f88009fe30037f8800dff40037fc8009ffc0027fe800dfd00037f6c00dfef0037f6000dfcc0027f64009feb0037f54009ff20027f60009fe80037f7c009fe20037f6000dfe60037f5000dff00037f08009ff30027ee8009fbe0037f6000dfbe0027ec800dff70027f8c009feb0037ecc009fae0037f68009fb10027ed800dfa10027f7400dfc70037e08009fb40037e0800dfa00027f2800dffa0037ef8005fa70027cbc009f8a0037d7c00df080037cac00dfce0037bcc00de31002773c009f790037aa800dea3003617400e000003
private def correction106_2 (k : ℕ) : ℕ := if k < 107 then 0x7fe800dffb0027ff4009fee0027fc0009fed0037fc800dfee0027fd400dff90027fe0009fff0027fac00dffc0037fc400dfec0027ff0009ff20037ff8009fe80037fc400dffb0037fa000dfef0037fd400dff40037fb000dff80037f9800dff80027fec00dffc0027fac00dff30037f9c009ff60037fa800dfe50037fd400dfdf0027fac009ffb0037f8800dfe70027fc8009ff10037f7400dfe30037f9000dffa0027fd000dff60037fb0009fe70037f8000dff90037fb000dfe30017fcc009ff10037fd000dfe00027fc4009ffc0027f8800dfe30027f8800dff40027fc8009ffc0037fec009fd00037f6c009fef0037f6400dfcc0027f6400dfec0027f5000dff30027f6000dfe90027f7c00dfe20037f64009fe50037f54009ff00027f0800dff40027ee800dfbf0027f60009fbd0037ecc009ff60037f8c00dfec0027ecc00dfae0037f6c009fb00037ed8009fa10027f78009fc80037e08009fb30037e0c009fa00027f2800dffb0037ef8009fa70027cb800df8a0027d7c009f080037cac009fce0037bc400de30002773000df790027aa800dea2003615800e000003 else 0x7fe0015ffa0037fec011fed0037fb4015feb0037fc400dfec0027fd0009ff70037fd800dffd0027fa400dffa0037fbc00dfeb0027fe8009ff10027fec00dfe70037fbc00dff90037f9c00dfef0037fcc00dff20037fa800dff60037f9400dff70027fe400dffb0037fa8009ff10037f9400dff50037fa0009fe30037fd0009fde0037fa000dff90027f84009fe50037fc0009fee0037f70009fe20037f8800dff80037fd0009ff50027fac009fe50027f7c009ff70037fa8009fe10027fc400dfef0037fc8009fdf0037fb800dffb0037f8000dfe20027f80009ff30037fc000dffb0037fe400dfcf0027f68009fed0037f5c00dfca0037f5800dfea0037f4c00dff00037f5800dfe70027f7c005fe00037f60009fe50027f4c00dfef0037f04009ff20037ee4009fbc0037f5800dfbc0037ec000dff60027f8c005fea0037ec8009fad0027f6000dfaf0037ed0009f9f0037f74009fc60037e0000dfb10037e04009f9e0037f24009ff90037eec00dfa50037cb0009f880027d74009f070027ca4009fcc0037bbc00de2c003772400df770037a9800dea1002613800e000002
private def correction104_4 (k : ℕ) : ℕ := if k < 106 then correction104_2 k else correction106_2 k
private def correction108_2 (k : ℕ) : ℕ := if k < 109 then 0x7fe0009ff90047fec00dfed0037fb8009feb0037fc4009fed0037fcc00dff70037fdc009ffd0037fa4011ffb0027fbc00dfeb0027fe400dff00027ff0009fe70037fc0009ffa0027f9800dfed0037fd0009ff30027fa800dff60037f9000dff70027fe4009ffb0037fa8009ff10027f94009ff40047f9c00dfe30037fd0009fde0037fa000dffa0037f8000dfe40027fbc00dfef0027f7000dfe30027f8c009ff80037fc800dff50027fac00dfe50037f7c00dff80037fac009fe00037fc400dfef0027fc4011fdf0027fb8009ffb0027f8000dfe10027f8000dff30037fc0011ffa0037fe000dfce0027f6400dfee0027f60009fc90037f5c00dfe90037f4800dff10037f58009fe70037f7400dfe00037f5c009fe50027f4c00dfef0037f0000dff20027ee000dfbb0047f5800dfbc0037ec000dff60037f8800dfe90047ec400dfac0027f60009fae0047ed000df9f0037f70009fc60037dfc00dfb10037e0400df9e0027f1c011ff80047eec00dfa40037cac00df870027d7400df050037ca000dfcc0037bbc009e2a003771c011f760037a9400de9e0046118016000002 else 0x7fe400dffa0037ff000dfed0047fc0009fec0037fc400dfed0047fd4009ff70037fd8011ffe0027fa800dffc0027fbc011feb0037fec009ff10027ff4009fe80037fc400dffb0027f98011fee0027fcc00dff30027fa8011ff70027f94011ff70037fe400dffb0037fac00dff20037f9800dff60027fa4009fe30047fd4009fdd0047fa400dffa0037f8800dfe40037fc0009fef0027f7000dfe40027f8c00dff90027fcc00dff60027fac00dfe50037f7c009ff90027fac009fe20027fc400dfef0037fc800dfe00037fbc009ffb0047f8000dfe20027f8400dff40027fc4009ffc0027fe400dfce0037f6400dfef0027f6000dfcb0027f58011fea0037f4800dff20027f5c009fe80037f78009fe20027f5c009fe50037f4c011fef0037f0000dff30037ee400dfbd0027f5800dfbb0037ec400dff60037f8800dfea0037ec8011fad0037f6000dfaf0037ecc011f9f0027f74009fc80027e00009fb20037e0400df9e0027f2400dffa0037ef000dfa50037cac00df880027d7400df060027ca4009fcd0037bb800de2a002771800df770027a98009e9f002610c00e000002
private def correction110_2 (k : ℕ) : ℕ := if k < 111 then 0x7fe400dffa0047ff0011fee0027fbc009fec0037fc8009fed0037fcc015ff80037fe000dffe0037fac009ffb0047fc000dfeb0047fec00dff00047ff400dfe90037fc400dffa0047fa000dfef0027fd000dff30037fac011ff80027f9800dff70047fe800dffc0037fb0009ff20037f98011ff60037fa0011fe30047fd400dfdf0027fa800dffb0027f8400dfe50047fc0011ff00037f70011fe30027f8c00dff90027fd4009ff50047fb0009fe60047f80009ff90037fa8011fe20027fc400dfef0047fd0009fe00027fbc011ffb0037f88009fe20047f88009ff40037fc400dffb0047fe800dfcf0037f64011fee0047f6000dfcb0037f5c00dfeb0027f50009ff10037f58011fe90037f7c009fe20027f6000dfe60037f5000dff00027f0000dff30027ee400dfbe0027f5c009fbd0027ec400dff60037f8c00dfea0047ec800dfae0037f6400dfb00027ed400df9f0037f7000dfc80027e0000dfb20027e04009f9f0027f2400dffb0027ef0009fa60027cac011f870047d7400df060027ca000dfcd0037bb800de29002771400df770037a9400de9e00360f0012000004 else 0x7fcc0a9ffa0177fc0079fec00d7fb0031feb0087fac039fed0087fd001dff500a7fcc029ffe0067fa4011ffa0057fb8021feb0057fe8019ff10057fec021fe50087fc0019ff90077f9c015fef0057fd400dff30057fac015ff70047f94015ff70057fe0015ffc0047fac015ff10057f9800dff50057fa4011fe40037fd4011fde0037fa4015ff90047f84011fe50047fc0015ff00037f74011fe40047f8c00dff90057fd0011ff50057fac00dfe60047f7c011ff90037fac00dfe10047fc800dff00047fcc00dfdf0047fbc011ffb0047f80011fe30037f8400dff40047fc800dffc0057fe800dfcf0047f64011fee0057f6000dfca0047f60011feb0047f5000dff10047f5c00dfe80047f7c00dfe20037f64009fe50047f5000dff00037f00011ff30037ee400dfbd0037f58015fbc0037ec800dff60037f8c011feb0037ec800dfad0037f6400dfaf0047ed400df9f0037f74009fc60047e00009fb20037e00011f9f0037f24011ffa0037ef000dfa50047cac00df870037d7400df040047ca000dfcd0037bb8009e27004770c011f770037a9000de9d00260e400e000003
private def correction108_4 (k : ℕ) : ℕ := if k < 110 then correction108_2 k else correction110_2 k
private def correction104_8 (k : ℕ) : ℕ := if k < 108 then correction104_4 k else correction108_4 k
private def correction96_16 (k : ℕ) : ℕ := if k < 104 then correction96_8 k else correction104_8 k
private def correction112_2 (k : ℕ) : ℕ := if k < 113 then 0x7fdc011ff90047fec011fed0047fb8011fec0047fc400dfed0027fcc011ff70047fdc011ffe0037fa800dffa0037fbc011feb0047fe8011ff10037ff0011fe70047fc000dff90047f9c009fee0047fd000dff20047fac009ff60047f90015ff60037fe0011ffa0047fa800dff00047f94011ff50047f9c011fe30037fd0011fde0037fa0011ffa0027f80011fe50037fc0009fef0037f70011fe10047f88011ff80047fd0009ff50037fa8011fe50047f7800dff80037fac00dfdf0057fc0011fee0047fc4011fde0047fb8011ffb0037f80011fe20037f8000dff30037fc000dffa0047fe0011fce0047f60011fed0037f58011fc90047f58011fe90047f48011ff00047f54011fe70047f74015fe00037f5800dfe40047f4c011fef0047efc011ff20047edc00dfbc0047f54011fb90057ebc015ff60037f8c00dfe80067ec0011fac0047f5c019fad0057ec4015f9d0047f68015fc40067df4019faf0087df4021f9b0067f20015ff80067ee0025fa50057ca0019f840067d64029efe00c7c9001dfc80087b9c039e2200976f002df6d00d7a54075e8801760440aa000003 else 0x7fe8009ffb0027ff000dfed0047fbc011fec0047fc8009fed0047fd0011ff80047fdc00dfff0037fac00dffb0047fc4009fec0037fec00dff10037ff8009fe80037fc0011ffb0037fa000dfef0047fd0011ff50027fb000dff60047f94011ff80027fe8011ffc0047fa8011ff20047f94011ff60047fa400dfe40047fd4011fdf0027fa800dffb0027f84011fe50037fc400dfef0047f74009fe30037f9000dff90037fd400dff50047fac011fe60047f7c011ff90047fac011fe10047fc4011ff00047fcc00dfe00027fbc00dffb0047f8400dfe20037f88009ff40047fc0011ffc0037fe800dfcf0037f68011fef0037f60011fca0047f5c011fea0047f4c00dff30027f5c011fe90027f78011fe10037f5c011fe60027f5000dff10027f0000dff30047edc011fbd0027f5c009fbc0037ec4009ff60047f90009feb0047ec4011fac0037f6400dfae0047ed4009f9e0037f74009fc70027e00009fb30027dfc011f9d0047f20011ffa0037eec00dfa40047ca8011f870047d6c011f030047c98011fcd0047bb400de260047704011f760027a8800de9c00460bc00e000004
private def correction114_2 (k : ℕ) : ℕ := if k < 115 then 0x7fe4011ffb0037ff0011fee0047fc0011fee0037fc8011fef0037fd0011ff90027fe0011ffe0047fac011ffc0037fc400dfec0047ff0009ff20037ff4011fe90027fc800dffb0047f9c011ff00037fd400dff50037fac00dff80037f98011ff80037fec00dffc0047fac011ff30027f98011ff70047fa800dfe50037fd4011fdf0047fa8011ffb0037f8c009fe50047fc0015ff10027f74011fe30047f90009ff90057fd0011ff70027fb0011fe60047f7c011ffa0027fb000dfe20047fc8011ff10027fcc011fe10027fc0011ffc0037f84011fe20047f84011ff50037fc800dffd0047fe800dfce0047f68011fef0047f64009fcb0037f6000dfeb0037f4c011ff20047f5c00dfe90027f78011fe10047f60011fe60027f5400dff10027f08009ff40027ee8009fbe0027f60009fbd0037ec4011ff60047f8c011fec0027ec4011fad0037f64011faf0047ed0011fa00037f78009fc70047e00009fb20047e00011f9e0047f28009ffb0037eec011fa50047ca4011f870047d74009f030047ca0009fcd0047bb0011e260027704009f770037a8800de9b00460a8012000004 else 0x7fdc019ffa0057fec015fec0047fb8011feb0037fc4011fed0057fcc011ff60047fd8015ffe0037fa4011ffa0037fc0009fea0047fe4015ff00037ff400dfe80037fc4009ff90057f98011fef0027fcc011ff40027fa8015ff70037f94009ff60047fe0015ffb0047fa8011ff10037f98009ff60047fa4009fe30057fd000dfdd0057fa8009ffa0037f8800dfe40057fc0009ff00027f74009fe20047f8c00dff70057fc8015ff60037fac011fe50037f7c011ff90037fac009fe10037fc400dfef0037fc800dfdf0037fbc011ffa0037f84009fe10047f8400dff20057fc000dffc0037fe400dfce0047f64011fed0047f5c00dfca0027f58011fea0027f4c009ff10037f54011fe70057f78011fe00037f5c00dfe40037f4800dff00037f0000dff10057edc00dfbc0027f54011fba0047ec0009ff50057f8800dfea0047ec0015fac0037f60011fad0047ed0009f9e0037f6c011fc50037df4011fb10027e00009f9d0037f2400dff90057ee8011fa40037ca400df860047d68011f020037c90011fcd0037bac011e2300376f4011f740047a80011e990046090016000003
private def correction112_4 (k : ℕ) : ℕ := if k < 114 then correction112_2 k else correction114_2 k
private def correction116_2 (k : ℕ) : ℕ := if k < 117 then 0x7fe4011ffb0037ff400dfee0037fc000dfec0037fc800dfef0037fd400dff90037fdc015fff0047fac00dffb0057fc4011fec0037fec015ff20037ff4015fe80057fc800dffa0057f9c015ff00037fd4011ff50027fb000dff70047f9800dff90037fec00dffc0057fb0011ff20057f9800dff70037fa800dfe50037fd800dfdf0047fa800dffc0037f8800dfe50057fc400dfef0057f7800dfe40037f94009ffa0037fd800dff70037fac00dfe60037f7c011ff90047fb000dfe20037fc8011fef0057fcc011fe00037fc000dffc0037f8400dfe30037f84015ff50037fc800dffc0057fe8011fcf0037f6800dff00037f5c015fca0047f60009fea0057f4c00dff10047f58015fe80057f7c00dfe10047f5c015fe40057f4c011ff00037f00011ff30037ee400dfbc0057f5c011fbb0057ec400dff70047f8c015feb0037ec4015fad0047f64015fb00027ed0011f9f0027f70015fc70037df8011fb10057e00009f9d0037f28009ffa0047ef400dfa50037ca4011f860037d6c011f020057c98015fce0047bb0009e2300476f4015f750047a8000de98005608001a000005 else 0x7fe400dff90057ff000dfec0037fb8015feb0037fc400dfed0037fcc00dff70037fd8015ffd0057fa4015ffa0057fbc015feb0037fe8015ff10037ff0015fe70057fc0015ff90057f98015fee0057fcc015ff40037fa800dff60057f90015ff60057fe800dffa0057fac00dff10037f9400dff70037fa0015fe30057fd000dfdd0057fa400dff90057f8400dfe40057fc000dfef0057f7000dfe10057f8c00dff90037fd000dff60027fac00dfe50057f78015ff70057fa8011fe00037fc800dfee0057fc4015fde0057fb8015ffb0037f8400dfe10057f8400dff40037fc400dffb0037fe400dfce0037f60015fed0057f58015fc80057f58015fe90047f48011ff00037f5c00dfe80047f74015fe00047f54015fe50037f4c015fef0057efc015ff20057edc015fbc0037f5800dfbb0057ec000dff70027f8800dfeb0037ec000dfaa0057f6400dfad0047ecc00df9e0037f6c015fc60047df4015fb00037dfc009f9c0057f2400dff90057ef0009fa30057c98015f860037d6800df000057c90011fcc0037ba800de2200376f000df740047a7c00de98003607800a000003
private def correction118_2 (k : ℕ) : ℕ := if k < 119 then 0x7fe000dff90057fec00dfec0037fb4015feb0037fbc019feb0057fcc00dff70037fd800dffd0037fa400dff90037fc000dfe90067fe0019ff10037ff000dfe70037fbc011ff90037f9c00dfee0037fd000dff20047fa0019ff60037f8c015ff60047fe400dffa0057fa800dff00037f9000dff50037fa000dfe30037fcc00dfdd0037fa000dff90057f78019fe30057fb8019fed0067f6c00dfe00057f8800dff80037fc8019ff50037fa4019fe40067f7400dff70057fa4019fe00037fc0015fed0057fc0015fdf0037fb400dffa0037f8000dfe20037f7c015ff20057fbc011ffa0057fdc015fcd0037f6000dfec0057f58011fc90037f5800dfe90057f4400dfef0057f54011fe50057f70015fdf0067f5c00dfe40037f4800dfee0037efc00dff00067edc00dfba0057f5400dfba0037eb800dff60037f84011fe90037ebc015fab0037f5c00dfab0057ec800df9c0057f6c00dfc40057df400dfaf0057dfc00df9a0057f1c015ff70067ee800dfa30037c9c00df850037d60015eff0057c88015fcb0037ba400de2100376e4015f740037a7800de960056068016000003 else 0x7fdc045ff900b7ff4019fec0097fb0025fec0067fc0019fec0067fd0011ff70067fd4019ffd0067fa8019ffb0067fbc019feb0067fec011fef0067ff0019fe70067fbc019ffb0037f98019ff00037fd4011ff20067fb0011ff80047f94019ff80037fe8019ffd0037fa4019ff30047f90019ff80037fa4019fe30067fcc019fdf0037fa0019ffa0047f8c00dfe60037fc0019fee0067f7000dfe20047f8c011ff80067fcc019ff50067fb000dfe60047f7c011ff90047fa8019fe10037fc0019ff00037fcc011fdf0047fc400dffc0037f80019fe20047f8400dff20067fc0015ffc0037fec00dfcd0067f60019fef0037f5c011fca0037f60011fec0037f4c015ff10057f58011fe80047f7c00dfe10047f5c011fe40067f50011ff00047f0400dff40037ee0011fbb0067f58011fbb0037ec000dff60057f8c011fe90067ec400dfab0057f64015faf0037ecc019f9c0067f70015fc70037df800dfb00067df800df9e0037f2000dffa0067eec011fa30067c9c015f860057d6c00df010037c9000dfcd0047ba8011e2100376e8011f740047a7c00de980036060016000006
private def correction116_4 (k : ℕ) : ℕ := if k < 118 then correction116_2 k else correction118_2 k
private def correction112_8 (k : ℕ) : ℕ := if k < 116 then correction112_4 k else correction116_4 k
private def correction120_2 (k : ℕ) : ℕ := if k < 121 then 0x7fe0011ff90077fe401dfec0047fb800dfeb0047fc0011feb0047fc8011ff50067fd8011ffc0077fa8011ffa0047fb8011fea0077fe4019fef0067fec019fe50077fb801dff90047f98011fed0067fcc011ff30037fa001dff50067f8c01dff40077fdc01dff90077fa4011ff10047f9400dff60037fa000dfe20077fd000dfdd0047fa400dff80067f80011fe40047fb801dfef0037f6c011fe10067f88011ff60077fc8011ff30077fa401dfe40047f78011ff70077fa800dfdf0077fb801dfef0047fc401dfde0037fb4019ffb0047f7c019fdf0077f7c011ff10077fc0011ffb0047fe400dfce0037f60011fec0067f5c00dfc70067f58011fe70077f4001dfee0067f50011fe70037f7400dfdf0047f54011fe40037f44019fef0037efc011ff10047ed4019fbb0037f54019fb90067eb4019ff50047f84011fe90047ebc00dfa90077f6000dfad0047ec8019f9c0067f68019fc40067de801dfaf0067df800df9c0047f18019ff80067ee4019fa30047c98011f840047d60019efe0067c88019fca0067b9801de1c00676d8021f710067a68025e92009602c03a000003 else 0x7fe8015ff80087ff0015fee0057fbc011fed0047fc4011feb0087fd4011ff80047fe0011fff0057fb0011ffc0057fb8021fec0047fe8021ff10047ff8011fe80047fc4015ff90087fa0011fee0077fd0011ff40057fac011ff70047f8c021ff90047fe0021ffc0057fa401dff10057f98011ff70047fa4011fe30087fd4011fdf0047fa8011ffc0047f8001dfe60047fb8021ff00057f70015fe40047f8c015ff80047fcc01dff50077fb4011fe70047f78015ff70087fb0015fe00077fcc011fef0047fcc011fe00047fb801dffb0047f88011fe20047f7c021ff30077fc4011ffc0057fec011fcf0047f64011fef0047f5c01dfc90047f60011fea0077f4c011ff20057f58015fe80077f78011fe00077f60015fe50047f50011ff00047efc01dff40047ee4011fbc0047f5001dfbd0047ebc01dff80047f8801dfea0047ec4011fac0047f5c01dfae0047ed0011f9e0047f70011fc60047dfc011faf0077df8011f9c0047f20011ffa0077eec011fa30077c9801df860047d6401df000077c90019fce0047ba0011e1f00776e800df750047a74019e960066054012000006
private def correction122_2 (k : ℕ) : ℕ := if k < 123 then 0x7fe0015ffa0057fec015feb0057fb4025fed0057fc0025fec0057fd4015ff70057fdc015ffd0057fa0025ff90097fb8025fea0057fec015ff10057fec021fe60097fc0015ffa0047fa0015ff00057fd4015ff40057fac015ff70087f9c015ff70057fe8015ffa0057fac011ff30057f98015ff80047f98025fe50047fd0015fdd0047fa0025ffa0047f80021fe60057fb8021fef0057f70015fe40057f8c015ff90057fcc025ff40087fb0015fe50057f74025ff90057fa8021fdf0097fcc015ff00057fd0015fdf0057fb4025ffa0087f80015fe10057f88015ff40057fc0015ff90097fe0025fce0047f60015fee0047f5c015fca0047f54021fea0087f4c015fef0097f5c015fe90057f78011fe00087f58015fe30087f4c011fef0087f04011ff30047ee0015fbc0047f54021fbb0057ebc021ff50057f84015fe90087ec0021fab0047f60015fae0047ecc015f9d0087f64021fc50047df8015fb10047e00011f9a0087f1c021ff90087eec015fa10087c94021f830087d5c021f000047c8c015fcb0087ba0011e1f00476e8011f720087a7c011e950076040022000005 else 0x7fdc02dffb0067fec019fed0067fb4019fea00b7fc0019fea00b7fc8019ff600b7fd002e0000057fa8019ffb0057fc0019fea0067fe4019ff00067ff0019fe500a7fb802dffa0067f98019fec0067fcc019ff20057fac019ff80067f90019ff50067fd802dffc0067fac019ff00057f98019ff200b7f94029fe100a7fd0019fdd0067f9802dffb0067f7c029fe20067fc4019fee00a7f68015fe000b7f88015ff600a7fd0015ff100b7fac015fe40067f74029ff80067fb0015fde00a7fc8019fee0067fd0015fdd0057fbc015ffc0057f78029fe10067f84015ff40057fc0019ffd0057fe8015fcc00a7f68015fef0057f54029fc70097f54019fe80067f50015fee00a7f54019fe80057f7c015fdf0057f54029fe40057f48015fed0097f00019ff10067ed8025fba0097f5c015fb900a7eb8025ff50057f80025fe90067eb4025faa0067f64015fad0057ec0025f9d0057f64025fc300a7df0019fb00057de8029f9d0057f20019ff800a7ef0015fa40057c98015f850067d60015f000057c88025fca00a7ba4015e1c00976e4015f720097a78015e960056038026000005
private def correction120_4 (k : ℕ) : ℕ := if k < 122 then correction120_2 k else correction122_2 k
private def correction124_2 (k : ℕ) : ℕ := if k < 125 then 0x7fec01dffa00e8000021fee0087fb0039feb0087fcc021feb00e7fd4021ff90087fe401e0000077fb001dff900e7fcc021fea00e7fec01dff30077fe8039fe600e7fd001dffc0077f9801dff20087fc8039ff60077fac021ff600d7f90039ff80077fec01dffa00d7fb801dff20077f9401dff70087fa001dfe40077fc8035fde0077fa0039ffd0077f78039fe50077fc401dff20077f7401dfe50077f80035ffb0077fd001dff80077fb801dfe70077f74035ff700d7fb401dfe20077fcc019ff10077fc8035fe10077fc4019ffc0077f8c01dfe20067f8c01dff300c7fc0031ffb00c7fe0031fd10077f5c031fec00c7f6401dfcb0077f58031fe900c7f40031ff40067f5801dfe600d7f74031fe30067f50031fe40077f48031ff00077efc031ff40067ee001dfbc00c7f54031fbc0067eb8031ff500c7f84031fed0067ebc031fac0067f6c01dfad00b7ec8031f9f0067f6802dfc400c7df8019fb30067df8019f9e0067f24019ffa0077ef8019fa200b7ca0019f8300c7d64031efe00c7c8c02dfcc00c7bac019e2100676d8031f750067a7c019e98006604001a00000b else 0x7fc802dff900b7fd4055fe40157f90055fe30157fb802dfe40147fb802dfed0147fc802dff30147f9402dff800b7fa002dfe20157fd002dfea00b7fe4029fe100b7fa404dff600b7f80051fea00a7fa4051feb0137fa4029ff500a7f8802dff600a7fd8029ff500b7fa0029ff000a7f7804dfed0127f8404dfdb0137fd0025fda00a7fa0025ff500a7f5c049fdc0137fb0025fe60127f4c049fdd00a7f68049ff10127fc0029ff00097f90049fde0127f60029ff40097f94029fd80127fa4049feb0097fc0025fd90097fa0029ff50097f6c029fd90117f7c025ff10097fb4025ff30117fdc025fc90097f40045fe90097f58025fc70097f54021fe80097f40021feb0097f48025fe20107f68025fd90107f4c021fdf0087f44021fea0087ee4041fed0097ed8025fb50107f40041fb90087e9c041ff10097f74021fe90097eb0025fa90087f4803dfad0087eb8041f960107f68021fc40087dd803dfa800f7ddc03df990087f18021ff80087ecc041f9f0087c8c021f7f00f7d58021ef90087c80021fc700f7b90021e1700f76d0021f6c00f7a68021e920086028022000007
private def correction127_2 (k : ℕ) : ℕ := if k < 128 then 0x603a8c1e995197a84d99f6a28d76b9051e123677b845d9fc21477c80489eff20b7d643b9f8b0da7c6464dfa70bb7ecc2bdfee0a47f30269f960927e0c451fa00847dd83e9fc90787f2c1cdf940da7ebc1a5fa90c97f30185fab0bc7e782d5fea0577f90155ffb0527e8827dfb509a7f10131fbb0927ea0239fdf0467ef421dfd60427f14105fe803f7f000f5fce03c7f5c0edfe003a7ee80e1fdc0377ef81adfec0357f4c0d1fc70667f2c18dfdc0327f000c1fcf05e7fb40b9fe502e7fac0b5fec02d7f70159fc902b7f600a9fff02a7f600a5fc90297f700a1fec0287fac09dfe50267fb4095fcf0267f00125fdc0247f2c08dfc70237f4c08dfec0237ef810dfdc0437ee8105fe00217f5c085fce03f7f000f9fe801f7f140f5fd603d7ef407dfdf03b7ea0075fbb01d7f100e5fb501c7e88071ffb01d7f9006dfea01b7e780d5fab01b7f300d5fa901a7ebc069f9401a7f2c0cdfc901a7dd8069fa00317e0c065f960197f30065fee0187ecc061fa70187c640bdf8b0187d6405deff0177c8005dfc202c7b84059e1202c76b8059f6a0167a84059e99016603805a000016 else 0x2000000
private def correction126_3 (k : ℕ) : ℕ := if k < 127 then 0x7fc8055ff60157fc00a5fea0147fa4055fe10287f8c09dfe80147fac051fee0147fdc051ff50147f68099ffc0147fc404dfe90147fe804dfe30257fd0095fe30137f9c091ff40127f80049fe30237fac08dfe80237f7c08dffa0127f6808dfeb0227fbc089fee0217f98049fec0127f94045ff40117f98045fe60117fc8045fd30207f8807dff80107f64041fe40107f9c07dfe601f7f68041fd701f7f84041ff500f7fb0079fe901e7fb0041fe500f7f7403dffc00f7f9c041fde00f7fc803dfee00e7fa4075fe000f7fb003dfff00e7f8c03dfe000e7f74039fea01c7fa8071ff301c7fec039fd000e7f54039fe501b7f68035fce00e7f50039fe201a7f48039feb01a7f64039fe400d7f6c039fdb00e7f48039fe200d7f40035fea0197f00035ff400d7ee0035fb900c7f50035fb700d7eb0031ff200d7f88035fe50187eb0061fad00c7f68031faa0177ec8031fa100c7f68031fbf0187df8031fab0177e04031f9a0177f18031ff70177efc031fa100c7c7c05df8600b7d6802deff00b7c9002dfc900c7b90059e1b01676dc031f700167a80031e90016602005600000b else correction127_2 k
private def correction124_5 (k : ℕ) : ℕ := if k < 126 then correction124_2 k else correction126_3 k
private def correction120_9 (k : ℕ) : ℕ := if k < 124 then correction120_4 k else correction124_5 k
private def correction112_17 (k : ℕ) : ℕ := if k < 120 then correction112_8 k else correction120_9 k
private def correction96_33 (k : ℕ) : ℕ := if k < 112 then correction96_16 k else correction112_17 k
private def correction64_65 (k : ℕ) : ℕ := if k < 96 then correction64_32 k else correction96_33 k
private def correction0_129 (k : ℕ) : ℕ := if k < 64 then correction0_64 k else correction64_65 k
private def correctionWords (k : ℕ) : ℕ := correction0_129 k
private def correction (k : ℕ) : ℕ :=
  (correctionWords (k/128) >>> (26*(k%128))) % (2^26)

private def eighth0_2 (k : ℕ) : ℕ := if k < 1 then 0x7ff6bcf0729b3731f87be58ffeea6dfbc7a9242ccf3449ffdf94014134396700f6dcbffc38d0e196eec4d50a3b47ff8f9543173bea704c518cfff2f82f2bc6d648e08b961ffe7e7afadc93893b7693e3ffd396896a34256d0cd9b77ffae6c756b6ddd5b363c2efff6ab9cc695b5e89e4938dffeeff993aeabf33126659bffe12878a77a15c633064e7ffc8548b2022cd0c871696fff9c126447b7424fbe1801fff4dbb98873a615d98f723ffec42d3725b6aeed1e40f7ffdd4d743a5ab1d46c005efffc38c9be717763928db05fff97c0cf909ae4be74e073fff4e592f189d6e9a7ffe67ffed5723ca45d6af540576fffe1285aed775d896f351dfffce090b21fbbf1dbb1c1bfffb10b1d15249ace38c417fff8718feb4cd429d08eaeffff4e58f17465de177337dffff09429bf798d50b084bbfffec42c43a03a54c0c50d7fffe9cb1c416aa9b13b5baffffec42c3773235ec9e2e5fffff62161a33eec9234e040000000000000000000000 else 0x7fd9c0ca543d184bdd6ff36ffb5ea31da2269e5bfdfce1ff7091e6913dbd0dd20fb33feea7763722c7a0f33fb577fde74713f7203aa705503effbf2a101907c4c5965827dff82c2c3296ba3a7791aa9bff0e3b5b703be62c719d887fe2d937eccaabeeabc903effc7cc2c782c5a7605c2a5dff93b819463183162366d23ff2f8841180282a55657287fe6ef1ba675afbebb7a43cffcfd081a441ba9901fd551ffa371de719b8867885558bff4e5dffdeeb93a59919267feab619e74aee39a2de81affd7370aab4cc25e8d3cd41ffb1f008f85e0d7d192c23bff6abc84bfb5cb6d3f63c07fee2e305acd14ee3ad44a8ffddffc2fca8a97044bd289ffbf328fe9db94de011cddbff84a3be3a7f05e9f4827c7ff1575cdd2b0fccf8f6aa0ffe42aa66909d2d20be28f9ffcb396b182a4d727ce3efbff9c139c54cf14214eaa507ff4319d7b415b139dabbc8ffe9b7b1228061b6191df31ffd6049318191e25232bd33ffb10c1099a19765595d54
private def eighth2_2 (k : ℕ) : ℕ := if k < 3 then 0x7fa90d8e3656aa2830167b2ff55bef8e30026b1ca5a70dfeb2b1fa969a5c042b4b0dbfd73a4a60821e19d429eed7fb037beb2039eabd2db942ff63ebf8ce7fdef470ce64dfecebd373e13d6c32cea933fdab1d96ce7878646e75617fb7132b754b309d7f32574ff717b6f22adced94fb2919fee98d5c760164811b4182bfde020504c3224f0fa93cc7fbd9fd0455802abe6b6f1eff7e6d53822b0d1ba567b01ff032259b43d7a8d1fb6583fe12acb1ce35a80d4670c57fc3dda917ed500d449d74aff8ac19df0cb2620cdac521ff1b7c1f3109fb421abca0bfe42c29c263d910cb6af4c7fc9ccb213696a777552d52ff967846d39908eaf724db9ff329a9de719f1f0ba36bfbfe7061f1aaeb79a878618b7fcf6ce78ec81a1c89fa9acffa19146f0dbb81411a0585ff487dc7939ad6d887f82e3fe9b8a9637da51f74b19967fd4be4611a4dfaa60bfe26ffac0c97701abece1047211ff5d258eb63d5b2a3941873fec43c6f2dafbc75087a3b else 0x7f64aabe9ae6ea525f519bafece34093e3c5f9937362e5fda61184e4cbc1e8c90adabfb5f4ea28a7180ecbe22e57f6e4a5dcfc96d93a25a4bcfee14bfb3a5d4779eb196b9fdcbf2ce88e129963cee75bfbaa73fe3e8ab953b0d1047f779b61f7153e5d89924e6fef3c6b4329fe7cee611821fdf099a05ff7b09ee1dd123fbf3245ee660e69782af4e7f809dc55197fdcf16c9f0eff05a428c0df141c08241e9fe1405e3ce450198109e8fbfc395f97ab6123447c64057f895182509fbf37253d008ff16e44ddff840ac8b7c701fe363782fa0779fa3d006c3fc7d257d3b10c35fd65c4c7f91b69395fe75ab3a74464ff278718ebd24eca710dd69fe572e68cb93a4a2deac13bfcbe75e5c7280d909f8c647f99ccf3f40d43b124c8102ff378c7fa1641d1a7f91ca9fe76ea80ed613c9d718363bfcfd50a905ac04d2c217057fa1949e6dafacf95ca262eff46f4781ebadc18c8597e1fe956bb7cc17b82b86eb483fd39b5a0310742a43d9a18
private def eighth0_4 (k : ℕ) : ℕ := if k < 2 then eighth0_2 k else eighth2_2 k
private def eighth4_2 (k : ℕ) : ℕ := if k < 5 then 0x7f0ca2e7246ddb4ab5b91c2fe1f5e49aa2a5faba08edfdfc4ad9f1e9827d88fd53673f8adc76fb35ebbf00216627f18b6792b82dfc9ebf41dcfe375e3bf844363dbdf331dfc7a8b712bd922c411f247bf90c8d9fd6e4298a1ee21d7f247ba4eee24becd0f2ccefe4ec15e148aefd5bded6f9fca90348c1d11421d7b819bf968e072286a8893553ea87f2ff2632bdf9cdd7931b2afe6587a191d51ab9037bc2dfcd6415c0177b2d39fbf1ebf9c2bfadb4cf5a88a41f3c7f3b1aacd02f20f11948ca2fe7bb0f863bd1b72eebcb19fd02458f02666d001ec4d8bfa1a2b1b0c10ecb82d3dc27f45f47af9ea54563bf637efe913d54dea9d744a720f6dfd2d0fc69dd3f4c912b8633fa6f228441708a974ebdbb7f507fc6f7941fe8b4f3314fea62ca9b7d722df0c89499fd569fe86ea4ffe2956a603fac1a5b4eb93c136dedb317f5abc8a481cfa28b22a3a0feba7eea055df5619bb3ec1fd7ef5dad17c8fb1c791c23fb11b47a24a4b3c104e43b else 0x7ea1039af5a08f1c18f41ecfd4958b0032bde2d4dda941faa140cc895cf6863199ec3f55f79619fbb70e5b1a5957eaf894312b9a57ea4363defd663cef3622776a41cefe5fadabb26a686f410750c0fbf5d1d1c8d9f75b1586fae37ebdc0c5ccecbfd63e3d454fd8284df37bed79776717a9fb12fcd995ed69bc763ee53f641b8d03aa990075b89c17ecbaa1a5f31d529f0078c2fd9e306e960cc89a27e1811fb4a05c2a3e0fb5d6660553f6af2e32bae8246feb1ce57ed9453834ba96dab9a9192fdb93f8c3f8e342c5cba97dfb7fd5bfdda3db41b1c3df3f71a31acd5b6d8bd26776c7ee69216e8f7bbbcfaee88afdd3b2278345ab2ef5dc305fbb46cb0117ebb14cca2fa3f782c2fc8830bf5389db497ef390ae479e2d6f226c8e0fded883010c0b174aed4ee9fbe7ca72ced545afad4fb5bf7e8e1e151b0f4a26ff9717f0040f64cac17ea7173256fe06c195f821cdffb50df45fc19eee8663a21cb52702c3f84c8e1c33fa68f6433476
private def eighth6_2 (k : ℕ) : ℕ := if k < 7 then 0x7e21dd7299872fe7d5c69ccfc4c443d1b64207394ddb4df8a987b5de3c24a8ac1119bf174e6f9696ef12c7034947e32d2f384ce544450847fafc6e0854a9c067cd4d69b75f8ecc20dd00d293b4ac5b83f1fabff5c83b59cc0a20097e437a9bfaec72744cb5ca6fc8f30b621c48ae4cb2308df92ec4ef4923537d85228abf27e29f0b580f1817560b27e53d461b5d82d3230292e0fcafbd4d0f623b30f776601f96f9031916c721d02096f3f2ff2499213350ea8f88ad7e63e03a9f935afbd8800fafccfae055ea4b3984fb4af1f9af23acb10fa30ee9c900bf37daf9f7bc519329381907e739e1cd2313ec63fec806fcef02cb5bbd1b0598cae3df9ed7f397085fb132d8af9bf3f9cab5b65907ca81beae7e830dfe97dca30a88d656afd0dbb8bb30eabad7b44595fa2aa2b158b2b695d8e38abf473758f42f21cd618ee1c7e922fd66addd728ac3c7cafd2bd833713a9efd8868011fa668deeb2faf3df816dffbf4eaafe114a2d42fab9af6 else 0x7d8f44097457a9247b98160fb2847f7a3dea44e350a5a1f663fc5b1873f8fec3e50d3eceeaad1079dc3ded2d5197da2a6c5b2b656430bbbc18fb4ee6b297aef25b7bdb2d5f6b0ec52f3e6436aff4e6c3ed87efbeb776e615873a757db5bc026ab96e09a3d945afb74ea689316529dd27b8d5f6fca635131721ec08cc63bee1ec8696fd6e45dd77d9b7dc883b3d6ebcf5e6d26900fb9a53022313caf0d45fee9f74729d2bfd8ff363394b1beeb33474240eec2798eba17ddafdce61ad9dbbdebaffefbbf20683454828d7c6cbbdf79076fe0361b1c1725c72bef453383464545b9c643247ded2a46a53b668904385d2fbe352841341fdf89162875f7d88d89a666d620d56cb4befd4c53cc7adcdd496abf57dff09116bb528ebde57394fc06e93f6c101fe3178a941f81f6d493139b339bab87ebf061e94818c1830a50ced17e109a23af254011871e7b8fc29e4844acaeef4244f221f8651610ebe2a8497b83853f0ec9f4e297526ac959de3
private def eighth4_4 (k : ℕ) : ℕ := if k < 6 then eighth4_2 k else eighth6_2 k
private def eighth0_8 (k : ℕ) : ℕ := if k < 4 then eighth0_4 k else eighth4_4 k
private def eighth8_2 (k : ℕ) : ℕ := if k < 9 then 0x7ce94dfabd71f8628c77e94f9dd90e627f23ad30c4ddb9f3d0f8698466fcc36ea97abe7cd7783778ca2aee976fc7cff1af507cddf1f2f18086fa09044fec56df1d89c86d5f427922412da95c81ae9d2be87a10bff25b93810c70e47d149ad4adf55c1681c3ea0fa33dd7dbddefbc6f08889df47cf75972922d3c279a6e3e92440d795768e8f490dde7d29cd8c6cd83aea99ed264fa5e1c552e349c417f7ed85f4d127d4f678cc1a5656edbe9cc076165e599c47f865a7d3eb30f30fe3c5b28b3716fa87c0bc2e35c42da99e6ddf5242362afe980488ead62bea7163f5e5a0df5041957b7d534b50168f27284b750dcfab0ca990e04827051916edf575e9cf6ecf65644d6286beb14562f13d0847d28622a7d679642695abb94b6b5d74fad939d27d16c98542e7a71f5c67ae8c1c53802a4cb50bebb4dda86d0b956481e61f7d7b93d9a4e0898253c28bafb010e4f8a460d04229ad9df615d67cf634735054153a3ec52f9feeb96055885ca8d else 0x7c3014de02f580eb5ccceb4f86c52081bce2573e250b81f0f0e180b66600475ce2c7be212179131ebd22acdaa777c4848b9bc32f84aa4476eef89c936d681272107b0b6d1f15117a349fb167eb92ab53e2d1ea7ee40b9db2b27c1f7c602feb972e67bc6df49c4f8cc3b778fa42e646a42ae9f1b01b00cfa12bad3c93053e38f57c508e10a825c06447c77ca64d548109e5b89b64f8fb4a092cebd24a698776df20deb5eab7b5e0c7fa1c03e44a5eeec75b36f9a3f1b97c8f1816e7338321c0eb8a0f929bf0538fcf655bde088df26a8882ff0c0c1cd1bc543e502ff88c139b117038a847ca618f36d00997a944f70ef9579a4f0ba83b95b1d13fdf2c5f234a95886f5ff4ef3be5b939211353a0aa03a3057cbcccec362455d780de730f984dbca5b8cf8e894e5f05f320283b470c4fb1a8833f3e66d0b4755de07ade1a1757cd333f34181a31da39fb06f9b1835b3e2aadd35953dddf3792a5f329bdfd96baa87be71e758c9cb118a11412b7
private def eighth10_2 (k : ℕ) : ℕ := if k < 11 then 0x7b63b5433778ffa84c8588ef6d4c44dff434cb5fb0b945edc42922def5c16d9f882abdbbd6d40f0ca16254328457b7e4c44f130fb0627e73fcf709cc3ddf5ee2d47346835ee2decd761b9ee6ba7770f3dc905c4b53b77927e6441f7b9897196500a3f91d873b4f73e3bcb0ee4edd67a7bcedee967fb6458930c0883f0abdd60e98a14a88ec92fb2b67bb295b05afec24e2558286f77212d53584cd8b3a8d16deefde17f08c866ebe528f5bde2f147c8e784b188533ff7bcc47f9ca497a1ed2fa704f7a5513c590191d84850f5def6411f1e60db7539daf333defadca39477f2e1cc1e157be5ade5d9102fe9d9dd606f7d7f6e0dd45b4678545de5efc910cfd447e697be67cf3dfc4418172bd8e429dbdfb7bfec764dc9d4fa2fd54ef4f80a03a384769840d1d0825f02cddda86e539b808c4d7be08b4299ee7172d69dd85d7c179467595ff6b464a0ac0f83b77656f07cf4388f47b5f08f78d46df9e3f3157458be14fdf72461ae54b1eb71a else 0x7a844eae4a80e9a1c5ecc8af51726909600030ef0d9f35ea4b4ca349e52a7436941b3d4d0727ccafffae63699117aa144bc5855fe0766b5382f550ecdd905796c920ffbf5eabe8d9a8782560569a524bd5b65d1cf511b3689d68ae7abdef2577cd36f43dee0faf58a1bd7cdd9a2b373b5a89eb309fda96ebd0389bea34bd699ea2b7102232bb437527ada4dd7fa34214ab1389e8f5c2b35c08794be3dfd7691eba1831d1abab2221c04833d77b191be16e871b2318577af660c25f8c732ba011556f5fab347579775127e38039ec11371c706e5f30a3c472bd859e9635ed6409a771f967b1227d35696d77205d35e6f6321b773018472723aa229ec7fbb93b09779738f2f39bd9365a7877f084644674d57b2da2f9bcdd9c58cb46fe2f668ebc9647880180b58f95eced103eaf02627c9b0e13bda106bd3320122933a31157b48d2249ebf454430dcd22f69f241c24e2880c6c9bd35ed5934d9fae148c2f3285ebdae81ced092c67a0b1e47d
private def eighth8_4 (k : ℕ) : ℕ := if k < 10 then eighth8_2 k else eighth10_2 k
private def eighth12_2 (k : ℕ) : ℕ := if k < 13 then 0x799203924c621440a5214aaf333bd873698f1b6caeeba5e686d5130ae72383164fa0bcd4c38abaa74e59836606a79b1543565ddd4bbf59f6c0f37239488ed138cd39673b9e70381873479b45cbbabe3bce44fb6d52e8890943ca6c79d059c792b0a6bba6d9638f3b01ede73a745e7ef0c1d1e77f01914ebb527975670fbcf3b6534a2cb3a2863bd4d79ef1435b018e6155ca12d2f3ed6e22b6c27d9663b67bde7f954e52b53126a6d19713d02f75699a2198bd4065e57a0d836cc9aeb11c7249d28f42a26ef8683a75abf9d4f9e8727b375566836e6299d3bd1212b75ac04952d99f8197a2ba75a196f99d69618720f466491f6e1c41c51dc0135e8ea743d11c83b0a7b67623d21086c3befe4e6fe3e74e7a497feb07ca3a91ca25f48f4a1d48d55a59d4e0388eb5e9613fac5f25ee1a5598e23d2fd86c02d660ade242b127a670d0d2ba9add4a5fd278f4dcc9148237bde1cd12c9de9d6dd3bf636173aeed5943d3e82ad8c5bb4bb058f171 else 0x788cf94c1e5080880bce306f12ad3bd31ddc3188b237e5e277572bdaaae0b100f9a9bc531e887232f43d09cc02078ae9fb00f303bad663df7af16dfb50488ec6abfe6c4ede2fd5be3445bf23249832b3c63d5d0e19c4990e3daeb178cffba2a873a4cb7d2c7caf1b08df65d7b48a0865ae3de38236ac10e7f2c44dc2903c7467d8eb9d0a28a1139a878f10d0f563d501ca9528d6f1f28b865fe22d581c52e95e405e7344cc34d9f01b0aebc84d4965782fcd439c44ba7911d3e1b2a807d6516f9b8f233f3d79af9150c8df9b25e4886d2abc5c7e5627483cbc951bff039cbca1abc3bb57932500585d36148ee127daf274c6c1b60577df7a88b19e509c83edc4e2c974507d63ca53e08e53ff8c83aeb73679528166c5f0359d1284f8cf2b5041cb47589207e64521e589f820e190d64c455b4dbcb53aaa08cfa65f50c6f94797267f1974cfe25c969694f2f4abc0f5f8e1ba32d8ab5e608fc81b9ac08041c36183cc511d891c223dd29521af
private def eighth14_2 (k : ℕ) : ℕ := if k < 15 then 0x7775581caf6bfef386e2aa8eefcb986541bd964ef71625de1d733927b50fbd4e075cbbc82c1edb1b02cdf88e62f77994f111641add9f385224ef448290232e6ecb77673a5deacbb893fac7bfe65ea8f3bda0befbc8fb3699d9f03977bcfc3f354399dd5c64010ef8bb80259299e9f64bc1cddf3adc941df6b7cc60a0b03bebc6d5374b37c3fc0e86277e05f910aa4e424f3fdf6eefd259b10938eb27961a1b9dfc7d6021678aab1f8631a3bfd5cc45b7c555758abbde780378f0c22840994bf203cf0186770a1adbd00aa38a91e053a77c337083843a6d19bc0ecdb2501ea8fa264b4e778264848b52d6cff0a968d8f05de115ec1a43427b18181e0de50ac35ab5c8b8b0cdebc201994530157dfa5cfaa57848cd836abe8beea5ffce0f0a2c6760d6c1b5b825b9ede167d13c94ba6f103cc859bc31405fb8cdb283f13955e786b088b979d63a0e778488f0e717668606c091b576731e1f028d87f27d629e95ea0bc424209ed0dc97f59c49f6 else 0x764b4b22c7ae1dc4b72a740eca9c4f28214da2462cb77dd979d4ff5e8341a2ccfae6bb3401bb167a8c1bea0e4b976718d1be2b81f25c5417a6ecf62461358f9b643a282e9da124acfdcbc775b96fae13b470752cd130f53f77ffa5769786052611f7f063094a4ed41f1a47b09db9d3c8fe75daa99c320cf9913927d15e3b59e859cd1571805ca244076bd35c725641893891e540ed8d2c8d9061bccb044b039db3fc8c89814f066f40b5b3b6ca4c471413594846054576e29c4aa176da719319bd8edd7d4ee0dbc6389a52eac1dbd4d036db8555cec96d38bb7f3c872aeb34ec7fb9a877707b9788840d6e217922b4ee21ea97e5a2972bb218c09dc68b220e99706674fd4b2bb91af968204c05ade1c9dc772c8d39f4f522551c9460aee6b6d5d651d2a0e947f751dcfb6e2b89a47ff664d6cabba3fde71522b343e874b0e7751177830116b8ee14ef18eeb45d1133d12a1bb025431dd8d03fc384ebe245770b83bb6276d998478c1e1be307
private def eighth12_4 (k : ℕ) : ℕ := if k < 14 then eighth12_2 k else eighth14_2 k
private def eighth8_8 (k : ℕ) : ℕ := if k < 12 then eighth8_4 k else eighth12_4 k
private def eighth0_16 (k : ℕ) : ℕ := if k < 8 then eighth0_8 k else eighth8_8 k
private def eighth16_2 (k : ℕ) : ℕ := if k < 17 then 0x750f005461ae6c9845ff926ea3251c073920c048bcea31d48d33a16cc95970a47cf0ba96b63630ea47c152832977537876be9c6759dd2daf30ea833bcd1e96c5f689caf35d52ebf6fbb4d2f998e572bbaaadea5d27d613f8936e62755fc6354e8afa8e9c92ee8ead3953110f39ab5d1c1ec5d5cf29d3bfa6f5dfd561053abee2e51114fd4bcce0eee7587bc97bcb665579163ce6eb235dbaba6f261b973fe7dd66e726a860b464c0d6071bad2c2e793cd1585ce78e7175af6a7a8dac69aecad4732eb729538e42a3717f0793b5d70c98d1cd725939e8fca5bae67ea1181bfd7fc36b8c375d6cfc5478939c671d90eeebc13b7ab0be2b4e5f4edadd7a99ca807d4a0fc76084cbafa160571d9f2c007a673275fdec5f9d309f69a2a84f0ec0f504f9c5b1381ae6dccdd8457d8c5a66f717afae9c3b0d89088b489ef4409e0107624c0316e5cf97a00114a4ec5cd3877ce5a0bc8aa9f3dd8e03b1e9dd65aea47cd92bb20d79e651a8c515f98408 else 0x73c0a8779443935d218b168e796c14f8da06d15cd6e05dcf58518483dea0a62b22a8b9f061d19c8cf54236fec3f73eb6e6da5c3136798b4a2ee7ec297ffb56a06104d672dd002da675edba774963669ba05a9fd657b248caffa0dd7415ece26ea5fa4a9fe42e4e84102a0b45d6333badb491d0ac451094953bef7ff1303a1ace5eb3a5711be7fb079744023bbb88caeec143de38e8954c7d62086122f6e7b51d1549117a3dc79f2c32ae83a2fcee87c6bb7eefe25cab746a12df79435fbf4e5fed8e8e906e2060ae2012cf5e21d1fbbe14bc51c94992ea1f3a44ab8dcb49c1176b2c7097493ba33d2d212d0ccc7540e93c319afa97dc52de96d41d2a1cba0bea4e74fdbdc0f3a596441c1df3d83e26a4ab74bd199f138c9a88c220888e98ecc74f281d12c14d1c6dd346b9553cd4835b7db1a03a6df8f797f7b722f34935274e63107b6226f1aafd4afee9e0d73cf95a71630be97f1d3ea86cc7a6d6dc61f5842ba8269a29b927358856b516
private def eighth18_2 (k : ℕ) : ℕ := if k < 19 then 0x7260771b0d190591e8959eee4d77a90dea3ffdb46c49f5c9dbfc321eb556e13e471b39411e33738891af387d695728d75571e8f13367f60e3ce53153b97ec8c38f7d892a5ca8f67dd6be7883da6b30fb95782d3417200e2169f08372ba2ce9c8e2cd97f6f6b3ee58a9f817dc3eaf027c94d5cb41b8abdbe3432e84b094b96dc41401b5315826da57372e69db776a55e356cd2ac0e5e35db1c688552ab388035cbf2ee2f70339db4af5748b983e1e7f9f8b8795d84ed97312c7a4be0f6428f511d7ae63b8e139b60462504eed21cca307fad923638aef1c69b999dc4185bd3f16774a8f8733eaa966111dd11f2327f4e6933070960f2ad817d2ef5cd5205a1760083e48a5f7bb9afb3131665ebc1a0bf3b6736a46714d66f3076a1c1f6e6ea4492a7f327b569d7e11cdffe6b7555f133703754cb9c5664f3340bfa738aea0673959b1a9ca2af87fac7e1ee740ca441a2671027a33a89ceacaad1355be0e5b2e1d3b9daf5e8798ee5e184944a4 else 0x70eea28e1d623a5073108c0e1f4e9f73e930f9ec113879c4190c384ffc1c5769fe843889066283800848f814877711dd22003f4fe4d91988aee253263d2d6260d5a117ec5c4d53f012ccc4679e26e9e38a0840256d20dd47f4e44d714cbbeb4a58dbcdc709222e2b0d6e75ba1ee91868ad65c5905a7592dcbf0996460038b7deb3fdf0b3e0f5bf936717b5fd30050a71dfebe564e30dfbbbfe623ed75829ca5c64a5e221768c1aec15685b8cf166910e7363b0d958f871a9bdba60bb9ce4478a9b8e36a9481a0f58cf25346d01c7034993fc40b71fc87d64b8e62b133d55adcc834465f71d7d584d1a7214d4eaae38e3c6a0ff25133a7fad815d1c7bb1c593010fc97191fdf38fd1ca44679e63655a64947205a715e46064971a0108ce42220fbc2fb0b2f40f335dc871d6004ea840a8397a5d3913eb0e0538261588358ed723332515585ecee1f8d71ce47d143f09982b2386fc2adc9277618a13d7548a28bb0b92a96426823e9ed0489e16
private def eighth16_4 (k : ℕ) : ℕ := if k < 18 then eighth16_2 k else eighth18_2 k
private def eighth20_2 (k : ℕ) : ℕ := if k < 21 then 0x6f6b63d859e5438a87c3910deef816695cc1321230ccf5be1065085d4c69bfab544737c836c222a98101192962c6f9cbd795b36bacd184ea58df521241bef36566ae03d2dbed541e963073e901f55d037e0c9c2a6efba242ac04d46fcdd24145cd84af8ad2ee6dfb4195b8f62d5f2fbf5dedbf990b296b6c6ffd606e5db7f93a4b43628dfd5c816236ffea211d314832b36d295ee01596778f3204f472dfbf1c05bc04fb133a074c61f9ab811884ce4aa921b157fd80702f2ccce7014d72ba9f300e07689599b974b528d958a1c11d60e4196479d2ac75bd3829b3b88cbcaee71b5b263705f72549026c2a6050becae0d6f1c5e70cd2f362304d1c1ddec6f33a0c3a58abc813841bc7f52e35f259aea2a6708f728b07c7823cfbe06bee136cf80f9757a68ac95951c29d627a3a6e1034aba7553859a29263c7e24b38be75170bf2d52b1e84a1d5a532ace196224fb04183ed9bc47f1c35bc28f137f001d148129387165e3017b61a47d3a2a0 else 0x6dd6f6b0cfa7605025cf412dbc7b8224d1a5ac52494321b7c2f4d3ac8c5a8f375aa1b6fecd0dcf25d2c3b32dff46e0a72c4c11338b218a8f0adc2e8e5fa96011bd8ddd319b8905d716a08b70748ac2a371871a4ea09d1756b2a0056e3daaf7c3184ca4c911518dc94dccb52dbf9a8f5ae1f1b95cb64c2471df55e8bd15b731f43fb22abcaaac81a7e6e709f2a3d74b92d53b4e58dcfaa3262dffe074b3ade11ba27fee5ce9b74cde159a2b74b54ce6b21a4bf5271b836ea34f3cc1d90e03ea6b076dd5fe131732c2ffdece3635baf236c10349b73c1c7e16376493416d8819e29ce71166ed5bb100bfbb0f139e922cddc496aeaed6a7d89fe3479bbbb5d61057ede8b41d684377daf892701d40df565ec46f07e28501ac273fd7650fade28c35fc1b0e338cb07349bc837249c0c80c9fa0a84b3796a9961a464e01410923c6f39c57cb2e64535d07d6dade8c6706e0ceaae5e95d791bd4a74ffc989d73bef8689b7af8158df2a533ed2c66a9
private def eighth22_2 (k : ℕ) : ℕ := if k < 23 then 0x6c319974ce96b471dd75822d87e0abae99ed789ba87bc1b131b46708ec555fc2551ab62ce8549945e922c7b46a36c67300b419cf8eb1524dfad8e9167ed6e63401e82eaa9b2078914b0f016c5483aed36479a8e0027685686ecd6b6c9c83c3642bd93f2d7aa8cd9539c75a8f998bd69bc1edb2dc52073852aafb93815cb6622b4be6f7e6eef1393716cd1947c5133ed11c5aa690d9bd9c5daa604528211d425b3b00ebb5d73c22e35a5e6b67c9a7deaae230a4a3a0766d0662154cf98447b8a6274da2715f57853067db6f395db482beae842a5c629dc3cf3696e813bcf24a7d3895ef76d3aec6dc528d8107ede908da9008fc02e48d196be85f9b554615eb6155a8ebabbb7b6b113fd242809c416c99f06d6f336550ea2265026d2e0daf875308d298eaa997d901b624f64aa2eba96c9599ad36cb1e29fb788e2a56a611d6da336dbb0f59bef80e50fcdb605a52ad60b53520b7f21b6f47cf1a0cc05d970b94836e5068a32dc7b21cb066d8 else 0x6a7b8d1e4b9ca8c2eede764d512fafad772fd785625ffdaa5da704452a8fc8df9b83b552a8f459731c061f402b96ab335f3c74ae9ab40afde0d5822bc38abff76980b2411ab3bc6c890d52a6f596f55356e64b22d81a8d45c642dc6aea9cf7e12b303eb02bfa6d5f0d8d85c6d5e40f781741ac18df02e76116cc9133693589ff7a7df58f9f9ebefbe6b21c2086c732030958c05cd65f01f50739d6a8a5e0985acf4ef2ae6f79c55fff2b535a5793c43aa215c020fc206b58a5036506fb920aa07bad6cca6d5974bc487ad45a29adcff6b8d0a67fb810e5fbb5c0d1e68bd9ddb31b2ceff6b8f45c6ef8e9e6a31796d0d739c7366a5b35a2c54680daea9f52588b3bef34b487235dc09687828e762c32de396bc5a431598a6129483a92cd7a662d42fdb99ebc2040a9af82e9ea96f0e8cae52e5bb5f71fb13eaf6c0473b44b46bfbc0211967e1e9a8264dcd812796be925496684e322db05ad482270e0f51569bddb61214b02a03ff36c92e7f7
private def eighth20_4 (k : ℕ) : ℕ := if k < 22 then eighth20_2 k else eighth22_2 k
private def eighth16_8 (k : ℕ) : ℕ := if k < 20 then eighth16_4 k else eighth20_4 k
private def eighth24_2 (k : ℕ) : ℕ := if k < 25 then 0x68b51539db949821f0c026cd1870fd265fc09856af273da347da3a4106fcd0c63fcc34703094b2778b21b69d21668eec7b922bd3b2d23b8e40d1fa547a77168e341b88089a42e22d485810266887340b48cf1902335908da606e9f6928397e1d02da6617a4248d26d179c2f4cb81da6d6c2da513683ea3f263b29dda8ab4a9922121ea464610c03f469616a655b2540a0b5ec5e0d2df58f0c41ba4e96ae6cb9a5f7a9eb2f55e15edd1d2534c6123605f5c385bbbab76699a5a4b95e7772f2954d76d3511831bb11d5527b929f1a6dae74d5adec83e7499e5b4e271bd3ac1e9072a3eab169d3090dae2588ccb61efccd3c25518e9faa6a1da3e821a7bd1fd8fa4fcb880e8867b4feb0a53fcd39342ddf53d6a0b7688acea2bcc9ac2c76d4330f6077099aaa0d4465da89e530282517c055570e8351acedca8b5a3f2771198d6a43a299c384537f9c10c6ad4a346c2d9056e296464d95a97e803f08c85c0282e4db3536cc521d4346067d8c3a2 else 0x66de77dc48b253c6ea2c026cddad542f904c34dc7c68e99bf165bb5811dd661449783385a221e0eb84ece4f8e45671a2b1facbfbde1bc82ea2ce521c040756db2f12e7fd59cdfb3a8ceb8b8e4482aca33a363ebd501aae2fd6eaff67559ec9d40d80a837230c6cec8e3803ead2eb620c49d99dcd02e7e63f5042a91d45b3c105db6848e42b01349c16790d2b6125c62b56bc73eacf3f2b6e5a2de8af0b8bde59eb952e63c40da8ab9d3a1b3de87de535f286c77f2d8067cbc6bfe2beddb4685c24ccfb4f38563ade2045a425959fa4a3120bcc74ee9f014333fbe9e26293bc8f36bc80268067ac2e7afa54290ac4b0d02a3b7cb3dda35ed81fd4da08ef2da2dbf0dbb9dbe1db4192bd575f26d0f9ae29a16840ee9aeb2815830c72224d09f030bf2763620a6c15e5a17841ae191cedf53763a3b4364da5814ebc261de863a687b2223deb68955738157ed11349eb1665c49fe6146ada2608efde36ae161a7b2aab4534f408c4f03bb5d13fa8
private def eighth26_2 (k : ℕ) : ℕ := if k < 27 then 0x64f7fd97c3f3b2af679eb2eca0edc4971d329b1434be01945b6b32403ddf431a92ba329321c75894d86a54ca3b76535a86a84230c24945ee2eca8a12bee219a5c28e4cd79955199b3807b439deecce5b2b1dfc91cdbad54f66512f657314cee65b5309e134312cb04cc449d6c625c74796ad9646ce2f6e68196415b2d4b2d07e857affc1ddc8a4d9865b0429f0706004904de86acb7f088eefe6fd0ef3a97b5973b080ec8d2c97e63946b32eefde98fae83755c32edf65ed31b52926a43f7cbd7a2cbf8c75272e4ea79f50150d982e46bae920b551680985b30d5de28aeb27287e0e7376629e1ebb6722e1f1ffaa14cc7208440d2ff922134bb9d9920899dc3ab248aa499d3332b9e5db01a445de0fa41f6666531d3f661b709287490cceacb18f32ea481f78eed19a11d021e81bd358a0b0dab349bf48560d639f59251d366a285247b5f8fa94a9c39ccd630f86a712383bb898b599b0219b281c920d4c31803b367c08fe70e816788ebcc6 else 0x6301f170b447c9f1e0eb552c623bac7d38e5135ea513158c8716155edc6e805d6530b198d4ea308ca90f3a64d4063418a506915338ca5dda3ac6a2cdf1a5efcb8d60912798d84ff3408d14c6253030931b88a662d319823b3f9b066380e5f63f430298f67d430c721669429704bb3e759c018e81f31cfb33498acb4889b1d8213690d8918d357052463c0043b21bb1b790428feec79f846146cd5b0edfdbbd98f7df1342d56ff7a2666aeb1f79947df2819d240acc6e63fee4f82143ea88cfe2b74c81d270b3289997d664dc299078f8de2e333bd8cef3e9b216f286aebdfc29d9618a4643d880674986865fffeae4c89a4e446d1cba35f000ffd9173098024c0e2caa8441bb2362cdfa93b43d882d58af647bed3f788006ce0f49bf0c916f9bfc32351c9389df89926c227fd05a737e57222a3255483f8b5029d2e0ec3a564ba147cafe686041386e34c99329304d8e752d018597193644343891b2ebd795cafb274449324c7f69ea0cd490
private def eighth24_4 (k : ℕ) : ℕ := if k < 26 then eighth24_2 k else eighth26_2 k
private def eighth28_2 (k : ℕ) : ℕ := if k < 29 then 0x60fca0d2252593e9480ea30c21a0b6e26670f9cb0a451584759b789ae78f72de53d3b096e2235f07f34e2dc1079613e1df037b1c2738ac3122c29ce7b3e48147c1e6e17ad857b180d320aded15243a4b0b78a35d2b198a2dd323bf617f5f125bf250ab4d47ea0c31f4bed9ecad1db65d297d867fa4617c5b98ec0658fb30d8143b35432a0c22b278461c064105158639196fadf8c3a137cae6ade2d18768b3d87833fd4c1c4310a1bbece30f8801f745d7d692a1f9df62012cc1fc6e4204b2450d8c422aafb97d356504bf7b758885e9c6dec52852b8bfceb118cdce903741a8e775da36241b8ff66f0123b2c9acc6c4a3a52fd8541e476d4f3a98987a19844d7d5dd8558cdb138fd349ba954edb750253628208a0bfe4804d45d5eb0c524261818ea847fb38c7098a8866a9fad0d2de74d04cb1590e3dbc3b0f3282ad24162c21b7e5bb54dbd9a430a8c5a42d6515233e27296d1b58b88385d9d420ab026126b317900d62a2e8169d0f6897 else 0x5ee85b81d65ab03179b71debdf26da29d13dc7448e05ed7c2839ddb3b837df83b3bbaf8d7139c5a6658c0a75fde5f2bb2c503900af89b2dc8cbe78fed65f8bc61df09a7717d352195a8827d38a9bd712faf06d9867b644589c57bb5f6ecf5372c32adf7e09156beff1a8bec49b81776fe8817e411e27c77d075b7512c7afd07f0f606d0c36c3519945fb1b103be2178bf586548abf84c07089cbbdb5eb04cd57f4c2eeec1f0c12282aa7eaff1d9c6ae2ee131b9398b55ff457aca42860b127e47dac009f031c73ca671125a21d80565345da999359a0ddf5301316eadca5f4c89b741a46036c32507bec4eb34c2c06c08ea97d7ca6e06667715cd815f8a88e60c034fcf8f0ab03436676af597510af694c6078f343f04e5a28a3e36e0c112ec01cb2725e860821858267d4144b1a77722b95ff30553827ea8bfda685e161560bae7e089dced8b7301370c196b76d1d1efdfabcb819d836f2f45033a21b14de0eeb0761c17ff2edba42f7c1c4
private def eighth30_2 (k : ℕ) : ℕ := if k < 31 then 0x5cc57393eee98409b1f9852b9ad8569004d8e27e756f8d73a039032382a6dd88edf4ae7cab1c0f32836cce76cca5d0a9a99d625134f4777336ba37b6ca8b6ac8dec0f347974b462670b37da94eb52c2ae9f291b51a51a008cc80505d4f883b3d28fac76e1af5abac1754dcd1947fd7142e7d75c7a5e3d6ec27f028d8a92ec18a58608ec777144838c5d943c4d9f412367531df50bb4ac09dcdac99cb524eae976da02cfbac4b168c31d952ee3cebe06e4c2573f3a35f5dd8b6a69b3ac148fcdb4f0bbd39865dc87f91fa99823d77eb7881792019a9d3de37af05f6372166b560dc9f1005e1cf71bf37e77feb14f25abc5bfc5190528b100cb25a978fc065062fee8f7fe2b36af2800ae9eabc97a92921245e60fd838e2a68ef81d9098bce3ec0cc72b70a904882397a0bab94586b9a9dc8aa352f49ee0f7f2fa49e4ba8da45ea4c9b3752c2bace9a54a6bd6b6743a6ddac90d0e00f57b1a67a5c8e2521c3198a6af6bbe44d55f5dbc2b214c7 else 0x5a943d5e54dc57a220c562ab54bfb4964174983ac7e5196adee9b1952ba0efa959ecad64b9da5fc537529cdf7485adb297d11dd094ca9eca2eb5d9b7895af029f33b39fe16bfa2a2b8ece02a451b564ad881ae78304ea24ba9f0015b21dd9066183775031e838b667039cab3cf055f9024b56d148a2099fc461d91cc03adab5fde955f993cbacb4a25b68596cb486c478be9e7d6b6f3df2c2c40e471d00c5b16e2e08e287e6b9708b199cadce88a9d5515d121fe1bd65bae9ce682ceac226fb32d0b78049e0faa6edcb56709b96f46a5c3b4a7be9f0bc8292df1953392b6ea7c8b9e8d35bf4a7d2795dd56af764f16b80c436478b72c7150064f5705e601707aee7bc412d8c2e1485662edaf38987010745c3a7a056384cec66fdc404b897cb604e8c66d72c0e75d7175372ff42bbd1ee257fc2e37592c1c837d91e9c9bd25c8013542f9174ec3877e3eb922e17e6a494c9d897fcf9728b2a6279782d5ef59146ae5a106fdfff2c86a77878c
private def eighth28_4 (k : ℕ) : ℕ := if k < 30 then eighth28_2 k else eighth30_2 k
private def eighth24_8 (k : ℕ) : ℕ := if k < 28 then eighth24_4 k else eighth28_4 k
private def eighth16_16 (k : ℕ) : ℕ := if k < 24 then eighth16_8 k else eighth24_8 k
private def eighth0_32 (k : ℕ) : ℕ := if k < 16 then eighth0_16 k else eighth16_16 k
private def eighth32_2 (k : ℕ) : ℕ := if k < 33 then 0x58550f6bac0116e77da9f80b0ce7c362ab812830502d7561e5a587f541b10cc393bcac45c89fd845fe7e6362f83589db5b37bde22b0e4ac58cb15fad79586feb7a2c252696307d16a3ab11a0434ecd6ac6a07463837d222491e13a58e625519ed8641c24fb324b1f07152cebd4f98a3afedd6429224c5e7192aee2fd11ac8e2a86fea6b541e331f52592e5e19664f6a701f591f8b280c7694143fb7979955756549977be99ab30aea3c1c2cb2324be0f07ae1eb27df959765fde457653c49f8462cb310af63a75c8acaaff8d0966693046ecc94ee612d18cacd61e7ea5670c8f17598d059be2a73d16f480ed3aaea8b3a028e93c4b63f20c3843d6787ebfc008d383af2d3742cf9ef09235e200ba8559155a05bdadc166df3f2acdefcb42f33a17f7779cc3e13f2d68a5c9ea45d6adb1d87c0d2d1da3d54338e27f52a14c75a4d195feeaf725fb36d26ab4bdcf3434a0e364981ccfd69c2c96166637501fb98cd2d413cccfe779921165f626 else 0x5608426dfd8f1960d0e9666ac35b9715967ec214c85c7558b5cec6261c96d93677a12b2003abee47be6a7e1ae82565297aaee749a69ac00accacca49540ffdddf94e4ef2959deb951c85f0ec73e599e2b451a54bae4a0abd12fc57569cb7a85c3e7774f6aa37cad5e6ea0dd86c6aaefd2f495b06ce83db13dc536c5044ab6a164c9ee89054674c35256e6a2388d96d0e9a4c7256adf228fc5fcc053370dd68d5c2e0da5babf05ae2d8adbab8ef77cca0318834f54e055730572dea1c940b040c430ae85780b768ea627517ec455d54760147f00edd639a13abb3bdce7c68b7c43dd34245779d65afa7f9b13878563aaf185b7343bf99b85da310d5e7a06e0e7b251650f2df52bd8692b06e0e877aa26a6d57c31f92689cb8e9fcaa996afaad2d92bb7c0e7e3091d15f9ebf8f83fd02370133f3abfcf97bcad41f01a319e78580c32a6ff99b05fdd3a334b03cdde2d56fd1c27e4db1160c29f588c22e5a4785a972c216eaa3a59bdb6b932b3e
private def eighth34_2 (k : ℕ) : ℕ := if k < 35 then 0x53ae31310ac5c28a39e1d0aa782687142cd5594fde27a14f50d0165f5ad5b5d57b1da9f3984b99490ca45aca8e753fa29ecb634f2e486e3042a81a400acef6976aae0abfd50804b822d04854fda66c2aa19813eb341365a4d18e8a5445eedb3e5b295c9fc1bd6a8b1aff2b00eb92e304069551aef75be38c72a0514c7daa3f5039b3354bff5b3053054917fcde63a1c66055df36a948b7cb7c1c3c6908e957152dcd2e8cf0cfdea3260aeaa65052546ab2b97b451d8854dcdc9610e4785d339a96aa9df57380955f296f187bdd5409dd6ebc1deaa2556941aa8a9fea2b3bf758edc53b955280505419aa05a7677e5eaa758ddb6e5c74e21e0648955361633f8473b10c426f3aab020712ea26ea2b86cf7d5572f8ed1be75b2b5093976ab0b5b5902737423ca5fb8156617c7f5273bc68eba56aaad586a32ec93d043c5f3b955bdb81f63bc6c60c2c7954aba0bf545dbae105b636145578c0f981b63431203e268aafad26919d93f4546fb369 else 0x5147388c4c9fe8b126e14d4a2b542c48b8231b4af85be145b81c554129df3c6aa70ca8c0b4d256654490e510cdb5194c90f9beecc65291c7bea3504aaabd07891952b8b9546edf9d4d5d3fd2dff182c28e76a3730e68e39432a6a151e2274024b5d54ceb6638aa3eaedd37ef007f75c29f8d48230da9cdeeab3f9d6be4a90e0660c123fdd1efd88f3522f52ee2d835f32f0e51c0a4852bdf6de6f8e067b87a14957571581f4ff6fe7ec11293489373612716c08f4946527c4bea1c0df2fad7699e0a51f046f64f6b2c21bfcb514a8ad559c73d87fa183e87295af2a2ce45e176c6274e752c912047551a3bd230b1d4a5b877247dc3497c0a68dbd4bbd87b8f06f9939caf495a981428bd8000812630cfaf5315a50dddad5898d293850a65183a010c517d81646c314cef6d75cdf84e41c650d9a9a778dab13efeb726ceb5b536204d719000328abb26baa6ea2983b58322c1467bafd4e2085d3ae7f3bdd9003d429cd9577c7cbd2278527db8
private def eighth32_4 (k : ℕ) : ℕ := if k < 34 then eighth32_2 k else eighth34_2 k
private def eighth36_2 (k : ℕ) : ℕ := if k < 37 then 0x4ed3b754a2c4b9ad9dec5289dcf05f58cf0bd3703dacb13bed2e58a3f88e2abb598827878893038a2f250b2b4dd4f22d3a99d97722fa4df4289e6d26405303af3c677bd0d3d293e239fb08e294942d1a7af04718b06877ef3050774f71bf2df1397e9aa0f9a0a9f0ae4d16dc914369d210253e648a4a927e0f4fd95a1c27d667d57c0d00186a2357c4fc079b0ef21dd342688a5c9fa841478f4693e5a07aea53f9f120afea3383f445616a7fdb2a68aada89b48b3045500f0302070222940274082a0453b41a606009d2556ad540d8d4a2df887bf3d5dea82824e4cc7a21188ddf3b1b7505d5af0c6e46e81cfb62c2a0e1d25edd5137a7357cf954211d150aa3447d4d03dbba84bfe2f1cd762bd9c6b3a850ab814cdb494e1a868adf2a17e063e9d6ddc2d8854021434a07534dc266bef325c82872feb65486ff46c59b0da50f975e60f458b2b9656d00a219d6808bd8ec84bc12769448175ea33db18c060bfdf2899e64a123bac300ed459e else 0x4c540e4db3eb48f01d059d498d0736d1af226193da08e531f188b52d658cb59c05fda64843d8934c3eb2f12e6494ca4aa41585fc034a9b9d98997193ba33eb585beda568133339a0e92f7ae93e625ca2670801a191cad2a06ad0b44cf516edfc060d03ceacd409a12556077beb2621f7a9cd3474ede8ae7772c6b32d292698a4a5829bc2ac1fa4b184d45542202bf9896afbe5f89ab2b7fcbccd763f4c1b92535b5837d49ebe21b5f71dda6c0b1620cb3e5701a62e534d9561abedb6225df0165a89b52bb2c1418d9dacf81e3536f55a06a4ba774ba10a9ba6e8a63702ff1aa226958534de53f5a5b7a48027dfd4ec9bf25e8bc97f0de38e3eea9383470bf74211ac43a32032710830bbfd64397f1ff6544e34ecfc0821fb436c4793c9c91a1b963f820744f120a93972c6e2e3afd5ba481f3da73847c7ac6051ec4fa4d894e846a5fcd66e59e0f363189d308452a5d2bb4339ddc953ab05bac95c23c441c5289a75ff45240a17278f8978e4
private def eighth38_2 (k : ℕ) : ℕ := if k < 39 then 0x49c8a01b01f20f509bf47be93ba5054b0b095e33b28f6d27c6b582b36bcb13ff8c4e250317de9a79738700005214a1aaf3f26352ae2547ad88945e57cb6ca5d7efec5f2b5290e96c06c6629c74cc78f252c0e4ec5395055b5b1ebb4a6c90ad3a640b03567888e950203bcc21fdf4966227012a55c0c0d2d3193dfaa2f92554edd0f5d6b00feb004184abe4432bc70ef541dc22a095a553c3bb261e2426128752b9c32ba170f2cab0e2141a57db64bf5e7d3eeb67e3854b0fc99d469fa99943a32a09648477b9a72b97c3ecb6112ce1ebe2dafb75703db4c8a5a667a69d376f78e9e9d554b6120ba8fa4b42a3d24d0296eade7fdbb0ad30e2c57052e26eb723279b9cc590763a5cf01c7d1d42d2730280e44bb249586ac436d506bac14978d186c33b9cd0036cda192f6b309fa3e865371c3ffe25f7849688202a3b7490ea74c034344c7f0fa239aff034982ef4dc90d4a23d2cd5ca130aebaa3289e321dfb2472261feff9c2e069c20673b20 else 0x4731d130b3f768fb2a9ef9e8e8d657809660dfe0352b891d6e461f76fe5149f8af71a3b836c9b890e43e2bc388c478546ddf0f981e65622b1e8f343acd1f039b9a78a7d011ebbc4b1fc43c0be8beb3f23e1e117790c35dde4c469f47d8906d1b2509bc5921a528fdab7cc59bdc40835112f92008926568258b627a30e9240b7542eac1ac6dec51004482badaad246f6f4ab63eec9080dc0f06d3bc6ccd446812154ae6c7074971cdaeacfa434f33267d6b162c27441c487e9e63d182b02c483d6ec9126a72eaa416d6c8def40d22a017fa389ad3011f964c245e5acc5827c31519c53f848d16264ef71ac3724b57e291cc18c4fefeaad8d07b58523eace42521995bdae56572487abf731583e714cf42894923f97b1e4301412772a469271306bf73e497395955852534d078bd07b8218f21f1a4b0e69976e2202747e1207497663736bdae2eb2ace6de9315edbdbcad12a17b7d375267e1dd1e88f6b6b6216c5a4da0a99ba25bd512c5e086
private def eighth36_4 (k : ℕ) : ℕ := if k < 38 then eighth36_2 k else eighth38_2 k
private def eighth32_8 (k : ℕ) : ℕ := if k < 36 then eighth32_4 k else eighth36_4 k
private def eighth40_2 (k : ℕ) : ℕ := if k < 41 then 0x449007c418cb86f1114459c894a7f2629a84d4204904a912e9d2f23f7272900e77b6a267d39fdc4a9d97b220c0944e4d71bbdc87b3c3f912fc89f4089f9cb6093099c5ee1143cbb6c652ed7d6b2bd9ba2922b5e66d9d67cd98156145397bf41ac64e4aaee43c08a9d3d005fa29b395ccb425158ef980f0f2d6f4fc23e8a2bc6dc9b7c5784f1517df5458df618f958cf5f2d426c28b461be012bb24ad5a838d516e08c5f3dabc46595c989a2e69ac7bdb69140886999c45e245563d6ae4b20e0ff0e8beea4d68b0b0a3ffb4032d183173370fe3a245670df42310b23e748dc991040696a46366977e55eb044e42dcb28c96d77bd29c3588875c5411981ad3896419305c92d41233ab413e5736fd9935272d468a624a0a2da462eeef2848d3eb36828b735d32ab31ad1ad139946a0a0aa9ef6cf52364a02e26e77d26f78b50e46de2f98df8887ba70054c08de6383402234019e83afbd1c20177b8f9ebe406e8ab5238e76735cd190d92ee933f else 0x41e3abbbe41f5617c87b71c83f26d11de0814bde1cb52d083afb2b6043b216bb3dac2112224065611826491bbf34239c7a9f2ad2c1055662c2849e908af700c1f4a993c390993194a440e0cc039bfd5213d20e82f8bc100d4645f2428fbabe11b69017806644e854a6235a9e8573d78c99dd0aea939753f499d3a4b27da1680b0f1f0bd7294c9e22342e584c33ca354f50baadaa85f5e1a7fa32308db0236990c41693eb02daa1e7e338a2192e09abb131d3961410c8433b2584882efb651add89a86a10e781e095b0374e88010d97996cde7f9756b4ee9021bda17097896b3d5f82e6b43909ccd228956b944725ac874be83c7e91d651cd871410eed234ecac33741c91d6aa1e84d76551cfb22538244443e5ea68537721c60b5b3da87f66e8bb829b6bb8092b7510420611c7660fe55c093e2212e491a152ad42d3c5322443b0e217c728408a80598e88a0a0fc9aaa277488d40c1119640e38dec4c70d91799223d66a8369645086e24b29
private def eighth42_2 (k : ℕ) : ℕ := if k < 43 then 0x3f2d26a028de8c056a5653a7e860231b3df8414ecf3d34fd636484b2e779842a08181fb7575c24d2ddd48046ef73f8481dd59344f167b74eca7f34a51f07fd61818743dc0fec08337cad88fc0d6db051fe2f64be7120fb5a1538d63fdbb5ec3f2a55c280f82e67fe2f994dd857b379da6ca1001d04c617fe67f2126918200e81905705c1495bd4e1c4032c29710296bfd8cfb1ea8090ff27ab69602936a15210178e858a08458b97272aa2039f90e987d6db2d72860f4089a7a819e6bade60441a2813eb56c1943ec11a3bdbed02d42d18cc09739274e57aa0655cabdb7b2b2127eea5f40e064e9c284e80430d7b0e81ec1bf6ff9b7ebc27941f9042ed2306424e450e2a538a090ac4d5c4434dc9bec8484136fa2688b525eafa51f728299325d6824151d7b041a90588d6c994ea14308a547220bbe7d863716dc3a46a595418d672903d83519f2ce0548345f8348e0144176bd986906e23a0eed6c9024d0e6a9a0e70f3245ffdb2d2ff5e5b else 0x3c6ce38a132d57fec37e60a7906149f713fe8690f02304f264bb008e9012c918adc99e57a86d3cd824da6fe46553cc5709de052924e1351d1679b71c12fa5f89a0f099f5cf3c6a471d80f9cea5324cf1e83e0eaf85113d0878fe203d1dd83512f4e497fb2a5707a67d87205fb6b3685343d8f527f7839b55cdd8a074719eb00695f2562054f27f4c13d761a1922c991d360efdfc7b18494f8f186c20074cd54f688b35be5a97d867ff2329edc1952ef78d588bc20f2f3dce36139ec72a125b68ccc7bc86e3ebf4ed2c3b57be34f7e8d7212199e9a25f5e289f081906bff7fdacd534abf3e262bee2d471f911daae747c7846d2ef0d6fe309fadc8f94861fa1784ed029dfae71f3405963fd06741a11b5113e7dfb728c274d57e08c88c7d27d29fa5dca4a19564cf4faa7530dee1cfd3426cc221f5fdee656cda2e840687f73ed5a46a90eb6f5b1be40a67dd711389aa14b7e24c5208fc05a9842aeeedd8fb138f1f8ba4dbf89ab9fb44f80f8
private def eighth40_4 (k : ℕ) : ℕ := if k < 42 then eighth40_2 k else eighth42_2 k
private def eighth44_2 (k : ℕ) : ℕ := if k < 45 then 0x39a34f13648c2357151a1d873737d77110338603faee14e740b0a7c7e6226a1ed89a1cf34baee1cd20bb9e36cb839fd005620201f2e63978567426ce2454bb046e463f714e8a72e4414eb6e7a4909c09d2016e8e9db5ac6e862c4d3a568dd3b8e5bbcf441839474d9d72bafe588a5f40a77cea0d1c5d507b5ec8c28dce1d4cd02ba8609cd901987393aaff754f14771c53b84266758c981eb26aa71a8f803aceb727a16b0941d694fd99d9d79775b86e3895543b21ee3b093ca2a1e260a864f625e763f108f18a895509d7d120ecd74693c4428294b02daa1da60c5cfa10d8de18e3bd73b625d85b9a854a7ccd2ca676f1400ecbb7e0735bfed6cee3b80f8742a0f4fdd79661dd28f1481cc57f0c54482b3bbb59c73e01be4d7793ec877a3262fe1af55f318ad5b0ef9f2869030cb0d00ed8461dfeff66a941dd962a4e4663c1431304aef9c67204dc027854c2849de7d0627f831b8f1023c0a0e524c47becd7a1e2b5d3806f63b1e0d891d3 else 0x36d0d745b4ad560d1bb8f306dcf18b5481891694b638f4dbf8fd46c2e61ef9845b141b8a7814fd569366a799946372b9ee2a1f4265995c0a2c6e8496f58d60f8a5924ba2cdd63d7c6246473059f66da1bb7cf2304bd0133c34b7b13786447768343760ad09b7e6f39d1098b7bbb81c54619cdece29b50a88e0cbacf30d1be51517ffc0d94ad99c4c637e0c7cc1d11ea98eac5c4e6feec681783b70b19fefbb4e037f233f614dbe49d687a9c1249d8011ee69fb15512b383b28a8eb52362bf5653b270a376edb3c51325ada6a00e1a13063bc9112ccc4eb3c1c3f6d47263129671ef43f2389566d612fd15bd4db6a567157e1dec8d4dd0dfb7d774e309e36588d717ce5f83a89c6c7f4997000a904f6658d38ef821be97fee138536122720c06e56d0308971fc5298e4720a5adb9ad54b88e6909c997fc3865388a75a81d3c39497a42d9cfe38eb7035aa72bfe592810876372e29cfce5d9a4658bf3cd12ddf93f9cc66e9931c45e16850e59b
private def eighth46_2 (k : ℕ) : ℕ := if k < 47 then 0x33f5eb89799239a387eaeec6819c51599355afc7ce0fc8d08f5e29a133f05561fbb69a1d6543b50abfdfb72604d3451bb80ef7469bc1e5fa6068d154ec2bfb95df05953b8d1fe5d97ed66727388e3421a4b4127dea1e4904e43f9034ad6b32798c34a9528d1066988a41a9c2d8be09165680d36cdb7d636dbbc41066321a790cd3dbf31ad010f2cf13508fa6589573ca16861f166a3fb22fd6c597fa23498fcd4dad6f7f14567513d79999aa6c82b6d3fc98a83be445356468e1a45e642cc94c9c26af67ebaf0e60375f58dcccd6484f25d55bc508f6b3109ad473125cdc08ec86121a735bfb66e6458a4d98c7aeea6bad094b281ead2137767bcd7b543259f1d1bb03af3f91b020d6c7f40091414ae7e4361ae2d3774dd97c4b852006c63516fe2b2978da75f770d921b2162f7eb8e0da41cb9b2f971db319727ea5c69283675edd89fb97be8cdb156c6d1956b8afdd5e38218d40cda8d9b16b989cebba8f2971b5d1009e15cc02b66c5972 else 0x3112fc94d98cd363bee7bac625463effc26395fd0a9ba4c50595d79759f7a60968be98ac4b86d5ed4445fe9fe4e316fc6be6b358c00803d078630de90e7e213ce261e04a0c678819d0a9e966f06145998daa52ec8a4afd1a29a48c31cc726946576be14ac42f063c73112fa8ca76c796157cc7eaf2f546764d641aad111908ef81ef7bd15300099bf3228ff5c4101fded1b1483264803b8b26fa5d7eb029d6cc95ce8fbc8f352edf461d819372a63bc93d72d08633c932856d5e4437a1b898b86ce65390804def38ac835776c4cace62cc5c39a48b82be9d196555b7ab948f5ebf547be32e1bc364c10c2c71b0400e65f1960e243f0ac9f01e1e8cc3f5f83170bcc54fbd8969993716141bdfeba85ccc75333debab67df0405b8f8a9866a9e5351f27b9e2dbb4bcccdafde3c5d57773ba572d019c17d440df9f232478a8143399fb84ba505f6ab26a4d06761f5081ec2ae9a41a6988cf1fde14e0c1dbafaa86ff19ef7943a8ed8a2db502520
private def eighth44_4 (k : ℕ) : ℕ := if k < 46 then eighth44_2 k else eighth46_2 k
private def eighth40_8 (k : ℕ) : ℕ := if k < 44 then eighth40_4 k else eighth44_4 k
private def eighth32_16 (k : ℕ) : ℕ := if k < 40 then eighth32_8 k else eighth40_8 k
private def eighth48_2 (k : ℕ) : ℕ := if k < 49 then 0x2e287c5a49cce71f2979fa45c7fd9161e0bafc00ecc9c4b95d6bcd738a3aa88208f5973763c9261091d5b9b60a52e863266f591512089300865d3b36e0e428f87c6538450bad40ab76a76f86a5cd10e1766340f2418f64acab72402ee3cbc0d3e7a34073de65a5df65b292dce9889c5f7bc4bc4a3662a9aca52d3c98a61794f5e613dfae3041496192f41482e2841f0da96cbc925eb1457b8ac5c87a6acf4b8bdbfede86290bc749e880717c3a9311dcce7019a3f21d2f9ea77547e9ca4e4d1be905f6bf564ae98862a0dca180bf3530620e2dd8198cfdba97f24dd37341e424f23436a2ffbe95c9a23cf5eef243e260266a7170d8b3f6f1d1dccc0a9fce96dc1e3a808b63e9820e3b04eaac3f36e430a630590daa9853367cbc345ea60e0a42ecd6721c129ae080c21e52988b4c233303799d984f6aaaf3903f2db9b857730b61425ce1d48e07465408619aa229e4ba7f844c00d3cc3923089ba1b0d47505f69187de2a6aea962d1a624585 else 0x2b36ddf6fc2642d42fb8d38569d0ab03fde36a4c89b930ad98ac376098445ed10fea95bee78b9db3b61e734a6302b957173605ff85209466ca575a2442bb9a1aba8982bd4af12c48129f263642f455795ee27379ea69358d3fcbe92bf3ea0d4d2dea4221c2e7c581707f3223d8ea109594c0b08c70cc80c16c25f99318161d595c88c2027dac78ccc2c52478a7c4bf0104f729e458d3b54cef9637107a40dd0b205b0306d558fc698cc89164c7ddd3f27c6110d2b4a52cb089b0b82f462df05403659902bdbc0f678beb5310ecb37e81c43b2c68b350ffaa167b949cad63ca977325b2c2d0eb045dc2a761544abd745a4c6b2b557d4336858e1b0b4f6e49f798085ee7c7ef716aa9d7dc77e16b1d2e3e9a2d6cbb0fd49133e5a944bb05b0872c78e5dc6d5a31ac94b66ed7d9fbd8cc910326ae16d998638a0cb5fdc6bd7582dcaa9d49edc318291b58145bc4423c6f2715c51e261a8b7e65a8bda97af2a9c14ee97088530fa459eaed3987dd
private def eighth50_2 (k : ℕ) : ℕ := if k < 51 then 0x283e95a11ec5f91f03d523450ace119b8a49d714578d10a1b927a9f0007de2c14e57144310dc8936f062da53a46289df7f7b4496a5a5626616516b994aec9ffeafbfbaab4a3367f05b5395d60be08f29472b8a5571053bf857c06b28fd41404db2ab8adcef91a522a1f42c1ff5dc9b099250a4b371b3f44a56c207d73f94a253d11b82f2ed505b291295c71402403d02792d6b0e52e8728bb28c72821229d94a62ffec9b05b0b0c9a860a94d1e24278e76a2482e430e29bb87bc7fd7a478a0ec76253a692b05754841c3ef8fc8a7ac255c2b3e739a1a1fa3150163dc19704784e64d3e82a1a847ab985e5b4508598054647f3b68f0d4bf657b98ca927e480e603af2c43cee71530d880af3c238151c77be2a79674039477066bcb1f64552237b7bfcef96450db714aaa33b4da186a7ffb7316a95604012f467b468382ca952ad82fd2775a650df1ce6b055dfbbb054791e20e718e28ac1e28d85f009283de1a8d158f9a75ab1fdcfe1023f29 else 0x25401895f0934aeaa10af4a4ab046bd20d5c97505076a095c0b2da75ee472827a26812c41a4e954520673c0d52925a03b114a6a1f4eb4857284b7080241ff94590403731497410e7a38c6474b6d808192f422daec0386a2bf916e22600465700899958479569a4c308b0235a84d8f62bd5e898c10ccce8406fda214ab313241fb638baaf07b3ba3dc26603a2bd44a5a25a9e85e84cf066e0ebc81cab98f796c9a40ace5a6984b94fda562935410c2e18151b0d3ff41926c01654957aa7bf91c942e4db01349e93b7af11de6da89bbfedd7d02902a31dc79a9383f5e353b6aa95fb56d68271fda962282efb9d74cca44e6f8fc6f22bbe03f9828109d3eceb6fbff531c69102d13b3cefa0414b77cdb712a6277f86b5688a40d24e430344f2edbe1e851b7d5bb9594c9ebd4e96fc6b655f7713bb93e39be96ec27160531b7a527df1a77639abb773f057184fedf724cb3e931f36208cca03b6c8bdf927bd8f7b21914135c941766014325f12be
private def eighth48_4 (k : ℕ) : ℕ := if k < 50 then eighth48_2 k else eighth50_2 k
private def eighth52_2 (k : ℕ) : ℕ := if k < 53 then 0x223bdd07acffaf5377d86ee44a827f02c6c48d1c0e379889b12656c24cec9357b75191423eefc6937848b4cda3a229cb0d4bd0e5ad580118f04569c4e8a2e764d50fee2548b344af56e396d46bc998d9172a0d7765177244aebe6522fd6f48160341fd7f745ea462b370fd21ce886016f3588cb719b5dcc3cd0cab13c511a2f7fbe8f24359196b21a235e18260ab059009628a1046ec7dee6652011973990708e3991a973c2235017fb0a11d3443f4cdb3dd1be57c7c23beab32fb37ea47cadcc2c47ad990d267eed79a8c99608fbbb1e1ce957372e7de6912038583d727bdc72c65739241f283355315df343b728c486e87f4f498892a6ac5648913d7970bebcba4bec815e1233bbabc3bb71666c1388b247f8eeb93cdf91060c8128492f4a2ecdd9c6879a9195492bee7684c67da4310196c9263e6995554ba474d43ff024dfdf203ffd946c0d25f0249efdf43cb0d1830d9d4d7c943ffadab70a65b10d49291294062ed59f05a8b5c974d else 0x1f325a0b520faa1361f32be3e9572cf393eb92230b4bf87d8c5e3c4208b74462a42b0fbdba405e9c00ccad24d2f1f93d03bb24cad12c3bea923f58557dfeb0001cb3402687f121026cff73927dd79070fee6e0d6ff6fc5a48b74fd1ff532f192e476b20086b42401b1119b952bebcab14460809773af3443cb42d740c3901f1806b9fdd1aedfb2b1a205681f0e1561ed974eddc040dda52a4a32afb1619a210821c87e53d2a3bc87cde07904fb80e37fdadff5f6992420b7bcfd9749b759e78b22641a01137aac00641ae7765083a14bd8e9d451c70f6ae010804e05eb661e553960f632118e3dbbab552a654bf544426254c9ed1977f84d218f88525be9a6aedd8ec55bd6910b0d9cfdbdb9013b3a7b8c2179f64f5e0202f6a67a63c43246f693c563716a04cecc86a9df3a23388ec016c86d10e15b4e1749cda92013aa321daf41ca030d1bc85ac23243e6609ddccfdda04109e60882dacc8a81ff0f95d37cd1111d262b1f6776093082ac
private def eighth54_2 (k : ℕ) : ℕ := if k < 55 then 0x1c240786436bf426b58e17638791718973baf654f947c8715439ee93bcbef7cea8a48e36c829aeba6e72026a0ed1c861112834e8791db1d056393d2170494d52b2879147c72dc3d0d3eca590ea01dc28e67c65989594312382b0ad1ce809067bf19deafc628ac3a010879338bf1e85e35ad87463f951ea42c96e3a25ea8e98bba6965ef725fb91cae1d49ef25bec4e34fe22ccee3ac4cbba7e4fc7427daa34075eb6dcaf1d199e376d1c48ec9a7f2a2a188aeb7244ed1dabc333e837c1720e1931a3b886abb68032988d24bb1c77729986dd6bce69ad0ca00efa8b1f8084ccdfc1050cd1e0d84f49fde9fd16efe6923c4be503456d0919532009c78f97b9461e4d861426f370f2b650f080d0da8d587f3f1e6f342b98981d173757dac3d0f3a1981fb5f2692699b47a80130261836e18d6989c0f5c35a316f1a3c806437201ed0d09c90b24179df83f943dd26985a00d8efd2c2030c7c065edfec96464d37e4de8f8cfcbd90af8d57a4221dc else 0x19115e1bcd4fdebeaf637823254060790329e707ec7580650a9bcd9b1fd1c59676f48cada4f4db157cf77fa616f1973ebe5c31b27cc8f20d12331919cd34f5d83821513006694b3ad24d99115b1d74b0cdee5f96e21b332c65a31119d669fc60a18aad11cb5aa33de0e0dc6b4697d4d5f3f4681e8c45c6027433d22c080d101f0d8c18ed1c1aadb561a38d822e494ea6b652da7e34a2e24fc7b57972232ed7869a824a48cf8e9df1c506b0d415012d802284f0df40041a9b361c977bf91e582d8f635679619cdfc888375609786b317bd6afb9880d68e4330d7278eaf9dcd5b551779de1afd83accbd7abe56f72c4a362c28f2839455437aa4ce06cba90e98c74cf9bf208898da399779eb391377cbabad1b5fc096de48a8be618133236f09a60a6d9b4f9c2515346e4362eaaa24d7336fe7b00dd4b19a78aed6515ece7f31bc1ec9e35b4ae1be3b9bbe37b4e9eb0ac65faa40b08786fcbf0e7b922dd03517f180e05c1353f27b17e50ebc60
private def eighth52_4 (k : ℕ) : ℕ := if k < 54 then eighth52_2 k else eighth54_2 k
private def eighth48_8 (k : ℕ) : ℕ := if k < 52 then eighth48_4 k else eighth52_4 k
private def eighth56_2 (k : ℕ) : ℕ := if k < 57 then 0x15fad71a8a2ecd3110aaff02c27322f34dd2964d30566058b168eb1e96b47fa861a90b228d418ec1869ad160319165dd9efa7be1b8feb4b9ea2ced30fee42d702cbcfd6f05a3d58c62155159a079a968b5409827b25591f0cd73f916c0cef8c7d082e528194a02db314181191b52f3085e645bc910f7147a13ba4f2e1a8b857ec684627fa4c187e251723b5f8dfb88236b7923382e78db00abfc15b7806fa205d549089de8d91759bee318bb6ecef285f98a3abddd8817868eb2ed70f4f36fc46f82f3e853eb3c239e16b756cc5edfd68a890429a7e62a3d0be853dde9658dc60dfe1ae17e958e9f7c2b4ebfd93266300412583ae895d828b4bf0606ae20540d5ac86a104718c19b3744e3262dcdad5a41184c14610e6a36dd75d8f7430c981d3656da02d199064061f5b206571386cb70d1790c4b0b93e20c0213fdab4e318aec0db4a3d2176530a6fe318ed3366994fd17bbf41886380459a417f129a31d68c0c7c5c1e34d3055b25cc8bf else 0x12e0ec69adef26a4198b52225f38f54f4e55ed0c9f7f1c4c4a88bffa642ae6ff09378995bdfca28b53a5449c4841344550558a735a9fa0578226ba5aa6881b6371a7ba2904dd813884851b077250ff609c76dd866c689dcce7bc0613a7b1be8150bf1af89d80827810e14707febe3f4bd6b04f656e4bf50aea0de4384109f917abeda4498dff3ff8f140b0257dd48938277b3fb22847a9241c82ccd534e860450f29815e4e55b9c0030e30a2abb58949f2ced7a5dbed146e46942966176bfb84f12290e2b5b099be8e60bfe974527f8ff11a6c6fb57f22368a5c58bfbcfd4436a69fcaf14d17e362a210d8a5d26a5829d4943ec496c2a2d9a348c540c54e8b6f896d17a0c158a8defc2cbe2f8fcc0cd1281534a900abb75c2aac360602a9ae354e9de05080bde9b05598e607fb46538a0d319a8abf80432a65ef1908c95c21597c6b68252cddb7297da62b61182325c70263906b6d45725425a480d337f3c123f0af10a22459fe32a63feef1
private def eighth58_2 (k : ℕ) : ℕ := if k < 59 then 0xfc41876399d3306b4934261fba124b07ad85e1f46dd243fd7e4e0f4ff9e945739cd08077456b7dc2d9673eac801027d7842525ea4d3e17fc620818b76cee8fc0584e8b604166cd49025893fab5435d88395023dd418e919db1f6e108b8c9adf39dcffe673bb42148f095717e3a9ac15c6e442f58d59447789a548f2e9086b26de5933c2e8ec5a9de10ef377ce6b3bfa0c80bac02210412bf041600d594bb884484241bc34ba31638d177889cf8676d7abb55b97965b1152d7ecc0b9eb0ca2f1f0c22d77cbf58b0ca7b561c8984612909aa03e70347cd4be08cec4a05f12739e8dcdca711b66dacf8e448fc848824c239ea2d4c540eec008a7d7c47a0d1e016cb976b1d0eae89008b6a763de75b7a6e3de1219f88021623c8de6563c82465b2f15da82780339ccc4492ee6f67d186fb38776fc09324ca6fe9a04b4e899c4c127d7828d32086b9e1d8bb8252cac9a572a7c08af7ba444abccee8448b8a2d78d7718964083747309d113000a87 else 0xca4d6201a7bf7d5e5b8d52197bb0caaba5700f199c980335b68b34029dbbfde6a738677edbac92a170f4b5a3db0d08dc3ea5e5b9cc1cd16c21a43b90e27f3c4bc6bf9f0c34eb7137974197ac38e9d506a9edc9125700de5399b9f0d6cda52d9dc7bd3fc94fa01b0bb11e1d5558d7ed7b418367b591731b21df0ad7ad686dbe9bb0e3d931db5d94340dd0d01f0834d0a21fe9f661bd3987f31fa0dd8dee7094380b1f5b60f22c70d6f7ae870de171e7b0b53d618c41b0e34bd6587df071a69539341c9b6eb6165c42afa7857b8399ac30d8b33856ca90eec073fd4cecc1f704c7f75c7a0e98a1e8b50d335305fc7641d633347858ce4312f8d6583b2a43372bfb0d1bf05a0c0771c3b2eba7f244bf68b5b0efc7d6af15934594d651a61e2ae5b8457f76fa39544303cb99ee1d4b8da225b730d07a3adff792a8fadc8a70d20f604faea3eab6a1096fdd21ef2858d27561a9bd1ba12c3e48d5172d60387e4006e387d59395aa5cc38d1382394
private def eighth56_4 (k : ℕ) : ℕ := if k < 58 then eighth56_2 k else eighth58_2 k
private def eighth60_2 (k : ℕ) : ℕ := if k < 61 then 0x983a0a7375d57b31fee41e1339614e41ffa5d360457a426d70120b26431c896df9804e767c4b168a6411287ff009e7de69cc548d260dd5a821401d9d0e3a50794061c3902867ec116ffaab0b3958c18519845e49c8256b4ef60d90a4c1610214284c59d27da814ca45fc1ba8b5a4ce0849829f8be158822e929496737854b9dd293534286cbb7c620ab0475c64789b174e800961592a554489bc80a8db05c82b897635bbe5627ed8be66857db402a6a906305fee97b0b147210c83336fbd389bc0165af75dd0f87bc9c6052842d1a137adc42f75dbb38c605afc6cf9e6c4a2eb4925f40b7895ef82bfe955eeee8b817233b9d236e70f7acd4ce42eaa94edcacd6bb04c776785e1d61a9756c855f7589ef0bdcb2bacea38a2f1659b5817eb7196b72ee3baf8e605c303af9977a3fd66437ad0a0613e1c4b04c28219d9144e0c40c834eac0534253e079018b398cf0c38e00d6c0380831cb4080ef17063f39fe958645e9af0a6d0af87639cb5 else 0x660f3986f2d73656d9b1e80cf41aeb4c9e4371d4e50ac1a4c9c4bc479507dc64b1283562037abf062d4d1cf44f06c55989e2deb1da7b5243c0dbce4c334c5bc685c0c3481bde2bd61aea8f13cc82b4038851a2581afc59d90e2d10729bb4e1f2779cc96c0cf40e85a621b7c8e81b166548c1d6faa2fbb13b8ca5deafe83ba80df3011d9211313a48078e18a7385e57192da7f0a0f4e5e8affaa93ee7c0e9981f011660fbaf6029ca8c5883ecadcf3f041bfda3c283607f271574593937851fe28010170d833bf42183b84cb1420926f723eab70d58b8746041ed853918c18ec7b073bd0856c52060b766e67a7acbe10dfb28ea201e6ad9a907942223b46bf1c1edb3216ac98451004d35c26ca013bb92108bb13c4a6c026484db303211a84d316d4f89cdd5aca2c23b4e4568f11a7ca0148f40483259d3b51132062b7051091f5d0637d07030ea4c2e61270dcefdfc45a6b72d2d902545fe3a9db6ed7e5cdf3b04b54824b3867d732fbbab7
private def eighth63_2 (k : ℕ) : ℕ := if k < 64 then 0x1921fb2aecb36061d84f6006487eabb991cb611ad1bc012d97b6824b0869894626803243f17d99497495d2033007da9d4759f61c299420ec012d97822f996bc4f96853c02bfb69fa6b91955a4612c806487c3f99c01c46ae59fa00e231603c5e20db3edb72401f6a65f9a2a3c5885ced680451d3d6b54745b2f823c60096cb587284b81770b766b0146b8607c3199364746ae602bfb406f580bc10053200405e3ee63a2b131eaaadfce00c90e8fe6f63c2330f1d7301ab3e9732788494d6c51520388bffc3c915b2280c1c740776054e655747e150926f00fb514b55ccbe541ad783a020fc3c65d0dee305ff5cee0451c9c36b5c4cc30ed3bbc0908179ef5d7b775d2f0ad012d936bbe30efd36bf23da027447affa6f72b1130bdaa051ad0e07f3a06dff9f89c80a9a245d4fa7759e6adddd015fd4d21fab225de7eadbd02d8ca1609e37fc0054f8dc05e3d4d77727c10d8ca56a80c2c2a9171ab39c54b13228192155f7a3667df938a737 else 0x0
private def eighth62_3 (k : ℕ) : ℕ := if k < 63 then 0x33d4aba8b9f931d78fe1e206acd52c5413f26d51b86a00dbe29435ed079069cd1be01c454f4ce53b1c8a709ffc03a1c95f80ee7923ade5c740775d163192ace629ac20a80f501f7b1ea65ef170ca9281f693731d1cf00fec0163c040645c6ec568a9ea3783f6083ec8ffcc22bfe51db723c10e20c40bdf6c36d47ecf28228d0bb68582fd6bb796be046abfb2d1bfe9e13576c860907bb867588e3427c8c5681273ee9c4f5f1d65d99270025b0caeb28ab9a2d0decb604cf36e5369abefffcd305609d0a87b210d7e1f8a318a01405c595ebe971debe7ac8028d472dff0c2f2226d57fb0533ab202205731a5ee68620a998f61ddd0758a217954415979035b3a53f10aa427582bf801a5219a86d1334d3005981c259cf2ea9a35b814a0b626fbebeadc1ec63a955c17294d83ce406331df707002f1b754b0e8d0bad7c42f905fc89b7b250be527ca98720c2b4915da89e0b235bfaac18bafc886b9ffe8b8ce3158323ecbe21bb027cdda85e0 else eighth63_2 k
private def eighth60_5 (k : ℕ) : ℕ := if k < 62 then eighth60_2 k else eighth62_3 k
private def eighth56_9 (k : ℕ) : ℕ := if k < 60 then eighth56_4 k else eighth60_5 k
private def eighth48_17 (k : ℕ) : ℕ := if k < 56 then eighth48_8 k else eighth56_9 k
private def eighth32_33 (k : ℕ) : ℕ := if k < 48 then eighth32_16 k else eighth48_17 k
private def eighth0_65 (k : ℕ) : ℕ := if k < 32 then eighth0_32 k else eighth32_33 k
private def eighthWords (k : ℕ) : ℕ := eighth0_65 k
private def eighth (k : ℕ) : ℕ :=
  (eighthWords (k/32) >>> (91*(k%32))) % (2^91)

private def predicted (k : ℕ) : ℕ :=
  let a := coarse (k/128)
  let b := fine (k%128)
  ((a >>> 91)*(b >>> 91) - (a%2^91)*(b%2^91)) >>> 90

def quarterBound (k : ℕ) : ℤ × ℤ :=
  let c := correction k
  let lo := if k%8=0 then eighth (k/8) else predicted k + c/4096 - 8192
  (lo, ((lo+c%4096:ℕ):ℤ))

theorem quarter_width (j : ℕ) :
    ((quarterBound j).2:ℝ) - ((quarterBound j).1:ℝ) ≤ 4096 := by
  let c := correction j
  let lo := if j%8=0 then eighth (j/8) else predicted j + c/4096 - 8192
  change (((lo+c%4096:ℕ):ℝ) - (lo:ℝ)) ≤ 4096
  rw [Nat.cast_add,add_sub_cancel_left]
  exact_mod_cast (Nat.mod_lt c (by decide : 0 < 4096)).le

def packedAngle (k : ℕ) : ℤ × ℤ :=
  let r := k % 65536
  let j := min r (65536-r)
  if j ≤ 16384 then quarterBound j else negBounds (quarterBound (32768-j))

end OMA.White241

/- The square of each stored cosine interval is checked against the doubled
  angle. Induction from angle zero then certifies the complete table. -/

namespace OMA.White241

def signedQuarter (j : ℕ) : ℤ × ℤ :=
  if j ≤ 16384 then quarterBound j else negBounds (quarterBound (32768-j))

def checkQuarter (k : ℕ) : Bool :=
  let v := quarterBound k
  let w := signedQuarter (2*k)
  decide (0 ≤ v.1 ∧ 0 ≤ v.2 ∧
    2*v.1^2 ≤ (P:ℤ)*((P:ℤ)+w.1) ∧ (P:ℤ)*((P:ℤ)+w.2) ≤ 2*v.2^2)

private lemma quarter_sound (hcheck : ∀ k ≤ 16384, checkQuarter k = true)
    (t k : ℕ) (hk : k ≤ 16384) (hdiv : 32768 ∣ 2^t*k) :
    Encloses (quarterBound k) ((P:ℝ)*Real.cos (Real.pi*k/32768)) := by
  induction t generalizing k with
  | zero =>
    simp only [pow_zero,one_mul] at hdiv
    have hz : k = 0 := by
      by_contra! h
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero h) hdiv
      omega
    subst k
    have h := (show quarterBound 0 = ((P:ℤ),(P:ℤ)) by decide)
    simp [h,Encloses]
  | succ t ih =>
    let x := Real.pi*k/32768
    have hx : 0 ≤ Real.cos x := by
      apply Real.cos_nonneg_of_mem_Icc
      have hkR : (k:ℝ) ≤ 16384 := by exact_mod_cast hk
      dsimp [x]
      exact ⟨by linarith [show 0 ≤ Real.pi*(k:ℝ) by positivity,Real.pi_pos],
        by nlinarith [mul_le_mul_of_nonneg_left hkR Real.pi_pos.le]⟩
    have h2 : 32768 ∣ 2^t*(2*k) := by simpa only [pow_succ,mul_assoc] using hdiv
    have hprev : Encloses (signedQuarter (2*k)) ((P:ℝ)*Real.cos (2*x)) := by
      by_cases hc : 2*k ≤ 16384
      · have hh := ih (2*k) hc h2
        rw [signedQuarter,if_pos hc]
        convert hh using 4 <;> dsimp [x] <;> push_cast <;> ring
      · have hle : 2*k ≤ 32768 := by omega
        have hh := ih (32768-2*k) (by omega) (show 32768 ∣ 2^t*(32768-2*k) by
          rw [Nat.mul_sub]
          exact Nat.dvd_sub (dvd_mul_left ..) h2)
        have he : Real.pi*(32768-2*k:ℕ)/32768 = Real.pi-2*x := by
          rw [Nat.cast_sub hle]; dsimp [x]; push_cast; ring
        rw [he,Real.cos_pi_sub] at hh
        simp only [signedQuarter,if_neg hc,Encloses,negBounds,Int.cast_neg] at hh ⊢
        constructor <;> linarith [hh.1,hh.2]
    have ht := hcheck k hk
    simp only [checkQuarter,decide_eq_true_eq] at ht
    obtain ⟨_,hs,hl,hu⟩ := ht
    have lp : 2*((quarterBound k).1:ℝ)^2 ≤ (P:ℝ)*((P:ℝ)+((signedQuarter (2*k)).1:ℝ)) := by
      exact_mod_cast hl
    have up : (P:ℝ)*((P:ℝ)+((signedQuarter (2*k)).2:ℝ)) ≤ 2*((quarterBound k).2:ℝ)^2 := by
      exact_mod_cast hu
    have hnon : 0 ≤ ((quarterBound k).2:ℝ) := by exact_mod_cast hs
    have hp := (Nat.cast_nonneg (α := ℝ) P)
    have hsquare : 2*((P:ℝ)*Real.cos x)^2 = (P:ℝ)*((P:ℝ)+(P:ℝ)*Real.cos (2*x)) := by
      rw [Real.cos_two_mul]; ring
    change ((quarterBound k).1:ℝ) ≤ (P:ℝ)*Real.cos x ∧ _ ≤ _
    exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hprev.1 hp,mul_nonneg hp hx],
      by nlinarith [mul_le_mul_of_nonneg_left hprev.2 hp]⟩

theorem packedAngle_sound (hcheck : ∀ k ≤ 16384, checkQuarter k = true) (n : ℕ) :
    Encloses (packedAngle n) ((P:ℝ)*Real.cos (Real.pi*n/32768)) := by
  let r := n%65536
  have hr : r < 65536 := Nat.mod_lt n (by decide)
  let j := min r (65536-r)
  have hj : j ≤ 32768 := by dsimp [j]; omega
  have hprod : (r:ℝ) + 65536*((n/65536:ℕ):ℝ) = n := by exact_mod_cast Nat.mod_add_div n 65536
  have hcos : Real.cos (Real.pi*n/32768) = Real.cos (Real.pi*j/32768) := by
    rw [show Real.pi*n/32768 = Real.pi*r/32768 + ((n/65536:ℕ):ℝ)*(2*Real.pi) by
      nlinarith [congrArg (fun z : ℝ => z*Real.pi) hprod], Real.cos_add_nat_mul_two_pi]
    by_cases h : r ≤ 65536-r
    · simp [j,h]
    · rw [show j = 65536-r from min_eq_right (by omega),Nat.cast_sub hr.le]
      push_cast
      rw [show Real.pi*(65536-(r:ℝ))/32768 = 2*Real.pi-Real.pi*r/32768 by ring,
        Real.cos_two_pi_sub]
  rw [hcos]
  change Encloses (signedQuarter j) _
  by_cases h : j ≤ 16384
  · rw [signedQuarter,if_pos h]
    exact quarter_sound hcheck 15 j h (dvd_mul_right ..)
  · have hh := quarter_sound hcheck 15 (32768-j) (by omega) (dvd_mul_right ..)
    rw [Nat.cast_sub hj] at hh
    push_cast at hh
    rw [show Real.pi*(32768-(j:ℝ))/32768 = Real.pi-Real.pi*j/32768 by ring,
      Real.cos_pi_sub] at hh
    simp only [signedQuarter,if_neg h,negBounds,Encloses,Int.cast_neg] at hh ⊢
    constructor <;> linarith [hh.1,hh.2]

end OMA.White241
namespace OMA.White241
abbrev Q : ℕ := 2*M
abbrev unitScale : ℕ := 2^68

def denomConst : ℕ := H*P*31415926^2

def newton (x : ℕ) : ℕ → ℕ → ℕ
  | 0, a => a
  | k+1, a => newton x k ((2*a + x/(a*a))/3)

def powUpper (a b : ℕ) : ℕ :=
  let num := unitScale^3*a^4
  let den := b^4
  let x := (num+den-1)/den
  let y := newton x 8 (2^((x.log2+3)/3))+1
  if num ≤ y^3*den then y else num+1

noncomputable def trigSum (n : ℕ) : ℝ :=
  (J.map (fun z => (z.2:ℝ) * Real.cos (Real.pi*n*z.1 / M))).sum

theorem powUpper_correct (a b : ℕ) (hb : 0 < b) :
    ((a:ℝ)/b)^((4:ℝ)/3) ≤ (powUpper a b:ℝ)/unitScale := by
  have hNat : unitScale^3*a^4 ≤ (powUpper a b)^3*b^4 := by
    simp only [powUpper]
    split_ifs with h
    · exact h
    · let x := unitScale^3*a^4
      change x ≤ (x+1)^3*b^4
      have hx : 1 ≤ x+1 := by omega
      have he : x+1 ≤ (x+1)^3 := le_self_pow₀ hx (by decide)
      exact (Nat.le_succ x).trans (he.trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos hb)))
  have hReal : (unitScale:ℝ)^3*(a:ℝ)^4 ≤ (powUpper a b:ℝ)^3*(b:ℝ)^4 := by exact_mod_cast hNat
  have hb' : 0 < (b:ℝ) := by exact_mod_cast hb
  have hcube : (((a:ℝ)/b)^((4:ℝ)/3))^3 ≤ ((powUpper a b:ℝ)/unitScale)^3 := by
    rw [← Real.rpow_mul_natCast (by positivity),show ((4:ℝ)/3)*((3:ℕ):ℝ) = 4 by norm_num]
    norm_cast
    rw [div_pow,div_pow]
    exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by linarith only [hReal])
  by_contra! h
  exact (not_lt_of_ge hcube) (pow_lt_pow_left₀ h (by positivity) (by decide))

end OMA.White241

/- The four frequency classes share the same two scalar products.  A small
  error allowance covers the widths of all the stored cosine intervals. -/

namespace OMA.White241

def midCos (k : ℕ) : ℤ :=
  let r := k % 65536
  let j := min r (65536-r)
  if j ≤ 16384 then (quarterBound j).1 else -(quarterBound (32768-j)).1

def dot (L : List (ℕ × ℤ)) (b : ℕ) : ℤ :=
  (L.map (fun z => z.2 * midCos (b*z.1))).sum

def evJ := J.filter (fun z => z.1 % 2 == 0)
def odJ := J.filter (fun z => z.1 % 2 != 0)
def err : ℕ := 4096 * (J.map (fun z => z.2.natAbs)).sum

def scaledNum (x : ℤ) : ℕ := M*(x.natAbs+err)*10^14

def score (r a : ℕ) : ℕ :=
  let b := denomConst
  powUpper a (b*r^2) + powUpper a (b*(r+Q)^2) + (7*powUpper a (b*Q^2)+19)/20

def groupScore (r : ℕ) : ℕ :=
  let e := dot evJ r
  let o := dot odJ r
  let p := scaledNum (e+o)
  let m := scaledNum (e-o)
  score r p + score (M-r) m + score (M+r) m + score (Q-r) p

def endScore : ℕ :=
  let e := dot evJ 0
  let o := dot odJ 0
  let q := M/2
  let p := scaledNum (dot evJ q + dot odJ q)
  score q p + score M (scaledNum (e-o)) + score (3*q) p + score Q (scaledNum (e+o))

def span (start len : ℕ) : ℕ :=
  (List.range len).foldl (fun acc i => acc + groupScore (start+i)) 0

def tests (start len : ℕ) : Bool := (List.range len).all (fun i => checkQuarter (start+i))

end OMA.White241


namespace OMA.White241

def spanAux (f : ℕ → ℕ) (a n : ℕ) :=
  (List.range n).foldl (fun u i => u+f (a+i)) 0

theorem spanAux_eq (f : ℕ → ℕ) (a n : ℕ) :
    spanAux f a n = ∑ i ∈ Finset.range n, f (a+i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [spanAux,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,
      Finset.sum_range_succ] using congrArg (· + f (a+n)) ih

theorem spanAux_join (f : ℕ → ℕ) {a n m b c : ℕ} (h : spanAux f a n = b)
    (g : spanAux f (a+n) m = c) : spanAux f a (n+m) = b+c := by
  rw [←h,←g,spanAux_eq,spanAux_eq,spanAux_eq,Finset.sum_range_add]
  simp only [Nat.add_assoc]

def testsAux (f : ℕ → Bool) (a n : ℕ) := (List.range n).all (fun i => f (a+i))

theorem testsAux_at (f : ℕ → Bool) {a n : ℕ} (h : testsAux f a n = true) {i : ℕ} (hi : i < n) :
    f (a+i) = true :=
  List.all_eq_true.mp h i (List.mem_range.mpr hi)

theorem testsAux_join (f : ℕ → Bool) {a n m : ℕ}
    (h : testsAux f a n = true) (g : testsAux f (a+n) m = true) : testsAux f a (n+m) = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hl := List.mem_range.mp hi
  by_cases hc : i < n
  · exact testsAux_at f h hc
  · obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hc)
    simpa only [Nat.add_assoc] using testsAux_at f g (i:=v) (by omega)

end OMA.White241


namespace OMA.White241

theorem span_eq (a n : ℕ) : span a n = ∑ i ∈ Finset.range n, groupScore (a+i) :=
  spanAux_eq groupScore a n

theorem span_join {a n m b c : ℕ} (h : span a n = b) (g : span (a+n) m = c) :
    span a (n+m) = b+c := spanAux_join groupScore (a:=a) (n:=n) (m:=m) h g

theorem tests_at {a n : ℕ} (h : tests a n = true) {i : ℕ} (hi : i < n) :
    checkQuarter (a+i) = true := testsAux_at checkQuarter (a:=a) (n:=n) h hi

theorem tests_join {a n m : ℕ} (h : tests a n = true) (g : tests (a+n) m = true) :
    tests a (n+m) = true := testsAux_join checkQuarter (a:=a) (n:=n) (m:=m) h g

end OMA.White241


/- A residue has two explicitly evaluated modes and one integral-test tail. -/

namespace OMA.White241

noncomputable def row (r : ℕ) (x : ℝ) : ℝ :=
  (x / (r:ℝ)^2)^((4:ℝ)/3) + (x/((r+Q:ℕ):ℝ)^2)^((4:ℝ)/3) +
    (7/20)*(x/(Q:ℝ)^2)^((4:ℝ)/3)

theorem row_score (r a : ℕ) (hr : 0 < r) {v : ℝ} (hv : 0 ≤ v) (hva : v ≤ (a:ℝ)/denomConst) :
    row r v ≤ (score r a : ℝ)/unitScale := by
  have hd : 0 < denomConst := by decide
  have hom (x : ℕ) (hx : 0 < x) :
      (v/(x:ℝ)^2)^((4:ℝ)/3) ≤ (powUpper a (denomConst*x^2):ℝ)/unitScale := by
    apply le_trans _ (powUpper_correct a (denomConst*x^2) (by positivity))
    simp only [Nat.cast_mul,Nat.cast_pow,← div_div]
    gcongr
  have h1 := hom r hr
  have h2 := hom (r+Q) (by omega)
  have h3 := hom Q (by decide)
  let z := powUpper a (denomConst*Q^2)
  have hround : 7*z ≤ 20*((7*z+19)/20) := by omega
  have hroundR : 7*(z:ℝ) ≤ 20*(((7*z+19)/20:ℕ):ℝ) := by exact_mod_cast hround
  have hs : (0:ℝ) < unitScale := by norm_num
  change _ ≤ ((powUpper a (denomConst*r^2)+powUpper a (denomConst*(r+Q)^2)+((7*z+19)/20):ℕ):ℝ)/unitScale
  simp only [Nat.cast_add,add_div]
  have h4 : 7/20*((z:ℝ)/unitScale) ≤ (((7*z+19)/20:ℕ):ℝ)/unitScale := by
    apply (le_div_iff₀ hs).mpr
    field_simp
    linarith
  rw [Nat.cast_add] at h2
  change (v / (Q:ℝ)^2)^((4:ℝ)/3) ≤ (z:ℝ)/unitScale at h3
  unfold row
  simp only [Nat.cast_add]
  linarith only [h1,h2,h3,h4]

end OMA.White241


/- Error estimates for the even and odd parts of the cosine scalar product. -/

namespace OMA.White241

private theorem mid_error (hcheck : ∀ j ≤ 16384, checkQuarter j = true) (k : ℕ) :
    |(P:ℝ)*Real.cos (Real.pi*k/M) - (midCos k:ℝ)| ≤ 4096 := by
  have hh := packedAngle_sound hcheck k
  simp only [packedAngle,Encloses,midCos,M] at hh ⊢
  split_ifs at hh ⊢ with h
  · apply abs_le.mpr
    exact ⟨by linarith [hh.1], by linarith [hh.2,quarter_width (min (k%65536) (65536-k%65536))]⟩
  · simp only [negBounds,Int.cast_neg] at hh ⊢
    apply abs_le.mpr
    constructor <;> linarith [hh.1,hh.2,quarter_width (32768-min (k%65536) (65536-k%65536))]

private def signedDot (b : ℕ) (s : Bool) (L : List (ℕ × ℤ)) : ℤ :=
  (L.map (fun z => if s && z.1%2!=0 then -(z.2*midCos (b*z.1)) else z.2*midCos (b*z.1))).sum

theorem signedDot_parts (b : ℕ) (s : Bool) (L : List (ℕ × ℤ)) :
    signedDot b s L = dot (L.filter (fun z => z.1%2==0)) b +
      (if s then -dot (L.filter (fun z => z.1%2!=0)) b else dot (L.filter (fun z => z.1%2!=0)) b) := by
  induction L with
  | nil => cases s <;> simp [signedDot,dot]
  | cons z L ih =>
    rcases (show z.1%2=0 ∨ z.1%2=1 by omega) with h|h <;> cases s <;>
      simp [signedDot,dot,h] at ih ⊢ <;> omega

private theorem dot_error (hcheck : ∀ j ≤ 16384, checkQuarter j = true) (n b : ℕ) (s : Bool)
    (hc : ∀ j : ℕ, Real.cos (Real.pi*n*j/M) =
      if s && j%2!=0 then -Real.cos (Real.pi*b*j/M) else Real.cos (Real.pi*b*j/M))
    (L : List (ℕ × ℤ)) :
    |(P:ℝ)*(L.map (fun z => (z.2:ℝ)*Real.cos (Real.pi*n*z.1/M))).sum - (signedDot b s L:ℝ)| ≤
      4096*((L.map (fun z => z.2.natAbs)).sum:ℕ) := by
  induction L with
  | nil => simp [signedDot]
  | cons z L ih =>
    let t := if s && z.1%2!=0 then -(z.2*midCos (b*z.1)) else z.2*midCos (b*z.1)
    have hx := mid_error hcheck (b*z.1)
    rw [Nat.cast_mul,← mul_assoc] at hx
    have hterm : |(P:ℝ)*((z.2:ℝ)*Real.cos (Real.pi*n*z.1/M))-(t:ℝ)| ≤
        4096*(z.2.natAbs:ℝ) := by
      have hg := mul_le_mul_of_nonneg_left hx (abs_nonneg (z.2:ℝ))
      rw [← abs_mul] at hg
      rw [hc,Nat.cast_natAbs,Int.cast_abs]
      dsimp only [t]
      split_ifs <;> simp only [Int.cast_neg,Int.cast_mul]
      · rw [show (P:ℝ)*(z.2*(-Real.cos (Real.pi*b*z.1/M))) - -((z.2:ℝ)*midCos (b*z.1)) =
            -((z.2:ℝ)*((P:ℝ)*Real.cos (Real.pi*b*z.1/M) - midCos (b*z.1))) by ring,abs_neg]
        linarith only [hg]
      · rw [show (P:ℝ)*(z.2*Real.cos (Real.pi*b*z.1/M)) - ((z.2:ℝ)*midCos (b*z.1)) =
            (z.2:ℝ)*((P:ℝ)*Real.cos (Real.pi*b*z.1/M) - midCos (b*z.1)) by ring]
        linarith only [hg]
    change |(P:ℝ)*((z.2:ℝ)*Real.cos (Real.pi*n*z.1/M) + _) - ((t + signedDot b s L:ℤ):ℝ)| ≤ _
    rw [Int.cast_add,mul_add,add_sub_add_comm]
    apply (abs_add_le ..).trans
    simp only [List.map_cons,List.sum_cons,Nat.cast_add,mul_add]
    exact add_le_add hterm ih

theorem folded_amplitude (hcheck : ∀ j ≤ 16384, checkQuarter j = true) (n b : ℕ) (s : Bool)
    (hc : ∀ j : ℕ, Real.cos (Real.pi*n*j/M) =
      if s && j%2!=0 then -Real.cos (Real.pi*b*j/M) else Real.cos (Real.pi*b*j/M)) :
    M * |trigSum n| / (H*Real.pi^2) ≤
      (scaledNum (dot evJ b + (if s then -dot odJ b else dot odJ b)) : ℝ)/denomConst := by
  let z := signedDot b s J
  have hz := dot_error hcheck n b s hc J
  have ha : (P:ℝ)*|trigSum n| ≤ (z.natAbs+err:ℕ) := by
    have h := abs_add_le ((P:ℝ)*trigSum n-(z:ℝ)) (z:ℝ)
    rw [sub_add_cancel,abs_mul,abs_of_nonneg (Nat.cast_nonneg P)] at h
    change |(P:ℝ)*trigSum n-(z:ℝ)| ≤ _ at hz
    simp only [err,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_natAbs,Int.cast_abs]
    linarith only [h,hz]
  unfold evJ odJ
  rw [← signedDot_parts b s J]
  have hπ : (31415926:ℝ)^2 ≤ 10^14*Real.pi^2 := by
    nlinarith [Real.pi_gt_d20, sq_nonneg (Real.pi - 3.14159265358979323846)]
  change _ ≤ ((M*(z.natAbs+err)*10^14:ℕ):ℝ)/(H*P*31415926^2:ℕ)
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hp : (0:ℝ) < P := by norm_num [P]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    _ = (M:ℝ)*H*((P:ℝ)*|trigSum n|)*31415926^2 := by ring
    _ ≤ (M:ℝ)*H*((z.natAbs+err:ℕ):ℝ)*(10^14*Real.pi^2) := by gcongr
    _ = _ := by ring

end OMA.White241


/- Summing the verified bounds over the four quadrants of one frequency period. -/

namespace OMA.White241
open Finset

noncomputable def trueAmp (r : ℕ) : ℝ := M * |trigSum r| / (H*Real.pi^2)
noncomputable def trueRow (r : ℕ) : ℝ := row r (trueAmp r)

private theorem row_unsigned (ht : ∀ j ≤ 16384, checkQuarter j = true)
    {n b : ℕ} (hn : 0 < n) (hc : ∀ j : ℕ, Real.cos (Real.pi*n*j/M) = Real.cos (Real.pi*b*j/M)) :
    trueRow n ≤ (score n (scaledNum (dot evJ b + dot odJ b)) : ℝ)/unitScale := by
  apply row_score _ _ hn (show 0 ≤ trueAmp n by unfold trueAmp; positivity)
  simpa only [trueAmp,Bool.false_and,Bool.false_eq_true,if_false] using
    folded_amplitude ht n b false (by simpa only [Bool.false_and,Bool.false_eq_true,if_false] using hc)

private theorem row_signed (ht : ∀ j ≤ 16384, checkQuarter j = true)
    {n b : ℕ} (hn : 0 < n) (hc : ∀ j : ℕ, Real.cos (Real.pi*n*j/M) =
        (-1:ℝ)^j * Real.cos (Real.pi*b*j/M)) :
    trueRow n ≤ (score n (scaledNum (dot evJ b - dot odJ b)) : ℝ)/unitScale := by
  apply row_score _ _ hn (show 0 ≤ trueAmp n by unfold trueAmp; positivity)
  rw [sub_eq_add_neg]
  apply folded_amplitude ht n b true
  intro j
  rw [hc j,neg_one_pow_eq_pow_mod_two]
  rcases (show j%2=0 ∨ j%2=1 by omega) with h|h <;> simp [h]

private theorem grouped_rows (ht : ∀ j ≤ 16384, checkQuarter j = true)
    (b : ℕ) (hb : 0 < b) (hb' : b < M/2) :
    trueRow b + trueRow (M-b) + trueRow (M+b) + trueRow (Q-b) ≤ (groupScore b:ℝ)/unitScale := by
  have bM : b < M := by omega
  have bQ : b < Q := by dsimp [M,Q] at *; omega
  have h1 := row_unsigned ht hb (b:=b) (fun _ => rfl)
  have h2 := row_signed ht (n:=M-b) (by omega) (OMA.WhiteFold241.cos_left (by decide) bM.le)
  have h3 := row_signed ht (n:=M+b) (by omega) (OMA.WhiteFold241.cos_right (by decide))
  have h4 := row_unsigned ht (n:=Q-b) (by omega) (OMA.WhiteFold241.cos_period_left (by decide) bQ.le)
  simp only [groupScore,Nat.cast_add,add_div]
  linarith only [h1,h2,h3,h4]

private theorem end_rows (ht : ∀ j ≤ 16384, checkQuarter j = true) :
    trueRow 16384 + trueRow 32768 + trueRow 49152 + trueRow 65536 ≤ (endScore:ℝ)/unitScale := by
  have h1 := row_unsigned ht (n:=16384) (b:=16384) (by decide) (fun _ => rfl)
  have h2 := row_signed ht (n:=M-0) (b:=0) (by decide) (OMA.WhiteFold241.cos_left (by decide) (Nat.zero_le _))
  have h3 := row_unsigned ht (n:=Q-16384) (b:=16384) (by decide) (OMA.WhiteFold241.cos_period_left (by decide) (by decide))
  have h4 := row_unsigned ht (n:=Q-0) (b:=0) (by decide) (OMA.WhiteFold241.cos_period_left (by decide) (Nat.zero_le _))
  exact (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans_eq (by
    simp only [endScore,Nat.cast_add,add_div]; rfl)

theorem whole_period_of_checks (ht : ∀ j ≤ 16384, checkQuarter j = true)
    (hs : endScore+span 1 16383 = 278195042329380884410) :
    (∑ r : Fin Q, row (r.val+1) (trueAmp (r.val+1))) ≤
      278195042329380884410/(295147905179352825856:ℝ) := by
  change (∑ r : Fin Q, trueRow (r.val+1)) ≤ _
  rw [Fin.sum_univ_eq_sum_range (fun i => trueRow (i+1)) Q]
  change (∑ i ∈ range (4*(16383+1)), trueRow (i+1)) ≤ _
  rw [OMA.WhiteFold241.four_blocks]
  have Hs : (∑ i ∈ range 16383,
      (trueRow (i+1)+trueRow (M-(i+1))+trueRow (M+(i+1))+trueRow (Q-(i+1)))) ≤
      ∑ i ∈ range 16383, (groupScore (i+1):ℝ)/unitScale := by
    apply sum_le_sum
    intro i hi
    exact grouped_rows ht (i+1) (by omega) (by have := mem_range.mp hi; dsimp [M]; omega)
  apply (add_le_add (end_rows ht) Hs).trans_eq
  rw [← sum_div,← add_div]
  have hu : (unitScale:ℝ) = 295147905179352825856 := by norm_num
  rw [hu]
  apply congrArg (fun x : ℝ => x/(295147905179352825856:ℝ))
  have hsR : ((endScore+span 1 16383:ℕ):ℝ) = 278195042329380884410 := by exact_mod_cast hs
  simpa only [Nat.cast_add,span_eq,Nat.cast_sum,Nat.add_comm 1] using hsR

end OMA.White241

namespace OMA.White241

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem checked_angles : ∀ j ≤ 16384, checkQuarter j = true := by
  have batch : tests 0 16384 = true :=
    (tests_join (a:=0) (n:=8192) (m:=8192)
      (tests_join (a:=0) (n:=4096) (m:=4096)
        (tests_join (a:=0) (n:=2048) (m:=2048)
          (tests_join (a:=0) (n:=1024) (m:=1024)
            (tests_join (a:=0) (n:=512) (m:=512)
              (tests_join (a:=0) (n:=256) (m:=256)
                (tests_join (a:=0) (n:=128) (m:=128)
                  (tests_join (a:=0) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=128) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=256) (n:=128) (m:=128)
                  (tests_join (a:=256) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=384) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=512) (n:=256) (m:=256)
                (tests_join (a:=512) (n:=128) (m:=128)
                  (tests_join (a:=512) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=640) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=768) (n:=128) (m:=128)
                  (tests_join (a:=768) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=896) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (tests_join (a:=1024) (n:=512) (m:=512)
              (tests_join (a:=1024) (n:=256) (m:=256)
                (tests_join (a:=1024) (n:=128) (m:=128)
                  (tests_join (a:=1024) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=1152) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=1280) (n:=128) (m:=128)
                  (tests_join (a:=1280) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=1408) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=1536) (n:=256) (m:=256)
                (tests_join (a:=1536) (n:=128) (m:=128)
                  (tests_join (a:=1536) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=1664) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=1792) (n:=128) (m:=128)
                  (tests_join (a:=1792) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=1920) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))))
          (tests_join (a:=2048) (n:=1024) (m:=1024)
            (tests_join (a:=2048) (n:=512) (m:=512)
              (tests_join (a:=2048) (n:=256) (m:=256)
                (tests_join (a:=2048) (n:=128) (m:=128)
                  (tests_join (a:=2048) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=2176) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=2304) (n:=128) (m:=128)
                  (tests_join (a:=2304) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=2432) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=2560) (n:=256) (m:=256)
                (tests_join (a:=2560) (n:=128) (m:=128)
                  (tests_join (a:=2560) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=2688) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=2816) (n:=128) (m:=128)
                  (tests_join (a:=2816) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=2944) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (tests_join (a:=3072) (n:=512) (m:=512)
              (tests_join (a:=3072) (n:=256) (m:=256)
                (tests_join (a:=3072) (n:=128) (m:=128)
                  (tests_join (a:=3072) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=3200) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=3328) (n:=128) (m:=128)
                  (tests_join (a:=3328) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=3456) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=3584) (n:=256) (m:=256)
                (tests_join (a:=3584) (n:=128) (m:=128)
                  (tests_join (a:=3584) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=3712) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=3840) (n:=128) (m:=128)
                  (tests_join (a:=3840) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=3968) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))))))
        (tests_join (a:=4096) (n:=2048) (m:=2048)
          (tests_join (a:=4096) (n:=1024) (m:=1024)
            (tests_join (a:=4096) (n:=512) (m:=512)
              (tests_join (a:=4096) (n:=256) (m:=256)
                (tests_join (a:=4096) (n:=128) (m:=128)
                  (tests_join (a:=4096) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=4224) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=4352) (n:=128) (m:=128)
                  (tests_join (a:=4352) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=4480) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=4608) (n:=256) (m:=256)
                (tests_join (a:=4608) (n:=128) (m:=128)
                  (tests_join (a:=4608) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=4736) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=4864) (n:=128) (m:=128)
                  (tests_join (a:=4864) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=4992) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (tests_join (a:=5120) (n:=512) (m:=512)
              (tests_join (a:=5120) (n:=256) (m:=256)
                (tests_join (a:=5120) (n:=128) (m:=128)
                  (tests_join (a:=5120) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=5248) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=5376) (n:=128) (m:=128)
                  (tests_join (a:=5376) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=5504) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=5632) (n:=256) (m:=256)
                (tests_join (a:=5632) (n:=128) (m:=128)
                  (tests_join (a:=5632) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=5760) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=5888) (n:=128) (m:=128)
                  (tests_join (a:=5888) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=6016) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))))
          (tests_join (a:=6144) (n:=1024) (m:=1024)
            (tests_join (a:=6144) (n:=512) (m:=512)
              (tests_join (a:=6144) (n:=256) (m:=256)
                (tests_join (a:=6144) (n:=128) (m:=128)
                  (tests_join (a:=6144) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=6272) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=6400) (n:=128) (m:=128)
                  (tests_join (a:=6400) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=6528) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=6656) (n:=256) (m:=256)
                (tests_join (a:=6656) (n:=128) (m:=128)
                  (tests_join (a:=6656) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=6784) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=6912) (n:=128) (m:=128)
                  (tests_join (a:=6912) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=7040) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (tests_join (a:=7168) (n:=512) (m:=512)
              (tests_join (a:=7168) (n:=256) (m:=256)
                (tests_join (a:=7168) (n:=128) (m:=128)
                  (tests_join (a:=7168) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=7296) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=7424) (n:=128) (m:=128)
                  (tests_join (a:=7424) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=7552) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=7680) (n:=256) (m:=256)
                (tests_join (a:=7680) (n:=128) (m:=128)
                  (tests_join (a:=7680) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=7808) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=7936) (n:=128) (m:=128)
                  (tests_join (a:=7936) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=8064) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))))))
      (tests_join (a:=8192) (n:=4096) (m:=4096)
        (tests_join (a:=8192) (n:=2048) (m:=2048)
          (tests_join (a:=8192) (n:=1024) (m:=1024)
            (tests_join (a:=8192) (n:=512) (m:=512)
              (tests_join (a:=8192) (n:=256) (m:=256)
                (tests_join (a:=8192) (n:=128) (m:=128)
                  (tests_join (a:=8192) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=8320) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=8448) (n:=128) (m:=128)
                  (tests_join (a:=8448) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=8576) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=8704) (n:=256) (m:=256)
                (tests_join (a:=8704) (n:=128) (m:=128)
                  (tests_join (a:=8704) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=8832) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=8960) (n:=128) (m:=128)
                  (tests_join (a:=8960) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=9088) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (tests_join (a:=9216) (n:=512) (m:=512)
              (tests_join (a:=9216) (n:=256) (m:=256)
                (tests_join (a:=9216) (n:=128) (m:=128)
                  (tests_join (a:=9216) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=9344) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=9472) (n:=128) (m:=128)
                  (tests_join (a:=9472) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=9600) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=9728) (n:=256) (m:=256)
                (tests_join (a:=9728) (n:=128) (m:=128)
                  (tests_join (a:=9728) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=9856) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=9984) (n:=128) (m:=128)
                  (tests_join (a:=9984) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=10112) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))))
          (tests_join (a:=10240) (n:=1024) (m:=1024)
            (tests_join (a:=10240) (n:=512) (m:=512)
              (tests_join (a:=10240) (n:=256) (m:=256)
                (tests_join (a:=10240) (n:=128) (m:=128)
                  (tests_join (a:=10240) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=10368) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=10496) (n:=128) (m:=128)
                  (tests_join (a:=10496) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=10624) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=10752) (n:=256) (m:=256)
                (tests_join (a:=10752) (n:=128) (m:=128)
                  (tests_join (a:=10752) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=10880) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=11008) (n:=128) (m:=128)
                  (tests_join (a:=11008) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=11136) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (tests_join (a:=11264) (n:=512) (m:=512)
              (tests_join (a:=11264) (n:=256) (m:=256)
                (tests_join (a:=11264) (n:=128) (m:=128)
                  (tests_join (a:=11264) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=11392) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=11520) (n:=128) (m:=128)
                  (tests_join (a:=11520) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=11648) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=11776) (n:=256) (m:=256)
                (tests_join (a:=11776) (n:=128) (m:=128)
                  (tests_join (a:=11776) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=11904) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=12032) (n:=128) (m:=128)
                  (tests_join (a:=12032) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=12160) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))))))
        (tests_join (a:=12288) (n:=2048) (m:=2048)
          (tests_join (a:=12288) (n:=1024) (m:=1024)
            (tests_join (a:=12288) (n:=512) (m:=512)
              (tests_join (a:=12288) (n:=256) (m:=256)
                (tests_join (a:=12288) (n:=128) (m:=128)
                  (tests_join (a:=12288) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=12416) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=12544) (n:=128) (m:=128)
                  (tests_join (a:=12544) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=12672) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=12800) (n:=256) (m:=256)
                (tests_join (a:=12800) (n:=128) (m:=128)
                  (tests_join (a:=12800) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=12928) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=13056) (n:=128) (m:=128)
                  (tests_join (a:=13056) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=13184) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (tests_join (a:=13312) (n:=512) (m:=512)
              (tests_join (a:=13312) (n:=256) (m:=256)
                (tests_join (a:=13312) (n:=128) (m:=128)
                  (tests_join (a:=13312) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=13440) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=13568) (n:=128) (m:=128)
                  (tests_join (a:=13568) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=13696) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=13824) (n:=256) (m:=256)
                (tests_join (a:=13824) (n:=128) (m:=128)
                  (tests_join (a:=13824) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=13952) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=14080) (n:=128) (m:=128)
                  (tests_join (a:=14080) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=14208) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))))
          (tests_join (a:=14336) (n:=1024) (m:=1024)
            (tests_join (a:=14336) (n:=512) (m:=512)
              (tests_join (a:=14336) (n:=256) (m:=256)
                (tests_join (a:=14336) (n:=128) (m:=128)
                  (tests_join (a:=14336) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=14464) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=14592) (n:=128) (m:=128)
                  (tests_join (a:=14592) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=14720) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=14848) (n:=256) (m:=256)
                (tests_join (a:=14848) (n:=128) (m:=128)
                  (tests_join (a:=14848) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=14976) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=15104) (n:=128) (m:=128)
                  (tests_join (a:=15104) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=15232) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (tests_join (a:=15360) (n:=512) (m:=512)
              (tests_join (a:=15360) (n:=256) (m:=256)
                (tests_join (a:=15360) (n:=128) (m:=128)
                  (tests_join (a:=15360) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=15488) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=15616) (n:=128) (m:=128)
                  (tests_join (a:=15616) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=15744) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))))
              (tests_join (a:=15872) (n:=256) (m:=256)
                (tests_join (a:=15872) (n:=128) (m:=128)
                  (tests_join (a:=15872) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=16000) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))
                (tests_join (a:=16128) (n:=128) (m:=128)
                  (tests_join (a:=16128) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel))
                  (tests_join (a:=16256) (n:=64) (m:=64)
                    (by decide +kernel)
                    (by decide +kernel)))))))))
  intro j hj
  by_cases h : j < 16384
  · simpa only [Nat.zero_add] using tests_at (a:=0) (n:=16384) batch h
  · have : j = 16384 := by omega
    subst j
    decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem checked_sum : endScore + span 1 16383 = 278195042329380884410 := by
  have endpoint : endScore = 951519366922 := by decide +kernel
  have batch : span 1 16383 = 278195041377861517488 :=
    (span_join (a:=1) (n:=8192) (m:=8191) (b:=278181584273704958740) (c:=13457104156558748)
      (span_join (a:=1) (n:=4096) (m:=4096) (b:=278161768251965626492) (c:=19816021739332248)
        (span_join (a:=1) (n:=2048) (m:=2048) (b:=278125041730428315580) (c:=36726521537310912)
          (span_join (a:=1) (n:=1024) (m:=1024) (b:=278053434690154541014) (c:=71607040273774566)
            (span_join (a:=1) (n:=512) (m:=512) (b:=277911486604881829865) (c:=141948085272711149)
              (span_join (a:=1) (n:=256) (m:=256) (b:=277628678265979628012) (c:=282808338902201853)
                (span_join (a:=1) (n:=128) (m:=128) (b:=277064839349634751926) (c:=563838916344876086)
                  (span_join (a:=1) (n:=64) (m:=64) (b:=275942923531013249998) (c:=1121915818621501928)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=129) (n:=64) (m:=64) (b:=376276459130158458) (c:=187562457214717628)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=257) (n:=128) (m:=128) (b:=188671776672717851) (c:=94136562229484002)
                  (span_join (a:=257) (n:=64) (m:=64) (b:=112956892460830679) (c:=75714884211887172)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=385) (n:=64) (m:=64) (b:=54044471794453967) (c:=40092090435030035)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=513) (n:=256) (m:=256) (b:=94640858144646096) (c:=47307227128065053)
                (span_join (a:=513) (n:=128) (m:=128) (b:=56630381112789046) (c:=38010477031857050)
                  (span_join (a:=513) (n:=64) (m:=64) (b:=31750402754101549) (c:=24879978358687497)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=641) (n:=64) (m:=64) (b:=20899828599126047) (c:=17110648432731003)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=769) (n:=128) (m:=128) (b:=27136520814560115) (c:=20170706313504938)
                  (span_join (a:=769) (n:=64) (m:=64) (b:=14530928710871912) (c:=12605592103688203)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=897) (n:=64) (m:=64) (b:=11104338105845601) (c:=9066368207659337)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (span_join (a:=1025) (n:=512) (m:=512) (b:=47661133532445864) (c:=23945906741328702)
              (span_join (a:=1025) (n:=256) (m:=256) (b:=28490672478660338) (c:=19170461053785526)
                (span_join (a:=1025) (n:=128) (m:=128) (b:=15956804352031902) (c:=12533868126628436)
                  (span_join (a:=1025) (n:=64) (m:=64) (b:=8498643972012661) (c:=7458160380019241)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=1153) (n:=64) (m:=64) (b:=6544485410863994) (c:=5989382715764442)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=1281) (n:=128) (m:=128) (b:=10530660514764346) (c:=8639800539021180)
                  (span_join (a:=1281) (n:=64) (m:=64) (b:=5526244884283096) (c:=5004415630481250)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=1409) (n:=64) (m:=64) (b:=4520587920776464) (c:=4119212618244716)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=1537) (n:=256) (m:=256) (b:=13716003898649272) (c:=10229902842679430)
                (span_join (a:=1537) (n:=128) (m:=128) (b:=7339618749997495) (c:=6376385148651777)
                  (span_join (a:=1537) (n:=64) (m:=64) (b:=3847648059927072) (c:=3491970690070423)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=1665) (n:=64) (m:=64) (b:=3291539370394158) (c:=3084845778257619)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=1793) (n:=128) (m:=128) (b:=5621451470556322) (c:=4608451372123108)
                  (span_join (a:=1793) (n:=64) (m:=64) (b:=2923075155307962) (c:=2698376315248360)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=1921) (n:=64) (m:=64) (b:=2451401647475089) (c:=2157049724648019)
                    (by decide +kernel)
                    (by decide +kernel))))))
          (span_join (a:=2049) (n:=1024) (m:=1024) (b:=24322329872482790) (c:=12404191664828122)
            (span_join (a:=2049) (n:=512) (m:=512) (b:=14499752126702347) (c:=9822577745780443)
              (span_join (a:=2049) (n:=256) (m:=256) (b:=8106599203985273) (c:=6393152922717074)
                (span_join (a:=2049) (n:=128) (m:=128) (b:=4310825982727252) (c:=3795773221258021)
                  (span_join (a:=2049) (n:=64) (m:=64) (b:=2189689977827967) (c:=2121136004899285)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=2177) (n:=64) (m:=64) (b:=1972284888868856) (c:=1823488332389165)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=2305) (n:=128) (m:=128) (b:=3335907713443219) (c:=3057245209273855)
                  (span_join (a:=2305) (n:=64) (m:=64) (b:=1709356978793367) (c:=1626550734649852)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=2433) (n:=64) (m:=64) (b:=1561869361633414) (c:=1495375847640441)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=2561) (n:=256) (m:=256) (b:=5385324895553303) (c:=4437252850227140)
                (span_join (a:=2561) (n:=128) (m:=128) (b:=2822786285954700) (c:=2562538609598603)
                  (span_join (a:=2561) (n:=64) (m:=64) (b:=1449977761469536) (c:=1372808524485164)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=2689) (n:=64) (m:=64) (b:=1320653911135012) (c:=1241884698463591)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=2817) (n:=128) (m:=128) (b:=2318798755599758) (c:=2118454094627382)
                  (span_join (a:=2817) (n:=64) (m:=64) (b:=1182350257969156) (c:=1136448497630602)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=2945) (n:=64) (m:=64) (b:=1100180457534889) (c:=1018273637092493)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (span_join (a:=3073) (n:=512) (m:=512) (b:=7078026310964469) (c:=5326165353863653)
              (span_join (a:=3073) (n:=256) (m:=256) (b:=3781276720767510) (c:=3296749590196959)
                (span_join (a:=3073) (n:=128) (m:=128) (b:=1979333639100963) (c:=1801943081666547)
                  (span_join (a:=3073) (n:=64) (m:=64) (b:=1013486736231593) (c:=965846902869370)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=3201) (n:=64) (m:=64) (b:=915306651123727) (c:=886636430542820)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=3329) (n:=128) (m:=128) (b:=1700131216219538) (c:=1596618373977421)
                  (span_join (a:=3329) (n:=64) (m:=64) (b:=864319971284980) (c:=835811244934558)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=3457) (n:=64) (m:=64) (b:=809295453395191) (c:=787322920582230)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=3585) (n:=256) (m:=256) (b:=2917114654100836) (c:=2409050699762817)
                (span_join (a:=3585) (n:=128) (m:=128) (b:=1514559649398100) (c:=1402555004702736)
                  (span_join (a:=3585) (n:=64) (m:=64) (b:=774112074789160) (c:=740447574608940)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=3713) (n:=64) (m:=64) (b:=717073125822456) (c:=685481878880280)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=3841) (n:=128) (m:=128) (b:=1278403109388144) (c:=1130647590374673)
                  (span_join (a:=3841) (n:=64) (m:=64) (b:=657380106842108) (c:=621023002546036)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=3969) (n:=64) (m:=64) (b:=585081982336479) (c:=545565608038194)
                    (by decide +kernel)
                    (by decide +kernel)))))))
        (span_join (a:=4097) (n:=2048) (m:=2048) (b:=12912507036385901) (c:=6903514702946347)
          (span_join (a:=4097) (n:=1024) (m:=1024) (b:=7636726048687655) (c:=5275780987698246)
            (span_join (a:=4097) (n:=512) (m:=512) (b:=4250619457892294) (c:=3386106590795361)
              (span_join (a:=4097) (n:=256) (m:=256) (b:=2253511511258591) (c:=1997107946633703)
                (span_join (a:=4097) (n:=128) (m:=128) (b:=1143065225890736) (c:=1110446285367855)
                  (span_join (a:=4097) (n:=64) (m:=64) (b:=567946237625358) (c:=575118988265378)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=4225) (n:=64) (m:=64) (b:=564181629088208) (c:=546264656279647)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=4353) (n:=128) (m:=128) (b:=1035863395228273) (c:=961244551405430)
                  (span_join (a:=4353) (n:=64) (m:=64) (b:=527338713095637) (c:=508524682132636)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=4481) (n:=64) (m:=64) (b:=490074699031947) (c:=471169852373483)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=4609) (n:=256) (m:=256) (b:=1763688130964770) (c:=1622418459830591)
                (span_join (a:=4609) (n:=128) (m:=128) (b:=902793461497365) (c:=860894669467405)
                  (span_join (a:=4609) (n:=64) (m:=64) (b:=459298484405069) (c:=443494977092296)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=4737) (n:=64) (m:=64) (b:=436535341424761) (c:=424359328042644)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=4865) (n:=128) (m:=128) (b:=827685060626811) (c:=794733399203780)
                  (span_join (a:=4865) (n:=64) (m:=64) (b:=416612203385218) (c:=411072857241593)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=4993) (n:=64) (m:=64) (b:=406609542409760) (c:=388123856794020)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (span_join (a:=5121) (n:=512) (m:=512) (b:=2877054750458635) (c:=2398726237239611)
              (span_join (a:=5121) (n:=256) (m:=256) (b:=1503690952688903) (c:=1373363797769732)
                (span_join (a:=5121) (n:=128) (m:=128) (b:=771045671516727) (c:=732645281172176)
                  (span_join (a:=5121) (n:=64) (m:=64) (b:=390396976962353) (c:=380648694554374)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=5249) (n:=64) (m:=64) (b:=369275709520512) (c:=363369571651664)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=5377) (n:=128) (m:=128) (b:=706380524873760) (c:=666983272895972)
                  (span_join (a:=5377) (n:=64) (m:=64) (b:=357842526704703) (c:=348537998169057)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=5505) (n:=64) (m:=64) (b:=338144957313921) (c:=328838315582051)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=5633) (n:=256) (m:=256) (b:=1249611064537849) (c:=1149115172701762)
                (span_join (a:=5633) (n:=128) (m:=128) (b:=636448369045662) (c:=613162695492187)
                  (span_join (a:=5633) (n:=64) (m:=64) (b:=323255422531444) (c:=313192946514218)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=5761) (n:=64) (m:=64) (b:=309038528470225) (c:=304124167021962)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=5889) (n:=128) (m:=128) (b:=594988457721370) (c:=554126714980392)
                  (span_join (a:=5889) (n:=64) (m:=64) (b:=301047494241868) (c:=293940963479502)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=6017) (n:=64) (m:=64) (b:=284298696762059) (c:=269828018218333)
                    (by decide +kernel)
                    (by decide +kernel))))))
          (span_join (a:=6145) (n:=1024) (m:=1024) (b:=3887845472340791) (c:=3015669230605556)
            (span_join (a:=6145) (n:=512) (m:=512) (b:=2066014961576240) (c:=1821830510764551)
              (span_join (a:=6145) (n:=256) (m:=256) (b:=1077689503133840) (c:=988325458442400)
                (span_join (a:=6145) (n:=128) (m:=128) (b:=550302758675672) (c:=527386744458168)
                  (span_join (a:=6145) (n:=64) (m:=64) (b:=275392346874827) (c:=274910411800845)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=6273) (n:=64) (m:=64) (b:=267817095465767) (c:=259569648992401)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=6401) (n:=128) (m:=128) (b:=501478174847616) (c:=486847283594784)
                  (span_join (a:=6401) (n:=64) (m:=64) (b:=253003269199328) (c:=248474905648288)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=6529) (n:=64) (m:=64) (b:=245157989482466) (c:=241689294112318)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=6657) (n:=256) (m:=256) (b:=936766077272121) (c:=885064433492430)
                (span_join (a:=6657) (n:=128) (m:=128) (b:=475402553558792) (c:=461363523713329)
                  (span_join (a:=6657) (n:=64) (m:=64) (b:=240016081349407) (c:=235386472209385)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=6785) (n:=64) (m:=64) (b:=233207021362019) (c:=228156502351310)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=6913) (n:=128) (m:=128) (b:=447803275649237) (c:=437261157843193)
                  (span_join (a:=6913) (n:=64) (m:=64) (b:=224867982006730) (c:=222935293642507)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=7041) (n:=64) (m:=64) (b:=222055854019808) (c:=215205303823385)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (span_join (a:=7169) (n:=512) (m:=512) (b:=1634808384390977) (c:=1380860846214579)
              (span_join (a:=7169) (n:=256) (m:=256) (b:=844771894968486) (c:=790036489422491)
                (span_join (a:=7169) (n:=128) (m:=128) (b:=430555343019472) (c:=414216551949014)
                  (span_join (a:=7169) (n:=64) (m:=64) (b:=217045769448568) (c:=213509573570904)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=7297) (n:=64) (m:=64) (b:=208500166529773) (c:=205716385419241)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=7425) (n:=128) (m:=128) (b:=402775487564993) (c:=387261001857498)
                  (span_join (a:=7425) (n:=64) (m:=64) (b:=203272567413024) (c:=199502920151969)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=7553) (n:=64) (m:=64) (b:=195410227486157) (c:=191850774371341)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=7681) (n:=256) (m:=256) (b:=728429418982251) (c:=652431427232328)
                (span_join (a:=7681) (n:=128) (m:=128) (b:=373280312212343) (c:=355149106769908)
                  (span_join (a:=7681) (n:=64) (m:=64) (b:=189390248314183) (c:=183890063898160)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=7809) (n:=64) (m:=64) (b:=180055786276082) (c:=175093320493826)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=7937) (n:=128) (m:=128) (b:=336715036756199) (c:=315716390476129)
                  (span_join (a:=7937) (n:=64) (m:=64) (b:=170975846447339) (c:=165739190308860)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=8065) (n:=64) (m:=64) (b:=160724808868752) (c:=154991581607377)
                    (by decide +kernel)
                    (by decide +kernel))))))))
      (span_join (a:=8193) (n:=4096) (m:=4095) (b:=7981127153688747) (c:=5475977002870001)
        (span_join (a:=8193) (n:=2048) (m:=2048) (b:=4538327205060850) (c:=3442799948627897)
          (span_join (a:=8193) (n:=1024) (m:=1024) (b:=2478987740486097) (c:=2059339464574753)
            (span_join (a:=8193) (n:=512) (m:=512) (b:=1299364432052802) (c:=1179623308433295)
              (span_join (a:=8193) (n:=256) (m:=256) (b:=655744109621148) (c:=643620322431654)
                (span_join (a:=8193) (n:=128) (m:=128) (b:=325305385351384) (c:=330438724269764)
                  (span_join (a:=8193) (n:=64) (m:=64) (b:=160590763786041) (c:=164714621565343)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=8321) (n:=64) (m:=64) (b:=165535154895036) (c:=164903569374728)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=8449) (n:=128) (m:=128) (b:=325886479420158) (c:=317733843011496)
                  (span_join (a:=8449) (n:=64) (m:=64) (b:=163711254156524) (c:=162175225263634)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=8577) (n:=64) (m:=64) (b:=160148247499772) (c:=157585595511724)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=8705) (n:=256) (m:=256) (b:=608063755060498) (c:=571559553372797)
                (span_join (a:=8705) (n:=128) (m:=128) (b:=308525097971119) (c:=299538657089379)
                  (span_join (a:=8705) (n:=64) (m:=64) (b:=155789910972841) (c:=152735186998278)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=8833) (n:=64) (m:=64) (b:=151247007691739) (c:=148291649397640)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=8961) (n:=128) (m:=128) (b:=290309870624143) (c:=281249682748654)
                  (span_join (a:=8961) (n:=64) (m:=64) (b:=146050182586959) (c:=144259688037184)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=9089) (n:=64) (m:=64) (b:=142925353848932) (c:=138324328899722)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (span_join (a:=9217) (n:=512) (m:=512) (b:=1063285233447129) (c:=996054231127624)
              (span_join (a:=9217) (n:=256) (m:=256) (b:=541887915094474) (c:=521397318352655)
                (span_join (a:=9217) (n:=128) (m:=128) (b:=274902296490138) (c:=266985618604336)
                  (span_join (a:=9217) (n:=64) (m:=64) (b:=138434874114667) (c:=136467422375471)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=9345) (n:=64) (m:=64) (b:=133955899020040) (c:=133029719584296)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=9473) (n:=128) (m:=128) (b:=263652402111381) (c:=257744916241274)
                  (span_join (a:=9473) (n:=64) (m:=64) (b:=132473762558971) (c:=131178639552410)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=9601) (n:=64) (m:=64) (b:=129514625272698) (c:=128230290968576)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=9729) (n:=256) (m:=256) (b:=505139511645941) (c:=490914719481683)
                (span_join (a:=9729) (n:=128) (m:=128) (b:=253833628128395) (c:=251305883517546)
                  (span_join (a:=9729) (n:=64) (m:=64) (b:=127754670254331) (c:=126078957874064)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=9857) (n:=64) (m:=64) (b:=125881520475281) (c:=125424363042265)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=9985) (n:=128) (m:=128) (b:=249848220872507) (c:=241066498609176)
                  (span_join (a:=9985) (n:=64) (m:=64) (b:=125476323214571) (c:=124371897657936)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=10113) (n:=64) (m:=64) (b:=122405683073479) (c:=118660815535697)
                    (by decide +kernel)
                    (by decide +kernel))))))
          (span_join (a:=10241) (n:=1024) (m:=1024) (b:=1828574412494301) (c:=1614225536133596)
            (span_join (a:=10241) (n:=512) (m:=512) (b:=942710365440906) (c:=885864047053395)
              (span_join (a:=10241) (n:=256) (m:=256) (b:=480015976852075) (c:=462694388588831)
                (span_join (a:=10241) (n:=128) (m:=128) (b:=241771528656375) (c:=238244448195700)
                  (span_join (a:=10241) (n:=64) (m:=64) (b:=120459212464654) (c:=121312316191721)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=10369) (n:=64) (m:=64) (b:=120018000754986) (c:=118226447440714)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=10497) (n:=128) (m:=128) (b:=232632788805058) (c:=230061599783773)
                  (span_join (a:=10497) (n:=64) (m:=64) (b:=116747851020139) (c:=115884937784919)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=10625) (n:=64) (m:=64) (b:=115299549445064) (c:=114762050338709)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=10753) (n:=256) (m:=256) (b:=451918274250321) (c:=433945772803074)
                (span_join (a:=10753) (n:=128) (m:=128) (b:=227872733410325) (c:=224045540839996)
                  (span_join (a:=10753) (n:=64) (m:=64) (b:=114532879922564) (c:=113339853487761)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=10881) (n:=64) (m:=64) (b:=112830196171292) (c:=111215344668704)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=11009) (n:=128) (m:=128) (b:=219011796802522) (c:=214933976000552)
                  (span_join (a:=11009) (n:=64) (m:=64) (b:=109949919347130) (c:=109061877455392)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=11137) (n:=64) (m:=64) (b:=108676389169293) (c:=106257586831259)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (span_join (a:=11265) (n:=512) (m:=512) (b:=828194988659765) (c:=786030547473831)
              (span_join (a:=11265) (n:=256) (m:=256) (b:=419411067546729) (c:=408783921113036)
                (span_join (a:=11265) (n:=128) (m:=128) (b:=212111933049158) (c:=207299134497571)
                  (span_join (a:=11265) (n:=64) (m:=64) (b:=106500412929685) (c:=105611520119473)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=11393) (n:=64) (m:=64) (b:=103989912397135) (c:=103309222100436)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=11521) (n:=128) (m:=128) (b:=205423725348225) (c:=203360195764811)
                  (span_join (a:=11521) (n:=64) (m:=64) (b:=102984087425563) (c:=102439637922662)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=11649) (n:=64) (m:=64) (b:=101786914647424) (c:=101573281117387)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=11777) (n:=256) (m:=256) (b:=402439001458082) (c:=383591546015749)
                (span_join (a:=11777) (n:=128) (m:=128) (b:=202538072696379) (c:=199900928761703)
                  (span_join (a:=11777) (n:=64) (m:=64) (b:=101711554994414) (c:=100826517701965)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=11905) (n:=64) (m:=64) (b:=100436589351063) (c:=99464339410640)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=12033) (n:=128) (m:=128) (b:=195696581582577) (c:=187894964433172)
                  (span_join (a:=12033) (n:=64) (m:=64) (b:=98615254583384) (c:=97081326999193)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=12161) (n:=64) (m:=64) (b:=95271870280808) (c:=92623094152364)
                    (by decide +kernel)
                    (by decide +kernel)))))))
        (span_join (a:=12289) (n:=2048) (m:=2047) (b:=2853080353807335) (c:=2622896649062666)
          (span_join (a:=12289) (n:=1024) (m:=1024) (b:=1471556114378467) (c:=1381524239428868)
            (span_join (a:=12289) (n:=512) (m:=512) (b:=754867417200395) (c:=716688697178072)
              (span_join (a:=12289) (n:=256) (m:=256) (b:=380894262650807) (c:=373973154549588)
                (span_join (a:=12289) (n:=128) (m:=128) (b:=189561933242844) (c:=191332329407963)
                  (span_join (a:=12289) (n:=64) (m:=64) (b:=93947794119159) (c:=95614139123685)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=12417) (n:=64) (m:=64) (b:=95855290646843) (c:=95477038761120)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=12545) (n:=128) (m:=128) (b:=188788283386821) (c:=185184871162767)
                  (span_join (a:=12545) (n:=64) (m:=64) (b:=94770459381841) (c:=94017824004980)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=12673) (n:=64) (m:=64) (b:=93059360152100) (c:=92125511010667)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=12801) (n:=256) (m:=256) (b:=361463811184750) (c:=355224885993322)
                (span_join (a:=12801) (n:=128) (m:=128) (b:=181781041054114) (c:=179682770130636)
                  (span_join (a:=12801) (n:=64) (m:=64) (b:=91395258208445) (c:=90385782845669)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=12929) (n:=64) (m:=64) (b:=90188169690805) (c:=89494600439831)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=13057) (n:=128) (m:=128) (b:=178061587373564) (c:=177163298619758)
                  (span_join (a:=13057) (n:=64) (m:=64) (b:=89098511650629) (c:=88963075722935)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=13185) (n:=64) (m:=64) (b:=89207278740232) (c:=87956019879526)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (span_join (a:=13313) (n:=512) (m:=512) (b:=698653326946175) (c:=682870912482693)
              (span_join (a:=13313) (n:=256) (m:=256) (b:=351370816060238) (c:=347282510885937)
                (span_join (a:=13313) (n:=128) (m:=128) (b:=176527597505911) (c:=174843218554327)
                  (span_join (a:=13313) (n:=64) (m:=64) (b:=88290372162990) (c:=88237225342921)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=13441) (n:=64) (m:=64) (b:=87480312063164) (c:=87362906491163)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=13569) (n:=128) (m:=128) (b:=174590600782539) (c:=172691910103398)
                  (span_join (a:=13569) (n:=64) (m:=64) (b:=87417842137960) (c:=87172758644579)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=13697) (n:=64) (m:=64) (b:=86534543844194) (c:=86157366259204)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=13825) (n:=256) (m:=256) (b:=342066634373822) (c:=340804278108871)
                (span_join (a:=13825) (n:=128) (m:=128) (b:=171291609772387) (c:=170775024601435)
                  (span_join (a:=13825) (n:=64) (m:=64) (b:=85962298930835) (c:=85329310841552)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=13953) (n:=64) (m:=64) (b:=85375319188377) (c:=85399705413058)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=14081) (n:=128) (m:=128) (b:=171638063959717) (c:=169166214149154)
                  (span_join (a:=14081) (n:=64) (m:=64) (b:=85817436709911) (c:=85820627249806)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=14209) (n:=64) (m:=64) (b:=85390925499833) (c:=83775288649321)
                    (by decide +kernel)
                    (by decide +kernel))))))
          (span_join (a:=14337) (n:=1024) (m:=1023) (b:=1346511018548887) (c:=1276385630513779)
            (span_join (a:=14337) (n:=512) (m:=512) (b:=677761284470199) (c:=668749734078688)
              (span_join (a:=14337) (n:=256) (m:=256) (b:=340690709390238) (c:=337070575079961)
                (span_join (a:=14337) (n:=128) (m:=128) (b:=170049557768745) (c:=170641151621493)
                  (span_join (a:=14337) (n:=64) (m:=64) (b:=84425261543874) (c:=85624296224871)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=14465) (n:=64) (m:=64) (b:=85561466153739) (c:=85079685467754)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=14593) (n:=128) (m:=128) (b:=168784988078319) (c:=168285587001642)
                  (span_join (a:=14593) (n:=64) (m:=64) (b:=84515229758980) (c:=84269758319339)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=14721) (n:=64) (m:=64) (b:=84100023865641) (c:=84185563136001)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=14849) (n:=256) (m:=256) (b:=336021500838923) (c:=332728233239765)
                (span_join (a:=14849) (n:=128) (m:=128) (b:=168212919194415) (c:=167808581644508)
                  (span_join (a:=14849) (n:=64) (m:=64) (b:=84237349993279) (c:=83975569201136)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=14977) (n:=64) (m:=64) (b:=84117344141577) (c:=83691237502931)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=15105) (n:=128) (m:=128) (b:=166494937378660) (c:=166233295861105)
                  (span_join (a:=15105) (n:=64) (m:=64) (b:=83324479971916) (c:=83170457406744)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=15233) (n:=64) (m:=64) (b:=83500881135542) (c:=82732414725563)
                    (by decide +kernel)
                    (by decide +kernel)))))
            (span_join (a:=15361) (n:=512) (m:=511) (b:=655532099664821) (c:=620853530848958)
              (span_join (a:=15361) (n:=256) (m:=256) (b:=330336731717997) (c:=325195367946824)
                (span_join (a:=15361) (n:=128) (m:=128) (b:=165925974110210) (c:=164410757607787)
                  (span_join (a:=15361) (n:=64) (m:=64) (b:=82850655750692) (c:=83075318359518)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=15489) (n:=64) (m:=64) (b:=82363722568033) (c:=82047035039754)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=15617) (n:=128) (m:=128) (b:=163487171348318) (c:=161708196598506)
                  (span_join (a:=15617) (n:=64) (m:=64) (b:=81881759669552) (c:=81605411678766)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=15745) (n:=64) (m:=64) (b:=80982372979717) (c:=80725823618789)
                    (by decide +kernel)
                    (by decide +kernel))))
              (span_join (a:=15873) (n:=256) (m:=255) (b:=318004584404584) (c:=302848946444374)
                (span_join (a:=15873) (n:=128) (m:=128) (b:=160206780591639) (c:=157797803812945)
                  (span_join (a:=15873) (n:=64) (m:=64) (b:=80444438105358) (c:=79762342486281)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=16001) (n:=64) (m:=64) (b:=79285771831208) (c:=78512031981737)
                    (by decide +kernel)
                    (by decide +kernel)))
                (span_join (a:=16129) (n:=128) (m:=127) (b:=154762251225708) (c:=148086695218666)
                  (span_join (a:=16129) (n:=64) (m:=64) (b:=77862116338814) (c:=76900134886894)
                    (by decide +kernel)
                    (by decide +kernel))
                  (span_join (a:=16257) (n:=64) (m:=63) (b:=75747766845064) (c:=72338928373602)
                    (by decide +kernel)
                    (by decide +kernel)))))))))
  exact congrArg₂ (·+·) endpoint batch

end OMA.White241

theorem OMA.solution : type_of% @Erdos241.erdos_241.variants.upper_bound_white :=
  OMA.WhiteBridge241.upper (OMA.White241.whole_period_of_checks OMA.White241.checked_angles OMA.White241.checked_sum)
