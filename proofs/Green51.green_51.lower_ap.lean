import FormalConjectures.GreensOpenProblems.«51»
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.NumberTheory.Bertrand

/-!
The arithmetic-progression lower bound via a sparse Fourier approximation. The probabilistic
Fourier selection is the idea of Croot, Łaba, and Sisask (arXiv:1103.6000). A pointwise deviation
bound controls the number of exceptional positions, which suffices for the progression.
-/

open Filter Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace SumsetAP

private def sampleAverage {ι X : Type*} {m : ℕ} (f : ι → X → ℝ)
    (w : Fin m → ι) (x : X) :=
  (∑ i, f (w i) x) / (m : ℝ)

private lemma sample_bad_bound {ι X : Type*} [Fintype ι] [Fintype X]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (μ : Measure ι)
    [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m) (f : ι → X → ℝ)
    (hf : ∀ a x, f a x ∈ Set.Icc (-1 : ℝ) 1) (e : ℝ) (he : 0 < e) :
    ∃ w : Fin m → ι, (((univ : Finset X).filter fun x =>
      e < |sampleAverage f w x - ∫ a, f a x ∂μ|).card : ℝ) ≤
        2 * Real.exp (-(m : ℝ) * e ^ 2 / 2) * Fintype.card X := by
  classical
  let ν : Measure (Fin m → ι) := Measure.pi fun _ => μ
  let F (i : Fin m) (w : Fin m → ι) (x : X) := f (w i) x
  let g (x : X) := ∫ a, f a x ∂μ
  let B (x : X) : Set (Fin m → ι) := {w | e < |sampleAverage f w x - g x|}
  have hF (x : X) : ∀ i, Measurable (fun w => F i w x) := fun i =>
    (measurable_of_countable (fun a => f a x)).comp (measurable_pi_apply i)
  have hB (x : X) : MeasurableSet (B x) := by
    unfold B sampleAverage
    exact measurableSet_lt measurable_const
      (((Finset.measurable_sum univ (fun i _ => hF x i)).div_const _).sub_const _).abs
  let : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin m => μ))
  have hmass (x : X) : ν.real (B x) ≤ 2 * Real.exp (-(m : ℝ) * e ^ 2 / 2) := by
    have hmean (i : Fin m) : ∫ w, F i w x ∂ν = g x := by
      have H := integral_map (μ := ν) (measurable_pi_apply i).aemeasurable
        (f := fun a => f a x) (measurable_of_countable (fun a => f a x)).aestronglyMeasurable
      rw [(measurePreserving_eval (fun _ : Fin m => μ) i).map_eq] at H
      exact H.symm
    have hsub (i : Fin m) : HasSubgaussianMGF (fun w => F i w x - g x) 1 ν := by
      convert hasSubgaussianMGF_of_mem_Icc (μ := ν) (hF x i).aemeasurable
        (Filter.Eventually.of_forall (fun w => hf (w i) x)) using 1
      · simp [hmean]
      · norm_num [Real.nnnorm_of_nonneg]
    have hind : iIndepFun (fun i (w : Fin m → ι) => F i w x) ν :=
      iIndepFun_pi (X := fun _ => fun a => f a x)
        (fun _ => (measurable_of_countable (fun a => f a x)).aemeasurable)
    have hind' := hind.comp (fun (_ : Fin m) (g₀ : ℝ) => g₀ - g x)
      (fun _ => measurable_id.sub_const _)
    let D (w : Fin m → ι) := (∑ i : Fin m, F i w x) - m * g x
    have hD : HasSubgaussianMGF D (m : ℝ≥0) ν := by
      simpa [D, Finset.sum_sub_distrib] using
        HasSubgaussianMGF.sum_of_iIndepFun hind' (s := univ) (fun i _ => hsub i)
    have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
    have hthreshold : 0 ≤ (m : ℝ) * e := (mul_pos hmr he).le
    have hplus := hD.measure_ge_le hthreshold
    have hminus := hD.neg.measure_ge_le hthreshold
    have hexp : -((m : ℝ) * e) ^ 2 / (2 * (m : ℝ)) = -(m : ℝ) * e ^ 2 / 2 := by
      field_simp
    rw [NNReal.coe_natCast, hexp] at hplus hminus
    have hsubset : B x ⊆ {w | (m : ℝ) * e ≤ D w} ∪ {w | (m : ℝ) * e ≤ -D w} := by
      intro w hw
      change e < |(∑ i : Fin m, F i w x) / (m : ℝ) - g x| at hw
      rw [lt_abs] at hw
      change (m : ℝ) * e ≤ D w ∨ (m : ℝ) * e ≤ -D w
      rcases hw with hp | hp
      · left
        have H := (lt_div_iff₀ hmr).mp (show e + g x < (∑ i, F i w x) / (m : ℝ) by linarith)
        dsimp [D]
        linarith
      · right
        have H := (div_lt_iff₀ hmr).mp (show (∑ i, F i w x) / (m : ℝ) < g x - e by linarith)
        dsimp [D]
        linarith
    calc
      ν.real (B x) ≤ ν.real ({w | (m : ℝ) * e ≤ D w} ∪ {w | (m : ℝ) * e ≤ -D w}) :=
        measureReal_mono hsubset
      _ ≤ _ := (measureReal_union_le _ _).trans (by rw [two_mul]; exact add_le_add hplus hminus)
  let score (w : Fin m → ι) := (((univ : Finset X).filter fun x => w ∈ B x).card : ℝ)
  have hscore (w : Fin m → ι) : score w = ∑ x : X, (B x).indicator (fun _ => (1:ℝ)) w := by
    simp [score, Set.indicator_apply]
  have hint (x : X) : Integrable ((B x).indicator (fun _ => (1 : ℝ))) ν :=
    (integrable_const (1 : ℝ)).indicator (hB x)
  have havg : (∫ w, score w ∂ν) ≤ 2 * Real.exp (-(m : ℝ) * e ^ 2 / 2) * Fintype.card X := by
    simp_rw [hscore]
    rw [integral_finsetSum _ (fun x _ => hint x), mul_comm, ← nsmul_eq_mul,
      ← Finset.card_univ, ← Finset.sum_const]
    apply sum_le_sum
    intro x hx
    simpa [integral_indicator_const _ (hB x)] using hmass x
  have hne : Nonempty (Fin m → ι) := by
    have : Nonempty ι := MeasureTheory.nonempty_of_isProbabilityMeasure μ
    infer_instance
  have hi : Integrable score ν := by
    simp_rw [show score = fun w => ∑ x : X, (B x).indicator (fun _ => (1:ℝ)) w from funext hscore]
    exact integrable_finsetSum _ fun x _ => hint x
  obtain ⟨w, -, hmin⟩ := Finset.exists_min_image univ score Finset.univ_nonempty
  have hb : score w ≤ (∫ w', score w' ∂ν) := by
    simpa using (integral_mono (integrable_const (score w)) hi (fun w' => hmin w' (mem_univ w')))
  exact ⟨w,hb.trans havg⟩

end SumsetAP

open Finset ZMod
open scoped BigOperators ZMod ComplexConjugate

noncomputable section

namespace SumsetAP

private def indicatorC {p : ℕ} (A : Finset (ZMod p)) (x : ZMod p) : ℂ :=
  if x ∈ A then 1 else 0

private def convC {p : ℕ} [NeZero p] (A : Finset (ZMod p)) (x : ZMod p) : ℂ :=
  ∑ y, indicatorC A y * indicatorC A (x-y)

private def convR {p : ℕ} [NeZero p] (A : Finset (ZMod p)) (x : ZMod p) : ℝ :=
  ((convC A x).re) / (p : ℝ)

private def coeff {p : ℕ} [NeZero p] (A : Finset (ZMod p)) (ξ : ZMod p) : ℂ :=
  (ZMod.dft (indicatorC A) ξ / (p : ℂ)) ^ 2

private lemma convDft {p : ℕ} [NeZero p] (A : Finset (ZMod p)) (ξ : ZMod p) :
    (ZMod.dft (convC A) ξ) = (ZMod.dft (indicatorC A) ξ)^2 := by
  simp only [ZMod.dft_apply, smul_eq_mul, convC, mul_sum, pow_two, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro y hy
  refine Fintype.sum_equiv (Equiv.subRight y) _ _ ?_
  intro x
  simp only [Equiv.subRight_apply]
  rw [show -(x*ξ) = -(y*ξ) + -((x-y)*ξ) by ring, AddChar.map_add_eq_mul]
  ring

private lemma inversion {p : ℕ} [NeZero p] (A : Finset (ZMod p)) (x : ZMod p) :
    convR A x = (∑ ξ : ZMod p, coeff A ξ * ZMod.stdAddChar (ξ*x)).re := by
  have H : (ZMod.dft (ZMod.dft (convC A)) (-x)) = (p : ℂ) * convC A x := by
    rw [ZMod.dft_dft]
    simp [smul_eq_mul]
  rw [ZMod.dft_apply] at H
  simp_rw [mul_neg, neg_neg, smul_eq_mul, convDft] at H
  have hnp : (p : ℂ) ≠ 0 := NeZero.ne _
  have hEq : (∑ ξ : ZMod p, coeff A ξ * ZMod.stdAddChar (ξ*x)) =
      (convC A x) / (p : ℂ) := by
    simp_rw [coeff, div_pow, div_mul_eq_mul_div, mul_comm _ (ZMod.stdAddChar _)]
    rw [← sum_div, H]
    field_simp
  rw [hEq, convR]
  simp only [Complex.div_natCast_re]

private lemma stdChar_conj {p : ℕ} [NeZero p] (x : ZMod p) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  simp only [ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj]
  congr 1
  exact (ZMod.toCircle.map_neg_eq_inv x).symm

private lemma parseval_indicator {p : ℕ} [NeZero p] (A : Finset (ZMod p)) :
    (∑ ξ : ZMod p, ‖ZMod.dft (indicatorC A) ξ‖ ^ 2) = (p : ℝ) * A.card := by
  let D := ZMod.dft (indicatorC A)
  have hconj (ξ : ZMod p) : conj (D ξ) =
      ∑ x : ZMod p, ZMod.stdAddChar (x*ξ) * indicatorC A x := by
    simp only [D, ZMod.dft_apply, smul_eq_mul, map_sum, map_mul, stdChar_conj, neg_neg]
    apply sum_congr rfl
    intro x hx
    by_cases h : x ∈ A <;> simp [indicatorC, h]
  have H : (∑ ξ : ZMod p, D ξ * conj (D ξ)) = (p : ℂ) * A.card := by
    simp_rw [hconj, mul_sum]
    rw [sum_comm]
    simp_rw [← mul_assoc, ← sum_mul]
    have hx (x : ZMod p) : (∑ ξ : ZMod p, D ξ * ZMod.stdAddChar (x*ξ)) =
        (p : ℂ) * indicatorC A x := by
      have h : (ZMod.dft D (-x)) = (p : ℂ) * indicatorC A x := by
        change ZMod.dft (ZMod.dft (indicatorC A)) (-x) = _
        rw [ZMod.dft_dft]
        simp [smul_eq_mul]
      rw [ZMod.dft_apply] at h
      simpa only [smul_eq_mul, mul_neg, neg_neg, mul_comm] using h
    simp_rw [hx, mul_assoc]
    rw [← mul_sum]
    congr 1
    simp [indicatorC]
  have hnorm (ξ : ZMod p) : (D ξ * conj (D ξ)).re = ‖D ξ‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.sq_norm, Complex.ofReal_re]
  have HR := congrArg Complex.re H
  simp only [Complex.re_sum, hnorm, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero] at HR
  exact HR

private lemma coeffMass {p : ℕ} [NeZero p] (A : Finset (ZMod p)) :
    (∑ ξ : ZMod p, ‖coeff A ξ‖) = (A.card : ℝ) / (p : ℝ) := by
  simp_rw [coeff, norm_pow, norm_div, Complex.norm_natCast, div_pow]
  rw [← sum_div, parseval_indicator]
  have hp : (p : ℝ) ≠ 0 := NeZero.ne _
  field_simp

private lemma convMean {p : ℕ} [NeZero p] (A : Finset (ZMod p)) :
    (∑ x : ZMod p, convR A x) = (A.card : ℝ)^2 / (p : ℝ) := by
  simp only [convR, ← sum_div, convC, Complex.re_sum]
  congr 1
  rw [sum_comm]
  have hsum (y : ZMod p) : (∑ x : ZMod p, (indicatorC A y * indicatorC A (x-y)).re) =
      (if y ∈ A then (A.card : ℝ) else 0) := by
    refine (Fintype.sum_equiv (Equiv.subRight y) _ (fun x =>
      (indicatorC A y * indicatorC A x).re) (by intro x; rfl)).trans ?_
    by_cases h : y ∈ A
    · simp [indicatorC, h, apply_ite]
    · simp [indicatorC, h]
  simp_rw [hsum]
  rw [← sum_filter]
  have H : (univ : Finset (ZMod p)).filter (· ∈ A) = A := by ext; simp
  simp [H, pow_two]

private lemma convR_range {p : ℕ} [NeZero p] (A : Finset (ZMod p)) (x : ZMod p) :
    convR A x ∈ Set.Icc (0 : ℝ) 1 := by
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (NeZero.pos p)
  have hunit (y : ZMod p) : (indicatorC A y * indicatorC A (x-y)).re ∈ Set.Icc (0:ℝ) 1 := by
    by_cases h : y ∈ A <;> by_cases h' : x-y ∈ A <;> simp [indicatorC, h, h']
  refine ⟨div_nonneg ?_ hp.le, (div_le_one hp).mpr ?_⟩
  · simp only [convC, Complex.re_sum]
    exact sum_nonneg fun y _ => (hunit y).1
  · simp only [convC, Complex.re_sum]
    calc
      _ ≤ ∑ _y : ZMod p, (1 : ℝ) := sum_le_sum fun y _ => (hunit y).2
      _ = p := by simp [ZMod.card]

private lemma convR_pos_mem_add {p : ℕ} [NeZero p] (A : Finset (ZMod p)) {x : ZMod p}
    (hx : 0 < convR A x) : ∃ y ∈ A, ∃ z ∈ A, x = y + z := by
  by_contra! h
  have H : convR A x = 0 := by
    unfold convR convC
    rw [Complex.re_sum, sum_eq_zero, zero_div]
    intro y hy
    by_cases h' : y ∈ A
    · have hz : x-y ∉ A := fun hz => h y h' (x-y) hz (by ring)
      simp [indicatorC, h', hz]
    · simp [indicatorC, h']
  linarith

end SumsetAP

open Finset ZMod
open scoped BigOperators

noncomputable section

namespace SumsetAP

private lemma commonIncrement {p m K : ℕ} [NeZero p] (hK : 0 < K)
    (hsmall : K ^ m < p) (freq : Fin m → ZMod p) :
    ∃ d : ZMod p, d ≠ 0 ∧ ∀ (i : Fin m) (j : ℕ),
      ‖ZMod.stdAddChar (freq i * ((j : ZMod p) * d)) - 1‖ ≤ 2 * Real.pi * j / K := by
  classical
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr (NeZero.pos p)
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  let coord (z : ZMod p) := (K : ℝ) * z.val / p
  have hcoord₀ (z : ZMod p) : 0 ≤ coord z := by dsimp [coord]; positivity
  have hcoord (z : ZMod p) : coord z < (K : ℝ) := by
    have hz : (z.val : ℝ) < (p : ℝ) := by exact_mod_cast ZMod.val_lt z
    exact (div_lt_iff₀ hpR).mpr (mul_lt_mul_of_pos_left hz hKR)
  let key (x : ZMod p) (i : Fin m) : Fin K :=
    ⟨⌊coord (freq i*x)⌋₊, (Nat.floor_lt (hcoord₀ _)).mpr (hcoord _)⟩
  obtain ⟨x,y,hxy,hkey⟩ := Fintype.exists_ne_map_eq_of_card_lt key
    (by simpa [ZMod.card] using hsmall)
  refine ⟨y-x, sub_ne_zero.mpr hxy.symm, ?_⟩
  intro i j
  let a := (freq i*x).val
  let b := (freq i*y).val
  let t := (b:ℤ) - (a:ℤ)
  have hk : ⌊coord (freq i*x)⌋₊ = ⌊coord (freq i*y)⌋₊ :=
    congrArg Fin.val (congrFun hkey i)
  have hc₁ := Nat.floor_le (hcoord₀ (freq i*x))
  have hc₂ := Nat.floor_le (hcoord₀ (freq i*y))
  have hc₃ := Nat.lt_floor_add_one (coord (freq i*x))
  have hc₄ := Nat.lt_floor_add_one (coord (freq i*y))
  rw [← hk] at hc₂ hc₄
  have hd : |coord (freq i*y) - coord (freq i*x)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have htR : (t : ℝ) = (b : ℝ) - (a : ℝ) := by dsimp [t]; push_cast; rfl
  have ht : |(t : ℝ) / p| ≤ 1 / (K : ℝ) := by
    have hd' : |(K : ℝ) * ((t : ℝ) / p)| ≤ 1 := by
      rw [htR]
      have H : coord (freq i*y) - coord (freq i*x) =
          (K : ℝ) * (((b : ℝ) - (a : ℝ)) / p) := by
        dsimp [coord, a, b]
        ring
      rw [← H]
      exact hd
    rw [abs_mul, abs_of_pos hKR] at hd'
    apply (mul_le_mul_iff_of_pos_left hKR).mp
    rwa [mul_one_div_cancel hKR.ne']
  have htZ : ((t : ℤ) : ZMod p) = freq i * (y-x) := by
    dsimp [t,a,b]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, mul_sub]
  have harg : freq i * ((j : ZMod p) * (y-x)) = (((j : ℤ) * t : ℤ) : ZMod p) := by
    push_cast
    rw [htZ]
    ring
  rw [harg, ZMod.stdAddChar_coe]
  let r : ℝ := 2 * Real.pi * j * ((t : ℝ) / p)
  have hr : (2 : ℂ) * ↑Real.pi * Complex.I * ↑((j : ℤ) * t) / (p : ℂ) =
      Complex.I * (r : ℂ) := by
    dsimp [r]
    push_cast
    ring
  rw [hr]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := r)).trans ?_
  rw [Real.norm_eq_abs, show r = (2 * Real.pi * j) * ((t : ℝ) / p) from rfl,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 * Real.pi * j : ℝ))]
  exact (mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq (by ring)

end SumsetAP

open Set Finset
open scoped BigOperators Pointwise

noncomputable section

namespace SumsetAP

private lemma liftProgression {p N L : ℕ} [NeZero p] (hp : 4*N < p) (hL : 2 ≤ L)
    (S : Set ℕ) (hS : ∀ u ∈ S, u ≤ 2*N) (x d : ZMod p) (hd : d ≠ 0)
    (h : ∀ j : ℕ, j < L → (x + (j : ZMod p)*d).val ∈ S) :
    ∃ s ⊆ S, s.IsAPOfLength (L : ℕ∞) := by
  have hz (j : ℕ) (hj : j < L) : (x + (j : ZMod p)*d).val ≤ 2*N := hS _ (h j hj)
  let u := x.val
  let v := (x+d).val
  have hu : u ≤ 2*N := by simpa [u] using hz 0 (by omega)
  have hv : v ≤ 2*N := by simpa [v] using hz 1 (by omega)
  have huZ : (u : ZMod p) = x := ZMod.natCast_zmod_val x
  have hvZ : (v : ZMod p) = x+d := ZMod.natCast_zmod_val (x+d)
  have hdir : ∃ y e : ZMod p, e ≠ 0 ∧ e.val ≤ 2*N ∧
      ∀ j : ℕ, j < L → (y + (j : ZMod p)*e).val ∈ S := by
    by_cases huv : u ≤ v
    · have he : (v-u : ℕ) = d.val := by
        have H : ((v-u : ℕ) : ZMod p) = d := by rw [Nat.cast_sub huv, hvZ, huZ]; ring
        have hlt : v-u < p := by omega
        simpa [ZMod.val_natCast_of_lt hlt] using congrArg ZMod.val H
      exact ⟨x,d,hd,by omega,h⟩
    · have he : (u-v : ℕ) = (-d).val := by
        have H : ((u-v : ℕ) : ZMod p) = -d := by
          rw [Nat.cast_sub (by omega : v ≤ u), huZ, hvZ]
          ring
        have hlt : u-v < p := by omega
        simpa [ZMod.val_natCast_of_lt hlt] using congrArg ZMod.val H
      refine ⟨x + ((L-1 : ℕ) : ZMod p)*d, -d, neg_ne_zero.mpr hd, by omega, ?_⟩
      intro j hj
      have eh : x + ((L-1 : ℕ) : ZMod p)*d + (j : ZMod p)*(-d) =
          x + ((L-1-j : ℕ) : ZMod p)*d := by
        rw [Nat.cast_sub (by omega : j ≤ L-1)]
        ring
      rw [eh]
      exact h _ (by omega)
  obtain ⟨y,e,he,heB,hy⟩ := hdir
  have he₀ : 0 < e.val := Nat.pos_of_ne_zero (fun hz => he ((ZMod.val_eq_zero e).mp hz))
  have hval (j : ℕ) (hj : j < L) : (y + (j : ZMod p)*e).val = y.val + j*e.val := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hh : (y + (j : ZMod p)*e).val + e.val < p := by
        have := hS _ (hy j (by omega))
        omega
      have hnext : y + ((j+1 : ℕ) : ZMod p)*e =
          (((y + (j : ZMod p)*e).val + e.val : ℕ) : ZMod p) := by
        rw [Nat.cast_add ((y + (j : ZMod p)*e).val) e.val,
          ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        push_cast
        ring
      rw [hnext, ZMod.val_natCast_of_lt hh, ih (by omega)]
      ring
  let f (i : Fin L) := y.val + i.val * e.val
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right he₀ (Nat.add_left_cancel hij)
  refine ⟨Set.range f, ?_, y.val,e.val, ?_, ?_⟩
  · rintro _ ⟨j,rfl⟩
    rw [show f j = y.val + j.val * e.val from rfl, ← hval j j.isLt]
    exact hy j j.isLt
  · rw [ENat.card_congr (Equiv.ofInjective f hf).symm, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  · ext t
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.val, by exact_mod_cast i.isLt, by simp [f]⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,by exact_mod_cast hi⟩, by simp [f]⟩

end SumsetAP

open Filter Finset
open scoped BigOperators Topology

noncomputable section

namespace SumsetAP

private lemma eventual_pars (e : ℝ) (he : 0 < e) :
    ∃ c > 0, ∀ᶠ N : ℕ in atTop, ∃ m K L : ℕ, 0 < m ∧ 0 < K ∧ 2 ≤ L ∧
      K^m < N ∧ 2*Real.pi*(L : ℝ)/(K : ℝ) ≤ e ∧
      (L : ℝ) * (2*Real.exp (-(m : ℝ)*e^2/2)) < 4*e ∧
      Real.exp (c*Real.sqrt (Real.log (N : ℝ))) ≤ (L : ℝ) := by
  let C := ⌈8/e^2⌉₊
  let M := ⌈2*Real.pi/e⌉₊
  have hC : 8/e^2 ≤ (C : ℝ) := Nat.le_ceil _
  have hM : 2*Real.pi/e ≤ (M : ℝ) := Nat.le_ceil _
  have hCp : 0 < (C : ℝ) := (show 0 < 8/e^2 by positivity).trans_le hC
  have hMp : 0 < (M : ℝ) := (show 0 < 2*Real.pi/e by positivity).trans_le hM
  have hC' : 8 ≤ (C : ℝ)*e^2 := (div_le_iff₀ (by positivity : 0 < e^2)).mp hC
  have hM' : 2*Real.pi ≤ (M : ℝ)*e := (div_le_iff₀ he).mp hM
  let s := Real.sqrt (4*C : ℝ)
  have hs : 0 < s := by dsimp [s]; positivity
  have hs₂ : s^2 = 4*(C : ℝ) := Real.sq_sqrt (by positivity)
  let c := Real.log 2 / (2*s)
  have hc : 0 < c := div_pos (Real.log_pos (by norm_num)) (by positivity)
  refine ⟨c,hc,?_⟩
  have hX : Tendsto (fun N : ℕ => Real.sqrt (Real.log (N : ℝ)) / s) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).atTop_div_const hs
  filter_upwards [hX.eventually (eventually_ge_atTop (2 + max 2 (max (Real.log (M : ℝ)) (-Real.log e)))),
    eventually_ge_atTop (2 : ℕ)] with N hQ hN
  let q := Real.sqrt (Real.log (N : ℝ)) / s
  let n := ⌊q⌋₊
  let m := C*n
  let L := 2^n
  let K := M*L
  have hqLB : 2 + max 2 (max (Real.log (M : ℝ)) (-Real.log e)) ≤ q := hQ
  have hq₀ : 2 ≤ q := by linarith [le_max_left 2 (max (Real.log (M : ℝ)) (-Real.log e))]
  have hnU : (n : ℝ) ≤ q := Nat.floor_le (by linarith)
  have hnL : q < (n : ℝ)+1 := Nat.lt_floor_add_one q
  have hn2R : 2 ≤ (n : ℝ) := by
    linarith [le_max_left 2 (max (Real.log (M : ℝ)) (-Real.log e))]
  have hn2 : 2 ≤ n := by exact_mod_cast hn2R
  have hnM : Real.log (M : ℝ) ≤ (n : ℝ) := by
    linarith [le_max_left (Real.log (M : ℝ)) (-Real.log e),
      le_max_right 2 (max (Real.log (M : ℝ)) (-Real.log e))]
  have hne : -Real.log e ≤ (n : ℝ) := by
    linarith [le_max_right (Real.log (M : ℝ)) (-Real.log e),
      le_max_right 2 (max (Real.log (M : ℝ)) (-Real.log e))]
  have hm : 0 < m := Nat.mul_pos (Nat.cast_pos.mp hCp) (by omega)
  have hL : 2 ≤ L := by
    exact (show 2 ^ 1 ≤ 2^n from Nat.pow_le_pow_right (by decide) (by omega))
  have hLR : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hK : 0 < K := Nat.mul_pos (Nat.cast_pos.mp hMp) (by omega)
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  have hNR : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hlogL : Real.log (L : ℝ) = (n : ℝ)*Real.log 2 := by simp [L, Real.log_pow]
  have hlogK : Real.log (K : ℝ) = Real.log (M : ℝ)+(n : ℝ)*Real.log 2 := by
    rw [show (K : ℝ) = (M : ℝ)*(L : ℝ) by exact Nat.cast_mul _ _, Real.log_mul hMp.ne' hLR.ne', hlogL]
  have hmR : (m : ℝ) = (C : ℝ)*(n : ℝ) := Nat.cast_mul _ _
  have hlog2 : Real.log 2 ≤ 1 := by
    have H := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
    norm_num at H ⊢
    exact H
  have hn₀ : 0 ≤ (n : ℝ) := by positivity
  have hnS : (n : ℝ)*s ≤ Real.sqrt (Real.log (N : ℝ)) := (le_div_iff₀ hs).mp hnU
  have hnSq : (n : ℝ)^2 * (4*(C : ℝ)) ≤ Real.log (N : ℝ) := by
    rw [← hs₂, ← mul_pow, ← Real.sq_sqrt hlogN.le]
    gcongr
  refine ⟨m,K,L,hm,hK,hL, ?_, ?_, ?_, ?_⟩
  · have hlt : (K : ℝ)^m < (N : ℝ) := by
      have hKP : 0 < (K : ℝ)^m := pow_pos hKR _
      have hNP : 0 < (N : ℝ) := by linarith
      apply (Real.strictMonoOn_log.lt_iff_lt hKP hNP).mp
      rw [Real.log_pow, hmR, hlogK]
      have hk : Real.log (M : ℝ)+(n : ℝ)*Real.log 2 ≤ 2*(n : ℝ) := by
        have := mul_le_mul_of_nonneg_left hlog2 hn₀
        linarith
      have H := mul_le_mul_of_nonneg_left hk (mul_nonneg hCp.le hn₀)
      nlinarith
    exact_mod_cast hlt
  · rw [show (K : ℝ) = (M : ℝ)*(L : ℝ) by exact Nat.cast_mul _ _]
    apply (div_le_iff₀ (mul_pos hMp hLR)).mpr
    have H := mul_le_mul_of_nonneg_right hM' hLR.le
    nlinarith
  · have hmul := mul_le_mul_of_nonneg_right hC' hn₀
    have hlog : Real.log (L : ℝ) - (m : ℝ)*e^2/2 < Real.log e := by
      rw [hlogL, hmR]
      have := mul_le_mul_of_nonneg_left hlog2 hn₀
      nlinarith
    calc
      _ = 2*Real.exp (Real.log (L : ℝ) - (m : ℝ)*e^2/2) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hLR]
        rw [show -((m : ℝ)*e^2/2) = -(m : ℝ)*e^2/2 by ring]
        ring
      _ < 2*Real.exp (Real.log e) := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hlog) (by norm_num)
      _ = 2*e := by rw [Real.exp_log he]
      _ < _ := by linarith
  · rw [← Real.exp_log hLR, Real.exp_le_exp, hlogL]
    have hnq : q/2 ≤ (n : ℝ) := by linarith
    have hh := mul_le_mul_of_nonneg_right hnq
      (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    calc
      _ = q/2 * Real.log 2 := by dsimp [c, q]; ring
      _ ≤ _ := hh

end SumsetAP

namespace SumsetAP

private lemma circleNorm {p : ℕ} [NeZero p] (x : ZMod p) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

private lemma ap_exists_modular {p m K L : ℕ} [NeZero p] (A : Finset (ZMod p))
    (hm : 0 < m) (hK : 0 < K) (hpow : K^m < p) (e : ℝ) (he : 0 < e)
    (hmass : 8*e ≤ ((A.card : ℝ)/p)^2)
    (hincr : 2*Real.pi*L / (K : ℝ) ≤ e)
    (herror : (L : ℝ) * (2*Real.exp (-(m : ℝ)*e^2/2)) < 4*e) :
    ∃ x d : ZMod p, d ≠ 0 ∧ ∀ j : ℕ, j < L → 0 < convR A (x + (j : ZMod p)*d) := by
  classical
  let : MeasurableSpace (Option (ZMod p)) := ⊤
  let : MeasurableSingletonClass (Option (ZMod p)) := ⟨fun _ => trivial⟩
  let c := coeff A
  let W : ℝ := ∑ ξ : ZMod p, ‖c ξ‖
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (NeZero.pos p)
  have hW : W ≤ 1 := by
    rw [show W = (A.card : ℝ) / p from coeffMass A]
    apply (div_le_one hp).mpr
    exact_mod_cast (show A.card ≤ p by simpa [ZMod.card] using A.card_le_univ)
  let wgt : Option (ZMod p) → ℝ := Option.elim' (1-W) (fun ξ => ‖c ξ‖)
  have hwgt (a : Option (ZMod p)) : 0 ≤ wgt a := by cases a <;> simp [wgt, hW]
  have hsum : ∑ a, ENNReal.ofReal (wgt a) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hwgt i), Fintype.sum_option]
    simp [wgt, W]
  let P := PMF.ofFintype (fun a => ENNReal.ofReal (wgt a)) hsum
  let u : Option (ZMod p) → ℂ := Option.elim' 0 (fun ξ => c ξ / (‖c ξ‖ : ℂ))
  let freq (a : Option (ZMod p)) := a.getD 0
  let φ (a : Option (ZMod p)) (x : ZMod p) := (u a * ZMod.stdAddChar (freq a*x)).re
  have hu (a : Option (ZMod p)) : ‖u a‖ ≤ 1 := by
    cases a with
    | none => simp [u]
    | some ξ =>
      dsimp [u]
      by_cases h : c ξ = 0
      · simp [h]
      · simp [h]
  have hφ (a : Option (ZMod p)) (x : ZMod p) : φ a x ∈ Set.Icc (-1:ℝ) 1 := by
    apply abs_le.mp
    exact (Complex.abs_re_le_norm _).trans (by simpa [φ, norm_mul, circleNorm] using hu a)
  have hmean (x : ZMod p) : (∫ a, φ a x ∂P.toMeasure) = convR A x := by
    rw [PMF.integral_eq_sum, Fintype.sum_option, inversion, Complex.re_sum]
    have hcancel (ξ : ZMod p) : (‖c ξ‖ : ℂ) * u (some ξ) = c ξ := by
      dsimp [u]
      by_cases h : c ξ = 0
      · simp [h]
      · rw [mul_comm, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h))]
    have hproduct (ξ : ZMod p) : (P (some ξ)).toReal • φ (some ξ) x =
        (c ξ * ZMod.stdAddChar (ξ*x)).re := by
      rw [show (P (some ξ)).toReal = ‖c ξ‖ by simp [P,wgt]]
      simp only [smul_eq_mul, φ, freq, Option.getD_some]
      calc
        _ = ((‖c ξ‖ : ℂ) * (u (some ξ) * ZMod.stdAddChar (ξ*x))).re := by
          rw [Complex.re_ofReal_mul]
        _ = _ := by rw [← mul_assoc, hcancel]
    have hnone : (P none).toReal • φ none x = 0 := by simp [φ,u]
    simp only [hnone, zero_add, hproduct, c]
  obtain ⟨w, hw⟩ := sample_bad_bound P.toMeasure hm φ hφ e he
  simp only [hmean, ZMod.card] at hw
  let g := sampleAverage φ w
  let B := (univ : Finset (ZMod p)).filter (fun x => e < |g x - convR A x|)
  let H := (univ : Finset (ZMod p)).filter (fun x => 4*e ≤ convR A x)
  have hH : 4*e*(p : ℝ) ≤ H.card := by
    have hlow : 8*e*(p : ℝ) ≤ ∑ x : ZMod p, convR A x := by
      rw [convMean]
      exact (mul_le_mul_of_nonneg_right hmass hp.le).trans_eq (by field_simp)
    have hupp : (∑ x : ZMod p, convR A x) ≤ (H.card : ℝ) + 4*e*p := by
      calc
        _ ≤ ∑ x : ZMod p, ((if x ∈ H then (1 : ℝ) else 0) + 4*e) :=
          sum_le_sum fun x _ => by
            by_cases h : 4*e ≤ convR A x
            · have hmem : x ∈ H := mem_filter.mpr ⟨mem_univ x,h⟩
              simp only [hmem, if_true]
              linarith [(convR_range A x).2]
            · have hnmem : x ∉ H := by simpa [H] using h
              simpa [hnmem] using le_of_not_ge h
        _ = _ := by
          rw [sum_add_distrib, ← sum_filter]
          have hflt : (univ : Finset (ZMod p)).filter (· ∈ H) = H := by ext; simp
          simp [hflt, ZMod.card, mul_comm, mul_left_comm]
    linarith
  obtain ⟨d, hd, hfreq⟩ := commonIncrement hK hpow (fun i => freq (w i))
  let T := (range L).biUnion (fun j => B.map (Equiv.addRight (-((j : ZMod p)*d))).toEmbedding)
  have hT : T.card ≤ L*B.card := by
    unfold T
    exact card_biUnion_le.trans (by simp)
  have hs : (T.card : ℝ) < H.card := by
    calc
      _ ≤ (L:ℝ) * B.card := by exact_mod_cast hT
      _ ≤ (L:ℝ) * (2 * Real.exp (-(m:ℝ)*e^2/2) * p) := mul_le_mul_of_nonneg_left hw (by positivity)
      _ < 4*e*p := by rw [← mul_assoc]; exact mul_lt_mul_of_pos_right herror hp
      _ ≤ _ := hH
  have hns : ¬ H ⊆ T := fun h => (not_le_of_gt hs) (by exact_mod_cast (Finset.card_le_card h))
  obtain ⟨x, hxH, hxT⟩ := Finset.not_subset.mp hns
  have hnot (j : ℕ) (hj : j < L) : |g (x + (j : ZMod p)*d) - convR A (x + (j : ZMod p)*d)| ≤ e := by
    by_contra! h
    apply hxT
    refine mem_biUnion.mpr ⟨j, mem_range.mpr hj, mem_map.mpr ⟨_, mem_filter.mpr ⟨mem_univ _, h⟩, ?_⟩⟩
    simp [add_assoc]
  have hshift (j : ℕ) (hj : j < L) : |g (x + (j : ZMod p)*d) - g x| ≤ e := by
    have hsingle (i : Fin m) : |φ (w i) (x + (j : ZMod p)*d) - φ (w i) x| ≤ e := by
      have hχ := hfreq i j
      have hji : (j : ℝ) ≤ L := by exact_mod_cast hj.le
      have hterm : 2 * Real.pi * (j : ℝ) / (K : ℝ) ≤ e := by
        apply le_trans _ hincr
        gcongr
      simp only [φ, ← Complex.sub_re]
      apply (Complex.abs_re_le_norm _).trans ?_
      have hEq : u (w i) * ZMod.stdAddChar (freq (w i)*(x + (j : ZMod p)*d)) -
          u (w i) * ZMod.stdAddChar (freq (w i)*x) =
          (u (w i) * ZMod.stdAddChar (freq (w i)*x)) *
            (ZMod.stdAddChar (freq (w i)*((j : ZMod p)*d))-1) := by
        rw [mul_add, AddChar.map_add_eq_mul]
        ring
      rw [hEq, norm_mul, norm_mul, circleNorm, mul_one]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hu _)).trans (hχ.trans hterm)
    have hpM : 0 < (m : ℝ) := by exact_mod_cast hm
    simp only [g, sampleAverage, ← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hpM]
    apply (div_le_iff₀ hpM).mpr
    calc
      _ ≤ ∑ i : Fin m, |φ (w i) (x + (j : ZMod p)*d) - φ (w i) x| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin m, e := sum_le_sum (fun i _ => hsingle i)
      _ = _ := by simp [mul_comm]
  refine ⟨x,d,hd,?_⟩
  intro j hj
  have h0 := hnot 0 (by omega : 0 < L)
  have h1 := hnot j hj
  have h2 := hshift j hj
  simp only [Nat.cast_zero, zero_mul, add_zero] at h0
  have hH' := (mem_filter.mp hxH).2
  rw [abs_le] at h0 h1 h2
  linarith [h0.1, h1.2, h2.1]

end SumsetAP

open SumsetAP

theorem OMA.solution : type_of% @Green51.green_51.lower_ap := by
  classical
  intro α hα hα₁
  let e : ℝ := α^2/1024
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨c,hc,hev⟩ := eventual_pars e he
  refine ⟨c,hc,?_⟩
  filter_upwards [hev, eventually_ge_atTop (1:ℕ)] with N hpar hN
  obtain ⟨m,K,L,hm,hK,hL,hpow,hincr,herror,hexp⟩ := hpar
  obtain ⟨p,hp,hpn,hpN⟩ := Nat.exists_prime_lt_and_le_two_mul (4*N) (by omega)
  let : NeZero p := ⟨hp.ne_zero⟩
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpB : (p : ℝ) ≤ 8*(N : ℝ) := by exact_mod_cast (show p ≤ 8*N by omega)
  have hLsup (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 N)
      (hs : α * (N : ℝ) ≤ (S.card : ℝ)) :
      L ≤ sSup {l : ℕ | ∃ s ⊆ (S + S : Set ℕ), s.IsAPOfLength (l : ℕ∞)} := by
    have hu (a : ℕ) (ha : a ∈ S) : a ≤ N := (Finset.mem_Icc.mp (hS ha)).2
    have hU (a : ℕ) (ha : a ∈ S) : a < p := by have := hu a ha; omega
    let f (a : ℕ) : ZMod p := a
    let A := S.image f
    have hcard : A.card = S.card := by
      apply card_image_of_injOn
      intro a ha b hb h
      have hh := congrArg ZMod.val h
      change (a : ZMod p).val = (b : ZMod p).val at hh
      rwa [ZMod.val_natCast_of_lt (hU a ha), ZMod.val_natCast_of_lt (hU b hb)] at hh
    have hD : α/8 ≤ (A.card : ℝ)/(p : ℝ) := by
      apply (le_div_iff₀ hpR).mpr
      rw [hcard]
      have H := mul_le_mul_of_nonneg_left hpB (show 0 ≤ α/8 by positivity)
      linarith
    have hmass : 8*e ≤ ((A.card : ℝ)/p)^2 := by
      calc
        _ ≤ (α/8)^2 := by dsimp [e]; nlinarith
        _ ≤ _ := by gcongr
    obtain ⟨x,d,hd,hx⟩ := ap_exists_modular A hm hK (hpow.trans (by omega)) e he
      hmass hincr herror
    have hB (u : ℕ) (h : u ∈ (S+S : Set ℕ)) : u ≤ 2*N := by
      obtain ⟨a,ha,b,hb,rfl⟩ := h
      exact (Nat.add_le_add (hu a ha) (hu b hb)).trans_eq (by omega)
    have hpoints (j : ℕ) (hj : j < L) : (x + (j : ZMod p)*d).val ∈ (S+S : Set ℕ) := by
      obtain ⟨a,ha,b,hb,hxj⟩ := convR_pos_mem_add A (hx j hj)
      obtain ⟨a₀,ha₀,ha'⟩ := mem_image.mp ha
      obtain ⟨b₀,hb₀,hb'⟩ := mem_image.mp hb
      have hlt : a₀+b₀ < p := by have := hu a₀ ha₀; have := hu b₀ hb₀; omega
      rw [hxj, ← ha', ← hb', show f a₀ + f b₀ = ((a₀+b₀ : ℕ) : ZMod p) by simp [f],
        ZMod.val_natCast_of_lt hlt]
      exact Set.add_mem_add ha₀ hb₀
    obtain ⟨s,hsub,hAP⟩ := liftProgression hpn hL (S+S : Set ℕ) hB x d hd hpoints
    have hmem : L ∈ {l : ℕ | ∃ s ⊆ (S + S : Set ℕ), s.IsAPOfLength (l : ℕ∞)} :=
      ⟨s,hsub,hAP⟩
    apply le_csSup _ hmem
    refine ⟨2*N+1,?_⟩
    rintro l ⟨s',hs',a,d',hsAP⟩
    have hss : s' ⊆ (Finset.range (2*N+1) : Set ℕ) :=
      fun z hz => Finset.mem_range.mpr (by have := hB z (hs' hz); omega)
    have H := Set.encard_le_encard hss
    rw [← ENat.card_coe_set_eq, hsAP.1, Set.encard_coe_eq_coe_finsetCard, Finset.card_range] at H
    exact_mod_cast H
  rw [← Real.sqrt_eq_rpow]
  apply hexp.trans
  apply Nat.cast_le.mpr
  unfold Green51.guaranteedMaxAPLength
  apply le_csInf
  · refine ⟨_, Finset.Icc 1 N, subset_rfl, ?_, rfl⟩
    simp [Nat.card_Icc]
    exact mul_le_of_le_one_left (by positivity) hα₁
  · rintro _ ⟨S,hS,hs,rfl⟩
    exact hLsup S hS hs