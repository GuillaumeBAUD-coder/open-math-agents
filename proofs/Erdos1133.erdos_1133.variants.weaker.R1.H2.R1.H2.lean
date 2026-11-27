import OMAReductions.R_Erdos1133_erdos_1133_variants_weaker_R1_H2_R1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.Calculus.MeanValue

namespace OMA.Bern

open Polynomial Polynomial.Chebyshev Real

private noncomputable def useq : Polynomial.Sequence ℝ where
  elems' n := U ℝ n
  degree_eq' n := degree_U_natCast ℝ n

private lemma expand_sequence (S : Polynomial.Sequence ℝ) (n : ℕ) (P : Polynomial ℝ)
    (h : P.natDegree < n) :
    ∃ c : ℕ → ℝ, ∑ i ∈ Finset.range n, c i • S i = P := by
  have hm : P ∈ degreeLT ℝ n := by
    rw [mem_degreeLT]
    exact P.degree_le_natDegree.trans_lt (by exact_mod_cast h)
  rw [← S.span_degreeLT (fun i _ => isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (S.ne_zero i))),
      show Set.Iio n = Finset.range n by simp,
      Submodule.mem_span_image_finset_iff_exists_fun'] at hm
  exact hm

private noncomputable def oddMode : ℕ → Polynomial ℝ
  | 0 => 0
  | k+1 => U ℝ k

private lemma oddMode_sin (i : ℕ) (t : ℝ) :
    sin t * (oddMode i).eval (cos t) = sin ((i : ℝ)*t) := by
  cases i with
  | zero => simp [oddMode]
  | succ j => simpa [oddMode, mul_comm (sin t), Nat.cast_succ] using U_real_cos t (j : ℤ)

private lemma oddMode_deg {d i : ℕ} (hd : 0 < d) (hi : i ≤ d) :
    (oddMode i).natDegree < d := by
  cases i with
  | zero => simpa [oddMode] using hd
  | succ i => simpa [oddMode] using hi

lemma shift_odd (d : ℕ) (A B : Polynomial ℝ)
    (hA : A.natDegree ≤ d) (hB : B.natDegree < d) (θ : ℝ) :
    let q := fun s : ℝ => A.eval (cos s) + sin s * B.eval (cos s)
    ∃ R : Polynomial ℝ, R.natDegree < d ∧
      ∀ t : ℝ, (q (θ+t) - q (θ-t))/2 = sin t * R.eval (cos t) := by
  dsimp only
  obtain ⟨a, ha⟩ := expand_sequence (chebyshevTsequence ℝ) (d+1) A (by omega)
  obtain ⟨b, hb⟩ := expand_sequence useq d B hB
  have ae (s : ℝ) : A.eval (cos s) =
      ∑ i ∈ Finset.range (d+1), a i * cos ((i:ℝ)*s) := by
    rw [← ha]
    simp [Polynomial.eval_finsetSum, Polynomial.eval_smul, chebyshevTsequence]
  have be (s : ℝ) : sin s * B.eval (cos s) =
      ∑ i ∈ Finset.range d, b i * sin (((i:ℝ)+1)*s) := by
    rw [← hb, Polynomial.eval_finsetSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change sin s * (b i • U ℝ (i:ℤ)).eval (cos s) = _
    rw [Polynomial.eval_smul, smul_eq_mul, mul_left_comm, mul_comm (sin s), U_real_cos]
    norm_cast
  let R₁ := ∑ i ∈ Finset.range (d+1), C (-a i * sin ((i:ℝ)*θ)) * oddMode i
  let R₂ := ∑ i ∈ Finset.range d, C (b i * cos (((i:ℝ)+1)*θ)) * U ℝ (i:ℤ)
  have hd : 0 < d := by omega
  have h1 : R₁.natDegree ≤ d-1 := by
    apply natDegree_sum_le_of_forall_le
    intro i hi
    refine (natDegree_C_mul_le _ _).trans ?_
    have h := oddMode_deg hd (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    omega
  have h2 : R₂.natDegree ≤ d-1 := by
    apply natDegree_sum_le_of_forall_le
    intro i hi
    refine (natDegree_C_mul_le _ _).trans ?_
    have h := Finset.mem_range.mp hi
    simp only [natDegree_U_natCast]
    omega
  refine ⟨R₁+R₂, (natDegree_add_le _ _).trans_lt (by omega), ?_⟩
  intro t
  have first : A.eval (cos (θ+t)) - A.eval (cos (θ-t)) = 2 * sin t * R₁.eval (cos t) := by
    simp only [ae, R₁, Polynomial.eval_finsetSum, eval_mul, eval_C,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_add, mul_sub, cos_add, cos_sub, ← oddMode_sin i t]
    ring
  have second : sin (θ+t) * B.eval (cos (θ+t)) - sin (θ-t) * B.eval (cos (θ-t)) =
      2 * sin t * R₂.eval (cos t) := by
    simp only [be, R₂, Polynomial.eval_finsetSum, eval_mul, eval_C,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hui : sin t * (U ℝ (i:ℤ)).eval (cos t) = sin (((i:ℝ)+1)*t) := by
      simpa [mul_comm (sin t)] using U_real_cos t (i : ℤ)
    rw [mul_add, mul_sub, sin_add, sin_sub, ← hui]
    ring
  rw [eval_add]
  linarith

end OMA.Bern

namespace OMA.Bern

lemma deriv_eq_of_shift_odd {q : ℝ → ℝ} {θ : ℝ} (R : Polynomial ℝ)
    (hd : DifferentiableAt ℝ q θ)
    (hs : ∀ t : ℝ, (q (θ+t)-q (θ-t))/2 = Real.sin t * R.eval (Real.cos t)) :
    deriv q θ = R.eval 1 := by
  have hp : HasDerivAt (fun t : ℝ => θ + t) 1 0 := by
    simpa [Pi.add_def, Pi.sub_def] using (hasDerivAt_const (0 : ℝ) θ).add (hasDerivAt_id' (0 : ℝ))
  have hm : HasDerivAt (fun t : ℝ => θ - t) (-1) 0 := by
    simpa [Pi.add_def, Pi.sub_def] using (hasDerivAt_const (0 : ℝ) θ).sub (hasDerivAt_id' (0 : ℝ))
  have hpq : HasDerivAt (fun t : ℝ => q (θ+t)) (deriv q θ) 0 := by
    have hq : HasDerivAt q (deriv q θ) (θ + 0) := by simpa using hd.hasDerivAt
    simpa [Function.comp_def] using hq.comp 0 hp
  have hmq : HasDerivAt (fun t : ℝ => q (θ-t)) (-(deriv q θ)) 0 := by
    have hq : HasDerivAt q (deriv q θ) (θ - 0) := by simpa using hd.hasDerivAt
    simpa [Function.comp_def] using hq.comp 0 hm
  have hl := (hpq.sub hmq).div_const 2
  have hr := (Real.hasDerivAt_sin (0 : ℝ)).mul
    ((R.hasDerivAt (Real.cos 0)).comp 0 (Real.hasDerivAt_cos (0 : ℝ)))
  have hl' : HasDerivAt (fun t : ℝ => Real.sin t * R.eval (Real.cos t))
      ((deriv q θ - -deriv q θ) / 2) 0 := by
    have eqf := funext hs
    rw [← eqf]
    simpa [Pi.sub_def] using hl
  have he := hl'.unique hr
  simpa [sub_neg_eq_add, ← two_mul, Function.comp_def] using he

end OMA.Bern

open Polynomial Real Set

namespace OMA.AngularBernstein

/-- The weighted endpoint bound obtained by applying the endpoint Markov inequality to
the even square of an odd trigonometric polynomial. -/
theorem weighted_endpoint (V : Polynomial ℝ) (d : ℕ) (hd : V.natDegree < d)
    (M : ℝ) (hM : 0 < M)
    (hb : ∀ θ : ℝ, |sin θ * V.eval (cos θ)| ≤ M) :
    |V.eval 1| ≤ (d : ℝ) * M := by
  let G : Polynomial ℝ := (1-X^2)*V^2
  let F : Polynomial ℝ := 1 - C (2/M^2)*G
  have hGd : G.natDegree ≤ 2*d := by
    have h1 : (1 - X^2 : Polynomial ℝ).natDegree ≤ 2 := by
      exact (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_X_pow_le 2))
    have h2 : (V^2).natDegree ≤ 2*V.natDegree := natDegree_pow_le
    exact natDegree_mul_le.trans ((Nat.add_le_add h1 h2).trans (by omega))
  have hFd : F.degree ≤ ↑(2*d) := by
    apply degree_le_of_natDegree_le
    exact (natDegree_sub_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans hGd))
  have hscale : 0 ≤ 2/M^2 := by positivity
  have hcancel : 2/M^2*M^2=2 := by field_simp
  have hFb (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) : |F.eval x| ≤ 1 := by
    have ht := Real.cos_arccos hx.1 hx.2
    have hb' := hb (arccos x)
    rw [ht] at hb'
    have hsin := Real.sin_sq_add_cos_sq (arccos x)
    rw [ht] at hsin
    have hsq : (1-x^2)*(V.eval x)^2 ≤ M^2 := by
      rw [show 1-x^2 = sin (arccos x)^2 by linarith, ← mul_pow]
      nlinarith [sq_abs (sin (arccos x) * V.eval x), abs_nonneg (sin (arccos x)*V.eval x)]
    have hpos : 0 ≤ (1-x^2)*(V.eval x)^2 := by
      rw [show 1-x^2 = sin (arccos x)^2 by linarith]
      positivity
    simp [F,G]
    apply abs_le.mpr
    constructor
    · linarith [mul_le_mul_of_nonneg_left hsq hscale]
    · nlinarith [mul_nonneg hscale hpos]
  have hext := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (k := 1) (x := (1 : ℝ)) le_rfl hFd hFb
  have hF : F.derivative.eval 1 ≤ ((2*d : ℕ) : ℝ)^2 := by
    simpa [Chebyshev.derivative_T_eval_one] using hext
  have hcalc : F.derivative.eval 1 = (2/M^2)*(2 * V.eval 1^2) := by
    simp [F,G,derivative_sub,derivative_mul,derivative_pow]
  rw [hcalc] at hF
  push_cast at hF
  have hF' : 4 * (V.eval 1)^2 ≤ ((2:ℝ)*d)^2 * M^2 := by
    calc
      _ = ((2/M^2)*(2 * V.eval 1^2))*M^2 := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hF (sq_nonneg _)
  have hdM : 0 ≤ (d:ℝ)*M := by positivity
  nlinarith [sq_abs (V.eval 1), abs_nonneg (V.eval 1)]

end OMA.AngularBernstein

open Polynomial Real Set

namespace OMA.Bern

/-- The odd part of every translate is bounded by the same global bound.
Applying the endpoint inequality to these translates bounds the derivative
everywhere, and the mean-value inequality then controls all secants. -/
theorem secant_of_shift_endpoint (q : ℝ → ℝ) (d : ℕ)
    (hq : Differentiable ℝ q)
    (shift : ∀ θ : ℝ, ∃ R : Polynomial ℝ, R.natDegree < d ∧
      ∀ t : ℝ, (q (θ+t) - q (θ-t))/2 = sin t * R.eval (cos t))
    (derivShift : ∀ (θ : ℝ) (R : Polynomial ℝ),
      (∀ t : ℝ, (q (θ+t) - q (θ-t))/2 = sin t * R.eval (cos t)) →
      deriv q θ = R.eval 1)
    (endpoint : ∀ (R : Polynomial ℝ), R.natDegree < d →
      ∀ M : ℝ, 0 < M → (∀ t, |sin t * R.eval (cos t)| ≤ M) →
      |R.eval 1| ≤ (d : ℝ)*M)
    (M : ℝ) (hM : ∀ t, |q t| ≤ M) (s u : ℝ) :
    |q s - q u| ≤ (d : ℝ)*M*|s-u| := by
  by_cases hpos : 0 < M
  · have bound (θ : ℝ) : |deriv q θ| ≤ (d : ℝ)*M := by
      obtain ⟨R, hR, hodd⟩ := shift θ
      rw [derivShift θ R hodd]
      apply endpoint R hR M hpos
      intro t
      rw [← hodd t, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
      linarith [abs_sub (q (θ+t)) (q (θ-t)), hM (θ+t), hM (θ-t)]
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x (_ : x ∈ (univ : Set ℝ)) => hq x)
      (fun x _ => by rw [Real.norm_eq_abs]; exact bound x)
      (convex_univ : Convex ℝ (univ : Set ℝ))
      (mem_univ u) (mem_univ s)
    simpa only [Real.norm_eq_abs] using h
  · have hzero : M = 0 := le_antisymm (le_of_not_gt hpos) ((abs_nonneg _).trans (hM 0))
    subst M
    have h (x : ℝ) : q x = 0 := abs_nonpos_iff.mp (hM x)
    simp [h]

theorem trig_differentiable (A B : Polynomial ℝ) :
    Differentiable ℝ (fun s : ℝ => A.eval (cos s) + sin s * B.eval (cos s)) :=
  (A.differentiable.comp differentiable_cos).add
    (differentiable_sin.mul (B.differentiable.comp differentiable_cos))

end OMA.Bern

/-- The degree-sharp Bernstein secant inequality for two-sided trigonometric polynomials. -/
theorem OMA.solution : OMA.R_Erdos1133_erdos_1133_variants_weaker_R1_H2_R1.H2 := by
  intro d A B hA hB
  let q := fun s : ℝ => A.eval (Real.cos s) + Real.sin s * B.eval (Real.cos s)
  have hd : Differentiable ℝ q := OMA.Bern.trig_differentiable A B
  change ∀ M : ℝ, (∀ t : ℝ, |q t| ≤ M) → ∀ s u : ℝ, |q s - q u| ≤ (d : ℝ)*M*|s-u|
  intro M hM s u
  exact OMA.Bern.secant_of_shift_endpoint q d hd
    (OMA.Bern.shift_odd d A B hA hB)
    (fun θ R h => OMA.Bern.deriv_eq_of_shift_odd R (hd θ) h)
    (fun R hR M hpos => OMA.AngularBernstein.weighted_endpoint R d hR M hpos)
    M hM s u
