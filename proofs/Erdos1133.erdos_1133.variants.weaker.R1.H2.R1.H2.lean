import OMAReductions.R_Erdos1133_erdos_1133_variants_weaker_R1_H2_R1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

/-! Bernstein's trigonometric inequality by applying the endpoint Markov inequality
to the square of the odd part of a translated trigonometric polynomial. -/

namespace TrigBernstein

open Real Polynomial

def Rep (d : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ U V : ℝ[X], U.natDegree ≤ d ∧ (V = 0 ∨ V.natDegree < d) ∧
    ∀ s, f s = U.eval (cos s) + sin s * V.eval (cos s)

theorem timesLinear {d : ℕ} {f : ℝ → ℝ} (hf : Rep d f) (a b c : ℝ) :
    Rep (d+1) (fun s => (a*cos s + b*sin s)*f s + c) := by
  obtain ⟨U,V,hu,hv,he⟩ := hf
  refine ⟨C a * X * U + C b * (1-X^2) * V + C c, C b * U + C a * X * V, ?_, Or.inr ?_, ?_⟩
  · rcases hv with rfl|hv
    · simp only [mul_zero,add_zero]; compute_degree; omega
    · compute_degree; omega
  · rcases hv with rfl|hv
    · simp only [mul_zero,add_zero]; exact Nat.lt_succ_of_le ((natDegree_C_mul_le _ _).trans hu)
    · apply Nat.lt_succ_of_le; compute_degree; omega
  · intro s
    simp only [he,eval_add,eval_mul,eval_sub,eval_pow,eval_one,eval_X,eval_C]
    linear_combination b * V.eval (cos s) * Real.sin_sq_add_cos_sq s

theorem polyRep (a b : ℝ) (d : ℕ) (P : ℝ[X]) (hp : P.natDegree ≤ d) :
    Rep d (fun s => P.eval (a*cos s+b*sin s)) := by
  induction d generalizing P with
  | zero =>
    exact ⟨P,0,hp,Or.inl rfl, fun s => by rw [eq_C_of_natDegree_le_zero hp]; simp⟩
  | succ d ih =>
    have hr := ih P.divX (by rw [natDegree_divX_eq_natDegree_tsub_one]; omega)
    have h := timesLinear hr a b (P.coeff 0)
    convert h using 1
    funext s
    have hP := congrArg (fun Q : ℝ[X] => Q.eval (a*cos s+b*sin s)) (divX_mul_X_add P)
    simpa only [eval_add, eval_mul, eval_X, eval_C, mul_comm] using hP.symm

theorem translated {d : ℕ} (A B : ℝ[X]) (ha : A.natDegree ≤ d) (hb : B.natDegree < d)
    (t : ℝ) : Rep d (fun s => A.eval (cos (t+s)) + sin (t+s) * B.eval (cos (t+s))) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  obtain ⟨U,V,hu,hv,he⟩ := polyRep (cos t) (-sin t) (k+1) A ha
  have h := timesLinear (polyRep (cos t) (-sin t) k B (by omega)) (sin t) (cos t) 0
  obtain ⟨W,Z,hw,hz,hh⟩ := h
  refine ⟨U+W,V+Z,(natDegree_add_le _ _).trans (max_le hu hw),Or.inr ?_, ?_⟩
  · apply lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · rcases hv with rfl|h <;> simp_all
    · rcases hz with rfl|h <;> simp_all
  · intro s
    simp only [Real.cos_add,Real.sin_add,eval_add]
    simp only [neg_mul,← sub_eq_add_neg,add_zero] at he hh
    rw [he s, hh s]
    ring

theorem endpoint {d : ℕ} {V : ℝ[X]} (hv : V.natDegree < d) {M : ℝ} (hp : 0 < M)
    (hb : ∀ s, |sin s * V.eval (cos s)| ≤ M) : |V.eval 1| ≤ d*M := by
  let P : ℝ[X] := 1 - C (2/M^2) * (1-X^2) * V^2
  have hdeg : P.natDegree ≤ 2*d := by
    unfold P
    compute_degree; omega
  have hbnd (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) : |P.eval x| ≤ 1 := by
    have h := hb (arccos x)
    rw [cos_arccos hx.1 hx.2] at h
    have hid := sin_sq_add_cos_sq (arccos x)
    rw [cos_arccos hx.1 hx.2] at hid
    have hb2 := sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
    rw [mul_pow,show sin (arccos x)^2 = 1-x^2 by linarith] at hb2
    have hxx : 0 ≤ 1-x^2 := by nlinarith [sq_nonneg (sin (arccos x))]
    simp only [P,eval_sub,eval_mul,eval_pow,eval_one,eval_X,eval_C]
    apply abs_le.mpr
    constructor
    · field_simp [hp.ne']; nlinarith
    · nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2/M^2) hxx) (sq_nonneg (V.eval x))]
  have he : P.derivative.eval 1 ≤ ((2*d:ℕ):ℝ)^2 := by
    simpa [Chebyshev.derivative_T_eval_one] using
      (Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one (k := 1) (x := 1)
        le_rfl (degree_le_of_natDegree_le hdeg) hbnd)
  have hder : P.derivative.eval 1 = 4/M^2*(V.eval 1)^2 := by
    simp [P,derivative_mul,derivative_pow]; ring_nf; simp
  rw [hder] at he
  push_cast at he
  have he' : (V.eval 1)^2 ≤ (d*M)^2 := by
    field_simp [hp.ne'] at he
    nlinarith
  exact abs_le.mpr (abs_le_of_sq_le_sq' he' (by positivity))

end TrigBernstein

open Real Polynomial TrigBernstein

theorem OMA.solution : OMA.R_Erdos1133_erdos_1133_variants_weaker_R1_H2_R1.H2 := by
  intro d A B hA hB
  dsimp only
  intro M hb s u
  let q := fun z : ℝ => A.eval (cos z) + sin z * B.eval (cos z)
  have hd (z : ℝ) : DifferentiableAt ℝ q z := by dsimp [q]; fun_prop
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  rcases hM.eq_or_lt with rfl|hM
  · have hq (z : ℝ) : q z = 0 := abs_nonpos_iff.mp (hb z)
    change |q s-q u| ≤ _
    simp [hq]
  have bound (z : ℝ) : |deriv q z| ≤ d*M := by
    obtain ⟨U,V,_,hv,he⟩ := translated A B hA hB z
    dsimp only at he
    have oddBound (v : ℝ) : |sin v * V.eval (cos v)| ≤ M := by
      have hplus := abs_le.mp (hb (z+v))
      have hminus := abs_le.mp (hb (z+ -v))
      rw [he v] at hplus
      rw [he (-v),sin_neg,cos_neg] at hminus
      apply abs_le.mpr; constructor <;> linarith
    have hrep : (fun v => q (z+v)) = (fun v => U.eval (cos v) + sin v * V.eval (cos v)) := funext he
    have hz0 : HasDerivAt q (deriv q z) (z + id 0) := by simpa using (hd z).hasDerivAt
    have hl := hz0.comp 0 ((hasDerivAt_const (0:ℝ) z).fun_add (hasDerivAt_id 0))
    have hr := (((U.hasDerivAt (cos 0)).comp 0 (hasDerivAt_cos 0))).fun_add
      ((hasDerivAt_sin 0).fun_mul ((V.hasDerivAt (cos 0)).comp 0 (hasDerivAt_cos 0)))
    have hl' : HasDerivAt (fun v => q (z+v)) (deriv q z) 0 := by
      simpa [Function.comp_def] using hl
    have hr' : HasDerivAt (fun v => U.eval (cos v) + sin v * V.eval (cos v)) (V.eval 1) 0 := by
      simpa [Function.comp_def] using hr
    rw [hrep] at hl'
    rw [hl'.unique hr']
    rcases hv with rfl|hv
    · simp; positivity
    · exact endpoint hv hM oddBound
  simpa [Real.norm_eq_abs,q] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (f := q) (fun z _ => hd z) (fun z _ => by simpa [Real.norm_eq_abs] using bound z)
      (Set.mem_univ u) (Set.mem_univ s)

