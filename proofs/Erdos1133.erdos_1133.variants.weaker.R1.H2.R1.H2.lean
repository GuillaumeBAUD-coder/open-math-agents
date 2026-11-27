import OMAReductions.R_Erdos1133_erdos_1133_variants_weaker_R1_H2_R1
import Mathlib

-- Step Erdos1133.erdos_1133.variants.weaker.R1.H2.R1.H2: hypothesis H2 of reduction Erdos1133.erdos_1133.variants.weaker.R1.H2.R1
-- Credit: @ivillar
-- Bernstein's inequality in Lipschitz form for trigonometric polynomials
-- q(s) = A(cos s) + sin s * B(cos s) with deg A <= d, deg B < d.
-- Proof: shifting by any angle keeps this form, so q'(t) = O(1) for the odd part
-- sin s * O(cos s) of the shifted polynomial. Since |sqrt(1-x^2) O(x)| <= M, the polynomial
-- 1 - 2 (1 - x^2) O(x)^2 / M^2 is bounded by 1 on [-1, 1] and has degree <= 2d, so the Markov
-- endpoint inequality from Mathlib (Chebyshev extremal property) gives 4 O(1)^2 / M^2 <= 4 d^2.
-- The mean value theorem then gives the Lipschitz bound.

open Polynomial Real

namespace OMA.L5Bern

/-- `Rep d f`: `f φ = E (cos φ) + sin φ * O (cos φ)` with `deg E ≤ d` and `deg O < d`. -/
def Rep (d : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ E O : ℝ[X], E.natDegree ≤ d ∧ O.natDegree < d ∧
    ∀ φ, f φ = E.eval (cos φ) + sin φ * O.eval (cos φ)

lemma rep_const {d : ℕ} (hd : 1 ≤ d) (c : ℝ) : Rep d (fun _ => c) :=
  ⟨C c, 0, by rw [natDegree_C]; omega, by rw [natDegree_zero]; omega, fun φ => by simp⟩

lemma Rep.mono {d d' : ℕ} {f : ℝ → ℝ} (h : Rep d f) (hdd : d ≤ d') : Rep d' f := by
  obtain ⟨E, O, hE, hO, hf⟩ := h
  exact ⟨E, O, hE.trans hdd, lt_of_lt_of_le hO hdd, hf⟩

lemma Rep.add {d : ℕ} {f g : ℝ → ℝ} (hf : Rep d f) (hg : Rep d g) :
    Rep d (fun φ => f φ + g φ) := by
  obtain ⟨E1, O1, hE1, hO1, h1⟩ := hf
  obtain ⟨E2, O2, hE2, hO2, h2⟩ := hg
  refine ⟨E1 + E2, O1 + O2, (natDegree_add_le _ _).trans (max_le hE1 hE2),
    lt_of_le_of_lt (natDegree_add_le _ _) (max_lt hO1 hO2), fun φ => ?_⟩
  simp only [h1, h2, eval_add]
  ring

lemma Rep.smul {d : ℕ} {f : ℝ → ℝ} (hf : Rep d f) (c : ℝ) : Rep d (fun φ => c * f φ) := by
  obtain ⟨E, O, hE, hO, h⟩ := hf
  refine ⟨C c * E, C c * O, (natDegree_C_mul_le _ _).trans hE,
    lt_of_le_of_lt (natDegree_C_mul_le _ _) hO, fun φ => ?_⟩
  simp only [h, eval_mul, eval_C]
  ring

lemma natDegree_one_sub_X_sq_le : (1 - X ^ 2 : ℝ[X]).natDegree ≤ 2 :=
  (natDegree_sub_le _ _).trans (by simp)

lemma Rep.mul {d1 d2 : ℕ} {f g : ℝ → ℝ} (hf : Rep d1 f) (hg : Rep d2 g) :
    Rep (d1 + d2) (fun φ => f φ * g φ) := by
  obtain ⟨E1, O1, hE1, hO1, h1⟩ := hf
  obtain ⟨E2, O2, hE2, hO2, h2⟩ := hg
  refine ⟨E1 * E2 + (1 - X ^ 2) * (O1 * O2), E1 * O2 + O1 * E2, ?_, ?_, fun φ => ?_⟩
  · have h3 := natDegree_one_sub_X_sq_le
    have h4 := natDegree_mul_le (p := E1) (q := E2)
    have h5 := natDegree_mul_le (p := (1 - X ^ 2 : ℝ[X])) (q := O1 * O2)
    have h6 := natDegree_mul_le (p := O1) (q := O2)
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_) <;> omega
  · have h4 := natDegree_mul_le (p := E1) (q := O2)
    have h5 := natDegree_mul_le (p := O1) (q := E2)
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_) <;> omega
  · simp only [h1, h2, eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X]
    linear_combination (O1.eval (cos φ) * O2.eval (cos φ)) * sin_sq_add_cos_sq φ

lemma Rep.sum {d : ℕ} (hd : 1 ≤ d) {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (h : ∀ i ∈ s, Rep d (f i)) : Rep d (fun φ => ∑ i ∈ s, f i φ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rep_const hd 0
  | @insert a s ha ih =>
    have e : (fun φ => ∑ i ∈ insert a s, f i φ) = (fun φ => f a φ + ∑ i ∈ s, f i φ) := by
      funext φ
      rw [Finset.sum_insert ha]
    rw [e]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma Rep.pow {L : ℝ → ℝ} (hL : Rep 1 L) (i : ℕ) : Rep (i + 1) (fun φ => L φ ^ (i + 1)) := by
  induction i with
  | zero => simpa using hL
  | succ i ih =>
    have h := ih.mul hL
    have e : (fun φ => L φ ^ (i + 1 + 1)) = (fun φ => L φ ^ (i + 1) * L φ) := by
      funext φ
      ring
    rw [e]
    exact h

lemma Rep.comp {L : ℝ → ℝ} (hL : Rep 1 L) {d : ℕ} (hd : 1 ≤ d) (P : ℝ[X])
    (hP : P.natDegree ≤ d) : Rep d (fun φ => P.eval (L φ)) := by
  have e : (fun φ => P.eval (L φ)) =
      (fun φ => ∑ i ∈ Finset.range (d + 1), P.coeff i * L φ ^ i) := by
    funext φ
    exact eval_eq_sum_range' (by omega) _
  rw [e]
  apply Rep.sum hd
  intro i hi
  have hi' : i < d + 1 := Finset.mem_range.mp hi
  rcases i with _ | i
  · simpa using rep_const hd (P.coeff 0)
  · exact ((hL.pow i).mono (by omega)).smul _

lemma Rep.mul_comp {S L : ℝ → ℝ} (hS : Rep 1 S) (hL : Rep 1 L) {d : ℕ} (B : ℝ[X])
    (hB : B.natDegree < d) : Rep d (fun φ => S φ * B.eval (L φ)) := by
  have hd : 1 ≤ d := by omega
  have e : (fun φ => S φ * B.eval (L φ)) =
      (fun φ => ∑ i ∈ Finset.range d, B.coeff i * (S φ * L φ ^ i)) := by
    funext φ
    rw [eval_eq_sum_range' hB, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [e]
  apply Rep.sum hd
  intro i hi
  have hi' : i < d := Finset.mem_range.mp hi
  refine Rep.smul ?_ _
  rcases i with _ | i
  · simpa using hS.mono hd
  · exact (hS.mul (hL.pow i)).mono (by omega)

lemma shift_rep {d : ℕ} (A B : ℝ[X]) (hA : A.natDegree ≤ d) (hB : B.natDegree < d) (θ : ℝ) :
    Rep d (fun φ => A.eval (cos (θ + φ)) + sin (θ + φ) * B.eval (cos (θ + φ))) := by
  have hd : 1 ≤ d := by omega
  have hL : Rep 1 (fun φ => cos (θ + φ)) :=
    ⟨C (cos θ) * X, C (-sin θ), (natDegree_C_mul_le _ _).trans (by simp), by simp,
      fun φ => by simp only [eval_mul, eval_C, eval_X, cos_add]; ring⟩
  have hS : Rep 1 (fun φ => sin (θ + φ)) :=
    ⟨C (sin θ) * X, C (cos θ), (natDegree_C_mul_le _ _).trans (by simp), by simp,
      fun φ => by simp only [eval_mul, eval_C, eval_X, sin_add]; ring⟩
  exact (hL.comp hd A hA).add (hS.mul_comp hL B hB)

lemma hasDerivAt_rep (E O : ℝ[X]) :
    HasDerivAt (fun φ => E.eval (cos φ) + sin φ * O.eval (cos φ)) (O.eval 1) 0 := by
  have h1 : HasDerivAt (fun φ => E.eval (cos φ)) (E.derivative.eval (cos 0) * (-sin 0)) 0 :=
    (E.hasDerivAt (cos 0)).comp 0 (hasDerivAt_cos 0)
  have h2 : HasDerivAt (fun φ => O.eval (cos φ)) (O.derivative.eval (cos 0) * (-sin 0)) 0 :=
    (O.hasDerivAt (cos 0)).comp 0 (hasDerivAt_cos 0)
  have h4 := h1.add ((hasDerivAt_sin 0).mul h2)
  exact h4.congr_deriv (by simp)

/-- Schur-type endpoint bound, from the Markov endpoint inequality applied to
`1 - 2 (1 - x^2) O(x)^2 / M^2`. -/
lemma endpoint_bound {d : ℕ} (O : ℝ[X]) (hO : O.natDegree < d) (M : ℝ) (hM : 0 < M)
    (hsq : ∀ x ∈ Set.Icc (-1 : ℝ) 1, (1 - x ^ 2) * O.eval x ^ 2 ≤ M ^ 2) :
    |O.eval 1| ≤ d * M := by
  have hM2 : 0 < M ^ 2 := by positivity
  have hdeg : (1 - C (2 / M ^ 2) * ((1 - X ^ 2) * O ^ 2) : ℝ[X]).degree ≤ ((2 * d : ℕ) : ℕ) := by
    apply degree_le_of_natDegree_le
    have h1 := natDegree_one_sub_X_sq_le
    have h2 := natDegree_mul_le (p := (1 - X ^ 2 : ℝ[X])) (q := O ^ 2)
    have h3 : (O ^ 2).natDegree ≤ 2 * O.natDegree := natDegree_pow_le
    have h4 := natDegree_C_mul_le (2 / M ^ 2) ((1 - X ^ 2 : ℝ[X]) * O ^ 2)
    have h5 := natDegree_sub_le (1 : ℝ[X]) (C (2 / M ^ 2) * ((1 - X ^ 2 : ℝ[X]) * O ^ 2))
    rw [natDegree_one] at h5
    omega
  have hbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |(1 - C (2 / M ^ 2) * ((1 - X ^ 2) * O ^ 2) : ℝ[X]).eval x| ≤ 1 := by
    intro x hx
    have h := hsq x hx
    have hx2 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hnn : 0 ≤ (1 - x ^ 2) * O.eval x ^ 2 := mul_nonneg hx2 (sq_nonneg _)
    simp only [eval_sub, eval_one, eval_mul, eval_C, eval_pow, eval_X]
    have e : 2 / M ^ 2 * ((1 - x ^ 2) * O.eval x ^ 2) =
        2 * ((1 - x ^ 2) * O.eval x ^ 2 / M ^ 2) := by ring
    have h' : (1 - x ^ 2) * O.eval x ^ 2 / M ^ 2 ≤ 1 := (div_le_one hM2).mpr h
    have h'' : 0 ≤ (1 - x ^ 2) * O.eval x ^ 2 / M ^ 2 := div_nonneg hnn hM2.le
    rw [e, abs_le]
    constructor <;> linarith
  have key := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (k := 1) (x := 1) le_rfl hdeg hbnd
  have hT : (derivative^[1] (Polynomial.Chebyshev.T ℝ ((2 * d : ℕ) : ℤ))).eval 1 =
      (2 * (d : ℝ)) ^ 2 := by
    rw [Function.iterate_one, Polynomial.Chebyshev.derivative_T_eval_one]
    push_cast
    ring
  have hP : (derivative^[1] (1 - C (2 / M ^ 2) * ((1 - X ^ 2) * O ^ 2) : ℝ[X])).eval 1 =
      4 / M ^ 2 * O.eval 1 ^ 2 := by
    rw [Function.iterate_one]
    simp [derivative_mul]
    ring
  rw [hT, hP] at key
  have h1 : O.eval 1 ^ 2 ≤ ((d : ℝ) * M) ^ 2 := by
    have e : O.eval 1 ^ 2 = (4 / M ^ 2 * O.eval 1 ^ 2) * (M ^ 2 / 4) := by
      field_simp
    rw [e]
    calc (4 / M ^ 2 * O.eval 1 ^ 2) * (M ^ 2 / 4) ≤ (2 * (d : ℝ)) ^ 2 * (M ^ 2 / 4) :=
          mul_le_mul_of_nonneg_right key (by positivity)
      _ = ((d : ℝ) * M) ^ 2 := by ring
  have hdM : 0 ≤ (d : ℝ) * M := by positivity
  exact (sq_le_sq.mp h1).trans_eq (abs_of_nonneg hdM)

lemma deriv_bound {d : ℕ} (E O : ℝ[X]) (hO : O.natDegree < d)
    (M : ℝ) (hM : 0 < M) (hb : ∀ φ, |E.eval (cos φ) + sin φ * O.eval (cos φ)| ≤ M) :
    |O.eval 1| ≤ d * M := by
  apply endpoint_bound O hO M hM
  intro x hx
  have hc : cos (arccos x) = x := cos_arccos hx.1 hx.2
  have hs : sin (arccos x) ^ 2 = 1 - x ^ 2 := by
    have := sin_sq_add_cos_sq (arccos x)
    rw [hc] at this
    linarith
  have h1 := hb (arccos x)
  have h2 := hb (-arccos x)
  rw [cos_neg, sin_neg, neg_mul] at h2
  rw [hc] at h1 h2
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  have h3 : -M ≤ sin (arccos x) * O.eval x ∧ sin (arccos x) * O.eval x ≤ M := by
    constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]
  calc (1 - x ^ 2) * O.eval x ^ 2 = (sin (arccos x) * O.eval x) ^ 2 := by rw [mul_pow, hs]
    _ ≤ M ^ 2 := by nlinarith [h3.1, h3.2]

lemma bernstein (d : ℕ) (A B : ℝ[X]) (hA : A.natDegree ≤ d) (hB : B.natDegree < d)
    (M : ℝ) (hM : ∀ s, |A.eval (cos s) + sin s * B.eval (cos s)| ≤ M) (s u : ℝ) :
    |(A.eval (cos s) + sin s * B.eval (cos s)) - (A.eval (cos u) + sin u * B.eval (cos u))|
      ≤ d * M * |s - u| := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rcases hM0.eq_or_lt with h0 | hpos
  · have hs := hM s
    have hu := hM u
    rw [← h0] at hs hu
    rw [abs_nonpos_iff.mp hs, abs_nonpos_iff.mp hu, ← h0]
    simp
  have hder : ∀ θ : ℝ, ∃ c : ℝ,
      HasDerivAt (fun x => A.eval (cos x) + sin x * B.eval (cos x)) c θ ∧ |c| ≤ d * M := by
    intro θ
    obtain ⟨E, O, hE, hO, hEO⟩ := shift_rep A B hA hB θ
    have hEO' : ∀ φ, A.eval (cos (θ + φ)) + sin (θ + φ) * B.eval (cos (θ + φ)) =
        E.eval (cos φ) + sin φ * O.eval (cos φ) := hEO
    refine ⟨O.eval 1, ?_, ?_⟩
    · have hfun : (fun x => A.eval (cos x) + sin x * B.eval (cos x)) =
          (fun x => E.eval (cos (x - θ)) + sin (x - θ) * O.eval (cos (x - θ))) := by
        funext x
        have h := hEO' (x - θ)
        have e : θ + (x - θ) = x := by ring
        rw [e] at h
        exact h
      rw [hfun]
      have h0 := hasDerivAt_rep E O
      rw [← sub_self θ] at h0
      exact h0.comp_sub_const θ θ
    · apply deriv_bound E O hO M hpos
      intro φ
      have h := hM (θ + φ)
      rw [hEO' φ] at h
      exact h
  choose c hc using hder
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
    (f := fun x => A.eval (cos x) + sin x * B.eval (cos x)) (C := d * M)
    (fun x _ => (hc x).1.differentiableAt)
    (fun x _ => by rw [(hc x).1.deriv, Real.norm_eq_abs]; exact (hc x).2)
    convex_univ (Set.mem_univ u) (Set.mem_univ s)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  exact hmvt

end OMA.L5Bern

theorem OMA.solution : OMA.R_Erdos1133_erdos_1133_variants_weaker_R1_H2_R1.H2 := by
  intro d A B hA hB q M hM s u
  exact OMA.L5Bern.bernstein d A B hA hB M hM s u
