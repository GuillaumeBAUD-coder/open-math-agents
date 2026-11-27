import OMAReductions.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1
import Mathlib
import Mathlib.Algebra.Polynomial.Homogenize

/-! Binary nonnegative homogeneous real polynomials are sums of two squares.
Formalization by Hanan Beer with Codex assistance. This proves the binary-form
case of the classical Hilbert polynomial sum-of-squares theorem. The argument
removes real double-root or positive quadratic factors, uses the two-squares
product identity with degree bounds, and homogenizes.
Target reduction by @marcusbuffett, PR4945. All algebraic and analytic infrastructure
comes from Mathlib; no external theorem proof is copied. -/


/- Nonnegative real univariate polynomials as two squares, with degree bounds.
Formalization by Hanan Beer. The proof removes a positive quadratic factor, or
an even real-root factor, and uses the two-squares product identity. -/

namespace BinarySOS
open Polynomial Filter
open scoped Topology

lemma nonneg_quotient (p q : ℝ[X]) (a b : ℝ)
    (h : p = ((X-C a)^2 + (C b)^2)*q) (hp : ∀ x : ℝ, 0 ≤ p.eval x) :
    ∀ x : ℝ, 0 ≤ q.eval x := by
  have hne (x : ℝ) (hx : x ≠ a) : 0 ≤ q.eval x := by
    have hpos : 0 < (x-a)^2 + b^2 := add_pos_of_pos_of_nonneg
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hx)) (sq_nonneg b)
    have he := hp x
    rw [h] at he
    simp only [eval_mul, eval_add, eval_pow, eval_sub, eval_X, eval_C] at he
    exact nonneg_of_mul_nonneg_right he hpos
  intro x
  by_cases hx : x = a
  · subst x
    apply ge_of_tendsto (q.continuous.continuousAt.tendsto.mono_left
      (show 𝓝[≠] a ≤ 𝓝 a from inf_le_left))
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hne y (by simpa using hy)
  · exact hne x hx

lemma real_double_root (p : ℝ[X]) (a : ℝ) (hp : ∀ x : ℝ, 0 ≤ p.eval x)
    (ha : p.eval a = 0) : (X-C a)^2 ∣ p := by
  have hmin : IsLocalMin (fun x : ℝ => p.eval x) a :=
    Filter.Eventually.of_forall (fun x => by simpa [ha] using hp x)
  have hd : p.derivative.eval a = 0 := (p.hasDerivAt a).deriv.symm.trans hmin.deriv_eq_zero
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr ha
  have hqa : q.eval a = 0 := by
    rw [hq] at hd
    simpa using hd
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr hqa
  refine ⟨r, ?_⟩
  rw [hq, hr]
  ring

lemma quadratic_degree (a b : ℝ) : ((X-C a)^2 + (C b)^2 : ℝ[X]).natDegree = 2 := by
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · simp

lemma factor_nonnegative (p : ℝ[X]) (hp0 : p ≠ 0) (hpdeg : 0 < p.natDegree)
    (hp : ∀ x : ℝ, 0 ≤ p.eval x) :
    ∃ a b : ℝ, ∃ q : ℝ[X], p = ((X-C a)^2 + (C b)^2)*q ∧
      (∀ x : ℝ, 0 ≤ q.eval x) ∧ q.natDegree + 2 = p.natDegree := by
  have hdeg : p.degree ≠ 0 := by
    intro h
    have hz : p.natDegree = 0 := natDegree_eq_of_degree_eq_some h
    omega
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ p hdeg
  have hdvd : ((X-C z.re)^2 + (C z.im)^2 : ℝ[X]) ∣ p := by
    by_cases hi : z.im = 0
    · have hr : p.eval z.re = 0 := by
        have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
        have hz' := hz
        rw [he] at hz'
        change p.aeval (algebraMap ℝ ℂ z.re) = 0 at hz'
        rw [aeval_algebraMap_apply_eq_algebraMap_eval] at hz'
        exact (algebraMap ℝ ℂ).injective (by simpa using hz')
      simpa [hi] using real_double_root p z.re hp hr
    · have h := p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz hi
      have he : (X ^ 2 - C (2*z.re)*X + C (‖z‖^2) : ℝ[X]) =
          (X-C z.re)^2 + (C z.im)^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [map_add, map_mul, map_ofNat]
        ring
      rwa [he] at h
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨z.re, z.im, q, hq, nonneg_quotient p q _ _ hq hp, ?_⟩
  have hqn : q ≠ 0 := by intro he; simp [he] at hq; exact hp0 hq
  have hfn : ((X-C z.re)^2 + (C z.im)^2 : ℝ[X]) ≠ 0 := by
    intro he
    have := quadratic_degree z.re z.im
    simp [he] at this
  rw [hq, natDegree_mul hfn hqn, quadratic_degree]
  omega

end BinarySOS


/- Two-square degree induction for nonnegative real polynomials.
Formalization by Hanan Beer with Codex assistance. The step uses the classical
identity expressing a product of two sums of two squares as two squares. -/

namespace BinarySOSInduction
open Polynomial

lemma two_squares_of_quadratic_factor
    (factor : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < p.natDegree →
      (∀ x : ℝ, 0 ≤ p.eval x) → ∃ a b : ℝ, ∃ q : Polynomial ℝ,
      p = ((X - C a)^2 + (C b)^2) * q ∧
        (∀ x : ℝ, 0 ≤ q.eval x) ∧ q.natDegree + 2 = p.natDegree) :
    ∀ (d : ℕ) (p : Polynomial ℝ), p.natDegree ≤ 2*d →
      (∀ x : ℝ, 0 ≤ p.eval x) → ∃ u v : Polynomial ℝ,
      p = u^2 + v^2 ∧ u.natDegree ≤ d ∧ v.natDegree ≤ d := by
  intro d
  induction d with
  | zero =>
      intro p hp hpos
      have hdeg : p.natDegree = 0 := by omega
      have he : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
      have hc : 0 ≤ p.coeff 0 := by
          have hh := hpos 0
          rw [he, eval_C] at hh
          exact hh
      refine ⟨C (Real.sqrt (p.coeff 0)), 0, ?_, by simp, by simp⟩
      simp only [zero_pow (by decide : 2 ≠ 0), add_zero, ← map_pow]
      rw [Real.sq_sqrt hc]
      exact he
  | succ d ih =>
      intro p hp hpos
      by_cases hz : p.natDegree = 0
      · have he : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hz
        have hc : 0 ≤ p.coeff 0 := by
          have hh := hpos 0
          rw [he, eval_C] at hh
          exact hh
        refine ⟨C (Real.sqrt (p.coeff 0)), 0, ?_, by simp, by simp⟩
        simp only [zero_pow (by decide : 2 ≠ 0), add_zero, ← map_pow]
        rw [Real.sq_sqrt hc]
        exact he
      · have hp0 : p ≠ 0 := by intro he; simp [he] at hz
        obtain ⟨a, b, q, hpq, hqpos, hqdeg⟩ := factor p hp0 (by omega) hpos
        obtain ⟨u, v, huv, hu, hv⟩ := ih q (by omega) hqpos
        refine ⟨(X - C a)*u - C b*v, (X - C a)*v + C b*u, ?_, ?_, ?_⟩
        · rw [hpq, huv]
          ring
        · apply (natDegree_sub_le _ _).trans
          apply max_le
          · apply natDegree_mul_le.trans
            simp only [natDegree_X_sub_C]
            omega
          · apply natDegree_mul_le.trans
            simp only [natDegree_C, zero_add]
            omega
        · apply (natDegree_add_le _ _).trans
          apply max_le
          · apply natDegree_mul_le.trans
            simp only [natDegree_X_sub_C]
            omega
          · apply natDegree_mul_le.trans
            simp only [natDegree_C, zero_add]
            omega

end BinarySOSInduction



/- Homogenization bridge for the binary case of Hilbert's polynomial theorem.
New formalization by Hanan Beer with Codex assistance, using Mathlib's homogenization API. -/

namespace BinaryHomogeneous
open Finset MvPolynomial

lemma degree_dehomogenize {n : ℕ} {p : MvPolynomial (Fin 2) ℝ}
    (hp : p.IsHomogeneous n) :
    (MvPolynomial.aeval ![Polynomial.X, 1] p : Polynomial ℝ).natDegree ≤ n := by
  classical
  rw [p.as_sum]
  simp only [MvPolynomial.aeval_sum, MvPolynomial.aeval_monomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply Polynomial.natDegree_mul_le.trans
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one, ← Polynomial.C_eq_algebraMap,
    Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
  have h := hp.degree_eq_sum_deg_support hm
  rw [h]
  by_cases hm0 : m 0 = 0
  · simp [hm0]
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finsupp.mem_support_iff.mpr hm0)

lemma binary_of_univariate
    (univariate : ∀ (d : ℕ) (p : Polynomial ℝ), p.natDegree ≤ 2*d →
      (∀ x : ℝ, 0 ≤ p.eval x) → ∃ u v : Polynomial ℝ,
      p = u^2 + v^2 ∧ u.natDegree ≤ d ∧ v.natDegree ≤ d) :
    ∀ d : ℕ, 0 < d → ∀ p : MvPolynomial (Fin 2) ℝ, p.IsHomogeneous (2*d) →
      (∀ x, 0 ≤ MvPolynomial.eval x p) →
      ∃ (m : ℕ) (g : Fin m → MvPolynomial (Fin 2) ℝ), p = ∑ i, (g i)^2 := by
  intro d _ p hp hpos
  let q : Polynomial ℝ := MvPolynomial.aeval ![Polynomial.X, 1] p
  have hq : q.natDegree ≤ 2*d := degree_dehomogenize hp
  have hqpos (x : ℝ) : 0 ≤ q.eval x := by
    change 0 ≤ Polynomial.eval x (MvPolynomial.aeval ![Polynomial.X, 1] p)
    have he : Polynomial.eval x (MvPolynomial.aeval ![Polynomial.X, 1] p) =
        MvPolynomial.eval ![x, 1] p := by
      rw [MvPolynomial.aeval_def, MvPolynomial.polynomial_eval_eval₂]
      congr 1
      · ext r; simp
      · ext i; fin_cases i <;> simp
    rw [he]
    exact hpos ![x, 1]
  obtain ⟨u, v, huv, hu, hv⟩ := univariate d q hq hqpos
  have hpq : q.homogenize (2*d) = p :=
    Polynomial.homogenize_eq_of_isHomogeneous hp rfl
  refine ⟨2, ![u.homogenize d, v.homogenize d], ?_⟩
  rw [← hpq, huv, Polynomial.homogenize_add, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp only [pow_two, two_mul, Polynomial.homogenize_mul u u hu hu,
    Polynomial.homogenize_mul v v hv hv]

end BinaryHomogeneous


theorem OMA.solution : OMA.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1.H1 := by
  exact BinaryHomogeneous.binary_of_univariate
    (BinarySOSInduction.two_squares_of_quadratic_factor BinarySOS.factor_nonnegative)
