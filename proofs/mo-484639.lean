import OMAStatements.S_mo_484639

/-!
# Proof of `mo-484639`: Closed form of a summation over an integer lattice

Constructive elementary proof of MathOverflow Question #484639 (`OMA.S_mo_484639.main`):
For every `n ≥ 1` and nonsingular `V : Matrix (Fin n) (Fin n) ℤ`, letting `d = |det V| > 0`
and `H⊥ = {r : Fin n → Fin d | ∀ c, (d : ℤ) ∣ ∑ j, V j c * r j}`, we prove `|H⊥| = d` and
`S V = π^n / (sinh π ^ n * d) * P (cosh (π / d))` with the explicit polynomial
`P = ∑ r ∈ H⊥, ∏ j, Polynomial.Chebyshev.T ℤ ((d : ℤ) - 2 * r j) ∈ ℤ[X]`.
-/

namespace MO484639Proof

open scoped BigOperators Classical
open Polynomial Complex Real MeasureTheory

/-! ### Section 1: Chebyshev hyperbolic identity (Lemma L4) -/

lemma chebyshev_T_eval_cosh (m : ℤ) (x : ℝ) :
    ((Polynomial.Chebyshev.T ℤ m).map (Int.castRingHom ℝ)).eval (Real.cosh x) =
      Real.cosh ((m : ℝ) * x) := by
  induction m using Polynomial.Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n h1 h0 =>
    rw [Polynomial.Chebyshev.T_add_two]
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_X,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    rw [h1, h0]
    have hadd := Real.cosh_add (((n : ℝ) + 1) * x) x
    have hsub := Real.cosh_sub (((n : ℝ) + 1) * x) x
    have hcomb : Real.cosh ((((n : ℝ) + 1) * x) + x) + Real.cosh ((((n : ℝ) + 1) * x) - x) =
        2 * Real.cosh (((n : ℝ) + 1) * x) * Real.cosh x := by
      linarith
    have harg1 : (((n : ℝ) + 1) * x) + x = ((↑(n : ℤ) + 2 : ℤ) : ℝ) * x := by push_cast; ring
    have harg2 : (((n : ℝ) + 1) * x) - x = ((n : ℤ) : ℝ) * x := by push_cast; ring
    have harg3 : ((↑(n : ℤ) + 1 : ℤ) : ℝ) * x = ((n : ℝ) + 1) * x := by push_cast; ring
    rw [harg1, harg2] at hcomb
    rw [harg3]
    linarith
  | neg m hm =>
    rw [Polynomial.Chebyshev.T_neg, hm]
    push_cast
    rw [neg_mul, Real.cosh_neg]

/-! ### Section 2: 1D Fourier series of `cosh (π (1 - 2x))` (Lemma L3) -/

lemma summable_one_div_one_add_sq_nat :
    Summable (fun m : ℕ => (1 : ℝ) / (1 + (m : ℝ) ^ 2)) := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective (add_left_injective 1))
  simp only [Function.comp_apply]
  gcongr
  linarith

lemma summable_one_div_one_add_sq_int :
    Summable (fun m : ℤ => (1 : ℝ) / (1 + (m : ℝ) ^ 2)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩
  · simpa using summable_one_div_one_add_sq_nat
  · simpa [neg_sq] using summable_one_div_one_add_sq_nat

lemma intervalIntegral_cexp_mul (a : ℂ) (ha : a ≠ 0) :
    ∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (a * (t : ℂ)) = (Complex.exp a - 1) / a := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) (1 : ℝ),
      HasDerivAt (fun s : ℝ => Complex.exp (a * (s : ℂ)) / a) (Complex.exp (a * (t : ℂ))) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => a * (s : ℂ)) a t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul a
    have h2 : HasDerivAt (fun s : ℝ => Complex.exp (a * (s : ℂ))) (Complex.exp (a * (t : ℂ)) * a) t :=
      h1.cexp
    simpa [mul_div_cancel_right₀ _ ha] using h2.div_const a
  have hint : IntervalIntegrable (fun t : ℝ => Complex.exp (a * (t : ℂ))) volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [sub_div]

lemma cexp_two_pi_I_mul_int (m : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)) = 1 := by
  have h : 2 * Real.pi * Complex.I * (m : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

lemma tsum_exp_div_one_add_sq (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∑' m : ℤ, Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) / (1 + (m : ℂ) ^ 2) =
      ((Real.pi / Real.sinh Real.pi * Real.cosh (Real.pi * (1 - 2 * x)) : ℝ) : ℂ) := by
  have : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  let g0 : ℝ → ℂ := fun t => ((Real.cosh (Real.pi * (1 - 2 * t)) : ℝ) : ℂ)
  have hg0_eq : g0 0 = g0 1 := by
    simp only [g0]
    congr 1
    have : Real.pi * (1 - 2 * (1 : ℝ)) = -Real.pi := by ring
    rw [this, Real.cosh_neg]
    ring_nf
  have hg0_cont : ContinuousOn g0 (Set.Icc 0 1) := by
    have : Continuous g0 := by fun_prop
    exact this.continuousOn
  let g : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨AddCircle.liftIoc (1 : ℝ) 0 g0, AddCircle.liftIoc_zero_continuous hg0_eq hg0_cont⟩
  have hcoeff : ∀ m : ℤ, fourierCoeff g m =
      ((Real.sinh Real.pi / (Real.pi * (1 + (m : ℝ) ^ 2)) : ℝ) : ℂ) := by
    intro m
    rw [fourierCoeff_eq_intervalIntegral g m 0]
    simp only [div_one, one_smul, zero_add]
    have hcongr : ∫ t in (0 : ℝ)..(1 : ℝ), @fourier (1 : ℝ) (-m) (t : AddCircle (1 : ℝ)) • g t =
        ∫ t in (0 : ℝ)..(1 : ℝ),
          (Complex.exp (Real.pi : ℂ) / 2) *
            Complex.exp ((-2 * (Real.pi : ℂ) * (1 + Complex.I * (m : ℂ))) * (t : ℂ)) +
          (Complex.exp (-(Real.pi : ℂ)) / 2) *
            Complex.exp ((2 * (Real.pi : ℂ) * (1 - Complex.I * (m : ℂ))) * (t : ℂ)) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
      have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
      change @fourier (1 : ℝ) (-m) (t : AddCircle (1 : ℝ)) • AddCircle.liftIoc (1 : ℝ) 0 g0 ↑t = _
      rw [AddCircle.liftIoc_zero_coe_apply htIoc]
      simp only [smul_eq_mul, fourier_coe_apply, Complex.ofReal_one, div_one, g0]
      rw [Real.cosh_eq]
      push_cast
      have e1 : Complex.exp (2 * ↑Real.pi * Complex.I * -↑m * ↑t) *
          Complex.exp (↑Real.pi * (1 - 2 * ↑t)) =
          Complex.exp ↑Real.pi *
            Complex.exp (-2 * ↑Real.pi * (1 + Complex.I * ↑m) * ↑t) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1; ring
      have e2 : Complex.exp (2 * ↑Real.pi * Complex.I * -↑m * ↑t) *
          Complex.exp (-(↑Real.pi * (1 - 2 * ↑t))) =
          Complex.exp (-↑Real.pi) *
            Complex.exp (2 * ↑Real.pi * (1 - Complex.I * ↑m) * ↑t) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1; ring
      calc Complex.exp (2 * ↑Real.pi * Complex.I * -↑m * ↑t) *
            ((Complex.exp (↑Real.pi * (1 - 2 * ↑t)) +
              Complex.exp (-(↑Real.pi * (1 - 2 * ↑t)))) / 2)
          = (Complex.exp (2 * ↑Real.pi * Complex.I * -↑m * ↑t) *
              Complex.exp (↑Real.pi * (1 - 2 * ↑t))) / 2 +
            (Complex.exp (2 * ↑Real.pi * Complex.I * -↑m * ↑t) *
              Complex.exp (-(↑Real.pi * (1 - 2 * ↑t)))) / 2 := by ring
        _ = (Complex.exp ↑Real.pi / 2) *
              Complex.exp (-2 * ↑Real.pi * (1 + Complex.I * ↑m) * ↑t) +
            (Complex.exp (-↑Real.pi) / 2) *
              Complex.exp (2 * ↑Real.pi * (1 - Complex.I * ↑m) * ↑t) := by
            rw [e1, e2]; ring
    rw [hcongr]
    have ha1 : (-2 * (Real.pi : ℂ) * (1 + Complex.I * (m : ℂ))) ≠ 0 := by
      intro h
      have hre := congr_arg Complex.re h
      simp [Real.pi_ne_zero] at hre
    have ha2 : (2 * (Real.pi : ℂ) * (1 - Complex.I * (m : ℂ))) ≠ 0 := by
      intro h
      have hre := congr_arg Complex.re h
      simp [Real.pi_ne_zero] at hre
    have hi1 : IntervalIntegrable
        (fun t : ℝ => (Complex.exp (Real.pi : ℂ) / 2) *
          Complex.exp ((-2 * (Real.pi : ℂ) * (1 + Complex.I * (m : ℂ))) * (t : ℂ)))
        volume 0 1 := Continuous.intervalIntegrable (by fun_prop) 0 1
    have hi2 : IntervalIntegrable
        (fun t : ℝ => (Complex.exp (-(Real.pi : ℂ)) / 2) *
          Complex.exp ((2 * (Real.pi : ℂ) * (1 - Complex.I * (m : ℂ))) * (t : ℂ)))
        volume 0 1 := Continuous.intervalIntegrable (by fun_prop) 0 1
    rw [intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral_cexp_mul _ ha1, intervalIntegral_cexp_mul _ ha2]
    have hexp1 : Complex.exp (-2 * (Real.pi : ℂ) * (1 + Complex.I * (m : ℂ))) =
        Complex.exp (-2 * (Real.pi : ℂ)) := by
      have hsplit : -2 * (Real.pi : ℂ) * (1 + Complex.I * (m : ℂ)) =
          -2 * (Real.pi : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * ((-m : ℤ) : ℂ) := by
        push_cast; ring
      rw [hsplit, Complex.exp_add, cexp_two_pi_I_mul_int (-m), mul_one]
    have hexp2 : Complex.exp (2 * (Real.pi : ℂ) * (1 - Complex.I * (m : ℂ))) =
        Complex.exp (2 * (Real.pi : ℂ)) := by
      have hsplit : 2 * (Real.pi : ℂ) * (1 - Complex.I * (m : ℂ)) =
          2 * (Real.pi : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * ((-m : ℤ) : ℂ) := by
        push_cast; ring
      rw [hsplit, Complex.exp_add, cexp_two_pi_I_mul_int (-m), mul_one]
    rw [hexp1, hexp2]
    have hprod1 : Complex.exp (Real.pi : ℂ) * Complex.exp (-2 * (Real.pi : ℂ)) =
        Complex.exp (-(Real.pi : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    have hprod2 : Complex.exp (-(Real.pi : ℂ)) * Complex.exp (2 * (Real.pi : ℂ)) =
        Complex.exp (Real.pi : ℂ) := by
      rw [← Complex.exp_add]; congr 1; ring
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hd1 : (1 : ℂ) + Complex.I * (m : ℂ) ≠ 0 := by
      intro h; have := congr_arg Complex.re h; simp at this
    have hd2 : (1 : ℂ) - Complex.I * (m : ℂ) ≠ 0 := by
      intro h; have := congr_arg Complex.re h; simp at this
    have hd3 : (1 : ℂ) + (m : ℂ) ^ 2 ≠ 0 := by
      intro h
      have h1 : ((1 + (m : ℝ) ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h
      have hpos : (0 : ℝ) < 1 + (m : ℝ) ^ 2 := by positivity
      exact hpos.ne' (Complex.ofReal_eq_zero.mp h1)
    have ht1 : Complex.exp (Real.pi : ℂ) / 2 *
        ((Complex.exp (-2 * (Real.pi : ℂ)) - 1) /
          (-2 * (Real.pi : ℂ) * (1 + Complex.I * (m : ℂ)))) =
        (Complex.exp (Real.pi : ℂ) - Complex.exp (-(Real.pi : ℂ))) /
          (4 * (Real.pi : ℂ) * (1 + Complex.I * (m : ℂ))) := by
      rw [div_mul_div_comm, mul_sub, mul_one, hprod1]
      field_simp [hpi, hd1]
      ring
    have ht2 : Complex.exp (-(Real.pi : ℂ)) / 2 *
        ((Complex.exp (2 * (Real.pi : ℂ)) - 1) /
          (2 * (Real.pi : ℂ) * (1 - Complex.I * (m : ℂ)))) =
        (Complex.exp (Real.pi : ℂ) - Complex.exp (-(Real.pi : ℂ))) /
          (4 * (Real.pi : ℂ) * (1 - Complex.I * (m : ℂ))) := by
      rw [div_mul_div_comm, mul_sub, mul_one, hprod2]
      field_simp [hpi, hd2]
      ring
    rw [ht1, ht2]
    have hprodI : (1 + Complex.I * (m : ℂ)) * (1 - Complex.I * (m : ℂ)) = 1 + (m : ℂ) ^ 2 := by
      linear_combination -(m : ℂ) ^ 2 * Complex.I_sq
    have hsum_inv : (1 : ℂ) / (1 + Complex.I * (m : ℂ)) + 1 / (1 - Complex.I * (m : ℂ)) =
        2 / (1 + (m : ℂ) ^ 2) := by
      rw [div_add_div _ _ hd1 hd2, hprodI]
      congr 1; ring
    have hlhs : (Complex.exp (Real.pi : ℂ) - Complex.exp (-(Real.pi : ℂ))) /
          (4 * (Real.pi : ℂ) * (1 + Complex.I * (m : ℂ))) +
        (Complex.exp (Real.pi : ℂ) - Complex.exp (-(Real.pi : ℂ))) /
          (4 * (Real.pi : ℂ) * (1 - Complex.I * (m : ℂ))) =
        ((Complex.exp (Real.pi : ℂ) - Complex.exp (-(Real.pi : ℂ))) / (4 * (Real.pi : ℂ))) *
          ((1 : ℂ) / (1 + Complex.I * (m : ℂ)) + 1 / (1 - Complex.I * (m : ℂ))) := by
      have h := mul_add
        ((Complex.exp (Real.pi : ℂ) - Complex.exp (-(Real.pi : ℂ))) / (4 * (Real.pi : ℂ)))
        ((1 : ℂ) / (1 + Complex.I * (m : ℂ)))
        ((1 : ℂ) / (1 - Complex.I * (m : ℂ)))
      rw [div_mul_div_comm, div_mul_div_comm, mul_one] at h
      exact h.symm
    rw [hlhs, hsum_inv, Real.sinh_eq]
    push_cast
    field_simp [hpi, hd3]
    ring
  have hsumm : Summable (fourierCoeff g) := by
    have hfun : fourierCoeff g = fun m : ℤ =>
        ((Real.sinh Real.pi / (Real.pi * (1 + (m : ℝ) ^ 2)) : ℝ) : ℂ) := funext hcoeff
    rw [hfun]
    have hreal : Summable (fun m : ℤ => Real.sinh Real.pi / (Real.pi * (1 + (m : ℝ) ^ 2))) := by
      have : (fun m : ℤ => Real.sinh Real.pi / (Real.pi * (1 + (m : ℝ) ^ 2))) =
          fun m : ℤ => (Real.sinh Real.pi / Real.pi) * (1 / (1 + (m : ℝ) ^ 2)) := by
        ext m
        rw [div_mul_div_comm, mul_one]
      rw [this]
      exact summable_one_div_one_add_sq_int.mul_left _
    exact Complex.summable_ofReal.mpr hreal
  have hpt := has_pointwise_sum_fourier_series_of_summable hsumm (x : AddCircle (1 : ℝ))
  have hgx : g (x : AddCircle (1 : ℝ)) = g0 x := by
    by_cases hx0' : x = 0
    · subst hx0'
      have h01 : ((0 : ℝ) : AddCircle (1 : ℝ)) = ((1 : ℝ) : AddCircle (1 : ℝ)) := by
        rw [QuotientAddGroup.eq]
        simp [AddSubgroup.mem_zmultiples]
      change AddCircle.liftIoc (1 : ℝ) 0 g0 ↑(0 : ℝ) = g0 0
      rw [h01, AddCircle.liftIoc_zero_coe_apply (by constructor <;> linarith)]
      exact hg0_eq.symm
    · have hxIoc : x ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hx0 (Ne.symm hx0'), hx1⟩
      change AddCircle.liftIoc (1 : ℝ) 0 g0 ↑x = g0 x
      exact AddCircle.liftIoc_zero_coe_apply hxIoc
  rw [hgx] at hpt
  have htsum := hpt.tsum_eq
  simp only [hcoeff, smul_eq_mul, fourier_coe_apply, Complex.ofReal_one, div_one] at htsum
  have hfactor : ∀ m : ℤ,
      ((Real.sinh Real.pi / (Real.pi * (1 + (m : ℝ) ^ 2)) : ℝ) : ℂ) *
        Complex.exp (2 * ↑Real.pi * Complex.I * ↑m * ↑x) =
      ((Real.sinh Real.pi / Real.pi : ℝ) : ℂ) *
        (Complex.exp (2 * ↑Real.pi * Complex.I * ↑m * ↑x) / (1 + (m : ℂ) ^ 2)) := by
    intro m
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_div, div_mul_eq_mul_div,
      mul_div_mul_comm]
    congr 2
    push_cast
    rfl
  simp_rw [hfactor, tsum_mul_left] at htsum
  have hres := congr_arg (fun z : ℂ => ((Real.pi / Real.sinh Real.pi : ℝ) : ℂ) * z) htsum
  simp only [g0] at hres
  have hcancel : ((Real.pi / Real.sinh Real.pi : ℝ) : ℂ) *
      ((Real.sinh Real.pi / Real.pi : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    have hs : Real.sinh Real.pi ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr Real.pi_pos)
    have h1 : Real.pi / Real.sinh Real.pi * (Real.sinh Real.pi / Real.pi) = 1 := by
      field_simp [hs, Real.pi_ne_zero]
    rw [h1, Complex.ofReal_one]
  rw [← mul_assoc, hcancel, one_mul] at hres
  simpa [Complex.ofReal_mul] using hres

/-! ### Section 3: Hermite upper-triangularization over `ℤ` (Lemma L1) -/

def ColEquiv {n : ℕ} (V M : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ U : (Matrix (Fin n) (Fin n) ℤ)ˣ, V * U.1 = M

lemma colEquiv_refl {n : ℕ} (V : Matrix (Fin n) (Fin n) ℤ) : ColEquiv V V :=
  ⟨1, by simp⟩

lemma colEquiv_trans {n : ℕ} {A B C : Matrix (Fin n) (Fin n) ℤ}
    (h1 : ColEquiv A B) (h2 : ColEquiv B C) : ColEquiv A C := by
  rcases h1 with ⟨U1, rfl⟩
  rcases h2 with ⟨U2, rfl⟩
  exact ⟨U1 * U2, by simp [Matrix.mul_assoc]⟩

lemma colEquiv_det_natAbs {n : ℕ} {V M : Matrix (Fin n) (Fin n) ℤ} (h : ColEquiv V M) :
    M.det.natAbs = V.det.natAbs := by
  rcases h with ⟨U, rfl⟩
  rw [Matrix.det_mul, Int.natAbs_mul]
  have hu : IsUnit U.1.det := (Matrix.isUnit_iff_isUnit_det U.1).mp U.isUnit
  have hu1 : U.1.det.natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hu
  rw [hu1, mul_one]

lemma colEquiv_range_mulVec {n : ℕ} {V M : Matrix (Fin n) (Fin n) ℤ} (h : ColEquiv V M) :
    Set.range M.mulVec = Set.range V.mulVec := by
  rcases h with ⟨U, rfl⟩
  ext k
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨U.1.mulVec a, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨a, rfl⟩
    refine ⟨U.inv.mulVec a, ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, U.val_inv, Matrix.mul_one]

def swapColMat {n : ℕ} (a b : Fin n) : (Matrix (Fin n) (Fin n) ℤ)ˣ where
  val := Matrix.of fun i j => if i = Equiv.swap a b j then (1 : ℤ) else 0
  inv := Matrix.of fun i j => if i = Equiv.swap a b j then (1 : ℤ) else 0
  val_inv := by
    ext i j
    simp [Matrix.mul_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  inv_val := by
    ext i j
    simp [Matrix.mul_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]

lemma mul_swapColMat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) (i j : Fin n) :
    (M * (swapColMat a b).1) i j = M i (Equiv.swap a b j) := by
  simp [Matrix.mul_apply, swapColMat]

def negColMat {n : ℕ} (a : Fin n) : (Matrix (Fin n) (Fin n) ℤ)ˣ where
  val := Matrix.diagonal (fun j => if j = a then (-1 : ℤ) else 1)
  inv := Matrix.diagonal (fun j => if j = a then (-1 : ℤ) else 1)
  val_inv := by
    ext i j
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  inv_val := by
    ext i j
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp

lemma mul_negColMat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (a : Fin n) (i j : Fin n) :
    (M * (negColMat a).1) i j = if j = a then -M i j else M i j := by
  simp only [negColMat, Matrix.mul_diagonal]
  split_ifs <;> ring

def addColMat {n : ℕ} (src dst : Fin n) (hne : src ≠ dst) (q : ℤ) :
    (Matrix (Fin n) (Fin n) ℤ)ˣ where
  val := 1 + Matrix.single src dst q
  inv := 1 + Matrix.single src dst (-q)
  val_inv := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have hsplit : ∀ k : Fin n,
        ((if i = k then (1 : ℤ) else 0) + (if src = i ∧ dst = k then q else 0)) *
        ((if k = j then (1 : ℤ) else 0) + (if src = k ∧ dst = j then -q else 0)) =
        (if i = k then 1 else 0) * (if k = j then 1 else 0) +
        (if i = k then 1 else 0) * (if src = k ∧ dst = j then -q else 0) +
        (if src = i ∧ dst = k then q else 0) * (if k = j then 1 else 0) := by
      intro k
      have hz : (if src = i ∧ dst = k then q else 0) * (if src = k ∧ dst = j then -q else 0) = 0 := by
        by_cases hkd : dst = k
        · subst hkd; simp [hne]
        · simp [hkd]
      linear_combination hz
    simp_rw [hsplit, Finset.sum_add_distrib]
    have s1 : (∑ k : Fin n, (if i = k then (1 : ℤ) else 0) * (if k = j then 1 else 0)) =
        if i = j then 1 else 0 := by
      simp
    have s2 : (∑ k : Fin n, (if i = k then (1 : ℤ) else 0) * (if src = k ∧ dst = j then -q else 0)) =
        if src = i ∧ dst = j then -q else 0 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki; simp [Ne.symm hki]
      · intro h; exact absurd (Finset.mem_univ i) h
    have s3 : (∑ k : Fin n, (if src = i ∧ dst = k then q else 0) * (if k = j then 1 else 0)) =
        if src = i ∧ dst = j then q else 0 := by
      rw [Finset.sum_eq_single dst]
      · by_cases h1 : src = i <;> by_cases h2 : dst = j <;> simp [h1, h2]
      · intro k _ hkd; simp [Ne.symm hkd]
      · intro h; exact absurd (Finset.mem_univ dst) h
    rw [s1, s2, s3]
    split_ifs <;> ring
  inv_val := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have hsplit : ∀ k : Fin n,
        ((if i = k then (1 : ℤ) else 0) + (if src = i ∧ dst = k then -q else 0)) *
        ((if k = j then (1 : ℤ) else 0) + (if src = k ∧ dst = j then q else 0)) =
        (if i = k then 1 else 0) * (if k = j then 1 else 0) +
        (if i = k then 1 else 0) * (if src = k ∧ dst = j then q else 0) +
        (if src = i ∧ dst = k then -q else 0) * (if k = j then 1 else 0) := by
      intro k
      have hz : (if src = i ∧ dst = k then -q else 0) * (if src = k ∧ dst = j then q else 0) = 0 := by
        by_cases hkd : dst = k
        · subst hkd; simp [hne]
        · simp [hkd]
      linear_combination hz
    simp_rw [hsplit, Finset.sum_add_distrib]
    have s1 : (∑ k : Fin n, (if i = k then (1 : ℤ) else 0) * (if k = j then 1 else 0)) =
        if i = j then 1 else 0 := by
      simp
    have s2 : (∑ k : Fin n, (if i = k then (1 : ℤ) else 0) * (if src = k ∧ dst = j then q else 0)) =
        if src = i ∧ dst = j then q else 0 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki; simp [Ne.symm hki]
      · intro h; exact absurd (Finset.mem_univ i) h
    have s3 : (∑ k : Fin n, (if src = i ∧ dst = k then -q else 0) * (if k = j then 1 else 0)) =
        if src = i ∧ dst = j then -q else 0 := by
      rw [Finset.sum_eq_single dst]
      · by_cases h1 : src = i <;> by_cases h2 : dst = j <;> simp [h1, h2]
      · intro k _ hkd; simp [Ne.symm hkd]
      · intro h; exact absurd (Finset.mem_univ dst) h
    rw [s1, s2, s3]
    split_ifs <;> ring

lemma mul_addColMat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (src dst : Fin n) (hne : src ≠ dst)
    (q : ℤ) (i j : Fin n) :
    (M * (addColMat src dst hne q).1) i j = if j = dst then M i j + M i src * q else M i j := by
  change (M * (1 + Matrix.single src dst q)) i j = _
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  simp only [Matrix.single_apply]
  by_cases hj : j = dst
  · subst hj
    simp
  · have hj' : dst ≠ j := Ne.symm hj
    simp [hj, hj']

lemma exists_nonzero_prefix_of_det_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hdet : M.det ≠ 0)
    (r : Fin n) (hbelow : ∀ i j : Fin n, r < i → j < i → M i j = 0) :
    ∃ j : Fin n, j ≤ r ∧ M r j ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hdet
  rw [Matrix.det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  suffices hzero : ∃ j : Fin n, M (σ j) j = 0 by
    rcases hzero with ⟨j, hj⟩
    have hp : (∏ k : Fin n, M (σ k) k) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [hp, smul_zero]
  by_contra hnz
  push Not at hnz
  have hmaps : ∀ j : Fin n, j ≤ r → σ j < r := by
    intro j hj
    by_contra hge
    push Not at hge
    rcases eq_or_lt_of_le hge with heq | hlt
    · exact hnz j (heq ▸ hall j hj)
    · exact hnz j (hbelow (σ j) j hlt (lt_of_le_of_lt hj hlt))
  let S : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j ≤ r)
  let T : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i < r)
  have hsub : S.image σ ⊆ T := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmaps j (Finset.mem_filter.mp hj).2⟩
  have hcard1 : (S.image σ).card = S.card :=
    Finset.card_image_of_injective S σ.injective
  have hcard_le : S.card ≤ T.card := by
    rw [← hcard1]; exact Finset.card_le_card hsub
  have hlt_card : T.card < S.card := by
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩, by simp [T]⟩
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_lt (Finset.mem_filter.mp hx).2⟩
  omega

lemma eliminate_row {n : ℕ} (r : Fin n) :
    ∀ (s : ℕ) (M : Matrix (Fin n) (Fin n) ℤ),
      M.det ≠ 0 →
      (∀ i j : Fin n, r < i → j < i → M i j = 0) →
      (∀ i : Fin n, r < i → 0 < M i i) →
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ r), (M r j).natAbs) = s →
      ∃ M' : Matrix (Fin n) (Fin n) ℤ,
        ColEquiv M M' ∧
        (∀ i j : Fin n, r ≤ i → j < i → M' i j = 0) ∧
        (∀ i : Fin n, r ≤ i → 0 < M' i i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro M hdet hbelow hpos hs
    let nz : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j ≤ r ∧ M r j ≠ 0)
    have hnz_ne : nz.Nonempty := by
      rcases exists_nonzero_prefix_of_det_ne_zero M hdet r hbelow with ⟨j, hj1, hj2⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj1, hj2⟩⟩
    by_cases hcard : nz.card = 1
    · rcases Finset.card_eq_one.mp hcard with ⟨j0, hj0_eq⟩
      have hj0_mem : j0 ∈ nz := by rw [hj0_eq]; exact Finset.mem_singleton_self j0
      have hj0_le : j0 ≤ r := (Finset.mem_filter.mp hj0_mem).2.1
      have hj0_ne : M r j0 ≠ 0 := (Finset.mem_filter.mp hj0_mem).2.2
      let M1 := M * (swapColMat j0 r).1
      have hce1 : ColEquiv M M1 := ⟨swapColMat j0 r, rfl⟩
      have hM1_below : ∀ i j : Fin n, r < i → j < i → M1 i j = 0 := by
        intro i j hi hj
        dsimp only [M1]
        rw [mul_swapColMat]
        have hsw : Equiv.swap j0 r j < i := by
          by_cases h1 : j = j0
          · subst h1; simpa using hi
          · by_cases h2 : j = r
            · subst h2; simpa using lt_of_le_of_lt hj0_le hi
            · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hj
        exact hbelow i _ hi hsw
      have hM1_pos_gt : ∀ i : Fin n, r < i → 0 < M1 i i := by
        intro i hi
        dsimp only [M1]
        rw [mul_swapColMat]
        have h1 : i ≠ j0 := ne_of_gt (lt_of_le_of_lt hj0_le hi)
        have h2 : i ≠ r := ne_of_gt hi
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        exact hpos i hi
      have hM1_row : ∀ j : Fin n, j < r → M1 r j = 0 := by
        intro j hj
        dsimp only [M1]
        rw [mul_swapColMat]
        have hsw_le : Equiv.swap j0 r j ≤ r := by
          by_cases h1 : j = j0
          · subst h1; simp
          · rw [Equiv.swap_apply_of_ne_of_ne h1 (ne_of_lt hj)]; exact le_of_lt hj
        have hsw_ne : Equiv.swap j0 r j ≠ j0 := by
          intro heq
          have : j = r := by
            have := congr_arg (Equiv.swap j0 r) heq
            simpa using this
          exact ne_of_lt hj this
        by_contra hne0
        have hmem : Equiv.swap j0 r j ∈ nz :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsw_le, hne0⟩
        rw [hj0_eq, Finset.mem_singleton] at hmem
        exact hsw_ne hmem
      have hM1_rr : M1 r r ≠ 0 := by
        dsimp only [M1]
        rw [mul_swapColMat]; simp [hj0_ne]
      by_cases hsign : 0 < M1 r r
      · refine ⟨M1, hce1, ?_, ?_⟩
        · intro i j hi hj
          rcases eq_or_lt_of_le hi with rfl | hlt
          · exact hM1_row j hj
          · exact hM1_below i j hlt hj
        · intro i hi
          rcases eq_or_lt_of_le hi with rfl | hlt
          · exact hsign
          · exact hM1_pos_gt i hlt
      · let M2 := M1 * (negColMat r).1
        refine ⟨M2, colEquiv_trans hce1 ⟨negColMat r, rfl⟩, ?_, ?_⟩
        · intro i j hi hj
          dsimp only [M2]
          rw [mul_negColMat]
          rcases eq_or_lt_of_le hi with rfl | hlt
          · simp [ne_of_lt hj, hM1_row j hj]
          · split_ifs <;> simp [hM1_below i j hlt hj]
        · intro i hi
          dsimp only [M2]
          rw [mul_negColMat]
          rcases eq_or_lt_of_le hi with rfl | hlt
          · simp only [↓reduceIte]; omega
          · simp [ne_of_gt hlt, hM1_pos_gt i hlt]
    · have hcard2 : 1 < nz.card := lt_of_le_of_ne (Finset.one_le_card.mpr hnz_ne) (Ne.symm hcard)
      obtain ⟨j0, hj0_mem, hj0_min⟩ :=
        Finset.exists_min_image nz (fun j => (M r j).natAbs) hnz_ne
      obtain ⟨j1, hj1_mem, hne⟩ : ∃ j1 ∈ nz, j1 ≠ j0 := by
        rcases Finset.one_lt_card.mp hcard2 with ⟨a, ha, b, hb, hab⟩
        by_cases h : a = j0
        · subst h; exact ⟨b, hb, hab.symm⟩
        · exact ⟨a, ha, h⟩
      have hj0_le : j0 ≤ r := (Finset.mem_filter.mp hj0_mem).2.1
      have hj0_ne : M r j0 ≠ 0 := (Finset.mem_filter.mp hj0_mem).2.2
      have hj1_le : j1 ≤ r := (Finset.mem_filter.mp hj1_mem).2.1
      have hmin_le : (M r j0).natAbs ≤ (M r j1).natAbs := hj0_min j1 hj1_mem
      let q : ℤ := M r j1 / M r j0
      let M1 := M * (addColMat j0 j1 hne.symm (-q)).1
      have hce1 : ColEquiv M M1 := ⟨addColMat j0 j1 hne.symm (-q), rfl⟩
      have hdet1 : M1.det ≠ 0 := by
        intro h0
        have := colEquiv_det_natAbs hce1
        rw [h0, Int.natAbs_zero] at this
        exact hdet (Int.natAbs_eq_zero.mp this.symm)
      have hbelow1 : ∀ i j : Fin n, r < i → j < i → M1 i j = 0 := by
        intro i j hi hj
        dsimp only [M1]
        rw [mul_addColMat]
        split_ifs
        · rw [hbelow i j hi hj, hbelow i j0 hi (lt_of_le_of_lt hj0_le hi)]
          simp
        · exact hbelow i j hi hj
      have hpos1 : ∀ i : Fin n, r < i → 0 < M1 i i := by
        intro i hi
        dsimp only [M1]
        rw [mul_addColMat]
        have hij1 : i ≠ j1 := ne_of_gt (lt_of_le_of_lt hj1_le hi)
        simp [hij1, hpos i hi]
      have hM1_j1 : M1 r j1 = M r j1 % M r j0 := by
        dsimp only [M1]
        rw [mul_addColMat]
        simp only [↓reduceIte, q]
        have hdiv := Int.emod_add_mul_ediv (M r j1) (M r j0)
        linarith
      have hlt_abs : (M1 r j1).natAbs < (M r j1).natAbs := by
        rw [hM1_j1]
        have hmod_nonneg : 0 ≤ M r j1 % M r j0 := Int.emod_nonneg _ hj0_ne
        have hmod_lt : M r j1 % M r j0 < |M r j0| := Int.emod_lt_abs _ hj0_ne
        have h1 : ((M r j1 % M r j0).natAbs : ℤ) < ((M r j0).natAbs : ℤ) := by
          rw [Int.natAbs_of_nonneg hmod_nonneg, ← Int.abs_eq_natAbs]
          exact hmod_lt
        exact lt_of_lt_of_le (Int.ofNat_lt.mp h1) hmin_le
      have hsum_lt :
          (∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ r), (M1 r j).natAbs) < s := by
        rw [← hs]
        refine Finset.sum_lt_sum (fun j _ => ?_)
          ⟨j1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj1_le⟩, hlt_abs⟩
        by_cases h : j = j1
        · subst h
          exact le_of_lt hlt_abs
        · dsimp only [M1]
          rw [mul_addColMat, if_neg h]
      obtain ⟨M', hce2, h2, h3⟩ := ih _ hsum_lt M1 hdet1 hbelow1 hpos1 rfl
      exact ⟨M', colEquiv_trans hce1 hce2, h2, h3⟩

lemma exists_upperTriangular_hermite {n : ℕ} (V : Matrix (Fin n) (Fin n) ℤ) (hdet : V.det ≠ 0) :
    ∃ T : Matrix (Fin n) (Fin n) ℤ,
      ColEquiv V T ∧
      (∀ i j : Fin n, j < i → T i j = 0) ∧
      (∀ i : Fin n, 0 < T i i) := by
  suffices h : ∀ k : ℕ, k ≤ n →
      ∃ M : Matrix (Fin n) (Fin n) ℤ,
        ColEquiv V M ∧
        (∀ i j : Fin n, n - k ≤ i.val → j < i → M i j = 0) ∧
        (∀ i : Fin n, n - k ≤ i.val → 0 < M i i) by
    obtain ⟨T, hce, h1, h2⟩ := h n le_rfl
    exact ⟨T, hce, fun i j hij => h1 i j (by omega) hij, fun i => h2 i (by omega)⟩
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨V, colEquiv_refl V, fun i _ hi => by omega, fun i hi => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨M, hce, h1, h2⟩ := ih (Nat.le_of_succ_le hk)
    let r : Fin n := ⟨n - (k + 1), by omega⟩
    have hdetM : M.det ≠ 0 := by
      intro h0
      have := colEquiv_det_natAbs hce
      rw [h0, Int.natAbs_zero] at this
      exact hdet (Int.natAbs_eq_zero.mp this.symm)
    have hbelow : ∀ i j : Fin n, r < i → j < i → M i j = 0 := by
      intro i j hi hj
      exact h1 i j (by simp only [r, Fin.lt_def] at hi; omega) hj
    have hpos : ∀ i : Fin n, r < i → 0 < M i i := by
      intro i hi
      exact h2 i (by simp only [r, Fin.lt_def] at hi; omega)
    obtain ⟨M', hce', h1', h2'⟩ := eliminate_row r _ M hdetM hbelow hpos rfl
    refine ⟨M', colEquiv_trans hce hce', ?_, ?_⟩
    · intro i j hi hj
      exact h1' i j (show r ≤ i by simp only [r, Fin.le_def]; exact hi) hj
    · intro i hi
      exact h2' i (show r ≤ i by simp only [r, Fin.le_def]; exact hi)

/-! ### Section 4: Backwards-peeling character orthogonality (Lemma L2) -/

lemma geom_sum_roots_unity (t : ℕ) (ht : 0 < t) (c : ℤ) :
    ∑ u : Fin t, Complex.exp (2 * Real.pi * Complex.I * ((u : ℕ) : ℂ) * (c : ℂ) / (t : ℂ)) =
      if (t : ℤ) ∣ c then (t : ℂ) else 0 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (c : ℂ) / (t : ℂ))
  have hterm : ∀ u : Fin t,
      Complex.exp (2 * Real.pi * Complex.I * ((u : ℕ) : ℂ) * (c : ℂ) / (t : ℂ)) = ζ ^ (u : ℕ) := by
    intro u
    rw [← Complex.exp_nat_mul]
    congr 1; ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun u => ζ ^ u) t]
  split_ifs with hdvd
  · rcases hdvd with ⟨q, rfl⟩
    have hζ : ζ = 1 := by
      simp only [ζ]
      have htC : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ht)
      have harg : 2 * ↑Real.pi * Complex.I * ((t : ℤ) * q : ℤ) / (t : ℂ) =
          (q : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; field_simp [htC]
      rw [harg, Complex.exp_int_mul_two_pi_mul_I]
    simp [hζ]
  · have hζne : ζ ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      rcases h1 with ⟨q, hq⟩
      have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have htC : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ht)
      have hceq : (c : ℂ) = (q : ℂ) * (t : ℂ) := by
        have h1' : (c : ℂ) / (t : ℂ) * (2 * Real.pi * Complex.I) =
            (q : ℂ) * (2 * Real.pi * Complex.I) := by
          rw [← hq]; ring
        have h2' := mul_right_cancel₀ h2pi h1'
        exact (div_eq_iff htC).mp h2'
      have hcz : c = (t : ℤ) * q := by
        have hcc : (c : ℂ) = (((t : ℤ) * q : ℤ) : ℂ) := by
          push_cast; rw [hceq]; ring
        exact Int.cast_injective hcc
      exact hdvd ⟨q, hcz⟩
    rw [geom_sum_eq hζne]
    have hpow : ζ ^ t = 1 := by
      simp only [ζ, ← Complex.exp_nat_mul]
      have htC : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ht)
      have harg : (t : ℂ) * (2 * Real.pi * Complex.I * (c : ℂ) / (t : ℂ)) =
          (c : ℂ) * (2 * Real.pi * Complex.I) := by
        field_simp [htC]
      rw [harg, Complex.exp_int_mul_two_pi_mul_I]
    rw [hpow, sub_self, zero_div]

def diagNat {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℕ := (T i i).toNat

lemma diagNat_pos {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) (hT_pos : ∀ i : Fin n, 0 < T i i)
    (i : Fin n) : 0 < diagNat T i := by
  simp only [diagNat]
  have := hT_pos i
  omega

lemma diagNat_cast {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) (hT_pos : ∀ i : Fin n, 0 < T i i)
    (i : Fin n) : (diagNat T i : ℤ) = T i i := by
  simp only [diagNat]
  exact Int.toNat_of_nonneg (le_of_lt (hT_pos i))

def prefixProd {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) (hm : m ≤ n) : ℕ :=
  ∏ j : Fin m, diagNat T ⟨j.1, lt_of_lt_of_le j.2 hm⟩

lemma prefixProd_pos {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) (hT_pos : ∀ i : Fin n, 0 < T i i)
    (m : ℕ) (hm : m ≤ n) : 0 < prefixProd T m hm := by
  apply Finset.prod_pos
  intro j _
  exact diagNat_pos T hT_pos _

lemma prefixProd_succ {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) (hm : m + 1 ≤ n) :
    prefixProd T (m + 1) hm = prefixProd T m (Nat.le_of_succ_le hm) * diagNat T ⟨m, hm⟩ := by
  simp only [prefixProd]
  rw [Fin.prod_univ_castSucc]
  rfl

lemma prefixProd_dvd_full {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) (hm : m ≤ n) :
    prefixProd T m hm ∣ prefixProd T n le_rfl := by
  suffices h : ∀ k : ℕ, ∀ m : ℕ, ∀ hm : m ≤ n, n - m = k →
      prefixProd T m hm ∣ prefixProd T n le_rfl from h (n - m) m hm rfl
  intro k
  induction k with
  | zero =>
    intro m hm hnm
    have hmn : m = n := by omega
    subst hmn; exact dvd_refl _
  | succ k ih =>
    intro m hm hnm
    have hm1 : m + 1 ≤ n := by omega
    have hd1 : prefixProd T m hm ∣ prefixProd T (m + 1) hm1 := by
      rw [prefixProd_succ]; exact dvd_mul_right _ _
    exact dvd_trans hd1 (ih (m + 1) hm1 (by omega))

def HPrefix {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) (d : ℕ) (m : ℕ) (hm : m ≤ n) :
    Finset (Fin m → Fin d) :=
  Finset.univ.filter fun r =>
    ∀ c : Fin m, (d : ℤ) ∣
      ∑ j : Fin m, T ⟨j.1, lt_of_lt_of_le j.2 hm⟩ ⟨c.1, lt_of_lt_of_le c.2 hm⟩ * (r j : ℤ)

lemma hPrefix_dvd_invariant {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ)
    (hT_upper : ∀ i j : Fin n, j < i → T i j = 0)
    (hT_pos : ∀ i : Fin n, 0 < T i i)
    (m : ℕ) (hm : m ≤ n) :
    let d := prefixProd T n le_rfl
    ∀ r ∈ HPrefix T d m hm, ∀ j : Fin m, (d : ℤ) ∣ (prefixProd T m hm : ℤ) * (r j : ℤ) := by
  intro d
  induction m with
  | zero => intro _ _ j; exact Fin.elim0 j
  | succ m ih =>
    intro r hr j
    have hm' : m ≤ n := Nat.le_of_succ_le hm
    let r' : Fin m → Fin d := fun i => r i.castSucc
    have hr' : r' ∈ HPrefix T d m hm' := by
      rw [HPrefix, Finset.mem_filter] at hr ⊢
      refine ⟨Finset.mem_univ _, fun c => ?_⟩
      have hc := hr.2 c.castSucc
      rw [Fin.sum_univ_castSucc] at hc
      have hlast : T ⟨m, hm⟩ ⟨c.1, lt_of_lt_of_le c.2 hm'⟩ = 0 :=
        hT_upper _ _ (by simp [Fin.lt_def])
      simpa [r', hlast] using hc
    have hprev : ∀ i : Fin m, (d : ℤ) ∣ (prefixProd T m hm' : ℤ) * (r i.castSucc : ℤ) :=
      fun i => ih hm' r' hr' i
    rw [prefixProd_succ T m hm, Nat.cast_mul]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [HPrefix, Finset.mem_filter] at hr
      have hlast_eq := hr.2 (Fin.last m)
      rw [Fin.sum_univ_castSucc] at hlast_eq
      have hmul : (d : ℤ) ∣ (prefixProd T m hm' : ℤ) *
          ((∑ i : Fin m, T ⟨i.1, lt_of_lt_of_le i.2 hm'⟩ ⟨m, hm⟩ * (r i.castSucc : ℤ)) +
            T ⟨m, hm⟩ ⟨m, hm⟩ * (r (Fin.last m) : ℤ)) :=
        dvd_mul_of_dvd_right hlast_eq _
      rw [mul_add, Finset.mul_sum] at hmul
      have hsum_dvd : (d : ℤ) ∣ ∑ i : Fin m,
          (prefixProd T m hm' : ℤ) * (T ⟨i.1, lt_of_lt_of_le i.2 hm'⟩ ⟨m, hm⟩ * (r i.castSucc : ℤ)) := by
        refine Finset.dvd_sum fun i _ => ?_
        have hrearr : (prefixProd T m hm' : ℤ) *
            (T ⟨i.1, lt_of_lt_of_le i.2 hm'⟩ ⟨m, hm⟩ * (r i.castSucc : ℤ)) =
            T ⟨i.1, lt_of_lt_of_le i.2 hm'⟩ ⟨m, hm⟩ * ((prefixProd T m hm' : ℤ) * (r i.castSucc : ℤ)) := by
          ring
        rw [hrearr]
        exact dvd_mul_of_dvd_right (hprev i) _
      have hterm := (dvd_add_right hsum_dvd).mp hmul
      rw [← mul_assoc, ← diagNat_cast T hT_pos ⟨m, hm⟩] at hterm
      exact hterm
    · have hrearr : (prefixProd T m hm' : ℤ) * (diagNat T ⟨m, hm⟩ : ℤ) * (r i.castSucc : ℤ) =
          (diagNat T ⟨m, hm⟩ : ℤ) * ((prefixProd T m hm' : ℤ) * (r i.castSucc : ℤ)) := by ring
      rw [hrearr]
      exact dvd_mul_of_dvd_right (hprev i) _

lemma sum_char_HPrefix {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ)
    (hT_upper : ∀ i j : Fin n, j < i → T i j = 0)
    (hT_pos : ∀ i : Fin n, 0 < T i i)
    (m : ℕ) (hm : m ≤ n) :
    let d := prefixProd T n le_rfl
    ∀ w : Fin m → ℤ,
      ∑ r ∈ HPrefix T d m hm,
        Complex.exp (2 * Real.pi * Complex.I * (∑ j : Fin m, ((r j : ℕ) : ℂ) * (w j : ℂ)) / (d : ℂ)) =
        if ∃ b : Fin m → ℤ, ∀ i : Fin m,
          ∑ j : Fin m, T ⟨i.1, lt_of_lt_of_le i.2 hm⟩ ⟨j.1, lt_of_lt_of_le j.2 hm⟩ * b j = w i
        then (prefixProd T m hm : ℂ) else 0 := by
  intro d
  have hd_pos : 0 < d := prefixProd_pos T hT_pos n le_rfl
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd_pos)
  induction m with
  | zero =>
    intro w
    have hH0 : HPrefix T d 0 hm = Finset.univ := by
      ext r; simp [HPrefix]
    rw [hH0]
    simp [prefixProd]
  | succ m ih =>
    intro w
    have hm' : m ≤ n := Nat.le_of_succ_le hm
    let tm : ℕ := diagNat T ⟨m, hm⟩
    have htm_pos : 0 < tm := diagNat_pos T hT_pos ⟨m, hm⟩
    have htm_cast : (tm : ℤ) = T ⟨m, hm⟩ ⟨m, hm⟩ := diagNat_cast T hT_pos ⟨m, hm⟩
    have hPm1_dvd : prefixProd T (m + 1) hm ∣ d := prefixProd_dvd_full T (m + 1) hm
    rw [prefixProd_succ T m hm] at hPm1_dvd
    have htm_dvd_d : tm ∣ d := dvd_trans (dvd_mul_left _ _) hPm1_dvd
    let qd : ℕ := d / tm
    have hqd_mul : tm * qd = d := Nat.mul_div_cancel' htm_dvd_d
    have hqd_pos : 0 < qd := by
      have : 0 < tm * qd := by omega
      exact Nat.pos_of_mul_pos_left this
    let sOf (r' : Fin m → Fin d) : ℤ :=
      ∑ i : Fin m, T ⟨i.1, lt_of_lt_of_le i.2 hm'⟩ ⟨m, hm⟩ * (r' i : ℤ)
    have htm_dvd_s : ∀ r' ∈ HPrefix T d m hm', (tm : ℤ) ∣ sOf r' := by
      intro r' hr'
      have hPm_dvd_d : prefixProd T m hm' ∣ d := prefixProd_dvd_full T m hm'
      let step := d / prefixProd T m hm'
      have hstep_mul : prefixProd T m hm' * step = d := Nat.mul_div_cancel' hPm_dvd_d
      have htm_dvd_step : tm ∣ step := by
        rcases hPm1_dvd with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        have hPm_pos : 0 < prefixProd T m hm' := prefixProd_pos T hT_pos m hm'
        have : prefixProd T m hm' * step = prefixProd T m hm' * (tm * c) := by
          linarith [hstep_mul, hc]
        exact Nat.eq_of_mul_eq_mul_left hPm_pos this
      refine Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right ?_ _
      have hinv := hPrefix_dvd_invariant T hT_upper hT_pos m hm' r' hr' i
      have hstep_dvd : (step : ℤ) ∣ (r' i : ℤ) := by
        rcases hinv with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hPm_ne : (prefixProd T m hm' : ℤ) ≠ 0 :=
          Int.ofNat_ne_zero.mpr (Nat.ne_of_gt (prefixProd_pos T hT_pos m hm'))
        have : (prefixProd T m hm' : ℤ) * (r' i : ℤ) =
            (prefixProd T m hm' : ℤ) * ((step : ℤ) * k) := by
          calc (prefixProd T m hm' : ℤ) * (r' i : ℤ)
              = (d : ℤ) * k := hk
            _ = (prefixProd T m hm' : ℤ) * (step : ℤ) * k := by
                rw [← hstep_mul]; push_cast; rfl
            _ = (prefixProd T m hm' : ℤ) * ((step : ℤ) * k) := by ring
        exact mul_left_cancel₀ hPm_ne this
      exact dvd_trans (Int.ofNat_dvd.mpr htm_dvd_step) hstep_dvd
    let r0 (r' : Fin m → Fin d) : ℕ := (((-(sOf r' / (tm : ℤ))) % (qd : ℤ))).toNat
    have hr0_lt : ∀ r' : Fin m → Fin d, r0 r' < qd := by
      intro r'
      have hqd_ne : (qd : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hqd_pos)
      have hnn : 0 ≤ (-(sOf r' / (tm : ℤ))) % (qd : ℤ) := Int.emod_nonneg _ hqd_ne
      have hlt : (-(sOf r' / (tm : ℤ))) % (qd : ℤ) < (qd : ℤ) :=
        Int.emod_lt_of_pos _ (Nat.cast_pos.mpr hqd_pos)
      have h1 : (r0 r' : ℤ) < (qd : ℤ) := by
        simp only [r0]
        rw [Int.toNat_of_nonneg hnn]
        exact hlt
      exact Int.ofNat_lt.mp h1
    have hr0_cast : ∀ r' : Fin m → Fin d, (r0 r' : ℤ) = (-(sOf r' / (tm : ℤ))) % (qd : ℤ) := by
      intro r'
      have hqd_ne : (qd : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hqd_pos)
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ hqd_ne)
    have hr0_cong : ∀ r' ∈ HPrefix T d m hm',
        (d : ℤ) ∣ (tm : ℤ) * (r0 r' : ℤ) + sOf r' := by
      intro r' hr'
      rcases htm_dvd_s r' hr' with ⟨k, hk⟩
      have hdiv : sOf r' / (tm : ℤ) = k := by
        rw [hk, Int.mul_ediv_cancel_left _ (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt htm_pos))]
      rw [hr0_cast, hdiv, hk]
      have hqd_dvd : (qd : ℤ) ∣ (-k % (qd : ℤ)) + k := by
        have := Int.emod_add_mul_ediv (-k) (qd : ℤ)
        refine ⟨-((-k) / (qd : ℤ)), ?_⟩
        linarith
      rcases hqd_dvd with ⟨u, hu⟩
      refine ⟨u, ?_⟩
      calc (tm : ℤ) * (-k % (qd : ℤ)) + (tm : ℤ) * k
          = (tm : ℤ) * ((-k % (qd : ℤ)) + k) := by ring
        _ = (tm : ℤ) * ((qd : ℤ) * u) := by rw [hu]
        _ = (d : ℤ) * u := by rw [← mul_assoc, ← Nat.cast_mul, hqd_mul]
    let lift (r' : Fin m → Fin d) (u : Fin tm) : Fin (m + 1) → Fin d :=
      Fin.snoc r' ⟨r0 r' + u.1 * qd, by
        have h1 := hr0_lt r'
        have h2 : u.1 + 1 ≤ tm := u.2
        have : r0 r' + u.1 * qd < (u.1 + 1) * qd := by nlinarith
        calc r0 r' + u.1 * qd < (u.1 + 1) * qd := this
          _ ≤ tm * qd := Nat.mul_le_mul_right qd h2
          _ = d := hqd_mul⟩
    have hsum_biject :
        ∑ r ∈ HPrefix T d (m + 1) hm,
          Complex.exp (2 * Real.pi * Complex.I *
            (∑ j : Fin (m + 1), ((r j : ℕ) : ℂ) * (w j : ℂ)) / (d : ℂ)) =
        ∑ r' ∈ HPrefix T d m hm', ∑ u : Fin tm,
          Complex.exp (2 * Real.pi * Complex.I *
            (∑ j : Fin (m + 1), (((lift r' u j : ℕ) : ℂ) * (w j : ℂ))) / (d : ℂ)) := by
      rw [← Finset.sum_product']
      refine (Finset.sum_bij (fun p _ => lift p.1 p.2) ?_ ?_ ?_ ?_).symm
      · intro ⟨r', u⟩ hp
        have hr' : r' ∈ HPrefix T d m hm' := (Finset.mem_product.mp hp).1
        rw [HPrefix, Finset.mem_filter] at hr' ⊢
        refine ⟨Finset.mem_univ _, fun c => ?_⟩
        refine Fin.lastCases ?_ (fun c' => ?_) c
        · rw [Fin.sum_univ_castSucc]
          simp only [lift, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_mk, Fin.val_last,
            Fin.val_castSucc]
          have heq : (∑ x : Fin m, T ⟨x.1, lt_of_lt_of_le x.2 hm'⟩ ⟨m, hm⟩ * (r' x : ℤ)) +
              T ⟨m, hm⟩ ⟨m, hm⟩ * ((r0 r' + u.1 * qd : ℕ) : ℤ) =
              ((tm : ℤ) * (r0 r' : ℤ) + sOf r') + (d : ℤ) * (u.1 : ℤ) := by
            simp only [sOf, Nat.cast_add, Nat.cast_mul, ← htm_cast]
            have : (tm : ℤ) * (qd : ℤ) = (d : ℤ) := by exact_mod_cast hqd_mul
            linear_combination (u.1 : ℤ) * this
          rw [heq]
          exact dvd_add (hr0_cong r' (by rw [HPrefix, Finset.mem_filter]; exact hr'))
            (dvd_mul_right _ _)
        · rw [Fin.sum_univ_castSucc]
          have hlast : T ⟨m, hm⟩ ⟨c'.1, lt_of_lt_of_le c'.2 hm'⟩ = 0 :=
            hT_upper _ _ (by simp [Fin.lt_def])
          simpa [lift, hlast] using hr'.2 c'
      · intro ⟨r1, u1⟩ _ ⟨r2, u2⟩ _ heq
        have hr_eq : r1 = r2 := by
          ext i
          have hci := congr_fun heq i.castSucc
          simp only [lift, Fin.snoc_castSucc] at hci
          exact congr_arg Fin.val hci
        subst hr_eq
        have hlast := congr_fun heq (Fin.last m)
        simp only [lift, Fin.snoc_last, Fin.mk.injEq] at hlast
        have hu_eq : u1 = u2 := by
          ext
          have : u1.1 * qd = u2.1 * qd := by omega
          exact Nat.eq_of_mul_eq_mul_right hqd_pos this
        exact Prod.ext rfl hu_eq
      · intro r hr
        rw [HPrefix, Finset.mem_filter] at hr
        let r' : Fin m → Fin d := fun i => r i.castSucc
        have hr' : r' ∈ HPrefix T d m hm' := by
          rw [HPrefix, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, fun c' => ?_⟩
          have hc := hr.2 c'.castSucc
          rw [Fin.sum_univ_castSucc] at hc
          have hlast : T ⟨m, hm⟩ ⟨c'.1, lt_of_lt_of_le c'.2 hm'⟩ = 0 :=
            hT_upper _ _ (by simp [Fin.lt_def])
          simpa [r', hlast] using hc
        have hlast_dvd := hr.2 (Fin.last m)
        rw [Fin.sum_univ_castSucc] at hlast_dvd
        have hdiff : (d : ℤ) ∣ (tm : ℤ) * ((r (Fin.last m) : ℤ) - (r0 r' : ℤ)) := by
          have h1 : (d : ℤ) ∣ (tm : ℤ) * (r (Fin.last m) : ℤ) + sOf r' := by
            simpa [sOf, r', htm_cast, add_comm] using hlast_dvd
          have h2 := hr0_cong r' hr'
          have hsub := dvd_sub h1 h2
          have hrew : ((tm : ℤ) * (r (Fin.last m) : ℤ) + sOf r') -
              ((tm : ℤ) * (r0 r' : ℤ) + sOf r') =
              (tm : ℤ) * ((r (Fin.last m) : ℤ) - (r0 r' : ℤ)) := by ring
          rwa [← hrew]
        have hqd_dvd : (qd : ℤ) ∣ (r (Fin.last m) : ℤ) - (r0 r' : ℤ) := by
          rcases hdiff with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          have htm_ne : (tm : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.ne_of_gt htm_pos)
          have : (tm : ℤ) * ((r (Fin.last m) : ℤ) - (r0 r' : ℤ)) = (tm : ℤ) * ((qd : ℤ) * k) := by
            calc _ = (d : ℤ) * k := hk
              _ = (tm : ℤ) * (qd : ℤ) * k := by rw [← hqd_mul]; push_cast; rfl
              _ = _ := by ring
          exact mul_left_cancel₀ htm_ne this
        rcases hqd_dvd with ⟨uZ, huZ⟩
        have huZ_nn : 0 ≤ uZ := by
          have hr_nn : (0 : ℤ) ≤ (r (Fin.last m) : ℤ) := Int.natCast_nonneg _
          have hr0_l : (r0 r' : ℤ) < (qd : ℤ) := Int.ofNat_lt.mpr (hr0_lt r')
          nlinarith
        have huZ_lt : uZ < (tm : ℤ) := by
          have hr_lt : (r (Fin.last m) : ℤ) < (d : ℤ) := Int.ofNat_lt.mpr (r (Fin.last m)).2
          have hd_eq : (d : ℤ) = (tm : ℤ) * (qd : ℤ) := by exact_mod_cast hqd_mul.symm
          have hr0_nn : (0 : ℤ) ≤ (r0 r' : ℤ) := Int.natCast_nonneg _
          nlinarith
        let u : Fin tm := ⟨uZ.toNat, by omega⟩
        refine ⟨(r', u), Finset.mem_product.mpr ⟨hr', Finset.mem_univ _⟩, ?_⟩
        ext j
        refine Fin.lastCases ?_ (fun i => by simp [lift, r']) j
        simp only [lift, Fin.snoc_last, Fin.val_mk]
        have : ((r0 r' + uZ.toNat * qd : ℕ) : ℤ) = (r (Fin.last m) : ℤ) := by
          push_cast
          rw [Int.toNat_of_nonneg huZ_nn]
          linarith
        exact_mod_cast this
      · intro ⟨r', u⟩ _; rfl
    rw [hsum_biject]
    have hfactor : ∀ r' ∈ HPrefix T d m hm',
        ∑ u : Fin tm,
          Complex.exp (2 * Real.pi * Complex.I *
            (∑ j : Fin (m + 1), (((lift r' u j : ℕ) : ℂ) * (w j : ℂ))) / (d : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I *
            (∑ i : Fin m, ((r' i : ℕ) : ℂ) * (w i.castSucc : ℂ)) / (d : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * ((r0 r' : ℕ) : ℂ) * (w (Fin.last m) : ℂ) / (d : ℂ)) *
        (if (tm : ℤ) ∣ w (Fin.last m) then (tm : ℂ) else 0) := by
      intro r' _
      rw [← geom_sum_roots_unity tm htm_pos (w (Fin.last m)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [Fin.sum_univ_castSucc]
      simp only [lift, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_mk, Nat.cast_add, Nat.cast_mul]
      have hqdC : (tm : ℂ) * (qd : ℂ) = (d : ℂ) := by exact_mod_cast hqd_mul
      have htmC : (tm : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt htm_pos)
      have hqdC_ne : (qd : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hqd_pos)
      rw [← hqdC]
      field_simp [htmC, hqdC_ne]
      ring
    rw [Finset.sum_congr rfl hfactor]
    by_cases hdvd : (tm : ℤ) ∣ w (Fin.last m)
    · rcases hdvd with ⟨bm, hbm⟩
      have hdiv_true : (tm : ℤ) ∣ w (Fin.last m) := ⟨bm, hbm⟩
      simp only [hdiv_true, ↓reduceIte]
      let w' : Fin m → ℤ := fun i => w i.castSucc - T ⟨i.1, lt_of_lt_of_le i.2 hm'⟩ ⟨m, hm⟩ * bm
      have hex_iff :
          (∃ b : Fin (m + 1) → ℤ, ∀ i : Fin (m + 1),
            ∑ j : Fin (m + 1), T ⟨i.1, lt_of_lt_of_le i.2 hm⟩ ⟨j.1, lt_of_lt_of_le j.2 hm⟩ * b j = w i) ↔
          (∃ b' : Fin m → ℤ, ∀ i : Fin m,
            ∑ j : Fin m, T ⟨i.1, lt_of_lt_of_le i.2 hm'⟩ ⟨j.1, lt_of_lt_of_le j.2 hm'⟩ * b' j = w' i) := by
        constructor
        · rintro ⟨b, hb⟩
          have hbm_eq : b (Fin.last m) = bm := by
            have hlast := hb (Fin.last m)
            rw [Fin.sum_univ_castSucc] at hlast
            simp only [Fin.val_last, Fin.val_castSucc] at hlast
            have hz : ∑ j : Fin m, T ⟨m, hm⟩ ⟨j.1, lt_of_lt_of_le j.2 hm'⟩ * b j.castSucc = 0 := by
              refine Finset.sum_eq_zero fun j _ => ?_
              rw [hT_upper _ _ (by simp [Fin.lt_def]), zero_mul]
            rw [hz, zero_add, ← htm_cast, hbm] at hlast
            exact mul_left_cancel₀ (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt htm_pos)) hlast
          refine ⟨fun j => b j.castSucc, fun i => ?_⟩
          have hi := hb i.castSucc
          rw [Fin.sum_univ_castSucc] at hi
          simp only [Fin.val_castSucc, Fin.val_last, hbm_eq] at hi
          simp only [w']; linarith
        · rintro ⟨b', hb'⟩
          refine ⟨Fin.snoc b' bm, fun i => ?_⟩
          refine Fin.lastCases ?_ (fun i' => ?_) i
          · rw [Fin.sum_univ_castSucc]
            simp only [Fin.val_last, Fin.val_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
            have hz : ∑ j : Fin m, T ⟨m, hm⟩ ⟨j.1, lt_of_lt_of_le j.2 hm'⟩ * b' j = 0 := by
              refine Finset.sum_eq_zero fun j _ => ?_
              rw [hT_upper _ _ (by simp [Fin.lt_def]), zero_mul]
            rw [hz, zero_add, ← htm_cast, hbm]
          · rw [Fin.sum_univ_castSucc]
            simp only [Fin.val_castSucc, Fin.val_last, Fin.snoc_castSucc, Fin.snoc_last]
            have hi' := hb' i'
            simp only [w'] at hi'
            linarith
      have hterm_eq : ∀ r' ∈ HPrefix T d m hm',
          Complex.exp (2 * Real.pi * Complex.I *
              (∑ i : Fin m, ((r' i : ℕ) : ℂ) * (w i.castSucc : ℂ)) / (d : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * ((r0 r' : ℕ) : ℂ) * (w (Fin.last m) : ℂ) / (d : ℂ)) *
          (tm : ℂ) =
          (tm : ℂ) * Complex.exp (2 * Real.pi * Complex.I *
              (∑ i : Fin m, ((r' i : ℕ) : ℂ) * (w' i : ℂ)) / (d : ℂ)) := by
        intro r' hr'
        rw [mul_comm _ (tm : ℂ)]
        congr 1
        rw [← Complex.exp_add]
        rcases hr0_cong r' hr' with ⟨k, hk⟩
        have hdiff_exp :
            2 * Real.pi * Complex.I * (∑ i : Fin m, ((r' i : ℕ) : ℂ) * (w i.castSucc : ℂ)) / (d : ℂ) +
            2 * Real.pi * Complex.I * ((r0 r' : ℕ) : ℂ) * (w (Fin.last m) : ℂ) / (d : ℂ) =
            2 * Real.pi * Complex.I * (∑ i : Fin m, ((r' i : ℕ) : ℂ) * (w' i : ℂ)) / (d : ℂ) +
            ((k * bm : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
          have hkC : (tm : ℂ) * ((r0 r' : ℕ) : ℂ) +
              (∑ i : Fin m, (T ⟨i.1, lt_of_lt_of_le i.2 hm'⟩ ⟨m, hm⟩ : ℂ) * ((r' i : ℕ) : ℂ)) =
              (d : ℂ) * (k : ℂ) := by
            have := congr_arg (Int.cast : ℤ → ℂ) hk
            simpa [sOf] using this
          have hw_split : ∑ i : Fin m, ((r' i : ℕ) : ℂ) * (w' i : ℂ) =
              (∑ i : Fin m, ((r' i : ℕ) : ℂ) * (w i.castSucc : ℂ)) -
              (bm : ℂ) * (∑ i : Fin m, (T ⟨i.1, lt_of_lt_of_le i.2 hm'⟩ ⟨m, hm⟩ : ℂ) * ((r' i : ℕ) : ℂ)) := by
            simp only [w', Int.cast_sub, Int.cast_mul, mul_sub, Finset.sum_sub_distrib,
              Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun i _ => by ring
          have hST : (∑ i : Fin m, (T ⟨i.1, lt_of_lt_of_le i.2 hm'⟩ ⟨m, hm⟩ : ℂ) * ((r' i : ℕ) : ℂ)) =
              (d : ℂ) * (k : ℂ) - (tm : ℂ) * ((r0 r' : ℕ) : ℂ) := eq_sub_of_add_eq' hkC
          rw [hw_split, hST, hbm]
          push_cast
          field_simp [hdC]
          ring
        rw [hdiff_exp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      rw [Finset.sum_congr rfl hterm_eq, ← Finset.mul_sum, ih hm' w', hex_iff]
      split_ifs
      · rw [prefixProd_succ T m hm, Nat.cast_mul, mul_comm]
      · simp
    · simp only [hdvd, ↓reduceIte, mul_zero, Finset.sum_const_zero]
      have hno : ¬ ∃ b : Fin (m + 1) → ℤ, ∀ i : Fin (m + 1),
          ∑ j : Fin (m + 1), T ⟨i.1, lt_of_lt_of_le i.2 hm⟩ ⟨j.1, lt_of_lt_of_le j.2 hm⟩ * b j = w i := by
        rintro ⟨b, hb⟩
        have hlast := hb (Fin.last m)
        rw [Fin.sum_univ_castSucc] at hlast
        simp only [Fin.val_last, Fin.val_castSucc] at hlast
        have hz : ∑ j : Fin m, T ⟨m, hm⟩ ⟨j.1, lt_of_lt_of_le j.2 hm'⟩ * b j.castSucc = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [hT_upper _ _ (by simp [Fin.lt_def]), zero_mul]
        rw [hz, zero_add, ← htm_cast] at hlast
        exact hdvd ⟨b (Fin.last m), hlast.symm⟩
      simp [hno]

/-! ### Section 5: Product factorization of `n`-dimensional `tsum` and Main Theorem (Lemma L5) -/

def finSuccFunEquiv (n : ℕ) : (Fin (n + 1) → ℤ) ≃ ℤ × (Fin n → ℤ) where
  toFun k := (k 0, fun j => k j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv k := by ext j; refine Fin.cases rfl (fun _ => rfl) j
  right_inv p := by rcases p with ⟨a, b⟩; ext <;> simp

lemma summable_and_tsum_fin_prod (n : ℕ) :
    ∀ (F : Fin n → ℤ → ℂ),
      (∀ j : Fin n, Summable (fun m : ℤ => ‖F j m‖)) →
      Summable (fun k : Fin n → ℤ => ‖∏ j : Fin n, F j (k j)‖) ∧
      (∑' k : Fin n → ℤ, ∏ j : Fin n, F j (k j)) = ∏ j : Fin n, ∑' m : ℤ, F j m := by
  induction n with
  | zero =>
    intro F _
    refine ⟨(hasSum_unique _).summable, ?_⟩
    rw [(hasSum_unique _).tsum_eq]
    simp
  | succ n ih =>
    intro F hF
    obtain ⟨hs_tail, htsum_tail⟩ := ih (fun j => F j.succ) (fun j => hF j.succ)
    let f0 : ℤ → ℂ := F 0
    let gtail : (Fin n → ℤ) → ℂ := fun k => ∏ j : Fin n, F j.succ (k j)
    have hs_prod_norm :
        Summable (fun p : ℤ × (Fin n → ℤ) => ‖f0 p.1 * gtail p.2‖) :=
      Summable.mul_norm (f := f0) (g := gtail) (hF 0) hs_tail
    have hnorm_eq : (fun k : Fin (n + 1) → ℤ => ‖∏ j : Fin (n + 1), F j (k j)‖) =
        (fun p : ℤ × (Fin n → ℤ) => ‖f0 p.1 * gtail p.2‖) ∘
          finSuccFunEquiv n := by
      ext k
      simp only [Function.comp_apply, finSuccFunEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, f0, gtail]
    have hs_all : Summable (fun k : Fin (n + 1) → ℤ => ‖∏ j : Fin (n + 1), F j (k j)‖) := by
      rw [hnorm_eq]
      exact hs_prod_norm.comp_injective (finSuccFunEquiv n).injective
    refine ⟨hs_all, ?_⟩
    have hval_eq :
        (fun p : ℤ × (Fin n → ℤ) => ∏ j : Fin (n + 1), F j ((finSuccFunEquiv n).symm p j)) =
        fun p => f0 p.1 * gtail p.2 := by
      ext ⟨a, b⟩
      simp only [finSuccFunEquiv, Equiv.coe_fn_symm_mk, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ, f0, gtail]
    calc ∑' k : Fin (n + 1) → ℤ, ∏ j : Fin (n + 1), F j (k j)
        = ∑' p : ℤ × (Fin n → ℤ), ∏ j : Fin (n + 1), F j ((finSuccFunEquiv n).symm p j) :=
          (Equiv.tsum_eq (finSuccFunEquiv n).symm _).symm
      _ = ∑' p : ℤ × (Fin n → ℤ), f0 p.1 * gtail p.2 := by
          rw [hval_eq]
      _ = (∑' m : ℤ, f0 m) * ∑' k' : Fin n → ℤ, gtail k' :=
          (tsum_mul_tsum_of_summable_norm (f := f0) (g := gtail) (hF 0) hs_tail).symm
      _ = (∑' m : ℤ, F 0 m) * ∏ j : Fin n, ∑' m : ℤ, F j.succ m := by
          rw [htsum_tail]
      _ = ∏ j : Fin (n + 1), ∑' m : ℤ, F j m := by
          rw [Fin.prod_univ_succ]

lemma mulVec_injective_of_det_ne_zero {n : ℕ} (V : Matrix (Fin n) (Fin n) ℤ) (hdet : V.det ≠ 0) :
    Function.Injective V.mulVec := by
  intro a b hab
  have hq_det : (V.map (Int.castRingHom ℚ)).det ≠ 0 := by
    change ((Int.castRingHom ℚ).mapMatrix V).det ≠ 0
    rw [← RingHom.map_det]
    exact Int.cast_ne_zero.mpr hdet
  rcases (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hq_det) with ⟨U, hU⟩
  have hmul : (V.map (Int.castRingHom ℚ)).mulVec (fun j => (a j : ℚ)) =
      (V.map (Int.castRingHom ℚ)).mulVec (fun j => (b j : ℚ)) := by
    ext i
    have hi := congr_fun hab i
    have hiq := congr_arg (Int.cast : ℤ → ℚ) hi
    simpa [Matrix.mulVec, dotProduct] using hiq
  have heq_q := congr_arg (fun v => U.inv.mulVec v) hmul
  rw [← hU, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_val,
    Matrix.one_mulVec, Matrix.one_mulVec] at heq_q
  ext i
  exact Int.cast_injective (congr_fun heq_q i)

theorem main_proof (n : ℕ) (V : Matrix (Fin n) (Fin n) ℤ) (_hn : 1 ≤ n) (hdet : V.det ≠ 0) :
    ∃ P : ℤ[X],
      (∑' a : Fin n → ℤ, ∏ j : Fin n, (1 : ℝ) / (1 + ((V.mulVec a j : ℤ) : ℝ) ^ 2)) =
        Real.pi ^ n / (Real.sinh Real.pi ^ n * |(V.det : ℝ)|) *
          (P.map (Int.castRingHom ℝ)).eval (Real.cosh (Real.pi / |(V.det : ℝ)|)) := by
  obtain ⟨T, hce, hT_upper, hT_pos⟩ := exists_upperTriangular_hermite V hdet
  let d : ℕ := prefixProd T n le_rfl
  have hd_pos : 0 < d := prefixProd_pos T hT_pos n le_rfl
  have hT_det : T.det = (d : ℤ) := by
    have hUT : T.IsUpperTriangular := fun i j hij => hT_upper i j hij
    rw [Matrix.det_of_isUpperTriangular hUT]
    simp only [d, prefixProd, Nat.cast_prod]
    exact Finset.prod_congr rfl fun i _ => (diagNat_cast T hT_pos i).symm
  have hd_eq_abs : |(V.det : ℝ)| = (d : ℝ) := by
    have hna : V.det.natAbs = d := by
      rw [← colEquiv_det_natAbs hce, hT_det, Int.natAbs_natCast]
    rw [← Int.cast_abs, Int.abs_eq_natAbs, hna, Int.cast_natCast]
  let Hperp : Finset (Fin n → Fin d) := HPrefix T d n le_rfl
  let P : ℤ[X] := ∑ r ∈ Hperp, ∏ j : Fin n, Polynomial.Chebyshev.T ℤ ((d : ℤ) - 2 * (r j : ℤ))
  refine ⟨P, ?_⟩
  rw [hd_eq_abs]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  let f : (Fin n → ℤ) → ℂ := fun k => ∏ j : Fin n, (1 : ℂ) / (1 + (k j : ℂ) ^ 2)
  have hcast_lhs : (fun a : Fin n → ℤ =>
      ((∏ j : Fin n, (1 : ℝ) / (1 + ((V.mulVec a j : ℤ) : ℝ) ^ 2) : ℝ) : ℂ)) =
      fun a => f (V.mulVec a) := by
    ext a
    simp only [f, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    push_cast; rfl
  rw [hcast_lhs]
  have h_inj : Function.Injective V.mulVec := mulVec_injective_of_det_ne_zero V hdet
  have h_reindex :
      (∑' a : Fin n → ℤ, f (V.mulVec a)) =
        ∑' k : Fin n → ℤ, if k ∈ Set.range V.mulVec then f k else 0 := by
    rw [← tsum_subtype_eq_of_support_subset (s := Set.range V.mulVec)
      (f := fun k => if k ∈ Set.range V.mulVec then f k else 0)
      (fun k hk => by by_contra h; exact hk (if_neg h))]
    let eRange : (Fin n → ℤ) ≃ Set.range V.mulVec := Equiv.ofInjective V.mulVec h_inj
    rw [← Equiv.tsum_eq eRange]
    congr 1; ext a
    simp [eRange]
  rw [h_reindex]
  have h_range_eq : Set.range V.mulVec = Set.range T.mulVec := (colEquiv_range_mulVec hce).symm
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd_pos)
  have h_ind : ∀ k : Fin n → ℤ,
      (if k ∈ Set.range V.mulVec then f k else 0) =
        ∑ r ∈ Hperp, (1 / (d : ℂ)) *
          (∏ j : Fin n, Complex.exp (2 * Real.pi * Complex.I * ((r j : ℕ) : ℂ) * (k j : ℂ) / (d : ℂ)) /
            (1 + (k j : ℂ) ^ 2)) := by
    intro k
    have hL2 := sum_char_HPrefix T hT_upper hT_pos n le_rfl k
    have hmem_iff : k ∈ Set.range V.mulVec ↔
        ∃ b : Fin n → ℤ, ∀ i : Fin n, ∑ j : Fin n, T i j * b j = k i := by
      rw [h_range_eq]
      constructor
      · rintro ⟨b, hb⟩; exact ⟨b, fun i => by simpa [Matrix.mulVec, dotProduct] using congr_fun hb i⟩
      · rintro ⟨b, hb⟩; exact ⟨b, by ext i; simpa [Matrix.mulVec, dotProduct] using hb i⟩
    have hsum_char :
        (∑ r ∈ Hperp, ∏ j : Fin n,
          Complex.exp (2 * Real.pi * Complex.I * ((r j : ℕ) : ℂ) * (k j : ℂ) / (d : ℂ))) =
        if k ∈ Set.range V.mulVec then (d : ℂ) else 0 := by
      have hprod_exp : ∀ r : Fin n → Fin d,
          (∏ j : Fin n, Complex.exp (2 * Real.pi * Complex.I * ((r j : ℕ) : ℂ) * (k j : ℂ) / (d : ℂ))) =
          Complex.exp (2 * Real.pi * Complex.I * (∑ j : Fin n, ((r j : ℕ) : ℂ) * (k j : ℂ)) / (d : ℂ)) := by
        intro r
        rw [← Complex.exp_sum, Finset.mul_sum, Finset.sum_div]
        congr 1; refine Finset.sum_congr rfl fun j _ => by ring
      simp_rw [hprod_exp]
      simpa only [hmem_iff] using hL2
    have hfactor_r : ∀ r : Fin n → Fin d,
        (1 / (d : ℂ)) * (∏ j : Fin n,
          Complex.exp (2 * Real.pi * Complex.I * ((r j : ℕ) : ℂ) * (k j : ℂ) / (d : ℂ)) /
            (1 + (k j : ℂ) ^ 2)) =
        (1 / (d : ℂ)) * f k *
          (∏ j : Fin n, Complex.exp (2 * Real.pi * Complex.I * ((r j : ℕ) : ℂ) * (k j : ℂ) / (d : ℂ))) := by
      intro r
      simp only [f, div_eq_mul_inv, Finset.prod_mul_distrib, one_mul]
      ring
    simp_rw [hfactor_r, ← Finset.mul_sum, hsum_char]
    split_ifs
    · field_simp [hdC]
    · simp
  simp_rw [h_ind]
  have h1D_norm : ∀ (r : Fin n → Fin d) (j : Fin n),
      Summable (fun m : ℤ =>
        ‖Complex.exp (2 * Real.pi * Complex.I * ((r j : ℕ) : ℂ) * (m : ℂ) / (d : ℂ)) /
          (1 + (m : ℂ) ^ 2)‖) := by
    intro r j
    have heq : (fun m : ℤ =>
        ‖Complex.exp (2 * Real.pi * Complex.I * ((r j : ℕ) : ℂ) * (m : ℂ) / (d : ℂ)) /
          (1 + (m : ℂ) ^ 2)‖) =
        fun m : ℤ => (1 : ℝ) / (1 + (m : ℝ) ^ 2) := by
      ext m
      rw [norm_div]
      have harg : 2 * Real.pi * Complex.I * ((r j : ℕ) : ℂ) * (m : ℂ) / (d : ℂ) =
          (((2 * Real.pi * ((r j : ℕ) : ℝ) * (m : ℝ) / (d : ℝ)) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I]
      have hden : (1 : ℂ) + (m : ℂ) ^ 2 = ((1 + (m : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [hden, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [heq]
    exact summable_one_div_one_add_sq_int
  have h_summ_r : ∀ r ∈ Hperp,
      Summable (fun k : Fin n → ℤ =>
        (1 / (d : ℂ)) * (∏ j : Fin n,
          Complex.exp (2 * Real.pi * Complex.I * ((r j : ℕ) : ℂ) * (k j : ℂ) / (d : ℂ)) /
            (1 + (k j : ℂ) ^ 2))) := by
    intro r _
    have hnorm := (summable_and_tsum_fin_prod n
      (fun j m => Complex.exp (2 * Real.pi * Complex.I * ((r j : ℕ) : ℂ) * (m : ℂ) / (d : ℂ)) /
        (1 + (m : ℂ) ^ 2)) (h1D_norm r)).1
    exact hnorm.of_norm.mul_left _
  rw [Summable.tsum_finsetSum h_summ_r]
  have heval_r : ∀ r ∈ Hperp,
      (∑' k : Fin n → ℤ, (1 / (d : ℂ)) * (∏ j : Fin n,
        Complex.exp (2 * Real.pi * Complex.I * ((r j : ℕ) : ℂ) * (k j : ℂ) / (d : ℂ)) /
          (1 + (k j : ℂ) ^ 2))) =
      ((Real.pi ^ n / (Real.sinh Real.pi ^ n * (d : ℝ)) : ℝ) : ℂ) *
        ((∏ j : Fin n, ((Polynomial.Chebyshev.T ℤ ((d : ℤ) - 2 * (r j : ℤ))).map
          (Int.castRingHom ℝ)).eval (Real.cosh (Real.pi / (d : ℝ))) : ℝ) : ℂ) := by
    intro r _
    rw [tsum_mul_left]
    rw [(summable_and_tsum_fin_prod n
      (fun j m => Complex.exp (2 * Real.pi * Complex.I * ((r j : ℕ) : ℂ) * (m : ℂ) / (d : ℂ)) /
        (1 + (m : ℂ) ^ 2)) (h1D_norm r)).2]
    have h1D_eval : ∀ j : Fin n,
        (∑' m : ℤ, Complex.exp (2 * Real.pi * Complex.I * ((r j : ℕ) : ℂ) * (m : ℂ) / (d : ℂ)) /
          (1 + (m : ℂ) ^ 2)) =
        ((Real.pi / Real.sinh Real.pi : ℝ) : ℂ) *
          ((((Polynomial.Chebyshev.T ℤ ((d : ℤ) - 2 * (r j : ℤ))).map
            (Int.castRingHom ℝ)).eval (Real.cosh (Real.pi / (d : ℝ))) : ℝ) : ℂ) := by
      intro j
      have hx0 : 0 ≤ ((r j : ℕ) : ℝ) / (d : ℝ) := by positivity
      have hx1 : ((r j : ℕ) : ℝ) / (d : ℝ) ≤ 1 := by
        rw [div_le_one (Nat.cast_pos.mpr hd_pos)]
        exact Nat.cast_le.mpr (le_of_lt (r j).2)
      have harg_eq : ∀ m : ℤ,
          2 * Real.pi * Complex.I * ((r j : ℕ) : ℂ) * (m : ℂ) / (d : ℂ) =
          2 * Real.pi * Complex.I * (m : ℂ) * ((((r j : ℕ) : ℝ) / (d : ℝ) : ℝ) : ℂ) := by
        intro m; push_cast; ring
      simp_rw [harg_eq]
      rw [tsum_exp_div_one_add_sq _ hx0 hx1, chebyshev_T_eval_cosh]
      rw [← Complex.ofReal_mul]
      congr 2
      have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd_pos)
      push_cast
      field_simp [hdR]
    simp_rw [h1D_eval, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    rw [div_pow]
    ring
  rw [Finset.sum_congr rfl heval_r, ← Finset.mul_sum]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_mul]
  congr 2
  simp only [P, Polynomial.map_sum, Polynomial.map_prod, Polynomial.eval_finsetSum,
    Polynomial.eval_prod]

end MO484639Proof

theorem OMA.solution : type_of% @OMA.S_mo_484639.main := fun n V hn hdet =>
  MO484639Proof.main_proof n V hn hdet
