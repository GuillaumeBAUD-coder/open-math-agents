import OMAStatements.S_mo_484639

-- Problem: Conjecture closed form of summation over an integer lattice
-- Upstream: formal-conjectures statements/mo-484639.lean:0 (declaration OMA.S_mo_484639.main)
-- Credit: @EmircanEsen (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA_MO484639

open Polynomial BigOperators Complex MeasureTheory

/-! ### Part 1: Chebyshev polynomials evaluated at cosh -/

lemma chebyshev_T_eval_cosh (k : ℕ) (θ : ℝ) :
    ((Polynomial.Chebyshev.T ℤ (k : ℤ)).map (Int.castRingHom ℝ)).eval (Real.cosh θ) =
      Real.cosh ((k : ℝ) * θ) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k with
    | 0 =>
      simp [Polynomial.Chebyshev.T_zero]
    | 1 =>
      simp [Polynomial.Chebyshev.T_one]
    | m + 2 =>
      have hT : Polynomial.Chebyshev.T ℤ ((m + 2 : ℕ) : ℤ) =
          2 * X * Polynomial.Chebyshev.T ℤ ((m + 1 : ℕ) : ℤ) -
            Polynomial.Chebyshev.T ℤ (m : ℤ) := by
        have h := Polynomial.Chebyshev.T_add_two ℤ (m : ℤ)
        push_cast
        exact h
      rw [hT]
      simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_X,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
      rw [ih (m + 1) (by omega), ih m (by omega)]
      have h1 : ((m + 2 : ℕ) : ℝ) * θ = ((m + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
      have h2 : (m : ℝ) * θ = ((m + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
      rw [h1, h2, Real.cosh_add, Real.cosh_sub]
      ring

/-! ### Part 2: 1D Fourier series of cosh(pi * (1 - 2 * t)) -/

lemma summable_inv_one_add_sq_real : Summable (fun m : ℤ => (1 : ℝ) / (1 + (m : ℝ) ^ 2)) := by
  have h0 : Summable (fun m : ℤ => (1 : ℝ) / (m : ℝ) ^ 2) := by
    have hp := Real.summable_one_div_int_pow.mpr (by norm_num : (1 : ℕ) < 2)
    simpa using hp
  let g : ℤ → ℝ := fun m => if m = 0 then 1 else 0
  have hg : Summable g := summable_of_ne_finset_zero (s := {0}) (fun m hm => by
    simp only [Finset.mem_singleton] at hm
    simp [g, hm])
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (h0.add hg)
  by_cases hm : m = 0
  · subst hm
    simp [g]
  · simp only [g, hm, ↓reduceIte, add_zero]
    have hpos : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    exact one_div_le_one_div_of_le hpos (by linarith)

lemma integral_exp_mul_complex_zero_one {a : ℂ} (ha : a ≠ 0) :
    ∫ x in (0 : ℝ)..1, Complex.exp (a * (x : ℂ)) = (Complex.exp a - 1) / a := by
  have h := integral_exp_mul_complex ha (a := (0 : ℝ)) (b := (1 : ℝ))
  simpa using h

lemma fourierCoeff_cosh_aux (m : ℤ) :
    let g : ℝ → ℂ := fun x => ((Real.cosh (Real.pi * (1 - 2 * x)) : ℝ) : ℂ)
    ∫ x in (0 : ℝ)..1, Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) * g x =
      (((Real.sinh Real.pi / Real.pi : ℝ) : ℂ) * (1 / (1 + (m : ℂ) ^ 2))) := by
  intro g
  set a₁ : ℂ := -2 * (Real.pi : ℂ) * (1 + Complex.I * (m : ℂ))
  set a₂ : ℂ := 2 * (Real.pi : ℂ) * (1 - Complex.I * (m : ℂ))
  have ha₁ : a₁ ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [a₁] at hre
  have ha₂ : a₂ ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [a₂] at hre
  have h1m : (1 : ℂ) + Complex.I * (m : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have h2m : (1 : ℂ) - Complex.I * (m : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have hsplit : ∀ x : ℝ,
      Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) * g x =
        (Complex.exp (Real.pi : ℂ) / 2) * Complex.exp (a₁ * (x : ℂ)) +
        (Complex.exp (-(Real.pi : ℂ)) / 2) * Complex.exp (a₂ * (x : ℂ)) := by
    intro x
    simp only [g, Real.cosh_eq, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_exp,
      Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_one]
    have e1 : Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) *
        Complex.exp ((Real.pi : ℂ) * (1 - 2 * (x : ℂ))) =
        Complex.exp (Real.pi : ℂ) * Complex.exp (a₁ * (x : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [a₁]
      ring
    have e2 : Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) *
        Complex.exp (-((Real.pi : ℂ) * (1 - 2 * (x : ℂ)))) =
        Complex.exp (-(Real.pi : ℂ)) * Complex.exp (a₂ * (x : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [a₂]
      ring
    calc Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) *
          ((Complex.exp ((Real.pi : ℂ) * (1 - 2 * (x : ℂ))) +
            Complex.exp (-((Real.pi : ℂ) * (1 - 2 * (x : ℂ))))) / 2)
        = (Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) *
            Complex.exp ((Real.pi : ℂ) * (1 - 2 * (x : ℂ)))) / 2 +
          (Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) *
            Complex.exp (-((Real.pi : ℂ) * (1 - 2 * (x : ℂ))))) / 2 := by ring
      _ = (Complex.exp (Real.pi : ℂ) / 2) * Complex.exp (a₁ * (x : ℂ)) +
          (Complex.exp (-(Real.pi : ℂ)) / 2) * Complex.exp (a₂ * (x : ℂ)) := by
          rw [e1, e2]; ring
  simp_rw [hsplit]
  have hi1 : IntervalIntegrable (fun x : ℝ => (Complex.exp (Real.pi : ℂ) / 2) *
      Complex.exp (a₁ * (x : ℂ))) volume 0 1 :=
    (Continuous.intervalIntegrable (by fun_prop) 0 1)
  have hi2 : IntervalIntegrable (fun x : ℝ => (Complex.exp (-(Real.pi : ℂ)) / 2) *
      Complex.exp (a₂ * (x : ℂ))) volume 0 1 :=
    (Continuous.intervalIntegrable (by fun_prop) 0 1)
  rw [intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_exp_mul_complex_zero_one ha₁, integral_exp_mul_complex_zero_one ha₂]
  have hexp_per_neg : Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (-m)
    convert this using 2
    push_cast; ring
  have hexp1 : Complex.exp a₁ = Complex.exp (-(2 * (Real.pi : ℂ))) := by
    have hEq : a₁ = -(2 * (Real.pi : ℂ)) + (-2 * Real.pi * Complex.I * (m : ℂ)) := by
      simp only [a₁]; ring
    rw [hEq, Complex.exp_add, hexp_per_neg, mul_one]
  have hexp2 : Complex.exp a₂ = Complex.exp (2 * (Real.pi : ℂ)) := by
    have hEq : a₂ = 2 * (Real.pi : ℂ) + (-2 * Real.pi * Complex.I * (m : ℂ)) := by
      simp only [a₂]; ring
    rw [hEq, Complex.exp_add, hexp_per_neg, mul_one]
  rw [hexp1, hexp2]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsq : (1 : ℂ) + (m : ℂ) ^ 2 ≠ 0 := by
    have hcast : (1 : ℂ) + (m : ℂ) ^ 2 = (((1 : ℝ) + (m : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.ofReal_ne_zero]
    positivity
  have hsinh : ((Real.sinh Real.pi : ℝ) : ℂ) =
      (Complex.exp (Real.pi : ℂ) - Complex.exp (-(Real.pi : ℂ))) / 2 := by
    rw [Real.sinh_eq]
    simp [Complex.ofReal_exp]
  have hmul1 : Complex.exp (Real.pi : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ))) =
      Complex.exp (-(Real.pi : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hmul2 : Complex.exp (-(Real.pi : ℂ)) * Complex.exp (2 * (Real.pi : ℂ)) =
      Complex.exp (Real.pi : ℂ) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [Complex.ofReal_div, hsinh]
  have ha₁_def : a₁ = -2 * (Real.pi : ℂ) * (1 + Complex.I * (m : ℂ)) := rfl
  have ha₂_def : a₂ = 2 * (Real.pi : ℂ) * (1 - Complex.I * (m : ℂ)) := rfl
  rw [ha₁_def, ha₂_def]
  field_simp [hpi, h1m, h2m, hsq]
  linear_combination
    (-(1 - Complex.I * (m : ℂ)) * (1 + (m : ℂ) ^ 2)) * hmul1 +
    ((1 + Complex.I * (m : ℂ)) * (1 + (m : ℂ) ^ 2)) * hmul2 +
    (2 * (Complex.exp (Real.pi : ℂ) - Complex.exp (-(Real.pi : ℂ))) * (m : ℂ) ^ 2) * Complex.I_sq

lemma hasSum_fourier_inv_one_add_sq (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    HasSum (fun m : ℤ => (1 / (1 + (m : ℂ) ^ 2)) *
        Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (t : ℂ)))
      (((Real.pi / Real.sinh Real.pi) * Real.cosh (Real.pi * (1 - 2 * t)) : ℝ) : ℂ) := by
  have : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  let g : ℝ → ℂ := fun x => ((Real.cosh (Real.pi * (1 - 2 * x)) : ℝ) : ℂ)
  have hg01 : g 0 = g 1 := by
    simp only [g]
    congr 1
    have : Real.pi * (1 - 2 * (1 : ℝ)) = -(Real.pi * (1 - 2 * (0 : ℝ))) := by ring
    rw [this, Real.cosh_neg]
  have hgcont : Continuous g := by
    unfold g
    fun_prop
  let G : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨AddCircle.liftIco (1 : ℝ) 0 g, AddCircle.liftIco_zero_continuous hg01 hgcont.continuousOn⟩
  have hfc : ∀ m : ℤ, fourierCoeff G m =
      (((Real.sinh Real.pi / Real.pi : ℝ) : ℂ) * (1 / (1 + (m : ℂ) ^ 2))) := by
    intro m
    change fourierCoeff (AddCircle.liftIco (1 : ℝ) 0 g) m = _
    rw [fourierCoeff_eq_intervalIntegral _ m 0]
    simp only [div_one, one_smul, zero_add]
    have hint : (∫ x in (0 : ℝ)..1, fourier (T := (1 : ℝ)) (-m) (x : AddCircle (1 : ℝ)) •
          AddCircle.liftIco (1 : ℝ) 0 g (x : AddCircle (1 : ℝ))) =
        ∫ x in (0 : ℝ)..1, Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) * g x := by
      refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun x hx => ?_
      rw [AddCircle.liftIco_coe_apply (by simp [hx.1.le, hx.2]), smul_eq_mul, fourier_coe_apply]
      congr 2
      simp only [Complex.ofReal_one, div_one]
      push_cast
      ring
    rw [hint]
    exact fourierCoeff_cosh_aux m
  have hsum_fc : Summable (fourierCoeff G) := by
    have hnorm : Summable (fun m : ℤ => ‖(((Real.sinh Real.pi / Real.pi : ℝ) : ℂ) *
        (1 / (1 + (m : ℂ) ^ 2)))‖) := by
      have hreal : ∀ m : ℤ, ‖(((Real.sinh Real.pi / Real.pi : ℝ) : ℂ) *
          (1 / (1 + (m : ℂ) ^ 2)))‖ =
          |Real.sinh Real.pi / Real.pi| * (1 / (1 + (m : ℝ) ^ 2)) := by
        intro m
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, norm_one]
        have : (1 : ℂ) + (m : ℂ) ^ 2 = (((1 : ℝ) + (m : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
        rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      simp_rw [hreal]
      exact summable_inv_one_add_sq_real.mul_left _
    refine Summable.of_norm ?_
    simpa [hfc] using hnorm
  have hpt := has_pointwise_sum_fourier_series_of_summable hsum_fc (t : AddCircle (1 : ℝ))
  have hGt : G (t : AddCircle (1 : ℝ)) = g t := by
    change AddCircle.liftIco (1 : ℝ) 0 g (t : AddCircle (1 : ℝ)) = g t
    rcases lt_or_eq_of_le ht1 with hlt | rfl
    · exact AddCircle.liftIco_coe_apply (by simp [ht0, hlt])
    · have h10 : ((1 : ℝ) : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) := by
        rw [QuotientAddGroup.eq_iff_sub_mem]
        simp
      rw [h10, AddCircle.liftIco_coe_apply (by norm_num), hg01]
  rw [hGt] at hpt
  have hpt' : HasSum (fun m : ℤ => (((Real.sinh Real.pi / Real.pi : ℝ) : ℂ) *
      (1 / (1 + (m : ℂ) ^ 2))) * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (t : ℂ)))
      (g t) := by
    refine hpt.congr_fun fun m => ?_
    rw [hfc m, smul_eq_mul, fourier_coe_apply]
    congr 2
    simp only [Complex.ofReal_one, div_one]
  have hsinh_ne : Real.sinh Real.pi ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr Real.pi_pos)
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hmul := hpt'.mul_left (((Real.pi / Real.sinh Real.pi : ℝ) : ℂ))
  have hrhs : (((Real.pi / Real.sinh Real.pi : ℝ) : ℂ) * g t) =
      (((Real.pi / Real.sinh Real.pi) * Real.cosh (Real.pi * (1 - 2 * t)) : ℝ) : ℂ) := by
    simp [g, Complex.ofReal_mul]
  rw [← hrhs]
  refine hmul.congr_fun fun m => ?_
  have hcancel : (((Real.pi / Real.sinh Real.pi : ℝ) : ℂ) *
      ((Real.sinh Real.pi / Real.pi : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul]
    norm_cast
    field_simp [hsinh_ne, hpi_ne]
  symm
  calc (((Real.pi / Real.sinh Real.pi : ℝ) : ℂ) *
        ((((Real.sinh Real.pi / Real.pi : ℝ) : ℂ) * (1 / (1 + (m : ℂ) ^ 2))) *
          Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (t : ℂ))))
      = ((((Real.pi / Real.sinh Real.pi : ℝ) : ℂ) * ((Real.sinh Real.pi / Real.pi : ℝ) : ℂ)) *
          ((1 / (1 + (m : ℂ) ^ 2)) *
            Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (t : ℂ)))) := by ring
    _ = (1 / (1 + (m : ℂ) ^ 2)) *
          Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (t : ℂ)) := by rw [hcancel, one_mul]

/-! ### Part 3: Product of 1D Fourier series over Fin n -> Z -/

lemma summable_norm_fourier_term (t : ℝ) :
    Summable (fun m : ℤ => ‖(1 / (1 + (m : ℂ) ^ 2)) *
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (t : ℂ))‖) := by
  have h : ∀ m : ℤ, ‖(1 / (1 + (m : ℂ) ^ 2)) *
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (t : ℂ))‖ =
      1 / (1 + (m : ℝ) ^ 2) := by
    intro m
    rw [norm_mul, norm_div, norm_one]
    have h1 : (1 : ℂ) + (m : ℂ) ^ 2 = (((1 : ℝ) + (m : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    have h2 : 2 * Real.pi * Complex.I * (m : ℂ) * (t : ℂ) =
        (((2 * Real.pi * (m : ℝ) * t : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      h2, Complex.norm_exp_ofReal_mul_I, mul_one]
  simp_rw [h]
  exact summable_inv_one_add_sq_real

lemma hasSum_pi_prod_of_hasSum_norm {n : ℕ} (f : Fin n → ℤ → ℂ) (L : Fin n → ℂ)
    (hsum : ∀ j, HasSum (f j) (L j)) (hnorm : ∀ j, Summable (fun m => ‖f j m‖)) :
    HasSum (fun k : Fin n → ℤ => ∏ j : Fin n, f j (k j)) (∏ j : Fin n, L j) ∧
    Summable (fun k : Fin n → ℤ => ‖∏ j : Fin n, f j (k j)‖) := by
  induction n with
  | zero =>
    constructor
    · simp only [Finset.univ_eq_empty, Finset.prod_empty]
      exact hasSum_unique _
    · simp only [Finset.univ_eq_empty, Finset.prod_empty, norm_one]
      exact (hasSum_unique _).summable
  | succ n ih =>
    let g : (Fin n → ℤ) → ℂ := fun k => ∏ j : Fin n, f j.succ (k j)
    have htail := ih (fun j => f j.succ) (fun j => L j.succ)
      (fun j => hsum j.succ) (fun j => hnorm j.succ)
    have hprod_norm : Summable (fun p : ℤ × (Fin n → ℤ) => ‖f 0 p.1‖ * ‖g p.2‖) :=
      (hnorm 0).mul_of_nonneg htail.2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    have hsm : Summable (fun p : ℤ × (Fin n → ℤ) => f 0 p.1 * g p.2) := by
      refine Summable.of_norm ?_
      simpa [norm_mul] using hprod_norm
    have hprod_sum : HasSum (fun p : ℤ × (Fin n → ℤ) => f 0 p.1 * g p.2)
        (L 0 * ∏ j : Fin n, L j.succ) := by
      have hts : (∑' p : ℤ × (Fin n → ℤ), f 0 p.1 * g p.2) = L 0 * ∏ j : Fin n, L j.succ := by
        rw [hsm.tsum_prod' (fun b => htail.1.summable.mul_left (f 0 b))]
        simp_rw [tsum_mul_left, g, htail.1.tsum_eq, tsum_mul_right, (hsum 0).tsum_eq]
      rw [← hts]
      exact hsm.hasSum
    let e : (ℤ × (Fin n → ℤ)) ≃ (Fin (n + 1) → ℤ) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun k => (k 0, fun j => k j.succ)
        left_inv := fun ⟨a, g⟩ => by ext <;> simp
        right_inv := fun k => by ext i; refine Fin.cases ?_ ?_ i <;> simp }
    constructor
    · rw [Fin.prod_univ_succ]
      rw [← e.hasSum_iff]
      refine hprod_sum.congr_fun fun p => ?_
      simp [e, g, Fin.prod_univ_succ]
    · rw [← e.summable_iff]
      refine hprod_norm.congr fun p => ?_
      simp [e, g, Fin.prod_univ_succ]

/-! ### Part 4: Finite abelian group duality and lattice index -/

lemma zmod_hom_card_and_sep {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (hmd : m ∣ d) :
    Nat.card (ZMod m →+ ZMod d) = m ∧
    (∀ y : ZMod m, y ≠ 0 → ∃ f : ZMod m →+ ZMod d, f y ≠ 0) := by
  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero d := ⟨hd.ne'⟩
  set q := d / m
  have hmq : m * q = d := Nat.mul_div_cancel' hmd
  have hqpos : 0 < q := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hmq; omega)
  let baseHom : ZMod m → (ℤ →+ ZMod d) := fun a =>
    { toFun := fun k => (k : ZMod d) * ((q : ZMod d) * (a.val : ZMod d))
      map_zero' := by simp
      map_add' := fun x y => by push_cast; ring }
  let mkHom : ZMod m → (ZMod m →+ ZMod d) := fun a =>
    ZMod.lift m ⟨baseHom a, by
      show ((m : ℤ) : ZMod d) * ((q : ZMod d) * (a.val : ZMod d)) = 0
      have hmul : ((m : ℤ) : ZMod d) * (q : ZMod d) = ((m * q : ℕ) : ZMod d) := by
        push_cast; rfl
      rw [← mul_assoc, hmul, hmq, ZMod.natCast_self, zero_mul]⟩
  have hmk_one : ∀ a : ZMod m, mkHom a 1 = (q : ZMod d) * (a.val : ZMod d) := by
    intro a
    have h1 : (1 : ZMod m) = ((1 : ℤ) : ZMod m) := by simp
    rw [h1]
    dsimp only [mkHom]
    rw [ZMod.lift_coe]
    simp [baseHom]
  have hmk_apply : ∀ (a y : ZMod m),
      mkHom a y = (y.val : ZMod d) * ((q : ZMod d) * (a.val : ZMod d)) := by
    intro a y
    have hy : y = y.val • (1 : ZMod m) := by simp
    conv_lhs => rw [hy]
    rw [map_nsmul, hmk_one, nsmul_eq_mul]
  have hmk_inj : Function.Injective mkHom := by
    intro a b hab
    have h1 : mkHom a 1 = mkHom b 1 := by rw [hab]
    rw [hmk_one, hmk_one] at h1
    have hva : q * a.val < d := by
      have := a.val_lt
      nlinarith
    have hvb : q * b.val < d := by
      have := b.val_lt
      nlinarith
    have hval := congrArg ZMod.val h1
    rw [← Nat.cast_mul, ← Nat.cast_mul, ZMod.val_natCast_of_lt hva,
      ZMod.val_natCast_of_lt hvb] at hval
    have heq : a.val = b.val := Nat.eq_of_mul_eq_mul_left hqpos hval
    exact ZMod.val_injective m heq
  have hmk_surj : Function.Surjective mkHom := by
    intro f
    have hmf : m • f 1 = 0 := by
      rw [← map_nsmul]
      have h0 : m • (1 : ZMod m) = 0 := by simp [nsmul_eq_mul]
      rw [h0, map_zero]
    have hdvd : d ∣ m * (f 1).val := by
      have h0 : ((m * (f 1).val : ℕ) : ZMod d) = 0 := by
        simpa [nsmul_eq_mul, ZMod.natCast_zmod_val] using hmf
      exact (ZMod.natCast_eq_zero_iff _ _).mp h0
    have hqdvd : q ∣ (f 1).val := by
      have hdvd' : m * q ∣ m * (f 1).val := hmq.symm ▸ hdvd
      exact (Nat.mul_dvd_mul_iff_left hm).mp hdvd'
    rcases hqdvd with ⟨c, hc⟩
    have hclt : c < m := by
      have hlt : (f 1).val < d := (f 1).val_lt
      rw [hc, ← hmq] at hlt
      nlinarith
    refine ⟨(c : ZMod m), ?_⟩
    apply AddMonoidHom.ext
    intro x
    have hx : x = x.val • (1 : ZMod m) := by simp
    rw [hx, map_nsmul, map_nsmul, hmk_one, ZMod.val_natCast_of_lt hclt]
    congr 1
    rw [← Nat.cast_mul, ← hc, ZMod.natCast_zmod_val]
  constructor
  · have heq := Equiv.ofBijective mkHom ⟨hmk_inj, hmk_surj⟩
    rw [← Nat.card_congr heq, Nat.card_zmod]
  · intro y hy
    refine ⟨mkHom 1, ?_⟩
    rw [hmk_apply]
    intro h0
    by_cases hm1 : m = 1
    · subst hm1
      exact hy (Subsingleton.elim y 0)
    · have : Fact (1 < m) := ⟨by omega⟩
      have h1 : (1 : ZMod m).val = 1 := ZMod.val_one m
      rw [h1, Nat.cast_one, mul_one, ← Nat.cast_mul] at h0
      have hlt : y.val * q < d := by
        have := y.val_lt
        nlinarith
      have hv := congrArg ZMod.val h0
      rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hv
      have hy0 : y.val = 0 := by
        rcases mul_eq_zero.mp hv with h | h
        · exact h
        · omega
      exact hy ((ZMod.val_eq_zero y).mp hy0)

lemma finite_ab_hom_card_and_sep {Q : Type*} [AddCommGroup Q] [Finite Q]
    {d : ℕ} (hd : 0 < d) (hcard : Nat.card Q = d) :
    Nat.card (Q →+ ZMod d) = d ∧
    (∀ q : Q, q ≠ 0 → ∃ ψ : Q →+ ZMod d, ψ q ≠ 0) := by
  obtain ⟨ι, hfin, m, hm_gt, ⟨e_ds⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' Q
  have : Fintype ι := hfin
  let : DecidableEq ι := Classical.decEq ι
  let e : Q ≃+ ((i : ι) → ZMod (m i)) := e_ds.trans (DirectSum.addEquivProd _)
  have hm_pos : ∀ i, 0 < m i := fun i => by linarith [hm_gt i]
  have : ∀ i, NeZero (m i) := fun i => ⟨(hm_pos i).ne'⟩
  have hprod : ∏ i : ι, m i = d := by
    rw [← hcard, Nat.card_congr e.toEquiv, Nat.card_pi]
    simp
  have hdvd : ∀ i : ι, m i ∣ d := fun i => by
    rw [← hprod]
    exact Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  let homEquiv : (Q →+ ZMod d) ≃ ((i : ι) → (ZMod (m i) →+ ZMod d)) :=
    { toFun := fun ψ i =>
        ψ.comp (e.symm.toAddMonoidHom.comp (AddMonoidHom.single (fun j => ZMod (m j)) i))
      invFun := fun f =>
        { toFun := fun q => ∑ i : ι, f i (e q i)
          map_zero' := by simp
          map_add' := fun x y => by simp [Finset.sum_add_distrib] }
      left_inv := fun ψ => by
        apply AddMonoidHom.ext
        intro q
        have hq : e q = ∑ i : ι, Pi.single i (e q i) := by
          ext j; simp [Finset.sum_apply]
        change ∑ i : ι, ψ (e.symm (Pi.single i (e q i))) = ψ q
        calc ∑ i : ι, ψ (e.symm (Pi.single i (e q i)))
            = ψ (e.symm (∑ i : ι, Pi.single i (e q i))) := by
              rw [map_sum, map_sum]
          _ = ψ (e.symm (e q)) := by rw [← hq]
          _ = ψ q := by simp
      right_inv := fun f => by
        funext i
        apply AddMonoidHom.ext
        intro x
        change ∑ j : ι, f j (e (e.symm (Pi.single i x)) j) = f i x
        simp only [AddEquiv.apply_symm_apply]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          rw [Pi.single_eq_of_ne hji, map_zero]
        · intro hi
          exact absurd (Finset.mem_univ i) hi }
  constructor
  · rw [Nat.card_congr homEquiv, Nat.card_pi]
    calc ∏ i : ι, Nat.card (ZMod (m i) →+ ZMod d)
        = ∏ i : ι, m i := Finset.prod_congr rfl (fun i _ => (zmod_hom_card_and_sep (hm_pos i) hd (hdvd i)).1)
      _ = d := hprod
  · intro q hq
    have heq0 : e q ≠ 0 := fun h => hq (e.injective (by simpa using h))
    have hex : ∃ i : ι, e q i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact heq0 (funext hall)
    rcases hex with ⟨i, hi⟩
    obtain ⟨fi, hfi⟩ := (zmod_hom_card_and_sep (hm_pos i) hd (hdvd i)).2 (e q i) hi
    refine ⟨fi.comp ((Pi.evalAddMonoidHom (fun j => ZMod (m j)) i).comp e.toAddMonoidHom), ?_⟩
    simpa using hfi

lemma mulVec_injective_of_det_ne_zero {n : ℕ} (V : Matrix (Fin n) (Fin n) ℤ) (hdet : V.det ≠ 0) :
    Function.Injective V.mulVec := by
  intro a b hab
  have h1 : V.adjugate.mulVec (V.mulVec a) = V.adjugate.mulVec (V.mulVec b) := by rw [hab]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at h1
  ext i
  have hi := congrFun h1 i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact mul_left_cancel₀ hdet hi

lemma lattice_index_eq_natAbs_det {n : ℕ} (V : Matrix (Fin n) (Fin n) ℤ) (hdet : V.det ≠ 0) :
    (LinearMap.range V.mulVecLin).toAddSubgroup.index = V.det.natAbs := by
  let S : Submodule ℤ (Fin n → ℤ) := LinearMap.range V.mulVecLin
  have hinj : Function.Injective V.mulVecLin := mulVec_injective_of_det_ne_zero V hdet
  let eS : (Fin n → ℤ) ≃ₗ[ℤ] S := LinearEquiv.ofInjective V.mulVecLin hinj
  let bS : Module.Basis (Fin n) ℤ S := (Pi.basisFun ℤ (Fin n)).map eS
  have hchange := Submodule.natAbs_det_basis_change (Pi.basisFun ℤ (Fin n)) S bS
  have hdet_eq : (Pi.basisFun ℤ (Fin n)).det (Subtype.val ∘ ⇑bS) = V.det := by
    rw [Pi.basisFun_det_apply]
    have hmat : Matrix.of (Subtype.val ∘ ⇑bS) = V.transpose := by
      ext j i
      rw [Matrix.of_apply, Function.comp_apply, Matrix.transpose_apply]
      dsimp only [bS]
      rw [Module.Basis.map_apply]
      change V.mulVec (Pi.basisFun ℤ (Fin n) j) i = V i j
      simp [Pi.basisFun_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hmat, Matrix.det_transpose]
  change Nat.card ((Fin n → ℤ) ⧸ S) = V.det.natAbs
  rw [← hchange]
  exact congrArg Int.natAbs hdet_eq

open Classical in
lemma char_orthogonality {n d : ℕ} [NeZero d] (V : Matrix (Fin n) (Fin n) ℤ)
    (hdet : V.det ≠ 0) (hd_eq : d = V.det.natAbs) :
    let H : Finset (Fin n → ZMod d) :=
      Finset.univ.filter (fun r => ∀ j : Fin n, ∑ i : Fin n, r i * (V i j : ZMod d) = 0)
    H.card = d ∧
    ∀ k : Fin n → ℤ,
      (∑ r ∈ H, ∏ j : Fin n,
        Complex.exp (2 * Real.pi * Complex.I * (k j : ℂ) * (((r j).val : ℂ) / (d : ℂ)))) =
      if k ∈ Set.range V.mulVec then (d : ℂ) else 0 := by
  intro H
  have hd : 0 < d := by rw [hd_eq]; exact Int.natAbs_pos.mpr hdet
  let L : AddSubgroup (Fin n → ℤ) := (LinearMap.range V.mulVecLin).toAddSubgroup
  let Q := (Fin n → ℤ) ⧸ L
  have hidx : L.index = d := by rw [hd_eq]; exact lattice_index_eq_natAbs_det V hdet
  have hQcard : Nat.card Q = d := by
    simpa [Q, AddSubgroup.index] using hidx
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQcard]; omega)
  have hmemL : ∀ k : Fin n → ℤ, k ∈ L ↔ k ∈ Set.range V.mulVec := fun _ => Iff.rfl
  let evalH : (Fin n → ZMod d) → ((Fin n → ℤ) →+ ZMod d) := fun r =>
    { toFun := fun k => ∑ i : Fin n, r i * (k i : ZMod d)
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib] }
  have heval_zero_on_L : ∀ r ∈ H, L ≤ (evalH r).ker := by
    intro r hr k hk
    change evalH r k = 0
    rw [hmemL] at hk
    rcases hk with ⟨a, rfl⟩
    have hr' : ∀ j : Fin n, ∑ i : Fin n, r i * (V i j : ZMod d) = 0 :=
      (Finset.mem_filter.mp hr).2
    simp only [evalH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct]
    push_cast
    calc ∑ i : Fin n, r i * ∑ j : Fin n, (V i j : ZMod d) * (a j : ZMod d)
        = ∑ i : Fin n, ∑ j : Fin n, r i * (V i j : ZMod d) * (a j : ZMod d) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j : Fin n, (∑ i : Fin n, r i * (V i j : ZMod d)) * (a j : ZMod d) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
      _ = 0 := by simp [hr']
  have hmemH : ∀ ψ : Q →+ ZMod d,
      (fun i => ψ (QuotientAddGroup.mk (Pi.single i 1))) ∈ H := by
    intro ψ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun j => ?_⟩
    have hsum_eq : ∑ i : Fin n, ψ (QuotientAddGroup.mk (Pi.single i 1)) * (V i j : ZMod d) =
        ψ (QuotientAddGroup.mk (V.mulVec (Pi.single j 1))) := by
      have hvec : V.mulVec (Pi.single j 1) = ∑ i : Fin n, V i j • Pi.single i (1 : ℤ) := by
        ext i
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply]
      rw [hvec, QuotientAddGroup.mk_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [QuotientAddGroup.mk_zsmul, map_zsmul, zsmul_eq_mul, mul_comm]
    rw [hsum_eq]
    have hmem : V.mulVec (Pi.single j 1) ∈ L := ⟨Pi.single j 1, rfl⟩
    rw [(QuotientAddGroup.eq_zero_iff _).mpr hmem, map_zero]
  let eH : {r : Fin n → ZMod d // r ∈ H} ≃ (Q →+ ZMod d) :=
    { toFun := fun r => QuotientAddGroup.lift L (evalH r.1) (heval_zero_on_L r.1 r.2)
      invFun := fun ψ => ⟨fun i => ψ (QuotientAddGroup.mk (Pi.single i 1)), hmemH ψ⟩
      left_inv := fun r => by
        apply Subtype.ext
        funext i
        change QuotientAddGroup.lift L (evalH r.1) (heval_zero_on_L r.1 r.2)
          (QuotientAddGroup.mk (Pi.single i 1)) = r.1 i
        rw [QuotientAddGroup.lift_mk]
        simp only [evalH, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          rw [Pi.single_eq_of_ne hji]
          simp
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      right_inv := fun ψ => by
        apply AddMonoidHom.ext
        intro q
        induction q using QuotientAddGroup.induction_on with
        | H k =>
          have hk : k = ∑ i : Fin n, k i • Pi.single i (1 : ℤ) := by
            ext j; simp [Finset.sum_apply, Pi.single_apply]
          conv_rhs => rw [hk, QuotientAddGroup.mk_sum, map_sum]
          change QuotientAddGroup.lift L (evalH (fun i => ψ (QuotientAddGroup.mk (Pi.single i 1))))
            (heval_zero_on_L _ (hmemH ψ)) (QuotientAddGroup.mk k) = _
          rw [QuotientAddGroup.lift_mk]
          simp only [evalH, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [QuotientAddGroup.mk_zsmul, map_zsmul, zsmul_eq_mul, mul_comm] }
  have hQ_res := finite_ab_hom_card_and_sep hd hQcard
  have hHcard : H.card = d := by
    have h1 : Nat.card {r : Fin n → ZMod d // r ∈ H} = H.card := by
      simp [Nat.card_eq_fintype_card]
    rw [← h1, Nat.card_congr eH, hQ_res.1]
  refine ⟨hHcard, fun k => ?_⟩
  have hprod_eq : ∀ r : Fin n → ZMod d,
      (∏ j : Fin n,
        Complex.exp (2 * Real.pi * Complex.I * (k j : ℂ) * (((r j).val : ℂ) / (d : ℂ)))) =
      Complex.exp (2 * Real.pi * Complex.I * (((evalH r k).val : ℂ) / (d : ℂ))) := by
    intro r
    rw [← Complex.exp_sum]
    have hmod : (∑ j : Fin n, k j * ((r j).val : ℤ)) ≡ ((evalH r k).val : ℤ) [ZMOD (d : ℤ)] := by
      rw [← ZMod.intCast_eq_intCast_iff]
      simp only [evalH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Int.cast_sum, Int.cast_mul,
        Int.cast_natCast, ZMod.natCast_zmod_val]
      refine Finset.sum_congr rfl fun j _ => mul_comm _ _
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hmod.symm
    have hsum_cast : (∑ j : Fin n, (k j : ℂ) * ((r j).val : ℂ)) =
        ((evalH r k).val : ℂ) + (d : ℂ) * (t : ℂ) := by
      have : (∑ j : Fin n, k j * ((r j).val : ℤ)) = ((evalH r k).val : ℤ) + (d : ℤ) * t := by
        linarith
      exact_mod_cast this
    have hexp_arg : (∑ j : Fin n, 2 * Real.pi * Complex.I * (k j : ℂ) *
          (((r j).val : ℂ) / (d : ℂ))) =
        2 * Real.pi * Complex.I * (((evalH r k).val : ℂ) / (d : ℂ)) +
        (t : ℂ) * (2 * Real.pi * Complex.I) := by
      have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
      have hfactor : (∑ j : Fin n, 2 * Real.pi * Complex.I * (k j : ℂ) *
            (((r j).val : ℂ) / (d : ℂ))) =
          (2 * Real.pi * Complex.I / (d : ℂ)) * (∑ j : Fin n, (k j : ℂ) * ((r j).val : ℂ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hfactor, hsum_cast]
      field_simp [hdC]
    rw [hexp_arg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp_rw [hprod_eq]
  split_ifs with hk
  · have hsum_one : ∑ r ∈ H, Complex.exp (2 * Real.pi * Complex.I *
        (((evalH r k).val : ℂ) / (d : ℂ))) = ∑ _r ∈ H, (1 : ℂ) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have h0 : evalH r k = 0 := heval_zero_on_L r hr ((hmemL k).mpr hk)
      rw [h0]
      simp
    rw [hsum_one, Finset.sum_const, nsmul_eq_mul, mul_one, hHcard]
  · have hqne : (QuotientAddGroup.mk k : Q) ≠ 0 := by
      intro h0
      exact hk ((hmemL k).mp ((QuotientAddGroup.eq_zero_iff k).mp h0))
    obtain ⟨ψ, hψ⟩ := hQ_res.2 (QuotientAddGroup.mk k) hqne
    let r0 := (eH.symm ψ).1
    have hr0 : r0 ∈ H := (eH.symm ψ).2
    have hev0 : evalH r0 k ≠ 0 := by
      have hlift : eH (eH.symm ψ) (QuotientAddGroup.mk k) = ψ (QuotientAddGroup.mk k) := by simp
      simpa [eH, r0] using hlift.symm ▸ hψ
    have hchi0 : Complex.exp (2 * Real.pi * Complex.I * (((evalH r0 k).val : ℂ) / (d : ℂ))) ≠ 1 := by
      rw [ne_eq, Complex.exp_eq_one_iff]
      rintro ⟨m, hm⟩
      have hpiI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hdiv : (((evalH r0 k).val : ℂ) / (d : ℂ)) = (m : ℂ) := by
        apply mul_left_cancel₀ hpiI
        linear_combination hm
      have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
      have hmul : ((evalH r0 k).val : ℂ) = (m : ℂ) * (d : ℂ) := (div_eq_iff hdC).mp hdiv
      have hre := congrArg Complex.re hmul
      simp only [Complex.natCast_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
        Complex.natCast_im, mul_zero, sub_zero] at hre
      have hZ : ((evalH r0 k).val : ℤ) = m * (d : ℤ) := by exact_mod_cast hre
      have hval_lt : (evalH r0 k).val < d := (evalH r0 k).val_lt
      have hval_pos : 0 < (evalH r0 k).val :=
        Nat.pos_of_ne_zero (fun h => hev0 ((ZMod.val_eq_zero _).mp h))
      have hm1 : 0 < m := by nlinarith
      nlinarith
    have hHadd : ∀ r ∈ H, r + r0 ∈ H := by
      intro r hr
      rw [Finset.mem_filter] at hr hr0 ⊢
      refine ⟨Finset.mem_univ _, fun j => ?_⟩
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hr.2 j, hr0.2 j, add_zero]
    have hHsub : ∀ r ∈ H, r - r0 ∈ H := by
      intro r hr
      rw [Finset.mem_filter] at hr hr0 ⊢
      refine ⟨Finset.mem_univ _, fun j => ?_⟩
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hr.2 j, hr0.2 j, sub_zero]
    have hchi_add : ∀ r : Fin n → ZMod d,
        Complex.exp (2 * Real.pi * Complex.I * (((evalH r0 k).val : ℂ) / (d : ℂ))) *
        Complex.exp (2 * Real.pi * Complex.I * (((evalH r k).val : ℂ) / (d : ℂ))) =
        Complex.exp (2 * Real.pi * Complex.I * (((evalH (r + r0) k).val : ℂ) / (d : ℂ))) := by
      intro r
      rw [← hprod_eq r0, ← hprod_eq r, ← hprod_eq (r + r0), ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← Complex.exp_add]
      have hmod : (((r0 j).val + (r j).val : ℕ) : ℤ) ≡ (((r + r0) j).val : ℤ) [ZMOD (d : ℤ)] := by
        rw [← ZMod.intCast_eq_intCast_iff]
        simp [add_comm]
      obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hmod.symm
      have hcast : ((r0 j).val : ℂ) + ((r j).val : ℂ) =
          (((r + r0) j).val : ℂ) + (d : ℂ) * (t : ℂ) := by
        have : ((r0 j).val : ℤ) + ((r j).val : ℤ) =
            (((r + r0) j).val : ℤ) + (d : ℤ) * t := by
          push_cast at ht; linarith
        exact_mod_cast this
      have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
      have harg : 2 * Real.pi * Complex.I * (k j : ℂ) * (((r0 j).val : ℂ) / (d : ℂ)) +
          2 * Real.pi * Complex.I * (k j : ℂ) * (((r j).val : ℂ) / (d : ℂ)) =
          2 * Real.pi * Complex.I * (k j : ℂ) * ((((r + r0) j).val : ℂ) / (d : ℂ)) +
          ((k j * t : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        have h1 : 2 * Real.pi * Complex.I * (k j : ℂ) * (((r0 j).val : ℂ) / (d : ℂ)) +
            2 * Real.pi * Complex.I * (k j : ℂ) * (((r j).val : ℂ) / (d : ℂ)) =
            (2 * Real.pi * Complex.I * (k j : ℂ) / (d : ℂ)) *
              (((r0 j).val : ℂ) + ((r j).val : ℂ)) := by ring
        rw [h1, hcast]
        push_cast
        field_simp [hdC]
      rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    set Ssum := ∑ r ∈ H, Complex.exp (2 * Real.pi * Complex.I *
      (((evalH r k).val : ℂ) / (d : ℂ)))
    have hshift : Complex.exp (2 * Real.pi * Complex.I *
        (((evalH r0 k).val : ℂ) / (d : ℂ))) * Ssum = Ssum := by
      rw [Finset.mul_sum]
      simp_rw [hchi_add]
      refine Finset.sum_bij (fun r _ => r + r0) (fun r hr => hHadd r hr)
        (fun a _ b _ hab => add_right_cancel hab)
        (fun r hr => ⟨r - r0, hHsub r hr, sub_add_cancel r r0⟩)
        (fun _ _ => rfl)
    have hmul0 : (Complex.exp (2 * Real.pi * Complex.I *
        (((evalH r0 k).val : ℂ) / (d : ℂ))) - 1) * Ssum = 0 := by
      linear_combination hshift
    exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr hchi0)

end OMA_MO484639

open Classical in
theorem OMA.solution : type_of% @OMA.S_mo_484639.main := by
  intro n V _hn hdet
  open Polynomial BigOperators Complex in
  set d : ℕ := V.det.natAbs
  have hd : 0 < d := Int.natAbs_pos.mpr hdet
  have : NeZero d := ⟨hd.ne'⟩
  set H : Finset (Fin n → ZMod d) :=
    Finset.univ.filter (fun r => ∀ j : Fin n, ∑ i : Fin n, r i * (V i j : ZMod d) = 0)
  let P : ℤ[X] := ∑ r ∈ H, ∏ j : Fin n,
    Polynomial.Chebyshev.T ℤ (((d : ℤ) - 2 * ((r j).val : ℤ)).natAbs : ℤ)
  refine ⟨P, ?_⟩
  have horth := OMA_MO484639.char_orthogonality (d := d) V hdet rfl
  have h1d : ∀ r ∈ H,
      HasSum (fun k : Fin n → ℤ =>
        ∏ j : Fin n, ((1 / (1 + (k j : ℂ) ^ 2)) *
          Complex.exp (2 * Real.pi * Complex.I * (k j : ℂ) * (((r j).val : ℂ) / (d : ℂ)))))
        (∏ j : Fin n, (((Real.pi / Real.sinh Real.pi) *
          Real.cosh (Real.pi * (1 - 2 * (((r j).val : ℝ) / (d : ℝ)))) : ℝ) : ℂ)) := by
    intro r _
    refine (OMA_MO484639.hasSum_pi_prod_of_hasSum_norm
      (fun j m => (1 / (1 + (m : ℂ) ^ 2)) *
        Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (((r j).val : ℂ) / (d : ℂ))))
      (fun j => (((Real.pi / Real.sinh Real.pi) *
        Real.cosh (Real.pi * (1 - 2 * (((r j).val : ℝ) / (d : ℝ)))) : ℝ) : ℂ))
      (fun j => by
        have ht0 : (0 : ℝ) ≤ ((r j).val : ℝ) / (d : ℝ) := by positivity
        have ht1 : ((r j).val : ℝ) / (d : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact_mod_cast le_of_lt (r j).val_lt
        have hs := OMA_MO484639.hasSum_fourier_inv_one_add_sq (((r j).val : ℝ) / (d : ℝ)) ht0 ht1
        simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using hs)
      (fun j => by
        have hs := OMA_MO484639.summable_norm_fourier_term (((r j).val : ℝ) / (d : ℝ))
        simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using hs)).1
  have hsum_all := hasSum_sum h1d
  have hsum_lhs : HasSum
      (fun k : Fin n → ℤ =>
        if k ∈ Set.range V.mulVec then
          (d : ℂ) * ∏ j : Fin n, (1 / (1 + (k j : ℂ) ^ 2))
        else 0)
      (∑ r ∈ H, ∏ j : Fin n, (((Real.pi / Real.sinh Real.pi) *
        Real.cosh (Real.pi * (1 - 2 * (((r j).val : ℝ) / (d : ℝ)))) : ℝ) : ℂ)) := by
    refine hsum_all.congr_fun fun k => ?_
    have hfactor : ∀ r ∈ H,
        (∏ j : Fin n, ((1 / (1 + (k j : ℂ) ^ 2)) *
          Complex.exp (2 * Real.pi * Complex.I * (k j : ℂ) * (((r j).val : ℂ) / (d : ℂ))))) =
        (∏ j : Fin n, (1 / (1 + (k j : ℂ) ^ 2))) *
        (∏ j : Fin n,
          Complex.exp (2 * Real.pi * Complex.I * (k j : ℂ) * (((r j).val : ℂ) / (d : ℂ)))) :=
      fun _ _ => Finset.prod_mul_distrib
    rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum, horth.2 k]
    split_ifs <;> ring
  have htsum_eq : (∑' k : Fin n → ℤ,
      if k ∈ Set.range V.mulVec then
        (d : ℂ) * ∏ j : Fin n, (1 / (1 + (k j : ℂ) ^ 2))
      else 0) =
      (d : ℂ) * (OMA.S_mo_484639.S V : ℂ) := by
    have hinj := OMA_MO484639.mulVec_injective_of_det_ne_zero V hdet
    have hrange := tsum_range (f := fun k : Fin n → ℤ =>
      (d : ℂ) * ∏ j : Fin n, (1 / (1 + (k j : ℂ) ^ 2))) hinj
    have hcast : (OMA.S_mo_484639.S V : ℂ) =
        ∑' a : Fin n → ℤ, ∏ j : Fin n, (1 / (1 + ((V.mulVec a j : ℤ) : ℂ) ^ 2)) := by
      unfold OMA.S_mo_484639.S
      rw [Complex.ofReal_tsum]
      congr 1; ext a
      simp
    rw [hcast, ← tsum_mul_left, ← hrange]
    rw [tsum_subtype (Set.range V.mulVec) (fun k : Fin n → ℤ =>
      (d : ℂ) * ∏ j : Fin n, (1 / (1 + (k j : ℂ) ^ 2)))]
    rfl
  have hmainC : (d : ℂ) * (OMA.S_mo_484639.S V : ℂ) =
      ∑ r ∈ H, ∏ j : Fin n, (((Real.pi / Real.sinh Real.pi) *
        Real.cosh (Real.pi * (1 - 2 * (((r j).val : ℝ) / (d : ℝ)))) : ℝ) : ℂ) := by
    rw [← htsum_eq]
    exact hsum_lhs.tsum_eq
  have hP_eval : (∑ r ∈ H, ∏ j : Fin n, (((Real.pi / Real.sinh Real.pi) *
        Real.cosh (Real.pi * (1 - 2 * (((r j).val : ℝ) / (d : ℝ)))) : ℝ) : ℂ)) =
      (((Real.pi ^ n / Real.sinh Real.pi ^ n) *
        (P.map (Int.castRingHom ℝ)).eval (Real.cosh (Real.pi / (d : ℝ))) : ℝ) : ℂ) := by
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    have hevalR : (P.map (Int.castRingHom ℝ)).eval (Real.cosh (Real.pi / (d : ℝ))) =
        ∑ r ∈ H, ∏ j : Fin n, Real.cosh (Real.pi * (1 - 2 * (((r j).val : ℝ) / (d : ℝ)))) := by
      change (Polynomial.evalRingHom (Real.cosh (Real.pi / (d : ℝ)))) (P.map (Int.castRingHom ℝ)) = _
      simp only [P, Polynomial.map_sum, Polynomial.map_prod, map_sum, map_prod]
      refine Finset.sum_congr rfl fun r _ => Finset.prod_congr rfl fun j _ => ?_
      change ((Polynomial.Chebyshev.T ℤ (((d : ℤ) - 2 * ((r j).val : ℤ)).natAbs : ℤ)).map
        (Int.castRingHom ℝ)).eval (Real.cosh (Real.pi / (d : ℝ))) = _
      rw [OMA_MO484639.chebyshev_T_eval_cosh]
      have habs : ((((d : ℤ) - 2 * ((r j).val : ℤ)).natAbs : ℕ) : ℝ) * (Real.pi / (d : ℝ)) =
          |Real.pi * (1 - 2 * (((r j).val : ℝ) / (d : ℝ)))| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        push_cast
        have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
        have hd0 : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
        rw [abs_mul, abs_of_pos hpi0]
        have hrew : (1 : ℝ) - 2 * (((r j).val : ℝ) / (d : ℝ)) =
            ((d : ℝ) - 2 * ((r j).val : ℝ)) / (d : ℝ) := by field_simp [hdR]
        rw [hrew, abs_div, abs_of_pos hd0]
        ring
      rw [habs, Real.cosh_abs]
    rw [hevalR, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow]
  rw [hP_eval] at hmainC
  have hreal : (d : ℝ) * OMA.S_mo_484639.S V =
      (Real.pi ^ n / Real.sinh Real.pi ^ n) *
        (P.map (Int.castRingHom ℝ)).eval (Real.cosh (Real.pi / (d : ℝ))) :=
    Complex.ofReal_injective (by simpa [Complex.ofReal_mul] using hmainC)
  have hd_abs : (d : ℝ) = |(V.det : ℝ)| := by
    simp [d, Int.cast_abs]
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [← hd_abs]
  have hsinh_ne : Real.sinh Real.pi ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr Real.pi_pos)
  field_simp [hdR, hsinh_ne] at hreal ⊢
  linarith
