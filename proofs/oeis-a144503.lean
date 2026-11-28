import OMAStatements.S_oeis_a144503


open Filter Topology MeasureTheory Polynomial

theorem PG_integrable (p : ℝ[X]) :
    IntegrableOn (fun x : ℝ => p.eval x / Real.exp x) (Set.Ioi (0 : ℝ)) := by
  refine integrable_of_isBigO_exp_neg (b := 1 / 2) (by norm_num) ?_ ?_
  · exact (p.continuous.div Real.continuous_exp (fun x => (Real.exp_pos x).ne')).continuousOn
  · have h1 : Tendsto (fun x : ℝ => (p.comp (C 2 * X)).eval (x / 2) / Real.exp (x / 2)) atTop
        (𝓝 0) :=
      (Polynomial.tendsto_div_exp_atTop (p.comp (C 2 * X))).comp
        (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    have h2 : (fun x : ℝ => (p.comp (C 2 * X)).eval (x / 2) / Real.exp (x / 2))
        =O[atTop] (fun _ : ℝ => (1 : ℝ)) := h1.isBigO_one ℝ
    have h3 := h2.mul (Asymptotics.isBigO_refl (fun x : ℝ => Real.exp (-(1 / 2) * x)) atTop)
    refine (h3.congr' (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_))
    · simp only [eval_comp, eval_mul, eval_C, eval_X]
      have e : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
        rw [← Real.exp_add]; ring_nf
      have e2 : Real.exp (-(1 / 2) * x) = (Real.exp (x / 2))⁻¹ := by
        rw [← Real.exp_neg]; ring_nf
      rw [e, e2, show (2 : ℝ) * (x / 2) = x by ring]
      rw [div_mul_eq_div_div, div_eq_mul_inv (_ / _)]
    · simp

theorem PG_parts (q : ℝ[X]) :
    ∫ x in Set.Ioi (0 : ℝ), q.eval x / Real.exp x =
      q.eval 0 + ∫ x in Set.Ioi (0 : ℝ), (derivative q).eval x / Real.exp x := by
  have hd : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt (fun x : ℝ => q.eval x / Real.exp x)
      ((derivative q).eval x / Real.exp x - q.eval x / Real.exp x) x := by
    intro x _
    have hx := (Real.exp_pos x).ne'
    have h : HasDerivAt (fun x : ℝ => q.eval x / Real.exp x) _ x :=
      (q.hasDerivAt x).div (Real.hasDerivAt_exp x) hx
    refine h.congr_deriv ?_
    field_simp
  have hi := (PG_integrable (derivative q)).sub (PG_integrable q)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi (Polynomial.tendsto_div_exp_atTop q)
  have h4 : ∫ x in Set.Ioi (0 : ℝ), ((derivative q).eval x / Real.exp x - q.eval x / Real.exp x)
      = (∫ x in Set.Ioi (0 : ℝ), (derivative q).eval x / Real.exp x)
        - ∫ x in Set.Ioi (0 : ℝ), q.eval x / Real.exp x :=
    integral_sub (PG_integrable (derivative q)) (PG_integrable q)
  have h5 : ∫ x in Set.Ioi (0 : ℝ), ((derivative q).eval x / Real.exp x - q.eval x / Real.exp x)
      = 0 - q.eval 0 / Real.exp 0 := h
  rw [h4] at h5
  simp at h5
  linarith

theorem PG_shift (p : ℝ[X]) (x : ℝ) : (p.comp (X + 1)).eval x = p.eval (x + 1) := by
  simp [eval_comp]

theorem PG_rec (n : ℤ) :
    (∫ x in Set.Ioi (0 : ℝ), (Chebyshev.U ℝ (n + 1)).eval (x + 1) / Real.exp x) =
      2 * ((n : ℝ) + 1) * (∫ x in Set.Ioi (0 : ℝ), (Chebyshev.U ℝ n).eval (x + 1) / Real.exp x)
      + (∫ x in Set.Ioi (0 : ℝ), (Chebyshev.U ℝ (n - 1)).eval (x + 1) / Real.exp x) + 2 := by
  have hT := PG_parts ((Chebyshev.T ℝ (n + 1)).comp (X + 1))
  have hder : derivative ((Chebyshev.T ℝ (n + 1)).comp (X + 1))
      = (C ((n : ℝ) + 1) * Chebyshev.U ℝ n).comp (X + 1) := by
    rw [derivative_comp, Chebyshev.T_derivative_eq_U]
    simp
  rw [hder] at hT
  have h2 : 2 * Chebyshev.T ℝ (n + 1) = Chebyshev.U ℝ (n + 1) - Chebyshev.U ℝ (n - 1) := by
    have := Chebyshev.two_mul_T_eq_U_sub_U ℝ (n - 1)
    rwa [show n - 1 + 2 = n + 1 by ring] at this
  have h3 : ∀ x : ℝ, (Chebyshev.T ℝ (n + 1)).eval (x + 1)
      = ((Chebyshev.U ℝ (n + 1)).eval (x + 1) - (Chebyshev.U ℝ (n - 1)).eval (x + 1)) / 2 := by
    intro x
    have := congrArg (fun p : ℝ[X] => p.eval (x + 1)) h2
    simp at this
    linarith
  simp only [PG_shift, eval_mul, eval_C, Chebyshev.T_eval_one, zero_add] at hT
  simp only [h3] at hT
  have i1 := PG_integrable ((Chebyshev.U ℝ (n + 1)).comp (X + 1))
  have i2 := PG_integrable ((Chebyshev.U ℝ (n - 1)).comp (X + 1))
  simp only [PG_shift] at i1 i2
  have e1 : (∫ x in Set.Ioi (0 : ℝ), ((Chebyshev.U ℝ (n + 1)).eval (x + 1)
      - (Chebyshev.U ℝ (n - 1)).eval (x + 1)) / 2 / Real.exp x)
      = ((∫ x in Set.Ioi (0 : ℝ), (Chebyshev.U ℝ (n + 1)).eval (x + 1) / Real.exp x)
        - ∫ x in Set.Ioi (0 : ℝ), (Chebyshev.U ℝ (n - 1)).eval (x + 1) / Real.exp x) / 2 := by
    rw [← integral_sub i1 i2, ← integral_div]
    congr 1
    funext x
    ring
  have e2 : (∫ x in Set.Ioi (0 : ℝ), ((n : ℝ) + 1) * (Chebyshev.U ℝ n).eval (x + 1) / Real.exp x)
      = ((n : ℝ) + 1) * ∫ x in Set.Ioi (0 : ℝ), (Chebyshev.U ℝ n).eval (x + 1) / Real.exp x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [e1, e2] at hT
  linarith

theorem PG_zero : (∫ x in Set.Ioi (0 : ℝ), (Chebyshev.U ℝ 0).eval (x + 1) / Real.exp x) = 1 := by
  have h := PG_parts (1 : ℝ[X])
  simpa using h

theorem PG_main : ∀ n : ℕ,
    (OMA.S_oeis_a144503.giftExchange n : ℝ) = 1 + (∫ x in Set.Ioi (0 : ℝ),
        (Chebyshev.U ℝ ((n : ℤ) - 1)).eval (x + 1) / Real.exp x) ∧
    (OMA.S_oeis_a144503.giftExchange (n + 1) : ℝ) = 1 + (∫ x in Set.Ioi (0 : ℝ),
        (Chebyshev.U ℝ (n : ℤ)).eval (x + 1) / Real.exp x) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [OMA.S_oeis_a144503.giftExchange]
    · have := PG_zero
      simp only [Nat.cast_zero]
      rw [this]
      simp [OMA.S_oeis_a144503.giftExchange]
      norm_num
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [h1]
      simp
    · have hr := PG_rec (k : ℤ)
      have hg : OMA.S_oeis_a144503.giftExchange (k + 1 + 1)
          = 2 * ((k : ℤ) + 1) * OMA.S_oeis_a144503.giftExchange (k + 1)
            + OMA.S_oeis_a144503.giftExchange k - 2 * (k : ℤ) := by
        rw [OMA.S_oeis_a144503.giftExchange]
      rw [hg]
      push_cast
      simp only [Int.cast_natCast] at hr
      rw [h0, h1, hr]
      ring

theorem solved : ∀ n : ℕ, (OMA.S_oeis_a144503.giftExchange n : ℝ) = 1 + ∫ x in Set.Ioi (0 : ℝ), (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1)).eval (x + 1) / Real.exp x :=
  fun n => (PG_main n).1

theorem OMA.solution : type_of% @OMA.S_oeis_a144503.main := solved
