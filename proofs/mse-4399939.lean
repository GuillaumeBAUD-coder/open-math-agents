import OMAStatements.S_mse_4399939

namespace OMA.Mse4399939

open Filter Topology MeasureTheory Real Complex

/-!
## 1. Extreme-tail monotonicity via derivative-coefficient comparison
-/

lemma coeff_pow_nonneg {n : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree ≤ n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) :
    ∀ (r m : ℕ), 0 ≤ (P ^ r).coeff m := by
  intro r
  induction r with
  | zero =>
    intro m
    simp [Polynomial.coeff_one]
    split_ifs <;> norm_num
  | succ r ih =>
    intro m
    rw [pow_succ, Polynomial.coeff_mul]
    refine Finset.sum_nonneg fun x _ => ?_
    refine mul_nonneg (ih x.1) ?_
    by_cases hx : x.2 ≤ n
    · exact (hpos x.2 hx).le
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

lemma coeff_mul_X_derivative (Q : Polynomial ℝ) (m : ℕ) :
    (Polynomial.X * Q.derivative).coeff m = (m : ℝ) * Q.coeff m := by
  cases m with
  | zero => simp
  | succ m =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
    push_cast
    ring

lemma left_tail_mono {n : ℕ} {P : Polynomial ℝ} (hn : 2 ≤ n) (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {r m : ℕ} (hr : 1 ≤ r)
    (hm : ((m + 1 : ℕ) : ℝ) * P.coeff 0 ≤ ((r : ℝ) - (m : ℝ)) * P.coeff 1) :
    (P ^ r).coeff m ≤ (P ^ r).coeff (m + 1) := by
  have hc_nonneg : ∀ j, 0 ≤ (P ^ (r - 1)).coeff j := coeff_pow_nonneg hdeg.le hpos (r - 1)
  have ha_nonneg : ∀ k, 0 ≤ P.coeff k := fun k => by
    by_cases hk : k ≤ n
    · exact (hpos k hk).le
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  have hpow : P ^ r = P * P ^ (r - 1) := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ']
  have hderiv_pow : (P ^ r).derivative = Polynomial.C (r : ℝ) * (P.derivative * P ^ (r - 1)) := by
    rw [Polynomial.derivative_pow]
    ring
  -- (1) `(m + 1) * b_{m+1} >= r * a_1 * c_m`
  have h1 : (r : ℝ) * P.coeff 1 * (P ^ (r - 1)).coeff m ≤ ((m + 1 : ℕ) : ℝ) * (P ^ r).coeff (m + 1) := by
    have heq : ((m + 1 : ℕ) : ℝ) * (P ^ r).coeff (m + 1) =
        (r : ℝ) * (P.derivative * P ^ (r - 1)).coeff m := by
      have := congrArg (fun Q : Polynomial ℝ => Q.coeff m) hderiv_pow
      rw [Polynomial.coeff_derivative, Polynomial.coeff_C_mul] at this
      simpa [Nat.cast_add, Nat.cast_one, mul_comm] using this
    rw [heq, Polynomial.coeff_mul]
    have hterm_nonneg : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal m,
        0 ≤ P.derivative.coeff x.1 * (P ^ (r - 1)).coeff x.2 := by
      intro x _
      rw [Polynomial.coeff_derivative]
      exact mul_nonneg (mul_nonneg (ha_nonneg _) (by positivity)) (hc_nonneg _)
    have hmem : (0, m) ∈ Finset.HasAntidiagonal.antidiagonal m := by simp
    have hsingle := Finset.single_le_sum hterm_nonneg hmem
    rw [Polynomial.coeff_derivative] at hsingle
    simp only [zero_add, Nat.cast_zero, mul_one] at hsingle
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
    calc (r : ℝ) * P.coeff 1 * (P ^ (r - 1)).coeff m
        = (r : ℝ) * (P.coeff 1 * (P ^ (r - 1)).coeff m) := by ring
      _ ≤ (r : ℝ) * ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, P.derivative.coeff x.1 * (P ^ (r - 1)).coeff x.2 :=
          mul_le_mul_of_nonneg_left hsingle hr0
  -- (2) `m * b_m = r * ∑_{k >= 1} k * a_k * c_{m - k} >= r * ∑_{k >= 1} a_k * c_{m - k} = r * (b_m - a_0 * c_m)`
  have h2 : ((r : ℝ) - (m : ℝ)) * (P ^ r).coeff m ≤ (r : ℝ) * P.coeff 0 * (P ^ (r - 1)).coeff m := by
    have hbm : (P ^ r).coeff m =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, P.coeff x.1 * (P ^ (r - 1)).coeff x.2 := by
      rw [hpow, Polynomial.coeff_mul]
    have hmbm : (m : ℝ) * (P ^ r).coeff m =
        (r : ℝ) * ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, (x.1 : ℝ) * P.coeff x.1 * (P ^ (r - 1)).coeff x.2 := by
      have hX : Polynomial.X * (P ^ r).derivative =
          Polynomial.C (r : ℝ) * ((Polynomial.X * P.derivative) * P ^ (r - 1)) := by
        rw [hderiv_pow]; ring
      have := congrArg (fun Q : Polynomial ℝ => Q.coeff m) hX
      rw [coeff_mul_X_derivative, Polynomial.coeff_C_mul, Polynomial.coeff_mul] at this
      rw [this]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [coeff_mul_X_derivative]
    have hmem : (0, m) ∈ Finset.HasAntidiagonal.antidiagonal m := by simp
    have hsplit_bm : (P ^ r).coeff m =
        P.coeff 0 * (P ^ (r - 1)).coeff m +
          ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal m).erase (0, m), P.coeff x.1 * (P ^ (r - 1)).coeff x.2 := by
      rw [hbm, ← Finset.add_sum_erase _ _ hmem]
    have hsplit_mbm : (m : ℝ) * (P ^ r).coeff m =
        (r : ℝ) * ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal m).erase (0, m),
          (x.1 : ℝ) * P.coeff x.1 * (P ^ (r - 1)).coeff x.2 := by
      rw [hmbm, ← Finset.add_sum_erase _ _ hmem]
      simp
    have hsum_le :
        ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal m).erase (0, m), P.coeff x.1 * (P ^ (r - 1)).coeff x.2 ≤
        ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal m).erase (0, m),
          (x.1 : ℝ) * P.coeff x.1 * (P ^ (r - 1)).coeff x.2 := by
      refine Finset.sum_le_sum fun x hx => ?_
      have hx_ne : x ≠ (0, m) := (Finset.mem_erase.mp hx).1
      have hx_sum : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_erase.mp hx).2
      have hx1_pos : 1 ≤ x.1 := by
        by_contra h0
        have hx1 : x.1 = 0 := by omega
        have hx2 : x.2 = m := by omega
        exact hx_ne (Prod.ext hx1 hx2)
      have hx1_ge : (1 : ℝ) ≤ (x.1 : ℝ) := by exact_mod_cast hx1_pos
      have hnn : 0 ≤ P.coeff x.1 * (P ^ (r - 1)).coeff x.2 := mul_nonneg (ha_nonneg _) (hc_nonneg _)
      calc P.coeff x.1 * (P ^ (r - 1)).coeff x.2
          = 1 * (P.coeff x.1 * (P ^ (r - 1)).coeff x.2) := (one_mul _).symm
        _ ≤ (x.1 : ℝ) * (P.coeff x.1 * (P ^ (r - 1)).coeff x.2) := mul_le_mul_of_nonneg_right hx1_ge hnn
        _ = (x.1 : ℝ) * P.coeff x.1 * (P ^ (r - 1)).coeff x.2 := by ring
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsum_le hr0]
  -- Combine (1), (2), and `hm`!
  have ha0 : 0 < P.coeff 0 := hpos 0 (by omega)
  have ha1 : 0 < P.coeff 1 := hpos 1 (by omega)
  have hbm0 : 0 ≤ (P ^ r).coeff m := coeff_pow_nonneg hdeg.le hpos r m
  have hcomb : ((m + 1 : ℕ) : ℝ) * P.coeff 0 * (P ^ r).coeff m ≤
      ((m + 1 : ℕ) : ℝ) * P.coeff 0 * (P ^ r).coeff (m + 1) := by
    calc ((m + 1 : ℕ) : ℝ) * P.coeff 0 * (P ^ r).coeff m
        ≤ ((r : ℝ) - (m : ℝ)) * P.coeff 1 * (P ^ r).coeff m :=
          mul_le_mul_of_nonneg_right hm hbm0
      _ = P.coeff 1 * (((r : ℝ) - (m : ℝ)) * (P ^ r).coeff m) := by ring
      _ ≤ P.coeff 1 * ((r : ℝ) * P.coeff 0 * (P ^ (r - 1)).coeff m) :=
          mul_le_mul_of_nonneg_left h2 ha1.le
      _ = P.coeff 0 * ((r : ℝ) * P.coeff 1 * (P ^ (r - 1)).coeff m) := by ring
      _ ≤ P.coeff 0 * (((m + 1 : ℕ) : ℝ) * (P ^ r).coeff (m + 1)) :=
          mul_le_mul_of_nonneg_left h1 ha0.le
      _ = ((m + 1 : ℕ) : ℝ) * P.coeff 0 * (P ^ r).coeff (m + 1) := by ring
  have hfac_pos : 0 < ((m + 1 : ℕ) : ℝ) * P.coeff 0 := by positivity
  exact le_of_mul_le_mul_left hcomb hfac_pos

lemma reverse_natDegree_eq {n : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) :
    P.reverse.natDegree = n := by
  refine le_antisymm ?_ ?_
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
    rw [Polynomial.coeff_reverse, hdeg, Polynomial.revAt_eq_self_of_lt hk]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [Polynomial.coeff_reverse, hdeg, Polynomial.revAt_le le_rfl, Nat.sub_self]
    exact (hpos 0 (Nat.zero_le n)).ne'

lemma coeff_reverse_pow {n : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree = n)
    (_hpos : ∀ i ≤ n, 0 < P.coeff i) (r : ℕ) :
    ∀ k ≤ n * r, (P.reverse ^ r).coeff k = (P ^ r).coeff (n * r - k) := by
  have hdeg_pow : ∀ s, (P ^ s).natDegree = n * s := by
    intro s
    rw [Polynomial.natDegree_pow, hdeg, mul_comm]
  have hrev_one : (1 : Polynomial ℝ).reverse = 1 := by
    ext k
    rw [Polynomial.coeff_reverse, Polynomial.natDegree_one]
    cases k with
    | zero => simp [Polynomial.revAt_le]
    | succ k' =>
      have : Polynomial.revAt 0 (k' + 1) = k' + 1 := Polynomial.revAt_eq_self_of_lt (Nat.succ_pos k')
      simp [this]
  have hrev_pow : P.reverse ^ r = (P ^ r).reverse := by
    induction r with
    | zero => simp [hrev_one]
    | succ r ih =>
      rw [pow_succ, pow_succ, ih]
      exact (Polynomial.reverse_mul_of_domain (P ^ r) P).symm
  intro k hk
  rw [hrev_pow, Polynomial.coeff_reverse, hdeg_pow r, Polynomial.revAt_le hk]

lemma right_tail_mono {n : ℕ} {P : Polynomial ℝ} (hn : 2 ≤ n) (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {r m : ℕ} (hr : 1 ≤ r) (hm_lt : m < n * r)
    (hm : ((n * r - m : ℕ) : ℝ) * P.coeff n ≤ ((r : ℝ) - ((n * r - 1 - m : ℕ) : ℝ)) * P.coeff (n - 1)) :
    (P ^ r).coeff (m + 1) ≤ (P ^ r).coeff m := by
  have hQ_deg : P.reverse.natDegree = n := reverse_natDegree_eq hdeg hpos
  have hQ_coeff : ∀ i ≤ n, P.reverse.coeff i = P.coeff (n - i) := by
    intro i hi
    rw [Polynomial.coeff_reverse, hdeg, Polynomial.revAt_le hi]
  have hQ_pos : ∀ i ≤ n, 0 < P.reverse.coeff i := by
    intro i hi
    rw [hQ_coeff i hi]
    exact hpos (n - i) (by omega)
  set k := n * r - 1 - m
  have hk1 : k + 1 = n * r - m := by omega
  have hQ0 : P.reverse.coeff 0 = P.coeff n := by simpa using hQ_coeff 0 (by omega)
  have hQ1 : P.reverse.coeff 1 = P.coeff (n - 1) := hQ_coeff 1 (by omega)
  have hle := left_tail_mono hn hQ_deg hQ_pos hr (m := k) (by rw [hk1, hQ0, hQ1]; exact hm)
  rw [coeff_reverse_pow hdeg hpos r k (by omega),
    coeff_reverse_pow hdeg hpos r (k + 1) (by omega)] at hle
  rw [show n * r - k = m + 1 by omega, show n * r - (k + 1) = m by omega] at hle
  exact hle

/-!
## 2. Complex exponential and cosine bounds, Fourier inversion, and Gaussian integrals
-/

lemma complex_exp_I_taylor (x : ℝ) :
    ‖Complex.exp (I * x) - (1 + I * x - (x : ℂ) ^ 2 / 2)‖ ≤ |x| ^ 3 / 6 := by
  -- Prove separately for real and imaginary parts via FTC!
  -- Actually `Re = cos x - (1 - x^2/2)` and `Im = sin x - x`,
  -- and even better: integral formula `e^{Ix} - (1 + Ix - x^2/2) = -I * ∫_0^x ((x - u)^2 / 2) * e^{Iu} du`!
  have h_id : ∀ y : ℝ,
      Complex.exp (I * y) - (1 + I * y - (y : ℂ) ^ 2 / 2) =
        (-I) * ∫ u in (0 : ℝ)..y, (((y - u : ℝ) ^ 2 / 2 : ℝ) : ℂ) * Complex.exp (I * u) := by
    intro y
    -- FTC on `F(u) = (1 + I*(y-u) - (y-u)^2/2) * e^{Iu}`!
    let F : ℝ → ℂ := fun u =>
      ((1 : ℂ) + I * ((y - u : ℝ) : ℂ) - ((y - u : ℝ) : ℂ) ^ 2 / 2) * Complex.exp (I * u)
    have hF_deriv : ∀ u ∈ Set.uIcc (0 : ℝ) y,
        HasDerivAt F ((-I) * ((((y - u : ℝ) ^ 2 / 2 : ℝ) : ℂ) * Complex.exp (I * u))) u := by
      intro u _
      have h1 : HasDerivAt (fun u : ℝ => ((y - u : ℝ) : ℂ)) (-1 : ℂ) u := by
        have hsub : HasDerivAt (fun u : ℝ => y - u) (-1 : ℝ) u := by
          simpa using (hasDerivAt_id u).const_sub y
        simpa using hsub.ofReal_comp
      have h2 : HasDerivAt (fun u : ℝ => (1 : ℂ) + I * ((y - u : ℝ) : ℂ) - ((y - u : ℝ) : ℂ) ^ 2 / 2)
          (-I + ((y - u : ℝ) : ℂ)) u := by
        have ha := (h1.const_mul I).const_add (1 : ℂ)
        have hb := (h1.pow 2).div_const (2 : ℂ)
        refine (ha.fun_sub hb).congr_deriv ?_
        simp; ring
      have h3 : HasDerivAt (fun u : ℝ => Complex.exp (I * (u : ℂ))) (I * Complex.exp (I * (u : ℂ))) u := by
        have hiu : HasDerivAt (fun u : ℝ => I * (u : ℂ)) I u := by
          simpa using (hasDerivAt_id u).ofReal_comp.const_mul I
        simpa [mul_comm] using hiu.cexp
      refine (h2.fun_mul h3).congr_deriv ?_
      push_cast
      have hI2 : I ^ 2 = -1 := I_sq
      linear_combination ((y : ℂ) - (u : ℂ)) * Complex.exp (I * (u : ℂ)) * hI2
    have hcont : Continuous (fun u : ℝ => (-I) * ((((y - u : ℝ) ^ 2 / 2 : ℝ) : ℂ) * Complex.exp (I * u))) := by
      fun_prop
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv (hcont.intervalIntegrable 0 y)
    rw [intervalIntegral.integral_const_mul] at hftc
    dsimp only [F] at hftc
    simp only [sub_self, ofReal_zero, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_div, sub_zero, one_mul, Complex.exp_zero, mul_one] at hftc
    exact hftc.symm
  rw [h_id x, norm_mul, norm_neg, norm_I, one_mul]
  have hint_val : ∫ u in (0 : ℝ)..x, (x - u) ^ 2 / 2 = x ^ 3 / 6 := by
    have hd : ∀ u ∈ Set.uIcc (0 : ℝ) x,
        HasDerivAt (fun u : ℝ => -((x - u) ^ 3 / 6)) ((x - u) ^ 2 / 2) u := by
      intro u _
      have h1 : HasDerivAt (fun u : ℝ => x - u) (-1) u := by simpa using (hasDerivAt_id u).const_sub x
      refine (((h1.pow 3).div_const 6).neg).congr_deriv ?_; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous _).intervalIntegrable 0 x)]
    ring
  rcases le_total 0 x with hx | hx
  · calc ‖∫ u in (0 : ℝ)..x, (((x - u : ℝ) ^ 2 / 2 : ℝ) : ℂ) * Complex.exp (I * u)‖
        ≤ ∫ u in (0 : ℝ)..x, ‖(((x - u : ℝ) ^ 2 / 2 : ℝ) : ℂ) * Complex.exp (I * u)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hx
      _ = ∫ u in (0 : ℝ)..x, (x - u) ^ 2 / 2 := by
          refine intervalIntegral.integral_congr fun u _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
            show I * (u : ℂ) = ((u : ℝ) : ℂ) * I by ring, Complex.norm_exp_ofReal_mul_I, mul_one]
      _ = x ^ 3 / 6 := hint_val
      _ = |x| ^ 3 / 6 := by rw [abs_of_nonneg hx]
  · rw [intervalIntegral.integral_symm, norm_neg]
    calc ‖∫ u in x..(0 : ℝ), (((x - u : ℝ) ^ 2 / 2 : ℝ) : ℂ) * Complex.exp (I * u)‖
        ≤ ∫ u in x..(0 : ℝ), ‖(((x - u : ℝ) ^ 2 / 2 : ℝ) : ℂ) * Complex.exp (I * u)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hx
      _ = ∫ u in x..(0 : ℝ), (x - u) ^ 2 / 2 := by
          refine intervalIntegral.integral_congr fun u _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
            show I * (u : ℂ) = ((u : ℝ) : ℂ) * I by ring, Complex.norm_exp_ofReal_mul_I, mul_one]
      _ = -(∫ u in (0 : ℝ)..x, (x - u) ^ 2 / 2) := intervalIntegral.integral_symm 0 x
      _ = -(x ^ 3 / 6) := by rw [hint_val]
      _ = |x| ^ 3 / 6 := by rw [abs_of_nonpos hx]; ring

lemma complex_exp_I_linear (x : ℝ) :
    ‖Complex.exp (I * x) - (1 + I * x)‖ ≤ x ^ 2 / 2 := by
  have h_id : ∀ y : ℝ,
      Complex.exp (I * y) - (1 + I * y) =
        (-1 : ℂ) * ∫ u in (0 : ℝ)..y, ((y - u : ℝ) : ℂ) * Complex.exp (I * u) := by
    intro y
    let F : ℝ → ℂ := fun u => ((1 : ℂ) + I * ((y - u : ℝ) : ℂ)) * Complex.exp (I * u)
    have hF_deriv : ∀ u ∈ Set.uIcc (0 : ℝ) y,
        HasDerivAt F ((-1 : ℂ) * (((y - u : ℝ) : ℂ) * Complex.exp (I * u))) u := by
      intro u _
      have h1 : HasDerivAt (fun u : ℝ => ((y - u : ℝ) : ℂ)) (-1 : ℂ) u := by
        simpa using ((hasDerivAt_id u).const_sub y).ofReal_comp
      have h2 := (h1.const_mul I).const_add (1 : ℂ)
      have h3 : HasDerivAt (fun u : ℝ => Complex.exp (I * (u : ℂ))) (I * Complex.exp (I * (u : ℂ))) u := by
        simpa [mul_comm] using ((hasDerivAt_id u).ofReal_comp.const_mul I).cexp
      refine (h2.fun_mul h3).congr_deriv ?_
      push_cast
      have hI2 : I ^ 2 = -1 := I_sq
      linear_combination ((y : ℂ) - (u : ℂ)) * Complex.exp (I * (u : ℂ)) * hI2
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv
      ((by fun_prop : Continuous _).intervalIntegrable 0 y)
    rw [intervalIntegral.integral_const_mul] at hftc
    dsimp only [F] at hftc
    simp only [sub_self, ofReal_zero, mul_zero, add_zero, one_mul, sub_zero, Complex.exp_zero, mul_one] at hftc
    exact hftc.symm
  rw [h_id x, norm_mul, norm_neg, norm_one, one_mul]
  rcases le_total 0 x with hx | hx
  · calc ‖∫ u in (0 : ℝ)..x, ((x - u : ℝ) : ℂ) * Complex.exp (I * u)‖
        ≤ ∫ u in (0 : ℝ)..x, ‖((x - u : ℝ) : ℂ) * Complex.exp (I * u)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hx
      _ = ∫ u in (0 : ℝ)..x, (x - u) := by
          refine intervalIntegral.integral_congr fun u hu => ?_
          rw [Set.uIcc_of_le hx] at hu
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hu.2]),
            show I * (u : ℂ) = ((u : ℝ) : ℂ) * I by ring, Complex.norm_exp_ofReal_mul_I, mul_one]
      _ = x ^ 2 / 2 := by
          have hd : ∀ u ∈ Set.uIcc (0 : ℝ) x, HasDerivAt (fun u : ℝ => -((x - u) ^ 2 / 2)) (x - u) u := by
            intro u _
            have h1 : HasDerivAt (fun u : ℝ => x - u) (-1) u := by simpa using (hasDerivAt_id u).const_sub x
            refine (((h1.pow 2).div_const 2).neg).congr_deriv ?_; ring
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous _).intervalIntegrable 0 x)]
          ring
  · rw [intervalIntegral.integral_symm, norm_neg]
    calc ‖∫ u in x..(0 : ℝ), ((x - u : ℝ) : ℂ) * Complex.exp (I * u)‖
        ≤ ∫ u in x..(0 : ℝ), ‖((x - u : ℝ) : ℂ) * Complex.exp (I * u)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hx
      _ = ∫ u in x..(0 : ℝ), (u - x) := by
          refine intervalIntegral.integral_congr fun u hu => ?_
          rw [Set.uIcc_of_le hx] at hu
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hu.1]),
            show I * (u : ℂ) = ((u : ℝ) : ℂ) * I by ring, Complex.norm_exp_ofReal_mul_I, mul_one]
          ring
      _ = x ^ 2 / 2 := by
          have hd : ∀ u ∈ Set.uIcc x (0 : ℝ), HasDerivAt (fun u : ℝ => (u - x) ^ 2 / 2) (u - x) u := by
            intro u _
            have h1 : HasDerivAt (fun u : ℝ => u - x) 1 u := by simpa using (hasDerivAt_id u).sub_const x
            refine ((h1.pow 2).div_const 2).congr_deriv ?_; ring
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous _).intervalIntegrable x 0)]
          ring

lemma real_exp_neg_taylor {y : ℝ} (hy : 0 ≤ y) :
    |Real.exp (-y) - (1 - y)| ≤ y ^ 2 / 2 := by
  have h1 : 0 ≤ Real.exp (-y) - (1 - y) := by
    have := Real.add_one_le_exp (-y)
    linarith
  rw [abs_of_nonneg h1]
  have h_id : Real.exp (-y) - (1 - y) = ∫ u in (0 : ℝ)..y, (y - u) * Real.exp (-u) := by
    let F : ℝ → ℝ := fun u => (1 + u - y) * Real.exp (-u)
    have hF : ∀ u ∈ Set.uIcc (0 : ℝ) y, HasDerivAt F ((y - u) * Real.exp (-u)) u := by
      intro u _
      have ha : HasDerivAt (fun u : ℝ => 1 + u - y) 1 u := by
        simpa using ((hasDerivAt_id u).const_add 1).sub_const y
      have hb : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-u)) u := by
        simpa using (hasDerivAt_id u).neg.exp
      refine (ha.fun_mul hb).congr_deriv ?_; ring
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      ((by fun_prop : Continuous _).intervalIntegrable 0 y)
    dsimp only [F] at hftc
    simp only [add_sub_cancel_right, one_mul, add_zero, neg_zero, Real.exp_zero, mul_one] at hftc
    linarith
  rw [h_id]
  calc ∫ u in (0 : ℝ)..y, (y - u) * Real.exp (-u)
      ≤ ∫ u in (0 : ℝ)..y, (y - u) := by
        refine intervalIntegral.integral_mono_on hy
          ((by fun_prop : Continuous _).intervalIntegrable 0 y)
          ((by fun_prop : Continuous _).intervalIntegrable 0 y) fun u hu => ?_
        have he : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hu.1])
        nlinarith [hu.2]
    _ = y ^ 2 / 2 := by
        have hd : ∀ u ∈ Set.uIcc (0 : ℝ) y, HasDerivAt (fun u : ℝ => -((y - u) ^ 2 / 2)) (y - u) u := by
          intro u _
          have h1 : HasDerivAt (fun u : ℝ => y - u) (-1) u := by simpa using (hasDerivAt_id u).const_sub y
          refine (((h1.pow 2).div_const 2).neg).congr_deriv ?_; ring
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous _).intervalIntegrable 0 y)]
        ring

lemma cos_quad_approx (θ : ℝ) :
    |2 * Real.cos θ - 2 + θ ^ 2| ≤ θ ^ 4 / 12 := by
  -- From `Real.cos θ = (Complex.exp (I * θ)).re`, wait: even simpler, FTC on `2 cos θ - 2 + θ^2`!
  -- `d/du (2 cos u - 2 + u^2) = -2 sin u + 2 u = 2 (u - sin u)`
  -- Use `|e^{Iθ} - (1 + Iθ - θ^2/2 - Iθ^3/6)| <= θ^4/24`, or 2-step FTC on `sin` and `cos`!
  have hcos_ge : ∀ u : ℝ, 0 ≤ u → 1 - u ^ 2 / 2 ≤ Real.cos u := by
    intro u hu
    have hsin : ∀ t ∈ Set.uIcc (0 : ℝ) u, Real.sin t ≤ t := by
      intro t ht
      rw [Set.uIcc_of_le hu] at ht
      exact Real.sin_le ht.1
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) u, HasDerivAt (fun t => Real.cos t) (-Real.sin t) t :=
      fun t _ => Real.hasDerivAt_cos t
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous _).intervalIntegrable 0 u)
    have hle : ∫ t in (0 : ℝ)..u, Real.sin t ≤ ∫ t in (0 : ℝ)..u, t :=
      intervalIntegral.integral_mono_on hu
        ((by fun_prop : Continuous _).intervalIntegrable 0 u)
        ((by fun_prop : Continuous _).intervalIntegrable 0 u) (fun t ht => hsin t (by rw [Set.uIcc_of_le hu]; exact ht))
    have ht_int : ∫ t in (0 : ℝ)..u, t = u ^ 2 / 2 := by
      have hd2 : ∀ t ∈ Set.uIcc (0 : ℝ) u, HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
        intro t _; refine ((hasDerivAt_pow 2 t).div_const 2).congr_deriv ?_; ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd2 ((by fun_prop : Continuous _).intervalIntegrable 0 u)]
      ring
    rw [intervalIntegral.integral_neg, Real.cos_zero] at hftc
    linarith
  have hsin_ge : ∀ u : ℝ, 0 ≤ u → u - u ^ 3 / 6 ≤ Real.sin u := by
    intro u hu
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) u, HasDerivAt (fun t => Real.sin t) (Real.cos t) t :=
      fun t _ => Real.hasDerivAt_sin t
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous _).intervalIntegrable 0 u)
    have hle : ∫ t in (0 : ℝ)..u, (1 - t ^ 2 / 2) ≤ ∫ t in (0 : ℝ)..u, Real.cos t :=
      intervalIntegral.integral_mono_on hu
        ((by fun_prop : Continuous _).intervalIntegrable 0 u)
        ((by fun_prop : Continuous _).intervalIntegrable 0 u) (fun t ht => hcos_ge t ht.1)
    have ht_int : ∫ t in (0 : ℝ)..u, (1 - t ^ 2 / 2) = u - u ^ 3 / 6 := by
      have hd2 : ∀ t ∈ Set.uIcc (0 : ℝ) u, HasDerivAt (fun t : ℝ => t - t ^ 3 / 6) (1 - t ^ 2 / 2) t := by
        intro t _
        refine ((hasDerivAt_id t).fun_sub ((hasDerivAt_pow 3 t).div_const 6)).congr_deriv ?_; ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd2 ((by fun_prop : Continuous _).intervalIntegrable 0 u)]
      ring
    rw [Real.sin_zero, sub_zero] at hftc
    linarith
  have hcos_le : ∀ u : ℝ, 0 ≤ u → Real.cos u ≤ 1 - u ^ 2 / 2 + u ^ 4 / 24 := by
    intro u hu
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) u, HasDerivAt (fun t => Real.cos t) (-Real.sin t) t :=
      fun t _ => Real.hasDerivAt_cos t
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous _).intervalIntegrable 0 u)
    have hle : ∫ t in (0 : ℝ)..u, (t - t ^ 3 / 6) ≤ ∫ t in (0 : ℝ)..u, Real.sin t :=
      intervalIntegral.integral_mono_on hu
        ((by fun_prop : Continuous _).intervalIntegrable 0 u)
        ((by fun_prop : Continuous _).intervalIntegrable 0 u) (fun t ht => hsin_ge t ht.1)
    have ht_int : ∫ t in (0 : ℝ)..u, (t - t ^ 3 / 6) = u ^ 2 / 2 - u ^ 4 / 24 := by
      have hd2 : ∀ t ∈ Set.uIcc (0 : ℝ) u, HasDerivAt (fun t : ℝ => t ^ 2 / 2 - t ^ 4 / 24) (t - t ^ 3 / 6) t := by
        intro t _
        refine (((hasDerivAt_pow 2 t).div_const 2).fun_sub ((hasDerivAt_pow 4 t).div_const 24)).congr_deriv ?_; ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd2 ((by fun_prop : Continuous _).intervalIntegrable 0 u)]
      ring
    rw [intervalIntegral.integral_neg, Real.cos_zero] at hftc
    linarith
  have habs_cos : Real.cos θ = Real.cos |θ| := by
    rcases le_total 0 θ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, Real.cos_neg]
  rw [habs_cos, ← sq_abs θ, show θ ^ 4 = |θ| ^ 4 by rw [show θ ^ 4 = (θ ^ 2) ^ 2 by ring, ← sq_abs θ]; ring]
  have hlo := hcos_ge |θ| (abs_nonneg θ)
  have hhi := hcos_le |θ| (abs_nonneg θ)
  rw [abs_le]
  constructor <;> linarith

lemma two_cos_sub_two_norm (θ : ℝ) : |2 * Real.cos θ - 2| ≤ θ ^ 2 := by
  have h1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have h2 : 1 - θ ^ 2 / 2 ≤ Real.cos θ := by
    have hcos := cos_quad_approx θ
    -- Actually prove `1 - θ^2/2 <= cos θ` directly from `|2 cos θ - 2 + θ^2| <= θ^4/12`? No, prove from `sin_le`!
    have hge : ∀ u : ℝ, 0 ≤ u → 1 - u ^ 2 / 2 ≤ Real.cos u := by
      intro u hu
      have hd : ∀ t ∈ Set.uIcc (0 : ℝ) u, HasDerivAt (fun t => Real.cos t) (-Real.sin t) t :=
        fun t _ => Real.hasDerivAt_cos t
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((by fun_prop : Continuous _).intervalIntegrable 0 u)
      have hle : ∫ t in (0 : ℝ)..u, Real.sin t ≤ ∫ t in (0 : ℝ)..u, t :=
        intervalIntegral.integral_mono_on hu
          ((by fun_prop : Continuous _).intervalIntegrable 0 u)
          ((by fun_prop : Continuous _).intervalIntegrable 0 u) (fun t ht => Real.sin_le ht.1)
      have ht_int : ∫ t in (0 : ℝ)..u, t = u ^ 2 / 2 := by
        have hd2 : ∀ t ∈ Set.uIcc (0 : ℝ) u, HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
          intro t _; refine ((hasDerivAt_pow 2 t).div_const 2).congr_deriv ?_; ring
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd2 ((by fun_prop : Continuous _).intervalIntegrable 0 u)]
        ring
      rw [intervalIntegral.integral_neg, Real.cos_zero] at hftc
      linarith
    rcases le_total 0 θ with h | h
    · exact hge θ h
    · simpa [Real.cos_neg] using hge (-θ) (by linarith)
  rw [abs_le]
  constructor <;> linarith

lemma norm_pow_sub_pow_le (u v : ℂ) {M : ℝ} (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M) :
    ∀ r : ℕ, 1 ≤ r → ‖u ^ r - v ^ r‖ ≤ (r : ℝ) * M ^ (r - 1) * ‖u - v‖ := by
  intro r hr
  have hM : 0 ≤ M := le_trans (norm_nonneg u) hu
  induction r with
  | zero => omega
  | succ r ih =>
    cases r with
    | zero => simp
    | succ r' =>
      have hdecomp : u ^ (r' + 2) - v ^ (r' + 2) =
          u * (u ^ (r' + 1) - v ^ (r' + 1)) + (u - v) * v ^ (r' + 1) := by ring
      rw [hdecomp]
      have h1 : ‖u * (u ^ (r' + 1) - v ^ (r' + 1))‖ ≤
          M * (((r' + 1 : ℕ) : ℝ) * M ^ r' * ‖u - v‖) := by
        rw [norm_mul]
        exact mul_le_mul hu (ih (by omega)) (norm_nonneg _) hM
      have h2 : ‖(u - v) * v ^ (r' + 1)‖ ≤ ‖u - v‖ * M ^ (r' + 1) := by
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg v) hv _) (norm_nonneg _)
      calc ‖u * (u ^ (r' + 1) - v ^ (r' + 1)) + (u - v) * v ^ (r' + 1)‖
          ≤ ‖u * (u ^ (r' + 1) - v ^ (r' + 1))‖ + ‖(u - v) * v ^ (r' + 1)‖ := norm_add_le _ _
        _ ≤ M * (((r' + 1 : ℕ) : ℝ) * M ^ r' * ‖u - v‖) + ‖u - v‖ * M ^ (r' + 1) := add_le_add h1 h2
        _ = ((r' + 1 + 1 : ℕ) : ℝ) * M ^ (r' + 1) * ‖u - v‖ := by
            push_cast; rw [pow_succ]; ring

lemma integral_cexp_int_mul_I (d : ℤ) :
    ∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (d : ℂ) * θ) =
      if d = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hd : d = 0
  · subst hd
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, Complex.real_smul, mul_one, ↓reduceIte]
    push_cast
    ring
  · rw [if_neg hd]
    have hId : I * (d : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Int.cast_ne_zero.mpr hd)
    have hderiv : ∀ θ ∈ Set.uIcc (-Real.pi) Real.pi,
        HasDerivAt (fun θ : ℝ => Complex.exp (I * (d : ℂ) * θ) / (I * (d : ℂ)))
          (Complex.exp (I * (d : ℂ) * θ)) θ := by
      intro θ _
      have h1 : HasDerivAt (fun θ : ℝ => I * (d : ℂ) * (θ : ℂ)) (I * (d : ℂ)) θ := by
        simpa using (hasDerivAt_id θ).ofReal_comp.const_mul (I * (d : ℂ))
      refine (h1.cexp.div_const (I * (d : ℂ))).congr_deriv ?_
      field_simp [hId]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous _).intervalIntegrable _ _)]
    have heq : Complex.exp (I * (d : ℂ) * (Real.pi : ℂ)) =
        Complex.exp (I * (d : ℂ) * ((-Real.pi : ℝ) : ℂ)) := by
      have hdiff : I * (d : ℂ) * (Real.pi : ℂ) - I * (d : ℂ) * ((-Real.pi : ℝ) : ℂ) =
          (d : ℂ) * (2 * Real.pi * I) := by push_cast; ring
      have hexp1 : Complex.exp ((d : ℂ) * (2 * Real.pi * I)) = 1 :=
        Complex.exp_int_mul_two_pi_mul_I d
      rw [← mul_one (Complex.exp (I * (d : ℂ) * ((-Real.pi : ℝ) : ℂ))), ← hexp1, ← Complex.exp_add]
      congr 1
      push_cast; ring
    rw [heq, sub_self]

lemma polynomial_coeff_fourier (Q : Polynomial ℝ) (m : ℕ) :
    Q.coeff m =
      (1 / (2 * Real.pi)) *
        (∫ θ in (-Real.pi)..Real.pi,
          Polynomial.aeval (Complex.exp (I * θ)) Q * Complex.exp (-I * (m : ℂ) * θ)).re := by
  have hexp : ∀ θ : ℝ,
      Polynomial.aeval (Complex.exp (I * θ)) Q * Complex.exp (-I * (m : ℂ) * θ) =
        ∑ k ∈ Finset.range (Q.natDegree + 1),
          ((Q.coeff k : ℝ) : ℂ) * Complex.exp (I * ((k : ℤ) - (m : ℤ) : ℤ) * θ) := by
    intro θ
    conv_lhs => rw [Q.as_sum_range]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.aeval_monomial]
    change ((Q.coeff k : ℝ) : ℂ) * Complex.exp (I * (θ : ℂ)) ^ k * Complex.exp (-I * (m : ℂ) * (θ : ℂ)) = _
    rw [mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    ((by fun_prop : Continuous _).intervalIntegrable _ _))]
  have hsum :
      ∑ k ∈ Finset.range (Q.natDegree + 1),
        ∫ θ in (-Real.pi)..Real.pi,
          ((Q.coeff k : ℝ) : ℂ) * Complex.exp (I * ((k : ℤ) - (m : ℤ) : ℤ) * θ) =
      ((Q.coeff m : ℝ) : ℂ) * (2 * Real.pi : ℂ) := by
    have hterm : ∀ k ∈ Finset.range (Q.natDegree + 1),
        ∫ θ in (-Real.pi)..Real.pi,
          ((Q.coeff k : ℝ) : ℂ) * Complex.exp (I * ((k : ℤ) - (m : ℤ) : ℤ) * θ) =
        if k = m then ((Q.coeff m : ℝ) : ℂ) * (2 * Real.pi : ℂ) else 0 := by
      intro k _
      rw [intervalIntegral.integral_const_mul, integral_cexp_int_mul_I]
      by_cases hkm : k = m
      · subst hkm; simp
      · have hne : (k : ℤ) - (m : ℤ) ≠ 0 := by omega
        rw [if_neg hne, if_neg hkm, mul_zero]
    rw [Finset.sum_congr rfl hterm]
    by_cases hm : m < Q.natDegree + 1
    · rw [Finset.sum_ite_eq' _ m, if_pos (Finset.mem_range.mpr hm)]
    · rw [Finset.sum_ite_eq' _ m, if_neg (by rw [Finset.mem_range]; exact hm)]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  rw [hsum]
  have hre : (((Q.coeff m : ℝ) : ℂ) * (2 * Real.pi : ℂ)).re = Q.coeff m * (2 * Real.pi) := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [hpi]

lemma gaussian_cos_integral {a : ℝ} (ha : 0 < a) (w : ℝ) :
    ∫ θ : ℝ, Real.exp (-a * θ ^ 2) * Real.cos (w * θ) =
      Real.sqrt (Real.pi / a) * Real.exp (-w ^ 2 / (4 * a)) := by
  have hb : (-(a : ℂ)).re < 0 := by simpa using ha
  have hcexp := integral_cexp_quadratic hb (I * (w : ℂ)) 0
  have hre_lhs : (∫ θ : ℝ, Complex.exp (-(a : ℂ) * (θ : ℂ) ^ 2 + I * (w : ℂ) * (θ : ℂ) + 0)).re =
      ∫ θ : ℝ, Real.exp (-a * θ ^ 2) * Real.cos (w * θ) := by
    have hint : Integrable (fun θ : ℝ => Complex.exp (-(a : ℂ) * (θ : ℂ) ^ 2 + I * (w : ℂ) * (θ : ℂ) + 0)) := by
      refine (integrable_exp_neg_mul_sq ha).mono' (by fun_prop) (Eventually.of_forall fun θ => ?_)
      rw [add_zero, Complex.exp_add, norm_mul,
        show -(a : ℂ) * (θ : ℂ) ^ 2 = ((-a * θ ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_exp_ofReal,
        show I * (w : ℂ) * (θ : ℂ) = ((w * θ : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    rw [show (∫ θ : ℝ, Complex.exp (-(a : ℂ) * (θ : ℂ) ^ 2 + I * (w : ℂ) * (θ : ℂ) + 0)).re =
        Complex.reCLM (∫ θ : ℝ, Complex.exp (-(a : ℂ) * (θ : ℂ) ^ 2 + I * (w : ℂ) * (θ : ℂ) + 0)) from rfl,
      ← Complex.reCLM.integral_comp_comm hint]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    change (Complex.exp (-(a : ℂ) * (θ : ℂ) ^ 2 + I * (w : ℂ) * (θ : ℂ) + 0)).re = _
    rw [add_zero, Complex.exp_add,
      show -(a : ℂ) * (θ : ℂ) ^ 2 = ((-a * θ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp,
      show I * (w : ℂ) * (θ : ℂ) = ((w * θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [← hre_lhs, hcexp]
  have harg1 : ((Real.pi : ℂ) / - -(a : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi / a) : ℝ) : ℂ) := by
    rw [neg_neg, ← Complex.ofReal_div, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    norm_num
  have harg2 : Complex.exp (0 - (I * (w : ℂ)) ^ 2 / (4 * -(a : ℂ))) =
      ((Real.exp (-w ^ 2 / (4 * a)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    rw [mul_pow, I_sq]
    have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    push_cast
    field_simp [ha']
    ring
  rw [harg1, harg2, ← Complex.ofReal_mul, Complex.ofReal_re]

lemma gaussian_moment_bound_pointwise (k : ℕ) (hk : k ≤ 5) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    |t| ^ k * Real.exp (-c * t ^ 2) ≤
      31 * (2 / c) ^ ((k : ℝ) / 2) * Real.exp (-(c / 2) * t ^ 2) := by
  set s := Real.sqrt (c / 2) * |t|
  have hs0 : 0 ≤ s := by positivity
  have hs_sq : s ^ 2 = (c / 2) * t ^ 2 := by
    dsimp only [s]
    rw [mul_pow, Real.sq_sqrt (by positivity), sq_abs]
  have hsk : s ^ k * Real.exp (-s ^ 2) ≤ 31 := by
    have he1 : s ^ 2 ≤ Real.exp (s ^ 2) := by linarith [Real.add_one_le_exp (s ^ 2)]
    have he2 : s ^ 4 ≤ 4 * Real.exp (s ^ 2) := by
      have h := Real.add_one_le_exp (s ^ 2 / 2)
      have hsq : (s ^ 2 / 2) ^ 2 ≤ Real.exp (s ^ 2 / 2) ^ 2 := by
        nlinarith [Real.exp_pos (s ^ 2 / 2), sq_nonneg s]
      rw [← Real.exp_nat_mul] at hsq
      have : (2 : ℕ) * (s ^ 2 / 2) = s ^ 2 := by push_cast; ring
      rw [this] at hsq
      linarith
    have he3 : s ^ 6 ≤ 27 * Real.exp (s ^ 2) := by
      have h := Real.add_one_le_exp (s ^ 2 / 3)
      have hcb : (s ^ 2 / 3) ^ 3 ≤ Real.exp (s ^ 2 / 3) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 3
      rw [← Real.exp_nat_mul] at hcb
      have : (3 : ℕ) * (s ^ 2 / 3) = s ^ 2 := by push_cast; ring
      rw [this] at hcb
      linarith
    have hpos_e : 0 < Real.exp (s ^ 2) := Real.exp_pos _
    have hbound : s ^ k ≤ 31 * Real.exp (s ^ 2) := by
      interval_cases k
      · simp; linarith [Real.one_le_exp (sq_nonneg s)]
      · have : s ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg (s - 1)]
        linarith [Real.one_le_exp (sq_nonneg s)]
      · linarith
      · have : s ^ 3 ≤ s ^ 2 + s ^ 4 := by nlinarith [sq_nonneg (s - 1), sq_nonneg s]
        linarith
      · linarith
      · have : s ^ 5 ≤ s ^ 4 + s ^ 6 := by nlinarith [sq_nonneg (s - 1), sq_nonneg (s ^ 2)]
        linarith
    rw [Real.exp_neg]
    calc s ^ k * (Real.exp (s ^ 2))⁻¹
        ≤ (31 * Real.exp (s ^ 2)) * (Real.exp (s ^ 2))⁻¹ :=
          mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = 31 := by field_simp [hpos_e.ne']
  have ht_eq : |t| = Real.sqrt (2 / c) * s := by
    dsimp only [s]
    rw [← mul_assoc, ← Real.sqrt_mul (by positivity)]
    have : (2 / c) * (c / 2) = 1 := by field_simp [hc.ne']
    rw [this, Real.sqrt_one, one_mul]
  have hpow_eq : (Real.sqrt (2 / c)) ^ k = (2 / c) ^ ((k : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; ring
  have hexp_split : Real.exp (-c * t ^ 2) = Real.exp (-s ^ 2) * Real.exp (-(c / 2) * t ^ 2) := by
    rw [← Real.exp_add, hs_sq]; congr 1; ring
  calc |t| ^ k * Real.exp (-c * t ^ 2)
      = (Real.sqrt (2 / c) * s) ^ k * (Real.exp (-s ^ 2) * Real.exp (-(c / 2) * t ^ 2)) := by
          rw [ht_eq, hexp_split]
    _ = (s ^ k * Real.exp (-s ^ 2)) * (2 / c) ^ ((k : ℝ) / 2) * Real.exp (-(c / 2) * t ^ 2) := by
          rw [mul_pow, hpow_eq]; ring
    _ ≤ 31 * (2 / c) ^ ((k : ℝ) / 2) * Real.exp (-(c / 2) * t ^ 2) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsk (by positivity)) (by positivity)

lemma gaussian_moment_integral_le (k : ℕ) (hk : k ≤ 5) {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ, |t| ^ k * Real.exp (-c * t ^ 2) ≤
      31 * (2 / c) ^ ((k : ℝ) / 2) * Real.sqrt (Real.pi / (c / 2)) := by
  have hint_rhs : Integrable (fun t : ℝ => 31 * (2 / c) ^ ((k : ℝ) / 2) * Real.exp (-(c / 2) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < c / 2)).const_mul _
  have hint_lhs : Integrable (fun t : ℝ => |t| ^ k * Real.exp (-c * t ^ 2)) :=
    hint_rhs.mono' (by fun_prop) (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact gaussian_moment_bound_pointwise k hk hc t)
  calc ∫ t : ℝ, |t| ^ k * Real.exp (-c * t ^ 2)
      ≤ ∫ t : ℝ, 31 * (2 / c) ^ ((k : ℝ) / 2) * Real.exp (-(c / 2) * t ^ 2) :=
        integral_mono hint_lhs hint_rhs (fun t => gaussian_moment_bound_pointwise k hk hc t)
    _ = 31 * (2 / c) ^ ((k : ℝ) / 2) * ∫ t : ℝ, Real.exp (-(c / 2) * t ^ 2) :=
        integral_const_mul _ _
    _ = 31 * (2 / c) ^ ((k : ℝ) / 2) * Real.sqrt (Real.pi / (c / 2)) := by
        rw [integral_gaussian (c / 2)]

lemma gaussian_sq_cos_integral {a : ℝ} (ha : 0 < a) (w : ℝ) :
    ∫ θ : ℝ, θ ^ 2 * Real.exp (-a * θ ^ 2) * Real.cos (w * θ) =
      ((1 - w ^ 2 / (2 * a)) / (2 * a)) * Real.sqrt (Real.pi / a) * Real.exp (-w ^ 2 / (4 * a)) := by
  -- Use complex FTC on `[-R, R]` and take `R -> +infty`!
  let f : ℝ → ℂ := fun θ => Complex.exp (-(a : ℂ) * (θ : ℂ) ^ 2 + I * (w : ℂ) * (θ : ℂ))
  have hf_norm : ∀ θ : ℝ, ‖f θ‖ = Real.exp (-a * θ ^ 2) := by
    intro θ
    dsimp only [f]
    rw [Complex.exp_add, norm_mul,
      show -(a : ℂ) * (θ : ℂ) ^ 2 = ((-a * θ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_ofReal,
      show I * (w : ℂ) * (θ : ℂ) = ((w * θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hf_int : Integrable f :=
    (integrable_exp_neg_mul_sq ha).mono' (by fun_prop) (Eventually.of_forall fun θ => (hf_norm θ).le)
  have hθf_int : Integrable (fun θ : ℝ => (θ : ℂ) * f θ) := by
    have hdom : Integrable (fun θ : ℝ => 31 * (2 / a) ^ ((1 : ℝ) / 2) * Real.exp (-(a / 2) * θ ^ 2)) :=
      (integrable_exp_neg_mul_sq (by positivity : 0 < a / 2)).const_mul _
    refine hdom.mono' (by fun_prop) (Eventually.of_forall fun θ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hf_norm θ]
    simpa using gaussian_moment_bound_pointwise 1 (by omega) ha θ
  have hθ2f_int : Integrable (fun θ : ℝ => (θ : ℂ) ^ 2 * f θ) := by
    have hdom : Integrable (fun θ : ℝ => 31 * (2 / a) ^ ((2 : ℝ) / 2) * Real.exp (-(a / 2) * θ ^ 2)) :=
      (integrable_exp_neg_mul_sq (by positivity : 0 < a / 2)).const_mul _
    refine hdom.mono' (by fun_prop) (Eventually.of_forall fun θ => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, hf_norm θ]
    simpa using gaussian_moment_bound_pointwise 2 (by omega) ha θ
  have hf_deriv : ∀ θ : ℝ, HasDerivAt f ((-2 * (a : ℂ) * (θ : ℂ) + I * (w : ℂ)) * f θ) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => -(a : ℂ) * (θ : ℂ) ^ 2 + I * (w : ℂ) * (θ : ℂ))
        (-2 * (a : ℂ) * (θ : ℂ) + I * (w : ℂ)) θ := by
      have ha1 : HasDerivAt (fun θ : ℝ => -(a : ℂ) * (θ : ℂ) ^ 2) (-2 * (a : ℂ) * (θ : ℂ)) θ := by
        refine (((hasDerivAt_id θ).ofReal_comp.pow 2).const_mul (-(a : ℂ))).congr_deriv ?_
        simp; ring
      have hb1 : HasDerivAt (fun θ : ℝ => I * (w : ℂ) * (θ : ℂ)) (I * (w : ℂ)) θ := by
        simpa using (hasDerivAt_id θ).ofReal_comp.const_mul (I * (w : ℂ))
      exact ha1.fun_add hb1
    refine h1.cexp.congr_deriv ?_
    dsimp only [f]; ring
  have hθf_deriv : ∀ θ : ℝ,
      HasDerivAt (fun θ : ℝ => (θ : ℂ) * f θ)
        ((1 - 2 * (a : ℂ) * (θ : ℂ) ^ 2 + I * (w : ℂ) * (θ : ℂ)) * f θ) θ := by
    intro θ
    refine ((hasDerivAt_id θ).ofReal_comp.fun_mul (hf_deriv θ)).congr_deriv ?_
    simp; ring
  -- Integral of `f'` is 0 because `f(±R) -> 0`
  have hf_tendsto : Tendsto f atTop (𝓝 0) ∧ Tendsto f atBot (𝓝 0) := by
    have hsq_top : Tendsto (fun θ : ℝ => -a * θ ^ 2) atTop atBot := by
      have h1 : Tendsto (fun θ : ℝ => θ ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
      exact Tendsto.const_mul_atTop_of_neg (by linarith) h1
    have hsq_bot : Tendsto (fun θ : ℝ => -a * θ ^ 2) atBot atBot := by
      have h1 : Tendsto (fun θ : ℝ => θ ^ 2) atBot atTop := by
        have := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0) :
          Tendsto (fun x : ℝ => x ^ 2) atTop atTop).comp tendsto_neg_atBot_atTop
        simpa [Function.comp_def, neg_sq] using this
      exact Tendsto.const_mul_atTop_of_neg (by linarith) h1
    constructor
    · exact tendsto_zero_iff_norm_tendsto_zero.mpr (by
        simp_rw [hf_norm]; exact Real.tendsto_exp_atBot.comp hsq_top)
    · exact tendsto_zero_iff_norm_tendsto_zero.mpr (by
        simp_rw [hf_norm]; exact Real.tendsto_exp_atBot.comp hsq_bot)
  have hθf_tendsto : Tendsto (fun θ : ℝ => (θ : ℂ) * f θ) atTop (𝓝 0) ∧
      Tendsto (fun θ : ℝ => (θ : ℂ) * f θ) atBot (𝓝 0) := by
    have hbound : ∀ θ : ℝ, ‖(θ : ℂ) * f θ‖ ≤ 31 * (2 / a) ^ ((1 : ℝ) / 2) * Real.exp (-(a / 2) * θ ^ 2) := by
      intro θ
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hf_norm θ]
      simpa using gaussian_moment_bound_pointwise 1 (by omega) ha θ
    have he_top : Tendsto (fun θ : ℝ => 31 * (2 / a) ^ ((1 : ℝ) / 2) * Real.exp (-(a / 2) * θ ^ 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun θ : ℝ => -(a / 2) * θ ^ 2) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by linarith) (tendsto_pow_atTop (by norm_num))
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (31 * (2 / a) ^ ((1 : ℝ) / 2))
    have he_bot : Tendsto (fun θ : ℝ => 31 * (2 / a) ^ ((1 : ℝ) / 2) * Real.exp (-(a / 2) * θ ^ 2)) atBot (𝓝 0) := by
      have h1 : Tendsto (fun θ : ℝ => -(a / 2) * θ ^ 2) atBot atBot := by
        have hp : Tendsto (fun θ : ℝ => θ ^ 2) atBot atTop := by
          have := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0) :
            Tendsto (fun x : ℝ => x ^ 2) atTop atTop).comp tendsto_neg_atBot_atTop
          simpa [Function.comp_def, neg_sq] using this
        exact Tendsto.const_mul_atTop_of_neg (by linarith) hp
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (31 * (2 / a) ^ ((1 : ℝ) / 2))
    constructor
    · exact tendsto_zero_iff_norm_tendsto_zero.mpr
        (squeeze_zero (fun θ => norm_nonneg _) hbound he_top)
    · exact tendsto_zero_iff_norm_tendsto_zero.mpr
        (squeeze_zero (fun θ => norm_nonneg _) hbound he_bot)
  have hint1_zero : ∫ θ : ℝ, (-2 * (a : ℂ) * (θ : ℂ) + I * (w : ℂ)) * f θ = 0 := by
    have hint' : Integrable (fun θ : ℝ => (-2 * (a : ℂ) * (θ : ℂ) + I * (w : ℂ)) * f θ) := by
      have : (fun θ : ℝ => (-2 * (a : ℂ) * (θ : ℂ) + I * (w : ℂ)) * f θ) =
          fun θ : ℝ => (-2 * (a : ℂ)) * ((θ : ℂ) * f θ) + (I * (w : ℂ)) * f θ := by
        funext θ; ring
      rw [this]
      exact (hθf_int.const_mul _).add (hf_int.const_mul _)
    simpa using integral_of_hasDerivAt_of_tendsto hf_deriv hint' hf_tendsto.2 hf_tendsto.1
  have hint2_zero : ∫ θ : ℝ, (1 - 2 * (a : ℂ) * (θ : ℂ) ^ 2 + I * (w : ℂ) * (θ : ℂ)) * f θ = 0 := by
    have hint' : Integrable (fun θ : ℝ => (1 - 2 * (a : ℂ) * (θ : ℂ) ^ 2 + I * (w : ℂ) * (θ : ℂ)) * f θ) := by
      have : (fun θ : ℝ => (1 - 2 * (a : ℂ) * (θ : ℂ) ^ 2 + I * (w : ℂ) * (θ : ℂ)) * f θ) =
          fun θ : ℝ => f θ + (-2 * (a : ℂ)) * ((θ : ℂ) ^ 2 * f θ) + (I * (w : ℂ)) * ((θ : ℂ) * f θ) := by
        funext θ; ring
      rw [this]
      exact (hf_int.add (hθ2f_int.const_mul _)).add (hθf_int.const_mul _)
    simpa using integral_of_hasDerivAt_of_tendsto hθf_deriv hint' hθf_tendsto.2 hθf_tendsto.1
  -- Expand both zero integrals into linear equations in `I0, I1, I2`!
  have heq1 : (-2 * (a : ℂ)) * (∫ θ : ℝ, (θ : ℂ) * f θ) + (I * (w : ℂ)) * (∫ θ : ℝ, f θ) = 0 := by
    have hfun : (fun θ : ℝ => (-2 * (a : ℂ) * (θ : ℂ) + I * (w : ℂ)) * f θ) =
        fun θ : ℝ => (-2 * (a : ℂ)) * ((θ : ℂ) * f θ) + (I * (w : ℂ)) * f θ := funext fun θ => by ring
    rw [hfun] at hint1_zero
    have hadd := integral_add (hθf_int.const_mul (-2 * (a : ℂ))) (hf_int.const_mul (I * (w : ℂ)))
    rw [integral_const_mul, integral_const_mul] at hadd
    exact hadd.symm.trans hint1_zero
  have heq2 : (∫ θ : ℝ, f θ) + (-2 * (a : ℂ)) * (∫ θ : ℝ, (θ : ℂ) ^ 2 * f θ) +
      (I * (w : ℂ)) * (∫ θ : ℝ, (θ : ℂ) * f θ) = 0 := by
    have hfun : (fun θ : ℝ => (1 - 2 * (a : ℂ) * (θ : ℂ) ^ 2 + I * (w : ℂ) * (θ : ℂ)) * f θ) =
        fun θ : ℝ => (f θ + (-2 * (a : ℂ)) * ((θ : ℂ) ^ 2 * f θ)) + (I * (w : ℂ)) * ((θ : ℂ) * f θ) :=
      funext fun θ => by ring
    rw [hfun] at hint2_zero
    have hadd1 := integral_add (hf_int.add (hθ2f_int.const_mul (-2 * (a : ℂ)))) (hθf_int.const_mul (I * (w : ℂ)))
    have hadd2 := integral_add hf_int (hθ2f_int.const_mul (-2 * (a : ℂ)))
    simp only [Pi.add_apply] at hadd1 hadd2
    rw [integral_const_mul] at hadd1 hadd2
    rw [hadd1, hadd2] at hint2_zero
    exact hint2_zero
  have ha_ne : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have ha_c : (2 * (a : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) ha_ne
  have hI1 : ∫ θ : ℝ, (θ : ℂ) * f θ = (I * (w : ℂ) / (2 * (a : ℂ))) * ∫ θ : ℝ, f θ := by
    apply mul_left_cancel₀ ha_c
    have hsimp : 2 * (a : ℂ) * (I * (w : ℂ) / (2 * (a : ℂ)) * ∫ θ : ℝ, f θ) =
        I * (w : ℂ) * ∫ θ : ℝ, f θ := by field_simp [ha_c, ha_ne]
    rw [hsimp]
    linear_combination -heq1
  have hI2 : ∫ θ : ℝ, (θ : ℂ) ^ 2 * f θ =
      (((1 - w ^ 2 / (2 * a)) / (2 * a) : ℝ) : ℂ) * ∫ θ : ℝ, f θ := by
    rw [hI1] at heq2
    have hI2sq : I ^ 2 = -1 := I_sq
    have heq2' : (2 * (a : ℂ)) * ((∫ θ : ℝ, f θ) + (-2 * (a : ℂ)) * (∫ θ : ℝ, (θ : ℂ) ^ 2 * f θ) +
        (I * (w : ℂ)) * ((I * (w : ℂ) / (2 * (a : ℂ))) * ∫ θ : ℝ, f θ)) = 0 := by
      rw [heq2, mul_zero]
    have hclear : (2 * (a : ℂ)) * ((I * (w : ℂ)) * ((I * (w : ℂ) / (2 * (a : ℂ))) * ∫ θ : ℝ, f θ)) =
        I ^ 2 * (w : ℂ) ^ 2 * ∫ θ : ℝ, f θ := by field_simp [ha_c, ha_ne]
    have heq2'' : (2 * (a : ℂ)) * (∫ θ : ℝ, f θ) - (2 * (a : ℂ)) ^ 2 * (∫ θ : ℝ, (θ : ℂ) ^ 2 * f θ) +
        I ^ 2 * (w : ℂ) ^ 2 * ∫ θ : ℝ, f θ = 0 := by
      rw [mul_add, mul_add, hclear] at heq2'
      linear_combination heq2'
    apply mul_left_cancel₀ (pow_ne_zero 2 ha_c)
    have hrhs : (2 * (a : ℂ)) ^ 2 * ((((1 - w ^ 2 / (2 * a)) / (2 * a) : ℝ) : ℂ) * ∫ θ : ℝ, f θ) =
        (2 * (a : ℂ) - (w : ℂ) ^ 2) * ∫ θ : ℝ, f θ := by
      push_cast; field_simp [ha_c, ha_ne]
    rw [hrhs]
    linear_combination -heq2'' + (w : ℂ) ^ 2 * (∫ θ : ℝ, f θ) * hI2sq
  -- Take real part!
  have hre_I2 : (∫ θ : ℝ, (θ : ℂ) ^ 2 * f θ).re =
      ∫ θ : ℝ, θ ^ 2 * Real.exp (-a * θ ^ 2) * Real.cos (w * θ) := by
    rw [show (∫ θ : ℝ, (θ : ℂ) ^ 2 * f θ).re = Complex.reCLM (∫ θ : ℝ, (θ : ℂ) ^ 2 * f θ) from rfl,
      ← Complex.reCLM.integral_comp_comm hθ2f_int]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    change ((θ : ℂ) ^ 2 * f θ).re = _
    dsimp only [f]
    rw [Complex.exp_add,
      show -(a : ℂ) * (θ : ℂ) ^ 2 = ((-a * θ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp,
      show I * (w : ℂ) * (θ : ℂ) = ((w * θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← mul_assoc, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hre_I0 : (∫ θ : ℝ, f θ).re = Real.sqrt (Real.pi / a) * Real.exp (-w ^ 2 / (4 * a)) := by
    rw [show (∫ θ : ℝ, f θ).re = Complex.reCLM (∫ θ : ℝ, f θ) from rfl,
      ← Complex.reCLM.integral_comp_comm hf_int]
    have heq_re : (fun θ : ℝ => Complex.reCLM (f θ)) = fun θ => Real.exp (-a * θ ^ 2) * Real.cos (w * θ) := by
      funext θ; change (f θ).re = _; dsimp only [f]
      rw [Complex.exp_add,
        show -(a : ℂ) * (θ : ℂ) ^ 2 = ((-a * θ ^ 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp,
        show I * (w : ℂ) * (θ : ℂ) = ((w * θ : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [heq_re, gaussian_cos_integral ha w]
  rw [← hre_I2, hI2, Complex.re_ofReal_mul, hre_I0]
  ring

/-!
## 3. Tilted distribution `P_t`, explicit uniform bounds on `[t_min, t_max]`, and local Fourier estimates
-/

noncomputable def evalP (P : Polynomial ℝ) (t : ℝ) : ℝ := P.eval t

noncomputable def prob (P : Polynomial ℝ) (t : ℝ) (k : ℕ) : ℝ :=
  P.coeff k * t ^ k / P.eval t

noncomputable def meanP (n : ℕ) (P : Polynomial ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (k : ℝ) * prob P t k

noncomputable def varP (n : ℕ) (P : Polynomial ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ((k : ℝ) - meanP n P t) ^ 2 * prob P t k

noncomputable def charFun (n : ℕ) (P : Polynomial ℝ) (t θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), ((prob P t k : ℝ) : ℂ) * Complex.exp (I * (((k : ℝ) - meanP n P t : ℝ) : ℂ) * θ)

lemma evalP_eq_sum {n : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree = n) (t : ℝ) :
    P.eval t = ∑ k ∈ Finset.range (n + 1), P.coeff k * t ^ k := by
  rw [Polynomial.eval_eq_sum_range, hdeg]

lemma evalP_pos {n : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {t : ℝ} (ht : 0 < t) :
    0 < P.eval t := by
  rw [evalP_eq_sum hdeg t]
  have hmem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have h0 : 0 < P.coeff 0 * t ^ 0 := by simpa using hpos 0 (Nat.zero_le n)
  exact lt_of_lt_of_le h0 (Finset.single_le_sum (fun k hk => by
    have : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact mul_nonneg (hpos k this).le (pow_nonneg ht.le k)) hmem)

lemma prob_pos {n : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {t : ℝ} (ht : 0 < t) {k : ℕ} (hk : k ≤ n) :
    0 < prob P t k :=
  div_pos (mul_pos (hpos k hk) (pow_pos ht k)) (evalP_pos hdeg hpos ht)

lemma sum_prob_eq_one {n : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {t : ℝ} (ht : 0 < t) :
    ∑ k ∈ Finset.range (n + 1), prob P t k = 1 := by
  unfold prob
  rw [← Finset.sum_div, ← evalP_eq_sum hdeg t, div_self (evalP_pos hdeg hpos ht).ne']

lemma meanP_bounds {n : ℕ} {P : Polynomial ℝ} (hn : 2 ≤ n) (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {t : ℝ} (ht : 0 < t) :
    0 < meanP n P t ∧ meanP n P t < (n : ℝ) := by
  unfold meanP
  have hsum1 := sum_prob_eq_one hdeg hpos ht
  constructor
  · have hmem : 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have h1 : 0 < ((1 : ℕ) : ℝ) * prob P t 1 := by simpa using prob_pos hdeg hpos ht (by omega)
    exact lt_of_lt_of_le h1 (Finset.single_le_sum (fun k hk =>
      mul_nonneg (Nat.cast_nonneg k) (prob_pos hdeg hpos ht (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).le) hmem)
  · calc ∑ k ∈ Finset.range (n + 1), (k : ℝ) * prob P t k
        < ∑ k ∈ Finset.range (n + 1), (n : ℝ) * prob P t k := by
          refine Finset.sum_lt_sum ?_ ?_
          · intro k hk
            have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            exact mul_le_mul_of_nonneg_right hkn (prob_pos hdeg hpos ht (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).le
          · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
            simp only [Nat.cast_zero, zero_mul]
            exact mul_pos (by exact_mod_cast (show 0 < n by omega)) (prob_pos hdeg hpos ht (Nat.zero_le n))
      _ = (n : ℝ) * ∑ k ∈ Finset.range (n + 1), prob P t k := (Finset.mul_sum _ _ _).symm
      _ = (n : ℝ) := by rw [hsum1, mul_one]

lemma meanP_hasDerivAt {n : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (meanP n P) (varP n P t / t) t := by
  have hmean_eq : ∀ s : ℝ, meanP n P s =
      (∑ k ∈ Finset.range (n + 1), (k : ℝ) * P.coeff k * s ^ k) / P.eval s := by
    intro s
    unfold meanP prob
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hfun : meanP n P = fun s =>
      (∑ k ∈ Finset.range (n + 1), (k : ℝ) * P.coeff k * s ^ k) /
        (∑ k ∈ Finset.range (n + 1), P.coeff k * s ^ k) := by
    funext s; rw [hmean_eq s, evalP_eq_sum hdeg s]
  rw [hfun]
  have hd_num : HasDerivAt (fun s : ℝ => ∑ k ∈ Finset.range (n + 1), (k : ℝ) * P.coeff k * s ^ k)
      (∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2 * P.coeff k * t ^ (k - 1)) t := by
    refine HasDerivAt.fun_sum fun k _ => ?_
    refine ((hasDerivAt_pow k t).const_mul ((k : ℝ) * P.coeff k)).congr_deriv ?_; ring
  have hd_den : HasDerivAt (fun s : ℝ => ∑ k ∈ Finset.range (n + 1), P.coeff k * s ^ k)
      (∑ k ∈ Finset.range (n + 1), (k : ℝ) * P.coeff k * t ^ (k - 1)) t := by
    refine HasDerivAt.fun_sum fun k _ => ?_
    refine ((hasDerivAt_pow k t).const_mul (P.coeff k)).congr_deriv ?_; ring
  have hEv : 0 < P.eval t := evalP_pos hdeg hpos ht
  have hden_ne : (∑ k ∈ Finset.range (n + 1), P.coeff k * t ^ k) ≠ 0 := by
    rw [← evalP_eq_sum hdeg t]; exact hEv.ne'
  refine (hd_num.fun_div hd_den hden_ne).congr_deriv ?_
  rw [← evalP_eq_sum hdeg t]
  have hvar_exp : varP n P t =
      (∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2 * prob P t k) - meanP n P t ^ 2 := by
    unfold varP
    have h1 : ∀ k ∈ Finset.range (n + 1),
        ((k : ℝ) - meanP n P t) ^ 2 * prob P t k =
          (k : ℝ) ^ 2 * prob P t k - 2 * meanP n P t * ((k : ℝ) * prob P t k) +
            meanP n P t ^ 2 * prob P t k := fun k _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, sum_prob_eq_one hdeg hpos ht]
    change _ - 2 * meanP n P t * meanP n P t + _ = _
    ring
  have ht_sum1 : t * ∑ k ∈ Finset.range (n + 1), (k : ℝ) * P.coeff k * t ^ (k - 1) =
      ∑ k ∈ Finset.range (n + 1), (k : ℝ) * P.coeff k * t ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    cases k with
    | zero => simp
    | succ k' => simp only [Nat.add_sub_cancel]; rw [pow_succ]; ring
  have ht_sum2 : t * ∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2 * P.coeff k * t ^ (k - 1) =
      ∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2 * P.coeff k * t ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    cases k with
    | zero => simp
    | succ k' => simp only [Nat.add_sub_cancel]; rw [pow_succ]; ring
  rw [hvar_exp, hmean_eq t]
  have hsum2_prob : ∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2 * prob P t k =
      (∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2 * P.coeff k * t ^ k) / P.eval t := by
    unfold prob; rw [Finset.sum_div]; refine Finset.sum_congr rfl fun k _ => by ring
  rw [hsum2_prob]
  field_simp [hEv.ne', ht.ne']
  rw [← ht_sum1, ← ht_sum2]
  ring

lemma varP_bounds {n : ℕ} {P : Polynomial ℝ} (hn : 2 ≤ n) (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {t : ℝ} (ht : 0 < t) :
    min (prob P t 0) (prob P t 1) / 2 ≤ varP n P t ∧ varP n P t ≤ (n : ℝ) ^ 2 := by
  have hsum1 := sum_prob_eq_one hdeg hpos ht
  have hmb := meanP_bounds hn hdeg hpos ht
  constructor
  · unfold varP
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (n + 1) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
    have hle : ∑ k ∈ ({0, 1} : Finset ℕ), ((k : ℝ) - meanP n P t) ^ 2 * prob P t k ≤
        ∑ k ∈ Finset.range (n + 1), ((k : ℝ) - meanP n P t) ^ 2 * prob P t k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ =>
        mul_nonneg (sq_nonneg _) (prob_pos hdeg hpos ht (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).le
    rw [Finset.sum_pair (by norm_num)] at hle
    simp only [Nat.cast_zero, Nat.cast_one] at hle
    have hmin0 : min (prob P t 0) (prob P t 1) ≤ prob P t 0 := min_le_left _ _
    have hmin1 : min (prob P t 0) (prob P t 1) ≤ prob P t 1 := min_le_right _ _
    have hsq_half : (1 : ℝ) / 2 ≤ (0 - meanP n P t) ^ 2 + (1 - meanP n P t) ^ 2 := by
      nlinarith [sq_nonneg (meanP n P t - 1 / 2)]
    have hmin_nn : 0 ≤ min (prob P t 0) (prob P t 1) :=
      le_min (prob_pos hdeg hpos ht (by omega)).le (prob_pos hdeg hpos ht (by omega)).le
    nlinarith [sq_nonneg (0 - meanP n P t), sq_nonneg (1 - meanP n P t)]
  · unfold varP
    calc ∑ k ∈ Finset.range (n + 1), ((k : ℝ) - meanP n P t) ^ 2 * prob P t k
        ≤ ∑ k ∈ Finset.range (n + 1), (n : ℝ) ^ 2 * prob P t k := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have hsq : ((k : ℝ) - meanP n P t) ^ 2 ≤ (n : ℝ) ^ 2 := by
            nlinarith [hmb.1, hmb.2, Nat.cast_nonneg (α := ℝ) k]
          exact mul_le_mul_of_nonneg_right hsq
            (prob_pos hdeg hpos ht (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).le
      _ = (n : ℝ) ^ 2 * ∑ k ∈ Finset.range (n + 1), prob P t k := (Finset.mul_sum _ _ _).symm
      _ = (n : ℝ) ^ 2 := by rw [hsum1, mul_one]

lemma charFun_eq_poly {n : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree = n)
    (_hpos : ∀ i ≤ n, 0 < P.coeff i) {t : ℝ} (_ht : 0 < t) (θ : ℝ) :
    charFun n P t θ =
      (Polynomial.aeval ((t : ℂ) * Complex.exp (I * θ)) P / ((P.eval t : ℝ) : ℂ)) *
        Complex.exp (-I * (meanP n P t : ℂ) * θ) := by
  unfold charFun prob
  have hP : Polynomial.aeval ((t : ℂ) * Complex.exp (I * θ)) P =
      ∑ k ∈ Finset.range (n + 1), ((P.coeff k * t ^ k : ℝ) : ℂ) * Complex.exp (I * (k : ℂ) * θ) := by
    conv_lhs => rw [P.as_sum_range, hdeg]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.aeval_monomial]
    change ((P.coeff k : ℝ) : ℂ) * ((t : ℂ) * Complex.exp (I * (θ : ℂ))) ^ k = _
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast; ring
  rw [hP, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_div, div_mul_eq_mul_div, div_mul_eq_mul_div]
  conv_rhs => rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

lemma charFun_norm_le_one {n : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {t : ℝ} (ht : 0 < t) (θ : ℝ) :
    ‖charFun n P t θ‖ ≤ 1 := by
  unfold charFun
  calc ‖∑ k ∈ Finset.range (n + 1), ((prob P t k : ℝ) : ℂ) *
          Complex.exp (I * (((k : ℝ) - meanP n P t : ℝ) : ℂ) * θ)‖
      ≤ ∑ k ∈ Finset.range (n + 1), ‖((prob P t k : ℝ) : ℂ) *
          Complex.exp (I * (((k : ℝ) - meanP n P t : ℝ) : ℂ) * θ)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n + 1), prob P t k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hp := prob_pos hdeg hpos ht (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp,
          show I * (((k : ℝ) - meanP n P t : ℝ) : ℂ) * (θ : ℂ) =
            ((((k : ℝ) - meanP n P t) * θ : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
    _ = 1 := sum_prob_eq_one hdeg hpos ht

lemma charFun_outer_bound {n : ℕ} {P : Polynomial ℝ} (hn : 2 ≤ n) (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {t : ℝ} (ht : 0 < t) {θ₀ θ : ℝ}
    (hθ₀_pos : 0 < θ₀) (hθ₀_le : θ₀ ≤ Real.pi) (hθ_lo : θ₀ ≤ |θ|) (hθ_hi : |θ| ≤ Real.pi) :
    ‖charFun n P t θ‖ ≤ 1 - prob P t 0 * prob P t 1 * (1 - Real.cos θ₀) := by
  -- Note `‖charFun n P t θ‖ = ‖∑_{k=0}^n p_k e^{i k θ}‖ <= ‖p_0 + p_1 e^{i θ}‖ + (1 - p_0 - p_1)`!
  have hnorm_eq : ‖charFun n P t θ‖ =
      ‖∑ k ∈ Finset.range (n + 1), ((prob P t k : ℝ) : ℂ) * Complex.exp (I * (k : ℂ) * θ)‖ := by
    have hmul : charFun n P t θ =
        (∑ k ∈ Finset.range (n + 1), ((prob P t k : ℝ) : ℂ) * Complex.exp (I * (k : ℂ) * θ)) *
          Complex.exp (-I * (meanP n P t : ℂ) * θ) := by
      unfold charFun
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_rhs => rw [mul_assoc, ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [hmul, norm_mul,
      show -I * (meanP n P t : ℂ) * (θ : ℂ) = ((-(meanP n P t * θ) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [hnorm_eq]
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (n + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
  have hsplit :
      ∑ k ∈ Finset.range (n + 1), ((prob P t k : ℝ) : ℂ) * Complex.exp (I * (k : ℂ) * θ) =
      (((prob P t 0 : ℝ) : ℂ) + ((prob P t 1 : ℝ) : ℂ) * Complex.exp (I * θ)) +
        ∑ k ∈ (Finset.range (n + 1)) \ {0, 1}, ((prob P t k : ℝ) : ℂ) * Complex.exp (I * (k : ℂ) * θ) := by
    conv_lhs => rw [← Finset.union_sdiff_of_subset hsub, Finset.sum_union Finset.disjoint_sdiff]
    congr 1
    rw [Finset.sum_pair (by norm_num)]
    simp
  rw [hsplit]
  have hp0 : 0 < prob P t 0 := prob_pos hdeg hpos ht (by omega)
  have hp1 : 0 < prob P t 1 := prob_pos hdeg hpos ht (by omega)
  have hrest_sum : ∑ k ∈ (Finset.range (n + 1)) \ {0, 1}, prob P t k = 1 - prob P t 0 - prob P t 1 := by
    have h1 := sum_prob_eq_one hdeg hpos ht
    rw [← Finset.union_sdiff_of_subset hsub, Finset.sum_union Finset.disjoint_sdiff,
      Finset.sum_pair (by norm_num)] at h1
    linarith
  have hrest_norm :
      ‖∑ k ∈ (Finset.range (n + 1)) \ {0, 1}, ((prob P t k : ℝ) : ℂ) * Complex.exp (I * (k : ℂ) * θ)‖ ≤
        1 - prob P t 0 - prob P t 1 := by
    calc _ ≤ ∑ k ∈ (Finset.range (n + 1)) \ {0, 1},
              ‖((prob P t k : ℝ) : ℂ) * Complex.exp (I * (k : ℂ) * θ)‖ := norm_sum_le _ _
      _ = ∑ k ∈ (Finset.range (n + 1)) \ {0, 1}, prob P t k := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hkr := (Finset.mem_sdiff.mp hk).1
          have hp := prob_pos hdeg hpos ht (Nat.lt_succ_iff.mp (Finset.mem_range.mp hkr))
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp,
            show I * (k : ℂ) * (θ : ℂ) = (((k : ℝ) * θ : ℝ) : ℂ) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, mul_one]
      _ = 1 - prob P t 0 - prob P t 1 := hrest_sum
  have hcos_le : Real.cos θ ≤ Real.cos θ₀ := by
    have habs : Real.cos θ = Real.cos |θ| := by
      rcases le_total 0 θ with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, Real.cos_neg]
    rw [habs]
    exact Real.strictAntiOn_cos.antitoneOn ⟨hθ₀_pos.le, hθ₀_le⟩ ⟨by linarith, hθ_hi⟩ hθ_lo
  have hpair_sq : ‖((prob P t 0 : ℝ) : ℂ) + ((prob P t 1 : ℝ) : ℂ) * Complex.exp (I * θ)‖ ^ 2 =
      (prob P t 0 + prob P t 1) ^ 2 - 2 * prob P t 0 * prob P t 1 * (1 - Real.cos θ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hexp : Complex.exp (I * (θ : ℂ)) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
      rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    rw [hexp]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.add_im, Complex.mul_im,
      zero_mul, add_zero, zero_add]
    have hsc := Real.sin_sq_add_cos_sq θ
    linear_combination (prob P t 1) ^ 2 * hsc
  have hp01_le : prob P t 0 + prob P t 1 ≤ 1 := by
    have : 0 ≤ ∑ k ∈ (Finset.range (n + 1)) \ {0, 1}, prob P t k :=
      Finset.sum_nonneg fun k hk =>
        (prob_pos hdeg hpos ht (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_sdiff.mp hk).1))).le
    linarith
  have hpair_le : ‖((prob P t 0 : ℝ) : ℂ) + ((prob P t 1 : ℝ) : ℂ) * Complex.exp (I * θ)‖ ≤
      prob P t 0 + prob P t 1 - prob P t 0 * prob P t 1 * (1 - Real.cos θ₀) := by
    have hrhs_nn : 0 ≤ prob P t 0 + prob P t 1 - prob P t 0 * prob P t 1 * (1 - Real.cos θ₀) := by
      have h1 : 1 - Real.cos θ₀ ≤ 2 := by linarith [Real.neg_one_le_cos θ₀]
      have h2 : 2 * prob P t 0 * prob P t 1 ≤ prob P t 0 + prob P t 1 := by nlinarith
      nlinarith [mul_pos hp0 hp1]
    have hsq_le : ‖((prob P t 0 : ℝ) : ℂ) + ((prob P t 1 : ℝ) : ℂ) * Complex.exp (I * θ)‖ ^ 2 ≤
        (prob P t 0 + prob P t 1 - prob P t 0 * prob P t 1 * (1 - Real.cos θ₀)) ^ 2 := by
      rw [hpair_sq]
      have hdiff_nn : 0 ≤ 1 - Real.cos θ₀ := by linarith [Real.cos_le_one θ₀]
      have hd_nn : 0 ≤ prob P t 0 * prob P t 1 * (1 - Real.cos θ₀) :=
        mul_nonneg (mul_pos hp0 hp1).le hdiff_nn
      have hle1 : (prob P t 0 + prob P t 1) * (prob P t 0 * prob P t 1 * (1 - Real.cos θ₀)) ≤
          prob P t 0 * prob P t 1 * (1 - Real.cos θ₀) := by nlinarith
      have hle2 : prob P t 0 * prob P t 1 * (1 - Real.cos θ₀) ≤
          prob P t 0 * prob P t 1 * (1 - Real.cos θ) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (mul_pos hp0 hp1).le
      nlinarith [sq_nonneg (prob P t 0 * prob P t 1 * (1 - Real.cos θ₀))]
    nlinarith [norm_nonneg (((prob P t 0 : ℝ) : ℂ) + ((prob P t 1 : ℝ) : ℂ) * Complex.exp (I * θ))]
  calc ‖(((prob P t 0 : ℝ) : ℂ) + ((prob P t 1 : ℝ) : ℂ) * Complex.exp (I * θ)) +
          ∑ k ∈ (Finset.range (n + 1)) \ {0, 1}, ((prob P t k : ℝ) : ℂ) * Complex.exp (I * (k : ℂ) * θ)‖
      ≤ ‖((prob P t 0 : ℝ) : ℂ) + ((prob P t 1 : ℝ) : ℂ) * Complex.exp (I * θ)‖ +
        ‖∑ k ∈ (Finset.range (n + 1)) \ {0, 1}, ((prob P t k : ℝ) : ℂ) * Complex.exp (I * (k : ℂ) * θ)‖ :=
        norm_add_le _ _
    _ ≤ (prob P t 0 + prob P t 1 - prob P t 0 * prob P t 1 * (1 - Real.cos θ₀)) +
        (1 - prob P t 0 - prob P t 1) := add_le_add hpair_le hrest_norm
    _ = 1 - prob P t 0 * prob P t 1 * (1 - Real.cos θ₀) := by ring

lemma charFun_local_approx {n : ℕ} {P : Polynomial ℝ} (hn : 2 ≤ n) (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {t : ℝ} (ht : 0 < t) {θ : ℝ} (hθ : |θ| ≤ 1) :
    ‖charFun n P t θ - ((Real.exp (-(varP n P t / 2) * θ ^ 2) : ℝ) : ℂ)‖ ≤
      ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * |θ| ^ 3 := by
  have hsum1 := sum_prob_eq_one hdeg hpos ht
  have hmb := meanP_bounds hn hdeg hpos ht
  have hvb := varP_bounds hn hdeg hpos ht
  -- Expand `charFun n P t θ - (1 - varP/2 * θ^2)`
  have hmean_zero : ∑ k ∈ Finset.range (n + 1), ((k : ℝ) - meanP n P t) * prob P t k = 0 := by
    have h1 : ∀ k ∈ Finset.range (n + 1),
        ((k : ℝ) - meanP n P t) * prob P t k = (k : ℝ) * prob P t k - meanP n P t * prob P t k :=
      fun k _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum1, mul_one]
    unfold meanP; ring
  have hchar_quad :
      charFun n P t θ - ((1 - varP n P t / 2 * θ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ Finset.range (n + 1),
        ((prob P t k : ℝ) : ℂ) *
          (Complex.exp (I * ((((k : ℝ) - meanP n P t) * θ : ℝ) : ℂ)) -
            (1 + I * ((((k : ℝ) - meanP n P t) * θ : ℝ) : ℂ) -
              ((((k : ℝ) - meanP n P t) * θ : ℝ) : ℂ) ^ 2 / 2)) := by
    unfold charFun
    have h1 :
        ∑ k ∈ Finset.range (n + 1),
          ((prob P t k : ℝ) : ℂ) *
            (1 + I * ((((k : ℝ) - meanP n P t) * θ : ℝ) : ℂ) -
              ((((k : ℝ) - meanP n P t) * θ : ℝ) : ℂ) ^ 2 / 2) =
        ((1 - varP n P t / 2 * θ ^ 2 : ℝ) : ℂ) := by
      have hterm : ∀ k ∈ Finset.range (n + 1),
          ((prob P t k : ℝ) : ℂ) *
            (1 + I * ((((k : ℝ) - meanP n P t) * θ : ℝ) : ℂ) -
              ((((k : ℝ) - meanP n P t) * θ : ℝ) : ℂ) ^ 2 / 2) =
          ((prob P t k : ℝ) : ℂ) +
            I * (θ : ℂ) * ((((k : ℝ) - meanP n P t) * prob P t k : ℝ) : ℂ) -
            ((θ ^ 2 / 2 : ℝ) : ℂ) * ((((k : ℝ) - meanP n P t) ^ 2 * prob P t k : ℝ) : ℂ) := by
        intro k _; push_cast; ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Complex.ofReal_sum, ← Complex.ofReal_sum,
        ← Complex.ofReal_sum, hsum1, hmean_zero]
      change (1 : ℂ) + _ - _ * ((varP n P t : ℝ) : ℂ) = _
      push_cast; ring
    rw [← h1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_sub]; congr 2; congr 1; push_cast; ring
  have hE1 : ‖charFun n P t θ - ((1 - varP n P t / 2 * θ ^ 2 : ℝ) : ℂ)‖ ≤ (n : ℝ) ^ 3 * |θ| ^ 3 := by
    rw [hchar_quad]
    calc _ ≤ ∑ k ∈ Finset.range (n + 1),
              ‖((prob P t k : ℝ) : ℂ) *
                (Complex.exp (I * ((((k : ℝ) - meanP n P t) * θ : ℝ) : ℂ)) -
                  (1 + I * ((((k : ℝ) - meanP n P t) * θ : ℝ) : ℂ) -
                    ((((k : ℝ) - meanP n P t) * θ : ℝ) : ℂ) ^ 2 / 2))‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (n + 1), prob P t k * ((n : ℝ) ^ 3 * |θ| ^ 3) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have hp := prob_pos hdeg hpos ht hkn
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
          refine mul_le_mul_of_nonneg_left ?_ hp.le
          have htay := complex_exp_I_taylor (((k : ℝ) - meanP n P t) * θ)
          have hk_abs : |(k : ℝ) - meanP n P t| ≤ (n : ℝ) := by
            rw [abs_le]
            have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
            constructor <;> linarith [hmb.1, hmb.2, Nat.cast_nonneg (α := ℝ) k]
          have hcub : |((k : ℝ) - meanP n P t) * θ| ^ 3 ≤ (n : ℝ) ^ 3 * |θ| ^ 3 := by
            rw [abs_mul, mul_pow]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hk_abs 3) (by positivity)
          calc _ ≤ |((k : ℝ) - meanP n P t) * θ| ^ 3 / 6 := htay
            _ ≤ ((n : ℝ) ^ 3 * |θ| ^ 3) / 6 := by linarith
            _ ≤ (n : ℝ) ^ 3 * |θ| ^ 3 := by
                have hnn : 0 ≤ (n : ℝ) ^ 3 * |θ| ^ 3 := by positivity
                linarith
      _ = (∑ k ∈ Finset.range (n + 1), prob P t k) * ((n : ℝ) ^ 3 * |θ| ^ 3) := (Finset.sum_mul _ _ _).symm
      _ = (n : ℝ) ^ 3 * |θ| ^ 3 := by rw [hsum1, one_mul]
  have hE2 : ‖((Real.exp (-(varP n P t / 2) * θ ^ 2) : ℝ) : ℂ) -
      ((1 - varP n P t / 2 * θ ^ 2 : ℝ) : ℂ)‖ ≤ (n : ℝ) ^ 4 * |θ| ^ 3 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hvar_nn : 0 ≤ varP n P t := by
      unfold varP
      exact Finset.sum_nonneg fun k hk =>
        mul_nonneg (sq_nonneg _) (prob_pos hdeg hpos ht (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).le
    have hy : 0 ≤ varP n P t / 2 * θ ^ 2 := by positivity
    have hre := real_exp_neg_taylor hy
    rw [show -(varP n P t / 2 * θ ^ 2) = -(varP n P t / 2) * θ ^ 2 by ring] at hre
    have hθ4 : |θ| ^ 4 ≤ |θ| ^ 3 := by
      calc |θ| ^ 4 = |θ| ^ 3 * |θ| := by ring
        _ ≤ |θ| ^ 3 * 1 := mul_le_mul_of_nonneg_left hθ (by positivity)
        _ = |θ| ^ 3 := mul_one _
    have hvar4 : (varP n P t / 2 * θ ^ 2) ^ 2 / 2 ≤ (n : ℝ) ^ 4 * |θ| ^ 3 := by
      have hv : varP n P t ^ 2 ≤ (n : ℝ) ^ 4 := by nlinarith [hvb.2]
      calc (varP n P t / 2 * θ ^ 2) ^ 2 / 2
          = (varP n P t ^ 2 / 8) * |θ| ^ 4 := by rw [← sq_abs θ]; ring
        _ ≤ (n : ℝ) ^ 4 * |θ| ^ 3 := by
            have : varP n P t ^ 2 / 8 ≤ (n : ℝ) ^ 4 := by nlinarith [hv, sq_nonneg (varP n P t)]
            nlinarith [pow_nonneg (abs_nonneg θ) 3, pow_nonneg (abs_nonneg θ) 4]
    exact le_trans hre hvar4
  have htri : charFun n P t θ - ((Real.exp (-(varP n P t / 2) * θ ^ 2) : ℝ) : ℂ) =
      (charFun n P t θ - ((1 - varP n P t / 2 * θ ^ 2 : ℝ) : ℂ)) -
      (((Real.exp (-(varP n P t / 2) * θ ^ 2) : ℝ) : ℂ) - ((1 - varP n P t / 2 * θ ^ 2 : ℝ) : ℂ)) := by ring
  rw [htri]
  calc _ ≤ ‖charFun n P t θ - ((1 - varP n P t / 2 * θ ^ 2 : ℝ) : ℂ)‖ +
          ‖((Real.exp (-(varP n P t / 2) * θ ^ 2) : ℝ) : ℂ) - ((1 - varP n P t / 2 * θ ^ 2 : ℝ) : ℂ)‖ :=
          norm_sub_le _ _
    _ ≤ (n : ℝ) ^ 3 * |θ| ^ 3 + (n : ℝ) ^ 4 * |θ| ^ 3 := add_le_add hE1 hE2
    _ = ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * |θ| ^ 3 := by ring

lemma charFun_norm_local_le {n : ℕ} {P : Polynomial ℝ} (hn : 2 ≤ n) (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {t σ₂ : ℝ} (ht : 0 < t)
    (hσ₂_pos : 0 < σ₂) (hσ₂_le : σ₂ ≤ varP n P t) {θ : ℝ}
    (hθ1 : |θ| ≤ 1) (hθ2 : |θ| ≤ σ₂ / (8 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4))) :
    ‖charFun n P t θ‖ ≤ Real.exp (-(σ₂ / 4) * θ ^ 2) := by
  set C0 := (n : ℝ) ^ 3 + (n : ℝ) ^ 4
  have hC0_pos : 0 < C0 := by dsimp [C0]; positivity
  set v : ℂ := ((Real.exp (-(varP n P t / 2) * θ ^ 2) : ℝ) : ℂ)
  have hdiff : ‖charFun n P t θ - v‖ ≤ C0 * |θ| ^ 3 := charFun_local_approx hn hdeg hpos ht hθ1
  have hv_norm : ‖v‖ = Real.exp (-(varP n P t / 2) * θ ^ 2) := by
    dsimp only [v]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hσ₂_le_n2 : σ₂ ≤ (n : ℝ) ^ 2 := le_trans hσ₂_le (varP_bounds hn hdeg hpos ht).2
  have hθ_small : σ₂ * θ ^ 2 ≤ 1 / 2 := by
    have hC0_ge : (n : ℝ) ^ 4 ≤ C0 := by dsimp [C0]; linarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 3]
    have hn_ge2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hθ_le_inv : |θ| ≤ 1 / (8 * (n : ℝ) ^ 2) := by
      calc |θ| ≤ σ₂ / (8 * C0) := hθ2
        _ ≤ (n : ℝ) ^ 2 / (8 * (n : ℝ) ^ 4) :=
            div_le_div₀ (by positivity) hσ₂_le_n2 (by positivity) (by linarith)
        _ = 1 / (8 * (n : ℝ) ^ 2) := by field_simp [show (n : ℝ) ≠ 0 by positivity]
    calc σ₂ * θ ^ 2 = σ₂ * |θ| ^ 2 := by rw [sq_abs]
      _ ≤ (n : ℝ) ^ 2 * (1 / (8 * (n : ℝ) ^ 2)) ^ 2 :=
          mul_le_mul hσ₂_le_n2 (pow_le_pow_left₀ (abs_nonneg θ) hθ_le_inv 2) (by positivity) (by positivity)
      _ = 1 / (64 * (n : ℝ) ^ 2) := by field_simp [show (n : ℝ) ≠ 0 by positivity]; ring
      _ ≤ 1 / 2 := by
          have : (64 : ℝ) * (n : ℝ) ^ 2 ≥ 2 := by nlinarith
          exact one_div_le_one_div_of_le (by norm_num) this
  have hC0θ : C0 * |θ| ^ 3 ≤ σ₂ / 8 * θ ^ 2 := by
    calc C0 * |θ| ^ 3 = (C0 * |θ|) * |θ| ^ 2 := by ring
      _ ≤ (σ₂ / 8) * |θ| ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have := (le_div_iff₀ (by positivity : 0 < 8 * C0)).mp hθ2
          linarith
      _ = σ₂ / 8 * θ ^ 2 := by rw [sq_abs]
  have hv_le1 : ‖v‖ ≤ 1 - σ₂ / 2 * θ ^ 2 + (σ₂ / 2 * θ ^ 2) ^ 2 / 2 := by
    have hre := real_exp_neg_taylor (show 0 ≤ σ₂ / 2 * θ ^ 2 by positivity)
    have hle : Real.exp (-(varP n P t / 2) * θ ^ 2) ≤ Real.exp (-(σ₂ / 2 * θ ^ 2)) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg θ])
    rw [hv_norm]
    have := (abs_le.mp hre).2
    linarith
  have hquad_small : (σ₂ / 2 * θ ^ 2) ^ 2 / 2 ≤ σ₂ / 16 * θ ^ 2 := by
    have : (σ₂ / 2 * θ ^ 2) ^ 2 / 2 = (σ₂ * θ ^ 2) * (σ₂ / 8 * θ ^ 2) := by ring
    rw [this]
    have hnn : 0 ≤ σ₂ / 8 * θ ^ 2 := by positivity
    nlinarith [hθ_small, hnn]
  have hu_le1 : ‖charFun n P t θ‖ ≤ 1 - σ₂ / 4 * θ ^ 2 := by
    have htri : ‖charFun n P t θ‖ ≤ ‖v‖ + ‖charFun n P t θ - v‖ := by
      simpa [add_sub_cancel] using norm_add_le v (charFun n P t θ - v)
    have hnn : 0 ≤ σ₂ * θ ^ 2 := by positivity
    linarith [htri, hv_le1, hquad_small, hC0θ, hdiff, hnn]
  exact le_trans hu_le1 (by linarith [Real.add_one_le_exp (-(σ₂ / 4) * θ ^ 2)])

lemma charFun_pow_local_approx {n : ℕ} {P : Polynomial ℝ} (hn : 2 ≤ n) (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {t σ₂ : ℝ} (ht : 0 < t)
    (hσ₂_pos : 0 < σ₂) (hσ₂_le : σ₂ ≤ varP n P t) {θ : ℝ}
    (hθ1 : |θ| ≤ 1) (hθ2 : |θ| ≤ σ₂ / (8 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4)))
    {r : ℕ} (hr : 2 ≤ r) :
    ‖charFun n P t θ ^ r - ((Real.exp (-(varP n P t * r / 2) * θ ^ 2) : ℝ) : ℂ)‖ ≤
      (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * |θ| ^ 3 * Real.exp (-(σ₂ / 8 * r) * θ ^ 2) := by
  set C0 := (n : ℝ) ^ 3 + (n : ℝ) ^ 4
  set v : ℂ := ((Real.exp (-(varP n P t / 2) * θ ^ 2) : ℝ) : ℂ)
  have hv_pow : v ^ r = ((Real.exp (-(varP n P t * r / 2) * θ ^ 2) : ℝ) : ℂ) := by
    dsimp only [v]
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2; ring
  rw [← hv_pow]
  have hdiff : ‖charFun n P t θ - v‖ ≤ C0 * |θ| ^ 3 := charFun_local_approx hn hdeg hpos ht hθ1
  have hv_le : ‖v‖ ≤ Real.exp (-(σ₂ / 4) * θ ^ 2) := by
    dsimp only [v]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg θ])
  have hu_le : ‖charFun n P t θ‖ ≤ Real.exp (-(σ₂ / 4) * θ ^ 2) :=
    charFun_norm_local_le hn hdeg hpos ht hσ₂_pos hσ₂_le hθ1 hθ2
  have hpow := norm_pow_sub_pow_le (charFun n P t θ) v hu_le hv_le r (by omega)
  calc ‖charFun n P t θ ^ r - v ^ r‖
      ≤ (r : ℝ) * (Real.exp (-(σ₂ / 4) * θ ^ 2)) ^ (r - 1) * ‖charFun n P t θ - v‖ := hpow
    _ ≤ (r : ℝ) * Real.exp (-(σ₂ / 8 * r) * θ ^ 2) * (C0 * |θ| ^ 3) := by
        rw [← Real.exp_nat_mul]
        have hr_half : ((r : ℝ) / 2) ≤ ((r - 1 : ℕ) : ℝ) := by
          have : r ≤ 2 * (r - 1) := by omega
          have hcast : (r : ℝ) ≤ 2 * ((r - 1 : ℕ) : ℝ) := by exact_mod_cast this
          linarith
        have hexp_le : Real.exp (((r - 1 : ℕ) : ℝ) * (-(σ₂ / 4) * θ ^ 2)) ≤
            Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2) := by
          have hnn : 0 ≤ σ₂ / 4 * θ ^ 2 := by positivity
          exact Real.exp_le_exp.mpr (by nlinarith [hr_half, hnn])
        exact mul_le_mul (mul_le_mul_of_nonneg_left hexp_le (by positivity)) hdiff (norm_nonneg _) (by positivity)
    _ = (r : ℝ) * C0 * |θ| ^ 3 * Real.exp (-(σ₂ / 8 * r) * θ ^ 2) := by ring

/-!
## 4. Tilted Fourier representations and the three quantitative asymptotic estimates
-/

lemma coeff_comp_C_mul_X (Q : Polynomial ℝ) (t : ℝ) (m : ℕ) :
    (Q.comp (Polynomial.C t * Polynomial.X)).coeff m = t ^ m * Q.coeff m := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, mul_add]
  | monomial k a =>
    rw [Polynomial.monomial_comp, Polynomial.coeff_C_mul, mul_pow,
      ← Polynomial.C_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_monomial]
    by_cases h : m = k
    · subst h; simp [mul_comm]
    · simp [h, Ne.symm h]

lemma tilted_coeff_fourier {n : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {t : ℝ} (ht : 0 < t) (r m : ℕ) :
    t ^ m * (P ^ r).coeff m / (P.eval t) ^ r =
      (1 / (2 * Real.pi)) *
        (∫ θ in (-Real.pi)..Real.pi,
          charFun n P t θ ^ r * Complex.exp (I * ((meanP n P t * (r : ℝ) - (m : ℝ) : ℝ) : ℂ) * θ)).re := by
  let Qt : Polynomial ℝ := P.comp (Polynomial.C t * Polynomial.X)
  have hQpow : Qt ^ r = (P ^ r).comp (Polynomial.C t * Polynomial.X) := by
    dsimp only [Qt]
    induction r with
    | zero => simp
    | succ r ih => rw [pow_succ, pow_succ, ih, Polynomial.mul_comp]
  have hcoeff : (Qt ^ r).coeff m = t ^ m * (P ^ r).coeff m := by
    rw [hQpow, coeff_comp_C_mul_X]
  have hf := polynomial_coeff_fourier (Qt ^ r) m
  rw [hcoeff] at hf
  have hEv : 0 < P.eval t := evalP_pos hdeg hpos ht
  have hEv_pow : (P.eval t) ^ r ≠ 0 := pow_ne_zero r hEv.ne'
  have haeval : ∀ θ : ℝ,
      Polynomial.aeval (Complex.exp (I * θ)) (Qt ^ r) * Complex.exp (-I * (m : ℂ) * θ) =
        (((P.eval t) ^ r : ℝ) : ℂ) *
          (charFun n P t θ ^ r * Complex.exp (I * ((meanP n P t * (r : ℝ) - (m : ℝ) : ℝ) : ℂ) * θ)) := by
    intro θ
    rw [map_pow]
    have hQt_eval : Polynomial.aeval (Complex.exp (I * θ)) Qt =
        Polynomial.aeval ((t : ℂ) * Complex.exp (I * θ)) P := by
      dsimp only [Qt]
      rw [Polynomial.aeval_comp]
      simp only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      rfl
    rw [hQt_eval]
    have hch := charFun_eq_poly hdeg hpos ht θ
    have hEv_c : ((P.eval t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hEv.ne'
    have hP_eq : Polynomial.aeval ((t : ℂ) * Complex.exp (I * θ)) P =
        ((P.eval t : ℝ) : ℂ) * charFun n P t θ * Complex.exp (I * (meanP n P t : ℂ) * θ) := by
      rw [hch]
      have hexp : Complex.exp (-I * (meanP n P t : ℂ) * θ) * Complex.exp (I * (meanP n P t : ℂ) * θ) = 1 := by
        rw [← Complex.exp_add]; simp
      calc Polynomial.aeval ((t : ℂ) * Complex.exp (I * θ)) P
          = Polynomial.aeval ((t : ℂ) * Complex.exp (I * θ)) P * 1 := (mul_one _).symm
        _ = Polynomial.aeval ((t : ℂ) * Complex.exp (I * θ)) P *
              (Complex.exp (-I * (meanP n P t : ℂ) * θ) * Complex.exp (I * (meanP n P t : ℂ) * θ)) := by rw [hexp]
        _ = ((P.eval t : ℝ) : ℂ) *
              (Polynomial.aeval ((t : ℂ) * Complex.exp (I * θ)) P / ((P.eval t : ℝ) : ℂ) *
                Complex.exp (-I * (meanP n P t : ℂ) * θ)) *
              Complex.exp (I * (meanP n P t : ℂ) * θ) := by field_simp [hEv_c]
    rw [hP_eq, mul_pow, mul_pow, ← Complex.exp_nat_mul, Complex.ofReal_pow]
    rw [mul_assoc, mul_assoc, ← Complex.exp_add]
    congr 2; congr 1
    push_cast; ring
  simp_rw [haeval] at hf
  rw [intervalIntegral.integral_const_mul, Complex.re_ofReal_mul] at hf
  rw [hf]
  field_simp [hEv_pow]

lemma interval_le_full_gaussian {g : ℝ → ℝ} (hg_nn : ∀ θ, 0 ≤ g θ) (hg_int : Integrable g)
    {a b : ℝ} (hab : a ≤ b) :
    ∫ θ in a..b, g θ ≤ ∫ θ : ℝ, g θ := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_le_integral hg_int (Eventually.of_forall hg_nn)

lemma gaussian_tail_bound {a θ₀ : ℝ} (ha : 0 < a) (hθ₀ : 0 < θ₀) :
    (∫ θ : ℝ, Real.exp (-a * θ ^ 2)) - (∫ θ in (-θ₀)..θ₀, Real.exp (-a * θ ^ 2)) ≤
      Real.exp (-(a / 2) * θ₀ ^ 2) * Real.sqrt (Real.pi / (a / 2)) := by
  have hint : Integrable (fun θ : ℝ => Real.exp (-a * θ ^ 2)) := integrable_exp_neg_mul_sq ha
  have hcompl : (∫ θ : ℝ, Real.exp (-a * θ ^ 2)) - (∫ θ in (-θ₀)..θ₀, Real.exp (-a * θ ^ 2)) =
      ∫ θ in (Set.Ioc (-θ₀) θ₀)ᶜ, Real.exp (-a * θ ^ 2) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    have hadd := integral_add_compl (measurableSet_Ioc (a := -θ₀) (b := θ₀)) hint
    linarith
  rw [hcompl]
  have hint_dom : Integrable (fun θ : ℝ => Real.exp (-(a / 2) * θ₀ ^ 2) * Real.exp (-(a / 2) * θ ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < a / 2)).const_mul _
  calc ∫ θ in (Set.Ioc (-θ₀) θ₀)ᶜ, Real.exp (-a * θ ^ 2)
      ≤ ∫ θ in (Set.Ioc (-θ₀) θ₀)ᶜ, Real.exp (-(a / 2) * θ₀ ^ 2) * Real.exp (-(a / 2) * θ ^ 2) := by
        refine setIntegral_mono_on hint.integrableOn hint_dom.integrableOn measurableSet_Ioc.compl fun θ hθ => ?_
        rw [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hθ
        have hsq : θ₀ ^ 2 ≤ θ ^ 2 := by
          rcases hθ with h | h <;> nlinarith
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ ∫ θ : ℝ, Real.exp (-(a / 2) * θ₀ ^ 2) * Real.exp (-(a / 2) * θ ^ 2) :=
        setIntegral_le_integral hint_dom (Eventually.of_forall fun _ => by positivity)
    _ = Real.exp (-(a / 2) * θ₀ ^ 2) * Real.sqrt (Real.pi / (a / 2)) := by
        rw [integral_const_mul, integral_gaussian (a / 2)]

lemma gaussian_sq_tail_bound {a θ₀ : ℝ} (ha : 0 < a) (hθ₀ : 0 < θ₀) :
    ∫ θ in (Set.Ioc (-θ₀) θ₀)ᶜ, θ ^ 2 * Real.exp (-a * θ ^ 2) ≤
      31 * (4 / a) * Real.exp (-(a / 2) * θ₀ ^ 2) * Real.sqrt (Real.pi / (a / 4)) := by
  have hint_dom : Integrable (fun θ : ℝ =>
      31 * (4 / a) * Real.exp (-(a / 2) * θ₀ ^ 2) * Real.exp (-(a / 4) * θ ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < a / 4)).const_mul _
  have hint_lhs : Integrable (fun θ : ℝ => θ ^ 2 * Real.exp (-a * θ ^ 2)) := by
    have hdom2 : Integrable (fun θ : ℝ => 31 * (2 / a) ^ ((2 : ℝ) / 2) * Real.exp (-(a / 2) * θ ^ 2)) :=
      (integrable_exp_neg_mul_sq (by positivity : 0 < a / 2)).const_mul _
    refine hdom2.mono' (by fun_prop) (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hm := gaussian_moment_bound_pointwise 2 (by omega) ha θ
    simpa [sq_abs] using hm
  calc ∫ θ in (Set.Ioc (-θ₀) θ₀)ᶜ, θ ^ 2 * Real.exp (-a * θ ^ 2)
      ≤ ∫ θ in (Set.Ioc (-θ₀) θ₀)ᶜ,
          31 * (4 / a) * Real.exp (-(a / 2) * θ₀ ^ 2) * Real.exp (-(a / 4) * θ ^ 2) := by
        refine setIntegral_mono_on hint_lhs.integrableOn hint_dom.integrableOn measurableSet_Ioc.compl fun θ hθ => ?_
        rw [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hθ
        have hsq : θ₀ ^ 2 ≤ θ ^ 2 := by
          rcases hθ with h | h <;> nlinarith
        have hsplit : Real.exp (-a * θ ^ 2) ≤ Real.exp (-(a / 2) * θ₀ ^ 2) * Real.exp (-(a / 2) * θ ^ 2) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
        have hmom := gaussian_moment_bound_pointwise 2 (by omega) (by positivity : 0 < a / 2) θ
        have hpow1 : (2 / (a / 2)) ^ (((2 : ℕ) : ℝ) / 2) = 4 / a := by
          rw [show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num, Real.rpow_one, div_div_eq_mul_div]; ring
        rw [sq_abs, hpow1, show a / 2 / 2 = a / 4 by ring] at hmom
        calc θ ^ 2 * Real.exp (-a * θ ^ 2)
            ≤ θ ^ 2 * (Real.exp (-(a / 2) * θ₀ ^ 2) * Real.exp (-(a / 2) * θ ^ 2)) :=
              mul_le_mul_of_nonneg_left hsplit (sq_nonneg θ)
          _ = Real.exp (-(a / 2) * θ₀ ^ 2) * (θ ^ 2 * Real.exp (-(a / 2) * θ ^ 2)) := by ring
          _ ≤ Real.exp (-(a / 2) * θ₀ ^ 2) * (31 * (4 / a) * Real.exp (-(a / 4) * θ ^ 2)) :=
              mul_le_mul_of_nonneg_left hmom (by positivity)
          _ = 31 * (4 / a) * Real.exp (-(a / 2) * θ₀ ^ 2) * Real.exp (-(a / 4) * θ ^ 2) := by ring
    _ ≤ ∫ θ : ℝ, 31 * (4 / a) * Real.exp (-(a / 2) * θ₀ ^ 2) * Real.exp (-(a / 4) * θ ^ 2) :=
        setIntegral_le_integral hint_dom (Eventually.of_forall fun _ => by positivity)
    _ = 31 * (4 / a) * Real.exp (-(a / 2) * θ₀ ^ 2) * Real.sqrt (Real.pi / (a / 4)) := by
        rw [integral_const_mul, integral_gaussian (a / 4)]

lemma integral_split_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} (hg : Continuous g) {θ₀ : ℝ} :
    ∫ θ in (-Real.pi)..Real.pi, g θ =
      (∫ θ in (-Real.pi)..(-θ₀), g θ) + (∫ θ in (-θ₀)..θ₀, g θ) + (∫ θ in θ₀..Real.pi, g θ) := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) (-Real.pi) (-θ₀)) (hg.intervalIntegrable (μ := volume) (-θ₀) θ₀)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) (-Real.pi) θ₀) (hg.intervalIntegrable (μ := volume) θ₀ Real.pi)
  rw [h1, h2]

lemma gaussian_moment_integrable (k : ℕ) (hk : k ≤ 5) {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => |t| ^ k * Real.exp (-c * t ^ 2)) := by
  have hdom : Integrable (fun t : ℝ => 31 * (2 / c) ^ ((k : ℝ) / 2) * Real.exp (-(c / 2) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < c / 2)).const_mul _
  exact hdom.mono' (by fun_prop) (Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact gaussian_moment_bound_pointwise k hk hc t)

lemma gaussian_moment_2 {γ r : ℝ} (hγ : 0 < γ) (hr : 0 < r) :
    ∫ t : ℝ, |t| ^ 2 * Real.exp (-(γ * r) * t ^ 2) ≤
      (31 * (2 / γ) * Real.sqrt (2 * Real.pi / γ)) / (r * Real.sqrt r) := by
  have h := gaussian_moment_integral_le 2 (by omega) (mul_pos hγ hr)
  refine le_trans h (le_of_eq ?_)
  rw [show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  rw [show Real.pi / (γ * r / 2) = (2 * Real.pi / γ) / r by field_simp [hγ.ne', hr.ne']]
  rw [Real.sqrt_div (by positivity)]
  field_simp [hγ.ne', hr.ne', (Real.sqrt_pos.mpr hr).ne']

lemma gaussian_moment_3 {γ r : ℝ} (hγ : 0 < γ) (hr : 0 < r) :
    ∫ t : ℝ, |t| ^ 3 * Real.exp (-(γ * r) * t ^ 2) ≤
      (31 * (2 / γ) ^ 2 * Real.sqrt Real.pi) / r ^ 2 := by
  have h := gaussian_moment_integral_le 3 (by omega) (mul_pos hγ hr)
  refine le_trans h ?_
  have hpow : (2 / (γ * r)) ^ (((3 : ℕ) : ℝ) / 2) = (2 / (γ * r)) * Real.sqrt (2 / (γ * r)) := by
    rw [show ((3 : ℕ) : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hsq_prod : Real.sqrt (2 / (γ * r)) * Real.sqrt (Real.pi / (γ * r / 2)) =
      (2 / (γ * r)) * Real.sqrt Real.pi := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show 2 / (γ * r) * (Real.pi / (γ * r / 2)) = (2 / (γ * r)) ^ 2 * Real.pi by
      field_simp [hγ.ne', hr.ne']]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hpow, mul_assoc 31, mul_assoc (2 / (γ * r)), hsq_prod]
  have heq : 31 * (2 / (γ * r) * (2 / (γ * r) * Real.sqrt Real.pi)) =
      (31 * (2 / γ) ^ 2 * Real.sqrt Real.pi) / r ^ 2 := by
    field_simp [hγ.ne', hr.ne']
  exact le_of_eq heq

lemma gaussian_moment_4 {γ r : ℝ} (hγ : 0 < γ) (hr : 0 < r) :
    ∫ t : ℝ, |t| ^ 4 * Real.exp (-(γ * r) * t ^ 2) ≤
      (31 * (2 / γ) ^ 2 * Real.sqrt (2 * Real.pi / γ)) / (r ^ 2 * Real.sqrt r) := by
  have h := gaussian_moment_integral_le 4 (by omega) (mul_pos hγ hr)
  refine le_trans h (le_of_eq ?_)
  rw [show ((4 : ℕ) : ℝ) / 2 = (2 : ℕ) by norm_num, Real.rpow_natCast]
  rw [show Real.pi / (γ * r / 2) = (2 * Real.pi / γ) / r by field_simp [hγ.ne', hr.ne']]
  rw [Real.sqrt_div (by positivity)]
  field_simp [hγ.ne', hr.ne', (Real.sqrt_pos.mpr hr).ne']

lemma gaussian_moment_5 {γ r : ℝ} (hγ : 0 < γ) (hr : 0 < r) :
    ∫ t : ℝ, |t| ^ 5 * Real.exp (-(γ * r) * t ^ 2) ≤
      (31 * (2 / γ) ^ 3 * Real.sqrt Real.pi) / r ^ 3 := by
  have h := gaussian_moment_integral_le 5 (by omega) (mul_pos hγ hr)
  refine le_trans h ?_
  have hpow : (2 / (γ * r)) ^ (((5 : ℕ) : ℝ) / 2) = (2 / (γ * r)) ^ 2 * Real.sqrt (2 / (γ * r)) := by
    rw [show ((5 : ℕ) : ℝ) / 2 = (2 : ℕ) + 1 / 2 by norm_num, Real.rpow_add (by positivity),
      Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hsq_prod : Real.sqrt (2 / (γ * r)) * Real.sqrt (Real.pi / (γ * r / 2)) =
      (2 / (γ * r)) * Real.sqrt Real.pi := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show 2 / (γ * r) * (Real.pi / (γ * r / 2)) = (2 / (γ * r)) ^ 2 * Real.pi by
      field_simp [hγ.ne', hr.ne']]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hpow, mul_assoc 31, mul_assoc ((2 / (γ * r)) ^ 2), hsq_prod]
  have heq : 31 * ((2 / (γ * r)) ^ 2 * (2 / (γ * r) * Real.sqrt Real.pi)) =
      (31 * (2 / γ) ^ 3 * Real.sqrt Real.pi) / r ^ 3 := by
    field_simp [hγ.ne', hr.ne']
  exact le_of_eq heq

/-- Estimate A: uniform lower bound on the tilted central coefficient at `m = meanP n P t * r`. -/
lemma tilted_central_lower {n : ℕ} {P : Polynomial ℝ} (hn : 2 ≤ n) (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {t σ₂ θ₀ ρ : ℝ} (ht : 0 < t)
    (hσ₂_pos : 0 < σ₂) (hσ₂_le : σ₂ ≤ varP n P t)
    (hθ₀_pos : 0 < θ₀) (hθ₀_le1 : θ₀ ≤ 1) (hθ₀_lepi : θ₀ ≤ Real.pi)
    (hθ₀_small : θ₀ ≤ σ₂ / (8 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4)))
    (hρ_nn : 0 ≤ ρ) (houter : ∀ θ : ℝ, θ₀ ≤ |θ| → |θ| ≤ Real.pi → ‖charFun n P t θ‖ ≤ ρ)
    {r : ℕ} (hr : 2 ≤ r) :
    1 / (Real.sqrt (2 * Real.pi) * (n : ℝ) * Real.sqrt r) -
        (31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 2 * Real.sqrt Real.pi / (2 * Real.pi)) / (r : ℝ) -
        (Real.sqrt (Real.pi / (σ₂ / 4)) / (2 * Real.pi)) * Real.exp (-(σ₂ * θ₀ ^ 2 / 4) * (r : ℝ)) -
        ρ ^ r ≤
      (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, charFun n P t θ ^ r).re := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
  have hcont_ch : Continuous (fun θ : ℝ => charFun n P t θ ^ r) := by
    unfold charFun; fun_prop
  rw [integral_split_symm hcont_ch (θ₀ := θ₀)]
  simp only [Complex.add_re]
  have htail_left : |(∫ θ in (-Real.pi)..(-θ₀), charFun n P t θ ^ r).re| ≤ Real.pi * ρ ^ r := by
    calc |(∫ θ in (-Real.pi)..(-θ₀), charFun n P t θ ^ r).re|
        ≤ ‖∫ θ in (-Real.pi)..(-θ₀), charFun n P t θ ^ r‖ := Complex.abs_re_le_norm _
      _ ≤ ∫ θ in (-Real.pi)..(-θ₀), ‖charFun n P t θ ^ r‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ _θ in (-Real.pi)..(-θ₀), ρ ^ r := by
          refine intervalIntegral.integral_mono_on (by linarith)
            (hcont_ch.norm.intervalIntegrable _ _) intervalIntegrable_const fun θ hθ => ?_
          rw [norm_pow]
          have habs : |θ| = -θ := abs_of_nonpos (by linarith [hθ.2])
          exact pow_le_pow_left₀ (norm_nonneg _) (houter θ (by linarith [hθ.2]) (by linarith [hθ.1])) r
      _ = (Real.pi - θ₀) * ρ ^ r := by
          simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ Real.pi * ρ ^ r := by nlinarith [pow_nonneg hρ_nn r]
  have htail_right : |(∫ θ in θ₀..Real.pi, charFun n P t θ ^ r).re| ≤ Real.pi * ρ ^ r := by
    calc |(∫ θ in θ₀..Real.pi, charFun n P t θ ^ r).re|
        ≤ ‖∫ θ in θ₀..Real.pi, charFun n P t θ ^ r‖ := Complex.abs_re_le_norm _
      _ ≤ ∫ θ in θ₀..Real.pi, ‖charFun n P t θ ^ r‖ :=
          intervalIntegral.norm_integral_le_integral_norm hθ₀_lepi
      _ ≤ ∫ _θ in θ₀..Real.pi, ρ ^ r := by
          refine intervalIntegral.integral_mono_on hθ₀_lepi
            (hcont_ch.norm.intervalIntegrable _ _) intervalIntegrable_const fun θ hθ => ?_
          rw [norm_pow]
          have habs : |θ| = θ := abs_of_nonneg (by linarith [hθ.1])
          exact pow_le_pow_left₀ (norm_nonneg _) (houter θ (by linarith [hθ.1]) (by linarith [hθ.2])) r
      _ = (Real.pi - θ₀) * ρ ^ r := by
          simp only [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ Real.pi * ρ ^ r := by nlinarith [pow_nonneg hρ_nn r]
  have hvar_pos : 0 < varP n P t := lt_of_lt_of_le hσ₂_pos hσ₂_le
  set a := varP n P t * (r : ℝ) / 2
  have ha_pos : 0 < a := by dsimp [a]; positivity
  have hinner_err :
      |(∫ θ in (-θ₀)..θ₀, charFun n P t θ ^ r).re - ∫ θ in (-θ₀)..θ₀, Real.exp (-a * θ ^ 2)| ≤
        31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 2 * Real.sqrt Real.pi / (r : ℝ) := by
    have hre_sub :
        (∫ θ in (-θ₀)..θ₀, charFun n P t θ ^ r).re - ∫ θ in (-θ₀)..θ₀, Real.exp (-a * θ ^ 2) =
        (∫ θ in (-θ₀)..θ₀, (charFun n P t θ ^ r - ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ))).re := by
      rw [intervalIntegral.integral_sub (hcont_ch.intervalIntegrable _ _)
        ((by fun_prop : Continuous _).intervalIntegrable _ _), Complex.sub_re]
      congr 1
      rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
    rw [hre_sub]
    calc |(∫ θ in (-θ₀)..θ₀, (charFun n P t θ ^ r - ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ))).re|
        ≤ ‖∫ θ in (-θ₀)..θ₀, (charFun n P t θ ^ r - ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ))‖ :=
          Complex.abs_re_le_norm _
      _ ≤ ∫ θ in (-θ₀)..θ₀, ‖charFun n P t θ ^ r - ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ θ in (-θ₀)..θ₀, (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (|θ| ^ 3 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2)) := by
          refine intervalIntegral.integral_mono_on (by linarith)
            ((by fun_prop : Continuous _).intervalIntegrable _ _)
            ((by fun_prop : Continuous _).intervalIntegrable _ _) fun θ hθ => ?_
          have hθ_abs : |θ| ≤ θ₀ := abs_le.mpr hθ
          have hloc := charFun_pow_local_approx hn hdeg hpos ht hσ₂_pos hσ₂_le
            (le_trans hθ_abs hθ₀_le1) (le_trans hθ_abs hθ₀_small) hr
          simpa [a, mul_assoc] using hloc
      _ = (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) *
            ∫ θ in (-θ₀)..θ₀, |θ| ^ 3 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2) := by
          rw [intervalIntegral.integral_const_mul]
      _ ≤ (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) *
            ∫ θ : ℝ, |θ| ^ 3 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (interval_le_full_gaussian (fun _ => by positivity)
              (gaussian_moment_integrable 3 (by omega) (by positivity)) (by linarith)) (by positivity)
      _ ≤ (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) *
            ((31 * (2 / (σ₂ / 8)) ^ 2 * Real.sqrt Real.pi) / (r : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (gaussian_moment_3 (by positivity : 0 < σ₂ / 8) hr_pos) (by positivity)
      _ = 31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 2 * Real.sqrt Real.pi / (r : ℝ) := by
          have : 2 / (σ₂ / 8) = 16 / σ₂ := by field_simp [hσ₂_pos.ne']; ring
          rw [this]; field_simp [hr_pos.ne']
  -- Main Gaussian term minus tail
  have hgauss_full : Real.sqrt (2 * Real.pi) / ((n : ℝ) * Real.sqrt r) ≤
      ∫ θ : ℝ, Real.exp (-a * θ ^ 2) := by
    rw [integral_gaussian a]
    have hvar_le : varP n P t ≤ (n : ℝ) ^ 2 := (varP_bounds hn hdeg hpos ht).2
    have ha_le : a ≤ (n : ℝ) ^ 2 * (r : ℝ) / 2 := by dsimp [a]; nlinarith
    have hdiv : 2 * Real.pi / ((n : ℝ) ^ 2 * (r : ℝ)) ≤ Real.pi / a := by
      rw [show 2 * Real.pi / ((n : ℝ) ^ 2 * (r : ℝ)) = Real.pi / ((n : ℝ) ^ 2 * (r : ℝ) / 2) by ring]
      exact div_le_div_of_nonneg_left Real.pi_pos.le ha_pos ha_le
    calc Real.sqrt (2 * Real.pi) / ((n : ℝ) * Real.sqrt r)
        = Real.sqrt (2 * Real.pi / ((n : ℝ) ^ 2 * (r : ℝ))) := by
            rw [Real.sqrt_div (by positivity), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg n)]
      _ ≤ Real.sqrt (Real.pi / a) := Real.sqrt_le_sqrt hdiv
  have hgauss_tail :
      (∫ θ : ℝ, Real.exp (-a * θ ^ 2)) - (∫ θ in (-θ₀)..θ₀, Real.exp (-a * θ ^ 2)) ≤
        Real.sqrt (Real.pi / (σ₂ / 4)) * Real.exp (-(σ₂ * θ₀ ^ 2 / 4) * (r : ℝ)) := by
    have ht1 := gaussian_tail_bound ha_pos hθ₀_pos
    have ha_ge : σ₂ / 4 ≤ a / 2 := by
      dsimp [a]
      have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
      nlinarith
    have ha_ge_r : σ₂ * (r : ℝ) / 4 ≤ a / 2 := by dsimp [a]; nlinarith
    have hexp_le : Real.exp (-(a / 2) * θ₀ ^ 2) ≤ Real.exp (-(σ₂ * θ₀ ^ 2 / 4) * (r : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg θ₀])
    have hsq_le : Real.sqrt (Real.pi / (a / 2)) ≤ Real.sqrt (Real.pi / (σ₂ / 4)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) ha_ge)
    calc (∫ θ : ℝ, Real.exp (-a * θ ^ 2)) - (∫ θ in (-θ₀)..θ₀, Real.exp (-a * θ ^ 2))
        ≤ Real.exp (-(a / 2) * θ₀ ^ 2) * Real.sqrt (Real.pi / (a / 2)) := ht1
      _ ≤ Real.exp (-(σ₂ * θ₀ ^ 2 / 4) * (r : ℝ)) * Real.sqrt (Real.pi / (σ₂ / 4)) :=
          mul_le_mul hexp_le hsq_le (by positivity) (by positivity)
      _ = Real.sqrt (Real.pi / (σ₂ / 4)) * Real.exp (-(σ₂ * θ₀ ^ 2 / 4) * (r : ℝ)) := by ring
  have hmain_pi : (1 / (2 * Real.pi)) * (Real.sqrt (2 * Real.pi) / ((n : ℝ) * Real.sqrt r)) =
      1 / (Real.sqrt (2 * Real.pi) * (n : ℝ) * Real.sqrt r) := by
    have h2pi : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
      Real.mul_self_sqrt (by positivity)
    have hsne : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hnne : (n : ℝ) ≠ 0 := by positivity
    have hrne : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr_pos).ne'
    field_simp [hsne, hnne, hrne, Real.pi_pos.ne']
    linarith [h2pi]
  have h1 := (abs_le.mp htail_left).1
  have h2 := (abs_le.mp htail_right).1
  have h3 := (abs_le.mp hinner_err).1
  have hsum_ineq :
      Real.sqrt (2 * Real.pi) / ((n : ℝ) * Real.sqrt r) -
        31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 2 * Real.sqrt Real.pi / (r : ℝ) -
        Real.sqrt (Real.pi / (σ₂ / 4)) * Real.exp (-(σ₂ * θ₀ ^ 2 / 4) * (r : ℝ)) -
        2 * Real.pi * ρ ^ r ≤
      (∫ θ in (-Real.pi)..(-θ₀), charFun n P t θ ^ r).re +
        (∫ θ in (-θ₀)..θ₀, charFun n P t θ ^ r).re +
        (∫ θ in θ₀..Real.pi, charFun n P t θ ^ r).re := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum_ineq (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
  have hlhs_eq :
      1 / (2 * Real.pi) *
        (Real.sqrt (2 * Real.pi) / ((n : ℝ) * Real.sqrt r) -
          31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 2 * Real.sqrt Real.pi / (r : ℝ) -
          Real.sqrt (Real.pi / (σ₂ / 4)) * Real.exp (-(σ₂ * θ₀ ^ 2 / 4) * (r : ℝ)) -
          2 * Real.pi * ρ ^ r) =
      1 / (Real.sqrt (2 * Real.pi) * (n : ℝ) * Real.sqrt r) -
        (31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 2 * Real.sqrt Real.pi / (2 * Real.pi)) / (r : ℝ) -
        (Real.sqrt (Real.pi / (σ₂ / 4)) / (2 * Real.pi)) * Real.exp (-(σ₂ * θ₀ ^ 2 / 4) * (r : ℝ)) -
        ρ ^ r := by
    rw [mul_sub, mul_sub, mul_sub, hmain_pi]
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp [hpi]
  linarith

/-- Estimate B: uniform `O(r^{-3/2})` upper bound on the tilted difference `t⁻¹ b_{m+1}^{(t)} - b_m^{(t)}` error term. -/
lemma tilted_diff_upper {n : ℕ} {P : Polynomial ℝ} (hn : 2 ≤ n) (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {t σ₂ θ₀ ρ : ℝ} (ht : 0 < t)
    (hσ₂_pos : 0 < σ₂) (hσ₂_le : σ₂ ≤ varP n P t)
    (hθ₀_pos : 0 < θ₀) (hθ₀_le1 : θ₀ ≤ 1) (hθ₀_lepi : θ₀ ≤ Real.pi)
    (hθ₀_small : θ₀ ≤ σ₂ / (8 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4)))
    (hρ_nn : 0 ≤ ρ) (houter : ∀ θ : ℝ, θ₀ ≤ |θ| → |θ| ≤ Real.pi → ‖charFun n P t θ‖ ≤ ρ)
    {r : ℕ} (hr : 2 ≤ r) :
    |(1 / (2 * Real.pi)) *
        (∫ θ in (-Real.pi)..Real.pi, (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re| ≤
      ((31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 2 * Real.sqrt (16 * Real.pi / σ₂) +
        (1 / 2) * (31 * (8 / σ₂) * Real.sqrt (8 * Real.pi / σ₂))) / (2 * Real.pi)) / ((r : ℝ) * Real.sqrt r) +
        2 * ρ ^ r := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
  have hcont_f : Continuous (fun θ : ℝ => (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r) := by
    unfold charFun; fun_prop
  rw [integral_split_symm hcont_f (θ₀ := θ₀)]
  simp only [Complex.add_re]
  have hexp_sub1 : ∀ θ : ℝ, ‖Complex.exp (-I * (θ : ℂ)) - 1‖ ≤ 2 := by
    intro θ
    calc ‖Complex.exp (-I * (θ : ℂ)) - 1‖
        ≤ ‖Complex.exp (-I * (θ : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
          rw [show -I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  have htail_left : |(∫ θ in (-Real.pi)..(-θ₀), (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re| ≤
      2 * Real.pi * ρ ^ r := by
    calc _ ≤ ‖∫ θ in (-Real.pi)..(-θ₀), (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r‖ :=
            Complex.abs_re_le_norm _
      _ ≤ ∫ θ in (-Real.pi)..(-θ₀), ‖(Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ _θ in (-Real.pi)..(-θ₀), 2 * ρ ^ r := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (hcont_f.norm.intervalIntegrable _ _) intervalIntegrable_const fun θ hθ => ?_
            rw [norm_mul, norm_pow]
            have habs : |θ| = -θ := abs_of_nonpos (by linarith [hθ.2])
            exact mul_le_mul (hexp_sub1 θ)
              (pow_le_pow_left₀ (norm_nonneg _) (houter θ (by linarith [hθ.2]) (by linarith [hθ.1])) r)
              (by positivity) (by norm_num)
      _ = (Real.pi - θ₀) * (2 * ρ ^ r) := by
            simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ 2 * Real.pi * ρ ^ r := by nlinarith [pow_nonneg hρ_nn r]
  have htail_right : |(∫ θ in θ₀..Real.pi, (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re| ≤
      2 * Real.pi * ρ ^ r := by
    calc _ ≤ ‖∫ θ in θ₀..Real.pi, (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r‖ :=
            Complex.abs_re_le_norm _
      _ ≤ ∫ θ in θ₀..Real.pi, ‖(Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r‖ :=
            intervalIntegral.norm_integral_le_integral_norm hθ₀_lepi
      _ ≤ ∫ _θ in θ₀..Real.pi, 2 * ρ ^ r := by
            refine intervalIntegral.integral_mono_on hθ₀_lepi
              (hcont_f.norm.intervalIntegrable _ _) intervalIntegrable_const fun θ hθ => ?_
            rw [norm_mul, norm_pow]
            have habs : |θ| = θ := abs_of_nonneg (by linarith [hθ.1])
            exact mul_le_mul (hexp_sub1 θ)
              (pow_le_pow_left₀ (norm_nonneg _) (houter θ (by linarith [hθ.1]) (by linarith [hθ.2])) r)
              (by positivity) (by norm_num)
      _ = (Real.pi - θ₀) * (2 * ρ ^ r) := by
            simp only [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ 2 * Real.pi * ρ ^ r := by nlinarith [pow_nonneg hρ_nn r]
  -- On `[-θ₀, θ₀]`, subtract purely imaginary `(-I * θ) * exp(-a * θ^2)` whose real part is identically 0!
  set a := varP n P t * (r : ℝ) / 2
  have hpure_im : (∫ θ in (-θ₀)..θ₀, (-I * (θ : ℂ)) * ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)).re = 0 := by
    rw [show (∫ θ in (-θ₀)..θ₀, (-I * (θ : ℂ)) * ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)).re =
        Complex.reCLM (∫ θ in (-θ₀)..θ₀, (-I * (θ : ℂ)) * ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)) from rfl,
      ← Complex.reCLM.intervalIntegral_comp_comm ((by fun_prop : Continuous _).intervalIntegrable _ _)]
    have h0 : (fun θ : ℝ => Complex.reCLM ((-I * (θ : ℂ)) * ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ))) = fun _ => (0 : ℝ) := by
      funext θ
      change ((-I * (θ : ℂ)) * ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)).re = 0
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [h0]; simp
  have hinner :
      |(∫ θ in (-θ₀)..θ₀, (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re| ≤
        (31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 2 * Real.sqrt (16 * Real.pi / σ₂) +
          (1 / 2) * (31 * (8 / σ₂) * Real.sqrt (8 * Real.pi / σ₂))) / ((r : ℝ) * Real.sqrt r) := by
    have hsub_eq :
        (∫ θ in (-θ₀)..θ₀, (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re =
        (∫ θ in (-θ₀)..θ₀,
          ((-I * (θ : ℂ)) * (charFun n P t θ ^ r - ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)) +
            (Complex.exp (-I * (θ : ℂ)) - 1 + I * (θ : ℂ)) * charFun n P t θ ^ r)).re := by
      have hpoint : ∀ θ : ℝ,
          (Complex.exp (-I * (θ : ℂ)) - 1) * charFun n P t θ ^ r -
            (-I * (θ : ℂ)) * ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ) =
          (-I * (θ : ℂ)) * (charFun n P t θ ^ r - ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)) +
            (Complex.exp (-I * (θ : ℂ)) - 1 + I * (θ : ℂ)) * charFun n P t θ ^ r := fun θ => by ring
      rw [← sub_zero (∫ θ in (-θ₀)..θ₀, (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re,
        ← hpure_im, ← Complex.sub_re,
        ← intervalIntegral.integral_sub (hcont_f.intervalIntegrable _ _)
          ((by fun_prop : Continuous _).intervalIntegrable _ _)]
      congr 1
      refine intervalIntegral.integral_congr fun θ _ => hpoint θ
    rw [hsub_eq]
    have hpt_bound : ∀ θ ∈ Set.Icc (-θ₀) θ₀,
        ‖(-I * (θ : ℂ)) * (charFun n P t θ ^ r - ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)) +
          (Complex.exp (-I * (θ : ℂ)) - 1 + I * (θ : ℂ)) * charFun n P t θ ^ r‖ ≤
        (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (|θ| ^ 4 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2)) +
          (1 / 2) * (|θ| ^ 2 * Real.exp (-(σ₂ / 4 * (r : ℝ)) * θ ^ 2)) := by
      intro θ hθ
      have hθ_abs : |θ| ≤ θ₀ := abs_le.mpr hθ
      have h1 : ‖(-I * (θ : ℂ)) * (charFun n P t θ ^ r - ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ))‖ ≤
          (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (|θ| ^ 4 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2)) := by
        rw [norm_mul, norm_mul, norm_neg, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        have hloc := charFun_pow_local_approx hn hdeg hpos ht hσ₂_pos hσ₂_le
          (le_trans hθ_abs hθ₀_le1) (le_trans hθ_abs hθ₀_small) hr
        calc |θ| * ‖charFun n P t θ ^ r - ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)‖
            ≤ |θ| * ((r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * |θ| ^ 3 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2)) :=
              mul_le_mul_of_nonneg_left hloc (abs_nonneg θ)
          _ = (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (|θ| ^ 4 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2)) := by ring
      have h2 : ‖(Complex.exp (-I * (θ : ℂ)) - 1 + I * (θ : ℂ)) * charFun n P t θ ^ r‖ ≤
          (1 / 2) * (|θ| ^ 2 * Real.exp (-(σ₂ / 4 * (r : ℝ)) * θ ^ 2)) := by
        rw [norm_mul, norm_pow]
        have hlin : ‖Complex.exp (-I * (θ : ℂ)) - 1 + I * (θ : ℂ)‖ ≤ θ ^ 2 / 2 := by
          have := complex_exp_I_linear (-θ)
          rw [show Complex.exp (I * ((-θ : ℝ) : ℂ)) - (1 + I * ((-θ : ℝ) : ℂ)) =
              Complex.exp (-I * (θ : ℂ)) - 1 + I * (θ : ℂ) by push_cast; ring, neg_sq] at this
          exact this
        have hch_le : ‖charFun n P t θ‖ ^ r ≤ Real.exp (-(σ₂ / 4 * (r : ℝ)) * θ ^ 2) := by
          have hch1 := charFun_norm_local_le hn hdeg hpos ht hσ₂_pos hσ₂_le
            (le_trans hθ_abs hθ₀_le1) (le_trans hθ_abs hθ₀_small)
          calc ‖charFun n P t θ‖ ^ r
              ≤ (Real.exp (-(σ₂ / 4) * θ ^ 2)) ^ r := pow_le_pow_left₀ (norm_nonneg _) hch1 r
            _ = Real.exp (-(σ₂ / 4 * (r : ℝ)) * θ ^ 2) := by
                rw [← Real.exp_nat_mul]; congr 1; ring
        calc _ ≤ (θ ^ 2 / 2) * Real.exp (-(σ₂ / 4 * (r : ℝ)) * θ ^ 2) :=
              mul_le_mul hlin hch_le (by positivity) (by positivity)
          _ = (1 / 2) * (|θ| ^ 2 * Real.exp (-(σ₂ / 4 * (r : ℝ)) * θ ^ 2)) := by rw [sq_abs]; ring
      exact le_trans (norm_add_le _ _) (add_le_add h1 h2)
    have hpart1 :
        ∫ θ in (-θ₀)..θ₀, (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (|θ| ^ 4 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2)) ≤
          31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 2 * Real.sqrt (16 * Real.pi / σ₂) / ((r : ℝ) * Real.sqrt r) := by
      rw [intervalIntegral.integral_const_mul]
      calc (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * ∫ θ in (-θ₀)..θ₀, |θ| ^ 4 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2)
          ≤ (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * ∫ θ : ℝ, |θ| ^ 4 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2) :=
            mul_le_mul_of_nonneg_left
              (interval_le_full_gaussian (fun _ => by positivity)
                (gaussian_moment_integrable 4 (by omega) (by positivity)) (by linarith)) (by positivity)
        _ ≤ (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) *
              ((31 * (2 / (σ₂ / 8)) ^ 2 * Real.sqrt (2 * Real.pi / (σ₂ / 8))) / ((r : ℝ) ^ 2 * Real.sqrt r)) :=
            mul_le_mul_of_nonneg_left (gaussian_moment_4 (by positivity : 0 < σ₂ / 8) hr_pos) (by positivity)
        _ = 31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 2 * Real.sqrt (16 * Real.pi / σ₂) / ((r : ℝ) * Real.sqrt r) := by
            rw [show 2 / (σ₂ / 8) = 16 / σ₂ by field_simp [hσ₂_pos.ne']; ring,
              show 2 * Real.pi / (σ₂ / 8) = 16 * Real.pi / σ₂ by field_simp [hσ₂_pos.ne']; ring]
            field_simp [hr_pos.ne', (Real.sqrt_pos.mpr hr_pos).ne']
    have hpart2 :
        ∫ θ in (-θ₀)..θ₀, (1 / 2) * (|θ| ^ 2 * Real.exp (-(σ₂ / 4 * (r : ℝ)) * θ ^ 2)) ≤
          (1 / 2) * (31 * (8 / σ₂) * Real.sqrt (8 * Real.pi / σ₂)) / ((r : ℝ) * Real.sqrt r) := by
      rw [intervalIntegral.integral_const_mul]
      calc (1 / 2) * ∫ θ in (-θ₀)..θ₀, |θ| ^ 2 * Real.exp (-(σ₂ / 4 * (r : ℝ)) * θ ^ 2)
          ≤ (1 / 2) * ∫ θ : ℝ, |θ| ^ 2 * Real.exp (-(σ₂ / 4 * (r : ℝ)) * θ ^ 2) :=
            mul_le_mul_of_nonneg_left
              (interval_le_full_gaussian (fun _ => by positivity)
                (gaussian_moment_integrable 2 (by omega) (by positivity)) (by linarith)) (by norm_num)
        _ ≤ (1 / 2) * ((31 * (2 / (σ₂ / 4)) * Real.sqrt (2 * Real.pi / (σ₂ / 4))) / ((r : ℝ) * Real.sqrt r)) :=
            mul_le_mul_of_nonneg_left (gaussian_moment_2 (by positivity : 0 < σ₂ / 4) hr_pos) (by norm_num)
        _ = (1 / 2) * (31 * (8 / σ₂) * Real.sqrt (8 * Real.pi / σ₂)) / ((r : ℝ) * Real.sqrt r) := by
            rw [show 2 / (σ₂ / 4) = 8 / σ₂ by field_simp [hσ₂_pos.ne']; ring,
              show 2 * Real.pi / (σ₂ / 4) = 8 * Real.pi / σ₂ by field_simp [hσ₂_pos.ne']; ring]
            ring
    have hcont_err : Continuous (fun θ : ℝ =>
        ‖(-I * (θ : ℂ)) * (charFun n P t θ ^ r - ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)) +
          (Complex.exp (-I * (θ : ℂ)) - 1 + I * (θ : ℂ)) * charFun n P t θ ^ r‖) := by
      unfold charFun; fun_prop
    calc |(∫ θ in (-θ₀)..θ₀,
            ((-I * (θ : ℂ)) * (charFun n P t θ ^ r - ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)) +
              (Complex.exp (-I * (θ : ℂ)) - 1 + I * (θ : ℂ)) * charFun n P t θ ^ r)).re|
        ≤ ‖∫ θ in (-θ₀)..θ₀,
            ((-I * (θ : ℂ)) * (charFun n P t θ ^ r - ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)) +
              (Complex.exp (-I * (θ : ℂ)) - 1 + I * (θ : ℂ)) * charFun n P t θ ^ r)‖ :=
            Complex.abs_re_le_norm _
      _ ≤ ∫ θ in (-θ₀)..θ₀, ‖(-I * (θ : ℂ)) * (charFun n P t θ ^ r - ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)) +
            (Complex.exp (-I * (θ : ℂ)) - 1 + I * (θ : ℂ)) * charFun n P t θ ^ r‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ θ in (-θ₀)..θ₀,
            ((r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (|θ| ^ 4 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2)) +
              (1 / 2) * (|θ| ^ 2 * Real.exp (-(σ₂ / 4 * (r : ℝ)) * θ ^ 2))) :=
          intervalIntegral.integral_mono_on (by linarith)
            (hcont_err.intervalIntegrable _ _)
            ((by fun_prop : Continuous _).intervalIntegrable _ _) hpt_bound
      _ = (∫ θ in (-θ₀)..θ₀, (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (|θ| ^ 4 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2))) +
          (∫ θ in (-θ₀)..θ₀, (1 / 2) * (|θ| ^ 2 * Real.exp (-(σ₂ / 4 * (r : ℝ)) * θ ^ 2))) :=
          intervalIntegral.integral_add ((by fun_prop : Continuous _).intervalIntegrable _ _)
            ((by fun_prop : Continuous _).intervalIntegrable _ _)
      _ ≤ (31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 2 * Real.sqrt (16 * Real.pi / σ₂) +
            (1 / 2) * (31 * (8 / σ₂) * Real.sqrt (8 * Real.pi / σ₂))) / ((r : ℝ) * Real.sqrt r) := by
          have := add_le_add hpart1 hpart2
          rw [← add_div] at this
          exact this
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have htri : |(∫ θ in (-Real.pi)..(-θ₀), (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re +
        (∫ θ in (-θ₀)..θ₀, (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re +
        (∫ θ in θ₀..Real.pi, (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re| ≤
      |(∫ θ in (-Real.pi)..(-θ₀), (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re| +
      |(∫ θ in (-θ₀)..θ₀, (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re| +
      |(∫ θ in θ₀..Real.pi, (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re| := by
    exact le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
  have hsum := le_trans htri (add_le_add (add_le_add htail_left hinner) htail_right)
  have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  refine le_trans hmul (le_of_eq ?_)
  field_simp [hpi]
  ring

/-- Estimate C: strict concavity (negative second difference) in the central window `|w| <= sqrt(varP * r) / 2`. -/
lemma central_second_diff_upper {n : ℕ} {P : Polynomial ℝ} (hn : 2 ≤ n) (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {σ₂ θ₀ ρ : ℝ}
    (hσ₂_pos : 0 < σ₂) (hσ₂_le : σ₂ ≤ varP n P 1)
    (hθ₀_pos : 0 < θ₀) (hθ₀_le1 : θ₀ ≤ 1) (hθ₀_lepi : θ₀ ≤ Real.pi)
    (hθ₀_small : θ₀ ≤ σ₂ / (8 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4)))
    (hρ_nn : 0 ≤ ρ) (houter : ∀ θ : ℝ, θ₀ ≤ |θ| → |θ| ≤ Real.pi → ‖charFun n P 1 θ‖ ≤ ρ)
    {r : ℕ} (hr : 2 ≤ r) {w : ℝ} (hw : |w| ≤ Real.sqrt (varP n P 1 * (r : ℝ)) / 2) :
    (1 / (2 * Real.pi)) *
      (∫ θ in (-Real.pi)..Real.pi,
        ((2 * Real.cos θ - 2 : ℝ) : ℂ) * charFun n P 1 θ ^ r * Complex.exp (I * (w : ℂ) * θ)).re ≤
      - ((3 / 4) * Real.exp (-1 / 8) / (Real.sqrt (2 * Real.pi) * (varP n P 1 * Real.sqrt (varP n P 1)))) /
          ((r : ℝ) * Real.sqrt r) +
      (((31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 3 * Real.sqrt Real.pi) +
        (1 / 12) * (31 * (4 / σ₂) ^ 2 * Real.sqrt (4 * Real.pi / σ₂))) / (2 * Real.pi)) / (r : ℝ) ^ 2 +
      (31 * (8 / σ₂) * Real.sqrt (Real.pi / (σ₂ / 8)) / (2 * Real.pi)) *
        Real.exp (-(σ₂ * θ₀ ^ 2 / 4) * (r : ℝ)) +
      4 * ρ ^ r := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
  have hvar_pos : 0 < varP n P 1 := lt_of_lt_of_le hσ₂_pos hσ₂_le
  set g : ℝ → ℂ := fun θ => ((2 * Real.cos θ - 2 : ℝ) : ℂ) * charFun n P 1 θ ^ r * Complex.exp (I * (w : ℂ) * θ)
  have hcont_g : Continuous g := by dsimp [g]; unfold charFun; fun_prop
  rw [integral_split_symm hcont_g (θ₀ := θ₀)]
  simp only [Complex.add_re]
  have hcos_le4 : ∀ θ : ℝ, |2 * Real.cos θ - 2| ≤ 4 := by
    intro θ; rw [abs_le]; constructor <;> linarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  have htail_left : (∫ θ in (-Real.pi)..(-θ₀), g θ).re ≤ 4 * Real.pi * ρ ^ r := by
    calc (∫ θ in (-Real.pi)..(-θ₀), g θ).re
        ≤ |(∫ θ in (-Real.pi)..(-θ₀), g θ).re| := le_abs_self _
      _ ≤ ‖∫ θ in (-Real.pi)..(-θ₀), g θ‖ := Complex.abs_re_le_norm _
      _ ≤ ∫ θ in (-Real.pi)..(-θ₀), ‖g θ‖ := intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ _θ in (-Real.pi)..(-θ₀), 4 * ρ ^ r := by
          refine intervalIntegral.integral_mono_on (by linarith)
            (hcont_g.norm.intervalIntegrable _ _) intervalIntegrable_const fun θ hθ => ?_
          dsimp only [g]
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
            show I * (w : ℂ) * (θ : ℂ) = ((w * θ : ℝ) : ℂ) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, mul_one]
          have habs : |θ| = -θ := abs_of_nonpos (by linarith [hθ.2])
          exact mul_le_mul (hcos_le4 θ)
            (pow_le_pow_left₀ (norm_nonneg _) (houter θ (by linarith [hθ.2]) (by linarith [hθ.1])) r)
            (by positivity) (by norm_num)
      _ = (Real.pi - θ₀) * (4 * ρ ^ r) := by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ 4 * Real.pi * ρ ^ r := by nlinarith [pow_nonneg hρ_nn r]
  have htail_right : (∫ θ in θ₀..Real.pi, g θ).re ≤ 4 * Real.pi * ρ ^ r := by
    calc (∫ θ in θ₀..Real.pi, g θ).re
        ≤ |(∫ θ in θ₀..Real.pi, g θ).re| := le_abs_self _
      _ ≤ ‖∫ θ in θ₀..Real.pi, g θ‖ := Complex.abs_re_le_norm _
      _ ≤ ∫ θ in θ₀..Real.pi, ‖g θ‖ := intervalIntegral.norm_integral_le_integral_norm hθ₀_lepi
      _ ≤ ∫ _θ in θ₀..Real.pi, 4 * ρ ^ r := by
          refine intervalIntegral.integral_mono_on hθ₀_lepi
            (hcont_g.norm.intervalIntegrable _ _) intervalIntegrable_const fun θ hθ => ?_
          dsimp only [g]
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
            show I * (w : ℂ) * (θ : ℂ) = ((w * θ : ℝ) : ℂ) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, mul_one]
          have habs : |θ| = θ := abs_of_nonneg (by linarith [hθ.1])
          exact mul_le_mul (hcos_le4 θ)
            (pow_le_pow_left₀ (norm_nonneg _) (houter θ (by linarith [hθ.1]) (by linarith [hθ.2])) r)
            (by positivity) (by norm_num)
      _ = (Real.pi - θ₀) * (4 * ρ ^ r) := by simp only [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ 4 * Real.pi * ρ ^ r := by nlinarith [pow_nonneg hρ_nn r]
  -- Inner integral on `[-θ₀, θ₀]`
  set a := varP n P 1 * (r : ℝ) / 2
  have ha_pos : 0 < a := by dsimp [a]; positivity
  -- Split `g θ = main θ + err θ`
  let main_fn : ℝ → ℂ := fun θ =>
    ((-θ ^ 2 : ℝ) : ℂ) * ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ) * Complex.exp (I * (w : ℂ) * θ)
  have hmain_re : (∫ θ in (-θ₀)..θ₀, main_fn θ).re =
      -(∫ θ in (-θ₀)..θ₀, θ ^ 2 * Real.exp (-a * θ ^ 2) * Real.cos (w * θ)) := by
    rw [show (∫ θ in (-θ₀)..θ₀, main_fn θ).re = Complex.reCLM (∫ θ in (-θ₀)..θ₀, main_fn θ) from rfl,
      ← Complex.reCLM.intervalIntegral_comp_comm ((by fun_prop : Continuous _).intervalIntegrable _ _),
      ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    change (main_fn θ).re = _
    dsimp only [main_fn]
    rw [← Complex.ofReal_mul,
      show I * (w : ℂ) * (θ : ℂ) = ((w * θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  -- Full Gaussian second moment cosine integral >= c / (r * sqrt r)
  have hfull_main :
      ((3 / 4) * Real.exp (-1 / 8) * Real.sqrt (2 * Real.pi) / (varP n P 1 * Real.sqrt (varP n P 1))) /
          ((r : ℝ) * Real.sqrt r) ≤
        ∫ θ : ℝ, θ ^ 2 * Real.exp (-a * θ ^ 2) * Real.cos (w * θ) := by
    rw [gaussian_sq_cos_integral ha_pos w]
    have hw_sq : w ^ 2 ≤ varP n P 1 * (r : ℝ) / 4 := by
      have h1 : |w| ^ 2 ≤ (Real.sqrt (varP n P 1 * (r : ℝ)) / 2) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg w) hw 2
      rw [sq_abs, div_pow, Real.sq_sqrt (by positivity)] at h1
      linarith
    have h2a : 2 * a = varP n P 1 * (r : ℝ) := by dsimp [a]; ring
    have h4a : 4 * a = 2 * (varP n P 1 * (r : ℝ)) := by dsimp [a]; ring
    have hfac1 : (3 : ℝ) / 4 ≤ 1 - w ^ 2 / (2 * a) := by
      rw [h2a]
      have : w ^ 2 / (varP n P 1 * (r : ℝ)) ≤ 1 / 4 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    have hfac2 : Real.exp (-1 / 8) ≤ Real.exp (-w ^ 2 / (4 * a)) := by
      refine Real.exp_le_exp.mpr ?_
      rw [h4a, neg_div]
      have : w ^ 2 / (2 * (varP n P 1 * (r : ℝ))) ≤ 1 / 8 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      have hneg : -w ^ 2 / (2 * (varP n P 1 * (r : ℝ))) = -(w ^ 2 / (2 * (varP n P 1 * (r : ℝ)))) := by ring
      linarith
    have hsqrt_eq : Real.sqrt (Real.pi / a) =
        Real.sqrt (2 * Real.pi) / (Real.sqrt (varP n P 1) * Real.sqrt r) := by
      dsimp [a]
      rw [show Real.pi / (varP n P 1 * (r : ℝ) / 2) = (2 * Real.pi) / (varP n P 1 * (r : ℝ)) by ring,
        Real.sqrt_div (by positivity), Real.sqrt_mul hvar_pos.le]
    calc ((3 / 4) * Real.exp (-1 / 8) * Real.sqrt (2 * Real.pi) / (varP n P 1 * Real.sqrt (varP n P 1))) /
            ((r : ℝ) * Real.sqrt r)
        = ((3 / 4) / (2 * a)) * Real.sqrt (Real.pi / a) * Real.exp (-1 / 8) := by
            rw [h2a, hsqrt_eq]
            field_simp [hvar_pos.ne', hr_pos.ne', (Real.sqrt_pos.mpr hvar_pos).ne', (Real.sqrt_pos.mpr hr_pos).ne']
      _ ≤ ((1 - w ^ 2 / (2 * a)) / (2 * a)) * Real.sqrt (Real.pi / a) * Real.exp (-w ^ 2 / (4 * a)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hfac1 (by positivity)) (by positivity))
              hfac2 (by positivity) (by positivity)
  -- Tail of Gaussian second moment integral
  have hmain_tail :
      (∫ θ : ℝ, θ ^ 2 * Real.exp (-a * θ ^ 2) * Real.cos (w * θ)) -
        (∫ θ in (-θ₀)..θ₀, θ ^ 2 * Real.exp (-a * θ ^ 2) * Real.cos (w * θ)) ≤
        31 * (8 / σ₂) * Real.sqrt (Real.pi / (σ₂ / 8)) * Real.exp (-(σ₂ * θ₀ ^ 2 / 4) * (r : ℝ)) := by
    have hint_f : Integrable (fun θ : ℝ => θ ^ 2 * Real.exp (-a * θ ^ 2) * Real.cos (w * θ)) := by
      refine (gaussian_moment_integrable 2 (by omega) ha_pos).mono' (by fun_prop) (Eventually.of_forall fun θ => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg θ), abs_of_pos (Real.exp_pos _)]
      have hsq : θ ^ 2 = |θ| ^ 2 := (sq_abs θ).symm
      calc θ ^ 2 * Real.exp (-a * θ ^ 2) * |Real.cos (w * θ)|
          ≤ θ ^ 2 * Real.exp (-a * θ ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
        _ = |θ| ^ 2 * Real.exp (-a * θ ^ 2) := by rw [mul_one, hsq]
    have hcompl :
        (∫ θ : ℝ, θ ^ 2 * Real.exp (-a * θ ^ 2) * Real.cos (w * θ)) -
          (∫ θ in (-θ₀)..θ₀, θ ^ 2 * Real.exp (-a * θ ^ 2) * Real.cos (w * θ)) =
        ∫ θ in (Set.Ioc (-θ₀) θ₀)ᶜ, θ ^ 2 * Real.exp (-a * θ ^ 2) * Real.cos (w * θ) := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      have := integral_add_compl (measurableSet_Ioc (a := -θ₀) (b := θ₀)) hint_f
      linarith
    rw [hcompl]
    have hint_abs : Integrable (fun θ : ℝ => θ ^ 2 * Real.exp (-a * θ ^ 2)) := by
      simpa [sq_abs] using gaussian_moment_integrable 2 (by omega) ha_pos
    have h1 : ∫ θ in (Set.Ioc (-θ₀) θ₀)ᶜ, θ ^ 2 * Real.exp (-a * θ ^ 2) * Real.cos (w * θ) ≤
        ∫ θ in (Set.Ioc (-θ₀) θ₀)ᶜ, θ ^ 2 * Real.exp (-a * θ ^ 2) := by
      refine setIntegral_mono_on hint_f.integrableOn hint_abs.integrableOn measurableSet_Ioc.compl fun θ _ => ?_
      have hcos1 := Real.cos_le_one (w * θ)
      have hnn : 0 ≤ θ ^ 2 * Real.exp (-a * θ ^ 2) := by positivity
      nlinarith
    have h2 := gaussian_sq_tail_bound ha_pos hθ₀_pos
    have ha_ge : σ₂ / 2 ≤ a := by
      dsimp [a]
      have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
      nlinarith
    have ha_ge_r : σ₂ * (r : ℝ) / 4 ≤ a / 2 := by dsimp [a]; nlinarith
    have hdiv_le : 4 / a ≤ 8 / σ₂ := by
      rw [show (8 : ℝ) / σ₂ = 4 / (σ₂ / 2) by ring]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) ha_ge
    have hexp_le : Real.exp (-(a / 2) * θ₀ ^ 2) ≤ Real.exp (-(σ₂ * θ₀ ^ 2 / 4) * (r : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg θ₀])
    have hsq_le : Real.sqrt (Real.pi / (a / 4)) ≤ Real.sqrt (Real.pi / (σ₂ / 8)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith))
    calc _ ≤ 31 * (4 / a) * Real.exp (-(a / 2) * θ₀ ^ 2) * Real.sqrt (Real.pi / (a / 4)) := le_trans h1 h2
      _ ≤ 31 * (8 / σ₂) * Real.exp (-(σ₂ * θ₀ ^ 2 / 4) * (r : ℝ)) * Real.sqrt (Real.pi / (σ₂ / 8)) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hdiv_le (by norm_num)) hexp_le
            (by positivity) (by positivity)) hsq_le (by positivity) (by positivity)
      _ = 31 * (8 / σ₂) * Real.sqrt (Real.pi / (σ₂ / 8)) * Real.exp (-(σ₂ * θ₀ ^ 2 / 4) * (r : ℝ)) := by ring
  -- Difference `g θ - main_fn θ` on `[-θ₀, θ₀]`
  have hinner_err :
      |(∫ θ in (-θ₀)..θ₀, g θ).re - (∫ θ in (-θ₀)..θ₀, main_fn θ).re| ≤
        (31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 3 * Real.sqrt Real.pi +
          (1 / 12) * (31 * (4 / σ₂) ^ 2 * Real.sqrt (4 * Real.pi / σ₂))) / (r : ℝ) ^ 2 := by
    rw [← Complex.sub_re, ← intervalIntegral.integral_sub (hcont_g.intervalIntegrable _ _)
      ((by fun_prop : Continuous _).intervalIntegrable _ _)]
    have hpt : ∀ θ ∈ Set.Icc (-θ₀) θ₀,
        ‖g θ - main_fn θ‖ ≤
          (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (|θ| ^ 5 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2)) +
            (1 / 12) * (|θ| ^ 4 * Real.exp (-(σ₂ / 2 * (r : ℝ)) * θ ^ 2)) := by
      intro θ hθ
      have hθ_abs : |θ| ≤ θ₀ := abs_le.mpr hθ
      have hdecomp : g θ - main_fn θ =
          (((2 * Real.cos θ - 2 : ℝ) : ℂ) * (charFun n P 1 θ ^ r - ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)) +
            ((2 * Real.cos θ - 2 + θ ^ 2 : ℝ) : ℂ) * ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)) *
            Complex.exp (I * (w : ℂ) * θ) := by
        dsimp only [g, main_fn]; push_cast; ring
      rw [hdecomp, norm_mul,
        show I * (w : ℂ) * (θ : ℂ) = ((w * θ : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      have h1 : ‖((2 * Real.cos θ - 2 : ℝ) : ℂ) * (charFun n P 1 θ ^ r - ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ))‖ ≤
          (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (|θ| ^ 5 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hloc := charFun_pow_local_approx hn hdeg hpos zero_lt_one hσ₂_pos hσ₂_le
          (le_trans hθ_abs hθ₀_le1) (le_trans hθ_abs hθ₀_small) hr
        calc _ ≤ θ ^ 2 * ((r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * |θ| ^ 3 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2)) :=
              mul_le_mul (two_cos_sub_two_norm θ) hloc (norm_nonneg _) (sq_nonneg θ)
          _ = (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (|θ| ^ 5 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2)) := by
              rw [← sq_abs θ]; ring
      have h2 : ‖((2 * Real.cos θ - 2 + θ ^ 2 : ℝ) : ℂ) * ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ)‖ ≤
          (1 / 12) * (|θ| ^ 4 * Real.exp (-(σ₂ / 2 * (r : ℝ)) * θ ^ 2)) := by
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        have hexp_le : Real.exp (-a * θ ^ 2) ≤ Real.exp (-(σ₂ / 2 * (r : ℝ)) * θ ^ 2) := by
          have hnn : 0 ≤ (r : ℝ) * θ ^ 2 := by positivity
          exact Real.exp_le_exp.mpr (by dsimp [a]; nlinarith [hσ₂_le, hnn])
        calc _ ≤ (θ ^ 4 / 12) * Real.exp (-(σ₂ / 2 * (r : ℝ)) * θ ^ 2) :=
              mul_le_mul (cos_quad_approx θ) hexp_le (by positivity) (by positivity)
          _ = (1 / 12) * (|θ| ^ 4 * Real.exp (-(σ₂ / 2 * (r : ℝ)) * θ ^ 2)) := by
              rw [show θ ^ 4 = (θ ^ 2) ^ 2 by ring, ← sq_abs θ]; ring
      exact le_trans (norm_add_le _ _) (add_le_add h1 h2)
    have hp1 :
        ∫ θ in (-θ₀)..θ₀, (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (|θ| ^ 5 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2)) ≤
          31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 3 * Real.sqrt Real.pi / (r : ℝ) ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
      calc _ ≤ (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * ∫ θ : ℝ, |θ| ^ 5 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2) :=
            mul_le_mul_of_nonneg_left
              (interval_le_full_gaussian (fun _ => by positivity)
                (gaussian_moment_integrable 5 (by omega) (by positivity)) (by linarith)) (by positivity)
        _ ≤ (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) *
              ((31 * (2 / (σ₂ / 8)) ^ 3 * Real.sqrt Real.pi) / (r : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_left (gaussian_moment_5 (by positivity : 0 < σ₂ / 8) hr_pos) (by positivity)
        _ = 31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 3 * Real.sqrt Real.pi / (r : ℝ) ^ 2 := by
            rw [show 2 / (σ₂ / 8) = 16 / σ₂ by field_simp [hσ₂_pos.ne']; ring]
            field_simp [hr_pos.ne']
    have hp2 :
        ∫ θ in (-θ₀)..θ₀, (1 / 12) * (|θ| ^ 4 * Real.exp (-(σ₂ / 2 * (r : ℝ)) * θ ^ 2)) ≤
          (1 / 12) * (31 * (4 / σ₂) ^ 2 * Real.sqrt (4 * Real.pi / σ₂)) / (r : ℝ) ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
      have hsr_ge1 : (1 : ℝ) ≤ Real.sqrt r := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ r by omega))
      calc _ ≤ (1 / 12) * ∫ θ : ℝ, |θ| ^ 4 * Real.exp (-(σ₂ / 2 * (r : ℝ)) * θ ^ 2) :=
            mul_le_mul_of_nonneg_left
              (interval_le_full_gaussian (fun _ => by positivity)
                (gaussian_moment_integrable 4 (by omega) (by positivity)) (by linarith)) (by norm_num)
        _ ≤ (1 / 12) * ((31 * (2 / (σ₂ / 2)) ^ 2 * Real.sqrt (2 * Real.pi / (σ₂ / 2))) / ((r : ℝ) ^ 2 * Real.sqrt r)) :=
            mul_le_mul_of_nonneg_left (gaussian_moment_4 (by positivity : 0 < σ₂ / 2) hr_pos) (by norm_num)
        _ ≤ (1 / 12) * ((31 * (4 / σ₂) ^ 2 * Real.sqrt (4 * Real.pi / σ₂)) / (r : ℝ) ^ 2) := by
            rw [show 2 / (σ₂ / 2) = 4 / σ₂ by field_simp [hσ₂_pos.ne']; ring,
              show 2 * Real.pi / (σ₂ / 2) = 4 * Real.pi / σ₂ by field_simp [hσ₂_pos.ne']; ring]
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
        _ = (1 / 12) * (31 * (4 / σ₂) ^ 2 * Real.sqrt (4 * Real.pi / σ₂)) / (r : ℝ) ^ 2 := by ring
    calc |(∫ θ in (-θ₀)..θ₀, g θ - main_fn θ).re|
        ≤ ‖∫ θ in (-θ₀)..θ₀, g θ - main_fn θ‖ := Complex.abs_re_le_norm _
      _ ≤ ∫ θ in (-θ₀)..θ₀, ‖g θ - main_fn θ‖ := intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ θ in (-θ₀)..θ₀,
            ((r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (|θ| ^ 5 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2)) +
              (1 / 12) * (|θ| ^ 4 * Real.exp (-(σ₂ / 2 * (r : ℝ)) * θ ^ 2))) :=
          intervalIntegral.integral_mono_on (by linarith)
            ((by fun_prop : Continuous _).intervalIntegrable _ _)
            ((by fun_prop : Continuous _).intervalIntegrable _ _) hpt
      _ = (∫ θ in (-θ₀)..θ₀, (r : ℝ) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (|θ| ^ 5 * Real.exp (-(σ₂ / 8 * (r : ℝ)) * θ ^ 2))) +
          (∫ θ in (-θ₀)..θ₀, (1 / 12) * (|θ| ^ 4 * Real.exp (-(σ₂ / 2 * (r : ℝ)) * θ ^ 2))) :=
          intervalIntegral.integral_add ((by fun_prop : Continuous _).intervalIntegrable _ _)
            ((by fun_prop : Continuous _).intervalIntegrable _ _)
      _ ≤ _ := by
          have := add_le_add hp1 hp2
          rw [← add_div] at this
          exact this
  have herr_hi := (abs_le.mp hinner_err).2
  have hsum_le :
      (∫ θ in (-Real.pi)..(-θ₀), g θ).re + (∫ θ in (-θ₀)..θ₀, g θ).re + (∫ θ in θ₀..Real.pi, g θ).re ≤
      - (((3 / 4) * Real.exp (-1 / 8) * Real.sqrt (2 * Real.pi) / (varP n P 1 * Real.sqrt (varP n P 1))) /
          ((r : ℝ) * Real.sqrt r)) +
      (31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 3 * Real.sqrt Real.pi +
        (1 / 12) * (31 * (4 / σ₂) ^ 2 * Real.sqrt (4 * Real.pi / σ₂))) / (r : ℝ) ^ 2 +
      31 * (8 / σ₂) * Real.sqrt (Real.pi / (σ₂ / 8)) * Real.exp (-(σ₂ * θ₀ ^ 2 / 4) * (r : ℝ)) +
      8 * Real.pi * ρ ^ r := by
    linarith [hmain_re, hfull_main, hmain_tail, htail_left, htail_right]
  have hmul := mul_le_mul_of_nonneg_left hsum_le (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
  have hmain_pi :
      1 / (2 * Real.pi) *
        (((3 / 4) * Real.exp (-1 / 8) * Real.sqrt (2 * Real.pi) / (varP n P 1 * Real.sqrt (varP n P 1))) /
          ((r : ℝ) * Real.sqrt r)) =
      ((3 / 4) * Real.exp (-1 / 8) / (Real.sqrt (2 * Real.pi) * (varP n P 1 * Real.sqrt (varP n P 1)))) /
        ((r : ℝ) * Real.sqrt r) := by
    have h2pi : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
      Real.mul_self_sqrt (by positivity)
    have hsne : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hvne : varP n P 1 * Real.sqrt (varP n P 1) ≠ 0 := by positivity
    have hrne : (r : ℝ) * Real.sqrt r ≠ 0 := by positivity
    field_simp [hsne, hvne, hrne, Real.pi_pos.ne']
    linarith [h2pi]
  refine le_trans hmul (le_of_eq ?_)
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [mul_add, mul_add, mul_add, mul_neg, hmain_pi]
  field_simp [hpi]
  ring

/-!
## 5. Choosing `t_min, t_max, r` and gluing all regions into unimodality
-/

lemma exists_tilt_interval {n : ℕ} {P : Polynomial ℝ} (hn : 2 ≤ n) (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t_min t_max : ℝ, 0 < t_min ∧ t_min < 1 ∧ 1 < t_max ∧
      meanP n P t_min ≤ δ ∧ (n : ℝ) - δ ≤ meanP n P t_max := by
  let S1 : ℝ := ∑ k ∈ Finset.range (n + 1), (k : ℝ) * P.coeff k
  have hS1_nn : 0 ≤ S1 := Finset.sum_nonneg fun k hk =>
    mul_nonneg (Nat.cast_nonneg k) (hpos k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).le
  let S2 : ℝ := ∑ k ∈ Finset.range (n + 1), ((n : ℝ) - (k : ℝ)) * P.coeff k
  have hS2_nn : 0 ≤ S2 := Finset.sum_nonneg fun k hk => by
    have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact mul_nonneg (by linarith) (hpos k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).le
  have ha0 : 0 < P.coeff 0 := hpos 0 (Nat.zero_le n)
  have han : 0 < P.coeff n := hpos n le_rfl
  let t_min : ℝ := min (1 / 2) (δ * P.coeff 0 / (S1 + 1))
  let t_max : ℝ := max 2 ((S2 + 1) / (δ * P.coeff n))
  refine ⟨t_min, t_max, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [t_min]; exact lt_min (by norm_num) (by positivity)
  · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · have ht_pos : 0 < t_min := lt_min (by norm_num) (by positivity)
    have ht_le1 : t_min ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
    have hEv_ge : P.coeff 0 ≤ P.eval t_min := by
      rw [evalP_eq_sum hdeg t_min]
      have hmem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      have h := Finset.single_le_sum (fun k hk => mul_nonneg
        (hpos k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).le (pow_nonneg ht_pos.le k)) hmem
      simpa using h
    have hnum_le : ∑ k ∈ Finset.range (n + 1), (k : ℝ) * (P.coeff k * t_min ^ k) ≤ t_min * S1 := by
      dsimp only [S1]
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      cases k with
      | zero => simp
      | succ k' =>
        have hpow : t_min ^ (k' + 1) ≤ t_min := by
          rw [pow_succ']
          calc t_min * t_min ^ k' ≤ t_min * 1 :=
                mul_le_mul_of_nonneg_left (pow_le_one₀ ht_pos.le ht_le1) ht_pos.le
            _ = t_min := mul_one _
        have ha : 0 ≤ ((k' + 1 : ℕ) : ℝ) * P.coeff (k' + 1) :=
          mul_nonneg (Nat.cast_nonneg _) (hpos (k' + 1) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).le
        have := mul_le_mul_of_nonneg_left hpow ha
        linarith
    unfold meanP prob
    calc ∑ k ∈ Finset.range (n + 1), (k : ℝ) * (P.coeff k * t_min ^ k / P.eval t_min)
        = (∑ k ∈ Finset.range (n + 1), (k : ℝ) * (P.coeff k * t_min ^ k)) / P.eval t_min := by
            rw [Finset.sum_div]; refine Finset.sum_congr rfl fun k _ => by ring
      _ ≤ (t_min * S1) / P.coeff 0 :=
            div_le_div₀ (by positivity) hnum_le ha0 hEv_ge
      _ ≤ (t_min * (S1 + 1)) / P.coeff 0 := by
            exact div_le_div_of_nonneg_right (by nlinarith) ha0.le
      _ ≤ δ := by
            have htm : t_min ≤ δ * P.coeff 0 / (S1 + 1) := min_le_right _ _
            have h1 : t_min * (S1 + 1) ≤ δ * P.coeff 0 := (le_div_iff₀ (by positivity)).mp htm
            exact (div_le_iff₀ ha0).mpr h1
  · have ht_ge1 : 1 ≤ t_max := le_trans (by norm_num) (le_max_left _ _)
    have ht_pos : 0 < t_max := by linarith
    have hEv_ge : P.coeff n * t_max ^ n ≤ P.eval t_max := by
      rw [evalP_eq_sum hdeg t_max]
      have hmem : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      exact Finset.single_le_sum (fun k hk => mul_nonneg
        (hpos k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).le (pow_nonneg ht_pos.le k)) hmem
    have hdiff_eq : (n : ℝ) - meanP n P t_max =
        (∑ k ∈ Finset.range (n + 1), ((n : ℝ) - (k : ℝ)) * (P.coeff k * t_max ^ k)) / P.eval t_max := by
      have hsum1 := sum_prob_eq_one hdeg hpos ht_pos
      unfold meanP prob at hsum1 ⊢
      calc (n : ℝ) - ∑ k ∈ Finset.range (n + 1), (k : ℝ) * (P.coeff k * t_max ^ k / P.eval t_max)
          = (n : ℝ) * (∑ k ∈ Finset.range (n + 1), P.coeff k * t_max ^ k / P.eval t_max) -
              ∑ k ∈ Finset.range (n + 1), (k : ℝ) * (P.coeff k * t_max ^ k / P.eval t_max) := by
              rw [hsum1, mul_one]
        _ = ∑ k ∈ Finset.range (n + 1), ((n : ℝ) - (k : ℝ)) * (P.coeff k * t_max ^ k / P.eval t_max) := by
              rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun k _ => by ring
        _ = (∑ k ∈ Finset.range (n + 1), ((n : ℝ) - (k : ℝ)) * (P.coeff k * t_max ^ k)) / P.eval t_max := by
              rw [Finset.sum_div]; refine Finset.sum_congr rfl fun k _ => by ring
    have hnum_le : ∑ k ∈ Finset.range (n + 1), ((n : ℝ) - (k : ℝ)) * (P.coeff k * t_max ^ k) ≤
        t_max ^ (n - 1) * S2 := by
      dsimp only [S2]
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      by_cases hkeq : k = n
      · subst hkeq; simp
      · have hk_le : k ≤ n - 1 := by omega
        have hpow : t_max ^ k ≤ t_max ^ (n - 1) := pow_le_pow_right₀ ht_ge1 hk_le
        have hc : 0 ≤ ((n : ℝ) - (k : ℝ)) * P.coeff k := by
          have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
          exact mul_nonneg (by linarith) (hpos k hkn).le
        have := mul_le_mul_of_nonneg_left hpow hc
        linarith
    have hdiff_le : (n : ℝ) - meanP n P t_max ≤ δ := by
      rw [hdiff_eq]
      calc (∑ k ∈ Finset.range (n + 1), ((n : ℝ) - (k : ℝ)) * (P.coeff k * t_max ^ k)) / P.eval t_max
          ≤ (t_max ^ (n - 1) * S2) / (P.coeff n * t_max ^ n) :=
            div_le_div₀ (by positivity) hnum_le (by positivity) hEv_ge
        _ = S2 / (P.coeff n * t_max) := by
            have hpow : t_max ^ n = t_max ^ (n - 1) * t_max := by
              conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
            rw [hpow]
            field_simp [han.ne', ht_pos.ne', (pow_pos ht_pos (n - 1)).ne']
        _ ≤ (S2 + 1) / (P.coeff n * t_max) := div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ ≤ δ := by
            have htm : (S2 + 1) / (δ * P.coeff n) ≤ t_max := le_max_right _ _
            have h1 : S2 + 1 ≤ t_max * (δ * P.coeff n) := (div_le_iff₀ (by positivity)).mp htm
            exact (div_le_iff₀ (by positivity)).mpr (by linarith)
    linarith

lemma tendsto_pow_mul_exp_neg {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℕ => ((r : ℝ) * Real.sqrt r) * Real.exp (-c * (r : ℝ))) atTop (𝓝 0) := by
  have hdom : ∀ r : ℕ, 1 ≤ r →
      0 ≤ ((r : ℝ) * Real.sqrt r) * Real.exp (-c * (r : ℝ)) ∧
      ((r : ℝ) * Real.sqrt r) * Real.exp (-c * (r : ℝ)) ≤ (6 / c ^ 3) / (r : ℝ) := by
    intro r hr
    have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
    have hsr : Real.sqrt r ≤ (r : ℝ) := by
      have : (r : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith [show (1 : ℝ) ≤ (r : ℝ) by exact_mod_cast hr]
      calc Real.sqrt r ≤ Real.sqrt ((r : ℝ) ^ 2) := Real.sqrt_le_sqrt this
        _ = (r : ℝ) := Real.sqrt_sq hr_pos.le
    -- `exp (c * r) >= (c * r)^3 / 6`!
    have hexp : (c * (r : ℝ)) ^ 3 / 6 ≤ Real.exp (c * (r : ℝ)) := by
      have h := Real.sum_le_exp_of_nonneg (show 0 ≤ c * (r : ℝ) by positivity) 4
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one] at h
      have h3 : (3 : ℕ).factorial = 6 := by norm_num
      have h2 : (2 : ℕ).factorial = 2 := by norm_num
      rw [h3, h2] at h
      have hnn1 : 0 ≤ c * (r : ℝ) := by positivity
      have hnn2 : 0 ≤ (c * (r : ℝ)) ^ 2 / (2 : ℝ) := by positivity
      push_cast at h
      linarith
    constructor
    · positivity
    · rw [show -c * (r : ℝ) = -(c * (r : ℝ)) by ring, Real.exp_neg]
      have hinv : (Real.exp (c * (r : ℝ)))⁻¹ ≤ 6 / (c * (r : ℝ)) ^ 3 := by
        rw [inv_eq_one_div, show 6 / (c * (r : ℝ)) ^ 3 = 1 / ((c * (r : ℝ)) ^ 3 / 6) by ring]
        exact one_div_le_one_div_of_le (by positivity) hexp
      calc (r : ℝ) * Real.sqrt r * (Real.exp (c * (r : ℝ)))⁻¹
          ≤ (r : ℝ) ^ 2 * (6 / (c * (r : ℝ)) ^ 3) := by
            refine mul_le_mul (by nlinarith) hinv (by positivity) (by positivity)
        _ = (6 / c ^ 3) / (r : ℝ) := by field_simp [hc.ne', hr_pos.ne']
  have hlim : Tendsto (fun r : ℕ => (6 / c ^ 3) / (r : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  exact squeeze_zero'
    (by filter_upwards [eventually_ge_atTop 1] with r hr using (hdom r hr).1)
    (by filter_upwards [eventually_ge_atTop 1] with r hr using (hdom r hr).2) hlim

lemma tendsto_pow_mul_geom {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun r : ℕ => ((r : ℝ) * Real.sqrt r) * ρ ^ r) atTop (𝓝 0) := by
  by_cases h0 : ρ = 0
  · subst h0
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with r hr
    rw [zero_pow (by omega), mul_zero]
  · have hρ_pos : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm h0)
    have hc : 0 < -Real.log ρ := by
      have : Real.log ρ < 0 := Real.log_neg hρ_pos hρ1
      linarith
    have heq : (fun r : ℕ => ((r : ℝ) * Real.sqrt r) * ρ ^ r) =
        fun r : ℕ => ((r : ℝ) * Real.sqrt r) * Real.exp (-(-Real.log ρ) * (r : ℝ)) := by
      funext r
      rw [neg_neg, mul_comm (Real.log ρ) (r : ℝ), Real.exp_nat_mul, Real.exp_log hρ_pos]
    rw [heq]
    exact tendsto_pow_mul_exp_neg hc

lemma exists_large_r {n : ℕ} {μ σ δ t_min ρ cA CA1 CA2 cg CB cC CC1 CC2 ct : ℝ}
    (hδ_pos : 0 < δ) (hμδ : 0 < μ - δ) (hnδ : 0 < (n : ℝ) - δ - μ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcA_pos : 0 < cA) (hcg_pos : 0 < cg) (hcC_pos : 0 < cC) (hct_pos : 0 < ct) :
    ∃ r : ℕ,
      2 ≤ r ∧
      (1 : ℝ) ≤ δ * (r : ℝ) ∧
      (σ / 2) * Real.sqrt r < (μ - δ) * (r : ℝ) ∧
      (σ / 2) * Real.sqrt r < ((n : ℝ) - δ - μ) * (r : ℝ) ∧
      CA1 / Real.sqrt r + CA2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ))) +
        (((r : ℝ) * Real.sqrt r) * ρ ^ r) < cA / 2 ∧
      (1 / t_min) * (CB / Real.sqrt r + 2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) < ct * (cA / 2) ∧
      CC1 / Real.sqrt r + CC2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ))) +
        4 * (((r : ℝ) * Real.sqrt r) * ρ ^ r) < cC := by
  have hsr_top : Tendsto (fun r : ℕ => Real.sqrt r) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have htail_exp : Tendsto (fun r : ℕ => ((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ))) atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg hcg_pos
  have htail_rho : Tendsto (fun r : ℕ => ((r : ℝ) * Real.sqrt r) * ρ ^ r) atTop (𝓝 0) :=
    tendsto_pow_mul_geom hρ0 hρ1
  have h1 : ∀ᶠ r : ℕ in atTop, 2 ≤ r := eventually_ge_atTop 2
  have h2 : ∀ᶠ r : ℕ in atTop, (1 : ℝ) ≤ δ * (r : ℝ) :=
    (Tendsto.const_mul_atTop hδ_pos tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have h3 : ∀ᶠ r : ℕ in atTop, (σ / 2) * Real.sqrt r < (μ - δ) * (r : ℝ) := by
    have hlim : Tendsto (fun r : ℕ => (σ / 2) / Real.sqrt r) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsr_top
    filter_upwards [hlim.eventually (gt_mem_nhds hμδ), eventually_ge_atTop 1] with r hr hge
    have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
    have hsr_pos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr_pos
    have hsq : Real.sqrt r * Real.sqrt r = (r : ℝ) := Real.mul_self_sqrt hr_pos.le
    have hmul : σ / 2 < (μ - δ) * Real.sqrt r := (div_lt_iff₀ hsr_pos).mp hr
    have hmul2 := mul_lt_mul_of_pos_right hmul hsr_pos
    rw [mul_assoc, hsq] at hmul2
    exact hmul2
  have h4 : ∀ᶠ r : ℕ in atTop, (σ / 2) * Real.sqrt r < ((n : ℝ) - δ - μ) * (r : ℝ) := by
    have hlim : Tendsto (fun r : ℕ => (σ / 2) / Real.sqrt r) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsr_top
    filter_upwards [hlim.eventually (gt_mem_nhds hnδ), eventually_ge_atTop 1] with r hr hge
    have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
    have hsr_pos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr_pos
    have hsq : Real.sqrt r * Real.sqrt r = (r : ℝ) := Real.mul_self_sqrt hr_pos.le
    have hmul : σ / 2 < ((n : ℝ) - δ - μ) * Real.sqrt r := (div_lt_iff₀ hsr_pos).mp hr
    have hmul2 := mul_lt_mul_of_pos_right hmul hsr_pos
    rw [mul_assoc, hsq] at hmul2
    exact hmul2
  have h5 : ∀ᶠ r : ℕ in atTop,
      CA1 / Real.sqrt r + CA2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ))) +
        (((r : ℝ) * Real.sqrt r) * ρ ^ r) < cA / 2 := by
    have hlim : Tendsto (fun r : ℕ =>
        CA1 / Real.sqrt r + CA2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ))) +
          (((r : ℝ) * Real.sqrt r) * ρ ^ r)) atTop (𝓝 0) := by
      have := (((tendsto_const_nhds (x := CA1)).div_atTop hsr_top).add (htail_exp.const_mul CA2)).add htail_rho
      simpa using this
    exact hlim.eventually (gt_mem_nhds (by positivity : 0 < cA / 2))
  have h6 : ∀ᶠ r : ℕ in atTop,
      (1 / t_min) * (CB / Real.sqrt r + 2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) < ct * (cA / 2) := by
    have hlim : Tendsto (fun r : ℕ =>
        (1 / t_min) * (CB / Real.sqrt r + 2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r))) atTop (𝓝 0) := by
      have := (((tendsto_const_nhds (x := CB)).div_atTop hsr_top).add (htail_rho.const_mul 2)).const_mul (1 / t_min)
      simpa using this
    exact hlim.eventually (gt_mem_nhds (by positivity : 0 < ct * (cA / 2)))
  have h7 : ∀ᶠ r : ℕ in atTop,
      CC1 / Real.sqrt r + CC2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ))) +
        4 * (((r : ℝ) * Real.sqrt r) * ρ ^ r) < cC := by
    have hlim : Tendsto (fun r : ℕ =>
        CC1 / Real.sqrt r + CC2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ))) +
          4 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) atTop (𝓝 0) := by
      have := (((tendsto_const_nhds (x := CC1)).div_atTop hsr_top).add (htail_exp.const_mul CC2)).add (htail_rho.const_mul 4)
      simpa using this
    exact hlim.eventually (gt_mem_nhds hcC_pos)
  have hall : ∀ᶠ r : ℕ in atTop,
      2 ≤ r ∧ (1 : ℝ) ≤ δ * (r : ℝ) ∧
      (σ / 2) * Real.sqrt r < (μ - δ) * (r : ℝ) ∧
      (σ / 2) * Real.sqrt r < ((n : ℝ) - δ - μ) * (r : ℝ) ∧
      CA1 / Real.sqrt r + CA2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ))) +
        (((r : ℝ) * Real.sqrt r) * ρ ^ r) < cA / 2 ∧
      (1 / t_min) * (CB / Real.sqrt r + 2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) < ct * (cA / 2) ∧
      CC1 / Real.sqrt r + CC2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ))) +
        4 * (((r : ℝ) * Real.sqrt r) * ρ ^ r) < cC := by
    filter_upwards [h1, h2, h3, h4, h5, h6, h7] with r a1 a2 a3 a4 a5 a6 a7
    exact ⟨a1, a2, a3, a4, a5, a6, a7⟩
  exact hall.exists

lemma region_left_mono {n : ℕ} {P : Polynomial ℝ} (hn : 2 ≤ n) (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i)
    {σ δ t_min t_max ρ cA CA1 CA2 cg CB ct : ℝ}
    (hσ_pos : 0 < σ) (hδ1 : δ ≤ P.coeff 1 / (2 * (P.coeff 0 + P.coeff 1)))
    (ht_min_pos : 0 < t_min) (ht_min_lt1 : t_min < 1) (ht_max_gt1 : 1 < t_max)
    (hmean_min : meanP n P t_min ≤ δ) (hmean_max : (n : ℝ) - δ ≤ meanP n P t_max)
    (hρ_nn : 0 ≤ ρ) (hcA_pos : 0 < cA) (hCA2_nn : 0 ≤ CA2) (hCB_nn : 0 ≤ CB)
    (hct_def : ct = (t_min * σ) / (2 * (n : ℝ) ^ 2 * t_max))
    (hmean_strict : StrictMonoOn (meanP n P) (Set.Icc t_min t_max))
    (hmean_lip : ∀ t ∈ Set.Icc t_min t_max, |meanP n P t - meanP n P 1| ≤ ((n : ℝ) ^ 2 / t_min) * |t - 1|)
    {r : ℕ} (hr2 : 2 ≤ r) (hδr : (1 : ℝ) ≤ δ * (r : ℝ))
    (hwinR : (σ / 2) * Real.sqrt r < ((n : ℝ) - δ - meanP n P 1) * (r : ℝ))
    (hA_inst : ∀ t ∈ Set.Icc t_min t_max,
      cA / Real.sqrt r - CA1 / (r : ℝ) - CA2 * Real.exp (-cg * (r : ℝ)) - ρ ^ r ≤
        (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, charFun n P t θ ^ r).re)
    (hB_inst : ∀ t ∈ Set.Icc t_min t_max,
      |(1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re| ≤
        CB / ((r : ℝ) * Real.sqrt r) + 2 * ρ ^ r)
    (hEstA : CA1 / Real.sqrt r + CA2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ))) +
      (((r : ℝ) * Real.sqrt r) * ρ ^ r) < cA / 2)
    (hEstB : (1 / t_min) * (CB / Real.sqrt r + 2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) < ct * (cA / 2))
    (m : ℕ) (hm : (m : ℝ) ≤ meanP n P 1 * (r : ℝ) - (σ / 2) * Real.sqrt r) :
    (P ^ r).coeff m ≤ (P ^ r).coeff (m + 1) := by
  have ha0 : 0 < P.coeff 0 := hpos 0 (by omega)
  have ha1 : 0 < P.coeff 1 := hpos 1 (by omega)
  have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
  have hsr_pos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr_pos
  have hr_ge1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
  have hσr : 0 < (σ / 2) * Real.sqrt r := by positivity
  have hct_pos : 0 < ct := by rw [hct_def]; positivity
  have h1_mem : (1 : ℝ) ∈ Set.Icc t_min t_max := ⟨ht_min_lt1.le, ht_max_gt1.le⟩
  by_cases htail : (m : ℝ) ≤ δ * (r : ℝ)
  · refine left_tail_mono hn hdeg hpos (by omega) ?_
    have h2δr : 2 * δ * (r : ℝ) ≤ P.coeff 1 / (P.coeff 0 + P.coeff 1) * (r : ℝ) := by
      have : 2 * δ ≤ P.coeff 1 / (P.coeff 0 + P.coeff 1) := by
        have := (le_div_iff₀ (by positivity : 0 < 2 * (P.coeff 0 + P.coeff 1))).mp hδ1
        exact (le_div_iff₀ (by positivity)).mpr (by linarith)
      nlinarith
    have hm1 : ((m + 1 : ℕ) : ℝ) ≤ P.coeff 1 * (r : ℝ) / (P.coeff 0 + P.coeff 1) := by
      rw [mul_div_right_comm]
      push_cast; linarith
    have hmul := (le_div_iff₀ (by positivity : 0 < P.coeff 0 + P.coeff 1)).mp hm1
    push_cast at hmul ⊢
    linarith
  · push Not at htail
    have hm_in : (m : ℝ) / (r : ℝ) ∈ Set.Icc (meanP n P t_min) (meanP n P t_max) := by
      constructor
      · exact le_trans hmean_min ((le_div_iff₀ hr_pos).mpr htail.le)
      · exact le_trans ((div_le_iff₀ hr_pos).mpr (by linarith [hwinR, hσr])) hmean_max
    have hcont_m : ContinuousOn (meanP n P) (Set.Icc t_min t_max) := fun s hs =>
      (meanP_hasDerivAt hdeg hpos (lt_of_lt_of_le ht_min_pos hs.1)).continuousAt.continuousWithinAt
    obtain ⟨t, ht_mem, ht_eq⟩ := intermediate_value_Icc (by linarith : t_min ≤ t_max) hcont_m hm_in
    have ht_pos : 0 < t := lt_of_lt_of_le ht_min_pos ht_mem.1
    have hμt_lt : meanP n P t < meanP n P 1 := by
      rw [ht_eq, div_lt_iff₀ hr_pos]; linarith [hσr]
    have ht_lt1 : t < 1 := by
      by_contra hge; push Not at hge
      rcases eq_or_lt_of_le hge with rfl | hgt
      · linarith
      · exact absurd (hmean_strict h1_mem ht_mem hgt) (not_lt.mpr hμt_lt.le)
    have h1_sub_t : ct / Real.sqrt r ≤ t⁻¹ - 1 := by
      have hlip := hmean_lip t ht_mem
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at hlip
      have hgap : (σ / 2) / Real.sqrt r ≤ meanP n P 1 - meanP n P t := by
        rw [ht_eq, div_le_iff₀ hsr_pos]
        have hsq : Real.sqrt r * Real.sqrt r = (r : ℝ) := Real.mul_self_sqrt hr_pos.le
        have hmul : (m : ℝ) / (r : ℝ) * (r : ℝ) = (m : ℝ) := div_mul_cancel₀ _ hr_pos.ne'
        have h1 : (meanP n P 1 - (m : ℝ) / (r : ℝ)) * (r : ℝ) = meanP n P 1 * (r : ℝ) - (m : ℝ) := by
          rw [sub_mul, hmul]
        have h2 : (σ / 2) * Real.sqrt r ≤ (meanP n P 1 - (m : ℝ) / (r : ℝ)) * (Real.sqrt r * Real.sqrt r) := by
          rw [hsq, h1]; linarith
        have h3 : (σ / 2) * Real.sqrt r ≤ ((meanP n P 1 - (m : ℝ) / (r : ℝ)) * Real.sqrt r) * Real.sqrt r := by
          simpa [mul_assoc] using h2
        exact le_of_mul_le_mul_right h3 hsr_pos
      have ht_gap : (t_min * σ) / (2 * (n : ℝ) ^ 2 * Real.sqrt r) ≤ 1 - t := by
        have : (σ / 2) / Real.sqrt r ≤ ((n : ℝ) ^ 2 / t_min) * (1 - t) := le_trans hgap (by linarith)
        rw [div_le_iff₀ (by positivity)]
        have h1 : ((n : ℝ) ^ 2 / t_min) * (1 - t) * (t_min * Real.sqrt r) =
            (n : ℝ) ^ 2 * Real.sqrt r * (1 - t) := by field_simp [ht_min_pos.ne']
        have h2 : (σ / 2) / Real.sqrt r * (t_min * Real.sqrt r) = (t_min * σ) / 2 := by
          field_simp [hsr_pos.ne']
        have h3 := mul_le_mul_of_nonneg_right this (by positivity : 0 ≤ t_min * Real.sqrt r)
        rw [h1, h2] at h3
        linarith
      have hct_le : ct / Real.sqrt r ≤ 1 - t := by
        refine le_trans ?_ ht_gap
        rw [hct_def, div_div]
        have hden : 2 * (n : ℝ) ^ 2 * Real.sqrt r ≤ 2 * (n : ℝ) ^ 2 * t_max * Real.sqrt r := by
          calc 2 * (n : ℝ) ^ 2 * Real.sqrt r
              = 1 * (2 * (n : ℝ) ^ 2 * Real.sqrt r) := (one_mul _).symm
            _ ≤ t_max * (2 * (n : ℝ) ^ 2 * Real.sqrt r) :=
                mul_le_mul_of_nonneg_right ht_max_gt1.le (by positivity)
            _ = 2 * (n : ℝ) ^ 2 * t_max * Real.sqrt r := by ring
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      have hinv_ge : 1 - t ≤ t⁻¹ - 1 := by
        have hle1 : (1 - t) * t ≤ 1 - t := mul_le_of_le_one_right (by linarith) ht_lt1.le
        have hle2 : 1 - t ≤ (1 - t) / t := (le_div_iff₀ ht_pos).mpr hle1
        rw [sub_div, div_self ht_pos.ne', one_div] at hle2
        exact hle2
      exact le_trans hct_le hinv_ge
    have hm_eq : meanP n P t * (r : ℝ) - (m : ℝ) = 0 := by
      rw [ht_eq, div_mul_cancel₀ _ hr_pos.ne', sub_self]
    have hbm_eq : t ^ m * (P ^ r).coeff m / (P.eval t) ^ r =
        (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, charFun n P t θ ^ r).re := by
      simpa [hm_eq] using tilted_coeff_fourier hdeg hpos ht_pos r m
    have hbm1_eq : t ^ (m + 1) * (P ^ r).coeff (m + 1) / (P.eval t) ^ r -
        t ^ m * (P ^ r).coeff m / (P.eval t) ^ r =
        (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re := by
      have h1 := tilted_coeff_fourier hdeg hpos ht_pos r (m + 1)
      rw [h1, hbm_eq, ← mul_sub, ← Complex.sub_re,
        ← intervalIntegral.integral_sub ((by unfold charFun; fun_prop : Continuous _).intervalIntegrable _ _)
          ((by unfold charFun; fun_prop : Continuous _).intervalIntegrable _ _)]
      congr 2
      refine intervalIntegral.integral_congr fun θ _ => ?_
      have hexp : meanP n P t * (r : ℝ) - ((m + 1 : ℕ) : ℝ) = -1 := by push_cast; linarith
      rw [hexp]
      have : I * ((-1 : ℝ) : ℂ) * (θ : ℂ) = -I * (θ : ℂ) := by push_cast; ring
      rw [this]; ring
    have hbm_lo : (cA / 2) / Real.sqrt r ≤ t ^ m * (P ^ r).coeff m / (P.eval t) ^ r := by
      rw [hbm_eq]
      have hA := hA_inst t ht_mem
      have hsq : Real.sqrt r * Real.sqrt r = (r : ℝ) := Real.mul_self_sqrt hr_pos.le
      have hA2 : CA1 / (r : ℝ) = (CA1 / Real.sqrt r) / Real.sqrt r := by rw [div_div, hsq]
      have hA3 : CA2 * Real.exp (-cg * (r : ℝ)) ≤
          (CA2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ)))) / Real.sqrt r := by
        rw [le_div_iff₀ hsr_pos]
        have hle : Real.sqrt r ≤ (r : ℝ) * Real.sqrt r := le_mul_of_one_le_left hsr_pos.le hr_ge1
        have hmul := mul_le_mul_of_nonneg_left hle (mul_nonneg hCA2_nn (Real.exp_pos (-cg * (r : ℝ))).le)
        linarith
      have hA4 : ρ ^ r ≤ (((r : ℝ) * Real.sqrt r) * ρ ^ r) / Real.sqrt r := by
        rw [le_div_iff₀ hsr_pos]
        have hle : Real.sqrt r ≤ (r : ℝ) * Real.sqrt r := le_mul_of_one_le_left hsr_pos.le hr_ge1
        have hmul := mul_le_mul_of_nonneg_right hle (pow_nonneg hρ_nn r)
        linarith
      have hsub : (cA / 2) / Real.sqrt r ≤
          cA / Real.sqrt r - (CA1 / Real.sqrt r) / Real.sqrt r -
            (CA2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ)))) / Real.sqrt r -
            (((r : ℝ) * Real.sqrt r) * ρ ^ r) / Real.sqrt r := by
        rw [← sub_div, ← sub_div, ← sub_div]
        exact div_le_div_of_nonneg_right (by linarith [hEstA]) hsr_pos.le
      linarith [hA, hA2, hA3, hA4, hsub]
    have hdiff_hi : |t ^ (m + 1) * (P ^ r).coeff (m + 1) / (P.eval t) ^ r -
        t ^ m * (P ^ r).coeff m / (P.eval t) ^ r| ≤
        (CB / Real.sqrt r + 2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) / (r : ℝ) := by
      rw [hbm1_eq]
      have hB := hB_inst t ht_mem
      have hB1 : CB / ((r : ℝ) * Real.sqrt r) = (CB / Real.sqrt r) / (r : ℝ) := by rw [div_div, mul_comm]
      have hB2 : 2 * ρ ^ r ≤ (2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) / (r : ℝ) := by
        rw [le_div_iff₀ hr_pos]
        have h1 : (1 : ℝ) ≤ Real.sqrt r := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hr_ge1
        have h2 : (r : ℝ) ≤ (r : ℝ) * Real.sqrt r := le_mul_of_one_le_right hr_pos.le h1
        have h3 := mul_le_mul_of_nonneg_right h2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (pow_nonneg hρ_nn r))
        linarith
      rw [add_div]
      linarith
    have hscale : t ^ m * ((P ^ r).coeff (m + 1) - (P ^ r).coeff m) / (P.eval t) ^ r =
        (t⁻¹ - 1) * (t ^ m * (P ^ r).coeff m / (P.eval t) ^ r) +
        t⁻¹ * (t ^ (m + 1) * (P ^ r).coeff (m + 1) / (P.eval t) ^ r -
          t ^ m * (P ^ r).coeff m / (P.eval t) ^ r) := by
      rw [pow_succ]; field_simp [ht_pos.ne', (pow_pos (evalP_pos hdeg hpos ht_pos) r).ne']; ring
    have hterm1 : (ct * (cA / 2)) / (r : ℝ) ≤ (t⁻¹ - 1) * (t ^ m * (P ^ r).coeff m / (P.eval t) ^ r) := by
      have hsq : Real.sqrt r * Real.sqrt r = (r : ℝ) := Real.mul_self_sqrt hr_pos.le
      calc (ct * (cA / 2)) / (r : ℝ)
          = (ct / Real.sqrt r) * ((cA / 2) / Real.sqrt r) := by rw [div_mul_div_comm, hsq]
        _ ≤ (t⁻¹ - 1) * (t ^ m * (P ^ r).coeff m / (P.eval t) ^ r) :=
              mul_le_mul h1_sub_t hbm_lo (by positivity) (le_trans (by positivity) h1_sub_t)
    have hterm2 : -(1 / t_min) * ((CB / Real.sqrt r + 2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) / (r : ℝ)) ≤
        t⁻¹ * (t ^ (m + 1) * (P ^ r).coeff (m + 1) / (P.eval t) ^ r -
          t ^ m * (P ^ r).coeff m / (P.eval t) ^ r) := by
      have htinv : t⁻¹ ≤ 1 / t_min := by rw [one_div]; exact inv_anti₀ ht_min_pos ht_mem.1
      have hlo := (abs_le.mp hdiff_hi).1
      have hnn : 0 ≤ (CB / Real.sqrt r + 2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) / (r : ℝ) := by positivity
      have h1 := mul_le_mul_of_nonneg_left hlo (inv_pos.mpr ht_pos).le
      have h2 := mul_le_mul_of_nonneg_right htinv hnn
      linarith
    have hpos_diff : 0 < t ^ m * ((P ^ r).coeff (m + 1) - (P ^ r).coeff m) / (P.eval t) ^ r := by
      rw [hscale]
      have hstrict : (1 / t_min) * ((CB / Real.sqrt r + 2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) / (r : ℝ)) <
          (ct * (cA / 2)) / (r : ℝ) := by
        rw [← mul_div_assoc]
        exact div_lt_div_of_pos_right hEstB hr_pos
      linarith
    have hfac : 0 < t ^ m / (P.eval t) ^ r := div_pos (pow_pos ht_pos m) (pow_pos (evalP_pos hdeg hpos ht_pos) r)
    have : 0 < (P ^ r).coeff (m + 1) - (P ^ r).coeff m := by
      rw [mul_div_right_comm] at hpos_diff
      exact pos_of_mul_pos_right hpos_diff hfac.le
    linarith

lemma region_right_mono {n : ℕ} {P : Polynomial ℝ} (hn : 2 ≤ n) (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i)
    {σ δ t_min t_max ρ cA CA1 CA2 cg CB ct : ℝ}
    (hσ_pos : 0 < σ) (hδ2 : δ ≤ P.coeff (n - 1) / (2 * (P.coeff n + P.coeff (n - 1))))
    (ht_min_pos : 0 < t_min) (ht_min_lt1 : t_min < 1) (ht_max_gt1 : 1 < t_max)
    (hmean_min : meanP n P t_min ≤ δ) (hmean_max : (n : ℝ) - δ ≤ meanP n P t_max)
    (hρ_nn : 0 ≤ ρ) (hcA_pos : 0 < cA) (hCA2_nn : 0 ≤ CA2) (hCB_nn : 0 ≤ CB)
    (hct_def : ct = (t_min * σ) / (2 * (n : ℝ) ^ 2 * t_max))
    (hmean_strict : StrictMonoOn (meanP n P) (Set.Icc t_min t_max))
    (hmean_lip : ∀ t ∈ Set.Icc t_min t_max, |meanP n P t - meanP n P 1| ≤ ((n : ℝ) ^ 2 / t_min) * |t - 1|)
    {r : ℕ} (hr2 : 2 ≤ r) (_hδr : (1 : ℝ) ≤ δ * (r : ℝ))
    (hwinL : (σ / 2) * Real.sqrt r < (meanP n P 1 - δ) * (r : ℝ))
    (hA_inst : ∀ t ∈ Set.Icc t_min t_max,
      cA / Real.sqrt r - CA1 / (r : ℝ) - CA2 * Real.exp (-cg * (r : ℝ)) - ρ ^ r ≤
        (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, charFun n P t θ ^ r).re)
    (hB_inst : ∀ t ∈ Set.Icc t_min t_max,
      |(1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re| ≤
        CB / ((r : ℝ) * Real.sqrt r) + 2 * ρ ^ r)
    (hEstA : CA1 / Real.sqrt r + CA2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ))) +
      (((r : ℝ) * Real.sqrt r) * ρ ^ r) < cA / 2)
    (hEstB : (1 / t_min) * (CB / Real.sqrt r + 2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) < ct * (cA / 2))
    (m : ℕ) (hm : meanP n P 1 * (r : ℝ) + (σ / 2) * Real.sqrt r ≤ (m : ℝ)) (hm_lt : m < n * r) :
    (P ^ r).coeff (m + 1) ≤ (P ^ r).coeff m := by
  have han1 : 0 < P.coeff (n - 1) := hpos (n - 1) (by omega)
  have han : 0 < P.coeff n := hpos n le_rfl
  have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
  have hsr_pos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr_pos
  have hr_ge1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
  have hσr : 0 < (σ / 2) * Real.sqrt r := by positivity
  have hct_pos : 0 < ct := by rw [hct_def]; positivity
  have h1_mem : (1 : ℝ) ∈ Set.Icc t_min t_max := ⟨ht_min_lt1.le, ht_max_gt1.le⟩
  by_cases htail : ((n : ℝ) - δ) * (r : ℝ) ≤ (m : ℝ)
  · refine right_tail_mono hn hdeg hpos (by omega) hm_lt ?_
    have hnr_m : ((n * r - m : ℕ) : ℝ) ≤ δ * (r : ℝ) := by
      rw [Nat.cast_sub (by omega : m ≤ n * r), Nat.cast_mul]; linarith
    have h1 : ((n * r - m : ℕ) : ℝ) ≤ P.coeff (n - 1) * (r : ℝ) / (P.coeff n + P.coeff (n - 1)) := by
      rw [mul_div_right_comm]
      have h2 : δ ≤ P.coeff (n - 1) / (P.coeff n + P.coeff (n - 1)) := by
        have := (le_div_iff₀ (by positivity : 0 < 2 * (P.coeff n + P.coeff (n - 1)))).mp hδ2
        exact (le_div_iff₀ (by positivity)).mpr (by linarith)
      nlinarith
    have hmul := (le_div_iff₀ (by positivity : 0 < P.coeff n + P.coeff (n - 1))).mp h1
    have hcast : ((n * r - 1 - m : ℕ) : ℝ) = ((n * r - m : ℕ) : ℝ) - 1 := by
      have : n * r - m = (n * r - 1 - m) + 1 := by omega
      have hc : ((n * r - m : ℕ) : ℝ) = ((n * r - 1 - m : ℕ) : ℝ) + 1 := by exact_mod_cast this
      linarith
    rw [hcast]
    nlinarith
  · push Not at htail
    have hm_in : (m : ℝ) / (r : ℝ) ∈ Set.Icc (meanP n P t_min) (meanP n P t_max) := by
      constructor
      · exact le_trans hmean_min ((le_div_iff₀ hr_pos).mpr (by linarith [hwinL, hσr]))
      · exact le_trans ((div_le_iff₀ hr_pos).mpr htail.le) hmean_max
    have hcont_m : ContinuousOn (meanP n P) (Set.Icc t_min t_max) := fun s hs =>
      (meanP_hasDerivAt hdeg hpos (lt_of_lt_of_le ht_min_pos hs.1)).continuousAt.continuousWithinAt
    obtain ⟨t, ht_mem, ht_eq⟩ := intermediate_value_Icc (by linarith : t_min ≤ t_max) hcont_m hm_in
    have ht_pos : 0 < t := lt_of_lt_of_le ht_min_pos ht_mem.1
    have hμt_gt : meanP n P 1 < meanP n P t := by
      rw [ht_eq, lt_div_iff₀ hr_pos]; linarith [hσr]
    have ht_gt1 : 1 < t := by
      by_contra hle; push Not at hle
      rcases eq_or_lt_of_le hle with rfl | hlt
      · linarith
      · exact absurd (hmean_strict ht_mem h1_mem hlt) (not_lt.mpr hμt_gt.le)
    have h1_sub_tinv : ct / Real.sqrt r ≤ 1 - t⁻¹ := by
      have hlip := hmean_lip t ht_mem
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hlip
      have hgap : (σ / 2) / Real.sqrt r ≤ meanP n P t - meanP n P 1 := by
        rw [ht_eq, div_le_iff₀ hsr_pos]
        have hsq : Real.sqrt r * Real.sqrt r = (r : ℝ) := Real.mul_self_sqrt hr_pos.le
        have hmul : (m : ℝ) / (r : ℝ) * (r : ℝ) = (m : ℝ) := div_mul_cancel₀ _ hr_pos.ne'
        have h1 : ((m : ℝ) / (r : ℝ) - meanP n P 1) * (r : ℝ) = (m : ℝ) - meanP n P 1 * (r : ℝ) := by
          rw [sub_mul, hmul]
        have h2 : (σ / 2) * Real.sqrt r ≤ ((m : ℝ) / (r : ℝ) - meanP n P 1) * (Real.sqrt r * Real.sqrt r) := by
          rw [hsq, h1]; linarith
        have h3 : (σ / 2) * Real.sqrt r ≤ (((m : ℝ) / (r : ℝ) - meanP n P 1) * Real.sqrt r) * Real.sqrt r := by
          simpa [mul_assoc] using h2
        exact le_of_mul_le_mul_right h3 hsr_pos
      have ht_gap : (t_min * σ) / (2 * (n : ℝ) ^ 2 * Real.sqrt r) ≤ t - 1 := by
        have : (σ / 2) / Real.sqrt r ≤ ((n : ℝ) ^ 2 / t_min) * (t - 1) := le_trans hgap hlip
        rw [div_le_iff₀ (by positivity)]
        have h1 : ((n : ℝ) ^ 2 / t_min) * (t - 1) * (t_min * Real.sqrt r) =
            (n : ℝ) ^ 2 * Real.sqrt r * (t - 1) := by field_simp [ht_min_pos.ne']
        have h2 : (σ / 2) / Real.sqrt r * (t_min * Real.sqrt r) = (t_min * σ) / 2 := by
          field_simp [hsr_pos.ne']
        have h3 := mul_le_mul_of_nonneg_right this (by positivity : 0 ≤ t_min * Real.sqrt r)
        rw [h1, h2] at h3
        linarith
      have hinv_ge : (t - 1) / t_max ≤ 1 - t⁻¹ := by
        have h1 : 1 - t⁻¹ = (t - 1) / t := by field_simp [ht_pos.ne']
        rw [h1]
        exact div_le_div_of_nonneg_left (by linarith) ht_pos ht_mem.2
      calc ct / Real.sqrt r
          = ((t_min * σ) / (2 * (n : ℝ) ^ 2 * Real.sqrt r)) / t_max := by rw [hct_def]; ring
        _ ≤ (t - 1) / t_max := div_le_div_of_nonneg_right ht_gap (by linarith)
        _ ≤ 1 - t⁻¹ := hinv_ge
    have hm_eq : meanP n P t * (r : ℝ) - (m : ℝ) = 0 := by
      rw [ht_eq, div_mul_cancel₀ _ hr_pos.ne', sub_self]
    have hbm_eq : t ^ m * (P ^ r).coeff m / (P.eval t) ^ r =
        (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, charFun n P t θ ^ r).re := by
      simpa [hm_eq] using tilted_coeff_fourier hdeg hpos ht_pos r m
    have hbm1_eq : t ^ (m + 1) * (P ^ r).coeff (m + 1) / (P.eval t) ^ r -
        t ^ m * (P ^ r).coeff m / (P.eval t) ^ r =
        (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re := by
      have h1 := tilted_coeff_fourier hdeg hpos ht_pos r (m + 1)
      rw [h1, hbm_eq, ← mul_sub, ← Complex.sub_re,
        ← intervalIntegral.integral_sub ((by unfold charFun; fun_prop : Continuous _).intervalIntegrable _ _)
          ((by unfold charFun; fun_prop : Continuous _).intervalIntegrable _ _)]
      congr 2
      refine intervalIntegral.integral_congr fun θ _ => ?_
      have hexp : meanP n P t * (r : ℝ) - ((m + 1 : ℕ) : ℝ) = -1 := by push_cast; linarith
      rw [hexp]
      have : I * ((-1 : ℝ) : ℂ) * (θ : ℂ) = -I * (θ : ℂ) := by push_cast; ring
      rw [this]; ring
    have hbm_lo : (cA / 2) / Real.sqrt r ≤ t ^ m * (P ^ r).coeff m / (P.eval t) ^ r := by
      rw [hbm_eq]
      have hA := hA_inst t ht_mem
      have hsq : Real.sqrt r * Real.sqrt r = (r : ℝ) := Real.mul_self_sqrt hr_pos.le
      have hA2 : CA1 / (r : ℝ) = (CA1 / Real.sqrt r) / Real.sqrt r := by rw [div_div, hsq]
      have hA3 : CA2 * Real.exp (-cg * (r : ℝ)) ≤
          (CA2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ)))) / Real.sqrt r := by
        rw [le_div_iff₀ hsr_pos]
        have hle : Real.sqrt r ≤ (r : ℝ) * Real.sqrt r := le_mul_of_one_le_left hsr_pos.le hr_ge1
        have hmul := mul_le_mul_of_nonneg_left hle (mul_nonneg hCA2_nn (Real.exp_pos (-cg * (r : ℝ))).le)
        linarith
      have hA4 : ρ ^ r ≤ (((r : ℝ) * Real.sqrt r) * ρ ^ r) / Real.sqrt r := by
        rw [le_div_iff₀ hsr_pos]
        have hle : Real.sqrt r ≤ (r : ℝ) * Real.sqrt r := le_mul_of_one_le_left hsr_pos.le hr_ge1
        have hmul := mul_le_mul_of_nonneg_right hle (pow_nonneg hρ_nn r)
        linarith
      have hsub : (cA / 2) / Real.sqrt r ≤
          cA / Real.sqrt r - (CA1 / Real.sqrt r) / Real.sqrt r -
            (CA2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ)))) / Real.sqrt r -
            (((r : ℝ) * Real.sqrt r) * ρ ^ r) / Real.sqrt r := by
        rw [← sub_div, ← sub_div, ← sub_div]
        exact div_le_div_of_nonneg_right (by linarith [hEstA]) hsr_pos.le
      linarith [hA, hA2, hA3, hA4, hsub]
    have hdiff_hi : |t ^ (m + 1) * (P ^ r).coeff (m + 1) / (P.eval t) ^ r -
        t ^ m * (P ^ r).coeff m / (P.eval t) ^ r| ≤
        (CB / Real.sqrt r + 2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) / (r : ℝ) := by
      rw [hbm1_eq]
      have hB := hB_inst t ht_mem
      have hB1 : CB / ((r : ℝ) * Real.sqrt r) = (CB / Real.sqrt r) / (r : ℝ) := by rw [div_div, mul_comm]
      have hB2 : 2 * ρ ^ r ≤ (2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) / (r : ℝ) := by
        rw [le_div_iff₀ hr_pos]
        have h1 : (1 : ℝ) ≤ Real.sqrt r := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hr_ge1
        have h2 : (r : ℝ) ≤ (r : ℝ) * Real.sqrt r := le_mul_of_one_le_right hr_pos.le h1
        have h3 := mul_le_mul_of_nonneg_right h2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (pow_nonneg hρ_nn r))
        linarith
      rw [add_div]
      linarith
    have hscale : t ^ m * ((P ^ r).coeff (m + 1) - (P ^ r).coeff m) / (P.eval t) ^ r =
        -(1 - t⁻¹) * (t ^ m * (P ^ r).coeff m / (P.eval t) ^ r) +
        t⁻¹ * (t ^ (m + 1) * (P ^ r).coeff (m + 1) / (P.eval t) ^ r -
          t ^ m * (P ^ r).coeff m / (P.eval t) ^ r) := by
      rw [pow_succ]; field_simp [ht_pos.ne', (pow_pos (evalP_pos hdeg hpos ht_pos) r).ne']; ring
    have hterm1 : (ct * (cA / 2)) / (r : ℝ) ≤ (1 - t⁻¹) * (t ^ m * (P ^ r).coeff m / (P.eval t) ^ r) := by
      have hsq : Real.sqrt r * Real.sqrt r = (r : ℝ) := Real.mul_self_sqrt hr_pos.le
      calc (ct * (cA / 2)) / (r : ℝ)
          = (ct / Real.sqrt r) * ((cA / 2) / Real.sqrt r) := by rw [div_mul_div_comm, hsq]
        _ ≤ (1 - t⁻¹) * (t ^ m * (P ^ r).coeff m / (P.eval t) ^ r) :=
              mul_le_mul h1_sub_tinv hbm_lo (by positivity) (le_trans (by positivity) h1_sub_tinv)
    have hterm2 : t⁻¹ * (t ^ (m + 1) * (P ^ r).coeff (m + 1) / (P.eval t) ^ r -
          t ^ m * (P ^ r).coeff m / (P.eval t) ^ r) ≤
        (1 / t_min) * ((CB / Real.sqrt r + 2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) / (r : ℝ)) := by
      have htinv : t⁻¹ ≤ 1 / t_min := by rw [one_div]; exact inv_anti₀ ht_min_pos ht_mem.1
      have hhi := (abs_le.mp hdiff_hi).2
      have hnn : 0 ≤ (CB / Real.sqrt r + 2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) / (r : ℝ) := by positivity
      have h1 := mul_le_mul_of_nonneg_left hhi (inv_pos.mpr ht_pos).le
      have h2 := mul_le_mul_of_nonneg_right htinv hnn
      linarith
    have hneg_diff : t ^ m * ((P ^ r).coeff (m + 1) - (P ^ r).coeff m) / (P.eval t) ^ r < 0 := by
      rw [hscale]
      have hstrict : (1 / t_min) * ((CB / Real.sqrt r + 2 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) / (r : ℝ)) <
          (ct * (cA / 2)) / (r : ℝ) := by
        rw [← mul_div_assoc]
        exact div_lt_div_of_pos_right hEstB hr_pos
      linarith
    have hfac : 0 < t ^ m / (P.eval t) ^ r := div_pos (pow_pos ht_pos m) (pow_pos (evalP_pos hdeg hpos ht_pos) r)
    have : (P ^ r).coeff (m + 1) - (P ^ r).coeff m < 0 := by
      rw [mul_div_right_comm] at hneg_diff
      exact neg_of_mul_neg_right hneg_diff hfac.le
    linarith

lemma region_center_concave {n : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i)
    {ρ cC CC1 CC2 cg : ℝ} (hv1_pos : 0 < varP n P 1)
    {r : ℕ} (hr2 : 2 ≤ r)
    (hC_inst : ∀ w : ℝ, |w| ≤ Real.sqrt (varP n P 1 * (r : ℝ)) / 2 →
      (1 / (2 * Real.pi)) *
        (∫ θ in (-Real.pi)..Real.pi,
          ((2 * Real.cos θ - 2 : ℝ) : ℂ) * charFun n P 1 θ ^ r * Complex.exp (I * (w : ℂ) * θ)).re ≤
      -cC / ((r : ℝ) * Real.sqrt r) + CC1 / (r : ℝ) ^ 2 + CC2 * Real.exp (-cg * (r : ℝ)) + 4 * ρ ^ r)
    (hEstC : CC1 / Real.sqrt r + CC2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ))) +
      4 * (((r : ℝ) * Real.sqrt r) * ρ ^ r) < cC)
    (m : ℕ) (hm1 : 1 ≤ m)
    (hm_lo : meanP n P 1 * (r : ℝ) - (Real.sqrt (varP n P 1) / 2) * Real.sqrt r ≤ (m : ℝ))
    (hm_hi : (m : ℝ) ≤ meanP n P 1 * (r : ℝ) + (Real.sqrt (varP n P 1) / 2) * Real.sqrt r) :
    (P ^ r).coeff (m + 1) - (P ^ r).coeff m < (P ^ r).coeff m - (P ^ r).coeff (m - 1) := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
  have hsr_pos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr_pos
  set w := meanP n P 1 * (r : ℝ) - (m : ℝ)
  have hw_abs : |w| ≤ Real.sqrt (varP n P 1 * (r : ℝ)) / 2 := by
    rw [Real.sqrt_mul hv1_pos.le, abs_le]
    dsimp only [w]
    constructor <;> linarith
  have hsec_eq : ((P ^ r).coeff (m + 1) - 2 * (P ^ r).coeff m + (P ^ r).coeff (m - 1)) / (P.eval 1) ^ r =
      (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi,
        ((2 * Real.cos θ - 2 : ℝ) : ℂ) * charFun n P 1 θ ^ r * Complex.exp (I * (w : ℂ) * θ)).re := by
    have h_m1 := tilted_coeff_fourier hdeg hpos zero_lt_one r (m + 1)
    have h_m0 := tilted_coeff_fourier hdeg hpos zero_lt_one r m
    have h_mm := tilted_coeff_fourier hdeg hpos zero_lt_one r (m - 1)
    simp only [one_pow, one_mul] at h_m1 h_m0 h_mm
    have hcomb : ((P ^ r).coeff (m + 1) - 2 * (P ^ r).coeff m + (P ^ r).coeff (m - 1)) / (P.eval 1) ^ r =
        (P ^ r).coeff (m + 1) / (P.eval 1) ^ r - 2 * ((P ^ r).coeff m / (P.eval 1) ^ r) +
          (P ^ r).coeff (m - 1) / (P.eval 1) ^ r := by ring
    rw [hcomb, h_m1, h_m0, h_mm]
    let f1 : ℝ → ℂ := fun θ => charFun n P 1 θ ^ r * Complex.exp (I * ((meanP n P 1 * (r : ℝ) - ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * θ)
    let f0 : ℝ → ℂ := fun θ => charFun n P 1 θ ^ r * Complex.exp (I * ((meanP n P 1 * (r : ℝ) - (m : ℝ) : ℝ) : ℂ) * θ)
    let fm : ℝ → ℂ := fun θ => charFun n P 1 θ ^ r * Complex.exp (I * ((meanP n P 1 * (r : ℝ) - ((m - 1 : ℕ) : ℝ) : ℝ) : ℂ) * θ)
    have hI1 : Continuous f1 := by dsimp [f1]; unfold charFun; fun_prop
    have hI0 : Continuous f0 := by dsimp [f0]; unfold charFun; fun_prop
    have hIm : Continuous fm := by dsimp [fm]; unfold charFun; fun_prop
    have hI02 : Continuous (fun θ : ℝ => (2 : ℂ) * f0 θ) := continuous_const.mul hI0
    have hsum_re :
        (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, f1 θ).re -
        2 * ((1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, f0 θ).re) +
        (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, fm θ).re =
        (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, (f1 θ - (2 : ℂ) * f0 θ + fm θ)).re := by
      have hadd := intervalIntegral.integral_add ((hI1.sub hI02).intervalIntegrable (μ := volume) (-Real.pi) Real.pi)
        (hIm.intervalIntegrable (μ := volume) (-Real.pi) Real.pi)
      have hsub := intervalIntegral.integral_sub (hI1.intervalIntegrable (μ := volume) (-Real.pi) Real.pi)
        (hI02.intervalIntegrable (μ := volume) (-Real.pi) Real.pi)
      have hmul := intervalIntegral.integral_const_mul (μ := volume) (2 : ℂ) (f := f0) (a := -Real.pi) (b := Real.pi)
      change (∫ θ in (-Real.pi)..Real.pi, f1 θ - (2 : ℂ) * f0 θ + fm θ) =
          (∫ θ in (-Real.pi)..Real.pi, f1 θ - (2 : ℂ) * f0 θ) + ∫ θ in (-Real.pi)..Real.pi, fm θ at hadd
      change (∫ θ in (-Real.pi)..Real.pi, f1 θ - (2 : ℂ) * f0 θ) =
          (∫ θ in (-Real.pi)..Real.pi, f1 θ) - ∫ θ in (-Real.pi)..Real.pi, (2 : ℂ) * f0 θ at hsub
      rw [hadd, hsub, hmul]
      have h2re : ((2 : ℂ) * ∫ θ in (-Real.pi)..Real.pi, f0 θ).re =
          2 * (∫ θ in (-Real.pi)..Real.pi, f0 θ).re := by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
      simp only [Complex.add_re, Complex.sub_re, h2re]
      ring
    change (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, f1 θ).re -
        2 * ((1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, f0 θ).re) +
        (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, fm θ).re = _
    rw [hsum_re]
    congr 2
    refine intervalIntegral.integral_congr fun θ _ => ?_
    dsimp only [f1, f0, fm]
    have hm_sub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have : m = (m - 1) + 1 := by omega
      have hc : (m : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast this
      linarith
    have he1 : Complex.exp (I * ((meanP n P 1 * (r : ℝ) - ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * θ) =
        Complex.exp (-I * (θ : ℂ)) * Complex.exp (I * (w : ℂ) * θ) := by
      rw [← Complex.exp_add]; congr 1; dsimp [w]; push_cast; ring
    have hem : Complex.exp (I * ((meanP n P 1 * (r : ℝ) - ((m - 1 : ℕ) : ℝ) : ℝ) : ℂ) * θ) =
        Complex.exp (I * (θ : ℂ)) * Complex.exp (I * (w : ℂ) * θ) := by
      rw [← Complex.exp_add]; congr 1; dsimp [w]; rw [hm_sub]; push_cast; ring
    have hcos2 : Complex.exp (-I * (θ : ℂ)) + Complex.exp (I * (θ : ℂ)) = ((2 * Real.cos θ : ℝ) : ℂ) := by
      rw [show -I * (θ : ℂ) = (-(θ : ℂ)) * I by ring, show I * (θ : ℂ) = (θ : ℂ) * I by ring,
        Complex.exp_mul_I, Complex.exp_mul_I]
      simp [Complex.cos_neg, Complex.sin_neg]
      ring
    rw [he1, hem]
    calc charFun n P 1 θ ^ r * (Complex.exp (-I * (θ : ℂ)) * Complex.exp (I * (w : ℂ) * θ)) -
          2 * (charFun n P 1 θ ^ r * Complex.exp (I * (w : ℂ) * θ)) +
          charFun n P 1 θ ^ r * (Complex.exp (I * (θ : ℂ)) * Complex.exp (I * (w : ℂ) * θ))
        = (Complex.exp (-I * (θ : ℂ)) + Complex.exp (I * (θ : ℂ)) - 2) *
            charFun n P 1 θ ^ r * Complex.exp (I * (w : ℂ) * θ) := by ring
      _ = ((2 * Real.cos θ - 2 : ℝ) : ℂ) * charFun n P 1 θ ^ r * Complex.exp (I * (w : ℂ) * θ) := by
            rw [hcos2]; push_cast; ring
  have hC := hC_inst w hw_abs
  rw [← hsec_eq] at hC
  have hsq : Real.sqrt r * Real.sqrt r = (r : ℝ) := Real.mul_self_sqrt hr_pos.le
  have hC1 : CC1 / (r : ℝ) ^ 2 = (CC1 / Real.sqrt r) / ((r : ℝ) * Real.sqrt r) := by
    rw [div_div]
    congr 1
    calc (r : ℝ) ^ 2 = (r : ℝ) * (r : ℝ) := sq (r : ℝ)
      _ = (r : ℝ) * (Real.sqrt r * Real.sqrt r) := by rw [hsq]
      _ = Real.sqrt r * ((r : ℝ) * Real.sqrt r) := by ring
  have hC2 : CC2 * Real.exp (-cg * (r : ℝ)) =
      (CC2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ)))) / ((r : ℝ) * Real.sqrt r) := by
    field_simp [hr_pos.ne', hsr_pos.ne']
  have hC3 : 4 * ρ ^ r = (4 * (((r : ℝ) * Real.sqrt r) * ρ ^ r)) / ((r : ℝ) * Real.sqrt r) := by
    field_simp [hr_pos.ne', hsr_pos.ne']
  have hneg : ((P ^ r).coeff (m + 1) - 2 * (P ^ r).coeff m + (P ^ r).coeff (m - 1)) / (P.eval 1) ^ r < 0 := by
    have hC0 : -cC / ((r : ℝ) * Real.sqrt r) = (-cC) / ((r : ℝ) * Real.sqrt r) := by ring
    rw [hC0, hC1, hC2, hC3, ← add_div, ← add_div, ← add_div] at hC
    have hnum : -cC + CC1 / Real.sqrt r + CC2 * (((r : ℝ) * Real.sqrt r) * Real.exp (-cg * (r : ℝ))) +
        4 * (((r : ℝ) * Real.sqrt r) * ρ ^ r) < 0 := by linarith [hEstC]
    exact lt_of_le_of_lt hC (div_neg_of_neg_of_pos hnum (by positivity))
  have hEv1 : 0 < (P.eval 1) ^ r := pow_pos (evalP_pos hdeg hpos zero_lt_one) r
  have hnum_neg : (P ^ r).coeff (m + 1) - 2 * (P ^ r).coeff m + (P ^ r).coeff (m - 1) < 0 := by
    by_contra hge; push Not at hge
    exact absurd hneg (not_lt.mpr (div_nonneg hge hEv1.le))
  linarith

lemma eventual_unimodal_ge2 {n : ℕ} {P : Polynomial ℝ} (hn : 2 ≤ n) (hdeg : P.natDegree = n)
    (hpos : ∀ i ≤ n, 0 < P.coeff i) :
    ∃ r : ℕ, 0 < r ∧
      ∃ j ≤ n * r,
        (∀ i, i < j → (P ^ r).coeff i ≤ (P ^ r).coeff (i + 1)) ∧
        (∀ i, j + 1 ≤ i → i < n * r → (P ^ r).coeff (i + 1) ≤ (P ^ r).coeff i) := by
  have ha0 : 0 < P.coeff 0 := hpos 0 (by omega)
  have ha1 : 0 < P.coeff 1 := hpos 1 (by omega)
  have han1 : 0 < P.coeff (n - 1) := hpos (n - 1) (by omega)
  have han : 0 < P.coeff n := hpos n le_rfl
  have hμ_b := meanP_bounds hn hdeg hpos zero_lt_one
  have hv1_pos : 0 < varP n P 1 := lt_of_lt_of_le
    (div_pos (lt_min (prob_pos hdeg hpos zero_lt_one (by omega)) (prob_pos hdeg hpos zero_lt_one (by omega))) (by norm_num))
    (varP_bounds hn hdeg hpos zero_lt_one).1
  set σ : ℝ := Real.sqrt (varP n P 1)
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hv1_pos
  set δ : ℝ := min (min (P.coeff 1 / (2 * (P.coeff 0 + P.coeff 1)))
      (P.coeff (n - 1) / (2 * (P.coeff n + P.coeff (n - 1)))))
      (min (meanP n P 1 / 2) (((n : ℝ) - meanP n P 1) / 2))
  have hδ_pos : 0 < δ :=
    lt_min (lt_min (by positivity) (by positivity))
      (lt_min (by linarith [hμ_b.1]) (by linarith [hμ_b.2]))
  have hδ1 : δ ≤ P.coeff 1 / (2 * (P.coeff 0 + P.coeff 1)) := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ2 : δ ≤ P.coeff (n - 1) / (2 * (P.coeff n + P.coeff (n - 1))) := le_trans (min_le_left _ _) (min_le_right _ _)
  have hμδ : 0 < meanP n P 1 - δ := by
    have : δ ≤ meanP n P 1 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith [hμ_b.1]
  have hnδ : 0 < (n : ℝ) - δ - meanP n P 1 := by
    have : δ ≤ ((n : ℝ) - meanP n P 1) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith [hμ_b.2]
  obtain ⟨t_min, t_max, ht_min_pos, ht_min_lt1, ht_max_gt1, hmean_min, hmean_max⟩ :=
    exists_tilt_interval hn hdeg hpos hδ_pos
  have hEv_mono : ∀ t ∈ Set.Icc t_min t_max, P.eval t ≤ P.eval t_max := by
    intro t ht
    rw [evalP_eq_sum hdeg t, evalP_eq_sum hdeg t_max]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_trans ht_min_pos.le ht.1) ht.2 k) (hpos k hk_le).le
  have hEv_max_pos : 0 < P.eval t_max := evalP_pos hdeg hpos (by linarith)
  obtain ⟨p0_min, hp0_def⟩ : ∃ x : ℝ, x = P.coeff 0 / P.eval t_max := ⟨_, rfl⟩
  obtain ⟨p1_min, hp1_def⟩ : ∃ x : ℝ, x = P.coeff 1 * t_min / P.eval t_max := ⟨_, rfl⟩
  have hp0_min_pos : 0 < p0_min := by rw [hp0_def]; positivity
  have hp1_min_pos : 0 < p1_min := by rw [hp1_def]; positivity
  have hp0_ge : ∀ t ∈ Set.Icc t_min t_max, p0_min ≤ prob P t 0 := by
    intro t ht
    unfold prob; rw [hp0_def, pow_zero, mul_one]
    exact div_le_div_of_nonneg_left ha0.le (evalP_pos hdeg hpos (lt_of_lt_of_le ht_min_pos ht.1)) (hEv_mono t ht)
  have hp1_ge : ∀ t ∈ Set.Icc t_min t_max, p1_min ≤ prob P t 1 := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le ht_min_pos ht.1
    unfold prob; rw [hp1_def, pow_one]
    have hnum : P.coeff 1 * t_min ≤ P.coeff 1 * t := mul_le_mul_of_nonneg_left ht.1 ha1.le
    exact div_le_div₀ (mul_nonneg ha1.le ht_pos.le) hnum (evalP_pos hdeg hpos ht_pos) (hEv_mono t ht)
  obtain ⟨σ₂, hσ₂_def⟩ : ∃ x : ℝ, x = min p0_min p1_min / 2 := ⟨_, rfl⟩
  have hσ₂_pos : 0 < σ₂ := by rw [hσ₂_def]; exact div_pos (lt_min hp0_min_pos hp1_min_pos) (by norm_num)
  have hσ₂_le : ∀ t ∈ Set.Icc t_min t_max, σ₂ ≤ varP n P t := by
    intro t ht
    have h1 := (varP_bounds hn hdeg hpos (lt_of_lt_of_le ht_min_pos ht.1)).1
    have h2 : min p0_min p1_min ≤ min (prob P t 0) (prob P t 1) :=
      le_min (le_trans (min_le_left _ _) (hp0_ge t ht)) (le_trans (min_le_right _ _) (hp1_ge t ht))
    rw [hσ₂_def]; linarith
  have h1_mem : (1 : ℝ) ∈ Set.Icc t_min t_max := ⟨ht_min_lt1.le, ht_max_gt1.le⟩
  obtain ⟨θ₀, hθ₀_def⟩ : ∃ x : ℝ, x = min (1 / 2) (σ₂ / (8 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4))) := ⟨_, rfl⟩
  have hθ₀_pos : 0 < θ₀ := by rw [hθ₀_def]; exact lt_min (by norm_num) (div_pos hσ₂_pos (by positivity))
  have hθ₀_le1 : θ₀ ≤ 1 := by rw [hθ₀_def]; exact le_trans (min_le_left _ _) (by norm_num)
  have hθ₀_lepi : θ₀ ≤ Real.pi := le_trans hθ₀_le1 (by linarith [Real.pi_gt_three])
  have hθ₀_small : θ₀ ≤ σ₂ / (8 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4)) := by rw [hθ₀_def]; exact min_le_right _ _
  obtain ⟨ρ, hρ_def⟩ : ∃ x : ℝ, x = 1 - p0_min * p1_min * (1 - Real.cos θ₀) := ⟨_, rfl⟩
  have hcos_lt1 : Real.cos θ₀ < 1 := by
    rw [← Real.cos_zero]
    exact Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ ⟨hθ₀_pos.le, hθ₀_lepi⟩ hθ₀_pos
  have hρ_lt1 : ρ < 1 := by rw [hρ_def]; nlinarith [mul_pos hp0_min_pos hp1_min_pos]
  have houter : ∀ t ∈ Set.Icc t_min t_max, ∀ θ : ℝ, θ₀ ≤ |θ| → |θ| ≤ Real.pi → ‖charFun n P t θ‖ ≤ ρ := by
    intro t ht θ hlo hhi
    have h1 := charFun_outer_bound hn hdeg hpos (lt_of_lt_of_le ht_min_pos ht.1) hθ₀_pos hθ₀_lepi hlo hhi
    have hprod : p0_min * p1_min ≤ prob P t 0 * prob P t 1 :=
      mul_le_mul (hp0_ge t ht) (hp1_ge t ht) hp1_min_pos.le (prob_pos hdeg hpos (lt_of_lt_of_le ht_min_pos ht.1) (by omega)).le
    have hdiff : 0 ≤ 1 - Real.cos θ₀ := by linarith
    rw [hρ_def]; nlinarith
  have hρ_nn : 0 ≤ ρ := by
    have := houter 1 h1_mem Real.pi (by rw [abs_of_pos Real.pi_pos]; exact hθ₀_lepi) (by rw [abs_of_pos Real.pi_pos])
    exact le_trans (norm_nonneg _) this
  have hmean_strict : StrictMonoOn (meanP n P) (Set.Icc t_min t_max) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc t_min t_max) ?_ ?_
    · intro t ht
      exact (meanP_hasDerivAt hdeg hpos (lt_of_lt_of_le ht_min_pos ht.1)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht_pos : 0 < t := lt_trans ht_min_pos ht.1
      rw [(meanP_hasDerivAt hdeg hpos ht_pos).deriv]
      exact div_pos (lt_of_lt_of_le hσ₂_pos (hσ₂_le t ⟨ht.1.le, ht.2.le⟩)) ht_pos
  have hmean_lip : ∀ t ∈ Set.Icc t_min t_max, |meanP n P t - meanP n P 1| ≤ ((n : ℝ) ^ 2 / t_min) * |t - 1| := by
    intro t ht
    by_cases ht1 : t = 1
    · subst ht1; simp
    · rcases lt_or_gt_of_ne ht1 with hlt | hgt
      · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (meanP n P) (fun s => varP n P s / s) hlt
          (fun s hs => (meanP_hasDerivAt hdeg hpos (lt_of_lt_of_le ht_min_pos (le_trans ht.1 hs.1))).continuousAt.continuousWithinAt)
          (fun s hs => meanP_hasDerivAt hdeg hpos (lt_of_lt_of_le ht_min_pos (le_trans ht.1 hs.1.le)))
        have hξ_pos : t_min ≤ ξ := le_trans ht.1 hξ.1.le
        have hvar_le : varP n P ξ ≤ (n : ℝ) ^ 2 := (varP_bounds hn hdeg hpos (lt_of_lt_of_le ht_min_pos hξ_pos)).2
        have hder_le : varP n P ξ / ξ ≤ (n : ℝ) ^ 2 / t_min :=
          div_le_div₀ (by positivity) hvar_le ht_min_pos hξ_pos
        have hder_nn : 0 ≤ varP n P ξ / ξ :=
          div_nonneg (le_trans hσ₂_pos.le (hσ₂_le ξ ⟨hξ_pos, le_trans hξ.2.le ht_max_gt1.le⟩)) (lt_of_lt_of_le ht_min_pos hξ_pos).le
        have heq : meanP n P 1 - meanP n P t = (varP n P ξ / ξ) * (1 - t) := by
          have hne : 1 - t ≠ 0 := by linarith
          field_simp [hne] at hslope
          rw [mul_div_right_comm] at hslope
          linarith
        have hnonneg_diff : 0 ≤ meanP n P 1 - meanP n P t := by
          rw [heq]; exact mul_nonneg hder_nn (by linarith)
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), neg_sub, neg_sub, heq]
        exact mul_le_mul_of_nonneg_right hder_le (by linarith)
      · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (meanP n P) (fun s => varP n P s / s) hgt
          (fun s hs => (meanP_hasDerivAt hdeg hpos (lt_trans ht_min_pos (lt_of_lt_of_le ht_min_lt1 hs.1))).continuousAt.continuousWithinAt)
          (fun s hs => meanP_hasDerivAt hdeg hpos (lt_trans ht_min_pos (lt_of_lt_of_le ht_min_lt1 hs.1.le)))
        have hξ_pos : t_min ≤ ξ := le_trans ht_min_lt1.le hξ.1.le
        have hvar_le : varP n P ξ ≤ (n : ℝ) ^ 2 := (varP_bounds hn hdeg hpos (lt_of_lt_of_le ht_min_pos hξ_pos)).2
        have hder_le : varP n P ξ / ξ ≤ (n : ℝ) ^ 2 / t_min :=
          div_le_div₀ (by positivity) hvar_le ht_min_pos hξ_pos
        have hder_nn : 0 ≤ varP n P ξ / ξ :=
          div_nonneg (le_trans hσ₂_pos.le (hσ₂_le ξ ⟨hξ_pos, le_trans hξ.2.le ht.2⟩)) (lt_of_lt_of_le ht_min_pos hξ_pos).le
        have heq : meanP n P t - meanP n P 1 = (varP n P ξ / ξ) * (t - 1) := by
          have hne : t - 1 ≠ 0 := by linarith
          field_simp [hne] at hslope
          rw [mul_div_right_comm] at hslope
          linarith
        have hnonneg_diff : 0 ≤ meanP n P t - meanP n P 1 := by
          rw [heq]; exact mul_nonneg hder_nn (by linarith)
        rw [abs_of_nonneg hnonneg_diff, abs_of_nonneg (by linarith), heq]
        exact mul_le_mul_of_nonneg_right hder_le (by linarith)
  obtain ⟨cA, hcA_def⟩ : ∃ x : ℝ, x = 1 / (Real.sqrt (2 * Real.pi) * (n : ℝ)) := ⟨_, rfl⟩
  obtain ⟨CA1, hCA1_def⟩ : ∃ x : ℝ, x = 31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 2 * Real.sqrt Real.pi / (2 * Real.pi) := ⟨_, rfl⟩
  obtain ⟨CA2, hCA2_def⟩ : ∃ x : ℝ, x = Real.sqrt (Real.pi / (σ₂ / 4)) / (2 * Real.pi) := ⟨_, rfl⟩
  obtain ⟨cg, hcg_def⟩ : ∃ x : ℝ, x = σ₂ * θ₀ ^ 2 / 4 := ⟨_, rfl⟩
  obtain ⟨CB, hCB_def⟩ : ∃ x : ℝ, x = (31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 2 * Real.sqrt (16 * Real.pi / σ₂) +
      (1 / 2) * (31 * (8 / σ₂) * Real.sqrt (8 * Real.pi / σ₂))) / (2 * Real.pi) := ⟨_, rfl⟩
  obtain ⟨cC, hcC_def⟩ : ∃ x : ℝ, x = (3 / 4) * Real.exp (-1 / 8) / (Real.sqrt (2 * Real.pi) * (varP n P 1 * Real.sqrt (varP n P 1))) := ⟨_, rfl⟩
  obtain ⟨CC1, hCC1_def⟩ : ∃ x : ℝ, x = ((31 * ((n : ℝ) ^ 3 + (n : ℝ) ^ 4) * (16 / σ₂) ^ 3 * Real.sqrt Real.pi) +
      (1 / 12) * (31 * (4 / σ₂) ^ 2 * Real.sqrt (4 * Real.pi / σ₂))) / (2 * Real.pi) := ⟨_, rfl⟩
  obtain ⟨CC2, hCC2_def⟩ : ∃ x : ℝ, x = 31 * (8 / σ₂) * Real.sqrt (Real.pi / (σ₂ / 8)) / (2 * Real.pi) := ⟨_, rfl⟩
  obtain ⟨ct, hct_def⟩ : ∃ x : ℝ, x = (t_min * σ) / (2 * (n : ℝ) ^ 2 * t_max) := ⟨_, rfl⟩
  have hcA_pos : 0 < cA := by rw [hcA_def]; positivity
  have hCA2_nn : 0 ≤ CA2 := by rw [hCA2_def]; positivity
  have hCB_nn : 0 ≤ CB := by rw [hCB_def]; positivity
  have hcg_pos : 0 < cg := by rw [hcg_def]; positivity
  have hcC_pos : 0 < cC := by rw [hcC_def]; positivity
  have hct_pos : 0 < ct := by rw [hct_def]; positivity
  obtain ⟨r, hr2, hδr, hwinL, hwinR, hEstA, hEstB, hEstC⟩ :=
    exists_large_r (n := n) (μ := meanP n P 1) (σ := σ) (δ := δ) (t_min := t_min) (ρ := ρ)
      (cA := cA) (CA1 := CA1) (CA2 := CA2) (cg := cg) (CB := CB) (cC := cC)
      (CC1 := CC1) (CC2 := CC2) (ct := ct)
      hδ_pos hμδ hnδ hρ_nn hρ_lt1 hcA_pos hcg_pos hcC_pos hct_pos
  have hA_inst : ∀ t ∈ Set.Icc t_min t_max,
      cA / Real.sqrt r - CA1 / (r : ℝ) - CA2 * Real.exp (-cg * (r : ℝ)) - ρ ^ r ≤
        (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, charFun n P t θ ^ r).re := by
    intro t ht
    have h := tilted_central_lower hn hdeg hpos (lt_of_lt_of_le ht_min_pos ht.1) hσ₂_pos (hσ₂_le t ht)
      hθ₀_pos hθ₀_le1 hθ₀_lepi hθ₀_small hρ_nn (houter t ht) hr2
    rw [hcA_def, hCA1_def, hCA2_def, hcg_def,
      show 1 / (Real.sqrt (2 * Real.pi) * (n : ℝ)) / Real.sqrt r =
        1 / (Real.sqrt (2 * Real.pi) * (n : ℝ) * Real.sqrt r) by ring]
    exact h
  have hB_inst : ∀ t ∈ Set.Icc t_min t_max,
      |(1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, (Complex.exp (-I * θ) - 1) * charFun n P t θ ^ r).re| ≤
        CB / ((r : ℝ) * Real.sqrt r) + 2 * ρ ^ r := by
    intro t ht
    have h := tilted_diff_upper hn hdeg hpos (lt_of_lt_of_le ht_min_pos ht.1) hσ₂_pos (hσ₂_le t ht)
      hθ₀_pos hθ₀_le1 hθ₀_lepi hθ₀_small hρ_nn (houter t ht) hr2
    rw [hCB_def]
    exact h
  have hC_inst : ∀ w : ℝ, |w| ≤ Real.sqrt (varP n P 1 * (r : ℝ)) / 2 →
      (1 / (2 * Real.pi)) *
        (∫ θ in (-Real.pi)..Real.pi,
          ((2 * Real.cos θ - 2 : ℝ) : ℂ) * charFun n P 1 θ ^ r * Complex.exp (I * (w : ℂ) * θ)).re ≤
      -cC / ((r : ℝ) * Real.sqrt r) + CC1 / (r : ℝ) ^ 2 + CC2 * Real.exp (-cg * (r : ℝ)) + 4 * ρ ^ r := by
    intro w hw
    have h := central_second_diff_upper hn hdeg hpos hσ₂_pos (hσ₂_le 1 h1_mem)
      hθ₀_pos hθ₀_le1 hθ₀_lepi hθ₀_small hρ_nn (houter 1 h1_mem) hr2 hw
    rw [hcC_def, hCC1_def, hCC2_def, hcg_def]
    exact h
  have hLeft := region_left_mono hn hdeg hpos hσ_pos hδ1 ht_min_pos ht_min_lt1 ht_max_gt1
    hmean_min hmean_max hρ_nn hcA_pos hCA2_nn hCB_nn hct_def hmean_strict hmean_lip
    hr2 hδr hwinR hA_inst hB_inst hEstA hEstB
  have hRight := region_right_mono hn hdeg hpos hσ_pos hδ2 ht_min_pos ht_min_lt1 ht_max_gt1
    hmean_min hmean_max hρ_nn hcA_pos hCA2_nn hCB_nn hct_def hmean_strict hmean_lip
    hr2 hδr hwinL hA_inst hB_inst hEstA hEstB
  have hCenter := region_center_concave hdeg hpos hv1_pos hr2 hC_inst hEstC
  refine ⟨r, by omega, ?_⟩
  classical
  by_cases hdrop : ∃ k < n * r, (P ^ r).coeff (k + 1) < (P ^ r).coeff k
  · let j := Nat.find hdrop
    have hj_spec : j < n * r ∧ (P ^ r).coeff (j + 1) < (P ^ r).coeff j := Nat.find_spec hdrop
    have hj_min : ∀ i < j, (P ^ r).coeff i ≤ (P ^ r).coeff (i + 1) := by
      intro i hi
      have hnot := Nat.find_min hdrop hi
      push Not at hnot
      exact hnot (lt_trans hi hj_spec.1)
    have hj_gt : meanP n P 1 * (r : ℝ) - (σ / 2) * Real.sqrt r < (j : ℝ) := by
      by_contra hle; push Not at hle
      exact absurd hj_spec.2 (not_lt.mpr (hLeft j hle))
    have hdesc : ∀ d : ℕ, j + d < n * r → (P ^ r).coeff (j + d + 1) ≤ (P ^ r).coeff (j + d) := by
      intro d
      induction d with
      | zero => intro _; simpa using hj_spec.2.le
      | succ d ih =>
        intro hlt
        have hprev : (P ^ r).coeff (j + d + 1) ≤ (P ^ r).coeff (j + d) := ih (by omega)
        set m := j + d + 1
        have hm_gt : meanP n P 1 * (r : ℝ) - (σ / 2) * Real.sqrt r < (m : ℝ) := by
          have : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show j ≤ m by omega)
          linarith
        by_cases hm_in : (m : ℝ) ≤ meanP n P 1 * (r : ℝ) + (σ / 2) * Real.sqrt r
        · have hm1 : 1 ≤ m := by omega
          have hc := hCenter m hm1 hm_gt.le hm_in
          rw [show m - 1 = j + d by omega] at hc
          have hm_eq : j + (d + 1) = m := by dsimp [m]; omega
          rw [hm_eq]
          linarith
        · push Not at hm_in
          have hm_eq : j + (d + 1) = m := by dsimp [m]; omega
          rw [hm_eq]
          exact hRight m hm_in.le (by omega)
    refine ⟨j, hj_spec.1.le, hj_min, ?_⟩
    intro i hi hlt
    have heq : i = j + (i - j) := by omega
    rw [heq]
    exact hdesc (i - j) (by omega)
  · push Not at hdrop
    refine ⟨n * r, le_rfl, ?_, fun i hi hlt => by omega⟩
    intro i hi
    exact hdrop i hi

end OMA.Mse4399939

theorem OMA.solution : type_of% @OMA.S_mse_4399939.main := by
  intro n P hdeg hpos
  by_cases hn : 2 ≤ n
  · exact OMA.Mse4399939.eventual_unimodal_ge2 hn hdeg hpos
  · refine ⟨1, by omega, 0, by omega, ?_, ?_⟩
    · intro i hi; omega
    · intro i hi hlt; omega


