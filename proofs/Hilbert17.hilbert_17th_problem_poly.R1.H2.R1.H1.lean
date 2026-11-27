import OMAReductions.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1

-- Step Hilbert17.hilbert_17th_problem_poly.R1.H2.R1.H1: hypothesis H1 of reduction Hilbert17.hilbert_17th_problem_poly.R1.H2.R1
-- Credit: @MrZaow
-- H1 := ∀ d : ℕ, 0 < d → Hilbert17thProblemHomogenousPoly 2 d

private lemma poly_nonneg_sum_two_sq (p : Polynomial ℝ) (hp : ∀ x : ℝ, 0 ≤ p.eval x) :
    ∃ a b : Polynomial ℝ, p = a ^ 2 + b ^ 2 := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hp0 : p = 0
    · subst hp0; exact ⟨0, 0, by simp⟩
    by_cases hn0 : n = 0
    · subst hn0
      have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hn
      have hc : 0 ≤ p.coeff 0 := by
        have h0 := hp 0
        rw [hpC, Polynomial.eval_C] at h0
        exact h0
      refine ⟨Polynomial.C (Real.sqrt (p.coeff 0)), 0, ?_⟩
      rw [zero_pow two_ne_zero, add_zero, ← map_pow, Real.sq_sqrt hc]
      exact hpC
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    let q : Polynomial ℂ := p.map (algebraMap ℝ ℂ)
    have hqdeg : q.natDegree = n := by
      rw [← hn]
      exact Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective p
    have hq_ne : q ≠ 0 := by
      intro h
      have := congrArg Polynomial.natDegree h
      simp [hqdeg] at this
      omega
    have hq_pos : 0 < q.degree := by
      rw [Polynomial.degree_eq_natDegree hq_ne, hqdeg]
      exact_mod_cast hn_pos
    obtain ⟨z, hz⟩ := Complex.exists_root hq_pos
    have hza : Polynomial.aeval z p = 0 := by
      simpa [q, Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map] using hz
    by_cases hzim : z.im = 0
    · let r : ℝ := z.re
      have hzr : z = (r : ℂ) := Complex.ext rfl (by simpa using hzim)
      have hpr : p.IsRoot r := by
        rw [Polynomial.IsRoot]
        apply Complex.ofReal_injective
        have hmap : ∀ (g : Polynomial ℝ), Complex.ofReal (Polynomial.eval r g) = Polynomial.aeval (r : ℂ) g := by
          intro g
          induction g using Polynomial.induction_on' with
          | add a b ha hb => simp [ha, hb]
          | monomial n a => simp [Polynomial.aeval_monomial]
        rw [hmap p, ← hzr, hza, Complex.ofReal_zero]
      obtain ⟨p1, hp1⟩ := Polynomial.dvd_iff_isRoot.mpr hpr
      have hp1r : p1.IsRoot r := by
        by_contra hne
        rw [Polynomial.IsRoot] at hne
        have hcont : ContinuousAt (fun x : ℝ => p1.eval x) r := p1.continuous.continuousAt
        obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont |p1.eval r| (abs_pos.mpr hne)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · let x := r + δ / 2
          have hx_dist : dist x r < δ := by
            simp only [x, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδpos)]
            linarith
          have hp1x_neg : p1.eval x < 0 := by
            have hd := hδ hx_dist
            rw [Real.dist_eq, abs_lt] at hd
            linarith [abs_of_neg hlt]
          have hpx_neg : p.eval x < 0 := by
            rw [hp1, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
            have hxr : 0 < x - r := by simp [x]; linarith
            exact mul_neg_of_pos_of_neg hxr hp1x_neg
          linarith [hp x]
        · let x := r - δ / 2
          have hx_dist : dist x r < δ := by
            simp only [x, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (half_pos hδpos)]
            linarith
          have hp1x_pos : 0 < p1.eval x := by
            have hd := hδ hx_dist
            rw [Real.dist_eq, abs_lt] at hd
            linarith [abs_of_pos hgt]
          have hpx_neg : p.eval x < 0 := by
            rw [hp1, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
            have hxr : x - r < 0 := by simp [x]; linarith
            exact mul_neg_of_neg_of_pos hxr hp1x_pos
          linarith [hp x]
      obtain ⟨p2, hp2⟩ := Polynomial.dvd_iff_isRoot.mpr hp1r
      have hp_eq : p = (Polynomial.X - Polynomial.C r) ^ 2 * p2 := by
        rw [hp1, hp2]; ring
      have hp2_ne : p2 ≠ 0 := by
        intro h; subst h; apply hp0; simpa using hp_eq
      have hp2_nonneg : ∀ x : ℝ, 0 ≤ p2.eval x := by
        intro x
        by_cases hxr : x = r
        · subst hxr
          by_contra! hlt
          have hcont : ContinuousAt (fun t : ℝ => p2.eval t) r := p2.continuous.continuousAt
          obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont |p2.eval r| (abs_pos.mpr hlt.ne)
          let y := r + δ / 2
          have hy_dist : dist y r < δ := by
            simp only [y, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδpos)]
            linarith
          have hp2y_neg : p2.eval y < 0 := by
            have hd := hδ hy_dist
            rw [Real.dist_eq, abs_lt] at hd
            linarith [abs_of_neg hlt]
          have hy_ne : y - r ≠ 0 := by simp [y]; linarith
          have hpy_neg : p.eval y < 0 := by
            rw [hp_eq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
              Polynomial.eval_X, Polynomial.eval_C]
            exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hy_ne) hp2y_neg
          linarith [hp y]
        · have hpos_sq : 0 < (x - r) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxr)
          have hpx := hp x
          rw [hp_eq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
            Polynomial.eval_X, Polynomial.eval_C] at hpx
          exact nonneg_of_mul_nonneg_right hpx hpos_sq
      have hdeg_lin : (Polynomial.X - Polynomial.C r).natDegree = 1 :=
        Polynomial.natDegree_X_sub_C r
      have hdeg_sq : ((Polynomial.X - Polynomial.C r) ^ 2).natDegree = 2 := by
        rw [Polynomial.natDegree_pow, hdeg_lin]
      have hp2_deg : p2.natDegree < n := by
        have hmul : p.natDegree = ((Polynomial.X - Polynomial.C r) ^ 2).natDegree + p2.natDegree := by
          rw [hp_eq]
          exact Polynomial.natDegree_mul (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero r)) hp2_ne
        omega
      obtain ⟨a2, b2, hab2⟩ := ih p2.natDegree hp2_deg p2 hp2_nonneg rfl
      refine ⟨(Polynomial.X - Polynomial.C r) * a2, (Polynomial.X - Polynomial.C r) * b2, ?_⟩
      rw [hp_eq, hab2]; ring
    · let Q : Polynomial ℝ := (Polynomial.X - Polynomial.C z.re) ^ 2 + Polynomial.C (z.im ^ 2)
      have hQ_eq : Q = Polynomial.X ^ 2 +
          (Polynomial.C (-2 * z.re) * Polynomial.X + Polynomial.C (z.re ^ 2 + z.im ^ 2)) := by
        simp only [Q, map_add, map_mul, map_neg, map_ofNat, map_pow]; ring
      have hQ_tail_deg :
          (Polynomial.C (-2 * z.re) * Polynomial.X + Polynomial.C (z.re ^ 2 + z.im ^ 2)).natDegree < 2 := by
        have h1 : (Polynomial.C (-2 * z.re) * Polynomial.X).natDegree ≤ 1 :=
          (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
        have h2 : (Polynomial.C (z.re ^ 2 + z.im ^ 2) : Polynomial ℝ).natDegree = 0 :=
          Polynomial.natDegree_C _
        have h3 := Polynomial.natDegree_add_le
          (Polynomial.C (-2 * z.re) * Polynomial.X) (Polynomial.C (z.re ^ 2 + z.im ^ 2))
        omega
      have hQ_tail_deg' :
          (Polynomial.C (-2 * z.re) * Polynomial.X + Polynomial.C (z.re ^ 2 + z.im ^ 2)).degree <
            (Polynomial.X ^ 2 : Polynomial ℝ).degree := by
        rw [Polynomial.degree_X_pow]
        exact (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast hQ_tail_deg)
      have hQ_monic : Q.Monic := by
        rw [hQ_eq]
        exact (Polynomial.monic_X_pow 2).add_of_left hQ_tail_deg'
      have hQ_deg : Q.natDegree = 2 := by
        rw [hQ_eq, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
        · simp
        · simpa using hQ_tail_deg
      have hQ_pos_deg : Q.degree = 2 := by
        rw [Polynomial.degree_eq_natDegree hQ_monic.ne_zero, hQ_deg]
        rfl
      let p2 := p /ₘ Q
      let rem := p %ₘ Q
      have hp_div : rem + Q * p2 = p := Polynomial.modByMonic_add_div p Q
      have hrem_deg : rem.degree < 2 := by
        rw [← hQ_pos_deg]
        exact Polynomial.degree_modByMonic_lt p hQ_monic
      have hrem_natDeg : rem.natDegree ≤ 1 := by
        by_cases hr0 : rem = 0
        · simp [hr0]
        rw [Polynomial.degree_eq_natDegree hr0] at hrem_deg
        have : rem.natDegree < 2 := by exact_mod_cast hrem_deg
        omega
      have hrem_eq : rem = Polynomial.C (rem.coeff 0) + Polynomial.C (rem.coeff 1) * Polynomial.X := by
        ext k
        rcases k with _ | _ | k
        · simp
        · simp
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
          simp
      have hQz : Polynomial.aeval z Q = 0 := by
        simp only [Q, map_add, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
        apply Complex.ext
        · simp [Complex.sub_re, Complex.mul_re, sq]
        · simp [Complex.sub_im, Complex.mul_im, sq]
      have hrem_z : Polynomial.aeval z rem = 0 := by
        have h1 := congrArg (Polynomial.aeval z) hp_div
        rw [map_add, map_mul, hQz, zero_mul, add_zero, hza] at h1
        exact h1
      have hrem_z' : (rem.coeff 0 : ℂ) + (rem.coeff 1 : ℂ) * z = 0 := by
        have h := hrem_z
        conv_lhs at h => rw [hrem_eq]
        simpa [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X] using h
      have hrem1 : rem.coeff 1 = 0 := by
        have him := congrArg Complex.im hrem_z'
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          zero_add, zero_mul, add_zero, Complex.zero_im] at him
        exact (mul_eq_zero.mp him).resolve_right hzim
      have hrem0 : rem.coeff 0 = 0 := by
        have hre := congrArg Complex.re hrem_z'
        simp only [hrem1, Complex.ofReal_zero, zero_mul, add_zero, Complex.zero_re] at hre
        exact hre
      have hrem_zero : rem = 0 := by
        rw [hrem_eq, hrem0, hrem1]; simp
      have hp_eq : p = Q * p2 := by
        rw [← hp_div, hrem_zero, zero_add]
      have hp2_ne : p2 ≠ 0 := by
        intro h
        apply hp0
        rw [h, mul_zero] at hp_eq
        exact hp_eq
      have hp2_nonneg : ∀ x : ℝ, 0 ≤ p2.eval x := by
        intro x
        have hQx : 0 < Q.eval x := by
          simp only [Q, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_sub,
            Polynomial.eval_X, Polynomial.eval_C]
          positivity [sq_pos_of_ne_zero hzim]
        have hpx := hp x
        rw [hp_eq, Polynomial.eval_mul] at hpx
        exact nonneg_of_mul_nonneg_right hpx hQx
      have hp2_deg : p2.natDegree < n := by
        have hmul : p.natDegree = Q.natDegree + p2.natDegree := by
          rw [hp_eq]
          exact Polynomial.natDegree_mul hQ_monic.ne_zero hp2_ne
        omega
      obtain ⟨a2, b2, hab2⟩ := ih p2.natDegree hp2_deg p2 hp2_nonneg rfl
      refine ⟨(Polynomial.X - Polynomial.C z.re) * a2 - Polynomial.C z.im * b2,
        (Polynomial.X - Polynomial.C z.re) * b2 + Polynomial.C z.im * a2, ?_⟩
      rw [hp_eq, hab2]
      simp only [Q, map_pow]
      ring

private lemma coeff_sq_two_mul {q : Polynomial ℝ} {m : ℕ} (hq : q.natDegree ≤ m) :
    (q ^ 2).coeff (2 * m) = (q.coeff m) ^ 2 := by
  rcases hq.lt_or_eq with hlt | rfl
  · have hdeg : (q ^ 2).natDegree < 2 * m := by
      have := Polynomial.natDegree_pow_le (p := q) (n := 2)
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg,
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt, zero_pow two_ne_zero]
  · have hdeg : (q ^ 2).natDegree = 2 * q.natDegree := Polynomial.natDegree_pow q 2
    have hlc : (q ^ 2).leadingCoeff = q.leadingCoeff ^ 2 := Polynomial.leadingCoeff_pow q 2
    rw [← hdeg]
    exact hlc

private lemma natDegree_le_of_sq_add_sq {a b : Polynomial ℝ} {d : ℕ}
    (h : (a ^ 2 + b ^ 2).natDegree ≤ 2 * d) : a.natDegree ≤ d ∧ b.natDegree ≤ d := by
  let m := max a.natDegree b.natDegree
  have hm : m ≤ d := by
    by_contra! hmd
    have hcoeff0 : (a ^ 2 + b ^ 2).coeff (2 * m) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [Polynomial.coeff_add, coeff_sq_two_mul (le_max_left _ _),
      coeff_sq_two_mul (le_max_right _ _)] at hcoeff0
    have ha0 : a.coeff m = 0 := by nlinarith
    have hb0 : b.coeff m = 0 := by nlinarith
    rcases le_max_iff.mp (le_refl m) with h1 | h2
    · have hm_eq : m = a.natDegree := le_antisymm h1 (le_max_left _ _)
      have ha_ne : a ≠ 0 := by
        intro h0
        rw [h0, Polynomial.natDegree_zero] at hm_eq
        omega
      exact absurd (by rw [Polynomial.leadingCoeff, ← hm_eq]; exact ha0)
        (Polynomial.leadingCoeff_ne_zero.mpr ha_ne)
    · have hm_eq : m = b.natDegree := le_antisymm h2 (le_max_right _ _)
      have hb_ne : b ≠ 0 := by
        intro h0
        rw [h0, Polynomial.natDegree_zero] at hm_eq
        omega
      exact absurd (by rw [Polynomial.leadingCoeff, ← hm_eq]; exact hb0)
        (Polynomial.leadingCoeff_ne_zero.mpr hb_ne)
  exact ⟨(le_max_left _ _).trans hm, (le_max_right _ _).trans hm⟩

private noncomputable def homogenize2 (d : ℕ) (q : Polynomial ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∑ i ∈ Finset.range (d + 1),
    MvPolynomial.C (q.coeff i) * MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ (d - i)

private lemma homogenize2_isHomogeneous (d : ℕ) (q : Polynomial ℝ) :
    (homogenize2 d q).IsHomogeneous d := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => ?_
  have hi_le : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : (MvPolynomial.C (q.coeff i) : MvPolynomial (Fin 2) ℝ).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C _ _
  have h2 : ((MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ) ^ i).IsHomogeneous i :=
    MvPolynomial.isHomogeneous_X_pow _ _
  have h3 : ((MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ) ^ (d - i)).IsHomogeneous (d - i) :=
    MvPolynomial.isHomogeneous_X_pow _ _
  have h123 := (h1.mul h2).mul h3
  rwa [show 0 + i + (d - i) = d by omega] at h123

private lemma eval_homogenize2_one {d : ℕ} {q : Polynomial ℝ} (hq : q.natDegree ≤ d) (t : ℝ) :
    MvPolynomial.eval ![t, 1] (homogenize2 d q) = q.eval t := by
  simp only [homogenize2, map_sum, map_mul, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_pow, mul_one]
  exact (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hq) t).symm

private lemma homogeneousScale2 {N : ℕ} {p : MvPolynomial (Fin 2) ℝ} (hp : p.IsHomogeneous N)
    (a : ℝ) (v : Fin 2 → ℝ) :
    MvPolynomial.eval (fun i => a * v i) p = a ^ N * MvPolynomial.eval v p := by
  classical
  conv_lhs => rw [← p.support_sum_monomial_coeff]
  conv_rhs => rw [← p.support_sum_monomial_coeff]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hp.degree_eq_sum_deg_support hu]
  ring

private lemma eq_of_isHomogeneous_eval_one {N : ℕ} {P Q : MvPolynomial (Fin 2) ℝ}
    (hP : P.IsHomogeneous N) (hQ : Q.IsHomogeneous N)
    (h : ∀ t : ℝ, MvPolynomial.eval ![t, 1] P = MvPolynomial.eval ![t, 1] Q) : P = Q := by
  let R := P - Q
  have hR : R.IsHomogeneous N := hP.sub hQ
  have hR_one : ∀ t : ℝ, MvPolynomial.eval ![t, 1] R = 0 := by
    intro t
    simp [R, map_sub, h t]
  have hR_all : ∀ x : Fin 2 → ℝ, MvPolynomial.eval x R = 0 := by
    intro x
    by_cases hx1 : x 1 = 0
    · let φ : ℝ → ℝ := fun y => MvPolynomial.eval ![x 0, y] R
      have hφ_cont : Continuous φ :=
        R.continuous_eval.comp (continuous_pi fun i => by fin_cases i <;> [exact continuous_const; exact continuous_id])
      have hφ_nz : ∀ y : ℝ, y ≠ 0 → φ y = 0 := by
        intro y hy
        have hvec : ![x 0, y] = fun i => y * (![x 0 / y, 1] i) := by
          ext i; fin_cases i <;> simp [mul_div_cancel₀ _ hy]
        dsimp [φ]
        rw [hvec, homogeneousScale2 hR, hR_one, mul_zero]
      have hφ0 : φ 0 = 0 := by
        by_contra hne
        obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hφ_cont.continuousAt |φ 0| (abs_pos.mpr hne)
        have hdist : dist (δ / 2) 0 < δ := by
          simp only [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδpos)]
          linarith
        have hd := hδ hdist
        rw [hφ_nz (δ / 2) (half_pos hδpos).ne', Real.dist_eq, zero_sub, abs_neg] at hd
        exact lt_irrefl _ hd
      have hx_eq : x = ![x 0, 0] := by
        ext i; fin_cases i <;> simp [hx1]
      rw [hx_eq]
      exact hφ0
    · have hvec : x = fun i => x 1 * (![x 0 / x 1, 1] i) := by
        ext i; fin_cases i <;> simp [mul_div_cancel₀ _ hx1]
      rw [hvec, homogeneousScale2 hR, hR_one, mul_zero]
  exact sub_eq_zero.mp (MvPolynomial.funext hR_all)

private lemma eval_dehomogenize2 (f : MvPolynomial (Fin 2) ℝ) (t : ℝ) :
    (MvPolynomial.aeval ![Polynomial.X, (1 : Polynomial ℝ)] f).eval t =
      MvPolynomial.eval ![t, 1] f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add a b ha hb => simp [ha, hb]
  | mul_X a i ha => fin_cases i <;> simp [ha]

theorem OMA.solution : OMA.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1.H1 := by
  intro d _hd f hf hpos
  let p : Polynomial ℝ := MvPolynomial.aeval ![Polynomial.X, (1 : Polynomial ℝ)] f
  have hp_eval : ∀ t : ℝ, p.eval t = MvPolynomial.eval ![t, 1] f := eval_dehomogenize2 f
  have hp_deg : p.natDegree ≤ 2 * d := by
    dsimp [p]
    conv_lhs => rw [← f.support_sum_monomial_coeff]
    rw [map_sum]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun u hu => ?_
    rw [MvPolynomial.aeval_monomial]
    have hdeg_sum : (∑ i : Fin 2, u i) = 2 * d := by
      have hs : (∑ i ∈ u.support, u i) = 2 * d := (hf.degree_eq_sum_deg_support hu).symm
      rw [← hs]
      exact (Finset.sum_subset (Finset.subset_univ u.support) fun i _ hi => by
        simpa [Finsupp.mem_support_iff] using hi).symm
    have hu0 : u 0 ≤ 2 * d := by
      rw [Fin.sum_univ_two] at hdeg_sum
      omega
    have hprod : (Finsupp.prod u fun i e => (![Polynomial.X, (1 : Polynomial ℝ)] i) ^ e) =
        Polynomial.X ^ (u 0) := by
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
      simp
    rw [hprod, Polynomial.algebraMap_eq]
    exact (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_X_pow_le _).trans hu0)
  obtain ⟨a, b, hab⟩ := poly_nonneg_sum_two_sq p (fun t => by rw [hp_eval]; exact hpos _)
  have hab_deg : (a ^ 2 + b ^ 2).natDegree ≤ 2 * d := by rwa [← hab]
  obtain ⟨ha, hb⟩ := natDegree_le_of_sq_add_sq hab_deg
  let A := homogenize2 d a
  let B := homogenize2 d b
  have hA : A.IsHomogeneous d := homogenize2_isHomogeneous d a
  have hB : B.IsHomogeneous d := homogenize2_isHomogeneous d b
  have hsq_hom : (A ^ 2 + B ^ 2).IsHomogeneous (2 * d) := by
    have hA2 : (A ^ 2).IsHomogeneous (2 * d) := by
      simpa [mul_comm] using hA.pow 2
    have hB2 : (B ^ 2).IsHomogeneous (2 * d) := by
      simpa [mul_comm] using hB.pow 2
    exact hA2.add hB2
  have h_eq : f = A ^ 2 + B ^ 2 := by
    refine eq_of_isHomogeneous_eval_one hf hsq_hom fun t => ?_
    rw [← hp_eval t, hab, map_add, map_pow, map_pow, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_pow,
      eval_homogenize2_one ha t, eval_homogenize2_one hb t]
  exact ⟨2, ![A, B], by simp [Fin.sum_univ_two, h_eq]⟩
