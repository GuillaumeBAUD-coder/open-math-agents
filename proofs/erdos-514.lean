import OMAStatements.S_erdos_514

namespace OMA.P_erdos_514

open Filter Polynomial Bornology Complex Metric Set Topology

/-!
## Part 1: Entire functions of polynomial growth are polynomials
-/

private lemma dslope_entire {h : ℂ → ℂ} (hh : Differentiable ℂ h) :
    Differentiable ℂ (dslope h 0) := by
  rw [← differentiableOn_univ] at hh ⊢
  exact (Complex.differentiableOn_dslope (by simp : (Set.univ : Set ℂ) ∈ 𝓝 (0 : ℂ))).mpr hh

private lemma dslope_eq_add_mul (h : ℂ → ℂ) (z : ℂ) :
    h z = h 0 + z * dslope h 0 z := by
  have h1 := sub_smul_dslope h (0 : ℂ) z
  simp only [sub_zero, smul_eq_mul] at h1
  linear_combination -h1

private lemma isPoly_of_norm_le_pow :
    ∀ (d : ℕ) (h : ℂ → ℂ), Differentiable ℂ h →
      (∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, ‖h z‖ ≤ K * (1 + ‖z‖) ^ d) →
      ∃ p : ℂ[X], h = fun z => p.eval z
  | 0, h, hh, ⟨K, hK, hbd⟩ => by
    have hbounded : IsBounded (Set.range h) := by
      rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
      refine ⟨K, ?_⟩
      rintro _ ⟨z, rfl⟩
      simp only [Metric.mem_closedBall, dist_zero_right]
      simpa using hbd z
    refine ⟨Polynomial.C (h 0), ?_⟩
    funext z
    simpa using hh.apply_eq_apply_of_bounded hbounded z 0
  | d + 1, h, hh, ⟨K, hK, hbd⟩ => by
    let h₁ : ℂ → ℂ := dslope h 0
    have hh₁ : Differentiable ℂ h₁ := dslope_entire hh
    have hcomp : IsCompact (Metric.closedBall (0 : ℂ) 1) := isCompact_closedBall 0 1
    obtain ⟨C₀, hC₀_nonneg, hC₀⟩ : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖h₁ z‖ ≤ C₀ := by
      obtain ⟨w, _, hw⟩ := hcomp.exists_isMaxOn ⟨0, Metric.mem_closedBall_self zero_le_one⟩
        hh₁.continuous.norm.continuousOn
      exact ⟨max 0 ‖h₁ w‖, le_max_left _ _, fun z hz => (hw hz).trans (le_max_right _ _)⟩
    have hbd₁ : ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ z : ℂ, ‖h₁ z‖ ≤ K₁ * (1 + ‖z‖) ^ d := by
      refine ⟨C₀ + 2 * K + ‖h 0‖, by positivity, fun z => ?_⟩
      by_cases hz : ‖z‖ ≤ 1
      · have h1 : ‖h₁ z‖ ≤ C₀ := hC₀ z (by simpa [Metric.mem_closedBall] using hz)
        have hpow : (1 : ℝ) ≤ (1 + ‖z‖) ^ d := one_le_pow₀ (by linarith [norm_nonneg z])
        nlinarith [norm_nonneg (h 0)]
      · push Not at hz
        have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at hz; linarith
        have hstep : h₁ z = z⁻¹ * (h z - h 0) := by
          simp only [h₁, dslope_of_ne _ hz0, slope, vsub_eq_sub, sub_zero, smul_eq_mul]
        have hnorm : ‖h₁ z‖ ≤ (‖h z‖ + ‖h 0‖) / ‖z‖ := by
          rw [hstep, norm_mul, norm_inv, ← div_eq_inv_mul]
          exact div_le_div_of_nonneg_right (norm_sub_le (h z) (h 0)) (norm_nonneg z)
        have hzpos : 0 < ‖z‖ := by linarith
        have h1 : (1 + ‖z‖) / ‖z‖ ≤ 2 := by
          rw [div_le_iff₀ hzpos]; linarith
        have h2 : K * (1 + ‖z‖) ^ (d + 1) / ‖z‖ ≤ 2 * K * (1 + ‖z‖) ^ d := by
          rw [pow_succ, mul_div_assoc]
          have hpow0 : 0 ≤ (1 + ‖z‖) ^ d := by positivity
          calc K * ((1 + ‖z‖) ^ d * (1 + ‖z‖) / ‖z‖)
              = K * (1 + ‖z‖) ^ d * ((1 + ‖z‖) / ‖z‖) := by ring
            _ ≤ K * (1 + ‖z‖) ^ d * 2 := by
                exact mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = 2 * K * (1 + ‖z‖) ^ d := by ring
        have h3 : ‖h 0‖ / ‖z‖ ≤ ‖h 0‖ * (1 + ‖z‖) ^ d := by
          have hpow1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ d := one_le_pow₀ (by linarith [norm_nonneg z])
          calc ‖h 0‖ / ‖z‖ ≤ ‖h 0‖ / 1 := div_le_div_of_nonneg_left (norm_nonneg _) zero_lt_one hz.le
            _ = ‖h 0‖ := div_one _
            _ ≤ ‖h 0‖ * (1 + ‖z‖) ^ d := le_mul_of_one_le_right (norm_nonneg _) hpow1
        have h4 : 0 ≤ C₀ * (1 + ‖z‖) ^ d := by positivity
        have hbdz := hbd z
        have h5 : (‖h z‖ + ‖h 0‖) / ‖z‖ ≤ K * (1 + ‖z‖) ^ (d + 1) / ‖z‖ + ‖h 0‖ / ‖z‖ := by
          rw [add_div]
          exact add_le_add (div_le_div_of_nonneg_right hbdz hzpos.le) le_rfl
        linarith
    obtain ⟨p, hp⟩ := isPoly_of_norm_le_pow d h₁ hh₁ hbd₁
    refine ⟨Polynomial.C (h 0) + Polynomial.X * p, ?_⟩
    funext z
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    have hval : p.eval z = h₁ z := by rw [hp]
    rw [hval]
    exact dslope_eq_add_mul h z

/-!
## Part 2: Iterated `dslope` sequence `shiftDiv f n`
-/

private noncomputable def shiftDiv (f : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => f
  | n + 1 => dslope (shiftDiv f n) 0

private lemma shiftDiv_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ∀ n : ℕ, Differentiable ℂ (shiftDiv f n)
  | 0 => hf
  | n + 1 => dslope_entire (shiftDiv_differentiable hf n)

private lemma shiftDiv_step (f : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    shiftDiv f n z = shiftDiv f n 0 + z * shiftDiv f (n + 1) z :=
  dslope_eq_add_mul (shiftDiv f n) z

private lemma shiftDiv_transcendental {f : ℂ → ℂ}
    (htrans : ∀ p : ℂ[X], f ≠ fun z => p.eval z) :
    ∀ n : ℕ, ∀ p : ℂ[X], shiftDiv f n ≠ fun z => p.eval z
  | 0, p => htrans p
  | n + 1, p => by
    intro h
    apply shiftDiv_transcendental htrans n (Polynomial.C (shiftDiv f n 0) + Polynomial.X * p)
    funext z
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    have hpz : p.eval z = shiftDiv f (n + 1) z := (congrFun h z).symm
    rw [hpz]
    exact shiftDiv_step f n z

private lemma shiftDiv_rem_bound (f : ℂ → ℂ) :
    ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, 1 ≤ ‖z‖ →
      ‖f z - z ^ n * shiftDiv f n z‖ ≤ B * ‖z‖ ^ n
  | 0 => ⟨0, le_rfl, fun z _ => by simp [shiftDiv]⟩
  | n + 1 => by
    obtain ⟨B, hB, hbd⟩ := shiftDiv_rem_bound f n
    refine ⟨B + ‖shiftDiv f n 0‖, by positivity, fun z hz => ?_⟩
    have hdecomp : f z - z ^ (n + 1) * shiftDiv f (n + 1) z =
        (f z - z ^ n * shiftDiv f n z) + z ^ n * shiftDiv f n 0 := by
      have hst := shiftDiv_step f n z
      rw [pow_succ]
      linear_combination z ^ n * hst
    rw [hdecomp]
    calc ‖(f z - z ^ n * shiftDiv f n z) + z ^ n * shiftDiv f n 0‖
        ≤ ‖f z - z ^ n * shiftDiv f n z‖ + ‖z ^ n * shiftDiv f n 0‖ := norm_add_le _ _
      _ ≤ B * ‖z‖ ^ n + ‖z‖ ^ n * ‖shiftDiv f n 0‖ := by
          rw [norm_mul, norm_pow]
          exact add_le_add (hbd z hz) le_rfl
      _ = (B + ‖shiftDiv f n 0‖) * ‖z‖ ^ n := by ring
      _ ≤ (B + ‖shiftDiv f n 0‖) * ‖z‖ ^ (n + 1) := by
          rw [pow_succ]
          have h1 : ‖z‖ ^ n ≤ ‖z‖ ^ n * ‖z‖ := le_mul_of_one_le_right (by positivity) hz
          exact mul_le_mul_of_nonneg_left h1 (by positivity)

private lemma shiftDiv_approx (f : ℂ → ℂ) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, 1 ≤ ‖z‖ →
      ‖shiftDiv f n z‖ - B ≤ ‖f z / z ^ n‖ := by
  obtain ⟨B, hB, hbd⟩ := shiftDiv_rem_bound f n
  refine ⟨B, hB, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at hz; linarith
  have hzn0 : z ^ n ≠ 0 := pow_ne_zero n hz0
  have hnorm_zn : 0 < ‖z‖ ^ n := by positivity
  have hdiff : ‖shiftDiv f n z - f z / z ^ n‖ ≤ B := by
    have heq : shiftDiv f n z - f z / z ^ n = -(f z - z ^ n * shiftDiv f n z) / z ^ n := by
      field_simp [hzn0]
      ring
    rw [heq, norm_div, norm_neg, norm_pow, div_le_iff₀ hnorm_zn]
    exact hbd z hz
  have htri : ‖shiftDiv f n z‖ - ‖f z / z ^ n‖ ≤ ‖shiftDiv f n z - f z / z ^ n‖ :=
    norm_sub_norm_le _ _
  linarith

/-!
## Part 3: Superlevel sets and path components
-/

private lemma superlevel_isOpen {h : ℂ → ℂ} (hh : Differentiable ℂ h) (M : ℝ) :
    IsOpen {z : ℂ | M < ‖h z‖} :=
  isOpen_lt continuous_const hh.continuous.norm

private lemma superlevel_nonempty {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (htrans : ∀ p : ℂ[X], h ≠ fun z => p.eval z) (M : ℝ) :
    ({z : ℂ | M < ‖h z‖}).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hbd : ∀ z : ℂ, ‖h z‖ ≤ max M 0 * (1 + ‖z‖) ^ 0 := by
    intro z
    have hz : z ∉ {w : ℂ | M < ‖h w‖} := by rw [hne]; exact Set.notMem_empty z
    simp only [Set.mem_ofPred_eq, not_lt] at hz
    simpa using hz.trans (le_max_left M 0)
  obtain ⟨p, hp⟩ := isPoly_of_norm_le_pow 0 h hh ⟨max M 0, le_max_right M 0, hbd⟩
  exact htrans p hp

private lemma norm_eq_of_mem_frontier_pathComponentIn {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (M : ℝ) {z₀ : ℂ} (_hz₀ : M < ‖h z₀‖) {w : ℂ}
    (hw : w ∈ frontier (pathComponentIn {z : ℂ | M < ‖h z‖} z₀)) :
    ‖h w‖ = M := by
  set V : Set ℂ := {z : ℂ | M < ‖h z‖}
  set C : Set ℂ := pathComponentIn V z₀
  have hV_open : IsOpen V := superlevel_isOpen hh M
  have hC_open : IsOpen C := hV_open.pathComponentIn z₀
  rw [hC_open.frontier_eq] at hw
  have hge : M ≤ ‖h w‖ := by
    have hsub : C ⊆ {z : ℂ | M ≤ ‖h z‖} :=
      pathComponentIn_subset.trans (fun _ hx => show M ≤ ‖h _‖ from le_of_lt hx)
    have hcl : IsClosed {z : ℂ | M ≤ ‖h z‖} := isClosed_le continuous_const hh.continuous.norm
    exact closure_minimal hsub hcl hw.1
  refine le_antisymm ?_ hge
  by_contra hlt
  push Not at hlt
  have hwV : w ∈ V := hlt
  have hW_open : IsOpen (pathComponentIn V w) := hV_open.pathComponentIn w
  have hwW : w ∈ pathComponentIn V w := mem_pathComponentIn_self hwV
  have hinter : (pathComponentIn V w ∩ C).Nonempty :=
    mem_closure_iff.mp hw.1 (pathComponentIn V w) hW_open hwW
  obtain ⟨y, hyW, hyC⟩ := hinter
  have hjoin : JoinedIn V z₀ w := hyC.trans hyW.symm
  exact hw.2 hjoin

private lemma not_isBounded_pathComponentIn {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (M : ℝ) {z₀ : ℂ} (hz₀ : M < ‖h z₀‖) :
    ¬ IsBounded (pathComponentIn {z : ℂ | M < ‖h z‖} z₀) := by
  intro hbdd
  have hle := Complex.norm_le_of_forall_mem_frontier_norm_le hbdd hh.diffContOnCl
    (C := M) (fun w hw => (norm_eq_of_mem_frontier_pathComponentIn hh M hz₀ hw).le)
    (subset_closure (mem_pathComponentIn_self hz₀))
  linarith

/-!
## Part 4: Elementary Blaschke product barrier
-/

private noncomputable def blaschkeFactor (r : ℝ) (ζ z : ℂ) : ℂ :=
  ((4 * r ^ 2 : ℝ) - starRingEnd ℂ ζ * z) / ((2 * r : ℝ) * (z - ζ))

private lemma blaschke_norm_sq_diff (r : ℝ) (ζ z : ℂ) :
    ‖((4 * r ^ 2 : ℝ) : ℂ) - starRingEnd ℂ ζ * z‖ ^ 2 - (2 * r * ‖z - ζ‖) ^ 2 =
      (4 * r ^ 2 - ‖z‖ ^ 2) * (4 * r ^ 2 - ‖ζ‖ ^ 2) := by
  have h1 : ‖((4 * r ^ 2 : ℝ) : ℂ) - starRingEnd ℂ ζ * z‖ ^ 2 =
      Complex.normSq (((4 * r ^ 2 : ℝ) : ℂ) - starRingEnd ℂ ζ * z) := Complex.sq_norm _
  have h2 : ‖z - ζ‖ ^ 2 = Complex.normSq (z - ζ) := Complex.sq_norm _
  have h3 : ‖z‖ ^ 2 = Complex.normSq z := Complex.sq_norm _
  have h4 : ‖ζ‖ ^ 2 = Complex.normSq ζ := Complex.sq_norm _
  have hmul : (2 * r * ‖z - ζ‖) ^ 2 = 4 * r ^ 2 * ‖z - ζ‖ ^ 2 := by ring
  rw [hmul, h1, h2, h3, h4]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private lemma blaschkeFactor_norm_eq_one {r : ℝ} (hr : 0 < r) {ζ z : ℂ}
    (hz : ‖z‖ = 2 * r) (hne : z ≠ ζ) :
    ‖blaschkeFactor r ζ z‖ = 1 := by
  have hden : 0 < 2 * r * ‖z - ζ‖ := mul_pos (by linarith) (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hnum_sq : ‖((4 * r ^ 2 : ℝ) : ℂ) - starRingEnd ℂ ζ * z‖ ^ 2 = (2 * r * ‖z - ζ‖) ^ 2 := by
    have hd := blaschke_norm_sq_diff r ζ z
    rw [hz] at hd
    linarith
  have hnum : ‖((4 * r ^ 2 : ℝ) : ℂ) - starRingEnd ℂ ζ * z‖ = 2 * r * ‖z - ζ‖ := by
    nlinarith [norm_nonneg (((4 * r ^ 2 : ℝ) : ℂ) - starRingEnd ℂ ζ * z)]
  rw [blaschkeFactor, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ 2 * r),
    hnum, div_self hden.ne']

private lemma blaschkeFactor_norm_ge_one {r : ℝ} (hr : 0 < r) {ζ z : ℂ}
    (hζ : ‖ζ‖ ≤ r) (hz : ‖z‖ ≤ 2 * r) (hne : z ≠ ζ) :
    1 ≤ ‖blaschkeFactor r ζ z‖ := by
  have hden : 0 < 2 * r * ‖z - ζ‖ := mul_pos (by linarith) (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hdiff := blaschke_norm_sq_diff r ζ z
  have h1 : 0 ≤ 4 * r ^ 2 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have h2 : 0 ≤ 4 * r ^ 2 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  have hsq : (2 * r * ‖z - ζ‖) ^ 2 ≤ ‖((4 * r ^ 2 : ℝ) : ℂ) - starRingEnd ℂ ζ * z‖ ^ 2 := by
    nlinarith
  have hle : 2 * r * ‖z - ζ‖ ≤ ‖((4 * r ^ 2 : ℝ) : ℂ) - starRingEnd ℂ ζ * z‖ := by
    nlinarith [norm_nonneg (((4 * r ^ 2 : ℝ) : ℂ) - starRingEnd ℂ ζ * z)]
  rw [blaschkeFactor, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ 2 * r),
    one_le_div hden]
  exact hle

private lemma blaschkeFactor_norm_ge_seven_sixths {r : ℝ} (hr : 0 < r) {ζ z : ℂ}
    (hζ : ‖ζ‖ ≤ r / 2) (hz : ‖z‖ ≤ r) (hne : z ≠ ζ) :
    (7 / 6 : ℝ) ≤ ‖blaschkeFactor r ζ z‖ := by
  have hden : 0 < 2 * r * ‖z - ζ‖ := mul_pos (by linarith) (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hnum_ge : (7 / 2 : ℝ) * r ^ 2 ≤ ‖((4 * r ^ 2 : ℝ) : ℂ) - starRingEnd ℂ ζ * z‖ := by
    have htri := norm_sub_norm_le (((4 * r ^ 2 : ℝ) : ℂ)) (starRingEnd ℂ ζ * z)
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ 4 * r ^ 2),
      norm_mul, Complex.norm_conj] at htri
    have hprod : ‖ζ‖ * ‖z‖ ≤ (r / 2) * r :=
      mul_le_mul hζ hz (norm_nonneg z) (by linarith)
    linarith
  have hden_le : 2 * r * ‖z - ζ‖ ≤ 3 * r ^ 2 := by
    have htri : ‖z - ζ‖ ≤ ‖z‖ + ‖ζ‖ := norm_sub_le z ζ
    nlinarith
  rw [blaschkeFactor, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ 2 * r),
    div_le_div_iff₀ (by norm_num : (0 : ℝ) < 6) hden]
  nlinarith

private lemma blaschkeFactor_norm_le {r : ℝ} (hr : 0 < r) {ζ z : ℂ}
    (hζ : ‖ζ‖ ≤ r) (hz : ‖z‖ ≤ 2 * r) (hne : z ≠ ζ) :
    ‖blaschkeFactor r ζ z‖ ≤ 3 * r / ‖z - ζ‖ := by
  have hnum_le : ‖((4 * r ^ 2 : ℝ) : ℂ) - starRingEnd ℂ ζ * z‖ ≤ 6 * r ^ 2 := by
    calc ‖((4 * r ^ 2 : ℝ) : ℂ) - starRingEnd ℂ ζ * z‖
        ≤ ‖((4 * r ^ 2 : ℝ) : ℂ)‖ + ‖starRingEnd ℂ ζ * z‖ := norm_sub_le _ _
      _ = 4 * r ^ 2 + ‖ζ‖ * ‖z‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_conj]
      _ ≤ 4 * r ^ 2 + r * (2 * r) := by
          exact add_le_add le_rfl (mul_le_mul hζ hz (norm_nonneg z) hr.le)
      _ = 6 * r ^ 2 := by ring
  have hzn : 0 < ‖z - ζ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  rw [blaschkeFactor, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ 2 * r)]
  calc ‖((4 * r ^ 2 : ℝ) : ℂ) - starRingEnd ℂ ζ * z‖ / (2 * r * ‖z - ζ‖)
      ≤ (6 * r ^ 2) / (2 * r * ‖z - ζ‖) := div_le_div_of_nonneg_right hnum_le (by positivity)
    _ = 3 * r / ‖z - ζ‖ := by field_simp; ring

private lemma pow_div_factorial_le_exp {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    x ^ k / (k.factorial : ℝ) ≤ Real.exp x := by
  have hsum := Real.sum_le_exp_of_nonneg hx (k + 1)
  have hmem : k ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_self k)
  exact (Finset.single_le_sum (f := fun i => x ^ i / (i.factorial : ℝ))
    (fun i _ => by positivity) hmem).trans hsum

private lemma prod_div_range_eq (c : ℝ) :
    ∀ m : ℕ, ∏ k ∈ Finset.range m, (c / ((k + 1 : ℕ) : ℝ)) = c ^ m / (m.factorial : ℝ)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.prod_range_succ, prod_div_range_eq c m, pow_succ, Nat.factorial_succ]
    push_cast
    field_simp

private lemma blaschkeProd_le_exp {N : ℕ} (hN : 10 ≤ N) {r η : ℝ} (hr : 0 < r) (hη : 0 < η)
    (hN_log : 2 * Real.log (max 1 (3 * r / η)) ≤ N)
    (ζ : Fin N → ℂ) (hζ_norm : ∀ j : Fin N, ‖ζ j‖ = ((j.val + 1 : ℕ) : ℝ) / N * r)
    {z : ℂ} (hz : ‖z‖ ≤ 2 * r) (hdist : ∀ j : Fin N, η ≤ ‖z - ζ j‖) :
    ‖∏ j : Fin N, blaschkeFactor r (ζ j) z‖ ≤ Real.exp (7 * (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hζ_le : ∀ j : Fin N, ‖ζ j‖ ≤ r := fun j => by
    rw [hζ_norm j]
    have hj : ((j.val + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast j.isLt
    rw [div_mul_eq_mul_div, div_le_iff₀ hNpos]
    nlinarith
  have hne : ∀ j : Fin N, z ≠ ζ j := fun j h => by
    have := hdist j; rw [h, sub_self, norm_zero] at this; linarith
  let j₀ : ℕ := min N ⌊(N : ℝ) * ‖z‖ / r⌋₊
  let A_low : Finset (Fin N) := Finset.univ.filter (fun j : Fin N => j.val + 1 < j₀)
  let A_near : Finset (Fin N) := Finset.univ.filter (fun j : Fin N => j.val + 1 = j₀ ∨ j.val + 1 = j₀ + 1)
  let A_high : Finset (Fin N) := Finset.univ.filter (fun j : Fin N => j₀ + 1 < j.val + 1)
  have hsplit : Finset.univ = (A_low ∪ A_near) ∪ A_high := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff,
      A_low, A_near, A_high]
    omega
  have hdisj1 : Disjoint (A_low ∪ A_near) A_high := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, A_low, A_near, A_high] at h1 h2
    omega
  have hdisj2 : Disjoint A_low A_near := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, A_low, A_near] at h1 h2
    omega
  rw [norm_prod, hsplit, Finset.prod_union hdisj1, Finset.prod_union hdisj2]
  -- Bound on A_near (card ≤ 2)
  have hnear_card : A_near.card ≤ 2 := by
    have hsub : A_near.image Fin.val ⊆ {j₀ - 1, j₀} := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, A_near] at hj
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    calc A_near.card = (A_near.image Fin.val).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ ({j₀ - 1, j₀} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  have hM_ge1 : (1 : ℝ) ≤ max 1 (3 * r / η) := le_max_left _ _
  have hnear_le : ∏ j ∈ A_near, ‖blaschkeFactor r (ζ j) z‖ ≤ Real.exp (N : ℝ) := by
    have hterm : ∀ j ∈ A_near, ‖blaschkeFactor r (ζ j) z‖ ≤ max 1 (3 * r / η) := fun j _ => by
      calc ‖blaschkeFactor r (ζ j) z‖ ≤ 3 * r / ‖z - ζ j‖ :=
            blaschkeFactor_norm_le hr (hζ_le j) hz (hne j)
        _ ≤ 3 * r / η := div_le_div_of_nonneg_left (by positivity) hη (hdist j)
        _ ≤ max 1 (3 * r / η) := le_max_right _ _
    calc ∏ j ∈ A_near, ‖blaschkeFactor r (ζ j) z‖
        ≤ ∏ _j ∈ A_near, max 1 (3 * r / η) :=
          Finset.prod_le_prod (fun j _ => norm_nonneg _) hterm
      _ = (max 1 (3 * r / η)) ^ A_near.card := Finset.prod_const _
      _ ≤ (max 1 (3 * r / η)) ^ 2 := pow_le_pow_right₀ hM_ge1 hnear_card
      _ = Real.exp (2 * Real.log (max 1 (3 * r / η))) := by
          rw [show (2 : ℝ) * Real.log (max 1 (3 * r / η)) = Real.log (max 1 (3 * r / η)) * 2 by ring,
            Real.exp_mul, Real.exp_log (by linarith)]
          norm_cast
      _ ≤ Real.exp (N : ℝ) := Real.exp_le_exp.mpr hN_log
  -- Bound on A_low
  have hj0_le_z : (j₀ : ℝ) / N * r ≤ ‖z‖ := by
    have h1 : (j₀ : ℝ) ≤ (N : ℝ) * ‖z‖ / r := by
      have hle : j₀ ≤ ⌊(N : ℝ) * ‖z‖ / r⌋₊ := Nat.min_le_right _ _
      exact (Nat.cast_le.mpr hle).trans (Nat.floor_le (by positivity))
    rw [div_mul_eq_mul_div, div_le_iff₀ hNpos]
    have h2 : (j₀ : ℝ) * r ≤ (N : ℝ) * ‖z‖ := (le_div_iff₀ hr).mp h1
    linarith
  have hlow_le : ∏ j ∈ A_low, ‖blaschkeFactor r (ζ j) z‖ ≤ Real.exp (3 * (N : ℝ)) := by
    have hterm : ∀ j ∈ A_low, ‖blaschkeFactor r (ζ j) z‖ ≤
        (3 * (N : ℝ)) / ((j₀ - (j.val + 1) : ℕ) : ℝ) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, A_low] at hj
      have hgap_pos : (0 : ℝ) < ((j₀ - (j.val + 1) : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_pos_of_lt hj
      have hdist_ge : ((j₀ - (j.val + 1) : ℕ) : ℝ) / N * r ≤ ‖z - ζ j‖ := by
        have htri : ‖z‖ - ‖ζ j‖ ≤ ‖z - ζ j‖ := norm_sub_norm_le z (ζ j)
        rw [hζ_norm j] at htri
        have hcast : ((j₀ - (j.val + 1) : ℕ) : ℝ) = (j₀ : ℝ) - ((j.val + 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub hj.le]
        rw [hcast, sub_div, sub_mul]
        linarith
      calc ‖blaschkeFactor r (ζ j) z‖ ≤ 3 * r / ‖z - ζ j‖ :=
            blaschkeFactor_norm_le hr (hζ_le j) hz (hne j)
        _ ≤ 3 * r / (((j₀ - (j.val + 1) : ℕ) : ℝ) / N * r) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hdist_ge
        _ = (3 * (N : ℝ)) / ((j₀ - (j.val + 1) : ℕ) : ℝ) := by
            field_simp [hr.ne', hNpos.ne', hgap_pos.ne']
    have h1 := Finset.prod_le_prod (fun j _ => norm_nonneg _) hterm
    -- Map j ↦ j₀ - (j.val + 1) - 1 bijectively onto Finset.range (j₀ - 1)
    have hbij : ∏ j ∈ A_low, ((3 * (N : ℝ)) / ((j₀ - (j.val + 1) : ℕ) : ℝ)) =
        ∏ k ∈ Finset.range (j₀ - 1), ((3 * (N : ℝ)) / ((k + 1 : ℕ) : ℝ)) := by
      refine Finset.prod_nbij (fun j => j₀ - (j.val + 1) - 1) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, A_low] at hj
        simp only [Finset.mem_range]
        omega
      · intro j₁ hj₁ j₂ hj₂ heq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, A_low] at hj₁ hj₂
        dsimp only at heq
        ext; omega
      · intro k hk
        simp only [Finset.mem_coe, Finset.mem_range] at hk
        have hj0N : j₀ ≤ N := Nat.min_le_left _ _
        refine ⟨⟨j₀ - 2 - k, by omega⟩, ?_, ?_⟩
        · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, A_low]
          omega
        · dsimp; omega
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, A_low] at hj
        congr 2
        omega
    rw [hbij, prod_div_range_eq] at h1
    exact h1.trans (pow_div_factorial_le_exp (by positivity) (j₀ - 1))
  -- Bound on A_high
  have hhigh_le : ∏ j ∈ A_high, ‖blaschkeFactor r (ζ j) z‖ ≤ Real.exp (3 * (N : ℝ)) := by
    by_cases hA : A_high.Nonempty
    · obtain ⟨j_ex, hj_ex⟩ := hA
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, A_high] at hj_ex
      have hj0_lt_N : j₀ < N := by omega
      have hj0_eq : j₀ = ⌊(N : ℝ) * ‖z‖ / r⌋₊ := by
        dsimp only [j₀] at hj0_lt_N ⊢
        exact min_eq_right (by omega)
      have hz_lt : ‖z‖ < ((j₀ + 1 : ℕ) : ℝ) / N * r := by
        have hfl : (N : ℝ) * ‖z‖ / r < (j₀ : ℝ) + 1 := by
          rw [hj0_eq]; exact Nat.lt_floor_add_one _
        rw [div_lt_iff₀ hr] at hfl
        rw [div_mul_eq_mul_div, lt_div_iff₀ hNpos]
        push_cast; linarith
      have hterm : ∀ j ∈ A_high, ‖blaschkeFactor r (ζ j) z‖ ≤
          (3 * (N : ℝ)) / ((j.val - j₀ : ℕ) : ℝ) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, A_high] at hj
        have hgap_pos : (0 : ℝ) < ((j.val - j₀ : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < j.val - j₀ by omega)
        have hdist_ge : ((j.val - j₀ : ℕ) : ℝ) / N * r ≤ ‖z - ζ j‖ := by
          have htri : ‖ζ j‖ - ‖z‖ ≤ ‖z - ζ j‖ := by
            rw [norm_sub_rev]; exact norm_sub_norm_le (ζ j) z
          rw [hζ_norm j] at htri
          have hcast : ((j.val - j₀ : ℕ) : ℝ) = ((j.val + 1 : ℕ) : ℝ) - ((j₀ + 1 : ℕ) : ℝ) := by
            have h1 : j.val - j₀ = (j.val + 1) - (j₀ + 1) := by omega
            rw [h1, Nat.cast_sub (by omega)]
          rw [hcast, sub_div, sub_mul]
          linarith
        calc ‖blaschkeFactor r (ζ j) z‖ ≤ 3 * r / ‖z - ζ j‖ :=
              blaschkeFactor_norm_le hr (hζ_le j) hz (hne j)
          _ ≤ 3 * r / (((j.val - j₀ : ℕ) : ℝ) / N * r) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) hdist_ge
          _ = (3 * (N : ℝ)) / ((j.val - j₀ : ℕ) : ℝ) := by
              field_simp [hr.ne', hNpos.ne', hgap_pos.ne']
      have h1 := Finset.prod_le_prod (fun j _ => norm_nonneg _) hterm
      have hbij : ∏ j ∈ A_high, ((3 * (N : ℝ)) / ((j.val - j₀ : ℕ) : ℝ)) =
          ∏ k ∈ Finset.range (N - 1 - j₀), ((3 * (N : ℝ)) / ((k + 1 : ℕ) : ℝ)) := by
        refine Finset.prod_nbij (fun j => j.val - j₀ - 1) ?_ ?_ ?_ ?_
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, A_high] at hj
          simp only [Finset.mem_range]
          omega
        · intro j₁ hj₁ j₂ hj₂ heq
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, A_high] at hj₁ hj₂
          dsimp only at heq
          ext; omega
        · intro k hk
          simp only [Finset.mem_coe, Finset.mem_range] at hk
          refine ⟨⟨j₀ + 1 + k, by omega⟩, ?_, ?_⟩
          · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, A_high]
            omega
          · dsimp; omega
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, A_high] at hj
          congr 2
          omega
      rw [hbij, prod_div_range_eq] at h1
      exact h1.trans (pow_div_factorial_le_exp (by positivity) (N - 1 - j₀))
    · rw [Finset.not_nonempty_iff_eq_empty] at hA
      rw [hA, Finset.prod_empty]
      exact Real.one_le_exp (by positivity)
  calc (∏ j ∈ A_low, ‖blaschkeFactor r (ζ j) z‖) *
        (∏ j ∈ A_near, ‖blaschkeFactor r (ζ j) z‖) *
        (∏ j ∈ A_high, ‖blaschkeFactor r (ζ j) z‖)
      ≤ Real.exp (3 * (N : ℝ)) * Real.exp (N : ℝ) * Real.exp (3 * (N : ℝ)) := by
        have hp1 : 0 ≤ ∏ j ∈ A_low, ‖blaschkeFactor r (ζ j) z‖ :=
          Finset.prod_nonneg (fun _ _ => norm_nonneg _)
        have hp2 : 0 ≤ ∏ j ∈ A_near, ‖blaschkeFactor r (ζ j) z‖ :=
          Finset.prod_nonneg (fun _ _ => norm_nonneg _)
        have hp3 : 0 ≤ ∏ j ∈ A_high, ‖blaschkeFactor r (ζ j) z‖ :=
          Finset.prod_nonneg (fun _ _ => norm_nonneg _)
        exact mul_le_mul (mul_le_mul hlow_le hnear_le hp2 (Real.exp_nonneg _)) hhigh_le hp3
          (by positivity)
    _ = Real.exp (7 * (N : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1; ring

private lemma blaschkeProd_ge {N : ℕ} (hN : 10 ≤ N) {r : ℝ} (hr : 0 < r)
    (ζ : Fin N → ℂ) (hζ_norm : ∀ j : Fin N, ‖ζ j‖ = ((j.val + 1 : ℕ) : ℝ) / N * r)
    {z : ℂ} (hz : ‖z‖ ≤ r) (hne : ∀ j : Fin N, z ≠ ζ j) :
    (7 / 6 : ℝ) ^ (N / 3) ≤ ‖∏ j : Fin N, blaschkeFactor r (ζ j) z‖ := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hζ_le : ∀ j : Fin N, ‖ζ j‖ ≤ r := fun j => by
    rw [hζ_norm j]
    have hj : ((j.val + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast j.isLt
    rw [div_mul_eq_mul_div, div_le_iff₀ hNpos]
    nlinarith
  let S : Finset (Fin N) := Finset.univ.filter (fun j : Fin N => j.val < N / 3)
  have hScard : S.card = N / 3 := by
    have hbij : S.card = (Finset.range (N / 3)).card := by
      refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hj
        exact Finset.mem_range.mpr hj
      · intro j₁ _ j₂ _ h; exact Fin.ext h
      · intro k hk
        rw [Finset.mem_range] at hk
        exact ⟨⟨k, by omega⟩, by simp [S, hk], rfl⟩
    rw [hbij, Finset.card_range]
  rw [norm_prod, ← Finset.prod_mul_prod_compl S]
  have hS_ge : (7 / 6 : ℝ) ^ (N / 3) ≤ ∏ j ∈ S, ‖blaschkeFactor r (ζ j) z‖ := by
    rw [← hScard, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => by norm_num) (fun j hj => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hj
    have hζ_half : ‖ζ j‖ ≤ r / 2 := by
      rw [hζ_norm j]
      have h2 : 2 * (j.val + 1) ≤ N := by omega
      have h2r : 2 * ((j.val + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hNpos (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    exact blaschkeFactor_norm_ge_seven_sixths hr hζ_half hz (hne j)
  have hSc_ge : 1 ≤ ∏ j ∈ Sᶜ, ‖blaschkeFactor r (ζ j) z‖ := by
    rw [← Finset.prod_const_one]
    exact Finset.prod_le_prod (fun _ _ => zero_le_one)
      (fun j _ => blaschkeFactor_norm_ge_one hr (hζ_le j) (by linarith) (hne j))
  calc (7 / 6 : ℝ) ^ (N / 3) = (7 / 6 : ℝ) ^ (N / 3) * 1 := (mul_one _).symm
    _ ≤ (∏ j ∈ S, ‖blaschkeFactor r (ζ j) z‖) * (∏ j ∈ Sᶜ, ‖blaschkeFactor r (ζ j) z‖) :=
        mul_le_mul hS_ge hSc_ge zero_le_one (Finset.prod_nonneg (fun _ _ => norm_nonneg _))

/-!
## Part 5: Superlinear growth on every path component of `{M < ‖h z‖}`
-/

private lemma exp_beats_linear {c a : ℝ} (hc : 1 < c) (ha : 0 < a) (A B : ℝ) :
    ∃ k : ℕ, A + (k : ℝ) * B < a * c ^ k := by
  set ε : ℝ := c - 1
  have hε : 0 < ε := by linarith
  have hquad : ∀ k : ℕ, 1 + (k : ℝ) * ε + ((k * (k - 1) : ℕ) : ℝ) / 2 * ε ^ 2 ≤ c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
      have hc_eq : c = 1 + ε := by dsimp only [ε]; ring
      rw [pow_succ c m]
      have hcm : c ^ m * c = c ^ m * (1 + ε) := by rw [hc_eq]
      rw [hcm]
      have hcast : (((m + 1) * m : ℕ) : ℝ) = ((m * (m - 1) : ℕ) : ℝ) + 2 * (m : ℝ) := by
        cases m with
        | zero => simp
        | succ t =>
          have : (t + 1 + 1) * (t + 1) = (t + 1) * t + 2 * (t + 1) := by ring
          rw [Nat.add_sub_cancel, this]
          push_cast; ring
      have hnonneg : 0 ≤ ((m * (m - 1) : ℕ) : ℝ) / 2 * ε ^ 3 := by positivity
      have hmul := mul_le_mul_of_nonneg_right ih (by linarith : (0 : ℝ) ≤ 1 + ε)
      simp only [Nat.add_sub_cancel] at hcast ⊢
      have hm1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; rfl
      rw [hcast, hm1]
      nlinarith
  let M : ℕ := Nat.ceil (max 0 ((|A| + |B| + 1) / (a * ε ^ 2 / 4))) + 4
  refine ⟨M, ?_⟩
  have hM4 : (4 : ℝ) ≤ M := by
    have : 4 ≤ M := Nat.le_add_left 4 _
    exact_mod_cast this
  have hM_big : (|A| + |B| + 1) / (a * ε ^ 2 / 4) ≤ (M : ℝ) := by
    have h1 : (|A| + |B| + 1) / (a * ε ^ 2 / 4) ≤ max 0 ((|A| + |B| + 1) / (a * ε ^ 2 / 4)) :=
      le_max_right _ _
    have h2 : max 0 ((|A| + |B| + 1) / (a * ε ^ 2 / 4)) ≤
        (Nat.ceil (max 0 ((|A| + |B| + 1) / (a * ε ^ 2 / 4))) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (max 0 ((|A| + |B| + 1) / (a * ε ^ 2 / 4))) : ℝ) ≤ (M : ℝ) := by
      dsimp only [M]; push_cast; linarith
    linarith
  have hden : 0 < a * ε ^ 2 / 4 := by positivity
  have hM_mul : |A| + |B| + 1 ≤ (M : ℝ) * (a * ε ^ 2 / 4) := (div_le_iff₀ hden).mp hM_big
  have hM_sq : (M : ℝ) ^ 2 / 2 ≤ ((M * (M - 1) : ℕ) : ℝ) := by
    have hM1 : 1 ≤ M := by omega
    rw [Nat.cast_mul, Nat.cast_sub hM1, Nat.cast_one]
    nlinarith
  have hq := hquad M
  have h1 : A + (M : ℝ) * B ≤ (|A| + |B|) * (M : ℝ) := by
    have hA : A ≤ |A| := le_abs_self A
    have hB : B ≤ |B| := le_abs_self B
    have hA' : |A| ≤ |A| * (M : ℝ) := le_mul_of_one_le_right (abs_nonneg A) (by linarith)
    nlinarith [abs_nonneg A, abs_nonneg B]
  have h2 : (|A| + |B|) * (M : ℝ) < (M : ℝ) ^ 2 * (a * ε ^ 2 / 4) := by
    nlinarith
  have h3 : (M : ℝ) ^ 2 * (a * ε ^ 2 / 4) ≤ a * (((M * (M - 1) : ℕ) : ℝ) / 2 * ε ^ 2) := by
    nlinarith [sq_nonneg ε]
  have h4 : a * (((M * (M - 1) : ℕ) : ℝ) / 2 * ε ^ 2) ≤ a * c ^ M := by
    have : ((M * (M - 1) : ℕ) : ℝ) / 2 * ε ^ 2 ≤ c ^ M := by
      nlinarith [mul_nonneg (Nat.cast_nonneg M) hε.le]
    exact mul_le_mul_of_nonneg_left this ha.le
  linarith

private lemma blaschke_contraction {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {M : ℝ} (hM : 0 < M)
    {C C' : Set ℂ} (hC_open : IsOpen C) (hC'_open : IsOpen C')
    (hC'_path : IsPathConnected C') (hC'_unbdd : ¬ IsBounded C')
    (hdisj : Disjoint C' C) (h0 : (0 : ℂ) ∈ C')
    (hfront : ∀ w ∈ frontier C, ‖h w‖ = M)
    {r : ℝ} (hr : 0 < r)
    {z_max : ℂ} (hz_max_cl : z_max ∈ closure C) (hz_max_ball : ‖z_max‖ ≤ r)
    {B2 : ℝ} (hB2_gt1 : 1 < B2)
    (hB2_bound : ∀ z ∈ closure C ∩ Metric.closedBall (0 : ℂ) (2 * r), ‖h z‖ / M ≤ B2)
    (hz_max_gt : 1 < ‖h z_max‖ / M) :
    Real.log (‖h z_max‖ / M) ≤ (1 - Real.log (7 / 6) / 28) * Real.log B2 := by
  -- C' is disjoint from closure C
  have hdisj_cl : Disjoint C' (closure C) := by
    rw [Set.disjoint_iff]
    intro w ⟨hw1, hw2⟩
    have hsub : C ⊆ C'ᶜ := hdisj.subset_compl_left
    have hcl : closure C ⊆ C'ᶜ := closure_minimal hsub hC'_open.isClosed_compl
    exact hcl hw2 hw1
  -- Pick w₁ ∈ C' with ‖w₁‖ ≥ r
  have hw1_ex : ∃ w₁ ∈ C', r ≤ ‖w₁‖ := by
    by_contra hall
    push Not at hall
    apply hC'_unbdd
    rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
    exact ⟨r, fun w hw => by simpa [Metric.mem_closedBall] using (hall w hw).le⟩
  obtain ⟨w₁, hw₁C', hw₁_norm⟩ := hw1_ex
  -- Path γ in C' from 0 to w₁
  obtain ⟨γ, hγ_mem⟩ := hC'_path.joinedIn 0 h0 w₁ hw₁C'
  let Kγ : Set ℂ := Set.range γ
  have hKγ_compact : IsCompact Kγ := isCompact_range γ.continuous
  have hKγ_sub : Kγ ⊆ C' := by rintro _ ⟨t, rfl⟩; exact hγ_mem t
  -- Compact set A = closure C ∩ closedBall 0 (2r) is disjoint from Kγ
  let A : Set ℂ := closure C ∩ Metric.closedBall (0 : ℂ) (2 * r)
  have hA_compact : IsCompact A := (isCompact_closedBall (0 : ℂ) (2 * r)).inter_left isClosed_closure
  have hA_nonempty : A.Nonempty := ⟨z_max, hz_max_cl, by simpa [Metric.mem_closedBall] using (by linarith)⟩
  have hKγ_nonempty : Kγ.Nonempty := ⟨0, ⟨0, γ.source⟩⟩
  -- Minimum distance η > 0 between A and Kγ
  obtain ⟨⟨a₀, k₀⟩, ⟨ha₀, hk₀⟩, hmin⟩ :=
    (hA_compact.prod hKγ_compact).exists_isMinOn (hA_nonempty.prod hKγ_nonempty)
      (continuous_fst.sub continuous_snd).norm.continuousOn
  set η : ℝ := ‖a₀ - k₀‖
  have hη : 0 < η := by
    rw [norm_pos_iff, sub_ne_zero]
    intro heq
    rw [heq] at ha₀
    exact Set.disjoint_left.mp hdisj_cl (hKγ_sub hk₀) ha₀.1
  have hdist : ∀ z ∈ A, ∀ w ∈ Kγ, η ≤ ‖z - w‖ := fun z hz w hw =>
    hmin (Set.mk_mem_prod hz hw)
  -- Choose N ≥ 10 with 2 * log (max 1 (3r/η)) ≤ N
  let N : ℕ := max 10 (Nat.ceil (2 * Real.log (max 1 (3 * r / η))) + 1)
  have hN10 : 10 ≤ N := le_max_left _ _
  have hN_log : 2 * Real.log (max 1 (3 * r / η)) ≤ (N : ℝ) := by
    have h1 : 2 * Real.log (max 1 (3 * r / η)) ≤
        (Nat.ceil (2 * Real.log (max 1 (3 * r / η))) : ℝ) := Nat.le_ceil _
    have h2 : Nat.ceil (2 * Real.log (max 1 (3 * r / η))) ≤ N :=
      (Nat.le_succ _).trans (le_max_right _ _)
    exact h1.trans (Nat.cast_le.mpr h2)
  have hNpos : (0 : ℝ) < N := by positivity
  -- Pick ζ j ∈ Kγ with ‖ζ j‖ = (j + 1) / N * r via IVT
  have hζ_ex : ∀ j : Fin N, ∃ ζ ∈ Kγ, ‖ζ‖ = ((j.val + 1 : ℕ) : ℝ) / N * r := by
    intro j
    let s : ℝ := ((j.val + 1 : ℕ) : ℝ) / N * r
    have hs0 : 0 ≤ s := by positivity
    have hsr : s ≤ r := by
      have hj : ((j.val + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast j.isLt
      dsimp only [s]; rw [div_mul_eq_mul_div, div_le_iff₀ hNpos]; nlinarith
    have hcont : ContinuousOn (fun t : ℝ => ‖γ (Set.projIcc 0 1 zero_le_one t)‖) (Set.Icc 0 1) :=
      (γ.continuous.comp continuous_projIcc).norm.continuousOn
    have hv0 : ‖γ (Set.projIcc 0 1 zero_le_one (0 : ℝ))‖ = 0 := by
      have : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := by ext; simp
      rw [this, γ.source, norm_zero]
    have hv1 : r ≤ ‖γ (Set.projIcc 0 1 zero_le_one (1 : ℝ))‖ := by
      have : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = 1 := by ext; simp
      rw [this, γ.target]; exact hw₁_norm
    have hmem : s ∈ Set.Icc (‖γ (Set.projIcc 0 1 zero_le_one (0 : ℝ))‖)
        (‖γ (Set.projIcc 0 1 zero_le_one (1 : ℝ))‖) :=
      ⟨by linarith, by linarith⟩
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (zero_le_one : (0 : ℝ) ≤ 1) hcont hmem
    exact ⟨γ (Set.projIcc 0 1 zero_le_one t), ⟨Set.projIcc 0 1 zero_le_one t, rfl⟩, ht⟩
  choose ζ hζK hζ_norm using hζ_ex
  -- Define Blaschke product P
  let P : ℂ → ℂ := fun z => ∏ j : Fin N, blaschkeFactor r (ζ j) z
  have hP_diff : DifferentiableOn ℂ P A := by
    intro z hz
    have hprod_diff : DifferentiableAt ℂ P z := by
      dsimp only [P]
      have hfac : ∀ j : Fin N, DifferentiableAt ℂ (fun w => blaschkeFactor r (ζ j) w) z := by
        intro j
        dsimp only [blaschkeFactor]
        refine DifferentiableAt.div ?_ ?_ ?_
        · exact (differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)
        · exact (differentiableAt_const _).mul (differentiableAt_id.sub (differentiableAt_const _))
        · have hne : z ≠ ζ j := by
            intro heq
            have := hdist z hz (ζ j) (hζK j)
            rw [heq, sub_self, norm_zero] at this; linarith
          exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith)) (sub_ne_zero.mpr hne)
      have hgen : ∀ s : Finset (Fin N),
          DifferentiableAt ℂ (fun w => ∏ j ∈ s, blaschkeFactor r (ζ j) w) z := by
        intro s
        induction s using Finset.cons_induction with
        | empty =>
          simp only [Finset.prod_empty]
          exact differentiableAt_const (1 : ℂ)
        | cons a s ha ih =>
          have hmul : DifferentiableAt ℂ
              (fun w => blaschkeFactor r (ζ a) w * ∏ j ∈ s, blaschkeFactor r (ζ j) w) z :=
            (hfac a).mul ih
          have heq : (fun w => ∏ j ∈ Finset.cons a s ha, blaschkeFactor r (ζ j) w) =
              (fun w => blaschkeFactor r (ζ a) w * ∏ j ∈ s, blaschkeFactor r (ζ j) w) := by
            funext w
            exact Finset.prod_cons (s := s) (a := a) (h := ha) (f := fun j => blaschkeFactor r (ζ j) w)
          rw [heq]
          exact hmul
      exact hgen Finset.univ
    exact hprod_diff.differentiableWithinAt
  -- Domain U = C ∩ ball 0 (2r)
  let U : Set ℂ := C ∩ Metric.ball (0 : ℂ) (2 * r)
  have hU_bdd : IsBounded U := isBounded_ball.subset Set.inter_subset_right
  have hU_cl_sub : closure U ⊆ A := by
    refine closure_minimal ?_ (isClosed_closure.inter isClosed_closedBall)
    exact Set.inter_subset_inter subset_closure Metric.ball_subset_closedBall
  have hP_dcc : DiffContOnCl ℂ P U :=
    ⟨hP_diff.mono (subset_closure.trans hU_cl_sub), (hP_diff.continuousOn).mono hU_cl_sub⟩
  have hU_front_sub : frontier U ⊆
      (frontier C ∩ Metric.closedBall (0 : ℂ) (2 * r)) ∪
      (closure C ∩ Metric.sphere (0 : ℂ) (2 * r)) := by
    calc frontier U
        ⊆ (frontier C ∩ closure (Metric.ball (0 : ℂ) (2 * r))) ∪
          (closure C ∩ frontier (Metric.ball (0 : ℂ) (2 * r))) :=
            frontier_inter_subset C (Metric.ball (0 : ℂ) (2 * r))
      _ ⊆ (frontier C ∩ Metric.closedBall (0 : ℂ) (2 * r)) ∪
          (closure C ∩ Metric.sphere (0 : ℂ) (2 * r)) := by
        refine Set.union_subset_union
          (Set.inter_subset_inter_right _ closure_ball_subset_closedBall)
          (Set.inter_subset_inter_right _ (frontier_ball_subset_sphere))
  -- z_max ∈ closure U because closedBall 0 r ⊆ ball 0 (2r) (open)
  have hz_max_clU : z_max ∈ closure U := by
    have hz_ball2 : z_max ∈ Metric.ball (0 : ℂ) (2 * r) := by
      simp only [Metric.mem_ball, dist_zero_right]; linarith
    rw [_root_.mem_closure_iff]
    intro O hO hzO
    have hO' : IsOpen (O ∩ Metric.ball (0 : ℂ) (2 * r)) := hO.inter isOpen_ball
    obtain ⟨y, ⟨hyO, hyB⟩, hyC⟩ := _root_.mem_closure_iff.mp hz_max_cl _ hO' ⟨hzO, hz_ball2⟩
    exact ⟨y, hyO, hyC, hyB⟩
  -- For every q ≥ 1, apply maximum modulus to (h(z)/M)^q * P(z)^p
  have hlogB2_pos : 0 < Real.log B2 := Real.log_pos hB2_gt1
  have hstep_q : ∀ q : ℕ, 1 ≤ q →
      Real.log (‖h z_max‖ / M) +
        ((Real.log B2 / (7 * (N : ℝ)) - 1 / (q : ℝ)) * ((N / 3 : ℕ) : ℝ) * Real.log (7 / 6)) ≤
      Real.log B2 := by
    intro q hq
    have hqpos : (0 : ℝ) < q := by positivity
    let p : ℕ := ⌊(q : ℝ) * Real.log B2 / (7 * (N : ℝ))⌋₊
    have hp_le : (p : ℝ) * (7 * (N : ℝ)) ≤ (q : ℝ) * Real.log B2 := by
      have hfl := Nat.floor_le (show (0 : ℝ) ≤ (q : ℝ) * Real.log B2 / (7 * (N : ℝ)) by positivity)
      exact (le_div_iff₀ (by positivity : (0 : ℝ) < 7 * (N : ℝ))).mp hfl
    have hp_gt : (q : ℝ) * Real.log B2 / (7 * (N : ℝ)) - 1 < (p : ℝ) := by
      have hfl := Nat.lt_floor_add_one ((q : ℝ) * Real.log B2 / (7 * (N : ℝ)))
      linarith
    let F : ℂ → ℂ := fun z => (h z / (M : ℂ)) ^ q * P z ^ p
    have hF_dcc : DiffContOnCl ℂ F U :=
      ⟨(((hh.div_const (M : ℂ)).pow q).differentiableOn).mul (hP_dcc.1.pow p),
       (((hh.div_const (M : ℂ)).pow q).continuous.continuousOn).mul (hP_dcc.2.pow p)⟩
    have hF_front : ∀ w ∈ frontier U, ‖F w‖ ≤ B2 ^ q := by
      intro w hw
      have hwA : w ∈ A := hU_cl_sub (frontier_subset_closure hw)
      have hwnorm : ‖w‖ ≤ 2 * r := by simpa [Metric.mem_closedBall] using hwA.2
      have hwdist : ∀ j : Fin N, η ≤ ‖w - ζ j‖ := fun j => hdist w hwA (ζ j) (hζK j)
      have hne_w : ∀ j : Fin N, w ≠ ζ j := fun j h => by
        have := hwdist j; rw [h, sub_self, norm_zero] at this; linarith
      rcases hU_front_sub hw with ⟨hwfC, _⟩ | ⟨_, hwsph⟩
      · -- On frontier C: ‖h w‖ = M and ‖P w‖ ≤ exp (7 * N)
        have hhw : ‖h w / (M : ℂ)‖ = 1 := by
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hM.le, hfront w hwfC, div_self hM.ne']
        have hPw : ‖P w‖ ≤ Real.exp (7 * (N : ℝ)) :=
          blaschkeProd_le_exp hN10 hr hη hN_log ζ hζ_norm hwnorm hwdist
        have hFnorm : ‖F w‖ = ‖h w / (M : ℂ)‖ ^ q * ‖P w‖ ^ p := by
          simp only [F, norm_mul, norm_pow]
        rw [hFnorm, hhw, one_pow, one_mul]
        calc ‖P w‖ ^ p ≤ (Real.exp (7 * (N : ℝ))) ^ p :=
              pow_le_pow_left₀ (norm_nonneg _) hPw p
          _ = Real.exp ((p : ℝ) * (7 * (N : ℝ))) := by
              rw [← Real.exp_nat_mul]
          _ ≤ Real.exp ((q : ℝ) * Real.log B2) := Real.exp_le_exp.mpr hp_le
          _ = B2 ^ q := by
              rw [mul_comm, Real.exp_mul, Real.exp_log (by linarith)]
              norm_cast
      · -- On sphere 0 (2r): ‖h w‖ / M ≤ B2 and ‖P w‖ = 1
        have hws : ‖w‖ = 2 * r := by simpa [Metric.mem_sphere] using hwsph
        have hPw : ‖P w‖ = 1 := by
          dsimp only [P]
          rw [norm_prod]
          exact Finset.prod_eq_one (fun j _ => blaschkeFactor_norm_eq_one hr hws (hne_w j))
        have hhw : ‖h w / (M : ℂ)‖ ≤ B2 := by
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hM.le]
          exact hB2_bound w hwA
        have hFnorm : ‖F w‖ = ‖h w / (M : ℂ)‖ ^ q * ‖P w‖ ^ p := by
          simp only [F, norm_mul, norm_pow]
        rw [hFnorm, hPw, one_pow, mul_one]
        exact pow_le_pow_left₀ (norm_nonneg _) hhw q
    have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le hU_bdd hF_dcc hF_front hz_max_clU
    -- Lower bound ‖F z_max‖
    have hzA : z_max ∈ A := hU_cl_sub hz_max_clU
    have hne_z : ∀ j : Fin N, z_max ≠ ζ j := fun j h => by
      have := hdist z_max hzA (ζ j) (hζK j)
      rw [h, sub_self, norm_zero] at this; linarith
    have hPz_ge : (7 / 6 : ℝ) ^ (N / 3) ≤ ‖P z_max‖ :=
      blaschkeProd_ge hN10 hr ζ hζ_norm hz_max_ball hne_z
    have hFz_ge : (‖h z_max‖ / M) ^ q * ((7 / 6 : ℝ) ^ (N / 3)) ^ p ≤ ‖F z_max‖ := by
      have hFnorm : ‖F z_max‖ = (‖h z_max‖ / M) ^ q * ‖P z_max‖ ^ p := by
        simp only [F, norm_mul, norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg hM.le]
      rw [hFnorm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hPz_ge p) (by positivity)
    have hcomb : (‖h z_max‖ / M) ^ q * ((7 / 6 : ℝ) ^ (N / 3)) ^ p ≤ B2 ^ q := hFz_ge.trans hmax
    have hlog_le : Real.log ((‖h z_max‖ / M) ^ q * ((7 / 6 : ℝ) ^ (N / 3)) ^ p) ≤ Real.log (B2 ^ q) :=
      Real.log_le_log (by positivity) hcomb
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow] at hlog_le
    have hlog76_pos : 0 < Real.log (7 / 6 : ℝ) := Real.log_pos (by norm_num)
    have hdiv : Real.log (‖h z_max‖ / M) + ((p : ℝ) / (q : ℝ)) * ((N / 3 : ℕ) : ℝ) * Real.log (7 / 6) ≤
        Real.log B2 := by
      have h1 : (q : ℝ) * (Real.log (‖h z_max‖ / M) +
          ((p : ℝ) / (q : ℝ)) * ((N / 3 : ℕ) : ℝ) * Real.log (7 / 6)) ≤ (q : ℝ) * Real.log B2 := by
        have heq : (q : ℝ) * (Real.log (‖h z_max‖ / M) +
            ((p : ℝ) / (q : ℝ)) * ((N / 3 : ℕ) : ℝ) * Real.log (7 / 6)) =
            (q : ℝ) * Real.log (‖h z_max‖ / M) + (p : ℝ) * (((N / 3 : ℕ) : ℝ) * Real.log (7 / 6)) := by
          field_simp [hqpos.ne']
        rw [heq]
        exact hlog_le
      exact le_of_mul_le_mul_left h1 hqpos
    have hpq : Real.log B2 / (7 * (N : ℝ)) - 1 / (q : ℝ) ≤ (p : ℝ) / (q : ℝ) := by
      rw [le_div_iff₀ hqpos, sub_mul, one_div_mul_cancel hqpos.ne']
      have : (Real.log B2 / (7 * (N : ℝ))) * (q : ℝ) = (q : ℝ) * Real.log B2 / (7 * (N : ℝ)) := by ring
      linarith
    have hcoeff_nn : 0 ≤ ((N / 3 : ℕ) : ℝ) * Real.log (7 / 6) := by positivity
    nlinarith
  -- Let q → ∞ via le_of_forall_pos_le_add
  have hN3_ge : (N : ℝ) / 4 ≤ ((N / 3 : ℕ) : ℝ) := by
    have h1 : N ≤ 4 * (N / 3) := by omega
    have h2 : (N : ℝ) ≤ 4 * ((N / 3 : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hlog76_pos : 0 < Real.log (7 / 6 : ℝ) := Real.log_pos (by norm_num)
  have hlim : Real.log (‖h z_max‖ / M) +
      (Real.log B2 / (7 * (N : ℝ))) * ((N / 3 : ℕ) : ℝ) * Real.log (7 / 6) ≤ Real.log B2 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    let q : ℕ := max 1 (Nat.ceil (((N / 3 : ℕ) : ℝ) * Real.log (7 / 6) / ε) + 1)
    have hq1 : 1 ≤ q := le_max_left _ _
    have hqpos : (0 : ℝ) < q := by positivity
    have hq_big : ((N / 3 : ℕ) : ℝ) * Real.log (7 / 6) / (q : ℝ) ≤ ε := by
      rw [div_le_iff₀ hqpos]
      have h1 : ((N / 3 : ℕ) : ℝ) * Real.log (7 / 6) / ε ≤ (q : ℝ) := by
        have ha := Nat.le_ceil (((N / 3 : ℕ) : ℝ) * Real.log (7 / 6) / ε)
        have hb : Nat.ceil (((N / 3 : ℕ) : ℝ) * Real.log (7 / 6) / ε) ≤ q :=
          (Nat.le_succ _).trans (le_max_right _ _)
        exact ha.trans (Nat.cast_le.mpr hb)
      have h2 := (div_le_iff₀ hε).mp h1
      linarith
    have hsq := hstep_q q hq1
    have hexp : (Real.log B2 / (7 * (N : ℝ)) - 1 / (q : ℝ)) * ((N / 3 : ℕ) : ℝ) * Real.log (7 / 6) =
        (Real.log B2 / (7 * (N : ℝ))) * ((N / 3 : ℕ) : ℝ) * Real.log (7 / 6) -
        ((N / 3 : ℕ) : ℝ) * Real.log (7 / 6) / (q : ℝ) := by ring
    linarith
  have hfrac : Real.log (7 / 6) / 28 * Real.log B2 ≤
      (Real.log B2 / (7 * (N : ℝ))) * ((N / 3 : ℕ) : ℝ) * Real.log (7 / 6) := by
    have h1 : Real.log (7 / 6) / 28 * Real.log B2 =
        (Real.log B2 / (7 * (N : ℝ))) * ((N : ℝ) / 4) * Real.log (7 / 6) := by
      field_simp [hNpos.ne']; ring
    rw [h1]
    have hfac1 : 0 ≤ Real.log B2 / (7 * (N : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN3_ge hfac1) hlog76_pos.le
  linarith

private lemma exists_gt_linear_on_pathComponentIn {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (htrans : ∀ p : ℂ[X], h ≠ fun z => p.eval z)
    {M : ℝ} (hM : 0 < M) {z₀ : ℂ} (hz₀ : M < ‖h z₀‖) (K : ℝ) :
    ∃ z ∈ pathComponentIn {w : ℂ | M < ‖h w‖} z₀, K * (1 + ‖z‖) < ‖h z‖ := by
  set V : Set ℂ := {w : ℂ | M < ‖h w‖}
  set C : Set ℂ := pathComponentIn V z₀
  by_contra hno
  push Not at hno
  have hK_nn : 0 ≤ max K 0 := le_max_right _ _
  -- Case 1: V ⊆ C -> global linear bound -> polynomial -> contradiction
  by_cases hVC : V ⊆ C
  · have hglob : ∃ K' : ℝ, 0 ≤ K' ∧ ∀ z : ℂ, ‖h z‖ ≤ K' * (1 + ‖z‖) ^ 1 := by
      refine ⟨max K 0 + M, by positivity, fun z => ?_⟩
      rw [pow_one]
      by_cases hzV : z ∈ V
      · have h1 := hno z (hVC hzV)
        have h2 : K * (1 + ‖z‖) ≤ max K 0 * (1 + ‖z‖) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        have h3 : 0 ≤ M * (1 + ‖z‖) := by positivity
        linarith
      · have h1 : ‖h z‖ ≤ M := by simpa [V] using hzV
        nlinarith [norm_nonneg z]
    obtain ⟨p, hp⟩ := isPoly_of_norm_le_pow 1 h hh hglob
    exact htrans p hp
  · -- Case 2: ∃ w₀ ∈ V \ C -> shifted Blaschke contraction -> contradiction
    rw [Set.not_subset] at hVC
    obtain ⟨w₀, hw₀V, hw₀nC⟩ := hVC
    set C' : Set ℂ := pathComponentIn V w₀
    have hV_open : IsOpen V := superlevel_isOpen hh M
    have hC_open : IsOpen C := hV_open.pathComponentIn z₀
    have hC'_open : IsOpen C' := hV_open.pathComponentIn w₀
    have hC'_path : IsPathConnected C' := isPathConnected_pathComponentIn hw₀V
    have hC'_unbdd : ¬ IsBounded C' := not_isBounded_pathComponentIn hh M hw₀V
    have hdisj : Disjoint C' C := by
      rw [Set.disjoint_left]
      intro y hyC' hyC
      exact hw₀nC (hyC.trans hyC'.symm)
    -- Shift by w₀: ht(z) = h(z + w₀)
    let ht : ℂ → ℂ := fun z => h (z + w₀)
    let Ct : Set ℂ := (fun z => z + w₀) ⁻¹' C
    let Ct' : Set ℂ := (fun z => z + w₀) ⁻¹' C'
    have hht : Differentiable ℂ ht := hh.comp (differentiable_id.add_const w₀)
    have hshift_cont : Continuous (fun z : ℂ => z + w₀) := continuous_id.add continuous_const
    let hshift_homeo : Homeomorph ℂ ℂ := Homeomorph.addRight w₀
    have hCt_open : IsOpen Ct := hC_open.preimage hshift_cont
    have hCt'_open : IsOpen Ct' := hC'_open.preimage hshift_cont
    have hCt'_path : IsPathConnected Ct' := by
      have heq : Ct' = hshift_homeo.symm '' C' := by
        ext z
        simp only [Ct', hshift_homeo, Set.mem_preimage, Set.mem_image, Homeomorph.addRight_symm,
          Homeomorph.coe_addRight]
        constructor
        · intro hz; exact ⟨z + w₀, hz, by ring⟩
        · rintro ⟨x, hx, rfl⟩; simpa using hx
      rw [heq]
      exact hC'_path.image hshift_homeo.symm.continuous
    have hCt'_unbdd : ¬ IsBounded Ct' := by
      intro hb
      apply hC'_unbdd
      have heq : C' = (fun z => z + w₀) '' Ct' := by
        ext w; simp [Ct']
      rw [heq]
      obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall (0 : ℂ) |>.mp hb
      rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
      refine ⟨R + ‖w₀‖, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      simp only [Metric.mem_closedBall, dist_zero_right] at hR ⊢
      have hzn : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall] using hR hz
      exact (norm_add_le z w₀).trans (add_le_add hzn le_rfl)
    have hdisjt : Disjoint Ct' Ct := hdisj.preimage (fun z => z + w₀)
    have h0t : (0 : ℂ) ∈ Ct' := by
      change (0 : ℂ) + w₀ ∈ C'
      rw [zero_add]
      exact mem_pathComponentIn_self hw₀V
    have hfrontt : ∀ w ∈ frontier Ct, ‖ht w‖ = M := by
      intro w hw
      have hwf : w + w₀ ∈ frontier C := by
        have h := hshift_homeo.preimage_frontier C
        have hw' : w ∈ hshift_homeo ⁻¹' frontier C := by
          rw [h]
          exact hw
        exact hw'
      exact norm_eq_of_mem_frontier_pathComponentIn hh M hz₀ hwf
    -- Linear growth on closure Ct
    let K' : ℝ := max K 0 * (1 + ‖w₀‖)
    have hK'_nn : 0 ≤ K' := by positivity
    have hlin_cl : ∀ z ∈ closure Ct, ‖ht z‖ ≤ K' * (1 + ‖z‖) := by
      have hsub : Ct ⊆ {z : ℂ | ‖ht z‖ ≤ K' * (1 + ‖z‖)} := fun z hz => by
        have h1 : ‖h (z + w₀)‖ ≤ K * (1 + ‖z + w₀‖) := hno (z + w₀) hz
        have h2 : K * (1 + ‖z + w₀‖) ≤ max K 0 * (1 + ‖z + w₀‖) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        have h3 : 1 + ‖z + w₀‖ ≤ (1 + ‖w₀‖) * (1 + ‖z‖) := by
          have := norm_add_le z w₀
          nlinarith [norm_nonneg z, norm_nonneg w₀]
        calc ‖ht z‖ = ‖h (z + w₀)‖ := rfl
          _ ≤ max K 0 * (1 + ‖z + w₀‖) := h1.trans h2
          _ ≤ max K 0 * ((1 + ‖w₀‖) * (1 + ‖z‖)) := mul_le_mul_of_nonneg_left h3 hK_nn
          _ = K' * (1 + ‖z‖) := by dsimp only [K']; ring
      have hcl : IsClosed {z : ℂ | ‖ht z‖ ≤ K' * (1 + ‖z‖)} :=
        isClosed_le hht.continuous.norm (continuous_const.mul (continuous_const.add continuous_norm))
      exact closure_minimal hsub hcl
    -- Initial point zt₀ = z₀ - w₀ ∈ Ct
    set zt₀ : ℂ := z₀ - w₀
    have hzt₀Ct : zt₀ ∈ Ct := by
      change z₀ - w₀ + w₀ ∈ C
      rw [sub_add_cancel]
      exact mem_pathComponentIn_self hz₀
    have hzt₀_ne : zt₀ ≠ 0 := by
      intro h0
      rw [h0] at hzt₀Ct
      exact Set.disjoint_left.mp hdisjt h0t hzt₀Ct
    set r₀ : ℝ := ‖zt₀‖
    have hr₀ : 0 < r₀ := norm_pos_iff.mpr hzt₀_ne
    -- Define B(r) = max_{z ∈ closure Ct ∩ closedBall 0 r} ‖ht z‖ / M for r ≥ r₀
    have hmax_ex : ∀ r : ℝ, r₀ ≤ r →
        ∃ z ∈ closure Ct ∩ Metric.closedBall (0 : ℂ) r,
          IsMaxOn (fun w => ‖ht w‖ / M) (closure Ct ∩ Metric.closedBall (0 : ℂ) r) z := by
      intro r hr
      have hcomp : IsCompact (closure Ct ∩ Metric.closedBall (0 : ℂ) r) :=
        (isCompact_closedBall 0 r).inter_left isClosed_closure
      have hne : (closure Ct ∩ Metric.closedBall (0 : ℂ) r).Nonempty :=
        ⟨zt₀, subset_closure hzt₀Ct, by simpa [Metric.mem_closedBall, r₀] using hr⟩
      exact hcomp.exists_isMaxOn hne (hht.continuous.norm.div_const M).continuousOn
    -- Define zmax(k) and B(k) at radius 2^k * r₀
    have hzk_ex : ∀ k : ℕ, ∃ z ∈ closure Ct ∩ Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ k * r₀),
        IsMaxOn (fun w => ‖ht w‖ / M) (closure Ct ∩ Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ k * r₀)) z :=
      fun k => hmax_ex ((2 : ℝ) ^ k * r₀) (by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
        nlinarith)
    choose zk hzk_mem hzk_max using hzk_ex
    let Bk : ℕ → ℝ := fun k => ‖ht (zk k)‖ / M
    have hB0_gt1 : 1 < Bk 0 := by
      have hz0_mem : zt₀ ∈ closure Ct ∩ Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ 0 * r₀) :=
        ⟨subset_closure hzt₀Ct, by simp [Metric.mem_closedBall, r₀]⟩
      have hge := hzk_max 0 hz0_mem
      have hval : 1 < ‖ht zt₀‖ / M := by
        rw [one_lt_div hM]
        change M < ‖h (z₀ - w₀ + w₀)‖
        rw [sub_add_cancel]; exact hz₀
      exact hval.trans_le hge
    have hBk_mono : ∀ k : ℕ, Bk k ≤ Bk (k + 1) := fun k => by
      have hsub : closure Ct ∩ Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ k * r₀) ⊆
          closure Ct ∩ Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1) * r₀) := by
        refine Set.inter_subset_inter_right _ (Metric.closedBall_subset_closedBall ?_)
        rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
      exact hzk_max (k + 1) (hsub (hzk_mem k))
    have hBk_gt1 : ∀ k : ℕ, 1 < Bk k := fun k => by
      induction k with
      | zero => exact hB0_gt1
      | succ m ih => exact ih.trans_le (hBk_mono m)
    -- Contraction at every step k
    set δ : ℝ := Real.log (7 / 6) / 28
    have hδ_pos : 0 < δ := div_pos (Real.log_pos (by norm_num)) (by norm_num)
    have hδ_lt1 : δ < 1 := by
      have h1 : Real.log (7 / 6 : ℝ) ≤ 7 / 6 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      dsimp only [δ]; linarith
    have hstep : ∀ k : ℕ, Real.log (Bk k) ≤ (1 - δ) * Real.log (Bk (k + 1)) := by
      intro k
      have hrk : 0 < (2 : ℝ) ^ k * r₀ := by positivity
      have hr2 : 2 * ((2 : ℝ) ^ k * r₀) = (2 : ℝ) ^ (k + 1) * r₀ := by rw [pow_succ]; ring
      have hbd2 : ∀ z ∈ closure Ct ∩ Metric.closedBall (0 : ℂ) (2 * ((2 : ℝ) ^ k * r₀)),
          ‖ht z‖ / M ≤ Bk (k + 1) := by
        intro z hz; rw [hr2] at hz; exact hzk_max (k + 1) hz
      exact blaschke_contraction hht hM hCt_open hCt'_open hCt'_path hCt'_unbdd hdisjt h0t hfrontt
        hrk (hzk_mem k).1 (by simpa [Metric.mem_closedBall] using (hzk_mem k).2)
        (hBk_gt1 (k + 1)) hbd2 (hBk_gt1 k)
    -- Exponential lower bound on log (Bk k)
    set c : ℝ := (1 - δ)⁻¹
    have hc_gt1 : 1 < c := one_lt_inv_iff₀.mpr ⟨by linarith, by linarith⟩
    have hlog_ge : ∀ k : ℕ, Real.log (Bk 0) * c ^ k ≤ Real.log (Bk k) := by
      intro k
      induction k with
      | zero => simp
      | succ m ih =>
        have hst := hstep m
        have h1 : Real.log (Bk m) * c ≤ Real.log (Bk (m + 1)) := by
          have hpos : 0 < 1 - δ := by linarith
          rw [show c = (1 - δ)⁻¹ from rfl, ← div_eq_mul_inv, div_le_iff₀ hpos]
          linarith
        calc Real.log (Bk 0) * c ^ (m + 1) = (Real.log (Bk 0) * c ^ m) * c := by rw [pow_succ]; ring
          _ ≤ Real.log (Bk m) * c := mul_le_mul_of_nonneg_right ih (by linarith)
          _ ≤ Real.log (Bk (m + 1)) := h1
    -- Linear upper bound on log (Bk k) from linear growth of h̃
    have hlog_le : ∀ k : ℕ, Real.log (Bk k) ≤
        Real.log (max 1 (K' * (1 + r₀) / M)) + (k : ℝ) * Real.log 2 := by
      intro k
      have hzk_norm : ‖zk k‖ ≤ (2 : ℝ) ^ k * r₀ := by
        simpa [Metric.mem_closedBall] using (hzk_mem k).2
      have h2k_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have hlin := hlin_cl (zk k) (hzk_mem k).1
      have hBk_le : Bk k ≤ max 1 (K' * (1 + r₀) / M) * (2 : ℝ) ^ k := by
        have h1 : 1 + ‖zk k‖ ≤ (1 + r₀) * (2 : ℝ) ^ k := by nlinarith
        have h2 : K' * (1 + ‖zk k‖) / M ≤ (K' * (1 + r₀) / M) * (2 : ℝ) ^ k := by
          rw [show (K' * (1 + r₀) / M) * (2 : ℝ) ^ k = K' * ((1 + r₀) * (2 : ℝ) ^ k) / M by ring]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hK'_nn) hM.le
        have h3 : (K' * (1 + r₀) / M) * (2 : ℝ) ^ k ≤ max 1 (K' * (1 + r₀) / M) * (2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        have h0 : Bk k ≤ K' * (1 + ‖zk k‖) / M := div_le_div_of_nonneg_right hlin hM.le
        linarith
      calc Real.log (Bk k) ≤ Real.log (max 1 (K' * (1 + r₀) / M) * (2 : ℝ) ^ k) :=
            Real.log_le_log (by linarith [hBk_gt1 k]) hBk_le
        _ = Real.log (max 1 (K' * (1 + r₀) / M)) + (k : ℝ) * Real.log 2 := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    obtain ⟨k, hk⟩ := exp_beats_linear hc_gt1 (Real.log_pos hB0_gt1)
      (Real.log (max 1 (K' * (1 + r₀) / M))) (Real.log 2)
    linarith [hlog_ge k, hlog_le k]

/-!
## Part 6: Nested path components and gluing the continuous path `γ : ℝ → ℂ`
-/

private lemma exists_closedBall_sup {h : ℂ → ℂ} (hh : Differentiable ℂ h) (R : ℝ) (hR : 0 ≤ R) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ z : ℂ, ‖z‖ ≤ R → ‖h z‖ ≤ S := by
  obtain ⟨w, _, hw⟩ := (isCompact_closedBall (0 : ℂ) R).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self hR⟩ hh.continuous.norm.continuousOn
  exact ⟨max 0 ‖h w‖, le_max_left _ _, fun z hz =>
    (hw (by simpa [Metric.mem_closedBall] using hz)).trans (le_max_right _ _)⟩

private structure Stage (f : ℂ → ℂ) (n : ℕ) where
  R : ℝ
  M : ℝ
  z : ℂ
  hR : (n : ℝ) + 1 ≤ R
  hM_pos : 0 < M
  hM_ball : ∀ w : ℂ, ‖w‖ ≤ R → ‖shiftDiv f n w‖ ≤ M
  hM_grow : ∀ w : ℂ, 1 ≤ ‖w‖ → M < ‖shiftDiv f n w‖ → (n : ℝ) + 1 < ‖f w / w ^ n‖
  hz : M < ‖shiftDiv f n z‖

private noncomputable def buildStages {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ∀ p : ℂ[X], f ≠ fun z => p.eval z) :
    (n : ℕ) → { _s : Stage f n // True }
  | 0 =>
    let hS := exists_closedBall_sup hf 1 zero_le_one
    let S := Classical.choose hS
    let hS_spec := Classical.choose_spec hS
    let hB := shiftDiv_approx f 0
    let B := Classical.choose hB
    let hB_spec := Classical.choose_spec hB
    let M := max S (B + 1) + 1
    have hM_pos : 0 < M := by
      dsimp only [M]; linarith [le_max_left S (B + 1), hS_spec.1]
    have hne := superlevel_nonempty hf htrans M
    let z := Classical.choose hne
    let hz := Classical.choose_spec hne
    ⟨{ R := 1
       M := M
       z := z
       hR := by norm_num
       hM_pos := hM_pos
       hM_ball := fun w hw => by
         dsimp only [shiftDiv, M]
         linarith [hS_spec.2 w hw, le_max_left S (B + 1)]
       hM_grow := fun w hw hgt => by
         have ha := hB_spec.2 w hw
         dsimp only [M] at hgt
         linarith [le_max_right S (B + 1)]
       hz := hz }, trivial⟩
  | n + 1 =>
    let prev := (buildStages hf htrans n).1
    let R₁ : ℝ := max (prev.R + 1) ((n + 1 : ℕ) + 1)
    have hR₁_ge : ((n + 1 : ℕ) : ℝ) + 1 ≤ R₁ := le_max_right _ _
    have hR₁_nn : 0 ≤ R₁ := by positivity
    let hS := exists_closedBall_sup (shiftDiv_differentiable hf (n + 1)) R₁ hR₁_nn
    let S := Classical.choose hS
    let hS_spec := Classical.choose_spec hS
    let hB := shiftDiv_approx f (n + 1)
    let B := Classical.choose hB
    let hB_spec := Classical.choose_spec hB
    let M₁ : ℝ := max S (max (prev.M + ‖shiftDiv f n 0‖) (B + ((n + 1 : ℕ) : ℝ) + 1)) + 1
    have hM₁_pos : 0 < M₁ := by
      dsimp only [M₁]; linarith [le_max_left S (max (prev.M + ‖shiftDiv f n 0‖) (B + ((n + 1 : ℕ) : ℝ) + 1)), hS_spec.1]
    let hSn := exists_closedBall_sup (shiftDiv_differentiable hf n) R₁ hR₁_nn
    let Sn := Classical.choose hSn
    let hSn_spec := Classical.choose_spec hSn
    let K : ℝ := max Sn (M₁ + ‖shiftDiv f n 0‖) + 1
    have hz_ex := exists_gt_linear_on_pathComponentIn (shiftDiv_differentiable hf n)
      (shiftDiv_transcendental htrans n) prev.hM_pos prev.hz K
    let z₁ := Classical.choose hz_ex
    let hz₁_spec := Classical.choose_spec hz_ex
    have hz₁_norm_gt : R₁ < ‖z₁‖ := by
      by_contra hle
      push Not at hle
      have h1 := hSn_spec.2 z₁ hle
      have h2 := hz₁_spec.2
      have hK_ge : Sn < K := by
        dsimp only [K]; linarith [le_max_left Sn (M₁ + ‖shiftDiv f n 0‖)]
      have hK_pos : 0 < K := by linarith [hSn_spec.1]
      nlinarith [norm_nonneg z₁]
    have hz₁_gt : M₁ < ‖shiftDiv f (n + 1) z₁‖ := by
      have hz₁_pos : 0 < ‖z₁‖ := by linarith
      have hstep := shiftDiv_step f n z₁
      have htri : ‖shiftDiv f n z₁‖ - ‖shiftDiv f n 0‖ ≤ ‖z₁‖ * ‖shiftDiv f (n + 1) z₁‖ := by
        have h1 : z₁ * shiftDiv f (n + 1) z₁ = shiftDiv f n z₁ - shiftDiv f n 0 := by
          linear_combination -hstep
        have h2 := norm_sub_norm_le (shiftDiv f n z₁) (shiftDiv f n 0)
        rw [← h1, norm_mul] at h2
        exact h2
      have hK_ge : M₁ + ‖shiftDiv f n 0‖ < K := by
        dsimp only [K]; linarith [le_max_right Sn (M₁ + ‖shiftDiv f n 0‖)]
      have hgt := hz₁_spec.2
      have hmul : M₁ * ‖z₁‖ < ‖z₁‖ * ‖shiftDiv f (n + 1) z₁‖ := by
        nlinarith [norm_nonneg (shiftDiv f n 0)]
      nlinarith
    ⟨{ R := R₁
       M := M₁
       z := z₁
       hR := hR₁_ge
       hM_pos := hM₁_pos
       hM_ball := fun w hw => by
         dsimp only [M₁]
         linarith [hS_spec.2 w hw,
           le_max_left S (max (prev.M + ‖shiftDiv f n 0‖) (B + ((n + 1 : ℕ) : ℝ) + 1))]
       hM_grow := fun w hw hgt => by
         have ha := hB_spec.2 w hw
         dsimp only [M₁] at hgt
         have h1 : B + ((n + 1 : ℕ) : ℝ) + 1 ≤
             max (prev.M + ‖shiftDiv f n 0‖) (B + ((n + 1 : ℕ) : ℝ) + 1) := le_max_right _ _
         have h2 : max (prev.M + ‖shiftDiv f n 0‖) (B + ((n + 1 : ℕ) : ℝ) + 1) ≤ M₁ - 1 := by
           dsimp only [M₁]; linarith [le_max_right S (max (prev.M + ‖shiftDiv f n 0‖) (B + ((n + 1 : ℕ) : ℝ) + 1))]
         linarith
       hz := hz₁_gt }, trivial⟩

private lemma stage_next_mem_prev {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ∀ p : ℂ[X], f ≠ fun z => p.eval z) (n : ℕ) :
    let s := (buildStages hf htrans n).1
    let s' := (buildStages hf htrans (n + 1)).1
    s'.z ∈ pathComponentIn {w : ℂ | s.M < ‖shiftDiv f n w‖} s.z := by
  dsimp only [buildStages]
  exact (Classical.choose_spec (exists_gt_linear_on_pathComponentIn
    (shiftDiv_differentiable hf n) (shiftDiv_transcendental htrans n)
    (buildStages hf htrans n).1.hM_pos (buildStages hf htrans n).1.hz _)).1

private lemma stage_norm_gt {f : ℂ → ℂ} {n : ℕ} (s : Stage f n) {w : ℂ}
    (hw : s.M < ‖shiftDiv f n w‖) : s.R < ‖w‖ := by
  by_contra hle
  push Not at hle
  linarith [s.hM_ball w hle]

/-- Glue a sequence of paths `σ n` (from `z n` to `z (n+1)`) into a continuous `γ : ℝ → ℂ`. -/
private noncomputable def gluePaths {z : ℕ → ℂ}
    (σ : ∀ n : ℕ, Path (z n) (z (n + 1))) (t : ℝ) : ℂ :=
  if h : t ≤ 0 then z 0
  else
    let k : ℕ := ⌊t⌋₊
    σ k ⟨t - k, ⟨by
      have h1 : (k : ℝ) ≤ t := Nat.floor_le (by linarith)
      linarith, by
      have h2 : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
      linarith⟩⟩

private lemma gluePaths_eq_on_Icc {z : ℕ → ℂ}
    (σ : ∀ n : ℕ, Path (z n) (z (n + 1))) (k : ℕ) {t : ℝ}
    (ht1 : (k : ℝ) ≤ t) (ht2 : t ≤ (k : ℝ) + 1) :
    gluePaths σ t = σ k ⟨t - k, ⟨by linarith, by linarith⟩⟩ := by
  by_cases ht0 : t ≤ 0
  · have hk0 : k = 0 := by
      by_contra hne
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hne
      linarith
    subst hk0
    have ht_eq : t = 0 := by linarith
    subst ht_eq
    simp only [gluePaths, le_refl, ↓reduceDIte]
    have h0 : (⟨(0 : ℝ) - ((0 : ℕ) : ℝ), ⟨by norm_num, by norm_num⟩⟩ : unitInterval) = 0 := by
      ext; simp
    rw [h0, Path.source]
  · push Not at ht0
    by_cases hlt : t < (k : ℝ) + 1
    · have hfl : ⌊t⌋₊ = k := Nat.floor_eq_iff ht0.le |>.mpr ⟨ht1, hlt⟩
      simp only [gluePaths, not_le.mpr ht0, ↓reduceDIte]
      have heq : ∀ (m : ℕ) (hm : m = k) (hmem : t - (m : ℝ) ∈ Set.Icc (0 : ℝ) 1),
          σ m ⟨t - m, hmem⟩ = σ k ⟨t - k, ⟨by linarith, by linarith⟩⟩ := by
        intro m hm hmem; subst hm; rfl
      exact heq ⌊t⌋₊ hfl _
    · have ht_eq : t = (k : ℝ) + 1 := by linarith
      have hfl : ⌊t⌋₊ = k + 1 := by
        rw [ht_eq, show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
      simp only [gluePaths, not_le.mpr ht0, ↓reduceDIte]
      have h1 : (⟨t - (k : ℝ), ⟨by linarith, by linarith⟩⟩ : unitInterval) = 1 := by
        ext; dsimp; linarith
      rw [h1, Path.target]
      have heq : ∀ (m : ℕ) (hm : m = k + 1) (hmem : t - (m : ℝ) ∈ Set.Icc (0 : ℝ) 1),
          σ m ⟨t - m, hmem⟩ = z (k + 1) := by
        intro m hm hmem
        subst hm
        have h0 : (⟨t - ((k + 1 : ℕ) : ℝ), hmem⟩ : unitInterval) = 0 := by
          ext; dsimp; push_cast; linarith
        rw [h0, Path.source]
      exact heq ⌊t⌋₊ hfl _

private lemma gluePaths_continuous {z : ℕ → ℂ} (σ : ∀ n : ℕ, Path (z n) (z (n + 1))) :
    Continuous (gluePaths σ) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht0 : t < 0
  · have hev : gluePaths σ =ᶠ[𝓝 t] fun _ => z 0 := by
      filter_upwards [isOpen_Iio.mem_nhds ht0] with s hs
      simp only [gluePaths, le_of_lt (Set.mem_Iio.mp hs), ↓reduceDIte]
    exact continuousAt_const.congr hev.symm
  · push Not at ht0
    have hcont_seg : ∀ k : ℕ, ContinuousOn (gluePaths σ) (Set.Icc (k : ℝ) ((k : ℝ) + 1)) := by
      intro k
      let g : ℝ → ℂ := fun s => σ k (Set.projIcc 0 1 zero_le_one (s - k))
      have hg : Continuous g :=
        (σ k).continuous.comp (continuous_projIcc.comp (continuous_id.sub continuous_const))
      refine hg.continuousOn.congr fun s hs => ?_
      rw [gluePaths_eq_on_Icc σ k hs.1 hs.2]
      dsimp only [g]
      congr 1
      ext
      simp only [Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1)
        (show s - (k : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨by linarith [hs.1], by linarith [hs.2]⟩)]
    have hcont_neg : ContinuousOn (gluePaths σ) (Set.Iic (0 : ℝ)) := by
      refine continuousOn_const (c := z 0) |>.congr fun s hs => ?_
      simp only [gluePaths, Set.mem_Iic.mp hs, ↓reduceDIte]
    by_cases hteq0 : t = 0
    · subst hteq0
      have h1 : ContinuousWithinAt (gluePaths σ) (Set.Iic 0) 0 := hcont_neg 0 (Set.mem_Iic.mpr le_rfl)
      have h2 : ContinuousWithinAt (gluePaths σ) (Set.Ici 0) 0 := by
        have hs := hcont_seg 0 0 ⟨by norm_num, by norm_num⟩
        have hnhds : Set.Icc ((0 : ℕ) : ℝ) (((0 : ℕ) : ℝ) + 1) ∈ 𝓝[≥] (0 : ℝ) := by
          simpa using Icc_mem_nhdsGE (zero_lt_one : (0 : ℝ) < 1)
        exact hs.mono_of_mem_nhdsWithin hnhds
      exact continuousAt_iff_continuous_left_right.mpr ⟨h1, h2⟩
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hteq0)
      let k : ℕ := ⌊t⌋₊
      have hk1 : (k : ℝ) ≤ t := Nat.floor_le htpos.le
      have hk2 : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
      by_cases hteqk : t = (k : ℝ)
      · have hkpos : 1 ≤ k := by
          by_contra h0
          have hk0 : k = 0 := by omega
          rw [hk0, Nat.cast_zero] at hteqk
          linarith
        have hkm1 : ((k - 1 : ℕ) : ℝ) + 1 = t := by
          rw [Nat.cast_sub hkpos]; push_cast; linarith
        have hleft : ContinuousWithinAt (gluePaths σ) (Set.Iic t) t := by
          have hs := hcont_seg (k - 1) t ⟨by linarith, by linarith⟩
          have hnhds : Set.Icc ((k - 1 : ℕ) : ℝ) (((k - 1 : ℕ) : ℝ) + 1) ∈ 𝓝[≤] t := by
            rw [hkm1]
            exact Icc_mem_nhdsLE (by linarith : ((k - 1 : ℕ) : ℝ) < t)
          exact hs.mono_of_mem_nhdsWithin hnhds
        have hright : ContinuousWithinAt (gluePaths σ) (Set.Ici t) t := by
          have hs := hcont_seg k t ⟨by linarith, by linarith⟩
          have hnhds : Set.Icc (k : ℝ) ((k : ℝ) + 1) ∈ 𝓝[≥] t := by
            rw [← hteqk]
            exact Icc_mem_nhdsGE (by linarith : t < t + 1)
          exact hs.mono_of_mem_nhdsWithin hnhds
        exact continuousAt_iff_continuous_left_right.mpr ⟨hleft, hright⟩
      · have hkt : (k : ℝ) < t := lt_of_le_of_ne hk1 (Ne.symm hteqk)
        have hnhds : Set.Icc (k : ℝ) ((k : ℝ) + 1) ∈ 𝓝 t :=
          Icc_mem_nhds hkt hk2
        exact (hcont_seg k t ⟨hk1, hk2.le⟩).continuousAt hnhds

private theorem prove_main :
    ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (∀ p : Polynomial ℂ, f ≠ fun z => p.eval z) →
      ∃ γ : ℝ → ℂ, Continuous γ ∧ Tendsto γ atTop (cobounded ℂ) ∧
        ∀ n : ℕ, Tendsto (fun t : ℝ => f (γ t) / (γ t) ^ n) atTop (cobounded ℂ) := by
  intro f hf htrans
  let S : ∀ n : ℕ, Stage f n := fun n => (buildStages hf htrans n).1
  let z : ℕ → ℂ := fun n => (S n).z
  have hpath_ex : ∀ n : ℕ, ∃ σ : Path (z n) (z (n + 1)),
      ∀ s : unitInterval, (S n).M < ‖shiftDiv f n (σ s)‖ := by
    intro n
    have hmem := stage_next_mem_prev hf htrans n
    obtain ⟨σ, hσ⟩ := hmem
    exact ⟨σ, hσ⟩
  choose σ hσ using hpath_ex
  let γ : ℝ → ℂ := gluePaths σ
  refine ⟨γ, gluePaths_continuous σ, ?_, ?_⟩
  · -- Tendsto γ atTop (cobounded ℂ)
    rw [← tendsto_norm_atTop_iff_cobounded, Filter.tendsto_atTop]
    intro B
    refine Filter.eventually_atTop.mpr ⟨(Nat.ceil (max 0 B) + 1 : ℕ), fun t ht => ?_⟩
    have ht_pos : 0 < t := by
      have : (1 : ℝ) ≤ (Nat.ceil (max 0 B) + 1 : ℕ) := by exact_mod_cast Nat.succ_pos _
      linarith
    let k : ℕ := ⌊t⌋₊
    have hk_ge : Nat.ceil (max 0 B) + 1 ≤ k := Nat.le_floor ht
    have hγt : γ t = σ k ⟨t - k, ⟨by linarith [Nat.floor_le ht_pos.le],
        by linarith [Nat.lt_floor_add_one t]⟩⟩ := by
      simp only [γ, gluePaths, not_le.mpr ht_pos, ↓reduceDIte, k]
    have hgt : (S k).M < ‖shiftDiv f k (γ t)‖ := by rw [hγt]; exact hσ k _
    have hnorm := stage_norm_gt (S k) hgt
    have hR := (S k).hR
    have hB : B ≤ (k : ℝ) := by
      have h1 : B ≤ max 0 B := le_max_right _ _
      have h2 : max 0 B ≤ (Nat.ceil (max 0 B) : ℝ) := Nat.le_ceil _
      have h3 : (Nat.ceil (max 0 B) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : Nat.ceil (max 0 B) ≤ k)
      linarith
    linarith
  · -- ∀ n, Tendsto (fun t => f (γ t) / (γ t) ^ n) atTop (cobounded ℂ)
    intro n
    rw [← tendsto_norm_atTop_iff_cobounded, Filter.tendsto_atTop]
    intro B
    let N₀ : ℕ := max n (Nat.ceil (max 0 B) + 1)
    refine Filter.eventually_atTop.mpr ⟨(N₀ : ℝ), fun t ht => ?_⟩
    have hN₀_pos : (1 : ℝ) ≤ N₀ := by
      have : 1 ≤ N₀ := (Nat.succ_pos _).trans_le (le_max_right _ _)
      exact_mod_cast this
    have ht_pos : 0 < t := by linarith
    let k : ℕ := ⌊t⌋₊
    have hk_ge : N₀ ≤ k := Nat.le_floor ht
    have hkn : n ≤ k := (le_max_left _ _).trans hk_ge
    have hγt : γ t = σ k ⟨t - k, ⟨by linarith [Nat.floor_le ht_pos.le],
        by linarith [Nat.lt_floor_add_one t]⟩⟩ := by
      simp only [γ, gluePaths, not_le.mpr ht_pos, ↓reduceDIte, k]
    have hgt : (S k).M < ‖shiftDiv f k (γ t)‖ := by rw [hγt]; exact hσ k _
    have hnorm : (S k).R < ‖γ t‖ := stage_norm_gt (S k) hgt
    have hnorm1 : 1 ≤ ‖γ t‖ := by linarith [(S k).hR, Nat.cast_nonneg (α := ℝ) k]
    have hgrow : (k : ℝ) + 1 < ‖f (γ t) / (γ t) ^ k‖ := (S k).hM_grow (γ t) hnorm1 hgt
    have hpow_ge : 1 ≤ ‖γ t‖ ^ (k - n) := one_le_pow₀ hnorm1
    have hzn0 : (γ t) ^ n ≠ 0 := pow_ne_zero n (by intro h0; rw [h0, norm_zero] at hnorm1; linarith)
    have hzk0 : (γ t) ^ k ≠ 0 := pow_ne_zero k (by intro h0; rw [h0, norm_zero] at hnorm1; linarith)
    have hratio : ‖f (γ t) / (γ t) ^ n‖ = ‖γ t‖ ^ (k - n) * ‖f (γ t) / (γ t) ^ k‖ := by
      rw [← norm_pow, ← norm_mul]
      congr 1
      have hpow : (γ t) ^ k = (γ t) ^ n * (γ t) ^ (k - n) := by
        rw [← pow_add, Nat.add_sub_cancel' hkn]
      field_simp [hzn0, hzk0]
      rw [hpow]; ring
    have hB : B ≤ (k : ℝ) := by
      have h1 : B ≤ max 0 B := le_max_right _ _
      have h2 : max 0 B ≤ (Nat.ceil (max 0 B) : ℝ) := Nat.le_ceil _
      have h3 : (Nat.ceil (max 0 B) : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast ((Nat.le_succ _).trans (le_max_right n _)).trans hk_ge
      linarith
    have hge_k : (k : ℝ) + 1 ≤ ‖f (γ t) / (γ t) ^ n‖ := by
      rw [hratio]
      have hfk_nn : 0 ≤ ‖f (γ t) / (γ t) ^ k‖ := norm_nonneg _
      nlinarith
    linarith

end OMA.P_erdos_514

theorem OMA.solution : type_of% @OMA.S_erdos_514.main :=
  OMA.P_erdos_514.prove_main
