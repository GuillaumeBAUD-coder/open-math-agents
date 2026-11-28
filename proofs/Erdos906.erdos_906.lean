import FormalConjectures.ErdosProblems.«906»

/-!
# Erdős Problem 906

Upstream: formal-conjectures `FormalConjectures/ErdosProblems/906.lean:33` (`Erdos906.erdos_906`).
Credit: @Brean0.

Constructs an explicit entire transcendental exponential-polygon series `f : ℂ → ℂ` whose
`n`-th derivative has `ε_k`-dense zeros on `‖z‖ ≤ R_k` for every sufficiently large `n`,
hence `⋃ k, Z(f^{(seq k)})` is dense in `ℂ` for every strictly increasing sequence `seq : ℕ → ℕ`.
-/

namespace OMA.Erdos906

open Complex Filter Finset Metric Topology
open scoped BigOperators

/- ### Section 1: Rouche zero existence via Maximum Modulus Principle -/

private lemma div_re_pos_of_norm_sub_lt {a b : ℂ} (ha : a ≠ 0) (h : ‖a - b‖ < ‖b‖) :
    0 < (b / a).re := by
  have hsq : ‖a - b‖ ^ 2 < ‖b‖ ^ 2 :=
    pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at hsq
  simp only [Complex.sub_re, Complex.sub_im] at hsq
  have ha_pos : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
  have ha_ns : Complex.normSq a = a.re * a.re + a.im * a.im := Complex.normSq_apply a
  have hdot : 0 < b.re * a.re + b.im * a.im := by nlinarith
  rw [Complex.div_re]
  have hsum : b.re * a.re / Complex.normSq a + b.im * a.im / Complex.normSq a =
      (b.re * a.re + b.im * a.im) / Complex.normSq a := by ring
  rw [hsum]
  exact div_pos hdot ha_pos

private lemma rouche_exists_zero {F G : ℂ → ℂ} {z₀ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hG0 : G z₀ = 0)
    (hbd : ∀ z, ‖z - z₀‖ = δ → ‖F z - G z‖ < ‖G z‖) :
    ∃ z ∈ Metric.closedBall z₀ δ, F z = 0 := by
  by_contra hno
  push Not at hno
  let H : ℂ → ℂ := fun z => Complex.exp (-(G z / F z))
  have hH_diff_pt : ∀ z ∈ Metric.closedBall z₀ δ, DifferentiableAt ℂ H z := by
    intro z hz
    have hFz : F z ≠ 0 := hno z hz
    exact ((hG z).div (hF z) hFz).neg.cexp
  have hH_cl : DiffContOnCl ℂ H (Metric.ball z₀ δ) := by
    refine ⟨fun z hz => (hH_diff_pt z (Metric.ball_subset_closedBall hz)).differentiableWithinAt, ?_⟩
    rw [closure_ball z₀ hδ.ne']
    exact fun z hz => (hH_diff_pt z hz).continuousAt.continuousWithinAt
  have hH_lt_one : ∀ z ∈ Metric.sphere z₀ δ, ‖H z‖ < 1 := by
    intro z hz
    have hdist : ‖z - z₀‖ = δ := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hz_cl : z ∈ Metric.closedBall z₀ δ := by
      rw [Metric.mem_closedBall, dist_eq_norm, hdist]
    have hre : 0 < (G z / F z).re := div_re_pos_of_norm_sub_lt (hno z hz_cl) (hbd z hdist)
    have hnorm : ‖H z‖ = Real.exp (-(G z / F z).re) := by
      dsimp [H]
      rw [Complex.norm_exp, Complex.neg_re]
    rw [hnorm]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hsphere_ne : (Metric.sphere z₀ δ).Nonempty := by
    refine ⟨z₀ + (δ : ℂ), ?_⟩
    rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hδ.le]
  have hH_cont_sph : ContinuousOn (fun z => ‖H z‖) (Metric.sphere z₀ δ) :=
    fun z hz => (hH_diff_pt z (Metric.sphere_subset_closedBall hz)).continuousAt.norm.continuousWithinAt
  obtain ⟨w, hw_mem, hw_max⟩ := (isCompact_sphere z₀ δ).exists_isMaxOn hsphere_ne hH_cont_sph
  have hfront_le : ∀ z ∈ frontier (Metric.ball z₀ δ), ‖H z‖ ≤ ‖H w‖ := by
    intro z hz
    have hzs : z ∈ Metric.sphere z₀ δ := frontier_ball_subset_sphere hz
    exact hw_max hzs
  have hz0_cl : z₀ ∈ closure (Metric.ball z₀ δ) := by
    rw [closure_ball z₀ hδ.ne']
    exact Metric.mem_closedBall_self hδ.le
  have hle := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hH_cl hfront_le hz0_cl
  have hHz0 : ‖H z₀‖ = 1 := by
    dsimp [H]
    rw [hG0, zero_div, neg_zero, Complex.exp_zero, norm_one]
  linarith [hH_lt_one w hw_mem]

private lemma one_sub_exp_norm_ge {w : ℂ} (hw : ‖w‖ = 1 / 2) :
    (1 / 4 : ℝ) ≤ ‖1 - Complex.exp w‖ := by
  have h1 : ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 :=
    Complex.norm_exp_sub_one_sub_id_le (by linarith)
  have htri : ‖w‖ ≤ ‖Complex.exp w - 1‖ + ‖Complex.exp w - 1 - w‖ := by
    have heq : w = (Complex.exp w - 1) - (Complex.exp w - 1 - w) := by ring
    conv_lhs => rw [heq]
    exact norm_sub_le _ _
  rw [norm_sub_rev]
  rw [hw] at h1 htri
  linarith

/- ### Section 2: Explicit parameters and elementary inequalities -/

private def R (k : ℕ) : ℝ := (k : ℝ) + 2

private noncomputable def ε (k : ℕ) : ℝ := (1 / 4 : ℝ) ^ (k + 1)

private def M (k : ℕ) : ℕ := 32 * (k + 2) * 4 ^ (k + 1)

private def rNat : ℕ → ℕ
  | 0 => 2 * (M 0) ^ 3 * 4
  | k + 1 => max (rNat k * (M (k + 1)) ^ 2) (2 * (M (k + 1)) ^ 3 * 4 ^ (k + 2))

private def r (k : ℕ) : ℝ := (rNat k : ℝ)

private def T : ℕ → ℕ
  | 0 => 16 * rNat 1 + 2 * M 1 + 200
  | k + 1 => T k + 4 * rNat (k + 2) * (k + 6) + 2 * M (k + 2) + 200 * (k + 2)

private def Hmid (k : ℕ) : ℕ := (T k + T (k + 1)) / 2

private noncomputable def c : ℕ → ℝ
  | 0 => 1
  | k + 1 => c k * (r k / r (k + 1)) ^ (T k)

private lemma ε_pos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity

private lemma ε_succ (k : ℕ) : ε (k + 1) = ε k / 4 := by
  dsimp [ε]
  rw [pow_succ]
  ring

private lemma M_ge_256 (k : ℕ) : 256 ≤ M k := by
  dsimp [M]
  have h1 : 4 ≤ 4 ^ (k + 1) := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  nlinarith

private lemma M_pos (k : ℕ) : 0 < M k := lt_of_lt_of_le (by norm_num) (M_ge_256 k)

private lemma M_mono {a b : ℕ} (hab : a ≤ b) : M a ≤ M b := by
  dsimp [M]
  have h1 : a + 2 ≤ b + 2 := by omega
  have h2 : 4 ^ (a + 1) ≤ 4 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 32 h1) h2

private lemma rNat_ge_cube (k : ℕ) : 2 * (M k) ^ 3 * 4 ^ (k + 1) ≤ rNat k := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_max_right _ _

private lemma rNat_step_ge (k : ℕ) : rNat k * (M (k + 1)) ^ 2 ≤ rNat (k + 1) :=
  le_max_left _ _

private lemma rNat_pos (k : ℕ) : 0 < rNat k := by
  have h1 := rNat_ge_cube k
  have h2 := M_pos k
  have h3 : 0 < 4 ^ (k + 1) := by positivity
  nlinarith [pow_pos h2 3]

private lemma r_pos (k : ℕ) : 0 < r k := by dsimp [r]; exact_mod_cast rNat_pos k

private lemma rNat_step_mul_four (k : ℕ) : 4 * rNat k ≤ rNat (k + 1) := by
  have h1 := rNat_step_ge k
  have h2 := M_ge_256 (k + 1)
  have h3 : 4 ≤ (M (k + 1)) ^ 2 := by nlinarith
  nlinarith [rNat_pos k]

private lemma r_step_mul_four (k : ℕ) : 4 * r k ≤ r (k + 1) := by
  dsimp [r]; exact_mod_cast rNat_step_mul_four k

private lemma rNat_mono {a b : ℕ} (hab : a ≤ b) : rNat a ≤ rNat b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this; exact le_rfl
  | succ b ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · exact (ih (by omega)).trans (by linarith [rNat_step_mul_four b])

private lemma r_mono {a b : ℕ} (hab : a ≤ b) : r a ≤ r b := by
  dsimp [r]; exact_mod_cast rNat_mono hab

private lemma r_div_r_ge_exp_one (k : ℕ) : Real.exp 1 ≤ r (k + 1) / r k := by
  have h1 : 4 * r k ≤ r (k + 1) := r_step_mul_four k
  have hpos := r_pos k
  have h4 : (4 : ℝ) ≤ r (k + 1) / r k := (le_div_iff₀ hpos).mpr h1
  have he : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  linarith

private lemma r_div_r_pow_le_exp (k m : ℕ) :
    (r k / r (k + 1)) ^ m ≤ Real.exp (-(m : ℝ)) := by
  have h1 := r_div_r_ge_exp_one k
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have hinv : r k / r (k + 1) ≤ (Real.exp 1)⁻¹ := by
    rw [← inv_div]
    exact inv_anti₀ hpos h1
  have hinv_eq : (Real.exp 1)⁻¹ = Real.exp (-1) := (Real.exp_neg 1).symm
  rw [hinv_eq] at hinv
  have hpow : (r k / r (k + 1)) ^ m ≤ (Real.exp (-1)) ^ m :=
    pow_le_pow_left₀ (div_nonneg (r_pos k).le (r_pos (k + 1)).le) hinv m
  rw [← Real.exp_nat_mul] at hpow
  simpa using hpow

private lemma T_even (k : ℕ) : Even (T k) := by
  induction k with
  | zero =>
    refine ⟨8 * rNat 1 + M 1 + 100, ?_⟩
    dsimp [T]; omega
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t + 2 * rNat (k + 2) * (k + 6) + M (k + 2) + 100 * (k + 2), ?_⟩
    dsimp [T]; rw [ht]; ring

private lemma T_step (k : ℕ) :
    T (k + 1) = T k + 4 * rNat (k + 2) * (k + 6) + 2 * M (k + 2) + 200 * (k + 2) := rfl

private lemma T_strictMono : StrictMono T := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [T_step]
  omega

private lemma two_mul_Hmid (k : ℕ) : 2 * Hmid k = T k + T (k + 1) := by
  obtain ⟨a, ha⟩ := T_even k
  obtain ⟨b, hb⟩ := T_even (k + 1)
  dsimp [Hmid]
  omega

private lemma Hmid_sub_T (k : ℕ) :
    Hmid k - T k = 2 * rNat (k + 2) * (k + 6) + M (k + 2) + 100 * (k + 2) := by
  have h1 := two_mul_Hmid k
  have h2 := T_step k
  have hmul : 4 * rNat (k + 2) * (k + 6) = 2 * (2 * rNat (k + 2) * (k + 6)) := by ring
  omega

private lemma T_succ_sub_Hmid (k : ℕ) :
    T (k + 1) - Hmid k = 2 * rNat (k + 2) * (k + 6) + M (k + 2) + 100 * (k + 2) := by
  have h1 := two_mul_Hmid k
  have h2 := T_step k
  have hmul : 4 * rNat (k + 2) * (k + 6) = 2 * (2 * rNat (k + 2) * (k + 6)) := by ring
  omega

private lemma Hmid_strictMono : StrictMono Hmid := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h1 := two_mul_Hmid k
  have h2 := two_mul_Hmid (k + 1)
  have h3 : T k < T (k + 1) := T_strictMono (Nat.lt_succ_self k)
  have h4 : T (k + 1) < T (k + 1 + 1) := T_strictMono (Nat.lt_succ_self (k + 1))
  omega

private lemma c_pos (k : ℕ) : 0 < c k := by
  induction k with
  | zero => exact zero_lt_one
  | succ k ih =>
    dsimp [c]
    exact mul_pos ih (pow_pos (div_pos (r_pos k) (r_pos (k + 1))) _)

private lemma weight_step_ge (k n : ℕ) (h : T k ≤ n) :
    c (k + 1) * r (k + 1) ^ n = c k * r k ^ n * (r (k + 1) / r k) ^ (n - T k) := by
  have hrk : r k ≠ 0 := (r_pos k).ne'
  have hrk1 : r (k + 1) ≠ 0 := (r_pos (k + 1)).ne'
  dsimp [c]
  rw [div_pow, div_pow]
  have h1 : n = T k + (n - T k) := by omega
  have hp1 : r (k + 1) ^ n = r (k + 1) ^ T k * r (k + 1) ^ (n - T k) := by
    conv_lhs => rw [h1]
    rw [pow_add]
  have hp2 : r k ^ n = r k ^ T k * r k ^ (n - T k) := by
    conv_lhs => rw [h1]
    rw [pow_add]
  rw [hp1, hp2]
  field_simp [hrk, hrk1]

private lemma weight_step_le (k n : ℕ) (h : n ≤ T k) :
    c (k + 1) * r (k + 1) ^ n = c k * r k ^ n * (r k / r (k + 1)) ^ (T k - n) := by
  have hrk : r k ≠ 0 := (r_pos k).ne'
  have hrk1 : r (k + 1) ≠ 0 := (r_pos (k + 1)).ne'
  dsimp [c]
  rw [div_pow, div_pow]
  have h1 : T k = n + (T k - n) := by omega
  have hp1 : r k ^ T k = r k ^ n * r k ^ (T k - n) := by
    conv_lhs => rw [h1]
    rw [pow_add]
  have hp2 : r (k + 1) ^ T k = r (k + 1) ^ n * r (k + 1) ^ (T k - n) := by
    conv_lhs => rw [h1]
    rw [pow_add]
  rw [hp1, hp2]
  field_simp [hrk, hrk1]

private lemma weight_ratio_le_of_le (a b n : ℕ) (hab : a ≤ b) (hn : T a ≤ n)
    (hstep : ∀ j, a ≤ j → j < b → T j ≤ n) :
    c a * r a ^ n ≤ c b * r b ^ n := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this; exact le_rfl
  | succ b ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · have hprev := ih (by omega) (fun j hj1 hj2 => hstep j hj1 (by omega))
      have hTb : T b ≤ n := hstep b (by omega) (Nat.lt_succ_self b)
      rw [weight_step_ge b n hTb]
      have hge1 : (1 : ℝ) ≤ (r (b + 1) / r b) ^ (n - T b) := by
        apply one_le_pow₀
        exact (one_le_div (r_pos b)).mpr (r_mono (Nat.le_succ b))
      have hnonneg : 0 ≤ c b * r b ^ n := mul_nonneg (c_pos b).le (pow_nonneg (r_pos b).le _)
      calc c a * r a ^ n ≤ c b * r b ^ n := hprev
        _ = c b * r b ^ n * 1 := (mul_one _).symm
        _ ≤ c b * r b ^ n * (r (b + 1) / r b) ^ (n - T b) :=
            mul_le_mul_of_nonneg_left hge1 hnonneg

private lemma weight_ratio_le_upper (a b n : ℕ) (hab : a ≤ b)
    (hstep : ∀ j, a ≤ j → j < b → n ≤ T j) :
    c b * r b ^ n ≤ c a * r a ^ n := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this; exact le_rfl
  | succ b ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · have hprev := ih (by omega) (fun j hj1 hj2 => hstep j hj1 (by omega))
      have hTb : n ≤ T b := hstep b (by omega) (Nat.lt_succ_self b)
      rw [weight_step_le b n hTb]
      have hle1 : (r b / r (b + 1)) ^ (T b - n) ≤ 1 := by
        apply pow_le_one₀ (div_nonneg (r_pos b).le (r_pos (b + 1)).le)
        exact (div_le_one (r_pos (b + 1))).mpr (r_mono (Nat.le_succ b))
      have hnonneg : 0 ≤ c b * r b ^ n := mul_nonneg (c_pos b).le (pow_nonneg (r_pos b).le _)
      calc c b * r b ^ n * (r b / r (b + 1)) ^ (T b - n) ≤ c b * r b ^ n * 1 :=
            mul_le_mul_of_nonneg_left hle1 hnonneg
        _ = c b * r b ^ n := mul_one _
        _ ≤ c a * r a ^ n := hprev

private lemma weight_lower_tail_term (k n m : ℕ) (hlo : Hmid k ≤ n) (hm : m ≤ k) :
    c m * r m ^ n * (M m : ℝ) * Real.exp (r m * ((k : ℝ) + 5)) ≤
      c (k + 1) * r (k + 1) ^ n * Real.exp (-100 * ((k + 2 : ℕ) : ℝ)) := by
  have hTk : T k ≤ n := by
    have := two_mul_Hmid k
    have : T k < T (k + 1) := T_strictMono (Nat.lt_succ_self k)
    omega
  have hcm : c m * r m ^ n ≤ c k * r k ^ n := by
    apply weight_ratio_le_of_le m k n hm
    · exact (T_strictMono.monotone hm).trans hTk
    · intro j _ hjk
      exact (T_strictMono.monotone (le_of_lt hjk)).trans hTk
  have hstep := weight_step_ge k n hTk
  have hinv : c k * r k ^ n = c (k + 1) * r (k + 1) ^ n * (r k / r (k + 1)) ^ (n - T k) := by
    rw [hstep, mul_assoc, ← mul_pow]
    have h1 : r (k + 1) / r k * (r k / r (k + 1)) = 1 := by
      field_simp [(r_pos k).ne', (r_pos (k + 1)).ne']
    rw [h1, one_pow, mul_one]
  have hpow : (r k / r (k + 1)) ^ (n - T k) ≤ Real.exp (-((n - T k : ℕ) : ℝ)) :=
    r_div_r_pow_le_exp k (n - T k)
  have hgap : 2 * rNat (k + 2) * (k + 6) + M (k + 2) + 100 * (k + 2) ≤ n - T k := by
    have := Hmid_sub_T k; omega
  have hgapR : 2 * r (k + 2) * ((k : ℝ) + 6) + (M (k + 2) : ℝ) + 100 * ((k + 2 : ℕ) : ℝ) ≤
      ((n - T k : ℕ) : ℝ) := by
    dsimp [r]; exact_mod_cast hgap
  have hMle : (M m : ℝ) ≤ Real.exp (M (k + 2) : ℝ) := by
    have h1 : (M m : ℝ) ≤ (M (k + 2) : ℝ) := by exact_mod_cast M_mono (by omega)
    linarith [Real.add_one_le_exp (M (k + 2) : ℝ)]
  have hrm : r m ≤ r (k + 2) := r_mono (by omega)
  have hexp_rm : r m * ((k : ℝ) + 5) ≤ 2 * r (k + 2) * ((k : ℝ) + 6) := by
    nlinarith [r_pos (k + 2)]
  have hnonneg : 0 ≤ c (k + 1) * r (k + 1) ^ n :=
    mul_nonneg (c_pos (k + 1)).le (pow_nonneg (r_pos (k + 1)).le _)
  calc c m * r m ^ n * (M m : ℝ) * Real.exp (r m * ((k : ℝ) + 5))
      ≤ c k * r k ^ n * Real.exp (M (k + 2) : ℝ) * Real.exp (2 * r (k + 2) * ((k : ℝ) + 6)) := by
        apply mul_le_mul
        · exact mul_le_mul hcm hMle (Nat.cast_nonneg _) (mul_nonneg (c_pos k).le (pow_nonneg (r_pos k).le _))
        · exact Real.exp_le_exp.mpr hexp_rm
        · exact (Real.exp_pos _).le
        · exact mul_nonneg (mul_nonneg (c_pos k).le (pow_nonneg (r_pos k).le _)) (Real.exp_pos _).le
    _ = c (k + 1) * r (k + 1) ^ n * ((r k / r (k + 1)) ^ (n - T k) *
          Real.exp (M (k + 2) : ℝ) * Real.exp (2 * r (k + 2) * ((k : ℝ) + 6))) := by
        rw [hinv]; ring
    _ ≤ c (k + 1) * r (k + 1) ^ n * (Real.exp (-((n - T k : ℕ) : ℝ)) *
          Real.exp (M (k + 2) : ℝ) * Real.exp (2 * r (k + 2) * ((k : ℝ) + 6))) := by
        apply mul_le_mul_of_nonneg_left _ hnonneg
        gcongr
    _ = c (k + 1) * r (k + 1) ^ n *
          Real.exp (-((n - T k : ℕ) : ℝ) + (M (k + 2) : ℝ) + 2 * r (k + 2) * ((k : ℝ) + 6)) := by
        rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ c (k + 1) * r (k + 1) ^ n * Real.exp (-100 * ((k + 2 : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hnonneg
        apply Real.exp_le_exp.mpr
        linarith

private lemma weight_upper_tail_term (k n m : ℕ) (hhi : n ≤ Hmid (k + 1)) (hm : k + 3 ≤ m)
    {B : ℝ} (hB : B ≤ (m : ℝ) + 4) :
    c m * r m ^ n * (M m : ℝ) * Real.exp (r m * B) ≤
      c (k + 2) * r (k + 2) ^ n * Real.exp (-100 * (m : ℝ)) := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 3 := ⟨m - 3, by omega⟩
  have hkp : k ≤ p := by omega
  have hn_le_H : n ≤ Hmid (p + 1) := hhi.trans (Hmid_strictMono.monotone (by omega))
  have hn_le_T : ∀ j, k + 2 ≤ j → j ≤ p + 2 → n ≤ T j := by
    intro j hj1 _
    have h1 : Hmid (k + 1) ≤ T (k + 2) := by
      have h1a : 2 * Hmid (k + 1) = T (k + 1) + T (k + 2) := two_mul_Hmid (k + 1)
      have h1b : T (k + 1) < T (k + 2) := T_strictMono (Nat.lt_succ_self (k + 1))
      omega
    exact (hhi.trans h1).trans (T_strictMono.monotone hj1)
  have hprev : c (p + 2) * r (p + 2) ^ n ≤ c (k + 2) * r (k + 2) ^ n :=
    weight_ratio_le_upper (k + 2) (p + 2) n (by omega) (fun j hj1 hj2 => hn_le_T j hj1 (by omega))
  have hstep := weight_step_le (p + 2) n (hn_le_T (p + 2) (by omega) le_rfl)
  have hpow : (r (p + 2) / r (p + 3)) ^ (T (p + 2) - n) ≤ Real.exp (-((T (p + 2) - n : ℕ) : ℝ)) :=
    r_div_r_pow_le_exp (p + 2) (T (p + 2) - n)
  have hgap : 2 * rNat (p + 3) * (p + 7) + M (p + 3) + 100 * (p + 3) ≤ T (p + 2) - n := by
    have h1 : T (p + 2) - Hmid (p + 1) = 2 * rNat (p + 3) * (p + 7) + M (p + 3) + 100 * (p + 3) :=
      T_succ_sub_Hmid (p + 1)
    omega
  have hgapR : 2 * r (p + 3) * (((p + 3 : ℕ) : ℝ) + 4) + (M (p + 3) : ℝ) + 100 * ((p + 3 : ℕ) : ℝ) ≤
      ((T (p + 2) - n : ℕ) : ℝ) := by
    have h1 : 2 * rNat (p + 3) * ((p + 3) + 4) + M (p + 3) + 100 * (p + 3) ≤ T (p + 2) - n := by omega
    dsimp [r]; exact_mod_cast h1
  have hMle : (M (p + 3) : ℝ) ≤ Real.exp (M (p + 3) : ℝ) := by
    linarith [Real.add_one_le_exp (M (p + 3) : ℝ)]
  have hB_mul : r (p + 3) * B ≤ 2 * r (p + 3) * (((p + 3 : ℕ) : ℝ) + 4) := by
    nlinarith [r_pos (p + 3)]
  have hnonneg : 0 ≤ c (k + 2) * r (k + 2) ^ n :=
    mul_nonneg (c_pos (k + 2)).le (pow_nonneg (r_pos (k + 2)).le _)
  calc c (p + 3) * r (p + 3) ^ n * (M (p + 3) : ℝ) * Real.exp (r (p + 3) * B)
      = c (p + 2) * r (p + 2) ^ n * (r (p + 2) / r (p + 3)) ^ (T (p + 2) - n) *
          (M (p + 3) : ℝ) * Real.exp (r (p + 3) * B) := by rw [hstep]
    _ ≤ c (k + 2) * r (k + 2) ^ n * Real.exp (-((T (p + 2) - n : ℕ) : ℝ)) *
          Real.exp (M (p + 3) : ℝ) * Real.exp (2 * r (p + 3) * (((p + 3 : ℕ) : ℝ) + 4)) := by
        have h1 : c (p + 2) * r (p + 2) ^ n * (r (p + 2) / r (p + 3)) ^ (T (p + 2) - n) ≤
            c (k + 2) * r (k + 2) ^ n * Real.exp (-((T (p + 2) - n : ℕ) : ℝ)) :=
          mul_le_mul hprev hpow (pow_nonneg (div_nonneg (r_pos _).le (r_pos _).le) _) hnonneg
        have h2 : c (p + 2) * r (p + 2) ^ n * (r (p + 2) / r (p + 3)) ^ (T (p + 2) - n) * (M (p + 3) : ℝ) ≤
            c (k + 2) * r (k + 2) ^ n * Real.exp (-((T (p + 2) - n : ℕ) : ℝ)) * Real.exp (M (p + 3) : ℝ) :=
          mul_le_mul h1 hMle (Nat.cast_nonneg _) (mul_nonneg hnonneg (Real.exp_pos _).le)
        exact mul_le_mul h2 (Real.exp_le_exp.mpr hB_mul) (Real.exp_pos _).le (by positivity)
    _ = c (k + 2) * r (k + 2) ^ n *
          Real.exp (-((T (p + 2) - n : ℕ) : ℝ) + (M (p + 3) : ℝ) +
            2 * r (p + 3) * (((p + 3 : ℕ) : ℝ) + 4)) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
    _ ≤ c (k + 2) * r (k + 2) ^ n * Real.exp (-100 * ((p + 3 : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hnonneg
        apply Real.exp_le_exp.mpr
        linarith

/- ### Section 3: Exponential-polygon blocks, entirety, termwise derivatives, and transcendence -/

private noncomputable def zeta (m : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))

private lemma norm_zeta (m : ℕ) : ‖zeta m‖ = 1 := by
  dsimp [zeta]
  have h : (2 * (Real.pi : ℂ) * Complex.I / (m : ℂ)) = ((2 * Real.pi / (m : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private lemma zeta_pow_self {m : ℕ} (hm : 0 < m) : zeta m ^ m = 1 := by
  dsimp [zeta]
  rw [← Complex.exp_nat_mul]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have h : (m : ℂ) * (2 * Real.pi * Complex.I / (m : ℂ)) = 2 * Real.pi * Complex.I := by
    field_simp [hmC]
  rw [h, Complex.exp_two_pi_mul_I]

private lemma zeta_pow_ne_one {m t : ℕ} (ht1 : 0 < t) (ht2 : t < m) : zeta m ^ t ≠ 1 := by
  dsimp [zeta]
  rw [← Complex.exp_nat_mul]
  intro h
  have harg : (t : ℂ) * (2 * Real.pi * Complex.I / (m : ℂ)) =
      (((2 * Real.pi * (t : ℝ) / (m : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.exp_eq_one_iff] at h
  obtain ⟨q, hq⟩ := h
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi).ne'
  have hmul : (((2 * Real.pi * (t : ℝ) / (m : ℝ)) : ℝ) : ℂ) = (q : ℂ) * (2 * Real.pi : ℂ) := by
    apply mul_right_cancel₀ hI
    simpa [mul_assoc, mul_comm, mul_left_comm] using hq
  have hreal : 2 * Real.pi * (t : ℝ) / (m : ℝ) = (q : ℝ) * (2 * Real.pi) := by exact_mod_cast hmul
  have hqR : (t : ℝ) / (m : ℝ) = (q : ℝ) := by
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    field_simp [hpi] at hreal ⊢
    nlinarith [Real.pi_pos]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_trans ht1 ht2)
  have hlo : (0 : ℝ) < (q : ℝ) := by rw [← hqR]; exact div_pos (by exact_mod_cast ht1) hmpos
  have hhi : (q : ℝ) < 1 := by rw [← hqR, div_lt_one hmpos]; exact_mod_cast ht2
  have hq1 : (0 : ℤ) < q := by exact_mod_cast hlo
  have hq2 : q < 1 := by exact_mod_cast hhi
  omega

private lemma sum_zeta_pow {m d : ℕ} (hm : 0 < m) :
    ∑ j ∈ Finset.range m, (zeta m ^ d) ^ j = if m ∣ d then (m : ℂ) else 0 := by
  split_ifs with hd
  · obtain ⟨q, rfl⟩ := hd
    have h1 : zeta m ^ (m * q) = 1 := by rw [pow_mul, zeta_pow_self hm, one_pow]
    simp [h1]
  · have hne : zeta m ^ d ≠ 1 := by
      have hdiv : d = m * (d / m) + d % m := (Nat.div_add_mod d m).symm
      have hmod0 : 0 < d % m := Nat.pos_of_ne_zero (fun h => hd (Nat.dvd_of_mod_eq_zero h))
      have hmodlt : d % m < m := Nat.mod_lt d hm
      have hpow : zeta m ^ d = zeta m ^ (d % m) := by
        conv_lhs => rw [hdiv, pow_add, pow_mul, zeta_pow_self hm, one_pow, one_mul]
      rw [hpow]
      exact zeta_pow_ne_one hmod0 hmodlt
    have hgeom := geom_sum_mul (zeta m ^ d) m
    have htop : (zeta m ^ d) ^ m - 1 = 0 := by
      rw [← pow_mul, mul_comm, pow_mul, zeta_pow_self hm, one_pow, sub_self]
    rw [htop] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)

private noncomputable def g (k : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (M k), Complex.exp ((r k : ℂ) * zeta (M k) ^ j * z)

private noncomputable def gDeriv (n k : ℕ) (z : ℂ) : ℂ :=
  (r k : ℂ) ^ n * ∑ j ∈ Finset.range (M k),
    (zeta (M k) ^ j) ^ n * Complex.exp ((r k : ℂ) * zeta (M k) ^ j * z)

private lemma gDeriv_zero (k : ℕ) (z : ℂ) : gDeriv 0 k z = g k z := by
  simp [gDeriv, g]

private lemma hasDerivAt_gDeriv (n k : ℕ) (z : ℂ) :
    HasDerivAt (gDeriv n k) (gDeriv (n + 1) k z) z := by
  unfold gDeriv
  have hsum : HasDerivAt
      (fun w => ∑ j ∈ Finset.range (M k),
        (zeta (M k) ^ j) ^ n * Complex.exp ((r k : ℂ) * zeta (M k) ^ j * w))
      (∑ j ∈ Finset.range (M k),
        (zeta (M k) ^ j) ^ n * (Complex.exp ((r k : ℂ) * zeta (M k) ^ j * z) * ((r k : ℂ) * zeta (M k) ^ j)))
      z := by
    apply HasDerivAt.fun_sum
    intro j _
    have hlin : HasDerivAt (fun w : ℂ => (r k : ℂ) * zeta (M k) ^ j * w)
        ((r k : ℂ) * zeta (M k) ^ j) z := by
      simpa using (hasDerivAt_id z).const_mul ((r k : ℂ) * zeta (M k) ^ j)
    exact (hlin.cexp).const_mul ((zeta (M k) ^ j) ^ n)
  have hmul := hsum.const_mul ((r k : ℂ) ^ n)
  have hderiv_eq : (r k : ℂ) ^ n * ∑ j ∈ Finset.range (M k),
        (zeta (M k) ^ j) ^ n * (Complex.exp ((r k : ℂ) * zeta (M k) ^ j * z) * ((r k : ℂ) * zeta (M k) ^ j)) =
      (r k : ℂ) ^ (n + 1) * ∑ j ∈ Finset.range (M k),
        (zeta (M k) ^ j) ^ (n + 1) * Complex.exp ((r k : ℂ) * zeta (M k) ^ j * z) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ, pow_succ]
    ring
  rwa [hderiv_eq] at hmul

private lemma norm_gDeriv_le (n k : ℕ) (z : ℂ) :
    ‖gDeriv n k z‖ ≤ r k ^ n * (M k : ℝ) * Real.exp (r k * ‖z‖) := by
  unfold gDeriv
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (r_pos k).le]
  have hsum : ‖∑ j ∈ Finset.range (M k),
      (zeta (M k) ^ j) ^ n * Complex.exp ((r k : ℂ) * zeta (M k) ^ j * z)‖ ≤
      (M k : ℝ) * Real.exp (r k * ‖z‖) := by
    calc _ ≤ ∑ j ∈ Finset.range (M k),
            ‖(zeta (M k) ^ j) ^ n * Complex.exp ((r k : ℂ) * zeta (M k) ^ j * z)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range (M k), Real.exp (r k * ‖z‖) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_pow, norm_pow, norm_zeta, one_pow, one_pow, one_mul, Complex.norm_exp]
          apply Real.exp_le_exp.mpr
          have hre := Complex.re_le_norm ((r k : ℂ) * zeta (M k) ^ j * z)
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (r_pos k).le,
            norm_pow, norm_zeta, one_pow, mul_one] at hre
          exact hre
      _ = (M k : ℝ) * Real.exp (r k * ‖z‖) := by simp
  calc r k ^ n * ‖∑ j ∈ Finset.range (M k), _‖
      ≤ r k ^ n * ((M k : ℝ) * Real.exp (r k * ‖z‖)) :=
        mul_le_mul_of_nonneg_left hsum (pow_nonneg (r_pos k).le _)
    _ = r k ^ n * (M k : ℝ) * Real.exp (r k * ‖z‖) := by ring

private noncomputable def fDeriv (n : ℕ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, (c k : ℂ) * gDeriv n k z

private noncomputable def f (z : ℂ) : ℂ := fDeriv 0 z

private lemma exists_summable_bound (n : ℕ) (B : ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ k : ℕ, ∀ z ∈ Metric.ball (0 : ℂ) B,
      ‖(c k : ℂ) * gDeriv n k z‖ ≤ u k := by
  obtain ⟨K0, hK0⟩ := exists_nat_gt B
  set K := max n K0
  have hn_le_H : n ≤ Hmid (K + 1) := by
    have h1 : K + 1 ≤ Hmid (K + 1) := Hmid_strictMono.id_le (K + 1)
    omega
  let A : ℝ := c (K + 2) * r (K + 2) ^ n
  let u : ℕ → ℝ := fun k =>
    if k < K + 3 then c k * r k ^ n * (M k : ℝ) * Real.exp (r k * B)
    else A * (Real.exp (-100)) ^ k
  have hsum_geom : Summable (fun k : ℕ => A * (Real.exp (-100)) ^ k) := by
    apply Summable.mul_left
    apply summable_geometric_of_lt_one (Real.exp_pos _).le
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hsum_u : Summable u := by
    have hfin : {k : ℕ | u k ≠ A * (Real.exp (-100)) ^ k}.Finite := by
      apply (Set.finite_lt_nat (K + 3)).subset
      intro k hk
      simp only [Set.mem_ofPred_eq, u] at hk
      by_contra hge
      have hnot : ¬ k < K + 3 := hge
      rw [if_neg hnot] at hk
      exact hk rfl
    exact hsum_geom.congr_cofinite (Filter.eventually_cofinite.mpr (by simpa [ne_comm] using hfin))
  refine ⟨u, hsum_u, fun k z hz => ?_⟩
  have hzB : ‖z‖ ≤ B := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact hz.le
  have hnorm : ‖(c k : ℂ) * gDeriv n k z‖ ≤ c k * r k ^ n * (M k : ℝ) * Real.exp (r k * B) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (c_pos k).le]
    calc c k * ‖gDeriv n k z‖
        ≤ c k * (r k ^ n * (M k : ℝ) * Real.exp (r k * ‖z‖)) :=
          mul_le_mul_of_nonneg_left (norm_gDeriv_le n k z) (c_pos k).le
      _ ≤ c k * (r k ^ n * (M k : ℝ) * Real.exp (r k * B)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzB (r_pos k).le))
              (mul_nonneg (pow_nonneg (r_pos k).le _) (Nat.cast_nonneg _)))
            (c_pos k).le
      _ = c k * r k ^ n * (M k : ℝ) * Real.exp (r k * B) := by ring
  dsimp [u]
  split_ifs with hlt
  · exact hnorm
  · push Not at hlt
    have hBm : B ≤ (k : ℝ) + 4 := by
      have : (K0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show K0 ≤ k by omega)
      linarith
    have htail := weight_upper_tail_term K n k hn_le_H hlt hBm
    have hexp_eq : Real.exp (-100 * (k : ℝ)) = (Real.exp (-100)) ^ k := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hexp_eq] at htail
    exact hnorm.trans htail

private lemma summable_fDeriv (n : ℕ) (z : ℂ) :
    Summable (fun k : ℕ => (c k : ℂ) * gDeriv n k z) := by
  obtain ⟨u, hu, hbd⟩ := exists_summable_bound n (‖z‖ + 1)
  apply Summable.of_norm_bounded hu
  intro k
  exact hbd k z (by rw [Metric.mem_ball, dist_zero_right]; linarith)

private lemma hasDerivAt_fDeriv (n : ℕ) (z : ℂ) :
    HasDerivAt (fDeriv n) (fDeriv (n + 1) z) z := by
  set B := ‖z‖ + 1
  obtain ⟨u, hu, hbd⟩ := exists_summable_bound (n + 1) B
  have hz_mem : z ∈ Metric.ball (0 : ℂ) B := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have h0_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) B := by
    rw [Metric.mem_ball, dist_zero_right, norm_zero]; positivity
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) B).isPreconnected
    (fun k y _ => (hasDerivAt_gDeriv n k y).const_mul (c k : ℂ))
    hbd h0_mem (summable_fDeriv n 0) hz_mem

private lemma f_differentiable : Differentiable ℂ f :=
  fun z => (hasDerivAt_fDeriv 0 z).differentiableAt

private lemma iteratedDeriv_f (n : ℕ) : iteratedDeriv n f = fDeriv n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext z
    rw [iteratedDeriv_succ, ih]
    exact (hasDerivAt_fDeriv n z).deriv

/- ### Section 4: Transcendentality over `Polynomial ℂ` -/

private lemma g_real_nonneg_and_lower (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ (g k (x : ℂ)).re ∧ ∀ q : ℕ,
      (M k : ℝ) * (r k * x) ^ (q * M k) / ((q * M k).factorial : ℝ) ≤ (g k (x : ℂ)).re := by
  have hterm_sum : ∀ j ∈ Finset.range (M k),
      HasSum (fun m : ℕ => ((r k : ℂ) * zeta (M k) ^ j * (x : ℂ)) ^ m / (m.factorial : ℂ))
        (Complex.exp ((r k : ℂ) * zeta (M k) ^ j * (x : ℂ))) := by
    intro j _
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp ((r k : ℂ) * zeta (M k) ^ j * (x : ℂ))
  have hsum_all : HasSum (fun m : ℕ =>
      ∑ j ∈ Finset.range (M k), ((r k : ℂ) * zeta (M k) ^ j * (x : ℂ)) ^ m / (m.factorial : ℂ))
      (g k (x : ℂ)) :=
    hasSum_sum hterm_sum
  have hsimp : ∀ m : ℕ,
      (∑ j ∈ Finset.range (M k), ((r k : ℂ) * zeta (M k) ^ j * (x : ℂ)) ^ m / (m.factorial : ℂ)) =
      if M k ∣ m then ((((M k : ℝ) * (r k * x) ^ m / (m.factorial : ℝ)) : ℝ) : ℂ) else 0 := by
    intro m
    have h1 : ∀ j ∈ Finset.range (M k),
        ((r k : ℂ) * zeta (M k) ^ j * (x : ℂ)) ^ m / (m.factorial : ℂ) =
        (((r k * x) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) * (zeta (M k) ^ m) ^ j := by
      intro j _
      push_cast
      rw [mul_pow, mul_pow, ← pow_mul, mul_comm j m, pow_mul]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, sum_zeta_pow (M_pos k)]
    split_ifs <;> push_cast <;> ring
  have hre_hasSum : HasSum (fun m : ℕ =>
      if M k ∣ m then (M k : ℝ) * (r k * x) ^ m / (m.factorial : ℝ) else 0)
      (g k (x : ℂ)).re := by
    have h1 := Complex.reCLM.hasSum hsum_all
    refine h1.congr_fun fun m => ?_
    rw [Complex.reCLM_apply, hsimp m]
    split_ifs
    · exact (Complex.ofReal_re _).symm
    · exact Complex.zero_re.symm
  have hnonneg_term : ∀ m : ℕ,
      0 ≤ (if M k ∣ m then (M k : ℝ) * (r k * x) ^ m / (m.factorial : ℝ) else 0) := by
    intro m
    split_ifs
    · have : 0 ≤ r k * x := mul_nonneg (r_pos k).le hx
      positivity
    · exact le_rfl
  constructor
  · exact hre_hasSum.nonneg hnonneg_term
  · intro q
    have hle := hre_hasSum.summable.le_tsum (q * M k) (fun m _ => hnonneg_term m)
    rw [hre_hasSum.tsum_eq] at hle
    have hdvd : M k ∣ q * M k := dvd_mul_left (M k) q
    simpa [if_pos hdvd] using hle

private lemma poly_eval_upper (p : Polynomial ℂ) (x : ℝ) (hx : 1 ≤ x) :
    ‖p.eval (x : ℂ)‖ ≤ (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) * x ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc ‖∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x : ℂ) ^ i‖
      ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i * (x : ℂ) ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * x ^ p.natDegree := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ x)]
        have hle : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hle) (norm_nonneg _)
    _ = (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) * x ^ p.natDegree := by
        rw [Finset.sum_mul]

private lemma poly_eval_lower {p : Polynomial ℂ} (hp : p ≠ 0) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → (‖p.leadingCoeff‖ / 2) * x ^ p.natDegree ≤ ‖p.eval (x : ℂ)‖ := by
  set a := p.leadingCoeff
  have ha : 0 < ‖a‖ := norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  cases hd : p.natDegree with
  | zero =>
    refine ⟨1, le_rfl, fun x _ => ?_⟩
    have hp0 : p.eval (x : ℂ) = p.coeff 0 := by
      conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
      exact Polynomial.eval_C
    have ha0 : a = p.coeff 0 := by
      dsimp [a]; rw [Polynomial.leadingCoeff, hd]
    rw [hp0, ha0, pow_zero, mul_one]
    have hpos : 0 < ‖p.coeff 0‖ := by rwa [← ha0]
    linarith
  | succ d' =>
    set S := ∑ i ∈ Finset.range (d' + 1), ‖p.coeff i‖
    refine ⟨max 1 (2 * S / ‖a‖), le_max_left _ _, fun x hx => ?_⟩
    have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
    have hx0 : 0 ≤ x := by linarith
    have heval : p.eval (x : ℂ) = a * (x : ℂ) ^ (d' + 1) +
        ∑ i ∈ Finset.range (d' + 1), p.coeff i * (x : ℂ) ^ i := by
      rw [Polynomial.eval_eq_sum_range, hd, Finset.sum_range_succ, add_comm]
      congr 2
      dsimp [a]; rw [Polynomial.leadingCoeff, hd]
    have hlow : ‖∑ i ∈ Finset.range (d' + 1), p.coeff i * (x : ℂ) ^ i‖ ≤ S * x ^ d' := by
      calc _ ≤ ∑ i ∈ Finset.range (d' + 1), ‖p.coeff i * (x : ℂ) ^ i‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (d' + 1), ‖p.coeff i‖ * x ^ d' := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0]
            have hi' : i ≤ d' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 hi') (norm_nonneg _)
        _ = S * x ^ d' := by rw [Finset.sum_mul]
    have hlead : ‖a * (x : ℂ) ^ (d' + 1)‖ = ‖a‖ * x ^ (d' + 1) := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0]
    have htri : ‖a * (x : ℂ) ^ (d' + 1)‖ - ‖∑ i ∈ Finset.range (d' + 1), p.coeff i * (x : ℂ) ^ i‖ ≤
        ‖p.eval (x : ℂ)‖ := by
      rw [heval]
      have := norm_add_le (a * (x : ℂ) ^ (d' + 1) + ∑ i ∈ Finset.range (d' + 1), p.coeff i * (x : ℂ) ^ i)
        (- ∑ i ∈ Finset.range (d' + 1), p.coeff i * (x : ℂ) ^ i)
      simp only [add_neg_cancel_right, norm_neg] at this
      linarith
    have hSx : S ≤ (‖a‖ / 2) * x := by
      have h1 : 2 * S / ‖a‖ ≤ x := (le_max_right _ _).trans hx
      have h2 := (div_le_iff₀ ha).mp h1
      linarith
    have hSxd : S * x ^ d' ≤ (‖a‖ / 2) * x ^ (d' + 1) := by
      rw [pow_succ]
      have : S * x ^ d' ≤ ((‖a‖ / 2) * x) * x ^ d' :=
        mul_le_mul_of_nonneg_right hSx (pow_nonneg hx0 _)
      linarith
    linarith

private lemma f_transcendental : Transcendental (Polynomial ℂ) f := by
  intro ⟨P, hP_ne, hP_eval⟩
  have hP_at : ∀ z : ℂ, ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j).eval z * (f z) ^ j = 0 := by
    intro z
    have h1 : (Polynomial.aeval f P) z = 0 := by rw [hP_eval]; rfl
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_apply] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Pi.mul_apply, Pi.pow_apply, Polynomial.algebraMap_algebraPi,
      Polynomial.coe_aeval_eq_eval]
  set d := P.natDegree
  have hpd_ne : P.coeff d ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP_ne
  obtain ⟨X, hX1, hpd_low⟩ := poly_eval_lower hpd_ne
  have ha_pos : 0 < ‖(P.coeff d).leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hpd_ne)
  cases hd : d with
  | zero =>
    have h0 := hP_at (X : ℂ)
    rw [hd, Finset.sum_range_one, pow_zero, mul_one] at h0
    have hlow := hpd_low X le_rfl
    rw [hd, h0, norm_zero] at hlow
    have hpos : 0 < ‖(P.coeff 0).leadingCoeff‖ / 2 * X ^ (P.coeff 0).natDegree := by
      have : 0 < ‖(P.coeff 0).leadingCoeff‖ := by rwa [← hd]
      positivity
    linarith
  | succ d' =>
    set D := (Finset.range (d' + 1)).sup (fun j => (P.coeff j).natDegree)
    set Csum := ∑ j ∈ Finset.range (d' + 1),
      ∑ i ∈ Finset.range ((P.coeff j).natDegree + 1), ‖(P.coeff j).coeff i‖
    have hbound_all : ∀ x : ℝ, X ≤ x → ‖f (x : ℂ)‖ ≤ max 1 (2 * Csum / ‖(P.coeff d).leadingCoeff‖) * x ^ D := by
      intro x hxX
      have hx1' : 1 ≤ x := hX1.trans hxX
      by_cases hfx1 : ‖f (x : ℂ)‖ ≤ 1
      · calc ‖f (x : ℂ)‖ ≤ 1 := hfx1
          _ = 1 * 1 := (mul_one 1).symm
          _ ≤ max 1 (2 * Csum / ‖(P.coeff d).leadingCoeff‖) * x ^ D :=
              mul_le_mul (le_max_left _ _) (one_le_pow₀ hx1') zero_le_one (le_trans zero_le_one (le_max_left _ _))
      · push Not at hfx1
        have h0 := hP_at (x : ℂ)
        rw [hd, Finset.sum_range_succ] at h0
        have hlead_eq : (P.coeff (d' + 1)).eval (x : ℂ) * (f (x : ℂ)) ^ (d' + 1) =
            - ∑ j ∈ Finset.range (d' + 1), (P.coeff j).eval (x : ℂ) * (f (x : ℂ)) ^ j :=
          eq_neg_of_add_eq_zero_right h0
        have hrhs : ‖∑ j ∈ Finset.range (d' + 1), (P.coeff j).eval (x : ℂ) * (f (x : ℂ)) ^ j‖ ≤
            Csum * x ^ D * ‖f (x : ℂ)‖ ^ d' := by
          calc _ ≤ ∑ j ∈ Finset.range (d' + 1), ‖(P.coeff j).eval (x : ℂ) * (f (x : ℂ)) ^ j‖ :=
                norm_sum_le _ _
            _ ≤ ∑ j ∈ Finset.range (d' + 1),
                  ((∑ i ∈ Finset.range ((P.coeff j).natDegree + 1), ‖(P.coeff j).coeff i‖) * x ^ D) *
                  ‖f (x : ℂ)‖ ^ d' := by
                refine Finset.sum_le_sum fun j hj => ?_
                rw [norm_mul, norm_pow]
                apply mul_le_mul
                · calc ‖(P.coeff j).eval (x : ℂ)‖
                      ≤ (∑ i ∈ Finset.range ((P.coeff j).natDegree + 1), ‖(P.coeff j).coeff i‖) *
                          x ^ (P.coeff j).natDegree := poly_eval_upper (P.coeff j) x hx1'
                    _ ≤ (∑ i ∈ Finset.range ((P.coeff j).natDegree + 1), ‖(P.coeff j).coeff i‖) * x ^ D := by
                        apply mul_le_mul_of_nonneg_left
                        · exact pow_le_pow_right₀ hx1' (Finset.le_sup (f := fun j => (P.coeff j).natDegree) hj)
                        · exact Finset.sum_nonneg fun _ _ => norm_nonneg _
                · exact pow_le_pow_right₀ hfx1.le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
                · positivity
                · positivity
            _ = Csum * x ^ D * ‖f (x : ℂ)‖ ^ d' := by
                rw [← Finset.sum_mul, ← Finset.sum_mul]
        have hlhs : (‖(P.coeff d).leadingCoeff‖ / 2) * ‖f (x : ℂ)‖ ^ (d' + 1) ≤
            ‖(P.coeff (d' + 1)).eval (x : ℂ) * (f (x : ℂ)) ^ (d' + 1)‖ := by
          rw [norm_mul, norm_pow, ← hd]
          have h1 := hpd_low x hxX
          have h2 : (1 : ℝ) ≤ x ^ (P.coeff d).natDegree := one_le_pow₀ hx1'
          have h3 : ‖(P.coeff d).leadingCoeff‖ / 2 ≤ ‖(P.coeff d).eval (x : ℂ)‖ := by
            calc ‖(P.coeff d).leadingCoeff‖ / 2
                = (‖(P.coeff d).leadingCoeff‖ / 2) * 1 := (mul_one _).symm
              _ ≤ (‖(P.coeff d).leadingCoeff‖ / 2) * x ^ (P.coeff d).natDegree :=
                  mul_le_mul_of_nonneg_left h2 (by positivity)
              _ ≤ ‖(P.coeff d).eval (x : ℂ)‖ := h1
          exact mul_le_mul_of_nonneg_right h3 (by positivity)
        rw [hlead_eq, norm_neg] at hlhs
        have hcmp : (‖(P.coeff d).leadingCoeff‖ / 2) * ‖f (x : ℂ)‖ ^ (d' + 1) ≤
            Csum * x ^ D * ‖f (x : ℂ)‖ ^ d' := hlhs.trans hrhs
        rw [pow_succ, ← mul_assoc] at hcmp
        have hpos_pow : 0 < ‖f (x : ℂ)‖ ^ d' := by positivity
        have hcancel : (‖(P.coeff d).leadingCoeff‖ / 2) * ‖f (x : ℂ)‖ ≤ Csum * x ^ D := by
          nlinarith
        have hdiv : ‖f (x : ℂ)‖ ≤ (2 * Csum / ‖(P.coeff d).leadingCoeff‖) * x ^ D := by
          have : (‖(P.coeff d).leadingCoeff‖ / 2) * ‖f (x : ℂ)‖ ≤
              (‖(P.coeff d).leadingCoeff‖ / 2) * ((2 * Csum / ‖(P.coeff d).leadingCoeff‖) * x ^ D) := by
            have heq : (‖(P.coeff d).leadingCoeff‖ / 2) * ((2 * Csum / ‖(P.coeff d).leadingCoeff‖) * x ^ D) =
                Csum * x ^ D := by field_simp [ha_pos.ne']
            rw [heq]; exact hcancel
          nlinarith
        exact hdiv.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    -- Now pick a huge x ≥ X using the direct superpoly bound!
    set m := (D + 1) * M 0
    have hm_ge : D + 1 ≤ m := Nat.le_mul_of_pos_right _ (M_pos 0)
    set K0 := (M 0 : ℝ) * (r 0) ^ m / (m.factorial : ℝ)
    have hK0_pos : 0 < K0 := by
      have := M_pos 0; have := r_pos 0; positivity
    set B0 := max 1 (2 * Csum / ‖(P.coeff d).leadingCoeff‖)
    set y := max X (B0 / K0 + 1)
    have hyX : X ≤ y := le_max_left _ _
    have hy1 : 1 ≤ y := hX1.trans hyX
    have hsum_re : HasSum (fun k : ℕ => c k * (g k (y : ℂ)).re) (f (y : ℂ)).re := by
      have h1 := Complex.reCLM.hasSum (summable_fDeriv 0 (y : ℂ)).hasSum
      refine h1.congr_fun fun k => ?_
      rw [Complex.reCLM_apply, gDeriv_zero, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    have hfy_ge : K0 * y ^ m ≤ ‖f (y : ℂ)‖ := by
      have h0 := hsum_re.summable.le_tsum 0 (fun k _ => mul_nonneg (c_pos k).le (g_real_nonneg_and_lower k y (by linarith)).1)
      rw [hsum_re.tsum_eq] at h0
      have hg0 := (g_real_nonneg_and_lower 0 y (by linarith)).2 (D + 1)
      have hrew : (M 0 : ℝ) * (r 0 * y) ^ m / (m.factorial : ℝ) = K0 * y ^ m := by
        dsimp [K0]; rw [mul_pow]; ring
      have hc0 : c 0 = 1 := rfl
      rw [hc0, one_mul] at h0
      exact le_trans (by linarith) (Complex.re_le_norm _)
    have hfy_le := hbound_all y hyX
    have hym : y ^ (D + 1) ≤ y ^ m := pow_le_pow_right₀ hy1 hm_ge
    have hB0_lt : B0 < K0 * y := by
      have : B0 / K0 < y := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
      linarith [(div_lt_iff₀ hK0_pos).mp this]
    have hcontr : B0 * y ^ D < K0 * y ^ m := by
      calc B0 * y ^ D < (K0 * y) * y ^ D := mul_lt_mul_of_pos_right hB0_lt (pow_pos (by linarith) D)
        _ = K0 * y ^ (D + 1) := by rw [pow_succ]; ring
        _ ≤ K0 * y ^ m := mul_le_mul_of_nonneg_left hym hK0_pos.le
    linarith

/- ### Section 5: Single-block Rouche localization -/

private noncomputable def rayAngle (b j : ℕ) : ℝ :=
  -((2 * (j : ℝ) + 1) * Real.pi / (M b : ℝ))

private noncomputable def delta (b : ℕ) : ℝ :=
  1 / (4 * r b * Real.sin (Real.pi / (M b : ℝ)))

private lemma sin_pi_div_M_pos (b : ℕ) : 0 < Real.sin (Real.pi / (M b : ℝ)) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · have := M_pos b; positivity
  · have hM : (2 : ℝ) ≤ (M b : ℝ) := by exact_mod_cast (le_trans (by norm_num) (M_ge_256 b))
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [Real.pi_pos]

private lemma sin_pi_div_M_ge (b : ℕ) : (2 : ℝ) / (M b : ℝ) ≤ Real.sin (Real.pi / (M b : ℝ)) := by
  have hM : (2 : ℝ) ≤ (M b : ℝ) := by exact_mod_cast (le_trans (by norm_num) (M_ge_256 b))
  have hle : Real.pi / (M b : ℝ) ≤ Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le two_pos hM
  have h1 := Real.mul_le_sin (by positivity) hle
  have hrew : 2 / Real.pi * (Real.pi / (M b : ℝ)) = 2 / (M b : ℝ) := by
    field_simp [Real.pi_pos.ne']
  rwa [hrew] at h1

private lemma delta_pos (b : ℕ) : 0 < delta b := by
  dsimp [delta]
  have := r_pos b
  have := sin_pi_div_M_pos b
  positivity

private lemma delta_le (b : ℕ) : delta b ≤ (M b : ℝ) / (8 * r b) := by
  dsimp [delta]
  have hr := r_pos b
  have hM : (0 : ℝ) < (M b : ℝ) := by exact_mod_cast M_pos b
  have hsin := sin_pi_div_M_ge b
  rw [div_le_div_iff₀ (by have := sin_pi_div_M_pos b; positivity) (by positivity)]
  have h1 : 4 * r b * (2 / (M b : ℝ)) ≤ 4 * r b * Real.sin (Real.pi / (M b : ℝ)) :=
    mul_le_mul_of_nonneg_left hsin (by positivity)
  have h2 : 8 * r b ≤ (M b : ℝ) * (4 * r b * Real.sin (Real.pi / (M b : ℝ))) := by
    have : 8 * r b = (M b : ℝ) * (4 * r b * (2 / (M b : ℝ))) := by field_simp [hM.ne']; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h1 hM.le
  linarith

private lemma delta_lt_eps (b : ℕ) : delta b < ε b / 64 := by
  have h1 := delta_le b
  have hr : 2 * ((M b : ℝ) ^ 3) * (4 : ℝ) ^ (b + 1) ≤ r b := by
    dsimp [r]; exact_mod_cast rNat_ge_cube b
  have hM : (256 : ℝ) ≤ (M b : ℝ) := by exact_mod_cast M_ge_256 b
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ (b + 1) := by positivity
  have hε : ε b = 1 / (4 : ℝ) ^ (b + 1) := by dsimp [ε]; rw [one_div_pow]
  rw [hε]
  have hr_pos := r_pos b
  have hstep : (M b : ℝ) / (8 * r b) < (1 / (4 : ℝ) ^ (b + 1)) / 64 := by
    rw [div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hMsq : (256 : ℝ) * 256 ≤ (M b : ℝ) ^ 2 := by nlinarith
    have hM2 : 64 * (M b : ℝ) < 16 * (M b : ℝ) ^ 3 := by nlinarith
    have h16 : 16 * (M b : ℝ) ^ 3 * (4 : ℝ) ^ (b + 1) ≤ 8 * r b := by linarith
    nlinarith [mul_lt_mul_of_pos_right hM2 h4pos]
  linarith

private lemma cos_pi_div_M_sub_cos_three (b : ℕ) :
    (16 : ℝ) / (M b : ℝ) ^ 2 ≤ Real.cos (Real.pi / (M b : ℝ)) - Real.cos (3 * Real.pi / (M b : ℝ)) := by
  have hM : (256 : ℝ) ≤ (M b : ℝ) := by exact_mod_cast M_ge_256 b
  have hMpos : (0 : ℝ) < (M b : ℝ) := by linarith
  have htrig : Real.cos (Real.pi / (M b : ℝ)) - Real.cos (3 * Real.pi / (M b : ℝ)) =
      2 * Real.sin (2 * Real.pi / (M b : ℝ)) * Real.sin (Real.pi / (M b : ℝ)) := by
    rw [Real.cos_sub_cos]
    have h1 : (Real.pi / (M b : ℝ) + 3 * Real.pi / (M b : ℝ)) / 2 = 2 * Real.pi / (M b : ℝ) := by ring
    have h2 : (Real.pi / (M b : ℝ) - 3 * Real.pi / (M b : ℝ)) / 2 = -(Real.pi / (M b : ℝ)) := by ring
    rw [h1, h2, Real.sin_neg]
    ring
  rw [htrig]
  have hs1 : 2 / (M b : ℝ) ≤ Real.sin (Real.pi / (M b : ℝ)) := sin_pi_div_M_ge b
  have hs2 : 4 / (M b : ℝ) ≤ Real.sin (2 * Real.pi / (M b : ℝ)) := by
    have hle : 2 * Real.pi / (M b : ℝ) ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hMpos two_pos]
      nlinarith [Real.pi_pos]
    have h1 := Real.mul_le_sin (by positivity) hle
    have hrew : 2 / Real.pi * (2 * Real.pi / (M b : ℝ)) = 4 / (M b : ℝ) := by
      field_simp [Real.pi_pos.ne']; ring
    rwa [hrew] at h1
  calc 16 / (M b : ℝ) ^ 2 = 2 * (4 / (M b : ℝ)) * (2 / (M b : ℝ)) := by ring
    _ ≤ 2 * Real.sin (2 * Real.pi / (M b : ℝ)) * Real.sin (Real.pi / (M b : ℝ)) := by
        have hs2_nn : 0 ≤ Real.sin (2 * Real.pi / (M b : ℝ)) := le_trans (by positivity) hs2
        nlinarith [mul_le_mul hs2 hs1 (by positivity) hs2_nn]

private noncomputable def twoTerm (n b j : ℕ) (z : ℂ) : ℂ :=
  (c b : ℂ) * (r b : ℂ) ^ n *
    ((zeta (M b) ^ j) ^ n * Complex.exp ((r b : ℂ) * zeta (M b) ^ j * z) +
     (zeta (M b) ^ (j + 1)) ^ n * Complex.exp ((r b : ℂ) * zeta (M b) ^ (j + 1) * z))

private lemma twoTerm_differentiable (n b j : ℕ) : Differentiable ℂ (twoTerm n b j) := by
  unfold twoTerm
  fun_prop

private lemma zeta_mul_rayAngle (b j : ℕ) :
    zeta (M b) ^ j * Complex.exp (Complex.I * (rayAngle b j : ℂ)) =
      Complex.exp (-((Real.pi / (M b : ℝ) : ℝ) : ℂ) * Complex.I) ∧
    zeta (M b) ^ (j + 1) * Complex.exp (Complex.I * (rayAngle b j : ℂ)) =
      Complex.exp (((Real.pi / (M b : ℝ) : ℝ) : ℂ) * Complex.I) := by
  dsimp [zeta, rayAngle]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
  have hM : ((M b : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (M_pos b).ne'
  constructor
  · congr 1; push_cast; field_simp [hM]; ring
  · congr 1; push_cast; field_simp [hM]; ring

private lemma zeta_diff_mul_rayAngle (b j : ℕ) :
    (zeta (M b) ^ (j + 1) - zeta (M b) ^ j) * Complex.exp (Complex.I * (rayAngle b j : ℂ)) =
      (2 * Real.sin (Real.pi / (M b : ℝ)) : ℝ) * Complex.I := by
  have ⟨h1, h2⟩ := zeta_mul_rayAngle b j
  rw [sub_mul, h1, h2]
  rw [Complex.exp_mul_I, show -((Real.pi / (M b : ℝ) : ℝ) : ℂ) * Complex.I =
      (-((Real.pi / (M b : ℝ) : ℝ) : ℂ)) * Complex.I by ring,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sin]
  ring

private lemma norm_zeta_diff (b j : ℕ) :
    ‖zeta (M b) ^ (j + 1) - zeta (M b) ^ j‖ = 2 * Real.sin (Real.pi / (M b : ℝ)) := by
  have h := zeta_diff_mul_rayAngle b j
  have h1 : ‖Complex.exp (Complex.I * (rayAngle b j : ℂ))‖ = 1 := by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  calc ‖zeta (M b) ^ (j + 1) - zeta (M b) ^ j‖
      = ‖(zeta (M b) ^ (j + 1) - zeta (M b) ^ j) * Complex.exp (Complex.I * (rayAngle b j : ℂ))‖ := by
        rw [norm_mul, h1, mul_one]
    _ = ‖((2 * Real.sin (Real.pi / (M b : ℝ)) : ℝ) : ℂ) * Complex.I‖ := by rw [h]
    _ = 2 * Real.sin (Real.pi / (M b : ℝ)) := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (by linarith [sin_pi_div_M_pos b])]

private lemma exists_twoTerm_zero (n b j : ℕ) (ρ : ℝ) :
    ∃ ρs : ℝ, |ρs - ρ| ≤ Real.pi / (2 * r b * Real.sin (Real.pi / (M b : ℝ))) ∧
      twoTerm n b j ((ρs : ℂ) * Complex.exp (Complex.I * (rayAngle b j : ℂ))) = 0 := by
  set α := 2 * r b * Real.sin (Real.pi / (M b : ℝ))
  have hα : 0 < α := by
    have := r_pos b; have := sin_pi_div_M_pos b; positivity
  set θ := Real.pi - 2 * Real.pi * (n : ℝ) / (M b : ℝ)
  set m : ℤ := round ((α * ρ - θ) / (2 * Real.pi))
  set ρs := (θ + 2 * Real.pi * (m : ℝ)) / α
  refine ⟨ρs, ?_, ?_⟩
  · have hround : |(α * ρ - θ) / (2 * Real.pi) - (m : ℝ)| ≤ 1 / 2 := abs_sub_round _
    have hdiff : ρs - ρ = -(((α * ρ - θ) / (2 * Real.pi) - (m : ℝ)) * (2 * Real.pi)) / α := by
      dsimp [ρs]
      field_simp [hα.ne', Real.pi_pos.ne']
      ring
    rw [hdiff, abs_div, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      abs_of_pos hα]
    calc |(α * ρ - θ) / (2 * Real.pi) - (m : ℝ)| * (2 * Real.pi) / α
        ≤ (1 / 2) * (2 * Real.pi) / α := by
          apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hround (by positivity)) hα.le
      _ = Real.pi / α := by ring
  · set zs : ℂ := (ρs : ℂ) * Complex.exp (Complex.I * (rayAngle b j : ℂ))
    unfold twoTerm
    have hpow : (zeta (M b) ^ (j + 1)) ^ n = (zeta (M b) ^ j) ^ n * zeta (M b) ^ n := by
      rw [pow_succ, mul_pow]
    have hexp_diff : Complex.exp ((r b : ℂ) * zeta (M b) ^ (j + 1) * zs) =
        Complex.exp ((r b : ℂ) * zeta (M b) ^ j * zs) *
          Complex.exp ((r b : ℂ) * (zeta (M b) ^ (j + 1) - zeta (M b) ^ j) * zs) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [hpow, hexp_diff]
    have hfactor : zeta (M b) ^ n *
        Complex.exp ((r b : ℂ) * (zeta (M b) ^ (j + 1) - zeta (M b) ^ j) * zs) = -1 := by
      have harg : (r b : ℂ) * (zeta (M b) ^ (j + 1) - zeta (M b) ^ j) * zs =
          ((α * ρs : ℝ) : ℂ) * Complex.I := by
        dsimp [zs, α]
        have hzd := zeta_diff_mul_rayAngle b j
        calc (r b : ℂ) * (zeta (M b) ^ (j + 1) - zeta (M b) ^ j) *
              ((ρs : ℂ) * Complex.exp (Complex.I * (rayAngle b j : ℂ)))
            = (r b : ℂ) * (ρs : ℂ) * ((zeta (M b) ^ (j + 1) - zeta (M b) ^ j) *
                Complex.exp (Complex.I * (rayAngle b j : ℂ))) := by ring
          _ = (r b : ℂ) * (ρs : ℂ) * (((2 * Real.sin (Real.pi / (M b : ℝ)) : ℝ) : ℂ) * Complex.I) := by
              rw [hzd]
          _ = ((2 * r b * Real.sin (Real.pi / (M b : ℝ)) * ρs : ℝ) : ℂ) * Complex.I := by
              push_cast; ring
      rw [harg]
      dsimp [zeta]
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      have hsum_arg : (n : ℂ) * (2 * Real.pi * Complex.I / (M b : ℂ)) + ((α * ρs : ℝ) : ℂ) * Complex.I =
          Real.pi * Complex.I + (m : ℂ) * (2 * Real.pi * Complex.I) := by
        have hαρ : α * ρs = θ + 2 * Real.pi * (m : ℝ) := mul_div_cancel₀ _ hα.ne'
        rw [hαρ]
        dsimp [θ]
        push_cast
        ring
      rw [hsum_arg, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have heq : (zeta (M b) ^ j) ^ n * Complex.exp ((r b : ℂ) * zeta (M b) ^ j * zs) +
        (zeta (M b) ^ j) ^ n * zeta (M b) ^ n *
          (Complex.exp ((r b : ℂ) * zeta (M b) ^ j * zs) *
            Complex.exp ((r b : ℂ) * (zeta (M b) ^ (j + 1) - zeta (M b) ^ j) * zs)) =
        (zeta (M b) ^ j) ^ n * Complex.exp ((r b : ℂ) * zeta (M b) ^ j * zs) *
          (1 + zeta (M b) ^ n * Complex.exp ((r b : ℂ) * (zeta (M b) ^ (j + 1) - zeta (M b) ^ j) * zs)) := by
      ring
    rw [heq, hfactor]
    ring

private lemma twoTerm_norm_on_circle (n b j : ℕ) {z₀ z : ℂ}
    (hzero : twoTerm n b j z₀ = 0) (hdist : ‖z - z₀‖ = delta b) :
    (1 / 4 : ℝ) * c b * r b ^ n * Real.exp (r b * (zeta (M b) ^ j * z).re) ≤
      ‖twoTerm n b j z‖ := by
  have hcb : (c b : ℂ) ≠ 0 := by exact_mod_cast (c_pos b).ne'
  have hrb : (r b : ℂ) ^ n ≠ 0 := pow_ne_zero n (by exact_mod_cast (r_pos b).ne')
  have hzj : (zeta (M b) ^ j) ^ n ≠ 0 := by
    intro h
    have := congrArg norm h
    rw [norm_pow, norm_pow, norm_zeta, one_pow, one_pow, norm_zero] at this
    norm_num at this
  have hpow : (zeta (M b) ^ (j + 1)) ^ n = (zeta (M b) ^ j) ^ n * zeta (M b) ^ n := by
    rw [pow_succ, mul_pow]
  have hfact_any : ∀ u : ℂ, twoTerm n b j u =
      (c b : ℂ) * (r b : ℂ) ^ n * (zeta (M b) ^ j) ^ n * Complex.exp ((r b : ℂ) * zeta (M b) ^ j * u) *
        (1 + zeta (M b) ^ n * Complex.exp ((r b : ℂ) * (zeta (M b) ^ (j + 1) - zeta (M b) ^ j) * u)) := by
    intro u
    unfold twoTerm
    rw [hpow]
    have he : Complex.exp ((r b : ℂ) * zeta (M b) ^ (j + 1) * u) =
        Complex.exp ((r b : ℂ) * zeta (M b) ^ j * u) *
          Complex.exp ((r b : ℂ) * (zeta (M b) ^ (j + 1) - zeta (M b) ^ j) * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [he]; ring
  have hz0_eq := hfact_any z₀
  rw [hzero] at hz0_eq
  have hpre_ne : (c b : ℂ) * (r b : ℂ) ^ n * (zeta (M b) ^ j) ^ n *
      Complex.exp ((r b : ℂ) * zeta (M b) ^ j * z₀) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hcb hrb) hzj) (Complex.exp_ne_zero _)
  have h1_plus : 1 + zeta (M b) ^ n *
      Complex.exp ((r b : ℂ) * (zeta (M b) ^ (j + 1) - zeta (M b) ^ j) * z₀) = 0 :=
    (mul_eq_zero.mp hz0_eq.symm).resolve_left hpre_ne
  have hneg1 : zeta (M b) ^ n *
      Complex.exp ((r b : ℂ) * (zeta (M b) ^ (j + 1) - zeta (M b) ^ j) * z₀) = -1 := by
    linear_combination h1_plus
  set w : ℂ := (r b : ℂ) * (zeta (M b) ^ (j + 1) - zeta (M b) ^ j) * (z - z₀)
  have h1_sub : 1 + zeta (M b) ^ n *
      Complex.exp ((r b : ℂ) * (zeta (M b) ^ (j + 1) - zeta (M b) ^ j) * z) = 1 - Complex.exp w := by
    have he : Complex.exp ((r b : ℂ) * (zeta (M b) ^ (j + 1) - zeta (M b) ^ j) * z) =
        Complex.exp ((r b : ℂ) * (zeta (M b) ^ (j + 1) - zeta (M b) ^ j) * z₀) * Complex.exp w := by
      rw [← Complex.exp_add]; congr 1; dsimp [w]; ring
    rw [he, ← mul_assoc, hneg1]
    ring
  have hw_norm : ‖w‖ = 1 / 2 := by
    dsimp [w]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (r_pos b).le,
      norm_zeta_diff b j, hdist]
    dsimp [delta]
    field_simp [(r_pos b).ne', (sin_pi_div_M_pos b).ne']
    ring
  rw [hfact_any z, h1_sub, norm_mul, norm_mul, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (c_pos b).le,
    norm_pow, Complex.norm_real, Real.norm_of_nonneg (r_pos b).le,
    norm_pow, norm_pow, norm_zeta, one_pow, one_pow, mul_one, Complex.norm_exp]
  have hre : ((r b : ℂ) * zeta (M b) ^ j * z).re = r b * (zeta (M b) ^ j * z).re := by
    rw [mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [hre]
  have hlow := one_sub_exp_norm_ge hw_norm
  have hnn : 0 ≤ c b * r b ^ n * Real.exp (r b * (zeta (M b) ^ j * z).re) := by
    have := c_pos b; have := r_pos b; positivity
  calc (1 / 4 : ℝ) * c b * r b ^ n * Real.exp (r b * (zeta (M b) ^ j * z).re)
      = c b * r b ^ n * Real.exp (r b * (zeta (M b) ^ j * z).re) * (1 / 4) := by ring
    _ ≤ c b * r b ^ n * Real.exp (r b * (zeta (M b) ^ j * z).re) * ‖1 - Complex.exp w‖ :=
        mul_le_mul_of_nonneg_left hlow hnn

private lemma cos_other_ray_le (b j l : ℕ) (hj : j < M b) (hl : l < M b)
    (hl1 : l ≠ j) (hl2 : l ≠ (j + 1) % M b) :
    Real.cos ((2 * (l : ℝ) - (2 * (j : ℝ) + 1)) * Real.pi / (M b : ℝ)) ≤
      Real.cos (3 * Real.pi / (M b : ℝ)) := by
  set m := M b
  have hm : 256 ≤ m := M_ge_256 b
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (M_pos b)
  set t := if j ≤ l then l - j else l + m - j
  have hmod_cases : (j + 1 < m ∧ (j + 1) % m = j + 1) ∨ (j + 1 = m ∧ (j + 1) % m = 0) := by
    by_cases hlast : j + 1 < m
    · exact Or.inl ⟨hlast, Nat.mod_eq_of_lt hlast⟩
    · have heq : j + 1 = m := by omega
      exact Or.inr ⟨heq, by rw [heq, Nat.mod_self]⟩
  have ht_ge : 2 ≤ t := by
    dsimp [t]
    split_ifs with hjl
    · rcases hmod_cases with ⟨_, hmod⟩ | ⟨heq, _⟩
      · rw [hmod] at hl2; omega
      · omega
    · rcases hmod_cases with ⟨_, _⟩ | ⟨heq, hmod⟩
      · omega
      · rw [hmod] at hl2; omega
  have ht_lt : t < m := by
    dsimp [t]; split_ifs <;> omega
  have hcos_eq : Real.cos ((2 * (l : ℝ) - (2 * (j : ℝ) + 1)) * Real.pi / (m : ℝ)) =
      Real.cos ((2 * (t : ℝ) - 1) * Real.pi / (m : ℝ)) := by
    by_cases hjl : j ≤ l
    · have ht_eq : t = l - j := if_pos hjl
      have hR : (l : ℝ) - (j : ℝ) = (t : ℝ) := by
        have hZ : (l : ℤ) - (j : ℤ) = (t : ℤ) := by omega
        exact_mod_cast hZ
      congr 1; field_simp [hmpos.ne']; nlinarith [Real.pi_pos]
    · have ht_eq : t = l + m - j := if_neg hjl
      have hR : (l : ℝ) - (j : ℝ) = (t : ℝ) - (m : ℝ) := by
        have hZ : (l : ℤ) - (j : ℤ) = (t : ℤ) - (m : ℤ) := by omega
        exact_mod_cast hZ
      have hdiff : (2 * (l : ℝ) - (2 * (j : ℝ) + 1)) * Real.pi / (m : ℝ) =
          (2 * (t : ℝ) - 1) * Real.pi / (m : ℝ) + (-1 : ℤ) * (2 * Real.pi) := by
        push_cast; field_simp [hmpos.ne']; nlinarith [Real.pi_pos]
      rw [hdiff, Real.cos_add_int_mul_two_pi]
  rw [hcos_eq]
  set θ := (2 * (t : ℝ) - 1) * Real.pi / (m : ℝ)
  have hlo : 3 * Real.pi / (m : ℝ) ≤ θ := by
    dsimp [θ]
    apply div_le_div_of_nonneg_right _ hmpos.le
    have : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_ge
    nlinarith [Real.pi_pos]
  have hhi : θ ≤ 2 * Real.pi - 3 * Real.pi / (m : ℝ) := by
    dsimp [θ]
    have ht_le : (t : ℝ) ≤ (m : ℝ) - 1 := by
      have : t + 1 ≤ m := ht_lt
      exact_mod_cast (show (t : ℤ) ≤ (m : ℤ) - 1 by omega)
    rw [le_sub_iff_add_le, ← add_div, div_le_iff₀ hmpos]
    nlinarith [Real.pi_pos]
  by_cases hpi : θ ≤ Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hpi hlo
  · push Not at hpi
    have hsym : Real.cos θ = Real.cos (2 * Real.pi - θ) := by
      rw [← Real.cos_neg (2 * Real.pi - θ)]
      have : -(2 * Real.pi - θ) = θ + (-1 : ℤ) * (2 * Real.pi) := by push_cast; ring
      rw [this, Real.cos_add_int_mul_two_pi]
    rw [hsym]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)

private lemma rest_of_block_bound (n b j : ℕ) (hj : j < M b) {ρs : ℝ}
    (hρs : ε b / 16 ≤ ρs) {z : ℂ}
    (hdist : ‖z - (ρs : ℂ) * Complex.exp (Complex.I * (rayAngle b j : ℂ))‖ = delta b) :
    ‖(c b : ℂ) * gDeriv n b z - twoTerm n b j z‖ ≤
      (1 / 16 : ℝ) * c b * r b ^ n * Real.exp (r b * (zeta (M b) ^ j * z).re) := by
  set z₀ : ℂ := (ρs : ℂ) * Complex.exp (Complex.I * (rayAngle b j : ℂ))
  set j1 := (j + 1) % M b
  have hj1_lt : j1 < M b := Nat.mod_lt _ (M_pos b)
  have hj1_ne : j1 ≠ j := by
    dsimp [j1]
    by_cases hlast : j + 1 < M b
    · rw [Nat.mod_eq_of_lt hlast]; omega
    · have heq : j + 1 = M b := by omega
      rw [heq, Nat.mod_self]
      have := M_ge_256 b; omega
  have hzeta_j1 : zeta (M b) ^ (j + 1) = zeta (M b) ^ j1 := by
    dsimp [j1]
    by_cases hlast : j + 1 < M b
    · rw [Nat.mod_eq_of_lt hlast]
    · have heq : j + 1 = M b := by omega
      rw [heq, Nat.mod_self, zeta_pow_self (M_pos b), pow_zero]
  let term : ℕ → ℂ := fun l =>
    (zeta (M b) ^ l) ^ n * Complex.exp ((r b : ℂ) * zeta (M b) ^ l * z)
  have hdiff_eq : (c b : ℂ) * gDeriv n b z - twoTerm n b j z =
      (c b : ℂ) * (r b : ℂ) ^ n *
        ∑ l ∈ ((Finset.range (M b)).erase j).erase j1, term l := by
    unfold gDeriv twoTerm
    rw [hzeta_j1]
    have hsplit1 : ∑ l ∈ Finset.range (M b), term l =
        term j + ∑ l ∈ (Finset.range (M b)).erase j, term l :=
      (Finset.add_sum_erase _ _ (Finset.mem_range.mpr hj)).symm
    have hj1_mem : j1 ∈ (Finset.range (M b)).erase j :=
      Finset.mem_erase.mpr ⟨hj1_ne, Finset.mem_range.mpr hj1_lt⟩
    have hsplit2 : ∑ l ∈ (Finset.range (M b)).erase j, term l =
        term j1 + ∑ l ∈ ((Finset.range (M b)).erase j).erase j1, term l :=
      (Finset.add_sum_erase _ _ hj1_mem).symm
    change (c b : ℂ) * ((r b : ℂ) ^ n * ∑ l ∈ Finset.range (M b), term l) -
      (c b : ℂ) * (r b : ℂ) ^ n * (term j + term j1) = _
    rw [hsplit1, hsplit2]
    ring
  rw [hdiff_eq, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (c_pos b).le,
    norm_pow, Complex.norm_real, Real.norm_of_nonneg (r_pos b).le]
  have hsum_le : ‖∑ l ∈ ((Finset.range (M b)).erase j).erase j1, term l‖ ≤
      (1 / 16 : ℝ) * Real.exp (r b * (zeta (M b) ^ j * z).re) := by
    have hterm_le : ∀ l ∈ ((Finset.range (M b)).erase j).erase j1,
        ‖term l‖ ≤ Real.exp (-(M b : ℝ) - 12) * Real.exp (r b * (zeta (M b) ^ j * z).re) := by
      intro l hl
      have hl1 : l ≠ j1 := (Finset.mem_erase.mp hl).1
      have hl2 : l ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
      have hllt : l < M b := Finset.mem_range.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).2
      dsimp [term]
      rw [norm_mul, norm_pow, norm_pow, norm_zeta, one_pow, one_pow, one_mul, Complex.norm_exp,
        ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hre_l : ((r b : ℂ) * zeta (M b) ^ l * z).re = r b * (zeta (M b) ^ l * z).re := by
        rw [mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
      rw [hre_l]
      have hsplit_z : (zeta (M b) ^ l * z).re - (zeta (M b) ^ j * z).re =
          ((zeta (M b) ^ l * z₀).re - (zeta (M b) ^ j * z₀).re) +
          ((zeta (M b) ^ l - zeta (M b) ^ j) * (z - z₀)).re := by
        have : zeta (M b) ^ l * z - zeta (M b) ^ j * z =
            (zeta (M b) ^ l * z₀ - zeta (M b) ^ j * z₀) +
            (zeta (M b) ^ l - zeta (M b) ^ j) * (z - z₀) := by ring
        have h1 := congrArg Complex.re this
        simpa [Complex.sub_re, Complex.add_re] using h1
      have hre_j0 : (zeta (M b) ^ j * z₀).re = ρs * Real.cos (Real.pi / (M b : ℝ)) := by
        dsimp [z₀]
        have h1 : zeta (M b) ^ j * ((ρs : ℂ) * Complex.exp (Complex.I * (rayAngle b j : ℂ))) =
            (ρs : ℂ) * (zeta (M b) ^ j * Complex.exp (Complex.I * (rayAngle b j : ℂ))) := by ring
        rw [h1, (zeta_mul_rayAngle b j).1]
        have harg : -((Real.pi / (M b : ℝ) : ℝ) : ℂ) * Complex.I =
            ((-(Real.pi / (M b : ℝ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [harg, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
          Real.cos_neg]
        ring
      have hre_l0 : (zeta (M b) ^ l * z₀).re =
          ρs * Real.cos ((2 * (l : ℝ) - (2 * (j : ℝ) + 1)) * Real.pi / (M b : ℝ)) := by
        dsimp [z₀, zeta, rayAngle]
        have h1 : Complex.exp (2 * Real.pi * Complex.I / (M b : ℂ)) ^ l *
            ((ρs : ℂ) * Complex.exp (Complex.I * (-((2 * (j : ℝ) + 1) * Real.pi / (M b : ℝ)) : ℝ))) =
            (ρs : ℂ) * Complex.exp ((((2 * (l : ℝ) - (2 * (j : ℝ) + 1)) * Real.pi / (M b : ℝ) : ℝ) : ℂ) * Complex.I) := by
          rw [← Complex.exp_nat_mul]
          calc _ = (ρs : ℂ) * (Complex.exp ((l : ℂ) * (2 * Real.pi * Complex.I / (M b : ℂ))) *
                Complex.exp (Complex.I * (-((2 * (j : ℝ) + 1) * Real.pi / (M b : ℝ)) : ℝ))) := by ring
            _ = (ρs : ℂ) * Complex.exp ((l : ℂ) * (2 * Real.pi * Complex.I / (M b : ℂ)) +
                Complex.I * (-((2 * (j : ℝ) + 1) * Real.pi / (M b : ℝ)) : ℝ)) := by rw [← Complex.exp_add]
            _ = _ := by
                congr 2
                have hM : ((M b : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (M_pos b).ne'
                push_cast; field_simp [hM]; ring
        rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re]
        ring
      have hcos_gap : (zeta (M b) ^ l * z₀).re - (zeta (M b) ^ j * z₀).re ≤
          -ρs * (16 / (M b : ℝ) ^ 2) := by
        rw [hre_l0, hre_j0]
        have h1 := cos_other_ray_le b j l hj hllt hl2 hl1
        have h2 := cos_pi_div_M_sub_cos_three b
        have hρpos : 0 ≤ ρs := le_trans (by have := ε_pos b; positivity) hρs
        nlinarith
      have hpert : ((zeta (M b) ^ l - zeta (M b) ^ j) * (z - z₀)).re ≤ 2 * delta b := by
        calc _ ≤ ‖(zeta (M b) ^ l - zeta (M b) ^ j) * (z - z₀)‖ := Complex.re_le_norm _
          _ = ‖zeta (M b) ^ l - zeta (M b) ^ j‖ * ‖z - z₀‖ := norm_mul _ _
          _ ≤ (‖zeta (M b) ^ l‖ + ‖zeta (M b) ^ j‖) * delta b := by
              rw [hdist]
              exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (delta_pos b).le
          _ = 2 * delta b := by rw [norm_pow, norm_pow, norm_zeta, one_pow, one_pow]; ring
      have hrb_pert : r b * (2 * delta b) ≤ (M b : ℝ) / 4 := by
        have h1 := delta_le b
        have h2 : 2 * r b * delta b ≤ 2 * r b * ((M b : ℝ) / (8 * r b)) :=
          mul_le_mul_of_nonneg_left h1 (by linarith [r_pos b])
        have h3 : 2 * r b * ((M b : ℝ) / (8 * r b)) = (M b : ℝ) / 4 := by
          field_simp [(r_pos b).ne']; ring
        linarith
      have hrb_gap : 2 * (M b : ℝ) ≤ r b * (ρs * (16 / (M b : ℝ) ^ 2)) := by
        have hr_cube : 2 * (M b : ℝ) ^ 3 * (4 : ℝ) ^ (b + 1) ≤ r b := by
          dsimp [r]; exact_mod_cast rNat_ge_cube b
        have hε_eq : ε b = 1 / (4 : ℝ) ^ (b + 1) := by dsimp [ε]; rw [one_div_pow]
        have h16ρ : 1 / (4 : ℝ) ^ (b + 1) ≤ 16 * ρs := by rw [← hε_eq]; linarith
        have hMpos : (0 : ℝ) < (M b : ℝ) := by exact_mod_cast M_pos b
        have h4pos : (0 : ℝ) < (4 : ℝ) ^ (b + 1) := by positivity
        have hmul1 : 2 * (M b : ℝ) ^ 3 ≤ r b * (16 * ρs) := by
          calc 2 * (M b : ℝ) ^ 3
              = 2 * (M b : ℝ) ^ 3 * (4 : ℝ) ^ (b + 1) * (1 / (4 : ℝ) ^ (b + 1)) := by
                field_simp [h4pos.ne']
            _ ≤ r b * (16 * ρs) :=
                mul_le_mul hr_cube h16ρ (by positivity) (r_pos b).le
        have hdiv : 2 * (M b : ℝ) ≤ (r b * (16 * ρs)) / (M b : ℝ) ^ 2 := by
          rw [le_div_iff₀ (pow_pos hMpos 2)]
          have : 2 * (M b : ℝ) * (M b : ℝ) ^ 2 = 2 * (M b : ℝ) ^ 3 := by ring
          linarith
        have heq : (r b * (16 * ρs)) / (M b : ℝ) ^ 2 = r b * (ρs * (16 / (M b : ℝ) ^ 2)) := by ring
        rwa [heq] at hdiv
      have hM16 : (256 : ℝ) ≤ (M b : ℝ) := by exact_mod_cast M_ge_256 b
      have hfinal : r b * ((zeta (M b) ^ l * z).re - (zeta (M b) ^ j * z).re) ≤ -(M b : ℝ) - 12 := by
        rw [hsplit_z, mul_add]
        have h1 : r b * ((zeta (M b) ^ l * z₀).re - (zeta (M b) ^ j * z₀).re) ≤
            -(r b * (ρs * (16 / (M b : ℝ) ^ 2))) := by
          have := mul_le_mul_of_nonneg_left hcos_gap (r_pos b).le
          linarith
        have h2 : r b * ((zeta (M b) ^ l - zeta (M b) ^ j) * (z - z₀)).re ≤ r b * (2 * delta b) :=
          mul_le_mul_of_nonneg_left hpert (r_pos b).le
        linarith
      linarith
    calc ‖∑ l ∈ ((Finset.range (M b)).erase j).erase j1, term l‖
        ≤ ∑ l ∈ ((Finset.range (M b)).erase j).erase j1, ‖term l‖ := norm_sum_le _ _
      _ ≤ ∑ _l ∈ ((Finset.range (M b)).erase j).erase j1,
            Real.exp (-(M b : ℝ) - 12) * Real.exp (r b * (zeta (M b) ^ j * z).re) :=
          Finset.sum_le_sum hterm_le
      _ = (((((Finset.range (M b)).erase j).erase j1).card : ℝ) * Real.exp (-(M b : ℝ) - 12)) *
            Real.exp (r b * (zeta (M b) ^ j * z).re) := by simp [mul_assoc]
      _ ≤ (1 / 16 : ℝ) * Real.exp (r b * (zeta (M b) ^ j * z).re) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have hcard : ((((Finset.range (M b)).erase j).erase j1).card : ℝ) ≤ (M b : ℝ) := by
            have h1 : (((Finset.range (M b)).erase j).erase j1).card ≤ (Finset.range (M b)).card :=
              Finset.card_le_card ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
            rw [Finset.card_range] at h1
            exact_mod_cast h1
          have hMe : (M b : ℝ) * Real.exp (-(M b : ℝ)) ≤ 1 := by
            rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
            linarith [Real.add_one_le_exp (M b : ℝ)]
          have he12 : Real.exp (-12) ≤ 1 / 16 := by
            rw [Real.exp_neg, one_div]
            apply inv_anti₀ (by norm_num)
            have h1 : (13 : ℝ) ≤ Real.exp 12 := by linarith [Real.add_one_le_exp (12 : ℝ)]
            have h2 : (16 : ℝ) ≤ (Real.exp 1) ^ 12 := by
              have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
              calc (16 : ℝ) ≤ 2 ^ 12 := by norm_num
                _ ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) h2e 12
            rw [← Real.exp_nat_mul] at h2
            simpa using h2
          calc (((((Finset.range (M b)).erase j).erase j1).card : ℝ) * Real.exp (-(M b : ℝ) - 12))
              ≤ (M b : ℝ) * Real.exp (-(M b : ℝ) - 12) :=
                mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
            _ = ((M b : ℝ) * Real.exp (-(M b : ℝ))) * Real.exp (-12) := by
                rw [sub_eq_add_neg, Real.exp_add, mul_assoc]
            _ ≤ 1 * (1 / 16) := mul_le_mul hMe he12 (Real.exp_pos _).le zero_le_one
            _ = 1 / 16 := one_mul _
  calc c b * r b ^ n * ‖∑ l ∈ ((Finset.range (M b)).erase j).erase j1, term l‖
      ≤ c b * r b ^ n * ((1 / 16 : ℝ) * Real.exp (r b * (zeta (M b) ^ j * z).re)) :=
        mul_le_mul_of_nonneg_left hsum_le (mul_nonneg (c_pos b).le (pow_nonneg (r_pos b).le _))
    _ = (1 / 16 : ℝ) * c b * r b ^ n * Real.exp (r b * (zeta (M b) ^ j * z).re) := by ring

private lemma re_zeta_mul_on_circle_ge (b j : ℕ) {ρs : ℝ} (hρs : ε b / 16 ≤ ρs) {z : ℂ}
    (hdist : ‖z - (ρs : ℂ) * Complex.exp (Complex.I * (rayAngle b j : ℂ))‖ = delta b) :
    ρs * Real.cos (Real.pi / (M b : ℝ)) - delta b ≤ (zeta (M b) ^ j * z).re ∧
      0 ≤ (zeta (M b) ^ j * z).re := by
  set z₀ : ℂ := (ρs : ℂ) * Complex.exp (Complex.I * (rayAngle b j : ℂ))
  have hre_j0 : (zeta (M b) ^ j * z₀).re = ρs * Real.cos (Real.pi / (M b : ℝ)) := by
    dsimp [z₀]
    have h1 : zeta (M b) ^ j * ((ρs : ℂ) * Complex.exp (Complex.I * (rayAngle b j : ℂ))) =
        (ρs : ℂ) * (zeta (M b) ^ j * Complex.exp (Complex.I * (rayAngle b j : ℂ))) := by ring
    rw [h1, (zeta_mul_rayAngle b j).1]
    have harg : -((Real.pi / (M b : ℝ) : ℝ) : ℂ) * Complex.I =
        ((-(Real.pi / (M b : ℝ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Real.cos_neg]
    ring
  have hdiff : |(zeta (M b) ^ j * z).re - (zeta (M b) ^ j * z₀).re| ≤ delta b := by
    have heq : (zeta (M b) ^ j * z).re - (zeta (M b) ^ j * z₀).re = (zeta (M b) ^ j * (z - z₀)).re := by
      have : zeta (M b) ^ j * z - zeta (M b) ^ j * z₀ = zeta (M b) ^ j * (z - z₀) := by ring
      have h1 := congrArg Complex.re this
      simpa [Complex.sub_re] using h1
    rw [heq]
    calc |(zeta (M b) ^ j * (z - z₀)).re|
        ≤ ‖zeta (M b) ^ j * (z - z₀)‖ := Complex.abs_re_le_norm _
      _ = ‖zeta (M b) ^ j‖ * ‖z - z₀‖ := norm_mul _ _
      _ = delta b := by rw [norm_pow, norm_zeta, one_pow, one_mul, hdist]
  have h1 : ρs * Real.cos (Real.pi / (M b : ℝ)) - delta b ≤ (zeta (M b) ^ j * z).re := by
    rw [← hre_j0]; linarith [(abs_le.mp hdiff).1]
  have hcos : (1 / 2 : ℝ) ≤ Real.cos (Real.pi / (M b : ℝ)) := by
    have hM : (256 : ℝ) ≤ (M b : ℝ) := by exact_mod_cast M_ge_256 b
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have hpos : Real.pi / (M b : ℝ) ≠ 0 := by positivity
    have hlt := Real.one_sub_sq_div_two_lt_cos hpos
    have hsq : (Real.pi / (M b : ℝ)) ^ 2 / 2 ≤ 1 / 2 := by
      have : Real.pi / (M b : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      nlinarith [div_nonneg Real.pi_pos.le (by linarith : (0 : ℝ) ≤ (M b : ℝ))]
    linarith
  have hdel := delta_lt_eps b
  have h2 : 0 ≤ ρs * Real.cos (Real.pi / (M b : ℝ)) - delta b := by
    nlinarith [ε_pos b]
  exact ⟨h1, h2.trans h1⟩

/- ### Section 6: Two-block transition and global zero density for every large `n` -/

private lemma tsum_other_blocks_bound (k n : ℕ) (hlo : Hmid k ≤ n) (hhi : n ≤ Hmid (k + 1))
    {z : ℂ} (hz : ‖z‖ ≤ (k : ℝ) + 5) :
    ‖fDeriv n z - ((c (k + 1) : ℂ) * gDeriv n (k + 1) z + (c (k + 2) : ℂ) * gDeriv n (k + 2) z)‖ ≤
      (1 / 64 : ℝ) * (c (k + 1) * r (k + 1) ^ n + c (k + 2) * r (k + 2) ^ n) := by
  let term : ℕ → ℂ := fun m => (c m : ℂ) * gDeriv n m z
  have hsum : Summable term := summable_fDeriv n z
  have hsplit : fDeriv n z = (∑ m ∈ Finset.range (k + 3), term m) + ∑' m : ℕ, term (m + (k + 3)) := by
    dsimp [fDeriv]
    exact (hsum.sum_add_tsum_nat_add (k + 3)).symm
  have hrange : ∑ m ∈ Finset.range (k + 3), term m =
      (∑ m ∈ Finset.range (k + 1), term m) + term (k + 1) + term (k + 2) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hdiff : fDeriv n z - (term (k + 1) + term (k + 2)) =
      (∑ m ∈ Finset.range (k + 1), term m) + ∑' m : ℕ, term (m + (k + 3)) := by
    rw [hsplit, hrange]; ring
  change ‖fDeriv n z - (term (k + 1) + term (k + 2))‖ ≤ _
  rw [hdiff]
  have hlow_sum : ‖∑ m ∈ Finset.range (k + 1), term m‖ ≤
      (1 / 64 : ℝ) * (c (k + 1) * r (k + 1) ^ n) := by
    have hterm_le : ∀ m ∈ Finset.range (k + 1),
        ‖term m‖ ≤ c (k + 1) * r (k + 1) ^ n * Real.exp (-100 * ((k + 2 : ℕ) : ℝ)) := by
      intro m hm
      have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      dsimp [term]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (c_pos m).le]
      calc c m * ‖gDeriv n m z‖
          ≤ c m * (r m ^ n * (M m : ℝ) * Real.exp (r m * ‖z‖)) :=
            mul_le_mul_of_nonneg_left (norm_gDeriv_le n m z) (c_pos m).le
        _ ≤ c m * r m ^ n * (M m : ℝ) * Real.exp (r m * ((k : ℝ) + 5)) := by
            rw [← mul_assoc, ← mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz (r_pos m).le))
              (mul_nonneg (mul_nonneg (c_pos m).le (pow_nonneg (r_pos m).le _)) (Nat.cast_nonneg _))
        _ ≤ c (k + 1) * r (k + 1) ^ n * Real.exp (-100 * ((k + 2 : ℕ) : ℝ)) :=
            weight_lower_tail_term k n m hlo hmk
    calc ‖∑ m ∈ Finset.range (k + 1), term m‖
        ≤ ∑ m ∈ Finset.range (k + 1), ‖term m‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ Finset.range (k + 1),
            c (k + 1) * r (k + 1) ^ n * Real.exp (-100 * ((k + 2 : ℕ) : ℝ)) :=
          Finset.sum_le_sum hterm_le
      _ = c (k + 1) * r (k + 1) ^ n * (((k + 1 : ℕ) : ℝ) * Real.exp (-100 * ((k + 2 : ℕ) : ℝ))) := by
          simp [mul_assoc, mul_left_comm]
      _ ≤ (1 / 64 : ℝ) * (c (k + 1) * r (k + 1) ^ n) := by
          rw [mul_comm (1 / 64 : ℝ)]
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (c_pos _).le (pow_nonneg (r_pos _).le _))
          have h1 : ((k + 1 : ℕ) : ℝ) ≤ Real.exp ((k + 1 : ℕ) : ℝ) := by
            linarith [Real.add_one_le_exp ((k + 1 : ℕ) : ℝ)]
          have h2 : ((k + 1 : ℕ) : ℝ) * Real.exp (-100 * ((k + 2 : ℕ) : ℝ)) ≤ Real.exp (-100) := by
            calc ((k + 1 : ℕ) : ℝ) * Real.exp (-100 * ((k + 2 : ℕ) : ℝ))
                ≤ Real.exp ((k + 1 : ℕ) : ℝ) * Real.exp (-100 * ((k + 2 : ℕ) : ℝ)) :=
                  mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
              _ = Real.exp (((k + 1 : ℕ) : ℝ) + -100 * ((k + 2 : ℕ) : ℝ)) := (Real.exp_add _ _).symm
              _ ≤ Real.exp (-100) := by
                  apply Real.exp_le_exp.mpr
                  push_cast; linarith
          have h3 : Real.exp (-100) ≤ 1 / 64 := by
            rw [Real.exp_neg, one_div]
            apply inv_anti₀ (by norm_num)
            linarith [Real.add_one_le_exp (100 : ℝ)]
          exact h2.trans h3
  have hup_sum : ‖∑' m : ℕ, term (m + (k + 3))‖ ≤
      (1 / 64 : ℝ) * (c (k + 2) * r (k + 2) ^ n) := by
    have hshift : Summable (fun m : ℕ => term (m + (k + 3))) :=
      (summable_nat_add_iff (k + 3)).mpr hsum
    have hterm_le : ∀ m : ℕ,
        ‖term (m + (k + 3))‖ ≤ c (k + 2) * r (k + 2) ^ n * (Real.exp (-100)) ^ (m + 1) := by
      intro m
      dsimp [term]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (c_pos _).le]
      have hBm : (k : ℝ) + 5 ≤ ((m + (k + 3) : ℕ) : ℝ) + 4 := by push_cast; linarith
      have htail := weight_upper_tail_term k n (m + (k + 3)) hhi (by omega) hBm
      have hpow_le : Real.exp (-100 * ((m + (k + 3) : ℕ) : ℝ)) ≤ (Real.exp (-100)) ^ (m + 1) := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        push_cast; linarith
      calc c (m + (k + 3)) * ‖gDeriv n (m + (k + 3)) z‖
          ≤ c (m + (k + 3)) * (r (m + (k + 3)) ^ n * (M (m + (k + 3)) : ℝ) *
              Real.exp (r (m + (k + 3)) * ‖z‖)) :=
            mul_le_mul_of_nonneg_left (norm_gDeriv_le n _ z) (c_pos _).le
        _ ≤ c (m + (k + 3)) * r (m + (k + 3)) ^ n * (M (m + (k + 3)) : ℝ) *
              Real.exp (r (m + (k + 3)) * ((k : ℝ) + 5)) := by
            rw [← mul_assoc, ← mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz (r_pos _).le))
              (mul_nonneg (mul_nonneg (c_pos _).le (pow_nonneg (r_pos _).le _)) (Nat.cast_nonneg _))
        _ ≤ c (k + 2) * r (k + 2) ^ n * Real.exp (-100 * ((m + (k + 3) : ℕ) : ℝ)) := htail
        _ ≤ c (k + 2) * r (k + 2) ^ n * (Real.exp (-100)) ^ (m + 1) :=
            mul_le_mul_of_nonneg_left hpow_le (mul_nonneg (c_pos _).le (pow_nonneg (r_pos _).le _))
    have hgeom : Summable (fun m : ℕ => c (k + 2) * r (k + 2) ^ n * (Real.exp (-100)) ^ (m + 1)) := by
      have h1 : Summable (fun m : ℕ => (c (k + 2) * r (k + 2) ^ n * Real.exp (-100)) * (Real.exp (-100)) ^ m) :=
        (summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left _
      refine h1.congr fun m => ?_
      rw [pow_succ]; ring
    have htsum_eq : ∑' m : ℕ, c (k + 2) * r (k + 2) ^ n * (Real.exp (-100)) ^ (m + 1) =
        c (k + 2) * r (k + 2) ^ n * (Real.exp (-100) / (1 - Real.exp (-100))) := by
      have hrew : (fun m : ℕ => c (k + 2) * r (k + 2) ^ n * (Real.exp (-100)) ^ (m + 1)) =
          (fun m : ℕ => (c (k + 2) * r (k + 2) ^ n * Real.exp (-100)) * (Real.exp (-100)) ^ m) := by
        ext m; rw [pow_succ]; ring
      rw [hrew, tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by norm_num))]
      ring
    have hratio : Real.exp (-100) / (1 - Real.exp (-100)) ≤ 1 / 64 := by
      have he : Real.exp (-100) ≤ 1 / 100 := by
        rw [Real.exp_neg, one_div]
        apply inv_anti₀ (by norm_num)
        linarith [Real.add_one_le_exp (100 : ℝ)]
      have hden : 0 < 1 - Real.exp (-100) := by linarith
      rw [div_le_iff₀ hden]
      linarith
    calc ‖∑' m : ℕ, term (m + (k + 3))‖
        ≤ ∑' m : ℕ, ‖term (m + (k + 3))‖ := norm_tsum_le_tsum_norm hshift.norm
      _ ≤ ∑' m : ℕ, c (k + 2) * r (k + 2) ^ n * (Real.exp (-100)) ^ (m + 1) :=
          hshift.norm.tsum_le_tsum hterm_le hgeom
      _ = c (k + 2) * r (k + 2) ^ n * (Real.exp (-100) / (1 - Real.exp (-100))) := htsum_eq
      _ ≤ c (k + 2) * r (k + 2) ^ n * (1 / 64) :=
          mul_le_mul_of_nonneg_left hratio (mul_nonneg (c_pos _).le (pow_nonneg (r_pos _).le _))
      _ = (1 / 64 : ℝ) * (c (k + 2) * r (k + 2) ^ n) := by ring
  calc ‖(∑ m ∈ Finset.range (k + 1), term m) + ∑' m : ℕ, term (m + (k + 3))‖
      ≤ ‖∑ m ∈ Finset.range (k + 1), term m‖ + ‖∑' m : ℕ, term (m + (k + 3))‖ := norm_add_le _ _
    _ ≤ (1 / 64 : ℝ) * (c (k + 1) * r (k + 1) ^ n) + (1 / 64 : ℝ) * (c (k + 2) * r (k + 2) ^ n) :=
        add_le_add hlow_sum hup_sum
    _ = (1 / 64 : ℝ) * (c (k + 1) * r (k + 1) ^ n + c (k + 2) * r (k + 2) ^ n) := by ring

private noncomputable def rho1 (k n : ℕ) : ℝ :=
  Real.log ((c (k + 1) * r (k + 1) ^ n) / (32 * (M (k + 2) : ℝ) * c (k + 2) * r (k + 2) ^ n)) /
    (r (k + 2) - r (k + 1) * Real.cos (Real.pi / (M (k + 1) : ℝ)))

private noncomputable def rho2 (k n : ℕ) : ℝ :=
  Real.log ((32 * (M (k + 1) : ℝ) * c (k + 1) * r (k + 1) ^ n) / (c (k + 2) * r (k + 2) ^ n)) /
    (r (k + 2) * Real.cos (Real.pi / (M (k + 2) : ℝ)) - r (k + 1))

private lemma transition_denoms (k : ℕ) :
    (1 / 2 : ℝ) * r (k + 2) ≤ r (k + 2) * Real.cos (Real.pi / (M (k + 2) : ℝ)) - r (k + 1) ∧
    r (k + 2) * Real.cos (Real.pi / (M (k + 2) : ℝ)) - r (k + 1) ≤
      r (k + 2) - r (k + 1) * Real.cos (Real.pi / (M (k + 1) : ℝ)) ∧
    (r (k + 2) - r (k + 1) * Real.cos (Real.pi / (M (k + 1) : ℝ))) -
      (r (k + 2) * Real.cos (Real.pi / (M (k + 2) : ℝ)) - r (k + 1)) ≤
      9 * r (k + 2) / (M (k + 2) : ℝ) ^ 2 := by
  have hr1 : 0 < r (k + 1) := r_pos (k + 1)
  have hr2 : 0 < r (k + 2) := r_pos (k + 2)
  have hM2 : (256 : ℝ) ≤ (M (k + 2) : ℝ) := by exact_mod_cast M_ge_256 (k + 2)
  have hM1 : (256 : ℝ) ≤ (M (k + 1) : ℝ) := by exact_mod_cast M_ge_256 (k + 1)
  have hstep : r (k + 1) * (M (k + 2) : ℝ) ^ 2 ≤ r (k + 2) := by
    dsimp [r]; exact_mod_cast rNat_step_ge (k + 1)
  have h4 : 4 * r (k + 1) ≤ r (k + 2) := r_step_mul_four (k + 1)
  have hcos_bound : ∀ b : ℕ, 1 - 8 / (M b : ℝ) ^ 2 ≤ Real.cos (Real.pi / (M b : ℝ)) := by
    intro b
    have hlt := Real.one_sub_sq_div_two_lt_cos (by have := M_pos b; positivity : Real.pi / (M b : ℝ) ≠ 0)
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have hsq : (Real.pi / (M b : ℝ)) ^ 2 / 2 ≤ 8 / (M b : ℝ) ^ 2 := by
      have : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos]
      rw [div_pow, div_div]
      calc Real.pi ^ 2 / ((M b : ℝ) ^ 2 * 2) ≤ 16 / ((M b : ℝ) ^ 2 * 2) :=
            div_le_div_of_nonneg_right this (by positivity)
        _ = 8 / (M b : ℝ) ^ 2 := by ring
    linarith
  have hc2 := hcos_bound (k + 2)
  have hc1 := hcos_bound (k + 1)
  have hc2_ge : (3 / 4 : ℝ) ≤ Real.cos (Real.pi / (M (k + 2) : ℝ)) := by
    have : 8 / (M (k + 2) : ℝ) ^ 2 ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hcos1_le : Real.cos (Real.pi / (M (k + 1) : ℝ)) ≤ 1 := Real.cos_le_one _
  have hcos2_le : Real.cos (Real.pi / (M (k + 2) : ℝ)) ≤ 1 := Real.cos_le_one _
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have h1 : r (k + 2) * (1 - Real.cos (Real.pi / (M (k + 2) : ℝ))) ≤ 8 * r (k + 2) / (M (k + 2) : ℝ) ^ 2 := by
    have : 1 - Real.cos (Real.pi / (M (k + 2) : ℝ)) ≤ 8 / (M (k + 2) : ℝ) ^ 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_left this hr2.le
    have heq : r (k + 2) * (8 / (M (k + 2) : ℝ) ^ 2) = 8 * r (k + 2) / (M (k + 2) : ℝ) ^ 2 := by ring
    linarith
  have h2 : r (k + 1) * (1 - Real.cos (Real.pi / (M (k + 1) : ℝ))) ≤ r (k + 2) / (M (k + 2) : ℝ) ^ 2 := by
    have hle1 : 1 - Real.cos (Real.pi / (M (k + 1) : ℝ)) ≤ 1 := by
      have : 0 ≤ Real.cos (Real.pi / (M (k + 1) : ℝ)) := by
        have : 8 / (M (k + 1) : ℝ) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
        linarith
      linarith
    have hdiv : r (k + 1) ≤ r (k + 2) / (M (k + 2) : ℝ) ^ 2 :=
      (le_div_iff₀ (by positivity)).mpr hstep
    nlinarith
  have hcomb : (r (k + 2) - r (k + 1) * Real.cos (Real.pi / (M (k + 1) : ℝ))) -
      (r (k + 2) * Real.cos (Real.pi / (M (k + 2) : ℝ)) - r (k + 1)) =
      r (k + 2) * (1 - Real.cos (Real.pi / (M (k + 2) : ℝ))) +
      r (k + 1) * (1 - Real.cos (Real.pi / (M (k + 1) : ℝ))) := by ring
  have h9 : 8 * r (k + 2) / (M (k + 2) : ℝ) ^ 2 + r (k + 2) / (M (k + 2) : ℝ) ^ 2 =
      9 * r (k + 2) / (M (k + 2) : ℝ) ^ 2 := by ring
  linarith

private lemma rho2_sub_rho1_le (k n : ℕ) (hρ1 : rho1 k n ≤ R (k + 1) + 2) :
    rho2 k n - rho1 k n < ε (k + 1) / 8 := by
  set D1 := r (k + 2) - r (k + 1) * Real.cos (Real.pi / (M (k + 1) : ℝ))
  set D2 := r (k + 2) * Real.cos (Real.pi / (M (k + 2) : ℝ)) - r (k + 1)
  have ⟨hD2_lo, hD2_le_D1, hD_diff⟩ := transition_denoms k
  have hr2 : 0 < r (k + 2) := r_pos (k + 2)
  have hD2_pos : 0 < D2 := by linarith
  have hD1_pos : 0 < D1 := lt_of_lt_of_le hD2_pos hD2_le_D1
  have hnum_diff :
      Real.log ((32 * (M (k + 1) : ℝ) * c (k + 1) * r (k + 1) ^ n) / (c (k + 2) * r (k + 2) ^ n)) -
      Real.log ((c (k + 1) * r (k + 1) ^ n) / (32 * (M (k + 2) : ℝ) * c (k + 2) * r (k + 2) ^ n)) =
      Real.log (1024 * (M (k + 1) : ℝ) * (M (k + 2) : ℝ)) := by
    have hpos1 : 0 < (32 * (M (k + 1) : ℝ) * c (k + 1) * r (k + 1) ^ n) / (c (k + 2) * r (k + 2) ^ n) := by
      have := M_pos (k + 1); have := c_pos (k + 1); have := c_pos (k + 2)
      have := r_pos (k + 1); have := r_pos (k + 2); positivity
    have hpos2 : 0 < (c (k + 1) * r (k + 1) ^ n) / (32 * (M (k + 2) : ℝ) * c (k + 2) * r (k + 2) ^ n) := by
      have := M_pos (k + 2); have := c_pos (k + 1); have := c_pos (k + 2)
      have := r_pos (k + 1); have := r_pos (k + 2); positivity
    rw [← Real.log_div hpos1.ne' hpos2.ne']
    congr 1
    have hc1 : c (k + 1) ≠ 0 := (c_pos (k + 1)).ne'
    have hc2 : c (k + 2) ≠ 0 := (c_pos (k + 2)).ne'
    have hr1' : r (k + 1) ≠ 0 := (r_pos (k + 1)).ne'
    have hr2' : r (k + 2) ≠ 0 := (r_pos (k + 2)).ne'
    field_simp [hc1, hc2, hr1', hr2']
    ring
  have hident : rho2 k n - rho1 k n =
      rho1 k n * ((D1 - D2) / D2) + Real.log (1024 * (M (k + 1) : ℝ) * (M (k + 2) : ℝ)) / D2 := by
    have hsub : Real.log ((32 * (M (k + 1) : ℝ) * c (k + 1) * r (k + 1) ^ n) / (c (k + 2) * r (k + 2) ^ n)) =
        Real.log ((c (k + 1) * r (k + 1) ^ n) / (32 * (M (k + 2) : ℝ) * c (k + 2) * r (k + 2) ^ n)) +
          Real.log (1024 * (M (k + 1) : ℝ) * (M (k + 2) : ℝ)) := by linarith
    change Real.log _ / D2 - Real.log _ / D1 =
        (Real.log _ / D1) * ((D1 - D2) / D2) + Real.log _ / D2
    rw [hsub]
    field_simp [hD1_pos.ne', hD2_pos.ne']
    ring
  rw [hident]
  have hpart1 : rho1 k n * ((D1 - D2) / D2) < ε (k + 1) / 16 := by
    have hfrac : (D1 - D2) / D2 ≤ 18 / (M (k + 2) : ℝ) ^ 2 := by
      calc (D1 - D2) / D2 ≤ (9 * r (k + 2) / (M (k + 2) : ℝ) ^ 2) / ((1 / 2 : ℝ) * r (k + 2)) :=
            div_le_div₀ (by positivity) hD_diff (by positivity) hD2_lo
        _ = 18 / (M (k + 2) : ℝ) ^ 2 := by field_simp [hr2.ne']; ring
    have hnonneg : 0 ≤ (D1 - D2) / D2 := div_nonneg (by linarith) hD2_pos.le
    have hR : R (k + 1) + 2 = (k : ℝ) + 5 := by dsimp [R]; push_cast; ring
    have hM2_eq : (M (k + 2) : ℝ) = 32 * ((k : ℝ) + 4) * (4 : ℝ) ^ (k + 3) := by
      dsimp [M]; push_cast; ring
    have hε1 : ε (k + 1) = 1 / (4 : ℝ) ^ (k + 2) := by dsimp [ε]; rw [one_div_pow]
    have hM2_pos : (0 : ℝ) < (M (k + 2) : ℝ) := by exact_mod_cast M_pos (k + 2)
    have hlt : ((k : ℝ) + 5) * (18 / (M (k + 2) : ℝ) ^ 2) < ε (k + 1) / 16 := by
      rw [hε1, div_div, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
      rw [hM2_eq]
      set P : ℝ := (4 : ℝ) ^ (k + 2)
      have hP_pos : 0 < P := by positivity
      have h4step : (4 : ℝ) ^ (k + 3) = 4 * P := by dsimp [P]; rw [pow_succ]; ring
      rw [h4step]
      have hP_ge : (16 : ℝ) ≤ P := by
        dsimp [P]
        calc (16 : ℝ) = (4 : ℝ) ^ 2 := by norm_num
          _ ≤ (4 : ℝ) ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hk_cmp : ((k : ℝ) + 5) * 18 * 16 < (32 * ((k : ℝ) + 4)) ^ 2 := by nlinarith
      have hP_cmp : P ≤ (4 * P) ^ 2 := by nlinarith
      calc ((k : ℝ) + 5) * 18 * (P * 16)
          = (((k : ℝ) + 5) * 18 * 16) * P := by ring
        _ < (32 * ((k : ℝ) + 4)) ^ 2 * P := mul_lt_mul_of_pos_right hk_cmp hP_pos
        _ ≤ (32 * ((k : ℝ) + 4)) ^ 2 * (4 * P) ^ 2 := mul_le_mul_of_nonneg_left hP_cmp (by positivity)
        _ = 1 * (32 * ((k : ℝ) + 4) * (4 * P)) ^ 2 := by ring
    calc rho1 k n * ((D1 - D2) / D2)
        ≤ (R (k + 1) + 2) * ((D1 - D2) / D2) := mul_le_mul_of_nonneg_right hρ1 hnonneg
      _ ≤ ((k : ℝ) + 5) * (18 / (M (k + 2) : ℝ) ^ 2) := by
          rw [hR]; exact mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ < ε (k + 1) / 16 := hlt
  have hpart2 : Real.log (1024 * (M (k + 1) : ℝ) * (M (k + 2) : ℝ)) / D2 < ε (k + 1) / 16 := by
    have hlog_le : Real.log (1024 * (M (k + 1) : ℝ) * (M (k + 2) : ℝ)) ≤ 1024 * (M (k + 2) : ℝ) ^ 2 := by
      have h1 : Real.log (1024 * (M (k + 1) : ℝ) * (M (k + 2) : ℝ)) ≤
          1024 * (M (k + 1) : ℝ) * (M (k + 2) : ℝ) := by
        linarith [Real.log_le_sub_one_of_pos (by have := M_pos (k+1); have := M_pos (k+2); positivity :
          (0 : ℝ) < 1024 * (M (k + 1) : ℝ) * (M (k + 2) : ℝ))]
      have hMle : (M (k + 1) : ℝ) ≤ (M (k + 2) : ℝ) := by exact_mod_cast M_mono (Nat.le_succ _)
      nlinarith [M_pos (k + 2)]
    have hr_cube : 2 * (M (k + 2) : ℝ) ^ 3 * (4 : ℝ) ^ (k + 3) ≤ r (k + 2) := by
      dsimp [r]; exact_mod_cast rNat_ge_cube (k + 2)
    have hM2 : (256 : ℝ) ≤ (M (k + 2) : ℝ) := by exact_mod_cast M_ge_256 (k + 2)
    have hε1 : ε (k + 1) = 1 / (4 : ℝ) ^ (k + 2) := by dsimp [ε]; rw [one_div_pow]
    calc Real.log (1024 * (M (k + 1) : ℝ) * (M (k + 2) : ℝ)) / D2
        ≤ (1024 * (M (k + 2) : ℝ) ^ 2) / ((1 / 2 : ℝ) * r (k + 2)) :=
          div_le_div₀ (by positivity) hlog_le (by positivity) hD2_lo
      _ < ε (k + 1) / 16 := by
          rw [hε1, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
          have h4step : (4 : ℝ) ^ (k + 3) = 4 * (4 : ℝ) ^ (k + 2) := by rw [pow_succ]; ring
          have h4pos : (0 : ℝ) < (4 : ℝ) ^ (k + 2) := by positivity
          have hr_big : 8 * (M (k + 2) : ℝ) ^ 3 * (4 : ℝ) ^ (k + 2) ≤ r (k + 2) := by
            rw [h4step] at hr_cube; linarith
          have hM3 : 16 * (1024 * (M (k + 2) : ℝ) ^ 2) < 4 * (M (k + 2) : ℝ) ^ 3 := by
            --Wait: 16 * 1024 = 16384, and 4 * M(k+2) >= 4 * 32 * 4 * 64 = 32768!
            have hM2_big : (8192 : ℝ) ≤ (M (k + 2) : ℝ) := by
              dsimp [M]
              have h4_3 : 64 ≤ 4 ^ (k + 3) := by
                calc 64 = 4 ^ 3 := by norm_num
                  _ ≤ 4 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
              have hnat : 8192 ≤ 32 * (k + 2 + 2) * 4 ^ (k + 3) := by nlinarith
              exact_mod_cast hnat
            nlinarith [sq_nonneg (M (k + 2) : ℝ)]
          nlinarith [mul_lt_mul_of_pos_right hM3 h4pos]
  linarith

private lemma exists_zero_inner_block (k n j : ℕ) (hj : j < M (k + 1))
    (hlo : Hmid k ≤ n) (hhi : n ≤ Hmid (k + 1))
    {ρ : ℝ} (hρ_lo : ε (k + 1) / 8 ≤ ρ) (hρ_hi : ρ ≤ R (k + 1) + 1)
    (hρ_rho1 : ρ ≤ rho1 k n - 2 * delta (k + 1) - ε (k + 1) / 32) :
    ∃ z : ℂ, fDeriv n z = 0 ∧
      ‖z - (ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 1) j : ℂ))‖ < ε (k + 1) / 16 := by
  obtain ⟨ρs, hρs_dist, htwo0⟩ := exists_twoTerm_zero n (k + 1) j ρ
  have hstep_le : Real.pi / (2 * r (k + 1) * Real.sin (Real.pi / (M (k + 1) : ℝ))) < ε (k + 1) / 32 := by
    have h1 : Real.pi / (2 * r (k + 1) * Real.sin (Real.pi / (M (k + 1) : ℝ))) =
        2 * Real.pi * delta (k + 1) := by
      dsimp [delta]; field_simp [(r_pos (k + 1)).ne', (sin_pi_div_M_pos (k + 1)).ne']; ring
    rw [h1]
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have hd := delta_le (k + 1)
    have hr : 2 * (M (k + 1) : ℝ) ^ 3 * (4 : ℝ) ^ (k + 2) ≤ r (k + 1) := by
      dsimp [r]; exact_mod_cast rNat_ge_cube (k + 1)
    have hM : (256 : ℝ) ≤ (M (k + 1) : ℝ) := by exact_mod_cast M_ge_256 (k + 1)
    have hε : ε (k + 1) = 1 / (4 : ℝ) ^ (k + 2) := by dsimp [ε]; rw [one_div_pow]
    rw [hε]
    calc 2 * Real.pi * delta (k + 1)
        ≤ 8 * ((M (k + 1) : ℝ) / (8 * r (k + 1))) :=
          mul_le_mul (by linarith) hd (delta_pos _).le (by norm_num)
      _ = (M (k + 1) : ℝ) / r (k + 1) := by field_simp [(r_pos (k + 1)).ne']
      _ < (1 / (4 : ℝ) ^ (k + 2)) / 32 := by
          rw [div_div, div_lt_div_iff₀ (r_pos (k + 1)) (by positivity)]
          have h4pos : (0 : ℝ) < (4 : ℝ) ^ (k + 2) := by positivity
          have hMsq : (256 : ℝ) * 256 ≤ (M (k + 1) : ℝ) ^ 2 := by nlinarith
          have : 32 * (M (k + 1) : ℝ) < 2 * (M (k + 1) : ℝ) ^ 3 := by nlinarith
          nlinarith [mul_lt_mul_of_pos_right this h4pos]
  have hρs_close : |ρs - ρ| < ε (k + 1) / 32 := lt_of_le_of_lt hρs_dist hstep_le
  have hρs_lo : ε (k + 1) / 16 ≤ ρs := by linarith [(abs_le.mp hρs_close.le).1, ε_pos (k + 1)]
  have hρs_rho1 : ρs ≤ rho1 k n - 2 * delta (k + 1) := by linarith [(abs_le.mp hρs_close.le).2]
  set z₀ : ℂ := (ρs : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 1) j : ℂ))
  have hz₀_norm : ‖z₀‖ = ρs := by
    dsimp [z₀]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [ε_pos (k + 1)]),
      mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hrouche : ∃ z ∈ Metric.closedBall z₀ (delta (k + 1)), fDeriv n z = 0 := by
    apply rouche_exists_zero (delta_pos (k + 1))
      (fun w => (hasDerivAt_fDeriv n w).differentiableAt)
      (twoTerm_differentiable n (k + 1) j) htwo0
    intro z hdist
    have hz_norm : ‖z‖ ≤ ρs + delta (k + 1) := by
      have htri : ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := by
        simpa [add_sub_cancel] using norm_add_le z₀ (z - z₀)
      linarith
    have hz_le_k5 : ‖z‖ ≤ (k : ℝ) + 5 := by
      have hdel := delta_lt_eps (k + 1)
      have hε_le : ε (k + 1) ≤ 1 := by dsimp [ε]; exact pow_le_one₀ (by norm_num) (by norm_num)
      have hR : R (k + 1) = (k : ℝ) + 3 := by dsimp [R]; push_cast; ring
      linarith [(abs_le.mp hρs_close.le).2]
    have hlow_two := twoTerm_norm_on_circle n (k + 1) j htwo0 hdist
    have hrest := rest_of_block_bound n (k + 1) j hj hρs_lo hdist
    have ⟨hre_ge, hre_nn⟩ := re_zeta_mul_on_circle_ge (k + 1) j hρs_lo hdist
    have hother := tsum_other_blocks_bound k n hlo hhi hz_le_k5
    set E := Real.exp (r (k + 1) * (zeta (M (k + 1)) ^ j * z).re)
    have hE_ge1 : 1 ≤ E := Real.one_le_exp (mul_nonneg (r_pos _).le hre_nn)
    -- Bound Block (k + 2) at z using ρs ≤ rho1 k n - 2 * delta (k + 1)
    have hblk2 : c (k + 2) * r (k + 2) ^ n * (M (k + 2) : ℝ) * Real.exp (r (k + 2) * ‖z‖) ≤
        (1 / 32 : ℝ) * c (k + 1) * r (k + 1) ^ n * E := by
      set D1 := r (k + 2) - r (k + 1) * Real.cos (Real.pi / (M (k + 1) : ℝ))
      have ⟨hD2_lo, hD2_le_D1, _⟩ := transition_denoms k
      have hD1_pos : 0 < D1 := lt_of_lt_of_le (by linarith [r_pos (k + 2)]) hD2_le_D1
      have h4r : 4 * r (k + 1) ≤ r (k + 2) := r_step_mul_four (k + 1)
      have hcos_le : Real.cos (Real.pi / (M (k + 1) : ℝ)) ≤ 1 := Real.cos_le_one _
      have hexp_cmp : r (k + 2) * ‖z‖ - r (k + 1) * (zeta (M (k + 1)) ^ j * z).re ≤ D1 * rho1 k n := by
        have h1 : r (k + 2) * ‖z‖ ≤ r (k + 2) * (ρs + delta (k + 1)) :=
          mul_le_mul_of_nonneg_left hz_norm (r_pos _).le
        have h2 : r (k + 1) * (ρs * Real.cos (Real.pi / (M (k + 1) : ℝ)) - delta (k + 1)) ≤
            r (k + 1) * (zeta (M (k + 1)) ^ j * z).re :=
          mul_le_mul_of_nonneg_left hre_ge (r_pos _).le
        have h3 : D1 * ρs + (r (k + 2) + r (k + 1)) * delta (k + 1) ≤ D1 * rho1 k n := by
          have hdel_pos := delta_pos (k + 1)
          have hcoef : r (k + 2) + r (k + 1) ≤ 2 * D1 := by
            dsimp [D1]; nlinarith [r_pos (k + 1)]
          nlinarith
        dsimp [D1] at h3 ⊢
        linarith
      have hD1_rho1 : D1 * rho1 k n =
          Real.log ((c (k + 1) * r (k + 1) ^ n) / (32 * (M (k + 2) : ℝ) * c (k + 2) * r (k + 2) ^ n)) := by
        dsimp [rho1, D1]
        exact mul_div_cancel₀ _ hD1_pos.ne'
      have hratio_pos : 0 < (c (k + 1) * r (k + 1) ^ n) / (32 * (M (k + 2) : ℝ) * c (k + 2) * r (k + 2) ^ n) := by
        have := c_pos (k + 1); have := c_pos (k + 2); have := r_pos (k + 1)
        have := r_pos (k + 2); have := M_pos (k + 2); positivity
      have hexp_le : Real.exp (r (k + 2) * ‖z‖) / E ≤
          (c (k + 1) * r (k + 1) ^ n) / (32 * (M (k + 2) : ℝ) * c (k + 2) * r (k + 2) ^ n) := by
        dsimp [E]
        rw [← Real.exp_sub]
        calc Real.exp (r (k + 2) * ‖z‖ - r (k + 1) * (zeta (M (k + 1)) ^ j * z).re)
            ≤ Real.exp (D1 * rho1 k n) := Real.exp_le_exp.mpr hexp_cmp
          _ = _ := by rw [hD1_rho1, Real.exp_log hratio_pos]
      have hmul := (div_le_iff₀ (Real.exp_pos _)).mp hexp_le
      have hpos_m : 0 < 32 * (M (k + 2) : ℝ) * c (k + 2) * r (k + 2) ^ n := by
        have := c_pos (k + 2); have := r_pos (k + 2); have := M_pos (k + 2); positivity
      have hcross : (c (k + 2) * r (k + 2) ^ n * (M (k + 2) : ℝ)) * Real.exp (r (k + 2) * ‖z‖) ≤
          (c (k + 2) * r (k + 2) ^ n * (M (k + 2) : ℝ)) *
            ((c (k + 1) * r (k + 1) ^ n) / (32 * (M (k + 2) : ℝ) * c (k + 2) * r (k + 2) ^ n) * E) :=
        mul_le_mul_of_nonneg_left hmul (by have := c_pos (k+2); have := r_pos (k+2); positivity)
      have hsimp : (c (k + 2) * r (k + 2) ^ n * (M (k + 2) : ℝ)) *
          ((c (k + 1) * r (k + 1) ^ n) / (32 * (M (k + 2) : ℝ) * c (k + 2) * r (k + 2) ^ n) * E) =
          (1 / 32 : ℝ) * c (k + 1) * r (k + 1) ^ n * E := by
        have hM2ne : (M (k + 2) : ℝ) ≠ 0 := by exact_mod_cast (M_pos (k + 2)).ne'
        have hc2ne : c (k + 2) ≠ 0 := (c_pos (k + 2)).ne'
        have hr2ne : r (k + 2) ^ n ≠ 0 := (pow_pos (r_pos (k + 2)) n).ne'
        field_simp [hM2ne, hc2ne, hr2ne]
      linarith
    have hblk2_norm : ‖(c (k + 2) : ℂ) * gDeriv n (k + 2) z‖ ≤
        (1 / 32 : ℝ) * c (k + 1) * r (k + 1) ^ n * E := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (c_pos _).le]
      calc c (k + 2) * ‖gDeriv n (k + 2) z‖
          ≤ c (k + 2) * (r (k + 2) ^ n * (M (k + 2) : ℝ) * Real.exp (r (k + 2) * ‖z‖)) :=
            mul_le_mul_of_nonneg_left (norm_gDeriv_le n (k + 2) z) (c_pos _).le
        _ = c (k + 2) * r (k + 2) ^ n * (M (k + 2) : ℝ) * Real.exp (r (k + 2) * ‖z‖) := by ring
        _ ≤ (1 / 32 : ℝ) * c (k + 1) * r (k + 1) ^ n * E := hblk2
    have hcr2_le : c (k + 2) * r (k + 2) ^ n ≤ (1 / 32 : ℝ) * c (k + 1) * r (k + 1) ^ n * E := by
      have hM1 : (1 : ℝ) ≤ (M (k + 2) : ℝ) := by exact_mod_cast (M_pos (k + 2))
      have he1 : 1 ≤ Real.exp (r (k + 2) * ‖z‖) := Real.one_le_exp (mul_nonneg (r_pos _).le (norm_nonneg _))
      have hnn : 0 ≤ c (k + 2) * r (k + 2) ^ n := mul_nonneg (c_pos _).le (pow_nonneg (r_pos _).le _)
      have hprod : 1 ≤ (M (k + 2) : ℝ) * Real.exp (r (k + 2) * ‖z‖) := by nlinarith
      nlinarith
    have hsplit_all : fDeriv n z - twoTerm n (k + 1) j z =
        (fDeriv n z - ((c (k + 1) : ℂ) * gDeriv n (k + 1) z + (c (k + 2) : ℂ) * gDeriv n (k + 2) z)) +
        (c (k + 2) : ℂ) * gDeriv n (k + 2) z +
        ((c (k + 1) : ℂ) * gDeriv n (k + 1) z - twoTerm n (k + 1) j z) := by ring
    have htotal : ‖fDeriv n z - twoTerm n (k + 1) j z‖ ≤
        (1 / 64 + 1 / 64 * (1 / 32) + 1 / 32 + 1 / 16 : ℝ) * c (k + 1) * r (k + 1) ^ n * E := by
      rw [hsplit_all]
      have htri1 := norm_add_le
        ((fDeriv n z - ((c (k + 1) : ℂ) * gDeriv n (k + 1) z + (c (k + 2) : ℂ) * gDeriv n (k + 2) z)) +
          (c (k + 2) : ℂ) * gDeriv n (k + 2) z)
        ((c (k + 1) : ℂ) * gDeriv n (k + 1) z - twoTerm n (k + 1) j z)
      have htri2 := norm_add_le
        (fDeriv n z - ((c (k + 1) : ℂ) * gDeriv n (k + 1) z + (c (k + 2) : ℂ) * gDeriv n (k + 2) z))
        ((c (k + 2) : ℂ) * gDeriv n (k + 2) z)
      have hcr1_le : c (k + 1) * r (k + 1) ^ n ≤ c (k + 1) * r (k + 1) ^ n * E :=
        le_mul_of_one_le_right (mul_nonneg (c_pos _).le (pow_nonneg (r_pos _).le _)) hE_ge1
      linarith
    have hpos_dom : 0 < c (k + 1) * r (k + 1) ^ n * E := by
      have := c_pos (k + 1); have := r_pos (k + 1); have := Real.exp_pos (r (k + 1) * (zeta (M (k + 1)) ^ j * z).re)
      positivity
    linarith
  obtain ⟨z, hz_cl, hf0⟩ := hrouche
  refine ⟨z, hf0, ?_⟩
  have h1 : ‖z - z₀‖ ≤ delta (k + 1) := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz_cl
  have h2 : ‖z₀ - (ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 1) j : ℂ))‖ = |ρs - ρ| := by
    dsimp [z₀]
    rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one]
  have htri : ‖z - (ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 1) j : ℂ))‖ ≤
      ‖z - z₀‖ + ‖z₀ - (ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 1) j : ℂ))‖ := by
    simpa [sub_add_sub_cancel] using norm_add_le (z - z₀) (z₀ - (ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 1) j : ℂ)))
  linarith [delta_lt_eps (k + 1), ε_pos (k + 1)]

private lemma exists_zero_outer_block (k n j : ℕ) (hj : j < M (k + 2))
    (hlo : Hmid k ≤ n) (hhi : n ≤ Hmid (k + 1))
    {ρ : ℝ} (hρ_lo : ε (k + 2) / 8 ≤ ρ) (hρ_hi : ρ ≤ R (k + 1) + 1)
    (hρ_rho2 : rho2 k n + 4 * delta (k + 2) + ε (k + 2) / 32 ≤ ρ) :
    ∃ z : ℂ, fDeriv n z = 0 ∧
      ‖z - (ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 2) j : ℂ))‖ < ε (k + 2) / 16 := by
  obtain ⟨ρs, hρs_dist, htwo0⟩ := exists_twoTerm_zero n (k + 2) j ρ
  have hstep_le : Real.pi / (2 * r (k + 2) * Real.sin (Real.pi / (M (k + 2) : ℝ))) < ε (k + 2) / 32 := by
    have h1 : Real.pi / (2 * r (k + 2) * Real.sin (Real.pi / (M (k + 2) : ℝ))) =
        2 * Real.pi * delta (k + 2) := by
      dsimp [delta]; field_simp [(r_pos (k + 2)).ne', (sin_pi_div_M_pos (k + 2)).ne']; ring
    rw [h1]
    have hd := delta_le (k + 2)
    have hr : 2 * (M (k + 2) : ℝ) ^ 3 * (4 : ℝ) ^ (k + 3) ≤ r (k + 2) := by
      dsimp [r]; exact_mod_cast rNat_ge_cube (k + 2)
    have hM : (256 : ℝ) ≤ (M (k + 2) : ℝ) := by exact_mod_cast M_ge_256 (k + 2)
    have hε : ε (k + 2) = 1 / (4 : ℝ) ^ (k + 3) := by dsimp [ε]; rw [one_div_pow]
    rw [hε]
    calc 2 * Real.pi * delta (k + 2)
        ≤ 8 * ((M (k + 2) : ℝ) / (8 * r (k + 2))) :=
          mul_le_mul (by linarith [Real.pi_lt_four]) hd (delta_pos _).le (by norm_num)
      _ = (M (k + 2) : ℝ) / r (k + 2) := by field_simp [(r_pos (k + 2)).ne']
      _ < (1 / (4 : ℝ) ^ (k + 3)) / 32 := by
          rw [div_div, div_lt_div_iff₀ (r_pos (k + 2)) (by positivity)]
          have h4pos : (0 : ℝ) < (4 : ℝ) ^ (k + 3) := by positivity
          have hMsq : (256 : ℝ) * 256 ≤ (M (k + 2) : ℝ) ^ 2 := by nlinarith
          have : 32 * (M (k + 2) : ℝ) < 2 * (M (k + 2) : ℝ) ^ 3 := by nlinarith
          nlinarith [mul_lt_mul_of_pos_right this h4pos]
  have hρs_close : |ρs - ρ| < ε (k + 2) / 32 := lt_of_le_of_lt hρs_dist hstep_le
  have hρs_lo : ε (k + 2) / 16 ≤ ρs := by linarith [(abs_le.mp hρs_close.le).1, ε_pos (k + 2)]
  have hρs_rho2 : rho2 k n + 4 * delta (k + 2) ≤ ρs := by linarith [(abs_le.mp hρs_close.le).1]
  set z₀ : ℂ := (ρs : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 2) j : ℂ))
  have hz₀_norm : ‖z₀‖ = ρs := by
    dsimp [z₀]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [ε_pos (k + 2)]),
      mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hrouche : ∃ z ∈ Metric.closedBall z₀ (delta (k + 2)), fDeriv n z = 0 := by
    apply rouche_exists_zero (delta_pos (k + 2))
      (fun w => (hasDerivAt_fDeriv n w).differentiableAt)
      (twoTerm_differentiable n (k + 2) j) htwo0
    intro z hdist
    have hz_norm : ‖z‖ ≤ ρs + delta (k + 2) := by
      have htri : ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := by
        simpa [add_sub_cancel] using norm_add_le z₀ (z - z₀)
      linarith
    have hz_le_k5 : ‖z‖ ≤ (k : ℝ) + 5 := by
      have hdel := delta_lt_eps (k + 2)
      have hε_le : ε (k + 2) ≤ 1 := by dsimp [ε]; exact pow_le_one₀ (by norm_num) (by norm_num)
      have hR : R (k + 1) = (k : ℝ) + 3 := by dsimp [R]; push_cast; ring
      linarith [(abs_le.mp hρs_close.le).2]
    have hlow_two := twoTerm_norm_on_circle n (k + 2) j htwo0 hdist
    have hrest := rest_of_block_bound n (k + 2) j hj hρs_lo hdist
    have ⟨hre_ge, hre_nn⟩ := re_zeta_mul_on_circle_ge (k + 2) j hρs_lo hdist
    have hother := tsum_other_blocks_bound k n hlo hhi hz_le_k5
    set E := Real.exp (r (k + 2) * (zeta (M (k + 2)) ^ j * z).re)
    have hE_ge1 : 1 ≤ E := Real.one_le_exp (mul_nonneg (r_pos _).le hre_nn)
    -- Bound Block (k + 1) at z using rho2 k n + 4 * delta (k + 2) ≤ ρs
    have hblk1 : c (k + 1) * r (k + 1) ^ n * (M (k + 1) : ℝ) * Real.exp (r (k + 1) * ‖z‖) ≤
        (1 / 32 : ℝ) * c (k + 2) * r (k + 2) ^ n * E := by
      set D2 := r (k + 2) * Real.cos (Real.pi / (M (k + 2) : ℝ)) - r (k + 1)
      have ⟨hD2_lo, _, _⟩ := transition_denoms k
      have hD2_pos : 0 < D2 := by linarith [r_pos (k + 2)]
      have h4r : 4 * r (k + 1) ≤ r (k + 2) := r_step_mul_four (k + 1)
      have hexp_cmp : r (k + 1) * ‖z‖ - r (k + 2) * (zeta (M (k + 2)) ^ j * z).re ≤ -D2 * rho2 k n := by
        have h1 : r (k + 1) * ‖z‖ ≤ r (k + 1) * (ρs + delta (k + 2)) :=
          mul_le_mul_of_nonneg_left hz_norm (r_pos _).le
        have h2 : r (k + 2) * (ρs * Real.cos (Real.pi / (M (k + 2) : ℝ)) - delta (k + 2)) ≤
            r (k + 2) * (zeta (M (k + 2)) ^ j * z).re :=
          mul_le_mul_of_nonneg_left hre_ge (r_pos _).le
        have h3 : (r (k + 1) + r (k + 2)) * delta (k + 2) - D2 * ρs ≤ -D2 * rho2 k n := by
          have hdel_pos := delta_pos (k + 2)
          have hcoef : r (k + 1) + r (k + 2) ≤ 4 * D2 := by linarith
          nlinarith
        dsimp [D2] at h3 ⊢
        linarith
      have hD2_rho2 : D2 * rho2 k n =
          Real.log ((32 * (M (k + 1) : ℝ) * c (k + 1) * r (k + 1) ^ n) / (c (k + 2) * r (k + 2) ^ n)) := by
        dsimp [rho2, D2]
        exact mul_div_cancel₀ _ hD2_pos.ne'
      have hratio_pos : 0 < (32 * (M (k + 1) : ℝ) * c (k + 1) * r (k + 1) ^ n) / (c (k + 2) * r (k + 2) ^ n) := by
        have := c_pos (k + 1); have := c_pos (k + 2); have := r_pos (k + 1)
        have := r_pos (k + 2); have := M_pos (k + 1); positivity
      have hexp_le : Real.exp (r (k + 1) * ‖z‖) / E ≤
          (c (k + 2) * r (k + 2) ^ n) / (32 * (M (k + 1) : ℝ) * c (k + 1) * r (k + 1) ^ n) := by
        dsimp [E]
        rw [← Real.exp_sub]
        calc Real.exp (r (k + 1) * ‖z‖ - r (k + 2) * (zeta (M (k + 2)) ^ j * z).re)
            ≤ Real.exp (-(D2 * rho2 k n)) := Real.exp_le_exp.mpr (by linarith)
          _ = (Real.exp (D2 * rho2 k n))⁻¹ := Real.exp_neg _
          _ = _ := by rw [hD2_rho2, Real.exp_log hratio_pos, inv_div]
      have hmul := (div_le_iff₀ (Real.exp_pos _)).mp hexp_le
      have hcross : (c (k + 1) * r (k + 1) ^ n * (M (k + 1) : ℝ)) * Real.exp (r (k + 1) * ‖z‖) ≤
          (c (k + 1) * r (k + 1) ^ n * (M (k + 1) : ℝ)) *
            ((c (k + 2) * r (k + 2) ^ n) / (32 * (M (k + 1) : ℝ) * c (k + 1) * r (k + 1) ^ n) * E) :=
        mul_le_mul_of_nonneg_left hmul (by have := c_pos (k+1); have := r_pos (k+1); positivity)
      have hsimp : (c (k + 1) * r (k + 1) ^ n * (M (k + 1) : ℝ)) *
          ((c (k + 2) * r (k + 2) ^ n) / (32 * (M (k + 1) : ℝ) * c (k + 1) * r (k + 1) ^ n) * E) =
          (1 / 32 : ℝ) * c (k + 2) * r (k + 2) ^ n * E := by
        have hM1ne : (M (k + 1) : ℝ) ≠ 0 := by exact_mod_cast (M_pos (k + 1)).ne'
        have hc1ne : c (k + 1) ≠ 0 := (c_pos (k + 1)).ne'
        have hr1ne : r (k + 1) ^ n ≠ 0 := (pow_pos (r_pos (k + 1)) n).ne'
        field_simp [hM1ne, hc1ne, hr1ne]
      linarith
    have hblk1_norm : ‖(c (k + 1) : ℂ) * gDeriv n (k + 1) z‖ ≤
        (1 / 32 : ℝ) * c (k + 2) * r (k + 2) ^ n * E := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (c_pos _).le]
      calc c (k + 1) * ‖gDeriv n (k + 1) z‖
          ≤ c (k + 1) * (r (k + 1) ^ n * (M (k + 1) : ℝ) * Real.exp (r (k + 1) * ‖z‖)) :=
            mul_le_mul_of_nonneg_left (norm_gDeriv_le n (k + 1) z) (c_pos _).le
        _ = c (k + 1) * r (k + 1) ^ n * (M (k + 1) : ℝ) * Real.exp (r (k + 1) * ‖z‖) := by ring
        _ ≤ (1 / 32 : ℝ) * c (k + 2) * r (k + 2) ^ n * E := hblk1
    have hcr1_le : c (k + 1) * r (k + 1) ^ n ≤ (1 / 32 : ℝ) * c (k + 2) * r (k + 2) ^ n * E := by
      have hM1 : (1 : ℝ) ≤ (M (k + 1) : ℝ) := by exact_mod_cast (M_pos (k + 1))
      have he1 : 1 ≤ Real.exp (r (k + 1) * ‖z‖) := Real.one_le_exp (mul_nonneg (r_pos _).le (norm_nonneg _))
      have hnn : 0 ≤ c (k + 1) * r (k + 1) ^ n := mul_nonneg (c_pos _).le (pow_nonneg (r_pos _).le _)
      have hprod : 1 ≤ (M (k + 1) : ℝ) * Real.exp (r (k + 1) * ‖z‖) := by nlinarith
      nlinarith
    have hsplit_all : fDeriv n z - twoTerm n (k + 2) j z =
        (fDeriv n z - ((c (k + 1) : ℂ) * gDeriv n (k + 1) z + (c (k + 2) : ℂ) * gDeriv n (k + 2) z)) +
        (c (k + 1) : ℂ) * gDeriv n (k + 1) z +
        ((c (k + 2) : ℂ) * gDeriv n (k + 2) z - twoTerm n (k + 2) j z) := by ring
    have htotal : ‖fDeriv n z - twoTerm n (k + 2) j z‖ ≤
        (1 / 64 * (1 / 32) + 1 / 64 + 1 / 32 + 1 / 16 : ℝ) * c (k + 2) * r (k + 2) ^ n * E := by
      rw [hsplit_all]
      have htri1 := norm_add_le
        ((fDeriv n z - ((c (k + 1) : ℂ) * gDeriv n (k + 1) z + (c (k + 2) : ℂ) * gDeriv n (k + 2) z)) +
          (c (k + 1) : ℂ) * gDeriv n (k + 1) z)
        ((c (k + 2) : ℂ) * gDeriv n (k + 2) z - twoTerm n (k + 2) j z)
      have htri2 := norm_add_le
        (fDeriv n z - ((c (k + 1) : ℂ) * gDeriv n (k + 1) z + (c (k + 2) : ℂ) * gDeriv n (k + 2) z))
        ((c (k + 1) : ℂ) * gDeriv n (k + 1) z)
      have hcr2_le : c (k + 2) * r (k + 2) ^ n ≤ c (k + 2) * r (k + 2) ^ n * E :=
        le_mul_of_one_le_right (mul_nonneg (c_pos _).le (pow_nonneg (r_pos _).le _)) hE_ge1
      linarith
    have hpos_dom : 0 < c (k + 2) * r (k + 2) ^ n * E := by
      have := c_pos (k + 2); have := r_pos (k + 2); have := Real.exp_pos (r (k + 2) * (zeta (M (k + 2)) ^ j * z).re)
      positivity
    linarith
  obtain ⟨z, hz_cl, hf0⟩ := hrouche
  refine ⟨z, hf0, ?_⟩
  have h1 : ‖z - z₀‖ ≤ delta (k + 2) := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz_cl
  have h2 : ‖z₀ - (ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 2) j : ℂ))‖ = |ρs - ρ| := by
    dsimp [z₀]
    rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one]
  have htri : ‖z - (ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 2) j : ℂ))‖ ≤
      ‖z - z₀‖ + ‖z₀ - (ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 2) j : ℂ))‖ := by
    simpa [sub_add_sub_cancel] using norm_add_le (z - z₀) (z₀ - (ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 2) j : ℂ)))
  linarith [delta_lt_eps (k + 2), ε_pos (k + 2)]

private lemma exists_near_rayAngle (b : ℕ) (z₀ : ℂ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) :
    ∃ j < M b, ‖(ρ : ℂ) * Complex.exp (Complex.I * (rayAngle b j : ℂ)) - z₀‖ ≤
      |ρ - ‖z₀‖| + ρ * Real.pi / (M b : ℝ) := by
  by_cases hz0 : z₀ = 0
  · subst hz0
    refine ⟨0, M_pos b, ?_⟩
    rw [sub_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0,
      mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one, norm_zero, sub_zero, abs_of_nonneg hρ0]
    have : 0 ≤ ρ * Real.pi / (M b : ℝ) := by positivity
    linarith
  · set θ := z₀.arg
    have hMpos : (0 : ℝ) < (M b : ℝ) := by exact_mod_cast M_pos b
    set m : ℤ := round ((-(θ * (M b : ℝ) / (2 * Real.pi)) - 1 / 2))
    set j : ℕ := Int.toNat (m % (M b : ℤ))
    have hmod_nn : 0 ≤ m % (M b : ℤ) := Int.emod_nonneg m (by exact_mod_cast (M_pos b).ne')
    have hmod_lt : m % (M b : ℤ) < (M b : ℤ) := Int.emod_lt_of_pos m (by exact_mod_cast M_pos b)
    have hj_lt : j < M b := by dsimp [j]; omega
    have hj_cast : (j : ℤ) = m % (M b : ℤ) := Int.toNat_of_nonneg hmod_nn
    refine ⟨j, hj_lt, ?_⟩
    have hround : |(-(θ * (M b : ℝ) / (2 * Real.pi)) - 1 / 2) - (m : ℝ)| ≤ 1 / 2 := abs_sub_round _
    have hq : ∃ q : ℤ, (j : ℤ) = m + q * (M b : ℤ) := ⟨-(m / (M b : ℤ)), by
      have hdiv := Int.emod_add_mul_ediv m (M b : ℤ)
      linear_combination hj_cast + hdiv⟩
    obtain ⟨q, hq⟩ := hq
    have hexp_eq : Complex.exp (Complex.I * (rayAngle b j : ℂ)) =
        Complex.exp (Complex.I * (-((2 * (m : ℝ) + 1) * Real.pi / (M b : ℝ)) : ℝ)) := by
      dsimp [rayAngle]
      have hR : (j : ℝ) = (m : ℝ) + (q : ℝ) * (M b : ℝ) := by exact_mod_cast hq
      have harg : Complex.I * (-((2 * (j : ℝ) + 1) * Real.pi / (M b : ℝ)) : ℝ) =
          Complex.I * (-((2 * (m : ℝ) + 1) * Real.pi / (M b : ℝ)) : ℝ) +
          ((-q : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hR]
        push_cast
        have hMC : ((M b : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (M_pos b).ne'
        field_simp [hMC]
        ring
      rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    set φ := -((2 * (m : ℝ) + 1) * Real.pi / (M b : ℝ))
    have hφ_θ : |φ - θ| ≤ Real.pi / (M b : ℝ) := by
      have heq : φ - θ = ((-(θ * (M b : ℝ) / (2 * Real.pi)) - 1 / 2) - (m : ℝ)) * (2 * Real.pi / (M b : ℝ)) := by
        dsimp [φ]
        field_simp [hMpos.ne', Real.pi_pos.ne']
        ring
      rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi / (M b : ℝ))]
      calc |(-(θ * (M b : ℝ) / (2 * Real.pi)) - 1 / 2) - (m : ℝ)| * (2 * Real.pi / (M b : ℝ))
          ≤ (1 / 2) * (2 * Real.pi / (M b : ℝ)) :=
            mul_le_mul_of_nonneg_right hround (by positivity)
        _ = Real.pi / (M b : ℝ) := by ring
    have hz0_polar : z₀ = (‖z₀‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I z₀).symm
    have hsplit : (ρ : ℂ) * Complex.exp (Complex.I * (rayAngle b j : ℂ)) - z₀ =
        ((ρ - ‖z₀‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) +
        (ρ : ℂ) * (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I)) := by
      conv_lhs => rw [hexp_eq, hz0_polar]
      have h1 : Complex.I * (φ : ℂ) = (φ : ℂ) * Complex.I := mul_comm _ _
      rw [h1]
      push_cast; ring
    have hexp_lip : ‖Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ |φ - θ| := by
      have h1 : Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I) =
          Complex.exp ((θ : ℂ) * Complex.I) * (Complex.exp (Complex.I * ((φ - θ : ℝ) : ℂ)) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]; congr 1; push_cast; ring
      rw [h1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
        Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
      have hsin : |Real.sin ((φ - θ) / 2)| ≤ |(φ - θ) / 2| := Real.abs_sin_le_abs
      rw [abs_div, abs_two] at hsin
      linarith
    rw [hsplit]
    calc ‖((ρ - ‖z₀‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) +
            (ρ : ℂ) * (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I))‖
        ≤ ‖((ρ - ‖z₀‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ +
          ‖(ρ : ℂ) * (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I))‖ :=
          norm_add_le _ _
      _ = |ρ - ‖z₀‖| + ρ * ‖Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one,
            norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0]
      _ ≤ |ρ - ‖z₀‖| + ρ * |φ - θ| := by linarith [mul_le_mul_of_nonneg_left hexp_lip hρ0]
      _ ≤ |ρ - ‖z₀‖| + ρ * (Real.pi / (M b : ℝ)) := by linarith [mul_le_mul_of_nonneg_left hφ_θ hρ0]
      _ = |ρ - ‖z₀‖| + ρ * Real.pi / (M b : ℝ) := by ring

private lemma exists_zero_for_stage (k n : ℕ) (hlo : Hmid k ≤ n) (hhi : n ≤ Hmid (k + 1))
    (z₀ : ℂ) (hz₀ : ‖z₀‖ ≤ R (k + 1)) :
    ∃ z : ℂ, fDeriv n z = 0 ∧ ‖z - z₀‖ < ε (k + 1) := by
  set a1 := rho1 k n - 2 * delta (k + 1) - ε (k + 1) / 32
  set a2 := rho2 k n + 4 * delta (k + 2) + ε (k + 2) / 32
  have hε1 : 0 < ε (k + 1) := ε_pos (k + 1)
  have hε2 : ε (k + 2) = ε (k + 1) / 4 := ε_succ (k + 1)
  have hdel1 := delta_lt_eps (k + 1)
  have hdel2 := delta_lt_eps (k + 2)
  have hM1_ang : ∀ ρ : ℝ, ρ ≤ R (k + 1) + 1 → ρ * Real.pi / (M (k + 1) : ℝ) < ε (k + 1) / 4 := by
    intro ρ hρ
    have hM1 : (M (k + 1) : ℝ) = 32 * ((k : ℝ) + 3) * (4 : ℝ) ^ (k + 2) := by
      dsimp [M]; push_cast; ring
    have hε_eq : ε (k + 1) = 1 / (4 : ℝ) ^ (k + 2) := by dsimp [ε]; rw [one_div_pow]
    have hR : R (k + 1) + 1 = (k : ℝ) + 4 := by dsimp [R]; push_cast; ring
    rw [hε_eq, div_div, div_lt_div_iff₀ (by exact_mod_cast M_pos (k + 1)) (by positivity)]
    rw [hM1]
    have h4pos : (0 : ℝ) < (4 : ℝ) ^ (k + 2) := by positivity
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hρ' : ρ ≤ (k : ℝ) + 4 := by linarith
    have h1 : ρ * Real.pi ≤ ((k : ℝ) + 4) * 4 := by nlinarith [Real.pi_pos]
    have h2 : 4 * (((k : ℝ) + 4) * 4) < 32 * ((k : ℝ) + 3) := by linarith
    nlinarith
  have hM2_ang : ∀ ρ : ℝ, ρ ≤ R (k + 1) + 1 → ρ * Real.pi / (M (k + 2) : ℝ) < ε (k + 1) / 8 := by
    intro ρ hρ
    have h1 := hM1_ang ρ hρ
    have hM2_ge : 2 * (M (k + 1) : ℝ) ≤ (M (k + 2) : ℝ) := by
      dsimp [M]
      have h4 : 4 ^ (k + 3) = 4 * 4 ^ (k + 2) := by rw [pow_succ]; ring
      have hnat : 2 * (32 * (k + 1 + 2) * 4 ^ (k + 2)) ≤ 32 * (k + 2 + 2) * (4 * 4 ^ (k + 2)) := by
        nlinarith [Nat.one_le_pow (k + 2) 4 (by norm_num)]
      rw [h4]
      exact_mod_cast hnat
    have hM1pos : (0 : ℝ) < (M (k + 1) : ℝ) := by exact_mod_cast M_pos (k + 1)
    by_cases hρ0 : ρ ≤ 0
    · have : ρ * Real.pi / (M (k + 2) : ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hρ0 Real.pi_pos.le) (by positivity)
      linarith
    · push Not at hρ0
      calc ρ * Real.pi / (M (k + 2) : ℝ)
          ≤ ρ * Real.pi / (2 * (M (k + 1) : ℝ)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hM2_ge
        _ = (ρ * Real.pi / (M (k + 1) : ℝ)) / 2 := by ring
        _ < (ε (k + 1) / 4) / 2 := by linarith
        _ = ε (k + 1) / 8 := by ring
  by_cases hcase1 : ε (k + 1) / 4 < a1 ∧ ‖z₀‖ ≤ a1
  · -- Use inner block k + 1!
    set ρ := max ‖z₀‖ (ε (k + 1) / 8)
    have hρ_lo : ε (k + 1) / 8 ≤ ρ := le_max_right _ _
    have hρ_hi : ρ ≤ R (k + 1) + 1 := by
      apply max_le (by linarith)
      have : ε (k + 1) ≤ 1 := by dsimp [ε]; exact pow_le_one₀ (by norm_num) (by norm_num)
      dsimp [R]; linarith
    have hρ_a1 : ρ ≤ a1 := max_le hcase1.2 (by linarith)
    obtain ⟨j, hj, hang⟩ := exists_near_rayAngle (k + 1) z₀ ρ (by linarith)
    obtain ⟨z, hf0, hclose⟩ := exists_zero_inner_block k n j hj hlo hhi hρ_lo hρ_hi hρ_a1
    have hdist_r : |ρ - ‖z₀‖| ≤ ε (k + 1) / 8 := by
      rw [abs_of_nonneg (by linarith [le_max_left ‖z₀‖ (ε (k + 1) / 8)])]
      have : ρ ≤ ‖z₀‖ + ε (k + 1) / 8 := max_le (by linarith) (by linarith [norm_nonneg z₀])
      linarith
    have htri : ‖z - z₀‖ ≤ ‖z - (ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 1) j : ℂ))‖ +
        ‖(ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 1) j : ℂ)) - z₀‖ := by
      simpa [sub_add_sub_cancel] using
        norm_add_le (z - (ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 1) j : ℂ)))
          ((ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 1) j : ℂ)) - z₀)
    refine ⟨z, hf0, ?_⟩
    linarith [hM1_ang ρ hρ_hi]
  · -- Use outer block k + 2!
    have ha1_le : a1 ≤ R (k + 1) := by
      by_contra hgt
      push Not at hgt
      have hε_le : ε (k + 1) ≤ 1 := by dsimp [ε]; exact pow_le_one₀ (by norm_num) (by norm_num)
      have hR_pos : 1 ≤ R (k + 1) := by dsimp [R]; linarith
      exact hcase1 ⟨by linarith, hz₀.trans hgt.le⟩
    have hρ1_le : rho1 k n ≤ R (k + 1) + 2 := by
      have : ε (k + 1) ≤ 1 := by dsimp [ε]; exact pow_le_one₀ (by norm_num) (by norm_num)
      dsimp [a1] at ha1_le
      linarith
    have hgap := rho2_sub_rho1_le k n hρ1_le
    have ha_gap : a2 - a1 < ε (k + 1) / 4 := by
      dsimp [a1, a2]
      linarith
    set ρ := max ‖z₀‖ (max (ε (k + 2) / 8) a2)
    have hρ_lo : ε (k + 2) / 8 ≤ ρ := (le_max_left _ _).trans (le_max_right _ _)
    have hρ_a2 : a2 ≤ ρ := (le_max_right _ _).trans (le_max_right _ _)
    have hρ_sub : |ρ - ‖z₀‖| < (3 / 4 : ℝ) * ε (k + 1) := by
      rw [abs_of_nonneg (by linarith [le_max_left ‖z₀‖ (max (ε (k + 2) / 8) a2)])]
      have h1 : ε (k + 2) / 8 - ‖z₀‖ < (3 / 4 : ℝ) * ε (k + 1) := by
        linarith [norm_nonneg z₀]
      have h2 : a2 - ‖z₀‖ < (3 / 4 : ℝ) * ε (k + 1) := by
        by_cases ha1_small : a1 ≤ ε (k + 1) / 4
        · linarith [norm_nonneg z₀]
        · push Not at ha1_small
          have hz_gt : a1 < ‖z₀‖ := by
            by_contra hle
            push Not at hle
            exact hcase1 ⟨ha1_small, hle⟩
          linarith
      have hmax : ρ < ‖z₀‖ + (3 / 4 : ℝ) * ε (k + 1) := by
        apply max_lt (by linarith)
        exact max_lt (by linarith) (by linarith)
      linarith
    have hρ_hi : ρ ≤ R (k + 1) + 1 := by
      have hε_le : ε (k + 1) ≤ 1 := by dsimp [ε]; exact pow_le_one₀ (by norm_num) (by norm_num)
      have hle := (abs_le.mp hρ_sub.le).2
      linarith
    obtain ⟨j, hj, hang⟩ := exists_near_rayAngle (k + 2) z₀ ρ (by linarith [ε_pos (k + 2)])
    obtain ⟨z, hf0, hclose⟩ := exists_zero_outer_block k n j hj hlo hhi hρ_lo hρ_hi hρ_a2
    have htri : ‖z - z₀‖ ≤ ‖z - (ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 2) j : ℂ))‖ +
        ‖(ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 2) j : ℂ)) - z₀‖ := by
      simpa [sub_add_sub_cancel] using
        norm_add_le (z - (ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 2) j : ℂ)))
          ((ρ : ℂ) * Complex.exp (Complex.I * (rayAngle (k + 2) j : ℂ)) - z₀)
    refine ⟨z, hf0, ?_⟩
    linarith [hM2_ang ρ hρ_hi]

/- ### Section 7: Final theorem -/

theorem solution : type_of% @Erdos906.erdos_906 := by
  refine ⟨f, f_transcendental, f_differentiable, fun seq hseq => ?_⟩
  rw [Metric.dense_iff]
  intro z₀ δ hδ
  -- Pick K large enough that R (K + 1) ≥ ‖z₀‖ and ε (K + 1) < δ
  obtain ⟨K1, hK1⟩ := exists_nat_gt ‖z₀‖
  have htend : Tendsto (fun k : ℕ => ε (k + 1)) atTop (𝓝 0) := by
    have hrew : (fun k : ℕ => ε (k + 1)) = (fun k : ℕ => (1 / 4 : ℝ) ^ k * ((1 / 4 : ℝ) ^ 2)) := by
      ext k; dsimp [ε]; rw [pow_succ, pow_succ]; ring
    rw [hrew]
    have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).mul_const ((1 / 4 : ℝ) ^ 2)
    rwa [zero_mul] at hlim
  obtain ⟨K2, hK2⟩ := Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds hδ))
  set K := max K1 K2
  -- Pick m so that seq m ≥ Hmid K
  set m := Hmid K
  have hseq_ge : Hmid K ≤ seq m := hseq.id_le (Hmid K)
  -- Find the unique k ≥ K with Hmid k ≤ seq m < Hmid (k + 1)
  have hex : ∃ j : ℕ, seq m < Hmid (j + 1) := by
    refine ⟨seq m, ?_⟩
    have h1 : seq m + 1 ≤ Hmid (seq m + 1) := Hmid_strictMono.id_le (seq m + 1)
    omega
  set k := Nat.find hex
  have hk_hi : seq m < Hmid (k + 1) := Nat.find_spec hex
  have hk_ge_K : K ≤ k := by
    by_contra hlt
    push Not at hlt
    have : Hmid (k + 1) ≤ Hmid K := Hmid_strictMono.monotone (by omega)
    omega
  have hk_lo : Hmid k ≤ seq m := by
    cases hk0 : k with
    | zero =>
      have hK0 : K = 0 := by omega
      rw [hK0] at hseq_ge
      exact hseq_ge
    | succ k' =>
      have hmin := Nat.find_min hex (show k' < Nat.find hex by change k' < k; rw [hk0]; exact Nat.lt_succ_self k')
      omega
  have hz0_le : ‖z₀‖ ≤ R (k + 1) := by
    dsimp [R]
    have h1 : (K1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (le_trans (le_max_left K1 K2) hk_ge_K)
    push_cast
    linarith
  obtain ⟨z, hf0, hclose⟩ := exists_zero_for_stage k (seq m) hk_lo hk_hi.le z₀ hz0_le
  refine ⟨z, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have hε_lt : ε (k + 1) < δ := hK2 k (le_trans (le_max_right K1 K2) hk_ge_K)
    exact lt_trans hclose hε_lt
  · exact ⟨m, by rw [iteratedDeriv_f]; exact hf0⟩

end OMA.Erdos906

theorem OMA.solution : type_of% @Erdos906.erdos_906 :=
  OMA.Erdos906.solution
