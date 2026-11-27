import FormalConjectures.ErdosProblems.«513»

open scoped Nat Real
open Filter Polynomial

private lemma ratio_nonneg (r : ℝ) (f : ℂ → ℂ) : 0 ≤ Erdos513.ratio r f :=
  div_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)
    (Real.iSup_nonneg fun _ => norm_nonneg _)

private lemma sphere_bddAbove {r : ℝ} {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    BddAbove (Set.range fun z : {z : ℂ // ‖z‖ = r} => ‖g z‖) := by
  have hc : IsCompact ((fun z : ℂ => ‖g z‖) '' Metric.sphere 0 r) :=
    (isCompact_sphere 0 r).image hg.continuous.norm
  refine hc.bddAbove.mono ?_
  rintro _ ⟨⟨z, hz⟩, rfl⟩
  exact ⟨z, mem_sphere_zero_iff_norm.mpr hz, rfl⟩

private lemma term_le_sup_sphere {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (n : ℕ) :
    ‖iteratedDeriv n g 0 * (n ! : ℝ)⁻¹ * r ^ n‖ ≤ ⨆ z : {z : ℂ // ‖z‖ = r}, ‖g z‖ := by
  set M : ℝ := ⨆ z : {z : ℂ // ‖z‖ = r}, ‖g z‖
  have h_sphere : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖g z‖ ≤ M :=
    fun z hz => le_ciSup (sphere_bddAbove hg) ⟨z, mem_sphere_zero_iff_norm.mp hz⟩
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    hg.diffContOnCl h_sphere
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)),
    Real.norm_of_nonneg hr.le]
  calc ‖iteratedDeriv n g 0‖ * (n ! : ℝ)⁻¹ * r ^ n
      ≤ (n ! * M / r ^ n) * (n ! : ℝ)⁻¹ * r ^ n := by gcongr
    _ = M := by
      have hn : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hrn : r ^ n ≠ 0 := pow_ne_zero n hr.ne'
      field_simp

private lemma ratio_le_one {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Erdos513.ratio r g ≤ 1 := by
  set M : ℝ := ⨆ z : {z : ℂ // ‖z‖ = r}, ‖g z‖
  have hM_nonneg : 0 ≤ M := Real.iSup_nonneg fun _ => norm_nonneg _
  by_cases hM0 : M = 0
  · simp [Erdos513.ratio, show (⨆ z : {z : ℂ // ‖z‖ = r}, ‖g z‖) = 0 from hM0]
  · exact div_le_one_of_le₀ (ciSup_le (term_le_sup_sphere hr hg)) hM_nonneg

private lemma liminf_ratio_le_one {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Filter.liminf (fun r : ℝ => Erdos513.ratio r g) Filter.atTop ≤ 1 := by
  have hbdd : Filter.atTop.IsBoundedUnder (· ≥ ·) (fun r : ℝ => Erdos513.ratio r g) :=
    ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun r => ratio_nonneg r g)⟩
  exact Filter.liminf_le_of_frequently_le
    ((Filter.eventually_gt_atTop 0).mono fun _ hr => ratio_le_one hr hg).frequently hbdd

private noncomputable def a_seq (n : ℕ) : ℂ := (-1 / 4 : ℂ) ^ (n * (n - 1) / 2)

private noncomputable def f_entire (z : ℂ) : ℂ := ∑' n : ℕ, a_seq n * z ^ n

private lemma norm_a_seq (n : ℕ) : ‖a_seq n‖ = (1 / 4 : ℝ) ^ (n * (n - 1) / 2) := by
  have h14 : ‖(-1 / 4 : ℂ)‖ = (1 / 4 : ℝ) := by norm_num
  rw [a_seq, norm_pow, h14]

private lemma summable_norm_a_mul_pow (z : ℂ) : Summable (fun n : ℕ => ‖a_seq n * z ^ n‖) := by
  set K : ℕ := Nat.ceil ‖z‖
  have hzK : ‖z‖ ≤ (4 : ℝ) ^ K := by
    have h1 : ‖z‖ ≤ (K : ℝ) := Nat.le_ceil _
    have h2 : (K : ℝ) ≤ (4 : ℝ) ^ K := by
      exact_mod_cast (Nat.lt_pow_self (a := 4) (by norm_num : 1 < 4) (n := K)).le
    linarith
  have h_geom : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h_tail : Summable (fun n : ℕ => ‖a_seq (n + (2 * K + 3)) * z ^ (n + (2 * K + 3))‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (h_geom.comp_injective (add_left_injective (2 * K + 3)))
    set m : ℕ := n + (2 * K + 3)
    have hm_exp : (K + 1) * m ≤ m * (m - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      have hm2 : 2 * (K + 1) ≤ m - 1 := by omega
      nlinarith
    rw [norm_mul, norm_a_seq, norm_pow]
    calc (1 / 4 : ℝ) ^ (m * (m - 1) / 2) * ‖z‖ ^ m
        ≤ (1 / 4 : ℝ) ^ ((K + 1) * m) * ((4 : ℝ) ^ K) ^ m := by
          exact mul_le_mul
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm_exp)
            (pow_le_pow_left₀ (norm_nonneg _) hzK m)
            (by positivity) (by positivity)
      _ = (1 / 4 : ℝ) ^ m := by
          rw [pow_mul (1 / 4 : ℝ), ← mul_pow]
          have h14 : (1 / 4 : ℝ) ^ (K + 1) * (4 : ℝ) ^ K = 1 / 4 := by
            rw [pow_succ, mul_right_comm, ← mul_pow]
            norm_num
          rw [h14]
  exact (summable_nat_add_iff (2 * K + 3)).mp h_tail

private lemma f_hasFPowerSeries :
    HasFPowerSeriesOnBall f_entire (FormalMultilinearSeries.ofScalars ℂ a_seq) 0 ⊤ := by
  refine ⟨?_, by simp, ?_⟩
  · rw [top_le_iff]
    refine FormalMultilinearSeries.radius_eq_top_of_summable_norm _ fun r => ?_
    simpa [FormalMultilinearSeries.ofScalars_norm] using summable_norm_a_mul_pow (r : ℂ)
  · intro y _
    simpa [f_entire, FormalMultilinearSeries.ofScalars, smul_eq_mul, mul_comm] using
      (summable_norm_a_mul_pow y).of_norm.hasSum

private lemma f_differentiable : Differentiable ℂ f_entire :=
  fun z => (f_hasFPowerSeries.analyticAt_of_mem (by simp)).differentiableAt

private lemma f_iteratedDeriv (n : ℕ) : iteratedDeriv n f_entire 0 = (n ! : ℂ) * a_seq n := by
  have ha : AnalyticOn ℂ f_entire Set.univ :=
    fun z _ => (f_hasFPowerSeries.analyticAt_of_mem (by simp)).analyticWithinAt
  rw [iteratedDeriv_eq_iteratedFDeriv, f_hasFPowerSeries.iteratedFDeriv_eq_sum ha]
  simp [FormalMultilinearSeries.ofScalars, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

private lemma f_term_norm (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ‖iteratedDeriv n f_entire 0 * (n ! : ℝ)⁻¹ * r ^ n‖ =
      (1 / 4 : ℝ) ^ (n * (n - 1) / 2) * r ^ n := by
  rw [f_iteratedDeriv, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h_eq : (n ! : ℂ) * a_seq n * (n ! : ℂ)⁻¹ * (r : ℂ) ^ n = a_seq n * (r : ℂ) ^ n := by
    field_simp
  rw [h_eq, norm_mul, norm_a_seq, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr]

private lemma poly_sos_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let u : ℝ := t + 1
    let A : ℝ := u + (1 / 4 : ℝ) * u ^ 3
    let B : ℝ := u ^ 2 - 1 / 4
    let E : ℝ := 1 / 4 + u ^ 2
    let D : ℝ := (1 / 2 : ℝ) * u ^ 3
    let c0 : ℝ := A ^ 2 + E ^ 2
    let c1 : ℝ := 2 * (A * B - E * D)
    let a_quad : ℝ := u ^ 2 + u ^ 4 - u ^ 3 / 2
    0 ≤ 4 * a_quad * ((19 / 10 : ℝ) ^ 2 * u ^ 4 - c0) - c1 ^ 2 := by
  dsimp only
  have h_id : 25600 * (4 * ((t + 1) ^ 2 + (t + 1) ^ 4 - (t + 1) ^ 3 / 2) *
      ((19 / 10 : ℝ) ^ 2 * (t + 1) ^ 4 -
        ((t + 1 + (1 / 4 : ℝ) * (t + 1) ^ 3) ^ 2 + (1 / 4 + (t + 1) ^ 2) ^ 2)) -
      (2 * ((t + 1 + (1 / 4 : ℝ) * (t + 1) ^ 3) * ((t + 1) ^ 2 - 1 / 4) -
        (1 / 4 + (t + 1) ^ 2) * ((1 / 2 : ℝ) * (t + 1) ^ 3))) ^ 2) =
      64496 + 941472 * t + 4091280 * t ^ 2 + 8961344 * t ^ 3 + 11519120 * t ^ 4 +
        8948896 * t ^ 5 + 3842032 * t ^ 6 + 47744 * t ^ 7 +
        295936 * t ^ 7 * (1 - t) + 124800 * t ^ 7 * (1 - t ^ 2) +
        12800 * t ^ 7 * (1 - t ^ 3) := by ring
  have h1t : 0 ≤ 1 - t := by linarith
  have h1t2 : 0 ≤ 1 - t ^ 2 := by nlinarith
  have h1t3 : 0 ≤ 1 - t ^ 3 := by nlinarith [sq_nonneg t]
  have h_pos : 0 ≤ 25600 * (4 * ((t + 1) ^ 2 + (t + 1) ^ 4 - (t + 1) ^ 3 / 2) *
      ((19 / 10 : ℝ) ^ 2 * (t + 1) ^ 4 -
        ((t + 1 + (1 / 4 : ℝ) * (t + 1) ^ 3) ^ 2 + (1 / 4 + (t + 1) ^ 2) ^ 2)) -
      (2 * ((t + 1 + (1 / 4 : ℝ) * (t + 1) ^ 3) * ((t + 1) ^ 2 - 1 / 4) -
        (1 / 4 + (t + 1) ^ 2) * ((1 / 2 : ℝ) * (t + 1) ^ 3))) ^ 2) := by
    rw [h_id]
    positivity
  exact nonneg_of_mul_nonneg_right h_pos (by norm_num)

private lemma norm_P_le_aux (u c s : ℝ) (hu1 : 1 ≤ u) (hu2 : u ≤ 2) (hcs : c ^ 2 + s ^ 2 = 1) :
    ((u + (1 / 4 : ℝ) * u ^ 3) + (u ^ 2 - 1 / 4) * c - (1 / 2 : ℝ) * u ^ 3 * c ^ 2) ^ 2 +
      s ^ 2 * ((1 / 4 + u ^ 2) - (1 / 2 : ℝ) * u ^ 3 * c) ^ 2 ≤ ((19 / 10 : ℝ) * u ^ 2) ^ 2 := by
  have hc_abs : -1 ≤ c ∧ c ≤ 1 := by
    have hc2 : c ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
    exact ⟨by nlinarith, by nlinarith⟩
  set A : ℝ := u + (1 / 4 : ℝ) * u ^ 3
  set B : ℝ := u ^ 2 - 1 / 4
  set E : ℝ := 1 / 4 + u ^ 2
  set D : ℝ := (1 / 2 : ℝ) * u ^ 3
  set c0 : ℝ := A ^ 2 + E ^ 2
  set c1 : ℝ := 2 * (A * B - E * D)
  set a_quad : ℝ := u ^ 2 + u ^ 4 - u ^ 3 / 2
  have ha_pos : 0 < a_quad := by
    have hfac : a_quad = u ^ 2 * ((u - 1 / 4) ^ 2 + 15 / 16) := by
      dsimp [a_quad]; ring
    rw [hfac]
    positivity
  have h_normSq : (A + B * c - D * c ^ 2) ^ 2 + s ^ 2 * (E - D * c) ^ 2 =
      c0 + c1 * c - u ^ 2 * (1 + u ^ 2) * c ^ 2 + (1 / 2 : ℝ) * u ^ 3 * c ^ 3 := by
    have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith
    rw [hs2]
    dsimp [c0, c1, A, B, E, D]
    ring
  have hc3_le : c ^ 3 ≤ c ^ 2 := by nlinarith [sq_nonneg c, hc_abs.2]
  have h_quad : (A + B * c - D * c ^ 2) ^ 2 + s ^ 2 * (E - D * c) ^ 2 ≤
      c0 + c1 * c - a_quad * c ^ 2 := by
    rw [h_normSq]
    have h1 : (1 / 2 : ℝ) * u ^ 3 * c ^ 3 ≤ (1 / 2 : ℝ) * u ^ 3 * c ^ 2 :=
      mul_le_mul_of_nonneg_left hc3_le (by positivity)
    dsimp [a_quad]
    linarith
  have h_comp_sq : 4 * a_quad * (c0 + c1 * c - a_quad * c ^ 2) ≤ 4 * a_quad * c0 + c1 ^ 2 := by
    nlinarith [sq_nonneg (2 * a_quad * c - c1)]
  have h_sos : 0 ≤ 4 * a_quad * ((19 / 10 : ℝ) ^ 2 * u ^ 4 - c0) - c1 ^ 2 := by
    have h_nn := poly_sos_nonneg (u - 1) (by linarith) (by linarith)
    dsimp only at h_nn
    rw [sub_add_cancel] at h_nn
    exact h_nn
  have h_a : 4 * a_quad * ((A + B * c - D * c ^ 2) ^ 2 + s ^ 2 * (E - D * c) ^ 2) ≤
      4 * a_quad * (c0 + c1 * c - a_quad * c ^ 2) :=
    mul_le_mul_of_nonneg_left h_quad (by linarith)
  have h_b : 4 * a_quad * c0 + c1 ^ 2 ≤ 4 * a_quad * ((19 / 10 : ℝ) ^ 2 * u ^ 4) := by
    have h_eq : 4 * a_quad * ((19 / 10 : ℝ) ^ 2 * u ^ 4) - (4 * a_quad * c0 + c1 ^ 2) =
        4 * a_quad * ((19 / 10 : ℝ) ^ 2 * u ^ 4 - c0) - c1 ^ 2 := by
      dsimp [a_quad, c0, c1, A, B, E, D]; ring
    exact sub_nonneg.mp (by rw [h_eq]; exact h_sos)
  have h_mul : 4 * a_quad * ((A + B * c - D * c ^ 2) ^ 2 + s ^ 2 * (E - D * c) ^ 2) ≤
      4 * a_quad * ((19 / 10 : ℝ) ^ 2 * u ^ 4) :=
    h_a.trans (le_trans h_comp_sq h_b)
  have h_res := le_of_mul_le_mul_left h_mul (by linarith)
  calc (A + B * c - D * c ^ 2) ^ 2 + s ^ 2 * (E - D * c) ^ 2
      ≤ (19 / 10 : ℝ) ^ 2 * u ^ 4 := h_res
    _ = ((19 / 10 : ℝ) * u ^ 2) ^ 2 := by ring

private lemma norm_P_le (w : ℂ) (hw1 : 1 ≤ ‖w‖) (hw2 : ‖w‖ ≤ 2) :
    ‖(-1 / 4 : ℂ) * w⁻¹ + 1 + w + (-1 / 4 : ℂ) * w ^ 2‖ ≤ (19 / 10 : ℝ) * ‖w‖ := by
  set u : ℝ := ‖w‖
  have hu_pos : 0 < u := by linarith
  have hu_ne : u ≠ 0 := hu_pos.ne'
  set c : ℝ := w.re / u
  set s : ℝ := w.im / u
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    have hns : w.re ^ 2 + w.im ^ 2 = u ^ 2 := by
      simpa [u, Complex.normSq_apply, ← sq] using Complex.normSq_eq_norm_sq w
    dsimp [c, s]
    field_simp
    linarith
  have hre : w.re = u * c := by dsimp [c]; field_simp
  have him : w.im = u * s := by dsimp [s]; field_simp
  have hns_u : Complex.normSq w = u ^ 2 := Complex.normSq_eq_norm_sq w
  set P : ℂ := (-1 / 4 : ℂ) * w⁻¹ + 1 + w + (-1 / 4 : ℂ) * w ^ 2
  have hPre : u * P.re =
      (u + (1 / 4 : ℝ) * u ^ 3) + (u ^ 2 - 1 / 4) * c - (1 / 2 : ℝ) * u ^ 3 * c ^ 2 := by
    have hinv : (w⁻¹).re = c / u := by
      rw [Complex.inv_re, hns_u, hre]
      field_simp
    have hsq : (w ^ 2).re = u ^ 2 * (2 * c ^ 2 - 1) := by
      rw [sq, Complex.mul_re, hre, him]
      have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith
      nlinarith
    have hP_re : P.re = (-1 / 4 : ℝ) * (w⁻¹).re + 1 + w.re + (-1 / 4 : ℝ) * (w ^ 2).re := by
      dsimp [P]
      simp [Complex.mul_re]
    rw [hP_re, hinv, hre, hsq]
    field_simp
    ring
  have hPim : u * P.im = s * ((1 / 4 + u ^ 2) - (1 / 2 : ℝ) * u ^ 3 * c) := by
    have hinv : (w⁻¹).im = -s / u := by
      rw [Complex.inv_im, hns_u, him]
      field_simp
    have hsq : (w ^ 2).im = 2 * u ^ 2 * c * s := by
      rw [sq, Complex.mul_im, hre, him]
      ring
    have hP_im : P.im = (-1 / 4 : ℝ) * (w⁻¹).im + w.im + (-1 / 4 : ℝ) * (w ^ 2).im := by
      dsimp [P]
      simp [Complex.mul_im]
    rw [hP_im, hinv, him, hsq]
    field_simp
    ring
  have h_aux := norm_P_le_aux u c s hw1 hw2 hcs
  have h_u2 : u ^ 2 * Complex.normSq P ≤ ((19 / 10 : ℝ) * u ^ 2) ^ 2 := by
    calc u ^ 2 * Complex.normSq P
        = (u * P.re) ^ 2 + (u * P.im) ^ 2 := by rw [Complex.normSq_apply]; ring
      _ = ((u + (1 / 4 : ℝ) * u ^ 3) + (u ^ 2 - 1 / 4) * c - (1 / 2 : ℝ) * u ^ 3 * c ^ 2) ^ 2 +
            s ^ 2 * ((1 / 4 + u ^ 2) - (1 / 2 : ℝ) * u ^ 3 * c) ^ 2 := by
          rw [hPre, hPim]; ring
      _ ≤ ((19 / 10 : ℝ) * u ^ 2) ^ 2 := h_aux
  have h_ns_le : Complex.normSq P ≤ ((19 / 10 : ℝ) * u) ^ 2 := by
    have h_u2_eq : u ^ 2 * ((19 / 10 : ℝ) * u) ^ 2 = ((19 / 10 : ℝ) * u ^ 2) ^ 2 := by ring
    exact le_of_mul_le_mul_left (h_u2_eq ▸ h_u2) (sq_pos_of_pos hu_pos)
  rw [← Real.sqrt_sq (by positivity : 0 ≤ (19 / 10 : ℝ) * u), Complex.norm_def]
  exact Real.sqrt_le_sqrt h_ns_le

private lemma tri_succ (m : ℕ) : (m + 1) * m / 2 = m * (m - 1) / 2 + m := by
  rcases m with _ | m
  · simp
  · rw [show (m + 1 + 1) * (m + 1) = (m + 1) * m + 2 * (m + 1) by ring,
      Nat.add_mul_div_left _ _ (by norm_num)]
    simp

private lemma tri_add (k j : ℕ) :
    (k + j) * (k + j - 1) / 2 = k * (k - 1) / 2 + j * (j - 1) / 2 + k * j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show k + (j + 1) = (k + j) + 1 by ring, show k + j + 1 - 1 = k + j by omega,
      show j + 1 - 1 = j by omega, tri_succ (k + j), ih, tri_succ j]
    ring

private lemma a_mul_pow_add (k j : ℕ) (z : ℂ) :
    a_seq (k + j) * z ^ (k + j) = (a_seq k * z ^ k) * a_seq j * ((-1 / 4 : ℂ) ^ k * z) ^ j := by
  dsimp [a_seq]
  rw [tri_add, pow_add, pow_add, pow_add, mul_pow, ← pow_mul]
  ring

private lemma a_mul_pow_sub {k m : ℕ} (hm : m ≤ k) {z : ℂ} (hz : z ≠ 0) :
    a_seq (k - m) * z ^ (k - m) =
      (a_seq k * z ^ k) * (-1 / 4 : ℂ) ^ (m * (m + 1) / 2) *
        (((-1 / 4 : ℂ) ^ k * z)⁻¹) ^ m := by
  have h2m : m * (m - 1) / 2 + m * (m + 1) / 2 = m * m := by
    have htri := tri_succ m
    rw [mul_comm m (m + 1)] at *
    have h_even : 2 * (m * (m - 1) / 2) = m * (m - 1) :=
      Nat.mul_div_cancel' (Nat.even_mul_pred_self m).two_dvd
    have h_even2 : 2 * ((m + 1) * m / 2) = (m + 1) * m :=
      Nat.mul_div_cancel' (by
        simpa [Nat.add_sub_cancel] using (Nat.even_mul_pred_self (m + 1)).two_dvd)
    have h_tot : 2 * (m * (m - 1) / 2 + (m + 1) * m / 2) = 2 * (m * m) := by
      rw [mul_add, h_even, h_even2]
      rcases m with _ | m <;> simp; ring
    omega
  have h_exp : k * (k - 1) / 2 + m * (m + 1) / 2 = (k - m) * (k - m - 1) / 2 + k * m := by
    have htri := tri_add (k - m) m
    rw [Nat.sub_add_cancel hm] at htri
    rw [htri]
    have hkm : (k - m) * m + m * m = k * m := by
      rw [← add_mul, Nat.sub_add_cancel hm]
    linarith [h2m]
  have hw_ne : ((-1 / 4 : ℂ) ^ k * z) ^ m ≠ 0 :=
    pow_ne_zero m (mul_ne_zero (pow_ne_zero k (by norm_num)) hz)
  rw [inv_pow, eq_mul_inv_iff_mul_eq₀ hw_ne]
  calc a_seq (k - m) * z ^ (k - m) * ((-1 / 4 : ℂ) ^ k * z) ^ m
    _ = (-1 / 4 : ℂ) ^ ((k - m) * (k - m - 1) / 2 + k * m) * z ^ ((k - m) + m) := by
        dsimp [a_seq]
        rw [mul_pow, ← pow_mul, pow_add, pow_add]
        ring
    _ = (-1 / 4 : ℂ) ^ (k * (k - 1) / 2 + m * (m + 1) / 2) * z ^ k := by
        rw [← h_exp, Nat.sub_add_cancel hm]
    _ = (a_seq k * z ^ k) * (-1 / 4 : ℂ) ^ (m * (m + 1) / 2) := by
        dsimp [a_seq]
        rw [pow_add]
        ring

private lemma f_split {k : ℕ} (hk : 3 ≤ k) {z : ℂ} (hz : z ≠ 0) :
    f_entire z = (∑ n ∈ Finset.range (k - 1), a_seq n * z ^ n) +
      (a_seq k * z ^ k) * ((-1 / 4 : ℂ) * ((-1 / 4 : ℂ) ^ k * z)⁻¹ + 1 +
        ((-1 / 4 : ℂ) ^ k * z) + (-1 / 4 : ℂ) * ((-1 / 4 : ℂ) ^ k * z) ^ 2) +
      ∑' i : ℕ, a_seq (k + 3 + i) * z ^ (k + 3 + i) := by
  have hs : Summable (fun n : ℕ => a_seq n * z ^ n) := (summable_norm_a_mul_pow z).of_norm
  rw [f_entire, ← hs.sum_add_tsum_nat_add (k + 3)]
  have hk1 : k + 3 = (k - 1) + 4 := by omega
  conv_lhs =>
    lhs
    rw [hk1, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
  have hm2 : k - 1 + 1 = k := by omega
  have hm3 : k - 1 + 2 = k + 1 := by omega
  have hm4 : k - 1 + 3 = k + 2 := by omega
  rw [hm2, hm3, hm4]
  have h_sub1 : a_seq (k - 1) * z ^ (k - 1) =
      (a_seq k * z ^ k) * (-1 / 4 : ℂ) * ((-1 / 4 : ℂ) ^ k * z)⁻¹ := by
    simpa using a_mul_pow_sub (by omega : 1 ≤ k) hz
  have h_add1 : a_seq (k + 1) * z ^ (k + 1) =
      (a_seq k * z ^ k) * ((-1 / 4 : ℂ) ^ k * z) := by
    simpa [a_seq] using a_mul_pow_add k 1 z
  have h_add2 : a_seq (k + 2) * z ^ (k + 2) =
      (a_seq k * z ^ k) * (-1 / 4 : ℂ) * ((-1 / 4 : ℂ) ^ k * z) ^ 2 := by
    simpa [a_seq] using a_mul_pow_add k 2 z
  rw [h_sub1, h_add1, h_add2]
  simp_rw [add_comm _ (k + 3)]
  ring

private lemma ratio_f_ge {r : ℝ} (hr : 64 ≤ r) :
    (100 / 199 : ℝ) ≤ Erdos513.ratio r f_entire := by
  have hr_pos : 0 < r := by linarith
  set N : ℕ := Nat.floor r
  have hN64 : 64 ≤ N := Nat.le_floor (by exact_mod_cast hr)
  set k : ℕ := Nat.log 4 N
  have hk3 : 3 ≤ k := Nat.le_log_of_pow_le (by norm_num) (by norm_num; exact hN64)
  have h4k_le : (4 : ℝ) ^ k ≤ r := by
    have h1 : 4 ^ k ≤ N := Nat.pow_log_le_self 4 (by omega)
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le hr_pos.le)
  have hr_lt_4k1 : r < (4 : ℝ) ^ (k + 1) := by
    have h1 : N < 4 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
    have h2 : (N : ℝ) + 1 ≤ (4 : ℝ) ^ (k + 1) := by exact_mod_cast h1
    linarith [Nat.lt_floor_add_one r]
  have h_bound_sphere : ∀ z : {z : ℂ // ‖z‖ = r},
      ‖f_entire z‖ ≤ (199 / 100 : ℝ) * (‖a_seq (k + 1)‖ * r ^ (k + 1)) := by
    rintro ⟨z, hz⟩
    have hz_ne : z ≠ 0 := by intro h0; rw [h0, norm_zero] at hz; linarith
    by_cases h_case : r ≤ 2 * (4 : ℝ) ^ k
    · set w : ℂ := (-1 / 4 : ℂ) ^ k * z
      have hw_norm : ‖w‖ = r / (4 : ℝ) ^ k := by
        rw [norm_mul, norm_pow, show ‖(-1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num, hz, one_div, inv_pow]
        ring
      have hw1 : 1 ≤ ‖w‖ := by
        rw [hw_norm, le_div_iff₀ (by positivity)]
        linarith
      have hw2 : ‖w‖ ≤ 2 := by
        rw [hw_norm, div_le_iff₀ (by positivity)]
        linarith
      have h_target_eq : ‖a_seq k * z ^ k‖ * ‖w‖ = ‖a_seq (k + 1)‖ * r ^ (k + 1) := by
        have h_add := a_mul_pow_add k 1 z
        simpa [w, a_seq, norm_mul, norm_pow, hz] using congrArg norm h_add.symm
      rw [f_split hk3 hz_ne]
      have h_main : ‖(a_seq k * z ^ k) * ((-1 / 4 : ℂ) * w⁻¹ + 1 + w + (-1 / 4 : ℂ) * w ^ 2)‖ ≤
          (19 / 10 : ℝ) * (‖a_seq k * z ^ k‖ * ‖w‖) := by
        rw [norm_mul]
        have hP := norm_P_le w hw1 hw2
        nlinarith [norm_nonneg (a_seq k * z ^ k)]
      have h_neg : ‖∑ n ∈ Finset.range (k - 1), a_seq n * z ^ n‖ ≤
          (1 / 63 : ℝ) * (‖a_seq k * z ^ k‖ * ‖w‖) := by
        calc ‖∑ n ∈ Finset.range (k - 1), a_seq n * z ^ n‖
            ≤ ∑ n ∈ Finset.range (k - 1), ‖a_seq n * z ^ n‖ := norm_sum_le _ _
          _ ≤ ∑ n ∈ Finset.range (k - 1),
                (‖a_seq k * z ^ k‖ * ‖w‖) * (1 / 64 : ℝ) ^ (k - n - 1) := by
              refine Finset.sum_le_sum fun n hn => ?_
              have hn_lt : n < k - 1 := Finset.mem_range.mp hn
              set m : ℕ := k - n
              have hm2 : 2 ≤ m := by omega
              have hm_le : m ≤ k := by omega
              have h_sub := a_mul_pow_sub hm_le hz_ne
              have hn_eq : k - m = n := by omega
              rw [hn_eq] at h_sub
              rw [h_sub, norm_mul, norm_mul, norm_pow, norm_pow, norm_inv,
                show ‖(-1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num]
              have hm_exp : 3 * (m - 1) ≤ m * (m + 1) / 2 := by
                rw [Nat.le_div_iff_mul_le (by norm_num)]
                rcases m with _ | _ | _ | m
                · omega
                · omega
                · norm_num
                · rw [show m + 1 + 1 + 1 - 1 = m + 2 by omega]
                  nlinarith [Nat.zero_le m]
              have hw_inv : ‖w‖⁻¹ ^ m ≤ ‖w‖ := by
                have h1 : ‖w‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hw1
                exact le_trans (pow_le_one₀ (by positivity) h1) hw1
              calc ‖a_seq k * z ^ k‖ * (1 / 4 : ℝ) ^ (m * (m + 1) / 2) * ‖w‖⁻¹ ^ m
                  ≤ ‖a_seq k * z ^ k‖ * (1 / 4 : ℝ) ^ (3 * (m - 1)) * ‖w‖ := by
                    exact mul_le_mul
                      (mul_le_mul_of_nonneg_left
                        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm_exp)
                        (norm_nonneg _))
                      hw_inv (by positivity) (by positivity)
                _ = (‖a_seq k * z ^ k‖ * ‖w‖) * (1 / 64 : ℝ) ^ (k - n - 1) := by
                    rw [pow_mul (1 / 4 : ℝ) 3 (m - 1)]
                    norm_num
                    ring
          _ ≤ (‖a_seq k * z ^ k‖ * ‖w‖) * (1 / 63 : ℝ) := by
              rw [← Finset.mul_sum]
              gcongr
              have h_sum_eq : ∑ n ∈ Finset.range (k - 1), (1 / 64 : ℝ) ^ (k - n - 1) =
                  ∑ j ∈ Finset.range (k - 1), (1 / 64 : ℝ) ^ (j + 1) := by
                refine Finset.sum_bij (fun n _ => k - n - 2) ?_ ?_ ?_ ?_
                · intro n hn; simp only [Finset.mem_range] at *; omega
                · intro a ha b hb hab; simp only [Finset.mem_range] at *; omega
                · intro j hj; simp only [Finset.mem_range] at *
                  refine ⟨k - j - 2, by omega, by omega⟩
                · intro n hn; simp only [Finset.mem_range] at *
                  congr 1; omega
              rw [h_sum_eq]
              have hs64 : Summable (fun j : ℕ => (1 / 64 : ℝ) ^ (j + 1)) :=
                (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
                  Nat.succ_injective
              have h_tsum : ∑' j : ℕ, (1 / 64 : ℝ) ^ (j + 1) = 1 / 63 := by
                have h_g : ∑' j : ℕ, (1 / 64 : ℝ) ^ j = 64 / 63 := by
                  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
                  norm_num
                simp_rw [pow_succ']
                rw [tsum_mul_left, h_g]
                norm_num
              exact le_trans (hs64.sum_le_tsum (Finset.range (k - 1)) (fun _ _ => by positivity))
                h_tsum.le
          _ = (1 / 63 : ℝ) * (‖a_seq k * z ^ k‖ * ‖w‖) := by ring
      have h_pos_tail : ‖∑' i : ℕ, a_seq (k + 3 + i) * z ^ (k + 3 + i)‖ ≤
          (1 / 14 : ℝ) * (‖a_seq k * z ^ k‖ * ‖w‖) := by
        have hs_tail : Summable (fun i : ℕ => ‖a_seq (k + 3 + i) * z ^ (k + 3 + i)‖) :=
          (summable_norm_a_mul_pow z).comp_injective (fun a b h => Nat.add_left_cancel h :
            Function.Injective fun i => k + 3 + i)
        have hs_geom8 : Summable (fun i : ℕ => (‖a_seq k * z ^ k‖ * ‖w‖) * ((1 / 16 : ℝ) * (1 / 8 : ℝ) ^ i)) :=
          ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _).mul_left _
        calc ‖∑' i : ℕ, a_seq (k + 3 + i) * z ^ (k + 3 + i)‖
            ≤ ∑' i : ℕ, ‖a_seq (k + 3 + i) * z ^ (k + 3 + i)‖ := norm_tsum_le_tsum_norm hs_tail
          _ ≤ ∑' i : ℕ, (‖a_seq k * z ^ k‖ * ‖w‖) * ((1 / 16 : ℝ) * (1 / 8 : ℝ) ^ i) := by
              refine hs_tail.tsum_le_tsum (fun i => ?_) hs_geom8
              rw [show k + 3 + i = k + (3 + i) by ring, a_mul_pow_add, mul_assoc, norm_mul]
              have hi_exp : 3 + 2 * i ≤ (3 + i) * (3 + i - 1) / 2 := by
                rw [Nat.le_div_iff_mul_le (by norm_num), show 3 + i - 1 = i + 2 by omega]
                nlinarith [Nat.zero_le i]
              calc ‖a_seq k * z ^ k‖ * ‖a_seq (3 + i) * ((-1 / 4 : ℂ) ^ k * z) ^ (3 + i)‖
                  = ‖a_seq k * z ^ k‖ * ((1 / 4 : ℝ) ^ ((3 + i) * (3 + i - 1) / 2) * ‖w‖ ^ (3 + i)) := by
                    conv_lhs => rhs; rw [norm_mul, norm_a_seq, norm_pow]
                _ ≤ ‖a_seq k * z ^ k‖ * ((1 / 4 : ℝ) ^ (3 + 2 * i) * (‖w‖ * 2 ^ (2 + i))) := by
                    refine mul_le_mul_of_nonneg_left (mul_le_mul
                      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hi_exp) ?_
                      (by positivity) (by positivity)) (norm_nonneg _)
                    rw [show 3 + i = 1 + (2 + i) by ring, pow_add, pow_one]
                    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw2 _) (norm_nonneg _)
                _ = (‖a_seq k * z ^ k‖ * ‖w‖) * ((1 / 16 : ℝ) * (1 / 8 : ℝ) ^ i) := by
                    rw [pow_add, pow_mul (1 / 4 : ℝ) 2 i, pow_add (2 : ℝ) 2 i]
                    have h16 : ((1 / 4 : ℝ) ^ 2) ^ i * 2 ^ i = (1 / 8 : ℝ) ^ i := by
                      rw [← mul_pow]; norm_num
                    calc ‖a_seq k * z ^ k‖ * ((1 / 4 : ℝ) ^ 3 * ((1 / 4 : ℝ) ^ 2) ^ i * (‖w‖ * (2 ^ 2 * 2 ^ i)))
                        = (‖a_seq k * z ^ k‖ * ‖w‖) * (((1 / 4 : ℝ) ^ 3 * 2 ^ 2) * (((1 / 4 : ℝ) ^ 2) ^ i * 2 ^ i)) := by ring
                      _ = (‖a_seq k * z ^ k‖ * ‖w‖) * ((1 / 16 : ℝ) * (1 / 8 : ℝ) ^ i) := by
                          rw [h16]; norm_num
          _ = (1 / 14 : ℝ) * (‖a_seq k * z ^ k‖ * ‖w‖) := by
              rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
              norm_num
              ring
      calc ‖(∑ n ∈ Finset.range (k - 1), a_seq n * z ^ n) +
              (a_seq k * z ^ k) * ((-1 / 4 : ℂ) * w⁻¹ + 1 + w + (-1 / 4 : ℂ) * w ^ 2) +
              ∑' i : ℕ, a_seq (k + 3 + i) * z ^ (k + 3 + i)‖
          ≤ ‖∑ n ∈ Finset.range (k - 1), a_seq n * z ^ n‖ +
              ‖(a_seq k * z ^ k) * ((-1 / 4 : ℂ) * w⁻¹ + 1 + w + (-1 / 4 : ℂ) * w ^ 2)‖ +
              ‖∑' i : ℕ, a_seq (k + 3 + i) * z ^ (k + 3 + i)‖ := by
            exact le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ (1 / 63 : ℝ) * (‖a_seq k * z ^ k‖ * ‖w‖) + (19 / 10 : ℝ) * (‖a_seq k * z ^ k‖ * ‖w‖) +
              (1 / 14 : ℝ) * (‖a_seq k * z ^ k‖ * ‖w‖) := by linarith
        _ ≤ (199 / 100 : ℝ) * (‖a_seq k * z ^ k‖ * ‖w‖) := by
            have hnn : 0 ≤ ‖a_seq k * z ^ k‖ * ‖w‖ := by positivity
            nlinarith
        _ = (199 / 100 : ℝ) * (‖a_seq (k + 1)‖ * r ^ (k + 1)) := by rw [h_target_eq]
    · push Not at h_case
      set k' : ℕ := k + 1
      have hk'3 : 3 ≤ k' := by omega
      set w : ℂ := (-1 / 4 : ℂ) ^ k' * z
      have hw_norm : ‖w‖ = r / (4 : ℝ) ^ k' := by
        rw [norm_mul, norm_pow, show ‖(-1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num, hz, one_div, inv_pow]
        ring
      have hw_half : 1 / 2 < ‖w‖ := by
        rw [hw_norm, lt_div_iff₀ (by positivity)]
        dsimp [k']
        rw [pow_succ']
        linarith
      have hw_lt1 : ‖w‖ < 1 := by
        rw [hw_norm, div_lt_one (by positivity)]
        exact hr_lt_4k1
      have hw_ne : w ≠ 0 := by intro h0; rw [h0, norm_zero] at hw_half; linarith
      set v : ℂ := w⁻¹
      have hv1 : 1 ≤ ‖v‖ := by
        rw [norm_inv]
        exact (one_le_inv₀ (by linarith)).mpr hw_lt1.le
      have hv2 : ‖v‖ ≤ 2 := by
        rw [norm_inv]
        exact (inv_le_iff_one_le_mul₀ (by linarith)).mpr (by linarith)
      have h_target_eq : ‖a_seq k' * z ^ k'‖ = ‖a_seq (k + 1)‖ * r ^ (k + 1) := by
        rw [norm_mul, norm_pow, hz]
      rw [f_split hk'3 hz_ne]
      have h_main : ‖(a_seq k' * z ^ k') * ((-1 / 4 : ℂ) * w⁻¹ + 1 + w + (-1 / 4 : ℂ) * w ^ 2)‖ ≤
          (19 / 10 : ℝ) * ‖a_seq k' * z ^ k'‖ := by
        have h_eqP : (-1 / 4 : ℂ) * w⁻¹ + 1 + w + (-1 / 4 : ℂ) * w ^ 2 =
            w * ((-1 / 4 : ℂ) * v⁻¹ + 1 + v + (-1 / 4 : ℂ) * v ^ 2) := by
          dsimp [v]
          field_simp
          ring
        rw [h_eqP]
        have hP := norm_P_le v hv1 hv2
        calc ‖(a_seq k' * z ^ k') * (w * ((-1 / 4 : ℂ) * v⁻¹ + 1 + v + (-1 / 4 : ℂ) * v ^ 2))‖
            = ‖a_seq k' * z ^ k'‖ * (‖w‖ * ‖(-1 / 4 : ℂ) * v⁻¹ + 1 + v + (-1 / 4 : ℂ) * v ^ 2‖) := by
              rw [norm_mul]; conv_lhs => rhs; rw [norm_mul]
          _ ≤ ‖a_seq k' * z ^ k'‖ * (‖w‖ * ((19 / 10 : ℝ) * ‖v‖)) := by
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP (norm_nonneg _)) (norm_nonneg _)
          _ = (19 / 10 : ℝ) * ‖a_seq k' * z ^ k'‖ := by
              dsimp [v]
              rw [norm_inv]
              have hw0 : ‖w‖ ≠ 0 := (by linarith : 0 < ‖w‖).ne'
              have : ‖w‖ * ((19 / 10 : ℝ) * ‖w‖⁻¹) = 19 / 10 := by field_simp
              rw [this]; ring
      have h_neg : ‖∑ n ∈ Finset.range (k' - 1), a_seq n * z ^ n‖ ≤
          (1 / 14 : ℝ) * ‖a_seq k' * z ^ k'‖ := by
        calc ‖∑ n ∈ Finset.range (k' - 1), a_seq n * z ^ n‖
            ≤ ∑ n ∈ Finset.range (k' - 1), ‖a_seq n * z ^ n‖ := norm_sum_le _ _
          _ ≤ ∑ n ∈ Finset.range (k' - 1),
                ‖a_seq k' * z ^ k'‖ * ((1 / 16 : ℝ) * (1 / 8 : ℝ) ^ (k' - n - 2)) := by
              refine Finset.sum_le_sum fun n hn => ?_
              have hn_lt : n < k' - 1 := Finset.mem_range.mp hn
              set m : ℕ := k' - n
              have hm2 : 2 ≤ m := by omega
              have hm_le : m ≤ k' := by omega
              have h_sub := a_mul_pow_sub hm_le hz_ne
              have hn_eq : k' - m = n := by omega
              rw [hn_eq] at h_sub
              rw [h_sub, norm_mul, norm_mul, norm_pow, norm_pow, norm_inv,
                show ‖(-1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num]
              have hm_exp : 3 + 2 * (m - 2) ≤ m * (m + 1) / 2 := by
                rw [Nat.le_div_iff_mul_le (by norm_num)]
                rcases m with _ | _ | _ | m
                · omega
                · omega
                · norm_num
                · rw [show m + 1 + 1 + 1 - 2 = m + 1 by omega]
                  nlinarith [Nat.zero_le m]
              have hw_inv : ‖w‖⁻¹ ^ m ≤ 2 ^ m := by
                have h1 : ‖w‖⁻¹ ≤ 2 := by rw [← norm_inv]; exact hv2
                exact pow_le_pow_left₀ (by positivity) h1 m
              calc ‖a_seq k' * z ^ k'‖ * (1 / 4 : ℝ) ^ (m * (m + 1) / 2) * ‖w‖⁻¹ ^ m
                  ≤ ‖a_seq k' * z ^ k'‖ * (1 / 4 : ℝ) ^ (3 + 2 * (m - 2)) * 2 ^ m := by
                    exact mul_le_mul
                      (mul_le_mul_of_nonneg_left
                        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm_exp)
                        (norm_nonneg _))
                      hw_inv (by positivity) (by positivity)
                _ = ‖a_seq k' * z ^ k'‖ * ((1 / 16 : ℝ) * (1 / 8 : ℝ) ^ (k' - n - 2)) := by
                    have hm_eq : m = 2 + (m - 2) := by omega
                    conv_lhs => rw [hm_eq, pow_add (2 : ℝ) 2 (m - 2)]
                    rw [show 2 + (m - 2) - 2 = m - 2 by omega,
                      pow_add (1 / 4 : ℝ) 3 (2 * (m - 2)), pow_mul (1 / 4 : ℝ) 2 (m - 2)]
                    have h_sub_eq : m - 2 = k' - n - 2 := by omega
                    rw [h_sub_eq]
                    have h16 : ((1 / 4 : ℝ) ^ 2) ^ (k' - n - 2) * 2 ^ (k' - n - 2) =
                        (1 / 8 : ℝ) ^ (k' - n - 2) := by
                      rw [← mul_pow]; norm_num
                    calc ‖a_seq k' * z ^ k'‖ * ((1 / 4 : ℝ) ^ 3 * ((1 / 4 : ℝ) ^ 2) ^ (k' - n - 2)) *
                            (2 ^ 2 * 2 ^ (k' - n - 2))
                        = ‖a_seq k' * z ^ k'‖ * (((1 / 4 : ℝ) ^ 3 * 2 ^ 2) *
                            (((1 / 4 : ℝ) ^ 2) ^ (k' - n - 2) * 2 ^ (k' - n - 2))) := by ring
                      _ = ‖a_seq k' * z ^ k'‖ * ((1 / 16 : ℝ) * (1 / 8 : ℝ) ^ (k' - n - 2)) := by
                          rw [h16]; norm_num
          _ ≤ ‖a_seq k' * z ^ k'‖ * (1 / 14 : ℝ) := by
              rw [← Finset.mul_sum]
              gcongr
              have h_sum_eq : ∑ n ∈ Finset.range (k' - 1), (1 / 16 : ℝ) * (1 / 8 : ℝ) ^ (k' - n - 2) =
                  ∑ j ∈ Finset.range (k' - 1), (1 / 16 : ℝ) * (1 / 8 : ℝ) ^ j := by
                refine Finset.sum_bij (fun n _ => k' - n - 2) ?_ ?_ ?_ ?_
                · intro n hn; simp only [Finset.mem_range] at *; omega
                · intro a ha b hb hab; simp only [Finset.mem_range] at *; omega
                · intro j hj; simp only [Finset.mem_range] at *
                  refine ⟨k' - j - 2, by omega, by omega⟩
                · intro n hn; rfl
              rw [h_sum_eq]
              have hs8 : Summable (fun j : ℕ => (1 / 16 : ℝ) * (1 / 8 : ℝ) ^ j) :=
                (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
              have h_tsum : ∑' j : ℕ, (1 / 16 : ℝ) * (1 / 8 : ℝ) ^ j = 1 / 14 := by
                rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
                norm_num
              exact le_trans (hs8.sum_le_tsum (Finset.range (k' - 1)) (fun _ _ => by positivity))
                h_tsum.le
          _ = (1 / 14 : ℝ) * ‖a_seq k' * z ^ k'‖ := by ring
      have h_pos_tail : ‖∑' i : ℕ, a_seq (k' + 3 + i) * z ^ (k' + 3 + i)‖ ≤
          (1 / 63 : ℝ) * ‖a_seq k' * z ^ k'‖ := by
        have hs_tail : Summable (fun i : ℕ => ‖a_seq (k' + 3 + i) * z ^ (k' + 3 + i)‖) :=
          (summable_norm_a_mul_pow z).comp_injective (fun a b h => Nat.add_left_cancel h :
            Function.Injective fun i => k' + 3 + i)
        have hs_geom64 : Summable (fun i : ℕ => ‖a_seq k' * z ^ k'‖ * (1 / 64 : ℝ) ^ (i + 1)) :=
          ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
            Nat.succ_injective).mul_left _
        calc ‖∑' i : ℕ, a_seq (k' + 3 + i) * z ^ (k' + 3 + i)‖
            ≤ ∑' i : ℕ, ‖a_seq (k' + 3 + i) * z ^ (k' + 3 + i)‖ := norm_tsum_le_tsum_norm hs_tail
          _ ≤ ∑' i : ℕ, ‖a_seq k' * z ^ k'‖ * (1 / 64 : ℝ) ^ (i + 1) := by
              refine hs_tail.tsum_le_tsum (fun i => ?_) hs_geom64
              rw [show k' + 3 + i = k' + (3 + i) by ring, a_mul_pow_add, mul_assoc, norm_mul]
              have hi_exp : 3 * (i + 1) ≤ (3 + i) * (3 + i - 1) / 2 := by
                rw [Nat.le_div_iff_mul_le (by norm_num), show 3 + i - 1 = i + 2 by omega]
                rcases i with _ | i
                · norm_num
                · nlinarith [Nat.zero_le i]
              calc ‖a_seq k' * z ^ k'‖ * ‖a_seq (3 + i) * ((-1 / 4 : ℂ) ^ k' * z) ^ (3 + i)‖
                  = ‖a_seq k' * z ^ k'‖ * ((1 / 4 : ℝ) ^ ((3 + i) * (3 + i - 1) / 2) * ‖w‖ ^ (3 + i)) := by
                    conv_lhs => rhs; rw [norm_mul, norm_a_seq, norm_pow]
                _ ≤ ‖a_seq k' * z ^ k'‖ * ((1 / 4 : ℝ) ^ (3 * (i + 1)) * 1 ^ (3 + i)) := by
                    exact mul_le_mul_of_nonneg_left (mul_le_mul
                      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hi_exp)
                      (pow_le_pow_left₀ (norm_nonneg _) hw_lt1.le _)
                      (by positivity) (by positivity)) (norm_nonneg _)
                _ = ‖a_seq k' * z ^ k'‖ * (1 / 64 : ℝ) ^ (i + 1) := by
                    rw [one_pow, mul_one, pow_mul (1 / 4 : ℝ) 3 (i + 1)]
                    norm_num
          _ = (1 / 63 : ℝ) * ‖a_seq k' * z ^ k'‖ := by
              rw [tsum_mul_left]
              have h_tsum : ∑' i : ℕ, (1 / 64 : ℝ) ^ (i + 1) = 1 / 63 := by
                simp_rw [pow_succ']
                rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
                norm_num
              rw [h_tsum]
              ring
      calc ‖(∑ n ∈ Finset.range (k' - 1), a_seq n * z ^ n) +
              (a_seq k' * z ^ k') * ((-1 / 4 : ℂ) * w⁻¹ + 1 + w + (-1 / 4 : ℂ) * w ^ 2) +
              ∑' i : ℕ, a_seq (k' + 3 + i) * z ^ (k' + 3 + i)‖
          ≤ ‖∑ n ∈ Finset.range (k' - 1), a_seq n * z ^ n‖ +
              ‖(a_seq k' * z ^ k') * ((-1 / 4 : ℂ) * w⁻¹ + 1 + w + (-1 / 4 : ℂ) * w ^ 2)‖ +
              ‖∑' i : ℕ, a_seq (k' + 3 + i) * z ^ (k' + 3 + i)‖ := by
            exact le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ (1 / 14 : ℝ) * ‖a_seq k' * z ^ k'‖ + (19 / 10 : ℝ) * ‖a_seq k' * z ^ k'‖ +
              (1 / 63 : ℝ) * ‖a_seq k' * z ^ k'‖ := by linarith
        _ ≤ (199 / 100 : ℝ) * ‖a_seq k' * z ^ k'‖ := by
            have hnn : 0 ≤ ‖a_seq k' * z ^ k'‖ := norm_nonneg _
            nlinarith
        _ = (199 / 100 : ℝ) * (‖a_seq (k + 1)‖ * r ^ (k + 1)) := by rw [h_target_eq]
  set μ : ℝ := ⨆ n : ℕ, ‖iteratedDeriv n f_entire 0 * (n ! : ℝ)⁻¹ * r ^ n‖
  set M : ℝ := ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f_entire z‖
  have hμ_bdd : BddAbove (Set.range fun n : ℕ => ‖iteratedDeriv n f_entire 0 * (n ! : ℝ)⁻¹ * r ^ n‖) := by
    refine ⟨∑' n : ℕ, ‖a_seq n * (r : ℂ) ^ n‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    dsimp only
    rw [f_term_norm n hr_pos.le]
    have h_eq : (1 / 4 : ℝ) ^ (n * (n - 1) / 2) * r ^ n = ‖a_seq n * (r : ℂ) ^ n‖ := by
      rw [norm_mul, norm_a_seq, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr_pos.le]
    rw [h_eq]
    exact (summable_norm_a_mul_pow (r : ℂ)).le_tsum n (fun _ _ => norm_nonneg _)
  have hμ_ge : ‖a_seq (k + 1)‖ * r ^ (k + 1) ≤ μ := by
    have h_eq := f_term_norm (k + 1) hr_pos.le
    rw [← norm_a_seq] at h_eq
    rw [← h_eq]
    exact le_ciSup hμ_bdd (k + 1)
  have hμ_pos : 0 < μ := by
    have h1 : 0 < ‖a_seq (k + 1)‖ * r ^ (k + 1) := by
      rw [norm_a_seq]
      positivity
    linarith
  have hM_le : M ≤ (199 / 100 : ℝ) * μ := by
    have : Nonempty {z : ℂ // ‖z‖ = r} := ⟨⟨(r : ℂ), by simp [abs_of_pos hr_pos]⟩⟩
    refine ciSup_le fun z => le_trans (h_bound_sphere z) ?_
    gcongr
  have hM_pos : 0 < M := by
    have h_le : μ ≤ M := ciSup_le (term_le_sup_sphere hr_pos f_differentiable)
    linarith
  rw [Erdos513.ratio]
  exact (le_div_iff₀ hM_pos).mpr (by linarith)

private lemma poly_eval_upper_bound (p : ℂ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → ‖p.eval z‖ ≤ C * ‖z‖ ^ p.natDegree := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ + 1, by positivity, fun z hz => ?_⟩
  rw [Polynomial.eval_eq_sum_range]
  calc ‖∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * z ^ i‖
      ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * ‖z‖ ^ p.natDegree := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hz (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
          (norm_nonneg _)
    _ = (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) * ‖z‖ ^ p.natDegree := by
        rw [← Finset.sum_mul]
    _ ≤ (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ + 1) * ‖z‖ ^ p.natDegree := by
        gcongr
        linarith

private lemma poly_eval_lower_bound {p : ℂ[X]} (hp : p ≠ 0) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      (‖p.leadingCoeff‖ / 2) * ‖z‖ ^ p.natDegree ≤ ‖p.eval z‖ := by
  by_cases hd0 : p.natDegree = 0
  · refine ⟨1, le_rfl, fun z _ => ?_⟩
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd0]
    simp
  · have h_lc_pos : 0 < ‖p.leadingCoeff‖ := norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
    set Cq : ℝ := ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ + 1
    have hCq_pos : 0 < Cq := by positivity
    set R : ℝ := max 1 (2 * Cq / ‖p.leadingCoeff‖)
    refine ⟨R, le_max_left _ _, fun z hz => ?_⟩
    have hz1 : 1 ≤ ‖z‖ := le_trans (le_max_left _ _) hz
    have h_split : p.eval z =
        p.leadingCoeff * z ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, p.coeff i * z ^ i := by
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, Polynomial.leadingCoeff]
      ring
    have hq_le : ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * z ^ i‖ ≤
        (‖p.leadingCoeff‖ / 2) * ‖z‖ ^ p.natDegree := by
      have h1 : ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * z ^ i‖ ≤
          Cq * ‖z‖ ^ (p.natDegree - 1) := by
        calc ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ * ‖z‖ ^ (p.natDegree - 1) := by
              refine Finset.sum_le_sum fun i hi => ?_
              rw [norm_mul, norm_pow]
              exact mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ hz1 (Nat.le_pred_of_lt (Finset.mem_range.mp hi)))
                (norm_nonneg _)
          _ = (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) * ‖z‖ ^ (p.natDegree - 1) := by
              rw [← Finset.sum_mul]
          _ ≤ Cq * ‖z‖ ^ (p.natDegree - 1) := by
              dsimp [Cq]; gcongr; linarith
      have h2 : Cq ≤ (‖p.leadingCoeff‖ / 2) * ‖z‖ := by
        have hR2 : 2 * Cq / ‖p.leadingCoeff‖ ≤ ‖z‖ := le_trans (le_max_right _ _) hz
        rw [div_le_iff₀ h_lc_pos] at hR2
        linarith
      calc ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * z ^ i‖
          ≤ Cq * ‖z‖ ^ (p.natDegree - 1) := h1
        _ ≤ ((‖p.leadingCoeff‖ / 2) * ‖z‖) * ‖z‖ ^ (p.natDegree - 1) := by gcongr
        _ = (‖p.leadingCoeff‖ / 2) * ‖z‖ ^ p.natDegree := by
            conv_rhs => rw [show p.natDegree = 1 + (p.natDegree - 1) by omega, pow_add, pow_one]
            ring
    have h_rev := norm_sub_le_norm_add (p.leadingCoeff * z ^ p.natDegree)
      (∑ i ∈ Finset.range p.natDegree, p.coeff i * z ^ i)
    rw [← h_split, norm_mul, norm_pow] at h_rev
    linarith

private lemma f_transcendental : Transcendental ℂ[X] f_entire := by
  intro h_alg
  rcases h_alg with ⟨Q, hQ0, hQ⟩
  set d : ℕ := Q.natDegree
  have hqd_ne : Q.coeff d ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ0
  have h_eval_zero : ∀ z : ℂ,
      ∑ j ∈ Finset.range (d + 1), (Q.coeff j).eval z * (f_entire z) ^ j = 0 := by
    intro z
    have hz := congrArg (fun g : ℂ → ℂ => g z) hQ
    simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, Finset.sum_apply,
      Pi.mul_apply, Pi.pow_apply, Pi.zero_apply] at hz
    simpa [d, Polynomial.algebraMap_apply] using hz
  by_cases hd0 : d = 0
  · have h0 : ∀ z : ℂ, (Q.coeff 0).eval z = 0 := fun z => by
      simpa [hd0] using h_eval_zero z
    exact hqd_ne (by rw [hd0]; exact Polynomial.funext fun z => by simp [h0 z])
  · obtain ⟨R, hR1, h_lb⟩ := poly_eval_lower_bound hqd_ne
    have h_lc_pos : 0 < ‖(Q.coeff d).leadingCoeff‖ :=
      norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hqd_ne)
    set D : ℕ := Finset.sup (Finset.range d) (fun j => (Q.coeff j).natDegree)
    have h_ub_sum : ∃ C1 : ℝ, 0 < C1 ∧ ∀ z : ℂ, 1 ≤ ‖z‖ →
        ∑ j ∈ Finset.range d, ‖(Q.coeff j).eval z‖ ≤ C1 * ‖z‖ ^ D := by
      choose Cj hCj_pos hCj using fun j => poly_eval_upper_bound (Q.coeff j)
      have h_sum_nn : 0 ≤ ∑ j ∈ Finset.range d, Cj j :=
        Finset.sum_nonneg fun j _ => (hCj_pos j).le
      refine ⟨∑ j ∈ Finset.range d, Cj j + 1, by linarith, fun z hz => ?_⟩
      calc ∑ j ∈ Finset.range d, ‖(Q.coeff j).eval z‖
          ≤ ∑ j ∈ Finset.range d, Cj j * ‖z‖ ^ (Q.coeff j).natDegree :=
            Finset.sum_le_sum fun j _ => hCj j z hz
        _ ≤ ∑ j ∈ Finset.range d, Cj j * ‖z‖ ^ D := by
            refine Finset.sum_le_sum fun j hj => ?_
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hz (Finset.le_sup (f := fun j => (Q.coeff j).natDegree) hj))
              (hCj_pos j).le
        _ = (∑ j ∈ Finset.range d, Cj j) * ‖z‖ ^ D := by rw [← Finset.sum_mul]
        _ ≤ (∑ j ∈ Finset.range d, Cj j + 1) * ‖z‖ ^ D := by gcongr; linarith
    obtain ⟨C1, hC1_pos, h_ub⟩ := h_ub_sum
    set C2 : ℝ := max 1 (2 * C1 / ‖(Q.coeff d).leadingCoeff‖)
    have h_poly_bound : ∀ z : ℂ, R ≤ ‖z‖ → ‖f_entire z‖ ≤ C2 * ‖z‖ ^ D := by
      intro z hz
      have hz1 : 1 ≤ ‖z‖ := le_trans hR1 hz
      by_cases hf1 : ‖f_entire z‖ ≤ 1
      · calc ‖f_entire z‖ ≤ 1 := hf1
          _ ≤ C2 := le_max_left _ _
          _ ≤ C2 * ‖z‖ ^ D := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hz1)
      · push Not at hf1
        have h_eq := h_eval_zero z
        rw [Finset.sum_range_succ] at h_eq
        have h_lead : (Q.coeff d).eval z * (f_entire z) ^ d =
            -∑ j ∈ Finset.range d, (Q.coeff j).eval z * (f_entire z) ^ j :=
          eq_neg_of_add_eq_zero_right h_eq
        have h_norm_eq := congrArg norm h_lead
        rw [norm_mul, norm_pow, norm_neg] at h_norm_eq
        have h_rhs : ‖∑ j ∈ Finset.range d, (Q.coeff j).eval z * (f_entire z) ^ j‖ ≤
            (∑ j ∈ Finset.range d, ‖(Q.coeff j).eval z‖) * ‖f_entire z‖ ^ (d - 1) := by
          calc ‖∑ j ∈ Finset.range d, (Q.coeff j).eval z * (f_entire z) ^ j‖
              ≤ ∑ j ∈ Finset.range d, ‖(Q.coeff j).eval z * (f_entire z) ^ j‖ := norm_sum_le _ _
            _ ≤ ∑ j ∈ Finset.range d, ‖(Q.coeff j).eval z‖ * ‖f_entire z‖ ^ (d - 1) := by
                refine Finset.sum_le_sum fun j hj => ?_
                rw [norm_mul, norm_pow]
                exact mul_le_mul_of_nonneg_left
                  (pow_le_pow_right₀ hf1.le (Nat.le_pred_of_lt (Finset.mem_range.mp hj)))
                  (norm_nonneg _)
            _ = (∑ j ∈ Finset.range d, ‖(Q.coeff j).eval z‖) * ‖f_entire z‖ ^ (d - 1) := by
                rw [← Finset.sum_mul]
        have h_f_pos : 0 < ‖f_entire z‖ ^ (d - 1) := pow_pos (by linarith) _
        have h_d_eq : ‖f_entire z‖ ^ d = ‖f_entire z‖ * ‖f_entire z‖ ^ (d - 1) := by
          conv_lhs => rw [show d = 1 + (d - 1) by omega, pow_add, pow_one]
        rw [← h_norm_eq, h_d_eq, ← mul_assoc] at h_rhs
        have h_div : ‖(Q.coeff d).eval z‖ * ‖f_entire z‖ ≤
            ∑ j ∈ Finset.range d, ‖(Q.coeff j).eval z‖ :=
          le_of_mul_le_mul_right h_rhs h_f_pos
        have h_lb_z := h_lb z hz
        have h_ub_z := h_ub z hz1
        have h1 : (‖(Q.coeff d).leadingCoeff‖ / 2) * ‖z‖ ^ (Q.coeff d).natDegree * ‖f_entire z‖ ≤
            C1 * ‖z‖ ^ D := by
          calc (‖(Q.coeff d).leadingCoeff‖ / 2) * ‖z‖ ^ (Q.coeff d).natDegree * ‖f_entire z‖
              ≤ ‖(Q.coeff d).eval z‖ * ‖f_entire z‖ := by gcongr
            _ ≤ ∑ j ∈ Finset.range d, ‖(Q.coeff j).eval z‖ := h_div
            _ ≤ C1 * ‖z‖ ^ D := h_ub_z
        have h_zd_ge1 : 1 ≤ ‖z‖ ^ (Q.coeff d).natDegree := one_le_pow₀ hz1
        have h2 : (‖(Q.coeff d).leadingCoeff‖ / 2) * ‖f_entire z‖ ≤ C1 * ‖z‖ ^ D := by
          calc (‖(Q.coeff d).leadingCoeff‖ / 2) * ‖f_entire z‖
              = (‖(Q.coeff d).leadingCoeff‖ / 2) * 1 * ‖f_entire z‖ := by ring
            _ ≤ (‖(Q.coeff d).leadingCoeff‖ / 2) * ‖z‖ ^ (Q.coeff d).natDegree * ‖f_entire z‖ := by
                gcongr
            _ ≤ C1 * ‖z‖ ^ D := h1
        have h3 : ‖f_entire z‖ ≤ (2 * C1 / ‖(Q.coeff d).leadingCoeff‖) * ‖z‖ ^ D := by
          rw [div_mul_eq_mul_div, le_div_iff₀ h_lc_pos]
          linarith
        calc ‖f_entire z‖ ≤ (2 * C1 / ‖(Q.coeff d).leadingCoeff‖) * ‖z‖ ^ D := h3
          _ ≤ C2 * ‖z‖ ^ D := by gcongr; exact le_max_right _ _
    obtain ⟨K, hK⟩ := exists_nat_gt (max R C2 + 2 * D + 2)
    set k : ℕ := K + 1
    set r : ℝ := (4 : ℝ) ^ k
    have hr_pos : 0 < r := by positivity
    have hr_ge_R : R ≤ r := by
      have h1 : (K : ℝ) ≤ (4 : ℝ) ^ K := by
        exact_mod_cast (Nat.lt_pow_self (a := 4) (by norm_num : 1 < 4) (n := K)).le
      have h2 : R ≤ (K : ℝ) := by linarith [hK, le_max_left R C2, le_max_right R C2]
      have h3 : (4 : ℝ) ^ K ≤ r := by
        dsimp [r, k]
        exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ K)
      linarith
    have hM_le : ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f_entire z‖ ≤ C2 * r ^ D := by
      have : Nonempty {z : ℂ // ‖z‖ = r} := ⟨⟨(r : ℂ), by simp [abs_of_pos hr_pos]⟩⟩
      refine ciSup_le fun ⟨z, hz⟩ => ?_
      have h_res := h_poly_bound z (by rw [hz]; exact hr_ge_R)
      rwa [hz] at h_res
    have h_cauchy := term_le_sup_sphere hr_pos f_differentiable (k + 1)
    rw [f_term_norm (k + 1) hr_pos.le] at h_cauchy
    have h_lhs : (4 : ℝ) ^ (k * (k + 1) / 2) =
        (1 / 4 : ℝ) ^ ((k + 1) * (k + 1 - 1) / 2) * r ^ (k + 1) := by
      have h_exp : k * (k + 1) = 2 * (k * (k + 1) / 2) := by
        rw [mul_comm k (k + 1)]
        exact (Nat.mul_div_cancel' (by
          simpa [Nat.add_sub_cancel] using (Nat.even_mul_pred_self (k + 1)).two_dvd)).symm
      rw [show k + 1 - 1 = k by omega, mul_comm (k + 1) k]
      dsimp [r]
      rw [← pow_mul, h_exp, pow_mul, one_div, inv_pow]
      have h4 : (4 : ℝ) ^ (k * (k + 1) / 2) ≠ 0 := by positivity
      rw [Nat.mul_div_cancel_left _ (by norm_num), ← pow_mul, mul_comm 2 _, pow_mul]
      field_simp
    rw [← h_lhs] at h_cauchy
    have h_contra : (4 : ℝ) ^ (k * (k + 1) / 2) ≤ C2 * (4 : ℝ) ^ (k * D) := by
      calc (4 : ℝ) ^ (k * (k + 1) / 2) ≤ ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f_entire z‖ := h_cauchy
        _ ≤ C2 * r ^ D := hM_le
        _ = C2 * (4 : ℝ) ^ (k * D) := by dsimp [r]; rw [← pow_mul]
    have hk_gt : 2 * D + 2 < k := by
      have h1 : (2 * D + 2 : ℝ) < K := by linarith [hK, le_max_left R C2, le_max_right R C2, hR1]
      have h2 : 2 * D + 2 < K := by exact_mod_cast h1
      omega
    have h_exp_gt : k * D + k ≤ k * (k + 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      nlinarith
    have h4k_gt_C2 : C2 < (4 : ℝ) ^ k := by
      have h1 : (K : ℝ) ≤ (4 : ℝ) ^ K := by
        exact_mod_cast (Nat.lt_pow_self (a := 4) (by norm_num : 1 < 4) (n := K)).le
      have h2 : C2 < K := by linarith [hK, le_max_left R C2, le_max_right R C2, hR1]
      have h3 : (4 : ℝ) ^ K ≤ (4 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (Nat.le_succ K)
      linarith
    have h_strict : C2 * (4 : ℝ) ^ (k * D) < (4 : ℝ) ^ (k * (k + 1) / 2) := by
      calc C2 * (4 : ℝ) ^ (k * D) < (4 : ℝ) ^ k * (4 : ℝ) ^ (k * D) := by
            gcongr
        _ = (4 : ℝ) ^ (k * D + k) := by rw [← pow_add, add_comm]
        _ ≤ (4 : ℝ) ^ (k * (k + 1) / 2) := pow_le_pow_right₀ (by norm_num) h_exp_gt
    linarith

theorem OMA.solution : type_of% @Erdos513.erdos_513.variants.lower_bound := by
  have h_ub : Filter.atTop.IsBoundedUnder (· ≤ ·) (fun r : ℝ => Erdos513.ratio r f_entire) :=
    ⟨1, Filter.eventually_map.mpr
      ((Filter.eventually_gt_atTop 0).mono fun _ hr => ratio_le_one hr f_differentiable)⟩
  have h_liminf : (100 / 199 : ℝ) ≤ Filter.liminf (fun r : ℝ => Erdos513.ratio r f_entire) Filter.atTop :=
    Filter.le_liminf_of_le h_ub.isCoboundedUnder_ge
      (Filter.eventually_ge_atTop 64 |>.mono fun _ hr => ratio_f_ge hr)
  have h_bdd : BddAbove (Set.range fun g : {g : ℂ → ℂ // Transcendental ℂ[X] g ∧ Differentiable ℂ g} =>
      Filter.liminf (fun r : ℝ => Erdos513.ratio r g) Filter.atTop) :=
    ⟨1, Set.forall_mem_range.mpr fun g => liminf_ratio_le_one g.2.2⟩
  have h_le_max : Filter.liminf (fun r : ℝ => Erdos513.ratio r f_entire) Filter.atTop ≤
      Erdos513.maxTermConstant :=
    le_ciSup h_bdd ⟨f_entire, f_transcendental, f_differentiable⟩
  linarith
