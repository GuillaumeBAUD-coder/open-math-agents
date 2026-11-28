import OMAReductions.R_Erdos66_erdos_66_R1

/-!
Proof of `Erdos66.erdos_66.R1.H1`: for `a > 0` and
`p i = a * √((1 + log (i + 1)) / (i + 1))`, the weights `p` are antitone, nonnegative, and
`sumConv p p n / log n → π * a ^ 2` as `n → ∞`.
-/

-- Problem: Erdos66.erdos_66.R1.H1
-- Upstream: reductions/Erdos66.erdos_66.R1.lean
-- Credit: @ppleskov

namespace OMA.P_Erdos66_R1_H1

open AdditiveCombinatorics Finset Filter
open scoped Topology

private lemma one_add_log_div_antitone {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    (1 + Real.log y) / y ≤ (1 + Real.log x) / x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  rw [div_le_div_iff₀ hy0 hx0]
  have hlog : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  rw [Real.log_div hy0.ne' hx0.ne'] at hlog
  have hmul : x * (Real.log y - Real.log x) ≤ y - x := by
    have h1 := mul_le_mul_of_nonneg_left hlog hx0.le
    have h2 : x * (y / x - 1) = y - x := by field_simp [hx0.ne']
    linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  nlinarith

private lemma sum_inv_sqrt_le (K : ℕ) :
    ∑ i ∈ range K, (1 : ℝ) / Real.sqrt ((i : ℝ) + 1) ≤ 2 * Real.sqrt (K : ℝ) := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have hsq : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt hk1.le
    have hsq0 : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hk0
    have hle : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have hstep : 1 / Real.sqrt ((k : ℝ) + 1) ≤
        2 * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ)) := by
      rw [div_le_iff₀ (Real.sqrt_pos.mpr hk1)]
      have hdiff : (Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ)) *
          (Real.sqrt ((k : ℝ) + 1) + Real.sqrt (k : ℝ)) = 1 := by
        nlinarith [hsq, hsq0]
      nlinarith [Real.sqrt_nonneg (k : ℝ), Real.sqrt_pos.mpr hk1]
    push_cast
    linarith

private noncomputable def arcsinMid (t : ℝ) : ℝ := Real.arcsin (2 * t - 1)

private noncomputable def betaKern (t : ℝ) : ℝ := 1 / Real.sqrt (t * (1 - t))

private lemma hasDerivAt_arcsinMid {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt arcsinMid (betaKern t) t := by
  have hlin : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
  have hcomp : HasDerivAt (fun x : ℝ => Real.arcsin (2 * x - 1))
      (1 / Real.sqrt (1 - (2 * t - 1) ^ 2) * 2) t :=
    (Real.hasDerivAt_arcsin (by linarith) (by linarith)).comp t hlin
  refine hcomp.congr_deriv ?_
  have hquad : 1 - (2 * t - 1) ^ 2 = 4 * (t * (1 - t)) := by ring
  rw [hquad, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hpos : 0 < Real.sqrt (t * (1 - t)) := Real.sqrt_pos.mpr (mul_pos ht0 (sub_pos.mpr ht1))
  unfold betaKern
  field_simp [hpos.ne']

private lemma betaKern_anti_left {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) :
    betaKern y ≤ betaKern x := by
  unfold betaKern
  have hprod : x * (1 - x) ≤ y * (1 - y) := by nlinarith
  have hxpos : 0 < x * (1 - x) := mul_pos hx (by linarith)
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hxpos) (Real.sqrt_le_sqrt hprod)

private lemma betaKern_mono_right {x y : ℝ} (hx : 1 / 2 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    betaKern x ≤ betaKern y := by
  unfold betaKern
  have hprod : y * (1 - y) ≤ x * (1 - x) := by nlinarith
  have hypos : 0 < y * (1 - y) := mul_pos (by linarith) (sub_pos.mpr hy)
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hypos) (Real.sqrt_le_sqrt hprod)

private lemma arcsinMid_diff_bounds_left {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2) :
    betaKern b * (b - a) ≤ arcsinMid b - arcsinMid a ∧
    arcsinMid b - arcsinMid a ≤ betaKern a * (b - a) := by
  have hcont : ContinuousOn arcsinMid (Set.Icc a b) := by
    intro x hx
    exact (hasDerivAt_arcsinMid (lt_of_lt_of_le ha hx.1) (lt_of_le_of_lt hx.2 (by linarith))).continuousAt.continuousWithinAt
  have hdiff : ∀ x ∈ Set.Ioo a b, HasDerivAt arcsinMid (betaKern x) x := fun x hx =>
    hasDerivAt_arcsinMid (lt_trans ha hx.1) (lt_trans hx.2 (by linarith))
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope arcsinMid betaKern hab hcont hdiff
  have hba : 0 < b - a := sub_pos.mpr hab
  have heq : arcsinMid b - arcsinMid a = betaKern c * (b - a) := by
    rw [hslope, div_mul_cancel₀ _ hba.ne']
  rw [heq]
  exact ⟨mul_le_mul_of_nonneg_right (betaKern_anti_left (lt_trans ha hc.1) hc.2.le hb) hba.le,
    mul_le_mul_of_nonneg_right (betaKern_anti_left ha hc.1.le (hc.2.le.trans hb)) hba.le⟩

private lemma arcsinMid_diff_bounds_right {a b : ℝ} (ha : 1 / 2 ≤ a) (hab : a < b) (hb : b < 1) :
    betaKern a * (b - a) ≤ arcsinMid b - arcsinMid a ∧
    arcsinMid b - arcsinMid a ≤ betaKern b * (b - a) := by
  have hcont : ContinuousOn arcsinMid (Set.Icc a b) := by
    intro x hx
    exact (hasDerivAt_arcsinMid (by linarith [hx.1]) (lt_of_le_of_lt hx.2 hb)).continuousAt.continuousWithinAt
  have hdiff : ∀ x ∈ Set.Ioo a b, HasDerivAt arcsinMid (betaKern x) x := fun x hx =>
    hasDerivAt_arcsinMid (by linarith [hx.1]) (lt_trans hx.2 hb)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope arcsinMid betaKern hab hcont hdiff
  have hba : 0 < b - a := sub_pos.mpr hab
  have heq : arcsinMid b - arcsinMid a = betaKern c * (b - a) := by
    rw [hslope, div_mul_cancel₀ _ hba.ne']
  rw [heq]
  exact ⟨mul_le_mul_of_nonneg_right (betaKern_mono_right ha hc.1.le (lt_trans hc.2 hb)) hba.le,
    mul_le_mul_of_nonneg_right (betaKern_mono_right (ha.trans hc.1.le) hc.2.le hb) hba.le⟩

private noncomputable def betaSum (n : ℕ) : ℝ :=
  ∑ i ∈ range (n + 1), 1 / Real.sqrt (((i : ℝ) + 1) * (((n - i : ℕ) : ℝ) + 1))

private lemma betaSum_eq_scaled (n : ℕ) :
    betaSum n = ∑ k ∈ Icc 1 (n + 1), betaKern ((k : ℝ) / ((n : ℝ) + 2)) * (1 / ((n : ℝ) + 2)) := by
  unfold betaSum
  have hN : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    rw [mem_range] at hi
    rw [mem_Icc]
    omega
  · intro i₁ _ i₂ _ h
    omega
  · intro k hk
    rw [mem_Icc] at hk
    exact ⟨k - 1, mem_range.mpr (by omega), by omega⟩
  · intro i hi
    rw [mem_range] at hi
    have hsub : ((n - i : ℕ) : ℝ) + 1 = ((n : ℝ) + 2) - (((i + 1 : ℕ) : ℝ)) := by
      have hi' : i ≤ n := by omega
      rw [Nat.cast_sub hi']
      push_cast
      ring
    unfold betaKern
    have h1 : (((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 2)) * (1 - ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 2)) =
        (((i : ℝ) + 1) * (((n - i : ℕ) : ℝ) + 1)) / ((n : ℝ) + 2) ^ 2 := by
      rw [hsub]
      push_cast
      field_simp [hN.ne']
    rw [h1, Real.sqrt_div (by positivity), Real.sqrt_sq hN.le]
    field_simp [hN.ne']

private lemma betaSum_bounds {n : ℕ} (hn : 4 ≤ n) :
    arcsinMid (((n : ℝ) + 1) / ((n : ℝ) + 2)) - arcsinMid (1 / ((n : ℝ) + 2)) -
      8 / ((n : ℝ) + 2) ≤ betaSum n ∧
    betaSum n ≤ arcsinMid (((n : ℝ) + 1) / ((n : ℝ) + 2)) - arcsinMid (1 / ((n : ℝ) + 2)) +
      8 / ((n : ℝ) + 2) + 2 / Real.sqrt ((n : ℝ) + 1) := by
  set N : ℝ := (n : ℝ) + 2
  have hNpos : 0 < N := by positivity
  set m : ℕ := (n + 2) / 2
  have hm1 : 2 ≤ m := by dsimp [m]; omega
  have hm_le : 2 * m ≤ n + 2 := Nat.mul_div_le (n + 2) 2
  have hm_gt : n + 2 ≤ 2 * m + 1 := by dsimp [m]; omega
  have hm_lt : m + 1 ≤ n + 1 := by dsimp [m]; omega
  have hmt_le : (m : ℝ) / N ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hNpos (by norm_num : (0 : ℝ) < 2)]
    have : ((2 * m : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_le.mpr hm_le
    push_cast at this
    dsimp [N]
    linarith
  have hmt1_ge : 1 / 2 ≤ ((m + 1 : ℕ) : ℝ) / N := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hNpos]
    have : ((n + 2 : ℕ) : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hm_gt
    push_cast at this ⊢
    dsimp [N]
    linarith
  let g (k : ℕ) : ℝ := betaKern ((k : ℝ) / N) * (1 / N)
  let F (k : ℕ) : ℝ := arcsinMid ((k : ℝ) / N)
  have hleft_step : ∀ k ∈ Ico 1 m,
      g (k + 1) ≤ F (k + 1) - F k ∧ F (k + 1) - F k ≤ g k := by
    intro k hk
    rw [mem_Ico] at hk
    have ha : 0 < (k : ℝ) / N := div_pos (Nat.cast_pos.mpr (by omega)) hNpos
    have hab : (k : ℝ) / N < ((k + 1 : ℕ) : ℝ) / N :=
      div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self k) hNpos
    have hb : ((k + 1 : ℕ) : ℝ) / N ≤ 1 / 2 := by
      refine le_trans (div_le_div_of_nonneg_right ?_ hNpos.le) hmt_le
      exact_mod_cast (show k + 1 ≤ m by omega)
    have hdiff_eq : ((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N = 1 / N := by
      push_cast; field_simp [hNpos.ne']; ring
    have hbnd := arcsinMid_diff_bounds_left ha hab hb
    rw [hdiff_eq] at hbnd
    simpa [g, F] using hbnd
  have hright_step : ∀ k ∈ Ico (m + 1) (n + 1),
      g k ≤ F (k + 1) - F k ∧ F (k + 1) - F k ≤ g (k + 1) := by
    intro k hk
    rw [mem_Ico] at hk
    have ha : 1 / 2 ≤ (k : ℝ) / N := by
      refine le_trans hmt1_ge (div_le_div_of_nonneg_right ?_ hNpos.le)
      exact_mod_cast hk.1
    have hab : (k : ℝ) / N < ((k + 1 : ℕ) : ℝ) / N :=
      div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self k) hNpos
    have hb : ((k + 1 : ℕ) : ℝ) / N < 1 := by
      rw [div_lt_one hNpos]
      have : k + 1 < n + 2 := by omega
      have hcast : ((k + 1 : ℕ) : ℝ) < ((n + 2 : ℕ) : ℝ) := Nat.cast_lt.mpr this
      push_cast at hcast
      simpa [N] using hcast
    have hdiff_eq : ((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N = 1 / N := by
      push_cast; field_simp [hNpos.ne']; ring
    have hbnd := arcsinMid_diff_bounds_right ha hab hb
    rw [hdiff_eq] at hbnd
    simpa [g, F] using hbnd
  -- Bound the middle transition F (m + 1) - F m and g m, g (m + 1), g 1, g (n + 1)
  have hmid_interval : ∀ t ∈ Set.Icc ((m : ℝ) / N) (((m + 1 : ℕ) : ℝ) / N),
      betaKern t ≤ 4 := by
    intro t ht
    have ht_lo : 1 / 4 ≤ t := by
      have : (1 / 4 : ℝ) ≤ (m : ℝ) / N := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hNpos]
        have : n + 2 ≤ 4 * m := by dsimp [m]; omega
        have hcast : ((n + 2 : ℕ) : ℝ) ≤ ((4 * m : ℕ) : ℝ) := Nat.cast_le.mpr this
        push_cast at hcast
        dsimp [N]; linarith
      linarith [ht.1]
    have ht_hi : t ≤ 3 / 4 := by
      have : ((m + 1 : ℕ) : ℝ) / N ≤ 3 / 4 := by
        rw [div_le_div_iff₀ hNpos (by norm_num : (0 : ℝ) < 4)]
        have : 4 * (m + 1) ≤ 3 * (n + 2) := by dsimp [m]; omega
        have hcast : ((4 * (m + 1) : ℕ) : ℝ) ≤ ((3 * (n + 2) : ℕ) : ℝ) := Nat.cast_le.mpr this
        push_cast at hcast ⊢
        dsimp [N]; linarith
      linarith [ht.2]
    unfold betaKern
    have hprod : (1 / 16 : ℝ) ≤ t * (1 - t) := by nlinarith
    have hsqrt : (1 / 4 : ℝ) ≤ Real.sqrt (t * (1 - t)) := by
      rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
        rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hprod
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (by linarith))]
    linarith
  have hmid_F : 0 ≤ F (m + 1) - F m ∧ F (m + 1) - F m ≤ 4 / N := by
    have hab : (m : ℝ) / N < ((m + 1 : ℕ) : ℝ) / N :=
      div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self m) hNpos
    have hcont : ContinuousOn arcsinMid (Set.Icc ((m : ℝ) / N) (((m + 1 : ℕ) : ℝ) / N)) := by
      intro x hx
      have h1 : 0 < x := by
        have := div_pos (Nat.cast_pos.mpr (by omega : 0 < m)) hNpos
        linarith [hx.1]
      have h2 : x < 1 := by
        have : ((m + 1 : ℕ) : ℝ) / N < 1 := by
          rw [div_lt_one hNpos]
          have : m + 1 < n + 2 := by omega
          have hcast : ((m + 1 : ℕ) : ℝ) < ((n + 2 : ℕ) : ℝ) := Nat.cast_lt.mpr this
          push_cast at hcast; simpa [N] using hcast
        linarith [hx.2]
      exact (hasDerivAt_arcsinMid h1 h2).continuousAt.continuousWithinAt
    have hdiff : ∀ x ∈ Set.Ioo ((m : ℝ) / N) (((m + 1 : ℕ) : ℝ) / N),
        HasDerivAt arcsinMid (betaKern x) x := by
      intro x hx
      have h1 : 0 < x := lt_trans (div_pos (Nat.cast_pos.mpr (by omega : 0 < m)) hNpos) hx.1
      have h2 : x < 1 := by
        have : ((m + 1 : ℕ) : ℝ) / N < 1 := by
          rw [div_lt_one hNpos]
          have : m + 1 < n + 2 := by omega
          have hcast : ((m + 1 : ℕ) : ℝ) < ((n + 2 : ℕ) : ℝ) := Nat.cast_lt.mpr this
          push_cast at hcast; simpa [N] using hcast
        linarith [hx.2]
      exact hasDerivAt_arcsinMid h1 h2
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope arcsinMid betaKern hab hcont hdiff
    have hba : ((m + 1 : ℕ) : ℝ) / N - (m : ℝ) / N = 1 / N := by
      push_cast; field_simp [hNpos.ne']; ring
    have heq : F (m + 1) - F m = betaKern c * (1 / N) := by
      dsimp [F]
      rw [← hba, hslope, div_mul_cancel₀ _ (sub_pos.mpr hab).ne']
    rw [heq]
    have hc_le : betaKern c ≤ 4 := hmid_interval c ⟨hc.1.le, hc.2.le⟩
    have hc_nn : 0 ≤ betaKern c := by unfold betaKern; positivity
    exact ⟨mul_nonneg hc_nn (by positivity), by
      rw [mul_one_div]; exact div_le_div_of_nonneg_right hc_le hNpos.le⟩
  have hgm : g m ≤ 4 / N := by
    dsimp [g]
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (hmid_interval _ ⟨le_rfl,
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ m) hNpos.le⟩) hNpos.le
  have hgm1 : g (m + 1) ≤ 4 / N := by
    dsimp [g]
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (hmid_interval _ ⟨
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ m) hNpos.le, le_rfl⟩) hNpos.le
  have hg1 : g 1 = 1 / Real.sqrt ((n : ℝ) + 1) := by
    dsimp [g, betaKern]
    have h1 : (1 : ℝ) / N * (1 - 1 / N) = ((n : ℝ) + 1) / N ^ 2 := by
      dsimp [N]; field_simp [hNpos.ne']; ring
    rw [Nat.cast_one, h1, Real.sqrt_div (by positivity), Real.sqrt_sq hNpos.le]
    field_simp [hNpos.ne']
  have hgn1 : g (n + 1) = 1 / Real.sqrt ((n : ℝ) + 1) := by
    dsimp [g, betaKern]
    have h1 : (((n + 1 : ℕ) : ℝ) / N) * (1 - ((n + 1 : ℕ) : ℝ) / N) = ((n : ℝ) + 1) / N ^ 2 := by
      push_cast; dsimp [N]; field_simp [hNpos.ne']; ring
    rw [h1, Real.sqrt_div (by positivity), Real.sqrt_sq hNpos.le]
    field_simp [hNpos.ne']
  have hg_nn : ∀ k, 0 ≤ g k := fun k => by dsimp [g, betaKern]; positivity
  -- Split `Icc 1 (n + 1)` into `Ico 1 m ∪ {m} ∪ {m + 1} ∪ Ico (m + 2) (n + 2)`
  have hsplit : ∑ k ∈ Icc 1 (n + 1), g k =
      (∑ k ∈ Ico 1 m, g k) + g m + (∑ k ∈ Ico (m + 1) (n + 1), g k) + g (n + 1) := by
    rw [← Finset.Ico_succ_right_eq_Icc]
    change ∑ k ∈ Ico 1 (n + 1 + 1), g k = _
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
    have hsplit2 : ∑ k ∈ Ico 1 (n + 1), g k =
        (∑ k ∈ Ico 1 (m + 1), g k) + ∑ k ∈ Ico (m + 1) (n + 1), g k :=
      (Finset.sum_Ico_consecutive g (by omega : 1 ≤ m + 1) hm_lt).symm
    rw [hsplit2, Finset.sum_Ico_succ_top (by omega : 1 ≤ m)]
  -- Also write the shifted version for upper bound:
  -- `Icc 1 (n + 1)` = `{1} ∪ Ico 2 (m + 1) ∪ {m + 1} ∪ Ico (m + 2) (n + 2)`
  have hsum_L_upper : ∑ k ∈ Ico 1 m, g (k + 1) ≤ F m - F 1 := by
    calc ∑ k ∈ Ico 1 m, g (k + 1)
        ≤ ∑ k ∈ Ico 1 m, (F (k + 1) - F k) := sum_le_sum fun k hk => (hleft_step k hk).1
      _ = F m - F 1 := Finset.sum_Ico_sub F (by omega : 1 ≤ m)
  have hsum_L_lower : F m - F 1 ≤ ∑ k ∈ Ico 1 m, g k := by
    calc F m - F 1 = ∑ k ∈ Ico 1 m, (F (k + 1) - F k) := (Finset.sum_Ico_sub F (by omega : 1 ≤ m)).symm
      _ ≤ ∑ k ∈ Ico 1 m, g k := sum_le_sum fun k hk => (hleft_step k hk).2
  have hsum_R_upper : ∑ k ∈ Ico (m + 1) (n + 1), g k ≤ F (n + 1) - F (m + 1) := by
    calc ∑ k ∈ Ico (m + 1) (n + 1), g k
        ≤ ∑ k ∈ Ico (m + 1) (n + 1), (F (k + 1) - F k) := sum_le_sum fun k hk => (hright_step k hk).1
      _ = F (n + 1) - F (m + 1) := Finset.sum_Ico_sub F hm_lt
  have hsum_R_lower : F (n + 1) - F (m + 1) ≤ ∑ k ∈ Ico (m + 1) (n + 1), g (k + 1) := by
    calc F (n + 1) - F (m + 1) = ∑ k ∈ Ico (m + 1) (n + 1), (F (k + 1) - F k) :=
          (Finset.sum_Ico_sub F hm_lt).symm
      _ ≤ ∑ k ∈ Ico (m + 1) (n + 1), g (k + 1) := sum_le_sum fun k hk => (hright_step k hk).2
  have hshift_L : ∑ k ∈ Ico 1 m, g k = g 1 + (∑ k ∈ Ico 1 m, g (k + 1)) - g m := by
    have h1 : ∑ k ∈ Ico 1 m, g (k + 1) = ∑ k ∈ Ico 2 (m + 1), g k := by
      refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
      · intro k hk; rw [mem_Ico] at hk ⊢; omega
      · intro _ _ _ _ h; omega
      · intro k hk; rw [mem_Ico] at hk; exact ⟨k - 1, mem_Ico.mpr (by omega), by omega⟩
      · intro _ _; rfl
    rw [h1, Finset.sum_Ico_succ_top (by omega : 2 ≤ m),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < m)]
    ring
  have hshift_R : ∑ k ∈ Ico (m + 1) (n + 1), g (k + 1) =
      (∑ k ∈ Ico (m + 1) (n + 1), g k) - g (m + 1) + g (n + 1) := by
    have h1 : ∑ k ∈ Ico (m + 1) (n + 1), g (k + 1) = ∑ k ∈ Ico (m + 2) (n + 2), g k := by
      refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
      · intro k hk; rw [mem_Ico] at hk ⊢; omega
      · intro _ _ _ _ h; omega
      · intro k hk; rw [mem_Ico] at hk; exact ⟨k - 1, mem_Ico.mpr (by omega), by omega⟩
      · intro _ _; rfl
    by_cases hmn : m + 1 < n + 1
    · rw [h1, Finset.sum_Ico_succ_top (by omega : m + 2 ≤ n + 1),
        Finset.sum_eq_sum_Ico_succ_bot hmn]
      ring
    · have heq : m + 1 = n + 1 := by omega
      simp [heq]
  have hF1 : F 1 = arcsinMid (1 / N) := by simp [F]
  have hFn1 : F (n + 1) = arcsinMid (((n : ℝ) + 1) / N) := by simp [F]
  have h4N : 0 ≤ 4 / N := by positivity
  have h8N : 0 ≤ 8 / N := by positivity
  have h48N : 4 / N ≤ 8 / N := by
    apply div_le_div_of_nonneg_right (by norm_num) hNpos.le
  have h2sq : 1 / Real.sqrt ((n : ℝ) + 1) + 1 / Real.sqrt ((n : ℝ) + 1) =
      2 / Real.sqrt ((n : ℝ) + 1) := by ring
  rw [betaSum_eq_scaled]
  change _ ≤ ∑ k ∈ Icc 1 (n + 1), g k ∧ ∑ k ∈ Icc 1 (n + 1), g k ≤ _
  rw [hsplit, ← hF1, ← hFn1]
  constructor
  · linarith [hsum_L_lower, hsum_R_lower, hshift_R, hmid_F.2, hgm1, hg_nn m, hg_nn (m + 1), h48N]
  · linarith [hsum_L_upper, hsum_R_upper, hshift_L, hmid_F.1, hgm, hg1, hgn1, h8N, h2sq]

private lemma tendsto_betaSum : Tendsto betaSum atTop (𝓝 Real.pi) := by
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hone : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) atTop (𝓝 1) := by
    have hrew : (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) =
        (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) := by
      ext n
      have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      field_simp [hpos.ne']
      ring
    rw [hrew]
    simpa using tendsto_const_nhds.sub hinv
  have hF_lo : Tendsto (fun n : ℕ => arcsinMid (1 / ((n : ℝ) + 2))) atTop (𝓝 (-(Real.pi / 2))) := by
    have h1 : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 2)) - 1) atTop (𝓝 (-1)) := by
      have h := (tendsto_const_nhds (x := (2 : ℝ)).mul hinv).sub (tendsto_const_nhds (x := (1 : ℝ)))
      simpa using h
    have h2 := Real.continuous_arcsin.continuousAt.tendsto.comp h1
    simpa [arcsinMid, Function.comp_def, Real.arcsin_neg_one] using h2
  have hF_hi : Tendsto (fun n : ℕ => arcsinMid (((n : ℝ) + 1) / ((n : ℝ) + 2))) atTop (𝓝 (Real.pi / 2)) := by
    have h1 : Tendsto (fun n : ℕ => 2 * (((n : ℝ) + 1) / ((n : ℝ) + 2)) - 1) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (2 : ℝ)).mul hone).sub (tendsto_const_nhds (x := (1 : ℝ)))
      norm_num at h
      exact h
    have h2 := Real.continuous_arcsin.continuousAt.tendsto.comp h1
    simpa [arcsinMid, Function.comp_def, Real.arcsin_one] using h2
  have hdiff : Tendsto (fun n : ℕ =>
      arcsinMid (((n : ℝ) + 1) / ((n : ℝ) + 2)) - arcsinMid (1 / ((n : ℝ) + 2)))
      atTop (𝓝 Real.pi) := by
    have h := hF_hi.sub hF_lo
    rwa [show Real.pi / 2 - -(Real.pi / 2) = Real.pi by ring] at h
  have h8 : Tendsto (fun n : ℕ => 8 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hsq : Tendsto (fun n : ℕ => 2 / Real.sqrt ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hsqrt_top : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    exact tendsto_const_nhds.div_atTop hsqrt_top
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by have h := hdiff.sub h8; rw [sub_zero] at h; exact h)
    (by have h := (hdiff.add h8).add hsq; rw [add_zero, add_zero] at h; exact h) ?_ ?_
  · filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
    exact (betaSum_bounds hn).1
  · filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
    exact (betaSum_bounds hn).2

private lemma tail_beta_le {n K : ℕ} (hn : 4 ≤ n) (hK : K ≤ n / 2 + 1) :
    ∑ i ∈ range K, 1 / Real.sqrt (((i : ℝ) + 1) * (((n - i : ℕ) : ℝ) + 1)) ≤
      4 * Real.sqrt ((K : ℝ) / (n : ℝ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hstep : ∀ i ∈ range K,
      1 / Real.sqrt (((i : ℝ) + 1) * (((n - i : ℕ) : ℝ) + 1)) ≤
        (2 / Real.sqrt (n : ℝ)) * (1 / Real.sqrt ((i : ℝ) + 1)) := by
    intro i hi
    rw [mem_range] at hi
    have hi_le : i ≤ n / 2 := by omega
    have hni : (n : ℝ) / 4 ≤ ((n - i : ℕ) : ℝ) + 1 := by
      have h1 : n / 2 ≤ n - i := by omega
      have h2 : (n : ℝ) / 2 - 1 ≤ ((n - i : ℕ) : ℝ) := by
        have : n ≤ 2 * (n - i) + 1 := by omega
        have hcast : (n : ℝ) ≤ 2 * ((n - i : ℕ) : ℝ) + 1 := by exact_mod_cast this
        linarith
      have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hsq_ge : Real.sqrt (n : ℝ) / 2 ≤ Real.sqrt (((n - i : ℕ) : ℝ) + 1) := by
      have h1 : Real.sqrt ((n : ℝ) / 4) ≤ Real.sqrt (((n - i : ℕ) : ℝ) + 1) :=
        Real.sqrt_le_sqrt hni
      rw [Real.sqrt_div hnpos.le, show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h1
      exact h1
    rw [Real.sqrt_mul (by positivity)]
    have h1 : 1 / (Real.sqrt ((i : ℝ) + 1) * Real.sqrt (((n - i : ℕ) : ℝ) + 1)) ≤
        1 / (Real.sqrt ((i : ℝ) + 1) * (Real.sqrt (n : ℝ) / 2)) :=
      one_div_le_one_div_of_le (mul_pos (Real.sqrt_pos.mpr (by positivity))
        (div_pos (Real.sqrt_pos.mpr hnpos) (by norm_num)))
        (mul_le_mul_of_nonneg_left hsq_ge (Real.sqrt_nonneg _))
    calc _ ≤ 1 / (Real.sqrt ((i : ℝ) + 1) * (Real.sqrt (n : ℝ) / 2)) := h1
      _ = (2 / Real.sqrt (n : ℝ)) * (1 / Real.sqrt ((i : ℝ) + 1)) := by ring
  calc ∑ i ∈ range K, 1 / Real.sqrt (((i : ℝ) + 1) * (((n - i : ℕ) : ℝ) + 1))
      ≤ ∑ i ∈ range K, (2 / Real.sqrt (n : ℝ)) * (1 / Real.sqrt ((i : ℝ) + 1)) :=
        sum_le_sum hstep
    _ = (2 / Real.sqrt (n : ℝ)) * ∑ i ∈ range K, 1 / Real.sqrt ((i : ℝ) + 1) :=
        (mul_sum ..).symm
    _ ≤ (2 / Real.sqrt (n : ℝ)) * (2 * Real.sqrt (K : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_inv_sqrt_le K) (by positivity)
    _ = 4 * Real.sqrt ((K : ℝ) / (n : ℝ)) := by
        rw [Real.sqrt_div (Nat.cast_nonneg K)]; ring

private lemma tendsto_unit_conv :
    let q : ℕ → ℝ := fun i ↦ Real.sqrt ((1 + Real.log ((i : ℝ) + 1)) / ((i : ℝ) + 1))
    Tendsto (fun n : ℕ ↦ sumConv q q n / Real.log n) atTop (𝓝 Real.pi) := by
  intro q
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Choose `δ > 0` small enough so `100 * √(2 * δ) < ε / 3` and `δ ≤ 1 / 8`.
  let δ : ℝ := min (1 / 8) ((ε / 600) ^ 2)
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδle : δ ≤ 1 / 8 := min_le_left _ _
  have hδsq : Real.sqrt (2 * δ) ≤ ε / 300 := by
    have h1 : 2 * δ ≤ (ε / 300) ^ 2 := by
      have h2 : δ ≤ (ε / 600) ^ 2 := min_le_right _ _
      nlinarith
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  -- Get `N1` so `|betaSum n - π| < ε / 3` and `betaSum n ≤ 4` for `n ≥ N1`.
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp tendsto_betaSum) (min (ε / 3) (1 / 2))
    (lt_min (by positivity) (by norm_num))
  -- Get `N2` so `(1 + |log δ|) / log n < ε / 24` and `(1 + log (n + 1)) / log n - 1 < ε / 24`
  -- and `(1 + log (n + 1)) / log n ≤ 3` and `1 / δ ≤ n`.
  have hlog_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv_log : Tendsto (fun n : ℕ => (1 + |Real.log δ|) / Real.log (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog_top
  obtain ⟨N2, hN2⟩ := (eventually_atTop.mp
    ((hinv_log.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 24 by positivity))).and
     ((hlog_top.eventually_ge_atTop (max 2 (48 / ε))).and
      (eventually_ge_atTop (max 8 (Nat.ceil (2 / δ)))))))
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := (le_max_left _ _).trans hn
  have hn2 : N2 ≤ n := (le_max_right _ _).trans hn
  obtain ⟨hlog_δ_small, hlog_ge, hn_big⟩ := hN2 n hn2
  have hn8 : 8 ≤ n := (le_max_left _ _).trans hn_big
  have hnδ : 2 / δ ≤ (n : ℝ) :=
    (Nat.le_ceil (2 / δ)).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hn_big))
  have hlog_ge2 : 2 ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hlog_ge
  have hlog_geE : 48 / ε ≤ Real.log (n : ℝ) := (le_max_right _ _).trans hlog_ge
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hbeta_dist : |betaSum n - Real.pi| < min (ε / 3) (1 / 2) := by
    simpa [Real.dist_eq] using hN1 n hn1
  have hbeta_ε : |betaSum n - Real.pi| < ε / 3 := lt_of_lt_of_le hbeta_dist (min_le_left _ _)
  have hbeta_le4 : betaSum n ≤ 4 := by
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have hlt : betaSum n - Real.pi < 1 / 2 := (abs_lt.mp (lt_of_lt_of_le hbeta_dist (min_le_right _ _))).2
    linarith
  -- Express `sumConv q q n / log n` as weighted `betaSum n`.
  let W (i : ℕ) : ℝ :=
    Real.sqrt ((1 + Real.log ((i : ℝ) + 1)) * (1 + Real.log (((n - i : ℕ) : ℝ) + 1))) / Real.log (n : ℝ)
  let B (i : ℕ) : ℝ := 1 / Real.sqrt (((i : ℝ) + 1) * (((n - i : ℕ) : ℝ) + 1))
  have hconv_eq : sumConv q q n / Real.log (n : ℝ) = ∑ i ∈ range (n + 1), W i * B i := by
    rw [sumConv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
    refine sum_congr rfl fun i _ => ?_
    dsimp [q, W, B]
    have hL1 : 0 ≤ 1 + Real.log ((i : ℝ) + 1) := by
      have : 0 ≤ Real.log ((i : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) i])
      linarith
    have hL2 : 0 ≤ 1 + Real.log (((n - i : ℕ) : ℝ) + 1) := by
      have : 0 ≤ Real.log (((n - i : ℕ) : ℝ) + 1) :=
        Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (n - i)])
      linarith
    rw [Real.sqrt_div hL1, Real.sqrt_div hL2, Real.sqrt_mul hL1, Real.sqrt_mul (by positivity)]
    ring
  have hdiff_eq : sumConv q q n / Real.log (n : ℝ) - betaSum n =
      ∑ i ∈ range (n + 1), (W i - 1) * B i := by
    rw [hconv_eq, betaSum, ← Finset.sum_sub_distrib]
    refine sum_congr rfl fun i _ => by dsimp [B]; ring
  -- Bound `W i` uniformly on all `i ≤ n`, and tightly on the middle.
  have hlog_np1 : Real.log ((n : ℝ) + 1) ≤ Real.log (n : ℝ) + 1 := by
    have h1 : (n : ℝ) + 1 ≤ (n : ℝ) * Real.exp 1 := by
      have he : (2 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) (Real.add_one_le_exp 1)
      have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      nlinarith
    calc Real.log ((n : ℝ) + 1)
        ≤ Real.log ((n : ℝ) * Real.exp 1) := Real.log_le_log (by positivity) h1
      _ = Real.log (n : ℝ) + 1 := by rw [Real.log_mul hnpos.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have hW_upper : ∀ i ∈ range (n + 1), W i ≤ 1 + 2 / Real.log (n : ℝ) := by
    intro i hi
    rw [mem_range] at hi
    dsimp [W]
    have h1 : 1 + Real.log ((i : ℝ) + 1) ≤ Real.log (n : ℝ) + 2 := by
      have := Real.log_le_log (by positivity) (show (i : ℝ) + 1 ≤ (n : ℝ) + 1 by
        exact_mod_cast (show i + 1 ≤ n + 1 by omega))
      linarith
    have h2 : 1 + Real.log (((n - i : ℕ) : ℝ) + 1) ≤ Real.log (n : ℝ) + 2 := by
      have := Real.log_le_log (by positivity) (show ((n - i : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 1 by
        exact_mod_cast (show (n - i) + 1 ≤ n + 1 by omega))
      linarith
    have hL1 : 0 ≤ 1 + Real.log ((i : ℝ) + 1) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (i : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) i])]
    have hL2 : 0 ≤ 1 + Real.log (((n - i : ℕ) : ℝ) + 1) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ ((n - i : ℕ) : ℝ) + 1 by
        linarith [Nat.cast_nonneg (α := ℝ) (n - i)])]
    have hprod : (1 + Real.log ((i : ℝ) + 1)) * (1 + Real.log (((n - i : ℕ) : ℝ) + 1)) ≤
        (Real.log (n : ℝ) + 2) ^ 2 := by
      rw [sq]
      exact mul_le_mul h1 h2 hL2 (by positivity)
    have hsq : Real.sqrt ((1 + Real.log ((i : ℝ) + 1)) * (1 + Real.log (((n - i : ℕ) : ℝ) + 1))) ≤
        Real.log (n : ℝ) + 2 := by
      calc _ ≤ Real.sqrt ((Real.log (n : ℝ) + 2) ^ 2) := Real.sqrt_le_sqrt hprod
        _ = Real.log (n : ℝ) + 2 := Real.sqrt_sq (by positivity)
    rw [div_le_iff₀ hlog_pos]
    have hmul_eq : (1 + 2 / Real.log (n : ℝ)) * Real.log (n : ℝ) = Real.log (n : ℝ) + 2 := by
      field_simp [hlog_pos.ne']
    rw [hmul_eq]
    exact hsq
  have hW_abs_all : ∀ i ∈ range (n + 1), |W i - 1| ≤ 2 := by
    intro i hi
    have hnn : 0 ≤ W i := by dsimp [W]; positivity
    have hup := hW_upper i hi
    have h2div : 2 / Real.log (n : ℝ) ≤ 1 := by
      rw [div_le_one hlog_pos]; exact hlog_ge2
    rw [abs_le]
    constructor <;> linarith
  -- Partition `range (n + 1)` into `L = range K`, `M = Ico K (n + 1 - K)`, `R = Ico (n + 1 - K) (n + 1)`
  let K : ℕ := Nat.floor (δ * (n : ℝ)) + 1
  have hK_gt : δ * (n : ℝ) < (K : ℝ) := by
    dsimp [K]; push_cast; exact Nat.lt_floor_add_one _
  have hK_le_real : (K : ℝ) ≤ 2 * δ * (n : ℝ) := by
    have h1 : (Nat.floor (δ * (n : ℝ)) : ℝ) ≤ δ * (n : ℝ) := Nat.floor_le (by positivity)
    have h2 : (1 : ℝ) ≤ δ * (n : ℝ) := by
      have := (div_le_iff₀ hδpos).mp hnδ
      linarith
    dsimp [K]; push_cast; linarith
  have hK_le_half : K ≤ n / 2 := by
    have : (K : ℝ) ≤ (n : ℝ) / 4 := by nlinarith
    have hcast : 4 * K ≤ n := by
      have : (4 * K : ℝ) ≤ (n : ℝ) := by linarith
      exact_mod_cast this
    omega
  have hW_mid : ∀ i ∈ Ico K (n + 1 - K), |W i - 1| ≤ ε / 24 := by
    intro i hi
    rw [mem_Ico] at hi
    have hi_lo : δ * (n : ℝ) ≤ (i : ℝ) + 1 := by
      have : (K : ℝ) ≤ (i : ℝ) := Nat.cast_le.mpr hi.1
      linarith
    have hni_lo : δ * (n : ℝ) ≤ ((n - i : ℕ) : ℝ) + 1 := by
      have : K ≤ n - i := by omega
      have hcast : (K : ℝ) ≤ ((n - i : ℕ) : ℝ) := Nat.cast_le.mpr this
      linarith
    have hlog_lo1 : Real.log (n : ℝ) - |Real.log δ| ≤ 1 + Real.log ((i : ℝ) + 1) := by
      have h1 : Real.log (δ * (n : ℝ)) ≤ Real.log ((i : ℝ) + 1) :=
        Real.log_le_log (mul_pos hδpos hnpos) hi_lo
      rw [Real.log_mul hδpos.ne' hnpos.ne'] at h1
      have habs : -|Real.log δ| ≤ Real.log δ := neg_abs_le _
      linarith
    have hlog_lo2 : Real.log (n : ℝ) - |Real.log δ| ≤ 1 + Real.log (((n - i : ℕ) : ℝ) + 1) := by
      have h1 : Real.log (δ * (n : ℝ)) ≤ Real.log (((n - i : ℕ) : ℝ) + 1) :=
        Real.log_le_log (mul_pos hδpos hnpos) hni_lo
      rw [Real.log_mul hδpos.ne' hnpos.ne'] at h1
      have habs : -|Real.log δ| ≤ Real.log δ := neg_abs_le _
      linarith
    have hW_lo : 1 - (1 + |Real.log δ|) / Real.log (n : ℝ) ≤ W i := by
      dsimp [W]
      by_cases hsign : Real.log (n : ℝ) - (1 + |Real.log δ|) ≤ 0
      · have : 1 - (1 + |Real.log δ|) / Real.log (n : ℝ) ≤ 0 := by
          rw [sub_nonpos, le_div_iff₀ hlog_pos, one_mul]; linarith
        exact le_trans this (by positivity)
      · push Not at hsign
        have hsq : Real.log (n : ℝ) - |Real.log δ| ≤
            Real.sqrt ((1 + Real.log ((i : ℝ) + 1)) * (1 + Real.log (((n - i : ℕ) : ℝ) + 1))) := by
          have hnn : 0 ≤ Real.log (n : ℝ) - |Real.log δ| := by linarith
          calc Real.log (n : ℝ) - |Real.log δ|
              = Real.sqrt ((Real.log (n : ℝ) - |Real.log δ|) ^ 2) := (Real.sqrt_sq hnn).symm
            _ ≤ _ := Real.sqrt_le_sqrt (by rw [sq]; exact mul_le_mul hlog_lo1 hlog_lo2 hnn (by linarith))
        rw [le_div_iff₀ hlog_pos, sub_mul, one_mul, div_mul_cancel₀ _ hlog_pos.ne']
        linarith
    have hW_hi := hW_upper i (mem_range.mpr (by omega))
    have h2log : 2 / Real.log (n : ℝ) ≤ ε / 24 := by
      rw [div_le_iff₀ hlog_pos]
      have := (div_le_iff₀ hε).mp hlog_geE
      linarith
    rw [abs_le]
    constructor <;> linarith
  -- Bound the three parts of `∑ i ∈ range (n + 1), |(W i - 1) * B i|`
  have hB_nn : ∀ i, 0 ≤ B i := fun i => by dsimp [B]; positivity
  have hpart : ∑ i ∈ range (n + 1), |W i - 1| * B i =
      (∑ i ∈ Ico 0 K, |W i - 1| * B i) +
      (∑ i ∈ Ico K (n + 1 - K), |W i - 1| * B i) +
      (∑ i ∈ Ico (n + 1 - K) (n + 1), |W i - 1| * B i) := by
    rw [← Nat.Ico_zero_eq_range]
    have h1 := Finset.sum_Ico_consecutive (fun i => |W i - 1| * B i) (Nat.zero_le K) (by omega : K ≤ n + 1 - K)
    have h2 := Finset.sum_Ico_consecutive (fun i => |W i - 1| * B i) (Nat.zero_le (n + 1 - K)) (by omega : n + 1 - K ≤ n + 1)
    rw [← h2, ← h1]
  have hL_tail : ∑ i ∈ Ico 0 K, |W i - 1| * B i ≤ 8 * Real.sqrt (2 * δ) := by
    rw [Nat.Ico_zero_eq_range]
    calc ∑ i ∈ range K, |W i - 1| * B i
        ≤ ∑ i ∈ range K, 2 * B i := sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (hW_abs_all i (mem_range.mpr (by rw [mem_range] at hi; omega))) (hB_nn i)
      _ = 2 * ∑ i ∈ range K, B i := (mul_sum ..).symm
      _ ≤ 2 * (4 * Real.sqrt ((K : ℝ) / (n : ℝ))) :=
          mul_le_mul_of_nonneg_left (tail_beta_le (by omega) (by omega)) (by norm_num)
      _ ≤ 8 * Real.sqrt (2 * δ) := by
          have hKn : (K : ℝ) / (n : ℝ) ≤ 2 * δ := (div_le_iff₀ hnpos).mpr hK_le_real
          have hsq := Real.sqrt_le_sqrt hKn
          linarith
  have hR_tail : ∑ i ∈ Ico (n + 1 - K) (n + 1), |W i - 1| * B i ≤ 8 * Real.sqrt (2 * δ) := by
    have hbij : ∑ i ∈ Ico (n + 1 - K) (n + 1), B i = ∑ j ∈ range K, B j := by
      refine Finset.sum_bij (fun i _ => n - i) ?_ ?_ ?_ ?_
      · intro i hi; rw [mem_Ico] at hi; rw [mem_range]; omega
      · intro i₁ hi₁ i₂ hi₂ h; rw [mem_Ico] at hi₁ hi₂; omega
      · intro j hj; rw [mem_range] at hj; exact ⟨n - j, mem_Ico.mpr (by omega), by omega⟩
      · intro i hi
        rw [mem_Ico] at hi
        dsimp [B]
        rw [Nat.sub_sub_self (by omega : i ≤ n), mul_comm]
    calc ∑ i ∈ Ico (n + 1 - K) (n + 1), |W i - 1| * B i
        ≤ ∑ i ∈ Ico (n + 1 - K) (n + 1), 2 * B i := sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (hW_abs_all i (mem_range.mpr (by rw [mem_Ico] at hi; omega))) (hB_nn i)
      _ = 2 * ∑ i ∈ Ico (n + 1 - K) (n + 1), B i := (mul_sum ..).symm
      _ = 2 * ∑ j ∈ range K, B j := by rw [hbij]
      _ ≤ 2 * (4 * Real.sqrt ((K : ℝ) / (n : ℝ))) :=
          mul_le_mul_of_nonneg_left (tail_beta_le (by omega) (by omega)) (by norm_num)
      _ ≤ 8 * Real.sqrt (2 * δ) := by
          have hKn : (K : ℝ) / (n : ℝ) ≤ 2 * δ := (div_le_iff₀ hnpos).mpr hK_le_real
          have hsq := Real.sqrt_le_sqrt hKn
          linarith
  have hM_part : ∑ i ∈ Ico K (n + 1 - K), |W i - 1| * B i ≤ (ε / 24) * 4 := by
    calc ∑ i ∈ Ico K (n + 1 - K), |W i - 1| * B i
        ≤ ∑ i ∈ Ico K (n + 1 - K), (ε / 24) * B i := sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (hW_mid i hi) (hB_nn i)
      _ = (ε / 24) * ∑ i ∈ Ico K (n + 1 - K), B i := (mul_sum ..).symm
      _ ≤ (ε / 24) * betaSum n := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => mem_range.mpr (by rw [mem_Ico] at hi; omega))
            (fun i _ _ => hB_nn i)
      _ ≤ (ε / 24) * 4 := mul_le_mul_of_nonneg_left hbeta_le4 (by positivity)
  have hdiff_bound : |sumConv q q n / Real.log (n : ℝ) - betaSum n| ≤
      16 * Real.sqrt (2 * δ) + ε / 6 := by
    rw [hdiff_eq]
    calc |∑ i ∈ range (n + 1), (W i - 1) * B i|
        ≤ ∑ i ∈ range (n + 1), |(W i - 1) * B i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ range (n + 1), |W i - 1| * B i := sum_congr rfl fun i _ => by
          rw [abs_mul, abs_of_nonneg (hB_nn i)]
      _ ≤ 8 * Real.sqrt (2 * δ) + (ε / 24) * 4 + 8 * Real.sqrt (2 * δ) := by
          rw [hpart]; linarith [hL_tail, hM_part, hR_tail]
      _ = 16 * Real.sqrt (2 * δ) + ε / 6 := by ring
  rw [Real.dist_eq]
  have htri : |sumConv q q n / Real.log (n : ℝ) - Real.pi| ≤
      |sumConv q q n / Real.log (n : ℝ) - betaSum n| + |betaSum n - Real.pi| := by
    have := abs_add_le (sumConv q q n / Real.log (n : ℝ) - betaSum n) (betaSum n - Real.pi)
    simpa [sub_add_sub_cancel] using this
  linarith

end OMA.P_Erdos66_R1_H1

open AdditiveCombinatorics Filter
open scoped Topology

theorem OMA.solution : OMA.R_Erdos66_erdos_66_R1.H1 := by
  intro a ha
  let q : ℕ → ℝ := fun i ↦ Real.sqrt ((1 + Real.log ((i : ℝ) + 1)) / ((i : ℝ) + 1))
  let p : ℕ → ℝ := fun i ↦ a * q i
  refine ⟨?_, ?_, Real.pi * a ^ 2, by positivity, ?_⟩
  · intro i j hij
    dsimp [p, q]
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) ha.le
    exact OMA.P_Erdos66_R1_H1.one_add_log_div_antitone
      (by linarith [Nat.cast_nonneg (α := ℝ) i]) (by exact_mod_cast Nat.add_le_add_right hij 1)
  · intro i
    dsimp [p, q]
    positivity
  · have hscale : (fun n : ℕ ↦ sumConv p p n / Real.log n) =
        (fun n : ℕ ↦ a ^ 2 * (sumConv q q n / Real.log n)) := by
      ext n
      rw [sumConv, sumConv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← mul_div_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => by dsimp [p]; ring
    rw [hscale, mul_comm Real.pi (a ^ 2)]
    exact OMA.P_Erdos66_R1_H1.tendsto_unit_conv.const_mul (a ^ 2)
