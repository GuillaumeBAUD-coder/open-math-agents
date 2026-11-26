import FormalConjectures.ErdosProblems.«1129»

/-! The Lebesgue constant of three nodes is minimized by equal gaps. -/

open Erdos1129

lemma OMA.three_coordinates (x : Fin 3 → ℝ) : x = ![x 0, x 1, x 2] := by
  funext i
  fin_cases i <;> rfl

lemma OMA.three_lebesgue (a b c t : ℝ) :
    lebesgueFunction ![a, b, c] t =
      |(t - b) * (t - c) / ((a - b) * (a - c))| +
      |(t - a) * (t - c) / ((b - a) * (b - c))| +
      |(t - a) * (t - b) / ((c - a) * (c - b))| := by
  rw [lebesgueFunction_eq, Fin.sum_univ_three]
  have h₀ : (Finset.univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide
  have h₁ : (Finset.univ : Finset (Fin 3)).erase 1 = {0, 2} := by decide
  have h₂ : (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} := by decide
  rw [h₀, h₁, h₂, Finset.prod_pair (by decide : (1 : Fin 3) ≠ 2),
    Finset.prod_pair (by decide : (0 : Fin 3) ≠ 2),
    Finset.prod_pair (by decide : (0 : Fin 3) ≠ 1)]
  simp only [div_mul_div_comm]
  rfl

lemma OMA.le_of_mem_interval (x : Fin 3 → ℝ) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    lebesgueFunction x t ≤ lebesgueConstant x := by
  have hc : Continuous (lebesgueFunction x) := by
    unfold lebesgueFunction
    fun_prop
  exact le_csSup (isCompact_Icc.image hc).bddAbove ⟨t, ht, rfl⟩

lemma OMA.left_gap (a b c : ℝ) (hab : a < b) (hbc : b < c) :
    1 + (b - a) ^ 2 / (2 * ((b - a) + (c - b)) * (c - b)) ≤
      lebesgueFunction ![a, b, c] ((a + b) / 2) := by
  let t := (a + b) / 2
  let A := (t - b) * (t - c) / ((a - b) * (a - c))
  let B := (t - a) * (t - c) / ((b - a) * (b - c))
  let C := (t - a) * (t - b) / ((c - a) * (c - b))
  have hden : (b - a) + (c - b) ≠ 0 := by linarith
  have hac := hab.trans hbc
  rw [OMA.three_lebesgue]
  change _ ≤ |A| + |B| + |C|
  calc
    1 + (b - a) ^ 2 / (2 * ((b - a) + (c - b)) * (c - b)) = A + B - C := by
      dsimp [A, B, C, t]
      field_simp [hden, sub_ne_zero.mpr hab.ne, sub_ne_zero.mpr hab.ne',
        sub_ne_zero.mpr hbc.ne, sub_ne_zero.mpr hbc.ne',
        sub_ne_zero.mpr hac.ne, sub_ne_zero.mpr hac.ne']
      ring
    _ ≤ |A| + |B| + |C| := by linarith [le_abs_self A, le_abs_self B, neg_le_abs C]

lemma OMA.right_gap (a b c : ℝ) (hab : a < b) (hbc : b < c) :
    1 + (c - b) ^ 2 / (2 * ((c - b) + (b - a)) * (b - a)) ≤
      lebesgueFunction ![a, b, c] ((b + c) / 2) := by
  let t := (b + c) / 2
  let A := (t - b) * (t - c) / ((a - b) * (a - c))
  let B := (t - a) * (t - c) / ((b - a) * (b - c))
  let C := (t - a) * (t - b) / ((c - a) * (c - b))
  have hden : (c - b) + (b - a) ≠ 0 := by linarith
  have hac := hab.trans hbc
  rw [OMA.three_lebesgue]
  change _ ≤ |A| + |B| + |C|
  calc
    1 + (c - b) ^ 2 / (2 * ((c - b) + (b - a)) * (b - a)) = -A + B + C := by
      dsimp [A, B, C, t]
      field_simp [hden, sub_ne_zero.mpr hab.ne, sub_ne_zero.mpr hab.ne',
        sub_ne_zero.mpr hbc.ne, sub_ne_zero.mpr hbc.ne',
        sub_ne_zero.mpr hac.ne, sub_ne_zero.mpr hac.ne']
      ring
    _ ≤ |A| + |B| + |C| := by linarith [neg_le_abs A, le_abs_self B, le_abs_self C]

lemma OMA.gap_difference (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    1 + u ^ 2 / (2 * (u + v) * v) - 5 / 4 =
      (u - v) * (2 * u + v) / (4 * (u + v) * v) := by
  field_simp [ne_of_gt hv, ne_of_gt (add_pos hu hv)]
  ring

lemma OMA.gap_ge (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) :
    5 / 4 ≤ 1 + u ^ 2 / (2 * (u + v) * v) := by
  have h : 0 ≤ (u - v) * (2 * u + v) / (4 * (u + v) * v) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hvu) (by positivity)) (by positivity)
  linarith [OMA.gap_difference u v hu hv]

lemma OMA.gap_le_imp (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hbound : 1 + u ^ 2 / (2 * (u + v) * v) ≤ 5 / 4) : u ≤ v := by
  by_contra! hvu
  have h : 0 < (u - v) * (2 * u + v) / (4 * (u + v) * v) :=
    div_pos (mul_pos (sub_pos.mpr hvu) (by positivity)) (by positivity)
  linarith [OMA.gap_difference u v hu hv]

lemma OMA.gap_bounds (x : Fin 3 → ℝ) (hx : IsNodeSet x) :
    (1 + (x 1 - x 0) ^ 2 / (2 * ((x 1 - x 0) + (x 2 - x 1)) * (x 2 - x 1)) ≤ lebesgueConstant x) ∧
    (1 + (x 2 - x 1) ^ 2 / (2 * ((x 2 - x 1) + (x 1 - x 0)) * (x 1 - x 0)) ≤ lebesgueConstant x) := by
  have hleft : x 0 < x 1 := hx.1 (by decide)
  have hright : x 1 < x 2 := hx.1 (by decide)
  have hm₁ : (x 0 + x 1) / 2 ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [(hx.2 0).1, (hx.2 1).1], by linarith [(hx.2 0).2, (hx.2 1).2]⟩
  have hm₂ : (x 1 + x 2) / 2 ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [(hx.2 1).1, (hx.2 2).1], by linarith [(hx.2 1).2, (hx.2 2).2]⟩
  constructor
  · refine le_trans ?_ (OMA.le_of_mem_interval x hm₁)
    simpa only [← OMA.three_coordinates x] using OMA.left_gap (x 0) (x 1) (x 2) hleft hright
  · refine le_trans ?_ (OMA.le_of_mem_interval x hm₂)
    simpa only [← OMA.three_coordinates x] using OMA.right_gap (x 0) (x 1) (x 2) hleft hright

lemma OMA.center_formula (t : ℝ) :
    lebesgueFunction (![(-1 : ℝ), 0, 1] : Fin 3 → ℝ) t =
      |t * (t - 1) / 2| + |1 - t ^ 2| + |t * (t + 1) / 2| := by
  rw [OMA.three_lebesgue]
  have h₀ : (t - 0) * (t - 1) / (((-1 : ℝ) - 0) * (-1 - 1)) = t * (t - 1) / 2 := by ring
  have h₁ : (t - (-1)) * (t - 1) / (((0 : ℝ) - (-1)) * (0 - 1)) = 1 - t ^ 2 := by ring
  have h₂ : (t - (-1)) * (t - 0) / (((1 : ℝ) - (-1)) * (1 - 0)) = t * (t + 1) / 2 := by ring
  rw [h₀, h₁, h₂]

lemma OMA.center_const :
    lebesgueConstant (![(-1 : ℝ), 0, 1] : Fin 3 → ℝ) = 5 / 4 := by
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, 0, by norm_num, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      have hlo : -1 ≤ t := ht.1
      have hhi : t ≤ 1 := ht.2
      have hb : 0 ≤ 1 - t ^ 2 := by
        nlinarith [mul_nonneg (show 0 ≤ 1 - t by linarith) (show 0 ≤ 1 + t by linarith)]
      rw [OMA.center_formula, abs_of_nonneg hb]
      by_cases h : t ≤ 0
      · have ha : 0 ≤ t * (t - 1) / 2 :=
          div_nonneg (mul_nonneg_of_nonpos_of_nonpos h (by linarith)) (by norm_num)
        have hc : t * (t + 1) / 2 ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h (by linarith)) (by norm_num)
        rw [abs_of_nonneg ha, abs_of_nonpos hc]
        nlinarith [sq_nonneg (t + 1 / 2)]
      · have ha : t * (t - 1) / 2 ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
            (by norm_num)
        have hc : 0 ≤ t * (t + 1) / 2 :=
          div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
        rw [abs_of_nonpos ha, abs_of_nonneg hc]
        nlinarith [sq_nonneg (t - 1 / 2)]
  · calc
      5 / 4 = lebesgueFunction (![(-1 : ℝ), 0, 1] : Fin 3 → ℝ) (1 / 2) := by
        rw [OMA.center_formula]
        norm_num
      _ ≤ _ := OMA.le_of_mem_interval _ (by norm_num)

lemma OMA.center_canonical : IsCanonical (![(-1 : ℝ), 0, 1] : Fin 3 → ℝ) := by
  refine ⟨⟨?_, ?_⟩, ⟨0, rfl⟩, ⟨2, rfl⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  · intro i
    fin_cases i <;> norm_num

theorem OMA.solution : type_of% @Erdos1129.erdos_1129.variants.three_nodes := by
  refine ⟨?_, OMA.center_const⟩
  ext x
  change (IsCanonical x ∧ IsMinimiser x) ↔ x ∈ ({![(-1 : ℝ), 0, 1]} : Set (Fin 3 → ℝ))
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hmin⟩
    have hA : x 0 = -1 := by
      obtain ⟨i, hi⟩ := hx.2.1
      refine le_antisymm ?_ (hx.1.2 0).1
      rw [← hi]
      exact hx.1.1.monotone (Fin.zero_le i)
    have hC : x 2 = 1 := by
      obtain ⟨i, hi⟩ := hx.2.2
      refine le_antisymm (hx.1.2 2).2 ?_
      rw [← hi]
      exact hx.1.1.monotone (by fin_cases i <;> decide)
    have hle : lebesgueConstant x ≤ 5 / 4 := by
      rw [← OMA.center_const]
      exact hmin.2 _ OMA.center_canonical.1
    obtain ⟨hl, hr⟩ := OMA.gap_bounds x hx.1
    have hu : 0 < x 1 - x 0 := sub_pos.mpr (hx.1.1 (by decide))
    have hv : 0 < x 2 - x 1 := sub_pos.mpr (hx.1.1 (by decide))
    have huv := OMA.gap_le_imp _ _ hu hv (hl.trans hle)
    have hvu := OMA.gap_le_imp _ _ hv hu (hr.trans hle)
    have hB : x 1 = 0 := by linarith
    calc
      x = ![x 0, x 1, x 2] := OMA.three_coordinates x
      _ = _ := by rw [hA, hB, hC]
  · rintro rfl
    refine ⟨OMA.center_canonical, OMA.center_canonical.1, ?_⟩
    intro y hy
    obtain ⟨hl, hr⟩ := OMA.gap_bounds y hy
    have hu : 0 < y 1 - y 0 := sub_pos.mpr (hy.1 (by decide))
    have hv : 0 < y 2 - y 1 := sub_pos.mpr (hy.1 (by decide))
    rw [OMA.center_const]
    rcases le_total (y 1 - y 0) (y 2 - y 1) with h | h
    · exact (OMA.gap_ge _ _ hv hu h).trans hr
    · exact (OMA.gap_ge _ _ hu hv h).trans hl