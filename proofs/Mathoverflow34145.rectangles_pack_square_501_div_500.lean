import FormalConjectures.Mathoverflow.«34145»

/-!
# Packing 1/k by 1/(k+1) rectangles into a 501/500 square

Explicit guillotine packing with NFDH tails for Mathoverflow 34145.
-/

open Mathoverflow34145

namespace OMA_MO34145

/-- Closed axis-aligned box `[x0, x1] × [y0, y1]`. -/
def boxSet (x0 y0 x1 y1 : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc x0 x1 ×ˢ Set.Icc y0 y1

/-- Open axis-aligned box `(x0, x1) × (y0, y1)`. -/
def boxInt (x0 y0 x1 y1 : ℝ) : Set (ℝ × ℝ) :=
  Set.Ioo x0 x1 ×ˢ Set.Ioo y0 y1

lemma interior_boxSet (x0 y0 x1 y1 : ℝ) :
    interior (boxSet x0 y0 x1 y1) = boxInt x0 y0 x1 y1 := by
  rw [boxSet, boxInt, interior_prod_eq, interior_Icc, interior_Icc]

lemma boxSet_mono {x0 y0 x1 y1 x0' y0' x1' y1' : ℝ}
    (hx0 : x0' ≤ x0) (hy0 : y0' ≤ y0) (hx1 : x1 ≤ x1') (hy1 : y1 ≤ y1') :
    boxSet x0 y0 x1 y1 ⊆ boxSet x0' y0' x1' y1' := by
  rintro ⟨x, y⟩ ⟨⟨hx_lo, hx_hi⟩, ⟨hy_lo, hy_hi⟩⟩
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

lemma boxInt_disjoint_of_x_le {x0 y0 x1 y1 x0' y0' x1' y1' : ℝ} (h : x1 ≤ x0') :
    boxInt x0 y0 x1 y1 ∩ boxInt x0' y0' x1' y1' = ∅ := by
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, boxInt, Set.mem_prod, Set.mem_Ioo, Set.mem_empty_iff_false,
    iff_false]
  rintro ⟨⟨⟨hx1, hx2⟩, _⟩, ⟨⟨hx3, hx4⟩, _⟩⟩
  linarith

lemma boxInt_disjoint_of_y_le {x0 y0 x1 y1 x0' y0' x1' y1' : ℝ} (h : y1 ≤ y0') :
    boxInt x0 y0 x1 y1 ∩ boxInt x0' y0' x1' y1' = ∅ := by
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, boxInt, Set.mem_prod, Set.mem_Ioo, Set.mem_empty_iff_false,
    iff_false]
  rintro ⟨⟨_, ⟨hy1, hy2⟩⟩, ⟨_, ⟨hy3, hy4⟩⟩⟩
  linarith

lemma boxInt_translate_disjoint {x0 y0 a0 b0 a1 b1 c0 d0 c1 d1 : ℝ}
    (h : boxInt a0 b0 a1 b1 ∩ boxInt c0 d0 c1 d1 = ∅) :
    boxInt (x0 + a0) (y0 + b0) (x0 + a1) (y0 + b1) ∩
    boxInt (x0 + c0) (y0 + d0) (x0 + c1) (y0 + d1) = ∅ := by
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, boxInt, Set.mem_prod, Set.mem_Ioo, Set.mem_empty_iff_false,
    iff_false]
  rintro ⟨⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩, ⟨⟨hx3, hx4⟩, ⟨hy3, hy4⟩⟩⟩
  have hmem : (x - x0, y - y0) ∈ boxInt a0 b0 a1 b1 ∩ boxInt c0 d0 c1 d1 :=
    ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩,
     ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩⟩
  rw [h] at hmem
  exact hmem

lemma boxInt_swap_translate_disjoint {x0 y0 a0 b0 a1 b1 c0 d0 c1 d1 : ℝ}
    (h : boxInt a0 b0 a1 b1 ∩ boxInt c0 d0 c1 d1 = ∅) :
    boxInt (x0 + b0) (y0 + a0) (x0 + b1) (y0 + a1) ∩
    boxInt (x0 + d0) (y0 + c0) (x0 + d1) (y0 + c1) = ∅ := by
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, boxInt, Set.mem_prod, Set.mem_Ioo, Set.mem_empty_iff_false,
    iff_false]
  rintro ⟨⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩, ⟨⟨hx3, hx4⟩, ⟨hy3, hy4⟩⟩⟩
  have hmem : (y - y0, x - x0) ∈ boxInt a0 b0 a1 b1 ∩ boxInt c0 d0 c1 d1 :=
    ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩,
     ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩⟩
  rw [h] at hmem
  exact hmem

lemma rect0_toSet {w h x y : ℝ} (hw : 0 ≤ w) (hh : 0 ≤ h) :
    Rectangle.toSet ⟨w, h, (x, y), 0⟩ = boxSet x y (x + w) (y + h) := by
  ext ⟨px, py⟩
  simp only [Rectangle.toSet, rigidMotion, scale, unitSquare, Set.mem_image, Set.mem_ofPred_eq,
    Real.Angle.cos_zero, Real.Angle.sin_zero, mul_one, mul_zero, sub_zero, add_zero, Prod.exists,
    Prod.mk.injEq, boxSet, Set.mem_prod, Set.mem_Icc]
  constructor
  · rintro ⟨qx, qy, ⟨ux, uy, ⟨hu1, hu2, hu3, hu4⟩, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
  · rintro ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    refine ⟨px - x, py - y, ⟨if w = 0 then 0 else (px - x) / w, if h = 0 then 0 else (py - y) / h,
      ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩, by ring, by ring⟩
    · split_ifs with hw0 <;> [norm_num; exact div_nonneg (by linarith) hw]
    · split_ifs with hw0
      · norm_num
      · exact (div_le_one (lt_of_le_of_ne hw (Ne.symm hw0))).2 (by linarith)
    · split_ifs with hh0 <;> [norm_num; exact div_nonneg (by linarith) hh]
    · split_ifs with hh0
      · norm_num
      · exact (div_le_one (lt_of_le_of_ne hh (Ne.symm hh0))).2 (by linarith)
    · split_ifs with hw0
      · subst hw0; simp; linarith
      · exact mul_div_cancel₀ _ hw0
    · split_ifs with hh0
      · subst hh0; simp; linarith
      · exact mul_div_cancel₀ _ hh0

lemma rect90_toSet {w h x y : ℝ} (hw : 0 ≤ w) (hh : 0 ≤ h) :
    Rectangle.toSet ⟨w, h, (x + h, y), (Real.pi / 2 : ℝ)⟩ = boxSet x y (x + h) (y + w) := by
  ext ⟨px, py⟩
  simp only [Rectangle.toSet, rigidMotion, scale, unitSquare, Set.mem_image, Set.mem_ofPred_eq,
    Real.Angle.cos_coe, Real.Angle.sin_coe, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero,
    mul_one, add_zero, Prod.exists, Prod.mk.injEq, boxSet, Set.mem_prod, Set.mem_Icc]
  constructor
  · rintro ⟨qx, qy, ⟨ux, uy, ⟨hu1, hu2, hu3, hu4⟩, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
  · rintro ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    refine ⟨py - y, x + h - px, ⟨if w = 0 then 0 else (py - y) / w,
      if h = 0 then 0 else (x + h - px) / h, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩, by ring, by ring⟩
    · split_ifs with hw0 <;> [norm_num; exact div_nonneg (by linarith) hw]
    · split_ifs with hw0
      · norm_num
      · exact (div_le_one (lt_of_le_of_ne hw (Ne.symm hw0))).2 (by linarith)
    · split_ifs with hh0 <;> [norm_num; exact div_nonneg (by linarith) hh]
    · split_ifs with hh0
      · norm_num
      · exact (div_le_one (lt_of_le_of_ne hh (Ne.symm hh0))).2 (by linarith)
    · split_ifs with hw0
      · subst hw0; simp; linarith
      · exact mul_div_cancel₀ _ hw0
    · split_ifs with hh0
      · subst hh0; simp; linarith
      · exact mul_div_cancel₀ _ hh0

/- ## Section 2: Closed-form NFDH lemma -/

lemma harmonic_dyadic_ge (m j : ℕ) (hm : 0 < m) :
    (1 / 2 : ℝ) ≤ ∑ k ∈ Finset.Ico (2 ^ j * m) (2 ^ (j + 1) * m), (1 : ℝ) / (k + 1) := by
  have hle : 2 ^ j * m ≤ 2 ^ (j + 1) * m := by
    rw [pow_succ']
    nlinarith [Nat.one_le_two_pow (n := j)]
  have hterm : ∀ k ∈ Finset.Ico (2 ^ j * m) (2 ^ (j + 1) * m),
      (1 : ℝ) / (2 ^ (j + 1) * m : ℝ) ≤ (1 : ℝ) / (k + 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast hk.2
  calc
    (1 / 2 : ℝ) = (2 ^ j * m : ℝ) * ((1 : ℝ) / (2 ^ (j + 1) * m : ℝ)) := by
      have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
      have hp0 : (2 : ℝ) ^ j ≠ 0 := by positivity
      rw [pow_succ']
      field_simp
    _ = ∑ _k ∈ Finset.Ico (2 ^ j * m) (2 ^ (j + 1) * m), (1 : ℝ) / (2 ^ (j + 1) * m : ℝ) := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have hsub : 2 ^ (j + 1) * m - 2 ^ j * m = 2 ^ j * m := by
        rw [pow_succ', mul_assoc, two_mul]
        exact Nat.add_sub_cancel _ _
      rw [hsub]
      push_cast
      rfl
    _ ≤ ∑ k ∈ Finset.Ico (2 ^ j * m) (2 ^ (j + 1) * m), (1 : ℝ) / (k + 1) :=
      Finset.sum_le_sum hterm

lemma harmonic_ge_half_mul (m M : ℕ) (hm : 0 < m) :
    (M : ℝ) / 2 ≤ ∑ k ∈ Finset.Ico m (2 ^ M * m), (1 : ℝ) / (k + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h1 : m ≤ 2 ^ M * m := Nat.le_mul_of_pos_left m (by positivity)
    have h2 : 2 ^ M * m ≤ 2 ^ (M + 1) * m := by
      rw [pow_succ']
      nlinarith
    rw [← Finset.sum_Ico_consecutive _ h1 h2]
    have hdy := harmonic_dyadic_ge m M hm
    push_cast
    linarith

lemma h_exceed (W : ℝ) (m : ℕ) (hm : 0 < m) :
    ∃ t > m, W < ∑ k ∈ Finset.Ico m t, (1 : ℝ) / (k + 1) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (max (2 * W) 1)
  have hM1 : 1 < M := by
    have : (1 : ℝ) < M := lt_of_le_of_lt (le_max_right _ _) hM
    exact_mod_cast this
  have hMW : 2 * W < M := lt_of_le_of_lt (le_max_left _ _) hM
  refine ⟨2 ^ M * m, ?_, ?_⟩
  · have hpow : 1 < 2 ^ M := one_lt_pow₀ (by norm_num) (by omega)
    nlinarith
  · calc
      W < (M : ℝ) / 2 := by linarith
      _ ≤ ∑ k ∈ Finset.Ico m (2 ^ M * m), (1 : ℝ) / (k + 1) := harmonic_ge_half_mul m M hm

noncomputable def nextShelf (W : ℝ) (m : ℕ) (hm : 0 < m) (hmW : (1 : ℝ) / m < W) :
    { t : ℕ // m < t ∧ (∑ k ∈ Finset.Ico m t, (1 : ℝ) / (k + 1)) ≤ W ∧
      W < ∑ k ∈ Finset.Ico m (t + 1), (1 : ℝ) / (k + 1) } := by
  classical
  let t0 := Nat.find (h_exceed W m hm)
  have ht0_gt : m < t0 := (Nat.find_spec (h_exceed W m hm)).1
  have ht0_sum : W < ∑ k ∈ Finset.Ico m t0, (1 : ℝ) / (k + 1) :=
    (Nat.find_spec (h_exceed W m hm)).2
  have ht0_ne : t0 ≠ m + 1 := by
    intro heq
    rw [heq] at ht0_sum
    simp only [Nat.Ico_succ_singleton, Finset.sum_singleton] at ht0_sum
    have h1 : (1 : ℝ) / (m + 1) ≤ (1 : ℝ) / m :=
      one_div_le_one_div_of_le (by exact_mod_cast hm) (by linarith)
    linarith
  have hm_lt_pred : m < t0 - 1 := by omega
  have hpred_add : t0 - 1 + 1 = t0 := by omega
  refine ⟨t0 - 1, hm_lt_pred, ?_, ?_⟩
  · by_contra hnot
    push Not at hnot
    have hmin := Nat.find_min (h_exceed W m hm) (show t0 - 1 < t0 by omega)
    exact hmin ⟨hm_lt_pred, hnot⟩
  · rw [hpred_add]
    exact ht0_sum

noncomputable def shelfStart (W : ℝ) (a : ℕ) (ha : 0 < a) (haW : (1 : ℝ) / a < W) :
    ℕ → { m : ℕ // 0 < m ∧ (1 : ℝ) / m < W }
  | 0 => ⟨a, ha, haW⟩
  | r + 1 =>
    let prev := shelfStart W a ha haW r
    let nx := nextShelf W prev.1 prev.2.1 prev.2.2
    ⟨nx.1, lt_trans prev.2.1 nx.2.1,
      lt_trans (one_div_lt_one_div_of_lt (by exact_mod_cast prev.2.1) (by exact_mod_cast nx.2.1))
        prev.2.2⟩

lemma shelfStart_zero (W : ℝ) (a : ℕ) (ha : 0 < a) (haW : (1 : ℝ) / a < W) :
    (shelfStart W a ha haW 0).1 = a := rfl

lemma shelfStart_lt_succ (W : ℝ) (a : ℕ) (ha : 0 < a) (haW : (1 : ℝ) / a < W) (r : ℕ) :
    (shelfStart W a ha haW r).1 < (shelfStart W a ha haW (r + 1)).1 :=
  (nextShelf W (shelfStart W a ha haW r).1 (shelfStart W a ha haW r).2.1
    (shelfStart W a ha haW r).2.2).2.1

lemma shelfStart_strictMono (W : ℝ) (a : ℕ) (ha : 0 < a) (haW : (1 : ℝ) / a < W) :
    StrictMono (fun r => (shelfStart W a ha haW r).1) :=
  strictMono_nat_of_lt_succ (shelfStart_lt_succ W a ha haW)

lemma shelfStart_ge_add (W : ℝ) (a : ℕ) (ha : 0 < a) (haW : (1 : ℝ) / a < W) (r : ℕ) :
    a + r ≤ (shelfStart W a ha haW r).1 := by
  induction r with
  | zero => simp [shelfStart_zero]
  | succ r ih =>
    have := shelfStart_lt_succ W a ha haW r
    omega

lemma shelfStart_sum_le (W : ℝ) (a : ℕ) (ha : 0 < a) (haW : (1 : ℝ) / a < W) (r : ℕ) :
    ∑ k ∈ Finset.Ico (shelfStart W a ha haW r).1 (shelfStart W a ha haW (r + 1)).1,
      (1 : ℝ) / (k + 1) ≤ W :=
  (nextShelf W (shelfStart W a ha haW r).1 (shelfStart W a ha haW r).2.1
    (shelfStart W a ha haW r).2.2).2.2.1

lemma shelfStart_sum_gt (W : ℝ) (a : ℕ) (ha : 0 < a) (haW : (1 : ℝ) / a < W) (r : ℕ) :
    W - (1 : ℝ) / a <
      ∑ k ∈ Finset.Ico (shelfStart W a ha haW r).1 (shelfStart W a ha haW (r + 1)).1,
        (1 : ℝ) / (k + 1) := by
  let prev := shelfStart W a ha haW r
  let nx := nextShelf W prev.1 prev.2.1 prev.2.2
  have hgt : W < ∑ k ∈ Finset.Ico prev.1 (nx.1 + 1), (1 : ℝ) / (k + 1) := nx.2.2.2
  have hle_succ : prev.1 ≤ nx.1 := nx.2.1.le
  rw [Finset.sum_Ico_succ_top hle_succ] at hgt
  have ha_le : a ≤ nx.1 + 1 := by
    have := shelfStart_ge_add W a ha haW r
    change a + r ≤ prev.1 at this
    omega
  have hdiv : (1 : ℝ) / (nx.1 + 1) ≤ (1 : ℝ) / a :=
    one_div_le_one_div_of_le (by exact_mod_cast ha) (by exact_mod_cast ha_le)
  change W - (1 : ℝ) / a < ∑ k ∈ Finset.Ico prev.1 nx.1, (1 : ℝ) / (k + 1)
  linarith

lemma telescoping_inv_Ico (m t : ℕ) (hm : 0 < m) (hmt : m ≤ t) :
    (1 : ℝ) / m - (1 : ℝ) / t =
      ∑ k ∈ Finset.Ico m t, (1 : ℝ) / ((k : ℝ) * (k + 1)) := by
  induction t, hmt using Nat.le_induction with
  | base => simp
  | succ t hmt ih =>
    rw [Finset.sum_Ico_succ_top hmt, ← ih]
    have ht0 : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have ht1 : (t : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma shelfStart_step_bound (W : ℝ) (a : ℕ) (ha : 0 < a) (haW : (1 : ℝ) / a < W) (r : ℕ) :
    (1 : ℝ) / (shelfStart W a ha haW (r + 1)).1 ≤
      ((1 : ℝ) / (shelfStart W a ha haW r).1 - (1 : ℝ) / (shelfStart W a ha haW (r + 1)).1) /
        (W - (1 : ℝ) / a) := by
  let sr := (shelfStart W a ha haW r).1
  let sr1 := (shelfStart W a ha haW (r + 1)).1
  have hsr_pos : 0 < sr := (shelfStart W a ha haW r).2.1
  have hlt : sr < sr1 := shelfStart_lt_succ W a ha haW r
  have hW : 0 < W - (1 : ℝ) / a := sub_pos.mpr haW
  rw [le_div_iff₀ hW]
  have htel := telescoping_inv_Ico sr sr1 hsr_pos hlt.le
  have hsum_gt := shelfStart_sum_gt W a ha haW r
  have hmul : (1 : ℝ) / sr1 * (W - (1 : ℝ) / a) ≤
      (1 : ℝ) / sr1 * ∑ k ∈ Finset.Ico sr sr1, (1 : ℝ) / (k + 1) :=
    mul_le_mul_of_nonneg_left hsum_gt.le (by positivity)
  rw [Finset.mul_sum] at hmul
  have hterm : ∑ k ∈ Finset.Ico sr sr1, (1 : ℝ) / sr1 * ((1 : ℝ) / (k + 1)) ≤
      ∑ k ∈ Finset.Ico sr sr1, (1 : ℝ) / ((k : ℝ) * (k + 1)) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast lt_of_lt_of_le hsr_pos hk.1
    have hks : (k : ℝ) ≤ sr1 := by exact_mod_cast hk.2.le
    have h1 : (1 : ℝ) / sr1 ≤ (1 : ℝ) / k := one_div_le_one_div_of_le hk_pos hks
    calc
      (1 : ℝ) / sr1 * ((1 : ℝ) / (k + 1)) ≤ (1 : ℝ) / k * ((1 : ℝ) / (k + 1)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (1 : ℝ) / ((k : ℝ) * (k + 1)) := by rw [one_div_mul_one_div]
  linarith

lemma shelfStart_sum_inv_le (W : ℝ) (a : ℕ) (ha : 0 < a) (haW : (1 : ℝ) / a < W) (R : ℕ) :
    ∑ j ∈ Finset.range (R + 1), (1 : ℝ) / (shelfStart W a ha haW j).1 ≤
      (1 : ℝ) / a + ((1 : ℝ) / a - (1 : ℝ) / (shelfStart W a ha haW R).1) / (W - (1 : ℝ) / a) := by
  induction R with
  | zero =>
    simp [shelfStart_zero]
  | succ R ih =>
    rw [Finset.sum_range_succ]
    have hstep := shelfStart_step_bound W a ha haW R
    have hW : 0 < W - (1 : ℝ) / a := sub_pos.mpr haW
    calc
      ∑ j ∈ Finset.range (R + 1), (1 : ℝ) / (shelfStart W a ha haW j).1 +
          (1 : ℝ) / (shelfStart W a ha haW (R + 1)).1
        ≤ ((1 : ℝ) / a +
            ((1 : ℝ) / a - (1 : ℝ) / (shelfStart W a ha haW R).1) / (W - (1 : ℝ) / a)) +
          ((1 : ℝ) / (shelfStart W a ha haW R).1 -
            (1 : ℝ) / (shelfStart W a ha haW (R + 1)).1) / (W - (1 : ℝ) / a) :=
          add_le_add ih hstep
      _ = (1 : ℝ) / a +
          ((1 : ℝ) / a - (1 : ℝ) / (shelfStart W a ha haW (R + 1)).1) / (W - (1 : ℝ) / a) := by
          ring

def optbLt (k : ℕ) : Option ℕ → Prop
  | none => True
  | some b => k < b

def nfdhBound (W H : ℝ) (a : ℕ) : Option ℕ → Prop
  | none => (1 : ℝ) / a + ((1 : ℝ) / a) / (W - (1 : ℝ) / a) ≤ H
  | some b => a < b ∧ (1 : ℝ) / a + ((1 : ℝ) / a - (1 : ℝ) / b) / (W - (1 : ℝ) / a) ≤ H

lemma nfdh_pack_box (W H : ℝ) (a : ℕ) (optb : Option ℕ)
    (ha : 0 < a) (haW : (1 : ℝ) / a < W) (_haH : (1 : ℝ) / a ≤ H)
    (hbound : nfdhBound W H a optb) :
    ∃ rx ry : ℕ → ℝ, ∀ k, a ≤ k → optbLt k optb →
      0 ≤ rx k ∧ rx k + (1 : ℝ) / (k + 1) ≤ W ∧
      0 ≤ ry k ∧ ry k + (1 : ℝ) / k ≤ H ∧
      ∀ k', a ≤ k' → optbLt k' optb → k ≠ k' →
        boxInt (rx k) (ry k) (rx k + (1 : ℝ) / (k + 1)) (ry k + (1 : ℝ) / k) ∩
        boxInt (rx k') (ry k') (rx k' + (1 : ℝ) / (k' + 1)) (ry k' + (1 : ℝ) / k') = ∅ := by
  classical
  let s : ℕ → ℕ := fun r => (shelfStart W a ha haW r).1
  have hex_shelf : ∀ k, ∃ r, k < s (r + 1) := by
    intro k
    refine ⟨k, ?_⟩
    have := shelfStart_ge_add W a ha haW (k + 1)
    change a + (k + 1) ≤ s (k + 1) at this
    omega
  let shelf : ℕ → ℕ := fun k => Nat.find (hex_shelf k)
  have hshelf_lt : ∀ k, k < s (shelf k + 1) := fun k => Nat.find_spec (hex_shelf k)
  have hshelf_le : ∀ k, a ≤ k → s (shelf k) ≤ k := by
    intro k hk
    by_cases h0 : shelf k = 0
    · rw [h0]; exact hk
    · have hmin := Nat.find_min (hex_shelf k) (show shelf k - 1 < shelf k by omega)
      have hpred : shelf k - 1 + 1 = shelf k := by omega
      rw [hpred] at hmin
      exact not_lt.mp hmin
  let rx : ℕ → ℝ := fun k => ∑ j ∈ Finset.Ico (s (shelf k)) k, (1 : ℝ) / (j + 1)
  let ry : ℕ → ℝ := fun k => ∑ j ∈ Finset.range (shelf k), (1 : ℝ) / s j
  refine ⟨rx, ry, fun k hk hkb => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · exact Finset.sum_nonneg (fun _ _ => by positivity)
  · have hle : rx k + (1 : ℝ) / (k + 1) = ∑ j ∈ Finset.Ico (s (shelf k)) (k + 1), (1 : ℝ) / (j + 1) := by
      simp only [rx]
      rw [Finset.sum_Ico_succ_top (hshelf_le k hk)]
    rw [hle]
    calc
      ∑ j ∈ Finset.Ico (s (shelf k)) (k + 1), (1 : ℝ) / (j + 1)
        ≤ ∑ j ∈ Finset.Ico (s (shelf k)) (s (shelf k + 1)), (1 : ℝ) / (j + 1) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.Ico_subset_Ico_right (hshelf_lt k)
          · intro _ _ _; positivity
      _ ≤ W := shelfStart_sum_le W a ha haW (shelf k)
  · exact Finset.sum_nonneg (fun _ _ => by positivity)
  · have hsk_pos : 0 < s (shelf k) := (shelfStart W a ha haW (shelf k)).2.1
    have hk_inv : (1 : ℝ) / k ≤ (1 : ℝ) / s (shelf k) :=
      one_div_le_one_div_of_le (by exact_mod_cast hsk_pos) (by exact_mod_cast hshelf_le k hk)
    have hsum : ry k + (1 : ℝ) / k ≤ ∑ j ∈ Finset.range (shelf k + 1), (1 : ℝ) / s j := by
      simp only [ry]
      rw [Finset.sum_range_succ]
      linarith
    have hbound_R := shelfStart_sum_inv_le W a ha haW (shelf k)
    have hW : 0 < W - (1 : ℝ) / a := sub_pos.mpr haW
    cases optb with
    | none =>
      simp only [nfdhBound] at hbound
      have hpos_s : (0 : ℝ) < (1 : ℝ) / s (shelf k) := by positivity
      have hnum : ((1 : ℝ) / a - (1 : ℝ) / s (shelf k)) / (W - (1 : ℝ) / a) ≤
          ((1 : ℝ) / a) / (W - (1 : ℝ) / a) :=
        div_le_div_of_nonneg_right (by linarith) hW.le
      linarith
    | some b =>
      simp only [optbLt, nfdhBound] at hkb hbound
      have hs_lt_b : s (shelf k) < b := lt_of_le_of_lt (hshelf_le k hk) hkb
      have hb_le : (1 : ℝ) / b ≤ (1 : ℝ) / s (shelf k) :=
        one_div_le_one_div_of_le (by exact_mod_cast hsk_pos) (by exact_mod_cast hs_lt_b.le)
      have hnum : ((1 : ℝ) / a - (1 : ℝ) / s (shelf k)) / (W - (1 : ℝ) / a) ≤
          ((1 : ℝ) / a - (1 : ℝ) / b) / (W - (1 : ℝ) / a) :=
        div_le_div_of_nonneg_right (by linarith) hW.le
      linarith
  · intro k' hk' hk'b hne
    rcases lt_trichotomy (shelf k) (shelf k') with hlt | heq | hgt
    · apply boxInt_disjoint_of_y_le
      have hsk_pos : 0 < s (shelf k) := (shelfStart W a ha haW (shelf k)).2.1
      have hk_inv : (1 : ℝ) / k ≤ (1 : ℝ) / s (shelf k) :=
        one_div_le_one_div_of_le (by exact_mod_cast hsk_pos) (by exact_mod_cast hshelf_le k hk)
      have hsum1 : ry k + (1 : ℝ) / k ≤ ∑ j ∈ Finset.range (shelf k + 1), (1 : ℝ) / s j := by
        simp only [ry]; rw [Finset.sum_range_succ]; linarith
      have hsum2 : ∑ j ∈ Finset.range (shelf k + 1), (1 : ℝ) / s j ≤ ry k' := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono hlt
        · intro _ _ _; positivity
      linarith
    · rcases lt_or_gt_of_ne hne with hkk' | hk'k
      · apply boxInt_disjoint_of_x_le
        have hle1 : rx k + (1 : ℝ) / (k + 1) = ∑ j ∈ Finset.Ico (s (shelf k)) (k + 1), (1 : ℝ) / (j + 1) := by
          simp only [rx]; rw [Finset.sum_Ico_succ_top (hshelf_le k hk)]
        rw [hle1, heq]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Ico_subset_Ico_right hkk'
        · intro _ _ _; positivity
      · rw [Set.inter_comm]
        apply boxInt_disjoint_of_x_le
        have hle1 : rx k' + (1 : ℝ) / (k' + 1) = ∑ j ∈ Finset.Ico (s (shelf k')) (k' + 1), (1 : ℝ) / (j + 1) := by
          simp only [rx]; rw [Finset.sum_Ico_succ_top (hshelf_le k' hk')]
        rw [hle1, ← heq]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Ico_subset_Ico_right hk'k
        · intro _ _ _; positivity
    · rw [Set.inter_comm]
      apply boxInt_disjoint_of_y_le
      have hsk_pos : 0 < s (shelf k') := (shelfStart W a ha haW (shelf k')).2.1
      have hk_inv : (1 : ℝ) / k' ≤ (1 : ℝ) / s (shelf k') :=
        one_div_le_one_div_of_le (by exact_mod_cast hsk_pos) (by exact_mod_cast hshelf_le k' hk')
      have hsum1 : ry k' + (1 : ℝ) / k' ≤ ∑ j ∈ Finset.range (shelf k' + 1), (1 : ℝ) / s j := by
        simp only [ry]; rw [Finset.sum_range_succ]; linarith
      have hsum2 : ∑ j ∈ Finset.range (shelf k' + 1), (1 : ℝ) / s j ≤ ry k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono hgt
        · intro _ _ _; positivity
      linarith

/- ## Section 3: Guillotine tree and pure-N validator -/

def D_val : ℕ := 10000000
def S_val : ℕ := 10020000

inductive GTree where
  | empty
  | rect (k : ℕ) (rot : Bool)
  | nfdh (a : ℕ) (b : Option ℕ) (flip : Bool)
  | hcut (c : ℕ) (l r : GTree)
  | vcut (c : ℕ) (l r : GTree)
  deriving DecidableEq

def GTree.valid (x0 y0 x1 y1 : ℕ) : GTree → Bool
  | .empty => decide (x0 ≤ x1 ∧ y0 ≤ y1)
  | .rect k rot => decide (x0 ≤ x1 ∧ y0 ≤ y1 ∧ 1 ≤ k) &&
      (if rot then decide (D_val ≤ (x1 - x0) * (k + 1) ∧ D_val ≤ (y1 - y0) * k)
      else decide (D_val ≤ (x1 - x0) * k ∧ D_val ≤ (y1 - y0) * (k + 1)))
  | .nfdh a optb flip =>
      let W := if flip then y1 - y0 else x1 - x0
      let H := if flip then x1 - x0 else y1 - y0
      decide (x0 ≤ x1 ∧ y0 ≤ y1 ∧ 1 ≤ a ∧ D_val < a * W ∧ D_val ≤ a * H) &&
        match optb with
        | none => decide (a * D_val * D_val ≤ (a * H - D_val) * (a * W - D_val))
        | some b => decide (a < b ∧ a * D_val * D_val * (b - a) ≤ b * (a * H - D_val) * (a * W - D_val))
  | .hcut c l r => decide (x0 ≤ c ∧ c ≤ x1) && l.valid x0 y0 c y1 && r.valid c y0 x1 y1
  | .vcut c l r => decide (y0 ≤ c ∧ c ≤ y1) && l.valid x0 y0 x1 c && r.valid x0 c x1 y1

def GTree.intervalsAux (acc : List (ℕ × Option ℕ)) : GTree → List (ℕ × Option ℕ)
  | .empty => acc
  | .rect k _ => (k, some (k + 1)) :: acc
  | .nfdh a optb _ => (a, optb) :: acc
  | .hcut _ l r => l.intervalsAux (r.intervalsAux acc)
  | .vcut _ l r => l.intervalsAux (r.intervalsAux acc)

def GTree.intervals (t : GTree) : List (ℕ × Option ℕ) :=
  t.intervalsAux []

def mergePairsFuel : ℕ → List (ℕ × Option ℕ) → List (ℕ × Option ℕ) → List (ℕ × Option ℕ)
  | 0, _, _ => []
  | _, [], ys => ys
  | _, xs, [] => xs
  | f + 1, x :: xs, y :: ys =>
    if x.1 ≤ y.1 then x :: mergePairsFuel f xs (y :: ys) else y :: mergePairsFuel f (x :: xs) ys

def mergePairs (xs ys : List (ℕ × Option ℕ)) : List (ℕ × Option ℕ) :=
  mergePairsFuel (xs.length + ys.length + 1) xs ys

def mergeRound : List (List (ℕ × Option ℕ)) → List (List (ℕ × Option ℕ))
  | [] => []
  | [x] => [x]
  | x :: y :: rest => mergePairs x y :: mergeRound rest

def mergeAll (n : ℕ) (xss : List (List (ℕ × Option ℕ))) : List (ℕ × Option ℕ) :=
  match n, xss with
  | _, [] => []
  | _, [x] => x
  | 0, _ => []
  | n + 1, _ => mergeAll n (mergeRound xss)

def sortPairs (l : List (ℕ × Option ℕ)) : List (ℕ × Option ℕ) :=
  mergeAll 10 (l.map fun x => [x])

def checkChain (cur : ℕ) : List (ℕ × Option ℕ) → Bool
  | [] => false
  | [(a, none)] => decide (cur = a)
  | (a, some b) :: rest => decide (cur = a ∧ a < b) && checkChain b rest
  | _ => false

def GTree.covers (t : GTree) : Bool :=
  checkChain 1 (sortPairs t.intervals)

def ivMem (k : ℕ) (iv : ℕ × Option ℕ) : Prop :=
  iv.1 ≤ k ∧ match iv.2 with | none => True | some b => k < b

lemma mem_intervalsAux {p : ℕ × Option ℕ} {acc : List (ℕ × Option ℕ)} {t : GTree} :
    p ∈ t.intervalsAux acc ↔ p ∈ t.intervalsAux [] ∨ p ∈ acc := by
  induction t generalizing acc with
  | empty => simp [GTree.intervalsAux]
  | rect k rot =>
    simp only [GTree.intervalsAux, List.mem_cons, List.not_mem_nil, or_false]
  | nfdh a optb flip =>
    simp only [GTree.intervalsAux, List.mem_cons, List.not_mem_nil, or_false]
  | hcut _ l r ihl ihr =>
    simp only [GTree.intervalsAux]
    rw [ihl, ihr, ihl (acc := r.intervalsAux [])]
    tauto
  | vcut _ l r ihl ihr =>
    simp only [GTree.intervalsAux]
    rw [ihl, ihr, ihl (acc := r.intervalsAux [])]
    tauto

lemma intervalsAux_eq_append (t : GTree) (acc : List (ℕ × Option ℕ)) :
    t.intervalsAux acc = t.intervalsAux [] ++ acc := by
  induction t generalizing acc with
  | empty => rfl
  | rect _ _ => rfl
  | nfdh _ _ _ => rfl
  | hcut _ l r ihl ihr =>
    simp only [GTree.intervalsAux]
    rw [ihl, ihr, ihl (acc := r.intervalsAux []), List.append_assoc]
  | vcut _ l r ihl ihr =>
    simp only [GTree.intervalsAux]
    rw [ihl, ihr, ihl (acc := r.intervalsAux []), List.append_assoc]

lemma intervalsAux_cons_eq_append (t : GTree) (a : ℕ × Option ℕ) (acc : List (ℕ × Option ℕ)) :
    t.intervalsAux (a :: acc) = t.intervalsAux [] ++ (a :: acc) :=
  intervalsAux_eq_append t (a :: acc)

lemma mem_mergePairsFuel {p : ℕ × Option ℕ} {f : ℕ} {xs ys : List (ℕ × Option ℕ)} :
    p ∈ mergePairsFuel f xs ys → p ∈ xs ∨ p ∈ ys := by
  induction f generalizing xs ys with
  | zero => simp [mergePairsFuel]
  | succ f ih =>
    cases xs with
    | nil => simp [mergePairsFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergePairsFuel]
      | cons y ys =>
        simp only [mergePairsFuel]
        split_ifs
        · intro hp
          simp only [List.mem_cons] at hp ⊢
          rcases hp with rfl | hp
          · exact Or.inl (Or.inl rfl)
          · rcases ih hp with h1 | h2
            · exact Or.inl (Or.inr h1)
            · exact Or.inr (List.mem_cons.mp h2)
        · intro hp
          simp only [List.mem_cons] at hp ⊢
          rcases hp with rfl | hp
          · exact Or.inr (Or.inl rfl)
          · rcases ih hp with h1 | h2
            · exact Or.inl (List.mem_cons.mp h1)
            · exact Or.inr (Or.inr h2)

lemma mem_mergePairs {p : ℕ × Option ℕ} {xs ys : List (ℕ × Option ℕ)} :
    p ∈ mergePairs xs ys → p ∈ xs ∨ p ∈ ys :=
  mem_mergePairsFuel

lemma mem_mergeRound {p : ℕ × Option ℕ} {xss : List (List (ℕ × Option ℕ))} :
    (∃ xs ∈ mergeRound xss, p ∈ xs) → ∃ xs ∈ xss, p ∈ xs := by
  match xss with
  | [] => simp [mergeRound]
  | [x] => simp [mergeRound]
  | x :: y :: rest =>
    rintro ⟨xs, hxs, hp⟩
    simp only [mergeRound, List.mem_cons] at hxs
    rcases hxs with rfl | hxs
    · rcases mem_mergePairs hp with hx | hy
      · exact ⟨x, List.mem_cons_self, hx⟩
      · exact ⟨y, List.mem_cons_of_mem _ List.mem_cons_self, hy⟩
    · obtain ⟨zs, hzs, hpz⟩ := mem_mergeRound ⟨xs, hxs, hp⟩
      exact ⟨zs, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hzs), hpz⟩
termination_by xss.length

lemma mem_mergeAll {p : ℕ × Option ℕ} {n : ℕ} {xss : List (List (ℕ × Option ℕ))} :
    p ∈ mergeAll n xss → ∃ xs ∈ xss, p ∈ xs := by
  induction n generalizing xss with
  | zero =>
    cases xss with
    | nil => simp [mergeAll]
    | cons x xs => cases xs <;> simp [mergeAll]
  | succ n ih =>
    cases xss with
    | nil => simp [mergeAll]
    | cons x xs =>
      cases xs with
      | nil => simp [mergeAll]
      | cons y ys =>
        intro hp
        exact mem_mergeRound (ih hp)

lemma mem_sortPairs {p : ℕ × Option ℕ} {l : List (ℕ × Option ℕ)} :
    p ∈ sortPairs l → p ∈ l := by
  intro hp
  obtain ⟨xs, hxs, hpx⟩ := mem_mergeAll hp
  simp only [List.mem_map] at hxs
  obtain ⟨q, hq, rfl⟩ := hxs
  simp only [List.mem_singleton] at hpx
  rwa [hpx]

lemma checkChain_covers {cur : ℕ} {l : List (ℕ × Option ℕ)}
    (h : checkChain cur l = true) :
    ∀ k, cur ≤ k → ∃ iv ∈ l, ivMem k iv := by
  induction l generalizing cur with
  | nil => simp [checkChain] at h
  | cons head tail ih =>
    rcases head with ⟨a, optb⟩
    cases optb with
    | none =>
      cases tail with
      | nil =>
        simp only [checkChain, decide_eq_true_eq] at h
        intro k hk
        exact ⟨(a, none), List.mem_singleton.mpr rfl, h ▸ hk, trivial⟩
      | cons _ _ => simp [checkChain] at h
    | some b =>
      cases tail with
      | nil => simp [checkChain] at h
      | cons h2 t2 =>
        simp only [checkChain, Bool.and_eq_true, decide_eq_true_eq] at h
        rcases h with ⟨⟨rfl, hab⟩, hrest⟩
        intro k hk
        by_cases hkb : k < b
        · exact ⟨(cur, some b), List.mem_cons_self, hk, hkb⟩
        · obtain ⟨iv, hiv, hmem⟩ := ih hrest k (not_lt.mp hkb)
          exact ⟨iv, List.mem_cons_of_mem _ hiv, hmem⟩

lemma covers_imp_mem {t : GTree} (h : t.covers = true) (k : ℕ) (hk : 1 ≤ k) :
    ∃ iv ∈ t.intervals, ivMem k iv := by
  obtain ⟨iv, hiv, hmem⟩ := checkChain_covers h k hk
  exact ⟨iv, mem_sortPairs hiv, hmem⟩

def GTree.leafAt (x0 y0 x1 y1 : ℕ) : GTree → ℕ → Option (ℕ × ℕ × ℕ × ℕ × GTree)
  | .empty, _ => none
  | .rect j rot, k => if k = j then some (x0, y0, x1, y1, .rect j rot) else none
  | .nfdh a optb flip, k =>
      if decide (a ≤ k) && (match optb with | none => true | some b => decide (k < b)) then
        some (x0, y0, x1, y1, .nfdh a optb flip)
      else none
  | .hcut c l r, k =>
      match l.leafAt x0 y0 c y1 k with
      | some v => some v
      | none => r.leafAt c y0 x1 y1 k
  | .vcut c l r, k =>
      match l.leafAt x0 y0 x1 c k with
      | some v => some v
      | none => r.leafAt x0 c x1 y1 k

def boxOfN (x0 y0 x1 y1 : ℕ) : Set (ℝ × ℝ) :=
  boxSet ((x0 : ℝ) / D_val) ((y0 : ℝ) / D_val) ((x1 : ℝ) / D_val) ((y1 : ℝ) / D_val)

def boxIntOfN (x0 y0 x1 y1 : ℕ) : Set (ℝ × ℝ) :=
  boxInt ((x0 : ℝ) / D_val) ((y0 : ℝ) / D_val) ((x1 : ℝ) / D_val) ((y1 : ℝ) / D_val)

lemma leafAt_of_mem_intervals {x0 y0 x1 y1 : ℕ} {t : GTree} {k : ℕ}
    (h : ∃ iv ∈ t.intervals, ivMem k iv) :
    (t.leafAt x0 y0 x1 y1 k).isSome = true := by
  induction t generalizing x0 y0 x1 y1 with
  | empty => simp [GTree.intervals, GTree.intervalsAux] at h
  | rect j rot =>
    obtain ⟨iv, hiv, hmem⟩ := h
    simp only [GTree.intervals, GTree.intervalsAux, List.mem_singleton] at hiv
    subst hiv
    simp only [ivMem] at hmem
    have hkj : k = j := by omega
    simp [GTree.leafAt, hkj]
  | nfdh a optb flip =>
    obtain ⟨iv, hiv, hmem⟩ := h
    simp only [GTree.intervals, GTree.intervalsAux, List.mem_singleton] at hiv
    subst hiv
    simp only [ivMem] at hmem
    cases optb with
    | none => simp [GTree.leafAt, hmem.1]
    | some b => simp [GTree.leafAt, hmem.1, hmem.2]
  | hcut c l r ihl ihr =>
    obtain ⟨iv, hiv, hmem⟩ := h
    rw [GTree.intervals, GTree.intervalsAux, mem_intervalsAux] at hiv
    rcases hiv with hl | hr
    · have hsome : (l.leafAt x0 y0 c y1 k).isSome = true := ihl ⟨iv, hl, hmem⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
      simp only [GTree.leafAt, hv, Option.isSome_some]
    · have hsome : (r.leafAt c y0 x1 y1 k).isSome = true := ihr ⟨iv, hr, hmem⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
      cases hlv : l.leafAt x0 y0 c y1 k with
      | some w => simp [GTree.leafAt, hlv]
      | none => simp [GTree.leafAt, hlv, hv]
  | vcut c l r ihl ihr =>
    obtain ⟨iv, hiv, hmem⟩ := h
    rw [GTree.intervals, GTree.intervalsAux, mem_intervalsAux] at hiv
    rcases hiv with hl | hr
    · have hsome : (l.leafAt x0 y0 x1 c k).isSome = true := ihl ⟨iv, hl, hmem⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
      simp only [GTree.leafAt, hv, Option.isSome_some]
    · have hsome : (r.leafAt x0 c x1 y1 k).isSome = true := ihr ⟨iv, hr, hmem⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
      cases hlv : l.leafAt x0 y0 x1 c k with
      | some w => simp [GTree.leafAt, hlv]
      | none => simp [GTree.leafAt, hlv, hv]

lemma leafAt_box_subset {x0 y0 x1 y1 bx0 by0 bx1 by1 : ℕ} {t leaf : GTree} {k : ℕ}
    (hv : t.valid x0 y0 x1 y1 = true)
    (hl : t.leafAt x0 y0 x1 y1 k = some (bx0, by0, bx1, by1, leaf)) :
    x0 ≤ bx0 ∧ bx0 ≤ bx1 ∧ bx1 ≤ x1 ∧ y0 ≤ by0 ∧ by0 ≤ by1 ∧ by1 ≤ y1 := by
  induction t generalizing x0 y0 x1 y1 with
  | empty => simp [GTree.leafAt] at hl
  | rect j rot =>
    simp only [GTree.leafAt] at hl
    split_ifs at hl
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Option.some.inj hl
    simp only [GTree.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact ⟨le_rfl, hv.1.1, le_rfl, le_rfl, hv.1.2.1, le_rfl⟩
  | nfdh a optb flip =>
    simp only [GTree.leafAt] at hl
    split_ifs at hl
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Option.some.inj hl
    simp only [GTree.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact ⟨le_rfl, hv.1.1, le_rfl, le_rfl, hv.1.2.1, le_rfl⟩
  | hcut c l r ihl ihr =>
    simp only [GTree.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    rcases hv with ⟨⟨⟨hc1, hc2⟩, hvl⟩, hvr⟩
    simp only [GTree.leafAt] at hl
    by_cases hls : (l.leafAt x0 y0 c y1 k).isSome = true
    · obtain ⟨v, hll⟩ := Option.isSome_iff_exists.mp hls
      rw [hll] at hl
      change some v = some (bx0, by0, bx1, by1, leaf) at hl
      rw [Option.some.inj hl] at hll
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ihl hvl hll
      exact ⟨a1, a2, le_trans a3 hc2, a4, a5, a6⟩
    · have hll : l.leafAt x0 y0 c y1 k = none := by
        cases hopt : l.leafAt x0 y0 c y1 k with
        | none => rfl
        | some w => exact absurd (by simp [hopt]) hls
      rw [hll] at hl
      change r.leafAt c y0 x1 y1 k = some (bx0, by0, bx1, by1, leaf) at hl
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ihr hvr hl
      exact ⟨le_trans hc1 a1, a2, a3, a4, a5, a6⟩
  | vcut c l r ihl ihr =>
    simp only [GTree.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    rcases hv with ⟨⟨⟨hc1, hc2⟩, hvl⟩, hvr⟩
    simp only [GTree.leafAt] at hl
    by_cases hls : (l.leafAt x0 y0 x1 c k).isSome = true
    · obtain ⟨v, hll⟩ := Option.isSome_iff_exists.mp hls
      rw [hll] at hl
      change some v = some (bx0, by0, bx1, by1, leaf) at hl
      rw [Option.some.inj hl] at hll
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ihl hvl hll
      exact ⟨a1, a2, a3, a4, a5, le_trans a6 hc2⟩
    · have hll : l.leafAt x0 y0 x1 c k = none := by
        cases hopt : l.leafAt x0 y0 x1 c k with
        | none => rfl
        | some w => exact absurd (by simp [hopt]) hls
      rw [hll] at hl
      change r.leafAt x0 c x1 y1 k = some (bx0, by0, bx1, by1, leaf) at hl
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ihr hvr hl
      exact ⟨a1, a2, a3, le_trans hc1 a4, a5, a6⟩

lemma D_val_pos : (0 : ℝ) < D_val := by norm_num [D_val]

noncomputable def placeLeaf (x0 y0 x1 y1 : ℕ) (k : ℕ) : GTree → Rectangle
  | .rect _ rot =>
    let rx := (x0 : ℝ) / D_val
    let ry := (y0 : ℝ) / D_val
    let w := (1 : ℝ) / k
    let h := (1 : ℝ) / (k + 1)
    if rot then ⟨w, h, (rx + h, ry), (Real.pi / 2 : ℝ)⟩
    else ⟨w, h, (rx, ry), 0⟩
  | .nfdh a optb flip =>
    let W_n := if flip then y1 - y0 else x1 - x0
    let H_n := if flip then x1 - x0 else y1 - y0
    let W := (W_n : ℝ) / D_val
    let H := (H_n : ℝ) / D_val
    let rx0 := (x0 : ℝ) / D_val
    let ry0 := (y0 : ℝ) / D_val
    let w := (1 : ℝ) / k
    let h := (1 : ℝ) / (k + 1)
    { width := w
      height := h
      start := by
        classical
        by_cases hcond : 0 < a ∧ (1 : ℝ) / a < W ∧ (1 : ℝ) / a ≤ H ∧ nfdhBound W H a optb
        · let coords := Classical.choose (nfdh_pack_box W H a optb hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2)
          let rxs := coords
          let rys := Classical.choose (Classical.choose_spec (nfdh_pack_box W H a optb hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2))
          exact if flip then (rx0 + rys k, ry0 + rxs k) else (rx0 + rxs k + h, ry0 + rys k)
        · exact (rx0, ry0)
      rotation := by
        classical
        by_cases hcond : 0 < a ∧ (1 : ℝ) / a < W ∧ (1 : ℝ) / a ≤ H ∧ nfdhBound W H a optb
        · exact if flip then 0 else (Real.pi / 2 : ℝ)
        · exact 0 }
  | _ => ⟨(1 : ℝ) / k, (1 : ℝ) / (k + 1), (0, 0), 0⟩

lemma placeLeaf_width (x0 y0 x1 y1 k : ℕ) (t : GTree) :
    (placeLeaf x0 y0 x1 y1 k t).width = (1 : ℝ) / k := by
  cases t with
  | empty => rfl
  | hcut _ _ _ => rfl
  | vcut _ _ _ => rfl
  | rect _ rot => cases rot <;> rfl
  | nfdh _ _ _ => rfl

lemma placeLeaf_height (x0 y0 x1 y1 k : ℕ) (t : GTree) :
    (placeLeaf x0 y0 x1 y1 k t).height = (1 : ℝ) / (k + 1) := by
  cases t with
  | empty => rfl
  | hcut _ _ _ => rfl
  | vcut _ _ _ => rfl
  | rect _ rot => cases rot <;> rfl
  | nfdh _ _ _ => rfl

lemma valid_nfdh_to_real {x0 y0 x1 y1 a : ℕ} {optb : Option ℕ} {flip : Bool}
    (hv : (GTree.nfdh a optb flip).valid x0 y0 x1 y1 = true) :
    0 < a ∧
    (1 : ℝ) / a < ((if flip then y1 - y0 else x1 - x0 : ℕ) : ℝ) / D_val ∧
    (1 : ℝ) / a ≤ ((if flip then x1 - x0 else y1 - y0 : ℕ) : ℝ) / D_val ∧
    nfdhBound (((if flip then y1 - y0 else x1 - x0 : ℕ) : ℝ) / D_val)
      (((if flip then x1 - x0 else y1 - y0 : ℕ) : ℝ) / D_val) a optb := by
  simp only [GTree.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
  rcases hv with ⟨⟨_, _, ha, hW_nat, hH_nat⟩, hbound⟩
  set Wn := if flip then y1 - y0 else x1 - x0
  set Hn := if flip then x1 - x0 else y1 - y0
  have ha_pos : (0 : ℝ) < a := by exact_mod_cast ha
  have hD_pos : (0 : ℝ) < D_val := D_val_pos
  have hW_real : (D_val : ℝ) < (a : ℝ) * Wn := by exact_mod_cast hW_nat
  have hH_real : (D_val : ℝ) ≤ (a : ℝ) * Hn := by exact_mod_cast hH_nat
  have haW : (1 : ℝ) / a < (Wn : ℝ) / D_val := by
    rw [div_lt_div_iff₀ ha_pos hD_pos]
    linarith
  have haH : (1 : ℝ) / a ≤ (Hn : ℝ) / D_val := by
    rw [div_le_div_iff₀ ha_pos hD_pos]
    linarith
  refine ⟨ha, haW, haH, ?_⟩
  have hsubW : ((a * Wn - D_val : ℕ) : ℝ) = (a : ℝ) * Wn - D_val := by
    rw [Nat.cast_sub hW_nat.le, Nat.cast_mul]
  have hsubH : ((a * Hn - D_val : ℕ) : ℝ) = (a : ℝ) * Hn - D_val := by
    rw [Nat.cast_sub hH_nat, Nat.cast_mul]
  have hWsub_pos : 0 < (a : ℝ) * Wn - D_val := sub_pos.mpr hW_real
  cases optb with
  | none =>
    simp only [decide_eq_true_eq] at hbound
    have hb_real : (a : ℝ) * D_val * D_val ≤ ((a : ℝ) * Hn - D_val) * ((a : ℝ) * Wn - D_val) := by
      rw [← hsubH, ← hsubW]
      exact_mod_cast hbound
    simp only [nfdhBound]
    rw [← le_sub_iff_add_le']
    have h1 : (Wn : ℝ) / D_val - (1 : ℝ) / a = ((a : ℝ) * Wn - D_val) / ((a : ℝ) * D_val) := by
      field_simp
    have h2 : (Hn : ℝ) / D_val - (1 : ℝ) / a = ((a : ℝ) * Hn - D_val) / ((a : ℝ) * D_val) := by
      field_simp
    rw [h1, h2]
    field_simp
    linarith [hb_real]
  | some b =>
    simp only [decide_eq_true_eq] at hbound
    rcases hbound with ⟨hab, hb_nat⟩
    simp only [nfdhBound]
    refine ⟨hab, ?_⟩
    have hb_pos : (0 : ℝ) < b := by exact_mod_cast lt_trans ha hab
    have hsub_ba : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := by rw [Nat.cast_sub hab.le]
    have hb_real : (a : ℝ) * D_val * D_val * ((b : ℝ) - a) ≤
        (b : ℝ) * ((a : ℝ) * Hn - D_val) * ((a : ℝ) * Wn - D_val) := by
      rw [← hsub_ba, ← hsubH, ← hsubW]
      exact_mod_cast hb_nat
    rw [← le_sub_iff_add_le']
    have h0 : (1 : ℝ) / a - (1 : ℝ) / b = ((b : ℝ) - a) / ((a : ℝ) * b) := by
      field_simp
    have h1 : (Wn : ℝ) / D_val - (1 : ℝ) / a = ((a : ℝ) * Wn - D_val) / ((a : ℝ) * D_val) := by
      field_simp
    have h2 : (Hn : ℝ) / D_val - (1 : ℝ) / a = ((a : ℝ) * Hn - D_val) / ((a : ℝ) * D_val) := by
      field_simp
    rw [h0, h1, h2]
    field_simp
    linarith [hb_real]

lemma placeLeaf_rect_toSet {x0 y0 x1 y1 k : ℕ} {rot : Bool}
    (hv : (GTree.rect k rot).valid x0 y0 x1 y1 = true) :
    (placeLeaf x0 y0 x1 y1 k (.rect k rot)).toSet ⊆ boxOfN x0 y0 x1 y1 := by
  simp only [GTree.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
  rcases hv with ⟨⟨hx, hy, hk⟩, hfit⟩
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hw : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have hh : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
  have hD : (0 : ℝ) < D_val := D_val_pos
  cases rot
  · simp only [placeLeaf, Bool.false_eq_true, ↓reduceIte, rect0_toSet hw hh]
    simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hfit
    apply boxSet_mono le_rfl le_rfl
    · have h1 : (D_val : ℝ) ≤ ((x1 - x0 : ℕ) : ℝ) * k := by exact_mod_cast hfit.1
      rw [Nat.cast_sub hx] at h1
      rw [← le_sub_iff_add_le']
      calc
        (1 : ℝ) / k ≤ ((x1 : ℝ) - x0) / D_val := by
          rw [div_le_div_iff₀ hk_pos hD]; linarith
        _ = (x1 : ℝ) / D_val - (x0 : ℝ) / D_val := by ring
    · have h2 : (D_val : ℝ) ≤ ((y1 - y0 : ℕ) : ℝ) * ((k : ℝ) + 1) := by exact_mod_cast hfit.2
      rw [Nat.cast_sub hy] at h2
      rw [← le_sub_iff_add_le']
      calc
        (1 : ℝ) / (k + 1) ≤ ((y1 : ℝ) - y0) / D_val := by
          rw [div_le_div_iff₀ (by positivity) hD]; linarith
        _ = (y1 : ℝ) / D_val - (y0 : ℝ) / D_val := by ring
  · simp only [placeLeaf, ↓reduceIte, rect90_toSet hw hh]
    simp only [↓reduceIte, decide_eq_true_eq] at hfit
    apply boxSet_mono le_rfl le_rfl
    · have h1 : (D_val : ℝ) ≤ ((x1 - x0 : ℕ) : ℝ) * ((k : ℝ) + 1) := by exact_mod_cast hfit.1
      rw [Nat.cast_sub hx] at h1
      rw [← le_sub_iff_add_le']
      calc
        (1 : ℝ) / (k + 1) ≤ ((x1 : ℝ) - x0) / D_val := by
          rw [div_le_div_iff₀ (by positivity) hD]; linarith
        _ = (x1 : ℝ) / D_val - (x0 : ℝ) / D_val := by ring
    · have h2 : (D_val : ℝ) ≤ ((y1 - y0 : ℕ) : ℝ) * k := by exact_mod_cast hfit.2
      rw [Nat.cast_sub hy] at h2
      rw [← le_sub_iff_add_le']
      calc
        (1 : ℝ) / k ≤ ((y1 : ℝ) - y0) / D_val := by
          rw [div_le_div_iff₀ hk_pos hD]; linarith
        _ = (y1 : ℝ) / D_val - (y0 : ℝ) / D_val := by ring

lemma placeLeaf_nfdh_spec {x0 y0 x1 y1 a k : ℕ} {optb : Option ℕ} {flip : Bool}
    (hv : (GTree.nfdh a optb flip).valid x0 y0 x1 y1 = true)
    (hk : a ≤ k) (hkb : optbLt k optb) :
    (placeLeaf x0 y0 x1 y1 k (.nfdh a optb flip)).toSet ⊆ boxOfN x0 y0 x1 y1 ∧
    ∀ k', a ≤ k' → optbLt k' optb → k ≠ k' →
      interior (placeLeaf x0 y0 x1 y1 k (.nfdh a optb flip)).toSet ∩
      interior (placeLeaf x0 y0 x1 y1 k' (.nfdh a optb flip)).toSet = ∅ := by
  have hv' := hv
  simp only [GTree.valid, Bool.and_eq_true, decide_eq_true_eq] at hv'
  rcases hv' with ⟨⟨hx, hy, ha, _⟩, _⟩
  set Wn := if flip then y1 - y0 else x1 - x0
  set Hn := if flip then x1 - x0 else y1 - y0
  set W := (Wn : ℝ) / D_val
  set H := (Hn : ℝ) / D_val
  have hcond : 0 < a ∧ (1 : ℝ) / a < W ∧ (1 : ℝ) / a ≤ H ∧ nfdhBound W H a optb :=
    valid_nfdh_to_real hv
  let hspec := Classical.choose_spec (nfdh_pack_box W H a optb hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2)
  let rxs := Classical.choose (nfdh_pack_box W H a optb hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2)
  let rys := Classical.choose hspec
  have hcoords : ∀ j, a ≤ j → optbLt j optb →
      0 ≤ rxs j ∧ rxs j + (1 : ℝ) / (j + 1) ≤ W ∧
      0 ≤ rys j ∧ rys j + (1 : ℝ) / j ≤ H ∧
      ∀ j', a ≤ j' → optbLt j' optb → j ≠ j' →
        boxInt (rxs j) (rys j) (rxs j + (1 : ℝ) / (j + 1)) (rys j + (1 : ℝ) / j) ∩
        boxInt (rxs j') (rys j') (rxs j' + (1 : ℝ) / (j' + 1)) (rys j' + (1 : ℝ) / j') = ∅ :=
    Classical.choose_spec hspec
  obtain ⟨hrx0, hrxW, hry0, hryH, hdisj⟩ := hcoords k hk hkb
  have hw : (0 : ℝ) ≤ (1 : ℝ) / k := by positivity
  have hh : (0 : ℝ) ≤ (1 : ℝ) / (k + 1) := by positivity
  have hD : (0 : ℝ) < D_val := D_val_pos
  have hW_eq : (x0 : ℝ) / D_val + (if flip then H else W) = (x1 : ℝ) / D_val := by
    cases flip <;> simp only [W, H, Wn, Hn, ↓reduceIte, Bool.false_eq_true]
    · rw [Nat.cast_sub hx]; ring
    · rw [Nat.cast_sub hx]; ring
  have hH_eq : (y0 : ℝ) / D_val + (if flip then W else H) = (y1 : ℝ) / D_val := by
    cases flip <;> simp only [W, H, Wn, Hn, ↓reduceIte, Bool.false_eq_true]
    · rw [Nat.cast_sub hy]; ring
    · rw [Nat.cast_sub hy]; ring
  constructor
  · cases flip
    · simp only [placeLeaf, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> try contradiction
      rw [rect90_toSet hw hh]
      apply boxSet_mono (by linarith) (by linarith)
      · have : (x0 : ℝ) / D_val + W = (x1 : ℝ) / D_val := by simpa using hW_eq
        linarith
      · have : (y0 : ℝ) / D_val + H = (y1 : ℝ) / D_val := by simpa using hH_eq
        linarith
    · simp only [placeLeaf, ↓reduceIte]
      split_ifs <;> try contradiction
      rw [rect0_toSet hw hh]
      apply boxSet_mono (by linarith) (by linarith)
      · have : (x0 : ℝ) / D_val + H = (x1 : ℝ) / D_val := by simpa using hW_eq
        linarith
      · have : (y0 : ℝ) / D_val + W = (y1 : ℝ) / D_val := by simpa using hH_eq
        linarith
  · intro k' hk' hk'b hne
    have hw' : (0 : ℝ) ≤ (1 : ℝ) / k' := by positivity
    have hh' : (0 : ℝ) ≤ (1 : ℝ) / (k' + 1) := by positivity
    have hd := hdisj k' hk' hk'b hne
    cases flip
    · simp only [placeLeaf, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> try contradiction
      rw [rect90_toSet hw hh, rect90_toSet hw' hh', interior_boxSet, interior_boxSet]
      simp only [add_assoc]
      exact boxInt_translate_disjoint hd
    · simp only [placeLeaf, ↓reduceIte]
      split_ifs <;> try contradiction
      rw [rect0_toSet hw hh, rect0_toSet hw' hh', interior_boxSet, interior_boxSet]
      simp only [add_assoc]
      exact boxInt_swap_translate_disjoint hd

noncomputable def GTree.place (x0 y0 x1 y1 : ℕ) (t : GTree) (k : ℕ) : Rectangle :=
  match t.leafAt x0 y0 x1 y1 k with
  | some (bx0, by0, bx1, by1, leaf) => placeLeaf bx0 by0 bx1 by1 k leaf
  | none => ⟨(1 : ℝ) / k, (1 : ℝ) / (k + 1), (0, 0), 0⟩

lemma GTree.place_width (x0 y0 x1 y1 : ℕ) (t : GTree) (k : ℕ) :
    (t.place x0 y0 x1 y1 k).width = (1 : ℝ) / k := by
  simp only [GTree.place]
  cases t.leafAt x0 y0 x1 y1 k with
  | none => rfl
  | some v => exact placeLeaf_width _ _ _ _ _ _

lemma GTree.place_height (x0 y0 x1 y1 : ℕ) (t : GTree) (k : ℕ) :
    (t.place x0 y0 x1 y1 k).height = (1 : ℝ) / (k + 1) := by
  simp only [GTree.place]
  cases t.leafAt x0 y0 x1 y1 k with
  | none => rfl
  | some v => exact placeLeaf_height _ _ _ _ _ _

def leafCond (k : ℕ) : GTree → Prop
  | .rect j _ => k = j
  | .nfdh a optb _ => a ≤ k ∧ optbLt k optb
  | _ => False

lemma leafAt_valid {x0 y0 x1 y1 bx0 by0 bx1 by1 : ℕ} {t leaf : GTree} {k : ℕ}
    (hv : t.valid x0 y0 x1 y1 = true)
    (hl : t.leafAt x0 y0 x1 y1 k = some (bx0, by0, bx1, by1, leaf)) :
    leaf.valid bx0 by0 bx1 by1 = true ∧ leafCond k leaf := by
  induction t generalizing x0 y0 x1 y1 with
  | empty => simp [GTree.leafAt] at hl
  | rect j rot =>
    simp only [GTree.leafAt] at hl
    split_ifs at hl with hkj
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Option.some.inj hl
    exact ⟨hv, hkj⟩
  | nfdh a optb flip =>
    simp only [GTree.leafAt] at hl
    split_ifs at hl with hcond
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Option.some.inj hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    refine ⟨hv, hcond.1, ?_⟩
    cases optb with
    | none => trivial
    | some b => simp only [optbLt]; exact decide_eq_true_eq.mp hcond.2
  | hcut c l r ihl ihr =>
    simp only [GTree.valid, Bool.and_eq_true] at hv
    simp only [GTree.leafAt] at hl
    by_cases hls : (l.leafAt x0 y0 c y1 k).isSome = true
    · obtain ⟨v, hll⟩ := Option.isSome_iff_exists.mp hls
      rw [hll] at hl
      change some v = some (bx0, by0, bx1, by1, leaf) at hl
      rw [Option.some.inj hl] at hll
      exact ihl hv.1.2 hll
    · have hll : l.leafAt x0 y0 c y1 k = none := by
        cases hopt : l.leafAt x0 y0 c y1 k with
        | none => rfl
        | some w => exact absurd (by simp [hopt]) hls
      rw [hll] at hl
      change r.leafAt c y0 x1 y1 k = some (bx0, by0, bx1, by1, leaf) at hl
      exact ihr hv.2 hl
  | vcut c l r ihl ihr =>
    simp only [GTree.valid, Bool.and_eq_true] at hv
    simp only [GTree.leafAt] at hl
    by_cases hls : (l.leafAt x0 y0 x1 c k).isSome = true
    · obtain ⟨v, hll⟩ := Option.isSome_iff_exists.mp hls
      rw [hll] at hl
      change some v = some (bx0, by0, bx1, by1, leaf) at hl
      rw [Option.some.inj hl] at hll
      exact ihl hv.1.2 hll
    · have hll : l.leafAt x0 y0 x1 c k = none := by
        cases hopt : l.leafAt x0 y0 x1 c k with
        | none => rfl
        | some w => exact absurd (by simp [hopt]) hls
      rw [hll] at hl
      change r.leafAt x0 c x1 y1 k = some (bx0, by0, bx1, by1, leaf) at hl
      exact ihr hv.2 hl

lemma GTree.place_subset {x0 y0 x1 y1 : ℕ} {t : GTree} {k : ℕ}
    (hv : t.valid x0 y0 x1 y1 = true)
    (hsome : (t.leafAt x0 y0 x1 y1 k).isSome = true) :
    (t.place x0 y0 x1 y1 k).toSet ⊆ boxOfN x0 y0 x1 y1 := by
  obtain ⟨⟨bx0, by0, bx1, by1, leaf⟩, hl⟩ := Option.isSome_iff_exists.mp hsome
  simp only [GTree.place, hl]
  obtain ⟨hx0, _, hx1, hy0, _, hy1⟩ := leafAt_box_subset hv hl
  have hbox : boxOfN bx0 by0 bx1 by1 ⊆ boxOfN x0 y0 x1 y1 := by
    apply boxSet_mono
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hx0) D_val_pos.le
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hy0) D_val_pos.le
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hx1) D_val_pos.le
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hy1) D_val_pos.le
  obtain ⟨hlv, hcond⟩ := leafAt_valid hv hl
  refine Set.Subset.trans ?_ hbox
  cases leaf with
  | empty => exact False.elim hcond
  | hcut _ _ _ => exact False.elim hcond
  | vcut _ _ _ => exact False.elim hcond
  | rect j rot =>
    simp only [leafCond] at hcond
    subst hcond
    exact placeLeaf_rect_toSet hlv
  | nfdh a optb flip =>
    simp only [leafCond] at hcond
    exact (placeLeaf_nfdh_spec hlv hcond.1 hcond.2).1

lemma GTree.place_disjoint {x0 y0 x1 y1 : ℕ} {t : GTree} {k1 k2 : ℕ}
    (hv : t.valid x0 y0 x1 y1 = true)
    (hs1 : (t.leafAt x0 y0 x1 y1 k1).isSome = true)
    (hs2 : (t.leafAt x0 y0 x1 y1 k2).isSome = true)
    (hne : k1 ≠ k2) :
    interior (t.place x0 y0 x1 y1 k1).toSet ∩ interior (t.place x0 y0 x1 y1 k2).toSet = ∅ := by
  induction t generalizing x0 y0 x1 y1 with
  | empty => simp [GTree.leafAt] at hs1
  | rect j rot =>
    simp only [GTree.leafAt] at hs1 hs2
    split_ifs at hs1 with h1 <;> [skip; simp at hs1]
    split_ifs at hs2 with h2 <;> [skip; simp at hs2]
    exact False.elim (hne (h1.trans h2.symm))
  | nfdh a optb flip =>
    obtain ⟨v1, hl1⟩ := Option.isSome_iff_exists.mp hs1
    obtain ⟨v2, hl2⟩ := Option.isSome_iff_exists.mp hs2
    simp only [GTree.leafAt] at hl1 hl2
    split_ifs at hl1 with h1
    split_ifs at hl2 with h2
    simp only [GTree.place, GTree.leafAt, if_pos h1, if_pos h2]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
    have h1b : optbLt k1 optb := by
      cases optb with | none => trivial | some b => simp only [optbLt]; exact decide_eq_true_eq.mp h1.2
    have h2b : optbLt k2 optb := by
      cases optb with | none => trivial | some b => simp only [optbLt]; exact decide_eq_true_eq.mp h2.2
    exact (placeLeaf_nfdh_spec hv h1.1 h1b).2 k2 h2.1 h2b hne
  | hcut c l r ihl ihr =>
    simp only [GTree.valid, Bool.and_eq_true] at hv
    rcases hv with ⟨⟨_, hvl⟩, hvr⟩
    by_cases h1 : (l.leafAt x0 y0 c y1 k1).isSome = true <;>
      by_cases h2 : (l.leafAt x0 y0 c y1 k2).isSome = true
    · obtain ⟨v1, hl1⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨v2, hl2⟩ := Option.isSome_iff_exists.mp h2
      have hp1 : GTree.place x0 y0 x1 y1 (.hcut c l r) k1 = GTree.place x0 y0 c y1 l k1 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl1]
      have hp2 : GTree.place x0 y0 x1 y1 (.hcut c l r) k2 = GTree.place x0 y0 c y1 l k2 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl2]
      rw [hp1, hp2]
      exact ihl hvl h1 h2
    · obtain ⟨v1, hl1⟩ := Option.isSome_iff_exists.mp h1
      have hl2 : l.leafAt x0 y0 c y1 k2 = none := by
        cases hopt : l.leafAt x0 y0 c y1 k2 with
        | none => rfl
        | some w => exact absurd (by simp [hopt]) h2
      have hs2' : (r.leafAt c y0 x1 y1 k2).isSome = true := by
        simpa [GTree.leafAt, hl2] using hs2
      have hp1 : GTree.place x0 y0 x1 y1 (.hcut c l r) k1 = GTree.place x0 y0 c y1 l k1 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl1]
      have hp2 : GTree.place x0 y0 x1 y1 (.hcut c l r) k2 = GTree.place c y0 x1 y1 r k2 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl2]
      have hsub1 : (GTree.place x0 y0 x1 y1 (.hcut c l r) k1).toSet ⊆ boxOfN x0 y0 c y1 := by
        rw [hp1]; exact GTree.place_subset hvl h1
      have hsub2 : (GTree.place x0 y0 x1 y1 (.hcut c l r) k2).toSet ⊆ boxOfN c y0 x1 y1 := by
        rw [hp2]; exact GTree.place_subset hvr hs2'
      have hint1 := interior_mono hsub1
      have hint2 := interior_mono hsub2
      simp only [boxOfN, interior_boxSet] at hint1 hint2
      have hdisj : boxIntOfN x0 y0 c y1 ∩ boxIntOfN c y0 x1 y1 = ∅ :=
        boxInt_disjoint_of_x_le le_rfl
      ext p
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hp1', hp2'⟩
      have : p ∈ boxIntOfN x0 y0 c y1 ∩ boxIntOfN c y0 x1 y1 := ⟨hint1 hp1', hint2 hp2'⟩
      exact (Set.ext_iff.mp hdisj p).mp this
    · obtain ⟨v2, hl2⟩ := Option.isSome_iff_exists.mp h2
      have hl1 : l.leafAt x0 y0 c y1 k1 = none := by
        cases hopt : l.leafAt x0 y0 c y1 k1 with
        | none => rfl
        | some w => exact absurd (by simp [hopt]) h1
      have hs1' : (r.leafAt c y0 x1 y1 k1).isSome = true := by
        simpa [GTree.leafAt, hl1] using hs1
      have hp1 : GTree.place x0 y0 x1 y1 (.hcut c l r) k1 = GTree.place c y0 x1 y1 r k1 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl1]
      have hp2 : GTree.place x0 y0 x1 y1 (.hcut c l r) k2 = GTree.place x0 y0 c y1 l k2 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl2]
      have hsub1 : (GTree.place x0 y0 x1 y1 (.hcut c l r) k1).toSet ⊆ boxOfN c y0 x1 y1 := by
        rw [hp1]; exact GTree.place_subset hvr hs1'
      have hsub2 : (GTree.place x0 y0 x1 y1 (.hcut c l r) k2).toSet ⊆ boxOfN x0 y0 c y1 := by
        rw [hp2]; exact GTree.place_subset hvl h2
      have hint1 := interior_mono hsub1
      have hint2 := interior_mono hsub2
      simp only [boxOfN, interior_boxSet] at hint1 hint2
      have hdisj : boxIntOfN x0 y0 c y1 ∩ boxIntOfN c y0 x1 y1 = ∅ :=
        boxInt_disjoint_of_x_le le_rfl
      ext p
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hp1', hp2'⟩
      have : p ∈ boxIntOfN x0 y0 c y1 ∩ boxIntOfN c y0 x1 y1 := ⟨hint2 hp2', hint1 hp1'⟩
      exact (Set.ext_iff.mp hdisj p).mp this
    · have hl1 : l.leafAt x0 y0 c y1 k1 = none := by
        cases hopt : l.leafAt x0 y0 c y1 k1 with
        | none => rfl
        | some w => exact absurd (by simp [hopt]) h1
      have hl2 : l.leafAt x0 y0 c y1 k2 = none := by
        cases hopt : l.leafAt x0 y0 c y1 k2 with
        | none => rfl
        | some w => exact absurd (by simp [hopt]) h2
      have hs1' : (r.leafAt c y0 x1 y1 k1).isSome = true := by
        simpa [GTree.leafAt, hl1] using hs1
      have hs2' : (r.leafAt c y0 x1 y1 k2).isSome = true := by
        simpa [GTree.leafAt, hl2] using hs2
      have hp1 : GTree.place x0 y0 x1 y1 (.hcut c l r) k1 = GTree.place c y0 x1 y1 r k1 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl1]
      have hp2 : GTree.place x0 y0 x1 y1 (.hcut c l r) k2 = GTree.place c y0 x1 y1 r k2 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl2]
      rw [hp1, hp2]
      exact ihr hvr hs1' hs2'
  | vcut c l r ihl ihr =>
    simp only [GTree.valid, Bool.and_eq_true] at hv
    rcases hv with ⟨⟨_, hvl⟩, hvr⟩
    by_cases h1 : (l.leafAt x0 y0 x1 c k1).isSome = true <;>
      by_cases h2 : (l.leafAt x0 y0 x1 c k2).isSome = true
    · obtain ⟨v1, hl1⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨v2, hl2⟩ := Option.isSome_iff_exists.mp h2
      have hp1 : GTree.place x0 y0 x1 y1 (.vcut c l r) k1 = GTree.place x0 y0 x1 c l k1 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl1]
      have hp2 : GTree.place x0 y0 x1 y1 (.vcut c l r) k2 = GTree.place x0 y0 x1 c l k2 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl2]
      rw [hp1, hp2]
      exact ihl hvl h1 h2
    · obtain ⟨v1, hl1⟩ := Option.isSome_iff_exists.mp h1
      have hl2 : l.leafAt x0 y0 x1 c k2 = none := by
        cases hopt : l.leafAt x0 y0 x1 c k2 with
        | none => rfl
        | some w => exact absurd (by simp [hopt]) h2
      have hs2' : (r.leafAt x0 c x1 y1 k2).isSome = true := by
        simpa [GTree.leafAt, hl2] using hs2
      have hp1 : GTree.place x0 y0 x1 y1 (.vcut c l r) k1 = GTree.place x0 y0 x1 c l k1 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl1]
      have hp2 : GTree.place x0 y0 x1 y1 (.vcut c l r) k2 = GTree.place x0 c x1 y1 r k2 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl2]
      have hsub1 : (GTree.place x0 y0 x1 y1 (.vcut c l r) k1).toSet ⊆ boxOfN x0 y0 x1 c := by
        rw [hp1]; exact GTree.place_subset hvl h1
      have hsub2 : (GTree.place x0 y0 x1 y1 (.vcut c l r) k2).toSet ⊆ boxOfN x0 c x1 y1 := by
        rw [hp2]; exact GTree.place_subset hvr hs2'
      have hint1 := interior_mono hsub1
      have hint2 := interior_mono hsub2
      simp only [boxOfN, interior_boxSet] at hint1 hint2
      have hdisj : boxIntOfN x0 y0 x1 c ∩ boxIntOfN x0 c x1 y1 = ∅ :=
        boxInt_disjoint_of_y_le le_rfl
      ext p
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hp1', hp2'⟩
      have : p ∈ boxIntOfN x0 y0 x1 c ∩ boxIntOfN x0 c x1 y1 := ⟨hint1 hp1', hint2 hp2'⟩
      exact (Set.ext_iff.mp hdisj p).mp this
    · obtain ⟨v2, hl2⟩ := Option.isSome_iff_exists.mp h2
      have hl1 : l.leafAt x0 y0 x1 c k1 = none := by
        cases hopt : l.leafAt x0 y0 x1 c k1 with
        | none => rfl
        | some w => exact absurd (by simp [hopt]) h1
      have hs1' : (r.leafAt x0 c x1 y1 k1).isSome = true := by
        simpa [GTree.leafAt, hl1] using hs1
      have hp1 : GTree.place x0 y0 x1 y1 (.vcut c l r) k1 = GTree.place x0 c x1 y1 r k1 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl1]
      have hp2 : GTree.place x0 y0 x1 y1 (.vcut c l r) k2 = GTree.place x0 y0 x1 c l k2 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl2]
      have hsub1 : (GTree.place x0 y0 x1 y1 (.vcut c l r) k1).toSet ⊆ boxOfN x0 c x1 y1 := by
        rw [hp1]; exact GTree.place_subset hvr hs1'
      have hsub2 : (GTree.place x0 y0 x1 y1 (.vcut c l r) k2).toSet ⊆ boxOfN x0 y0 x1 c := by
        rw [hp2]; exact GTree.place_subset hvl h2
      have hint1 := interior_mono hsub1
      have hint2 := interior_mono hsub2
      simp only [boxOfN, interior_boxSet] at hint1 hint2
      have hdisj : boxIntOfN x0 y0 x1 c ∩ boxIntOfN x0 c x1 y1 = ∅ :=
        boxInt_disjoint_of_y_le le_rfl
      ext p
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hp1', hp2'⟩
      have : p ∈ boxIntOfN x0 y0 x1 c ∩ boxIntOfN x0 c x1 y1 := ⟨hint2 hp2', hint1 hp1'⟩
      exact (Set.ext_iff.mp hdisj p).mp this
    · have hl1 : l.leafAt x0 y0 x1 c k1 = none := by
        cases hopt : l.leafAt x0 y0 x1 c k1 with
        | none => rfl
        | some w => exact absurd (by simp [hopt]) h1
      have hl2 : l.leafAt x0 y0 x1 c k2 = none := by
        cases hopt : l.leafAt x0 y0 x1 c k2 with
        | none => rfl
        | some w => exact absurd (by simp [hopt]) h2
      have hs1' : (r.leafAt x0 c x1 y1 k1).isSome = true := by
        simpa [GTree.leafAt, hl1] using hs1
      have hs2' : (r.leafAt x0 c x1 y1 k2).isSome = true := by
        simpa [GTree.leafAt, hl2] using hs2
      have hp1 : GTree.place x0 y0 x1 y1 (.vcut c l r) k1 = GTree.place x0 c x1 y1 r k1 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl1]
      have hp2 : GTree.place x0 y0 x1 y1 (.vcut c l r) k2 = GTree.place x0 c x1 y1 r k2 := by
        rw [GTree.place, GTree.place, GTree.leafAt, hl2]
      rw [hp1, hp2]
      exact ihr hvr hs1' hs2'

lemma pack_of_valid_covers (t : GTree)
    (hv : t.valid 0 0 S_val S_val = true)
    (hc : t.covers = true) :
    ∃ c : Configuration,
      (∀ n, (c.rect n).toSet ⊆ Rectangle.toSet ⟨501/500, 501/500, (0, 0), 0⟩) ∧
      c.IsPacking := by
  have htarget : Rectangle.toSet ⟨501/500, 501/500, (0, 0), 0⟩ = boxOfN 0 0 S_val S_val := by
    rw [rect0_toSet (by norm_num) (by norm_num)]
    simp only [boxOfN, D_val, S_val]
    norm_num
  refine ⟨⟨fun n => t.place 0 0 S_val S_val (n + 1), fun n => ?_, fun n => ?_⟩, fun n => ?_, ?_⟩
  · rw [GTree.place_width]; push_cast; rfl
  · rw [GTree.place_height]; push_cast; ring_nf
  · rw [htarget]
    exact GTree.place_subset hv (leafAt_of_mem_intervals (covers_imp_mem hc (n + 1) (by omega)))
  · intro m n hmn
    have hs1 := leafAt_of_mem_intervals (x0 := 0) (y0 := 0) (x1 := S_val) (y1 := S_val)
      (covers_imp_mem hc (m + 1) (by omega))
    have hs2 := leafAt_of_mem_intervals (x0 := 0) (y0 := 0) (x1 := S_val) (y1 := S_val)
      (covers_imp_mem hc (n + 1) (by omega))
    exact GTree.place_disjoint hv hs1 hs2 (by omega)

/- ## Section 4: Explicit packing tree -/

def subTree_0 : GTree :=
  (.vcut 9048891
    (.hcut 5818404
      (.rect 177 false)
      (.empty))
    (.vcut 9104757
      (.hcut 5818086
        (.rect 178 false)
        (.empty))
      (.vcut 9160313
        (.hcut 5817772
          (.rect 179 false)
          (.empty))
        (.vcut 9215562
          (.hcut 5817462
            (.rect 180 false)
            (.empty))
          (.vcut 9270207
            (.hcut 5816852
              (.rect 182 false)
              (.empty))
            (.vcut 9324555
              (.hcut 5816551
                (.rect 183 false)
                (.empty))
              (.vcut 9378610
                (.hcut 5816254
                  (.rect 184 false)
                  (.empty))
                (.hcut 5815670
                  (.vcut 9432665
                    (.rect 185 true)
                    (.empty))
                  (.empty)))))))))

lemma subTree_0_ivs : subTree_0.intervalsAux [] = [(177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186)] := by
  rfl

def subTree_1 : GTree :=
  (.vcut 8992711
    (.hcut 5818725
      (.rect 176 false)
      (.empty))
    subTree_0)

lemma subTree_1_ivs : subTree_1.intervalsAux [] = [(176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186)] := by
  simp only [subTree_1, GTree.intervalsAux, subTree_0_ivs]
  try rfl

def subTree_2 : GTree :=
  (.vcut 8936213
    (.hcut 5819049
      (.rect 175 false)
      (.empty))
    subTree_1)

lemma subTree_2_ivs : subTree_2.intervalsAux [] = [(175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186)] := by
  simp only [subTree_2, GTree.intervalsAux, subTree_1_ivs]
  try rfl

def subTree_3 : GTree :=
  (.vcut 8879394
    (.hcut 5819378
      (.rect 174 false)
      (.empty))
    subTree_2)

lemma subTree_3_ivs : subTree_3.intervalsAux [] = [(174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186)] := by
  simp only [subTree_3, GTree.intervalsAux, subTree_2_ivs]
  try rfl

def subTree_4 : GTree :=
  (.vcut 8822251
    (.hcut 5820046
      (.rect 172 false)
      (.empty))
    subTree_3)

lemma subTree_4_ivs : subTree_4.intervalsAux [] = [(172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186)] := by
  simp only [subTree_4, GTree.intervalsAux, subTree_3_ivs]
  try rfl

def subTree_5 : GTree :=
  (.vcut 8764447
    (.hcut 5820386
      (.rect 171 false)
      (.empty))
    subTree_4)

lemma subTree_5_ivs : subTree_5.intervalsAux [] = [(171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186)] := by
  simp only [subTree_5, GTree.intervalsAux, subTree_4_ivs]
  try rfl

def subTree_6 : GTree :=
  (.vcut 8706307
    (.hcut 5820730
      (.rect 170 false)
      (.empty))
    subTree_5)

lemma subTree_6_ivs : subTree_6.intervalsAux [] = [(170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186)] := by
  simp only [subTree_6, GTree.intervalsAux, subTree_5_ivs]
  try rfl

def subTree_7 : GTree :=
  (.vcut 8647827
    (.hcut 5824406
      (.rect 160 false)
      (.empty))
    subTree_6)

lemma subTree_7_ivs : subTree_7.intervalsAux [] = [(160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186)] := by
  simp only [subTree_7, GTree.intervalsAux, subTree_6_ivs]
  try rfl

def subTree_8 : GTree :=
  (.vcut 8585715
    (.hcut 5824800
      (.rect 159 false)
      (.empty))
    subTree_7)

lemma subTree_8_ivs : subTree_8.intervalsAux [] = [(159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186)] := by
  simp only [subTree_8, GTree.intervalsAux, subTree_7_ivs]
  try rfl

def subTree_9 : GTree :=
  (.vcut 8523215
    (.hcut 5825198
      (.rect 158 false)
      (.empty))
    subTree_8)

lemma subTree_9_ivs : subTree_9.intervalsAux [] = [(158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186)] := by
  simp only [subTree_9, GTree.intervalsAux, subTree_8_ivs]
  try rfl

def subTree_10 : GTree :=
  (.vcut 8460321
    (.hcut 5825601
      (.rect 157 false)
      (.empty))
    subTree_9)

lemma subTree_10_ivs : subTree_10.intervalsAux [] = [(157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186)] := by
  simp only [subTree_10, GTree.intervalsAux, subTree_9_ivs]
  try rfl

def subTree_11 : GTree :=
  (.vcut 8397029
    (.hcut 5826009
      (.rect 156 false)
      (.empty))
    subTree_10)

lemma subTree_11_ivs : subTree_11.intervalsAux [] = [(156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186)] := by
  simp only [subTree_11, GTree.intervalsAux, subTree_10_ivs]
  try rfl

def subTree_12 : GTree :=
  (.hcut 5761906
    (.rect 9 true)
    subTree_11)

lemma subTree_12_ivs : subTree_12.intervalsAux [] = [(9, some 10), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186)] := by
  simp only [subTree_12, GTree.intervalsAux, subTree_11_ivs]
  try rfl

def subTree_13 : GTree :=
  (.hcut 5350142
    (.vcut 10000002
      (.rect 17 false)
      (.empty))
    (.vcut 9944446
      (.hcut 5826333
        (.rect 20 true)
        (.empty))
      (.hcut 5425900
        (.vcut 10019634
          (.rect 132 false)
          (.empty))
        (.hcut 5500527
          (.vcut 10019634
            (.rect 133 true)
            (.empty))
          (.hcut 5574602
            (.vcut 10019073
              (.rect 134 true)
              (.empty))
            (.hcut 5648132
              (.vcut 10018521
                (.rect 135 true)
                (.empty))
              (.hcut 5721125
                (.vcut 10017976
                  (.rect 136 true)
                  (.empty))
                (.hcut 5793589
                  (.vcut 10017439
                    (.rect 137 true)
                    (.empty))
                  (.nfdh 744 (some 753) false)))))))))

lemma subTree_13_ivs : subTree_13.intervalsAux [] = [(17, some 18), (20, some 21), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (136, some 137), (137, some 138), (744, some 753)] := by
  rfl

def subTree_14 : GTree :=
  (.vcut 9444446
    subTree_12
    subTree_13)

lemma subTree_14_ivs : subTree_14.intervalsAux [] = [(9, some 10), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186), (17, some 18), (20, some 21), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (136, some 137), (137, some 138), (744, some 753)] := by
  simp only [subTree_14, GTree.intervalsAux, intervalsAux_cons_eq_append, subTree_12_ivs, subTree_13_ivs]
  try rfl

def subTree_15 : GTree :=
  (.hcut 4761906
    (.vcut 10000001
      (.rect 6 true)
      (.empty))
    subTree_14)

lemma subTree_15_ivs : subTree_15.intervalsAux [] = [(6, some 7), (9, some 10), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186), (17, some 18), (20, some 21), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (136, some 137), (137, some 138), (744, some 753)] := by
  simp only [subTree_15, GTree.intervalsAux, subTree_14_ivs]
  try rfl

def subTree_16 : GTree :=
  (.vcut 8333334
    (.rect 3 true)
    subTree_15)

lemma subTree_16_ivs : subTree_16.intervalsAux [] = [(3, some 4), (6, some 7), (9, some 10), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186), (17, some 18), (20, some 21), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (136, some 137), (137, some 138), (744, some 753)] := by
  simp only [subTree_16, GTree.intervalsAux, subTree_15_ivs]
  try rfl

def subTree_17 : GTree :=
  (.hcut 6268117
    (.vcut 9994230
      (.rect 22 true)
      (.nfdh 903 (some 956) false))
    (.hcut 6684784
      (.vcut 9974467
        (.rect 23 true)
        (.nfdh 574 (some 613) false))
      (.vcut 9939684
        (.hcut 7069400
          (.rect 25 true)
          (.empty))
        (.hcut 6764150
          (.vcut 10019684
            (.rect 125 true)
            (.empty))
          (.hcut 6842891
            (.vcut 10019050
              (.rect 126 true)
              (.empty))
            (.hcut 6921016
              (.vcut 10018425
                (.rect 127 true)
                (.empty))
              (.hcut 6998536
                (.vcut 10017809
                  (.rect 128 true)
                  (.empty))
                (.hcut 7075460
                  (.vcut 10017204
                    (.rect 129 true)
                    (.empty))
                  (.empty)))))))))

lemma subTree_17_ivs : subTree_17.intervalsAux [] = [(22, some 23), (903, some 956), (23, some 24), (574, some 613), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130)] := by
  rfl

def subTree_18 : GTree :=
  (.vcut 9539684
    (.rect 8 false)
    subTree_17)

lemma subTree_18_ivs : subTree_18.intervalsAux [] = [(8, some 9), (22, some 23), (903, some 956), (23, some 24), (574, some 613), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130)] := by
  simp only [subTree_18, GTree.intervalsAux, subTree_17_ivs]
  try rfl

def subTree_19 : GTree :=
  (.vcut 8428572
    (.rect 7 true)
    subTree_18)

lemma subTree_19_ivs : subTree_19.intervalsAux [] = [(7, some 8), (8, some 9), (22, some 23), (903, some 956), (23, some 24), (574, some 613), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130)] := by
  simp only [subTree_19, GTree.intervalsAux, subTree_18_ivs]
  try rfl

def subTree_20 : GTree :=
  (.hcut 9187873
    (.vcut 7900902
      (.rect 148 true)
      (.empty))
    (.hcut 9254540
      (.vcut 7900449
        (.rect 149 true)
        (.empty))
      (.hcut 9320766
        (.vcut 7900001
          (.rect 150 true)
          (.empty))
        (.hcut 9386556
          (.vcut 7899560
            (.rect 151 true)
            (.empty))
          (.hcut 9451916
            (.vcut 7899124
              (.rect 152 true)
              (.empty))
            (.hcut 9516852
              (.vcut 7898694
                (.rect 153 true)
                (.empty))
              (.hcut 9581369
                (.vcut 7898270
                  (.rect 154 true)
                  (.empty))
                (.hcut 9645472
                  (.vcut 7897851
                    (.rect 155 true)
                    (.empty))
                  (.nfdh 762 (some 772) false)))))))))

lemma subTree_20_ivs : subTree_20.intervalsAux [] = [(148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772)] := by
  rfl

def subTree_21 : GTree :=
  (.hcut 9120758
    (.vcut 7901362
      (.rect 147 true)
      (.empty))
    subTree_20)

lemma subTree_21_ivs : subTree_21.intervalsAux [] = [(147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772)] := by
  simp only [subTree_21, GTree.intervalsAux, subTree_20_ivs]
  try rfl

def subTree_22 : GTree :=
  (.hcut 9053190
    (.vcut 7901828
      (.rect 146 true)
      (.empty))
    subTree_21)

lemma subTree_22_ivs : subTree_22.intervalsAux [] = [(146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772)] := by
  simp only [subTree_22, GTree.intervalsAux, subTree_21_ivs]
  try rfl

def subTree_23 : GTree :=
  (.hcut 8985162
    (.vcut 7902300
      (.rect 145 true)
      (.empty))
    subTree_22)

lemma subTree_23_ivs : subTree_23.intervalsAux [] = [(145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772)] := by
  simp only [subTree_23, GTree.intervalsAux, subTree_22_ivs]
  try rfl

def subTree_24 : GTree :=
  (.vcut 7833334
    (.rect 12 true)
    subTree_23)

lemma subTree_24_ivs : subTree_24.intervalsAux [] = [(12, some 13), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772)] := by
  simp only [subTree_24, GTree.intervalsAux, subTree_23_ivs]
  try rfl

def subTree_25 : GTree :=
  (.hcut 9685899
    subTree_24
    (.vcut 7344828
      (.hcut 10019233
        (.rect 29 true)
        (.empty))
      (.vcut 7667409
        (.hcut 10019233
          (.rect 30 false)
          (.empty))
        (.hcut 9929802
          (.vcut 7905505
            (.rect 41 false)
            (.empty))
          (.vcut 7758319
            (.hcut 10019893
              (.rect 110 true)
              (.empty))
            (.vcut 7847605
              (.hcut 10019893
                (.rect 111 false)
                (.empty))
              (.hcut 9991531
                (.vcut 7908955
                  (.rect 162 false)
                  (.empty))
                (.nfdh 984 (some 993) false))))))))

lemma subTree_25_ivs : subTree_25.intervalsAux [] = [(12, some 13), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772), (29, some 30), (30, some 31), (41, some 42), (110, some 111), (111, some 112), (162, some 163), (984, some 993)] := by
  simp only [subTree_25, GTree.intervalsAux, intervalsAux_cons_eq_append, subTree_24_ivs]
  try rfl

def subTree_26 : GTree :=
  (.hcut 8916668
    (.rect 11 true)
    subTree_25)

lemma subTree_26_ivs : subTree_26.intervalsAux [] = [(11, some 12), (12, some 13), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772), (29, some 30), (30, some 31), (41, some 42), (110, some 111), (111, some 112), (162, some 163), (984, some 993)] := by
  simp only [subTree_26, GTree.intervalsAux, subTree_25_ivs]
  try rfl

def subTree_27 : GTree :=
  (.hcut 8083334
    (.rect 10 false)
    subTree_26)

lemma subTree_27_ivs : subTree_27.intervalsAux [] = [(10, some 11), (11, some 12), (12, some 13), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772), (29, some 30), (30, some 31), (41, some 42), (110, some 111), (111, some 112), (162, some 163), (984, some 993)] := by
  simp only [subTree_27, GTree.intervalsAux, subTree_26_ivs]
  try rfl

def subTree_28 : GTree :=
  (.vcut 9430460
    (.hcut 7794541
      (.rect 116 false)
      (.empty))
    (.vcut 9515206
      (.hcut 7793805
        (.rect 117 false)
        (.empty))
      (.vcut 9599240
        (.hcut 7793080
          (.rect 118 false)
          (.empty))
        (.vcut 9682574
          (.hcut 7792368
            (.rect 119 false)
            (.empty))
          (.vcut 9765219
            (.hcut 7791668
              (.rect 120 false)
              (.empty))
            (.vcut 9847187
              (.hcut 7790979
                (.rect 121 false)
                (.empty))
              (.vcut 9928488
                (.hcut 7790302
                  (.rect 122 false)
                  (.empty))
                (.vcut 10009134
                  (.hcut 7789635
                    (.rect 123 false)
                    (.empty))
                  (.empty)))))))))

lemma subTree_28_ivs : subTree_28.intervalsAux [] = [(116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124)] := by
  rfl

def subTree_29 : GTree :=
  (.hcut 7708334
    (.vcut 10011656
      (.rect 15 true)
      (.empty))
    subTree_28)

lemma subTree_29_ivs : subTree_29.intervalsAux [] = [(15, some 16), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124)] := by
  simp only [subTree_29, GTree.intervalsAux, subTree_28_ivs]
  try rfl

def subTree_30 : GTree :=
  (.vcut 9344989
    (.rect 14 false)
    subTree_29)

lemma subTree_30_ivs : subTree_30.intervalsAux [] = [(14, some 15), (15, some 16), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124)] := by
  simp only [subTree_30, GTree.intervalsAux, subTree_29_ivs]
  try rfl

def subTree_31 : GTree :=
  (.vcut 8678322
    (.rect 13 true)
    subTree_30)

lemma subTree_31_ivs : subTree_31.intervalsAux [] = [(13, some 14), (14, some 15), (15, some 16), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124)] := by
  simp only [subTree_31, GTree.intervalsAux, subTree_30_ivs]
  try rfl

def subTree_32 : GTree :=
  (.vcut 9122519
    (.hcut 8385665
      (.rect 161 true)
      (.empty))
    (.vcut 9183495
      (.hcut 8385286
        (.rect 163 false)
        (.empty))
      (.vcut 9244102
        (.hcut 8384912
          (.rect 164 false)
          (.empty))
        (.vcut 9304343
          (.hcut 8384543
            (.rect 165 false)
            (.empty))
          (.vcut 9364224
            (.hcut 8384177
              (.rect 166 false)
              (.empty))
            (.vcut 9423748
              (.hcut 8383817
                (.rect 167 false)
                (.empty))
              (.vcut 9482920
                (.hcut 8383460
                  (.rect 168 false)
                  (.empty))
                (.vcut 9541744
                  (.hcut 8383108
                    (.rect 169 false)
                    (.empty))
                  (.empty)))))))))

lemma subTree_32_ivs : subTree_32.intervalsAux [] = [(161, some 162), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170)] := by
  rfl

def subTree_33 : GTree :=
  (.hcut 8323936
    (.rect 19 false)
    subTree_32)

lemma subTree_33_ivs : subTree_33.intervalsAux [] = [(19, some 20), (161, some 162), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170)] := by
  simp only [subTree_33, GTree.intervalsAux, subTree_32_ivs]
  try rfl

def subTree_34 : GTree :=
  (.vcut 9560407
    subTree_33
    (.hcut 8273811
      (.vcut 10014953
        (.rect 21 false)
        (.empty))
      (.vcut 9669103
        (.hcut 8383702
          (.rect 91 false)
          (.empty))
        (.vcut 9772196
          (.hcut 8377978
            (.rect 96 false)
            (.empty))
          (.vcut 9874237
            (.hcut 8376904
              (.rect 97 false)
              (.empty))
            (.vcut 9975248
              (.hcut 8375852
                (.rect 98 false)
                (.empty))
              (.nfdh 647 (some 659) false)))))))

lemma subTree_34_ivs : subTree_34.intervalsAux [] = [(19, some 20), (161, some 162), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (21, some 22), (91, some 92), (96, some 97), (97, some 98), (98, some 99), (647, some 659)] := by
  simp only [subTree_34, GTree.intervalsAux, intervalsAux_cons_eq_append, subTree_33_ivs]
  try rfl

def subTree_35 : GTree :=
  (.vcut 9060407
    (.hcut 8353176
      (.rect 18 false)
      (.nfdh 696 (some 744) false))
    subTree_34)

lemma subTree_35_ivs : subTree_35.intervalsAux [] = [(18, some 19), (696, some 744), (19, some 20), (161, some 162), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (21, some 22), (91, some 92), (96, some 97), (97, some 98), (98, some 99), (647, some 659)] := by
  simp only [subTree_35, GTree.intervalsAux, subTree_34_ivs]
  try rfl

def subTree_36 : GTree :=
  (.vcut 8534091
    (.rect 16 true)
    subTree_35)

lemma subTree_36_ivs : subTree_36.intervalsAux [] = [(16, some 17), (18, some 19), (696, some 744), (19, some 20), (161, some 162), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (21, some 22), (91, some 92), (96, some 97), (97, some 98), (98, some 99), (647, some 659)] := by
  simp only [subTree_36, GTree.intervalsAux, subTree_35_ivs]
  try rfl

def subTree_37 : GTree :=
  (.vcut 9513682
    (.rect 131 false)
    (.vcut 9585625
      (.hcut 9356502
        (.rect 138 false)
        (.empty))
      (.vcut 9657054
        (.hcut 9355981
          (.rect 139 false)
          (.empty))
        (.vcut 9727976
          (.hcut 9355467
            (.rect 140 false)
            (.empty))
          (.vcut 9798399
            (.hcut 9354960
              (.rect 141 false)
              (.empty))
            (.vcut 9868330
              (.hcut 9354461
                (.rect 142 false)
                (.empty))
              (.vcut 9937775
                (.hcut 9353969
                  (.rect 143 false)
                  (.empty))
                (.vcut 10006741
                  (.hcut 9353483
                    (.rect 144 false)
                    (.empty))
                  (.empty)))))))))

lemma subTree_37_ivs : subTree_37.intervalsAux [] = [(131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145)] := by
  rfl

def subTree_38 : GTree :=
  (.vcut 9437924
    (.rect 130 true)
    subTree_37)

lemma subTree_38_ivs : subTree_38.intervalsAux [] = [(130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145)] := by
  simp only [subTree_38, GTree.intervalsAux, subTree_37_ivs]
  try rfl

def subTree_39 : GTree :=
  (.vcut 9625856
    (.hcut 9413006
      (.rect 190 false)
      (.empty))
    (.vcut 9677940
      (.hcut 9412731
        (.rect 191 false)
        (.empty))
      (.vcut 9729754
        (.hcut 9412458
          (.rect 192 false)
          (.empty))
        (.vcut 9781301
          (.hcut 9412188
            (.rect 193 false)
            (.empty))
          (.vcut 9832584
            (.hcut 9411921
              (.rect 194 false)
              (.empty))
            (.vcut 9883605
              (.hcut 9411657
                (.rect 195 false)
                (.empty))
              (.vcut 9934367
                (.hcut 9411395
                  (.rect 196 false)
                  (.empty))
                (.vcut 9984873
                  (.hcut 9411136
                    (.rect 197 false)
                    (.empty))
                  (.nfdh 956 (some 965) false)))))))))

lemma subTree_39_ivs : subTree_39.intervalsAux [] = [(190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965)] := by
  rfl

def subTree_40 : GTree :=
  (.vcut 9573499
    (.hcut 9413285
      (.rect 189 false)
      (.empty))
    subTree_39)

lemma subTree_40_ivs : subTree_40.intervalsAux [] = [(189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965)] := by
  simp only [subTree_40, GTree.intervalsAux, subTree_39_ivs]
  try rfl

def subTree_41 : GTree :=
  (.vcut 9520867
    (.hcut 9413566
      (.rect 188 false)
      (.empty))
    subTree_40)

lemma subTree_41_ivs : subTree_41.intervalsAux [] = [(188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965)] := by
  simp only [subTree_41, GTree.intervalsAux, subTree_40_ivs]
  try rfl

def subTree_42 : GTree :=
  (.vcut 9467956
    (.rect 187 false)
    subTree_41)

lemma subTree_42_ivs : subTree_42.intervalsAux [] = [(187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965)] := by
  simp only [subTree_42, GTree.intervalsAux, subTree_41_ivs]
  try rfl

def subTree_43 : GTree :=
  (.vcut 9414764
    (.rect 186 true)
    subTree_42)

lemma subTree_43_ivs : subTree_43.intervalsAux [] = [(186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965)] := by
  simp only [subTree_43, GTree.intervalsAux, subTree_42_ivs]
  try rfl

def subTree_44 : GTree :=
  (.hcut 9413850
    subTree_43
    (.vcut 9411252
      (.hcut 9464356
        (.rect 198 false)
        (.hcut 9514356
          (.rect 199 true)
          (.nfdh 528 (some 574) false)))
      (.nfdh 200 (some 528) false)))

lemma subTree_44_ivs : subTree_44.intervalsAux [] = [(186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_44, GTree.intervalsAux, intervalsAux_cons_eq_append, subTree_43_ivs]
  try rfl

def subTree_45 : GTree :=
  (.hcut 9360374
    subTree_38
    subTree_44)

lemma subTree_45_ivs : subTree_45.intervalsAux [] = [(130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_45, GTree.intervalsAux, intervalsAux_cons_eq_append, subTree_38_ivs, subTree_44_ivs]
  try rfl

def subTree_46 : GTree :=
  (.vcut 9361000
    (.hcut 9378378
      (.rect 106 false)
      (.hcut 9470971
        (.rect 107 true)
        (.hcut 9562715
          (.vcut 9360135
            (.rect 108 true)
            (.empty))
          (.hcut 9653625
            (.vcut 9359286
              (.rect 109 true)
              (.empty))
            (.hcut 9742121
              (.vcut 9356828
                (.rect 112 true)
                (.empty))
              (.hcut 9829841
                (.vcut 9356038
                  (.rect 113 true)
                  (.empty))
                (.hcut 9916798
                  (.vcut 9355262
                    (.rect 114 true)
                    (.empty))
                  (.hcut 10003005
                    (.vcut 9354499
                      (.rect 115 true)
                      (.empty))
                    (.empty)))))))))
    subTree_45)

lemma subTree_46_ivs : subTree_46.intervalsAux [] = [(106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_46, GTree.intervalsAux, subTree_45_ivs]
  try rfl

def subTree_47 : GTree :=
  (.vcut 9267542
    (.hcut 9385049
      (.rect 99 false)
      (.hcut 9484059
        (.rect 100 true)
        (.hcut 9582099
          (.vcut 9266552
            (.rect 101 true)
            (.empty))
          (.hcut 9679187
            (.vcut 9265582
              (.rect 102 true)
              (.empty))
            (.hcut 9775341
              (.vcut 9264630
                (.rect 103 true)
                (.empty))
              (.hcut 9870580
                (.vcut 9263696
                  (.rect 104 true)
                  (.empty))
                (.hcut 9964920
                  (.vcut 9262781
                    (.rect 105 true)
                    (.empty))
                  (.vcut 9222791
                    (.hcut 10019866
                      (.rect 181 true)
                      (.empty))
                    (.nfdh 772 (some 780) false)))))))))
    subTree_46)

lemma subTree_47_ivs : subTree_47.intervalsAux [] = [(99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_47, GTree.intervalsAux, subTree_46_ivs]
  try rfl

def subTree_48 : GTree :=
  (.hcut 9284038
    (.vcut 9288024
      (.rect 83 true)
      (.vcut 9405672
        (.rect 84 false)
        (.vcut 9521952
          (.hcut 9282638
            (.rect 85 false)
            (.empty))
          (.vcut 9636895
            (.hcut 9281270
              (.rect 86 false)
              (.empty))
            (.vcut 9750532
              (.hcut 9279933
                (.rect 87 false)
                (.empty))
              (.vcut 9862892
                (.hcut 9278627
                  (.rect 88 false)
                  (.empty))
                (.vcut 9974004
                  (.hcut 9277350
                    (.rect 89 false)
                    (.empty))
                  (.nfdh 659 (some 673) false))))))))
    subTree_47)

lemma subTree_48_ivs : subTree_48.intervalsAux [] = [(83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_48, GTree.intervalsAux, subTree_47_ivs]
  try rfl

def subTree_49 : GTree :=
  (.vcut 9167542
    (.hcut 9294861
      (.rect 77 false)
      (.hcut 9421444
        (.rect 78 true)
        (.hcut 9546444
          (.vcut 9165919
            (.rect 79 true)
            (.empty))
          (.hcut 9669901
            (.vcut 9164336
              (.rect 80 true)
              (.empty))
            (.hcut 9791853
              (.vcut 9162793
                (.rect 81 true)
                (.empty))
              (.hcut 9912335
                (.vcut 9161288
                  (.rect 82 true)
                  (.empty))
                (.vcut 9148032
                  (.hcut 10019862
                    (.rect 92 true)
                    (.empty))
                  (.empty))))))))
    subTree_48)

lemma subTree_49_ivs : subTree_49.intervalsAux [] = [(77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_49, GTree.intervalsAux, subTree_48_ivs]
  try rfl

def subTree_50 : GTree :=
  (.hcut 9164990
    (.vcut 9182194
      (.rect 70 true)
      (.vcut 9321083
        (.rect 71 false)
        (.vcut 9458070
          (.hcut 9163033
            (.rect 72 false)
            (.empty))
          (.vcut 9593206
            (.hcut 9161131
              (.rect 73 false)
              (.empty))
            (.vcut 9726540
              (.hcut 9159280
                (.rect 74 false)
                (.empty))
              (.vcut 9858119
                (.hcut 9157478
                  (.rect 75 false)
                  (.empty))
                (.vcut 9987990
                  (.hcut 9155723
                    (.rect 76 false)
                    (.empty))
                  (.nfdh 852 (some 871) false))))))))
    subTree_49)

lemma subTree_50_ivs : subTree_50.intervalsAux [] = [(70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_50, GTree.intervalsAux, subTree_49_ivs]
  try rfl

def subTree_51 : GTree :=
  (.hcut 9024144
    (.vcut 9206003
      (.rect 60 true)
      (.vcut 9367294
        (.rect 61 false)
        (.vcut 9526025
          (.hcut 9021500
            (.rect 62 false)
            (.empty))
          (.vcut 9682275
            (.hcut 9018940
              (.rect 63 false)
              (.empty))
            (.vcut 9836122
              (.hcut 9016459
                (.rect 64 false)
                (.empty))
              (.vcut 9987638
                (.hcut 9014056
                  (.rect 65 false)
                  (.empty))
                (.nfdh 780 (some 798) false)))))))
    subTree_50)

lemma subTree_51_ivs : subTree_51.intervalsAux [] = [(60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (780, some 798), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_51, GTree.intervalsAux, subTree_50_ivs]
  try rfl

def subTree_52 : GTree :=
  (.vcut 9039336
    (.hcut 9048889
      (.rect 53 false)
      (.hcut 9230708
        (.rect 54 true)
        (.hcut 9406147
          (.vcut 9032722
            (.rect 56 true)
            (.empty))
          (.hcut 9578561
            (.vcut 9029589
              (.rect 57 true)
              (.empty))
            (.hcut 9748053
              (.vcut 9026564
                (.rect 58 true)
                (.empty))
              (.hcut 9914720
                (.vcut 9023642
                  (.rect 59 true)
                  (.empty))
                (.vcut 8958317
                  (.hcut 10019984
                    (.rect 95 false)
                    (.empty))
                  (.hcut 9994720
                    (.vcut 9038963
                      (.rect 124 true)
                      (.empty))
                    (.nfdh 1954 (some 2014) false)))))))))
    subTree_51)

lemma subTree_52_ivs : subTree_52.intervalsAux [] = [(53, some 54), (54, some 55), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (95, some 96), (124, some 125), (1954, some 2014), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (780, some 798), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_52, GTree.intervalsAux, subTree_51_ivs]
  try rfl

def subTree_53 : GTree :=
  (.hcut 8860209
    (.vcut 9062484
      (.rect 48 true)
      (.vcut 9262484
        (.rect 49 false)
        (.vcut 9458563
          (.hcut 8856127
            (.rect 50 false)
            (.empty))
          (.vcut 9650871
            (.hcut 8852206
              (.rect 51 false)
              (.empty))
            (.vcut 9839551
              (.hcut 8848435
                (.rect 52 false)
                (.empty))
              (.hcut 8837946
                (.vcut 10018123
                  (.rect 55 false)
                  (.empty))
                (.nfdh 965 (some 984) false)))))))
    subTree_52)

lemma subTree_53_ivs : subTree_53.intervalsAux [] = [(48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (55, some 56), (965, some 984), (53, some 54), (54, some 55), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (95, some 96), (124, some 125), (1954, some 2014), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (780, some 798), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_53, GTree.intervalsAux, subTree_52_ivs]
  try rfl

def subTree_54 : GTree :=
  (.vcut 8854150
    (.hcut 8894223
      (.rect 42 false)
      (.hcut 9121496
        (.rect 43 true)
        (.hcut 9343719
          (.vcut 8848864
            (.rect 44 true)
            (.empty))
          (.hcut 9561111
            (.vcut 8843814
              (.rect 45 true)
              (.empty))
            (.hcut 9773877
              (.vcut 8838983
                (.rect 46 true)
                (.empty))
              (.hcut 9982211
                (.vcut 8834357
                  (.rect 47 true)
                  (.empty))
                (.nfdh 673 (some 696) false)))))))
    subTree_53)

lemma subTree_54_ivs : subTree_54.intervalsAux [] = [(42, some 43), (43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (673, some 696), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (55, some 56), (965, some 984), (53, some 54), (54, some 55), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (95, some 96), (124, some 125), (1954, some 2014), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (780, some 798), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_54, GTree.intervalsAux, subTree_53_ivs]
  try rfl

def subTree_55 : GTree :=
  (.hcut 8656127
    (.vcut 8899369
      (.rect 36 true)
      (.vcut 9162527
        (.rect 37 false)
        (.vcut 9418938
          (.hcut 8649014
            (.rect 38 false)
            (.empty))
          (.vcut 9668938
            (.hcut 8642267
              (.rect 39 false)
              (.empty))
            (.vcut 9912841
              (.hcut 8635856
                (.rect 40 false)
                (.empty))
              (.hcut 8493383
                (.vcut 10019224
                  (.rect 93 false)
                  (.empty))
                (.hcut 8598647
                  (.vcut 10019224
                    (.rect 94 true)
                    (.empty))
                  (.vcut 9970645
                    (.hcut 8656119
                      (.rect 173 true)
                      (.empty))
                    (.nfdh 753 (some 762) false)))))))))
    subTree_54)

lemma subTree_55_ivs : subTree_55.intervalsAux [] = [(36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (93, some 94), (94, some 95), (173, some 174), (753, some 762), (42, some 43), (43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (673, some 696), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (55, some 56), (965, some 984), (53, some 54), (54, some 55), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (95, some 96), (124, some 125), (1954, some 2014), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (780, some 798), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_55, GTree.intervalsAux, subTree_54_ivs]
  try rfl

def subTree_56 : GTree :=
  (.vcut 8621591
    (.hcut 8708437
      (.rect 31 false)
      (.hcut 9011468
        (.rect 32 true)
        (.hcut 9305586
          (.vcut 8612122
            (.rect 33 true)
            (.empty))
          (.hcut 9591301
            (.vcut 8603209
              (.rect 34 true)
              (.empty))
            (.hcut 9869079
              (.vcut 8594806
                (.rect 35 true)
                (.nfdh 871 (some 903) false))
              (.vcut 8460607
                (.hcut 10018333
                  (.rect 66 true)
                  (.empty))
                (.vcut 8607666
                  (.hcut 10018333
                    (.rect 67 false)
                    (.empty))
                  (.empty))))))))
    subTree_55)

lemma subTree_56_ivs : subTree_56.intervalsAux [] = [(31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (871, some 903), (66, some 67), (67, some 68), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (93, some 94), (94, some 95), (173, some 174), (753, some 762), (42, some 43), (43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (673, some 696), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (55, some 56), (965, some 984), (53, some 54), (54, some 55), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (95, some 96), (124, some 125), (1954, some 2014), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (780, some 798), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_56, GTree.intervalsAux, subTree_55_ivs]
  try rfl

def subTree_57 : GTree :=
  (.vcut 8309091
    (.hcut 8802523
      (.rect 24 false)
      (.hcut 9172894
        (.vcut 8293707
          (.rect 26 true)
          (.empty))
        (.hcut 9530037
          (.vcut 8279462
            (.rect 27 true)
            (.nfdh 798 (some 837) false))
          (.hcut 9874865
            (.vcut 8266234
              (.rect 28 true)
              (.nfdh 613 (some 647) false))
            (.vcut 8056150
              (.hcut 10019793
                (.rect 68 true)
                (.empty))
              (.vcut 8199008
                (.hcut 10019793
                  (.rect 69 false)
                  (.empty))
                (.hcut 9985977
                  (.vcut 8308899
                    (.rect 90 false)
                    (.empty))
                  (.nfdh 837 (some 852) false))))))))
    subTree_56)

lemma subTree_57_ivs : subTree_57.intervalsAux [] = [(24, some 25), (26, some 27), (27, some 28), (798, some 837), (28, some 29), (613, some 647), (68, some 69), (69, some 70), (90, some 91), (837, some 852), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (871, some 903), (66, some 67), (67, some 68), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (93, some 94), (94, some 95), (173, some 174), (753, some 762), (42, some 43), (43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (673, some 696), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (55, some 56), (965, some 984), (53, some 54), (54, some 55), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (95, some 96), (124, some 125), (1954, some 2014), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (780, some 798), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_57, GTree.intervalsAux, subTree_56_ivs]
  try rfl

def subTree_58 : GTree :=
  (.hcut 8385856
    subTree_36
    subTree_57)

lemma subTree_58_ivs : subTree_58.intervalsAux [] = [(16, some 17), (18, some 19), (696, some 744), (19, some 20), (161, some 162), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (21, some 22), (91, some 92), (96, some 97), (97, some 98), (98, some 99), (647, some 659), (24, some 25), (26, some 27), (27, some 28), (798, some 837), (28, some 29), (613, some 647), (68, some 69), (69, some 70), (90, some 91), (837, some 852), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (871, some 903), (66, some 67), (67, some 68), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (93, some 94), (94, some 95), (173, some 174), (753, some 762), (42, some 43), (43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (673, some 696), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (55, some 56), (965, some 984), (53, some 54), (54, some 55), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (95, some 96), (124, some 125), (1954, some 2014), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (780, some 798), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_58, GTree.intervalsAux, intervalsAux_cons_eq_append, subTree_36_ivs, subTree_57_ivs]
  try rfl

def subTree_59 : GTree :=
  (.hcut 7797620
    subTree_31
    subTree_58)

lemma subTree_59_ivs : subTree_59.intervalsAux [] = [(13, some 14), (14, some 15), (15, some 16), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124), (16, some 17), (18, some 19), (696, some 744), (19, some 20), (161, some 162), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (21, some 22), (91, some 92), (96, some 97), (97, some 98), (98, some 99), (647, some 659), (24, some 25), (26, some 27), (27, some 28), (798, some 837), (28, some 29), (613, some 647), (68, some 69), (69, some 70), (90, some 91), (837, some 852), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (871, some 903), (66, some 67), (67, some 68), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (93, some 94), (94, some 95), (173, some 174), (753, some 762), (42, some 43), (43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (673, some 696), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (55, some 56), (965, some 984), (53, some 54), (54, some 55), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (95, some 96), (124, some 125), (1954, some 2014), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (780, some 798), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_59, GTree.intervalsAux, intervalsAux_cons_eq_append, subTree_31_ivs, subTree_58_ivs]
  try rfl

def subTree_60 : GTree :=
  (.vcut 7909091
    subTree_27
    subTree_59)

lemma subTree_60_ivs : subTree_60.intervalsAux [] = [(10, some 11), (11, some 12), (12, some 13), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772), (29, some 30), (30, some 31), (41, some 42), (110, some 111), (111, some 112), (162, some 163), (984, some 993), (13, some 14), (14, some 15), (15, some 16), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124), (16, some 17), (18, some 19), (696, some 744), (19, some 20), (161, some 162), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (21, some 22), (91, some 92), (96, some 97), (97, some 98), (98, some 99), (647, some 659), (24, some 25), (26, some 27), (27, some 28), (798, some 837), (28, some 29), (613, some 647), (68, some 69), (69, some 70), (90, some 91), (837, some 852), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (871, some 903), (66, some 67), (67, some 68), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (93, some 94), (94, some 95), (173, some 174), (753, some 762), (42, some 43), (43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (673, some 696), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (55, some 56), (965, some 984), (53, some 54), (54, some 55), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (95, some 96), (124, some 125), (1954, some 2014), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (780, some 798), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_60, GTree.intervalsAux, intervalsAux_cons_eq_append, subTree_27_ivs, subTree_59_ivs]
  try rfl

def subTree_61 : GTree :=
  (.hcut 7083334
    subTree_19
    subTree_60)

lemma subTree_61_ivs : subTree_61.intervalsAux [] = [(7, some 8), (8, some 9), (22, some 23), (903, some 956), (23, some 24), (574, some 613), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130), (10, some 11), (11, some 12), (12, some 13), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772), (29, some 30), (30, some 31), (41, some 42), (110, some 111), (111, some 112), (162, some 163), (984, some 993), (13, some 14), (14, some 15), (15, some 16), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124), (16, some 17), (18, some 19), (696, some 744), (19, some 20), (161, some 162), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (21, some 22), (91, some 92), (96, some 97), (97, some 98), (98, some 99), (647, some 659), (24, some 25), (26, some 27), (27, some 28), (798, some 837), (28, some 29), (613, some 647), (68, some 69), (69, some 70), (90, some 91), (837, some 852), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (871, some 903), (66, some 67), (67, some 68), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (93, some 94), (94, some 95), (173, some 174), (753, some 762), (42, some 43), (43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (673, some 696), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (55, some 56), (965, some 984), (53, some 54), (54, some 55), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (95, some 96), (124, some 125), (1954, some 2014), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (780, some 798), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_61, GTree.intervalsAux, intervalsAux_cons_eq_append, subTree_19_ivs, subTree_60_ivs]
  try rfl

def subTree_62 : GTree :=
  (.vcut 7000000
    (.hcut 8333334
      (.rect 4 false)
      (.hcut 10000001
        (.rect 5 true)
        (.empty)))
    subTree_61)

lemma subTree_62_ivs : subTree_62.intervalsAux [] = [(4, some 5), (5, some 6), (7, some 8), (8, some 9), (22, some 23), (903, some 956), (23, some 24), (574, some 613), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130), (10, some 11), (11, some 12), (12, some 13), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772), (29, some 30), (30, some 31), (41, some 42), (110, some 111), (111, some 112), (162, some 163), (984, some 993), (13, some 14), (14, some 15), (15, some 16), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124), (16, some 17), (18, some 19), (696, some 744), (19, some 20), (161, some 162), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (21, some 22), (91, some 92), (96, some 97), (97, some 98), (98, some 99), (647, some 659), (24, some 25), (26, some 27), (27, some 28), (798, some 837), (28, some 29), (613, some 647), (68, some 69), (69, some 70), (90, some 91), (837, some 852), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (871, some 903), (66, some 67), (67, some 68), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (93, some 94), (94, some 95), (173, some 174), (753, some 762), (42, some 43), (43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (673, some 696), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (55, some 56), (965, some 984), (53, some 54), (54, some 55), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (95, some 96), (124, some 125), (1954, some 2014), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (780, some 798), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_62, GTree.intervalsAux, subTree_61_ivs]
  try rfl

def subTree_63 : GTree :=
  (.hcut 5833334
    subTree_16
    subTree_62)

lemma subTree_63_ivs : subTree_63.intervalsAux [] = [(3, some 4), (6, some 7), (9, some 10), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186), (17, some 18), (20, some 21), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (136, some 137), (137, some 138), (744, some 753), (4, some 5), (5, some 6), (7, some 8), (8, some 9), (22, some 23), (903, some 956), (23, some 24), (574, some 613), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130), (10, some 11), (11, some 12), (12, some 13), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772), (29, some 30), (30, some 31), (41, some 42), (110, some 111), (111, some 112), (162, some 163), (984, some 993), (13, some 14), (14, some 15), (15, some 16), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124), (16, some 17), (18, some 19), (696, some 744), (19, some 20), (161, some 162), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (21, some 22), (91, some 92), (96, some 97), (97, some 98), (98, some 99), (647, some 659), (24, some 25), (26, some 27), (27, some 28), (798, some 837), (28, some 29), (613, some 647), (68, some 69), (69, some 70), (90, some 91), (837, some 852), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (871, some 903), (66, some 67), (67, some 68), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (93, some 94), (94, some 95), (173, some 174), (753, some 762), (42, some 43), (43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (673, some 696), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (55, some 56), (965, some 984), (53, some 54), (54, some 55), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (95, some 96), (124, some 125), (1954, some 2014), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (780, some 798), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_63, GTree.intervalsAux, intervalsAux_cons_eq_append, subTree_16_ivs, subTree_62_ivs]
  try rfl

def subTree_64 : GTree :=
  (.hcut 3333334
    (.vcut 10000000
      (.rect 2 true)
      (.nfdh 2014 none false))
    subTree_63)

lemma subTree_64_ivs : subTree_64.intervalsAux [] = [(2, some 3), (2014, none), (3, some 4), (6, some 7), (9, some 10), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186), (17, some 18), (20, some 21), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (136, some 137), (137, some 138), (744, some 753), (4, some 5), (5, some 6), (7, some 8), (8, some 9), (22, some 23), (903, some 956), (23, some 24), (574, some 613), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130), (10, some 11), (11, some 12), (12, some 13), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772), (29, some 30), (30, some 31), (41, some 42), (110, some 111), (111, some 112), (162, some 163), (984, some 993), (13, some 14), (14, some 15), (15, some 16), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124), (16, some 17), (18, some 19), (696, some 744), (19, some 20), (161, some 162), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (21, some 22), (91, some 92), (96, some 97), (97, some 98), (98, some 99), (647, some 659), (24, some 25), (26, some 27), (27, some 28), (798, some 837), (28, some 29), (613, some 647), (68, some 69), (69, some 70), (90, some 91), (837, some 852), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (871, some 903), (66, some 67), (67, some 68), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (93, some 94), (94, some 95), (173, some 174), (753, some 762), (42, some 43), (43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (673, some 696), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (55, some 56), (965, some 984), (53, some 54), (54, some 55), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (95, some 96), (124, some 125), (1954, some 2014), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (780, some 798), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)] := by
  simp only [subTree_64, GTree.intervalsAux, subTree_63_ivs]
  try rfl

def rootTree : GTree :=
  .vcut 5000000
    (.hcut 10000000
      (.rect 1 false)
      (.nfdh 993 (some 1954) false))
    subTree_64

def rootIvs : List (ℕ × Option ℕ) :=
  [(1, some 2), (993, some 1954), (2, some 3), (2014, none), (3, some 4), (6, some 7), (9, some 10), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186), (17, some 18), (20, some 21), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (136, some 137), (137, some 138), (744, some 753), (4, some 5), (5, some 6), (7, some 8), (8, some 9), (22, some 23), (903, some 956), (23, some 24), (574, some 613), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130), (10, some 11), (11, some 12), (12, some 13), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772), (29, some 30), (30, some 31), (41, some 42), (110, some 111), (111, some 112), (162, some 163), (984, some 993), (13, some 14), (14, some 15), (15, some 16), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124), (16, some 17), (18, some 19), (696, some 744), (19, some 20), (161, some 162), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (21, some 22), (91, some 92), (96, some 97), (97, some 98), (98, some 99), (647, some 659), (24, some 25), (26, some 27), (27, some 28), (798, some 837), (28, some 29), (613, some 647), (68, some 69), (69, some 70), (90, some 91), (837, some 852), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (871, some 903), (66, some 67), (67, some 68), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (93, some 94), (94, some 95), (173, some 174), (753, some 762), (42, some 43), (43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (673, some 696), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (55, some 56), (965, some 984), (53, some 54), (54, some 55), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (95, some 96), (124, some 125), (1954, some 2014), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (780, some 798), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (852, some 871), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (92, some 93), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (659, some 673), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (181, some 182), (772, some 780), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (956, some 965), (198, some 199), (199, some 200), (528, some 574), (200, some 528)]

def sortedIvs : List (ℕ × Option ℕ) :=
  [(1, some 2), (2, some 3), (3, some 4), (4, some 5), (5, some 6), (6, some 7), (7, some 8), (8, some 9), (9, some 10), (10, some 11), (11, some 12), (12, some 13), (13, some 14), (14, some 15), (15, some 16), (16, some 17), (17, some 18), (18, some 19), (19, some 20), (20, some 21), (21, some 22), (22, some 23), (23, some 24), (24, some 25), (25, some 26), (26, some 27), (27, some 28), (28, some 29), (29, some 30), (30, some 31), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (41, some 42), (42, some 43), (43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (53, some 54), (54, some 55), (55, some 56), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (66, some 67), (67, some 68), (68, some 69), (69, some 70), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (90, some 91), (91, some 92), (92, some 93), (93, some 94), (94, some 95), (95, some 96), (96, some 97), (97, some 98), (98, some 99), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (110, some 111), (111, some 112), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124), (124, some 125), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130), (130, some 131), (131, some 132), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (136, some 137), (137, some 138), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (161, some 162), (162, some 163), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (170, some 171), (171, some 172), (172, some 173), (173, some 174), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (181, some 182), (182, some 183), (183, some 184), (184, some 185), (185, some 186), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (198, some 199), (199, some 200), (200, some 528), (528, some 574), (574, some 613), (613, some 647), (647, some 659), (659, some 673), (673, some 696), (696, some 744), (744, some 753), (753, some 762), (762, some 772), (772, some 780), (780, some 798), (798, some 837), (837, some 852), (852, some 871), (871, some 903), (903, some 956), (956, some 965), (965, some 984), (984, some 993), (993, some 1954), (1954, some 2014), (2014, none)]

lemma rootTree_ivs : rootTree.intervals = rootIvs := by
  simp only [GTree.intervals, rootTree, GTree.intervalsAux, subTree_64_ivs]
  try rfl

set_option maxRecDepth 2000 in
lemma sortPairs_rootIvs : sortPairs rootIvs = sortedIvs := by
  have h0 : rootIvs.map (fun x => [x]) = [[(1, some 2)], [(993, some 1954)], [(2, some 3)], [(2014, none)], [(3, some 4)], [(6, some 7)], [(9, some 10)], [(156, some 157)], [(157, some 158)], [(158, some 159)], [(159, some 160)], [(160, some 161)], [(170, some 171)], [(171, some 172)], [(172, some 173)], [(174, some 175)], [(175, some 176)], [(176, some 177)], [(177, some 178)], [(178, some 179)], [(179, some 180)], [(180, some 181)], [(182, some 183)], [(183, some 184)], [(184, some 185)], [(185, some 186)], [(17, some 18)], [(20, some 21)], [(132, some 133)], [(133, some 134)], [(134, some 135)], [(135, some 136)], [(136, some 137)], [(137, some 138)], [(744, some 753)], [(4, some 5)], [(5, some 6)], [(7, some 8)], [(8, some 9)], [(22, some 23)], [(903, some 956)], [(23, some 24)], [(574, some 613)], [(25, some 26)], [(125, some 126)], [(126, some 127)], [(127, some 128)], [(128, some 129)], [(129, some 130)], [(10, some 11)], [(11, some 12)], [(12, some 13)], [(145, some 146)], [(146, some 147)], [(147, some 148)], [(148, some 149)], [(149, some 150)], [(150, some 151)], [(151, some 152)], [(152, some 153)], [(153, some 154)], [(154, some 155)], [(155, some 156)], [(762, some 772)], [(29, some 30)], [(30, some 31)], [(41, some 42)], [(110, some 111)], [(111, some 112)], [(162, some 163)], [(984, some 993)], [(13, some 14)], [(14, some 15)], [(15, some 16)], [(116, some 117)], [(117, some 118)], [(118, some 119)], [(119, some 120)], [(120, some 121)], [(121, some 122)], [(122, some 123)], [(123, some 124)], [(16, some 17)], [(18, some 19)], [(696, some 744)], [(19, some 20)], [(161, some 162)], [(163, some 164)], [(164, some 165)], [(165, some 166)], [(166, some 167)], [(167, some 168)], [(168, some 169)], [(169, some 170)], [(21, some 22)], [(91, some 92)], [(96, some 97)], [(97, some 98)], [(98, some 99)], [(647, some 659)], [(24, some 25)], [(26, some 27)], [(27, some 28)], [(798, some 837)], [(28, some 29)], [(613, some 647)], [(68, some 69)], [(69, some 70)], [(90, some 91)], [(837, some 852)], [(31, some 32)], [(32, some 33)], [(33, some 34)], [(34, some 35)], [(35, some 36)], [(871, some 903)], [(66, some 67)], [(67, some 68)], [(36, some 37)], [(37, some 38)], [(38, some 39)], [(39, some 40)], [(40, some 41)], [(93, some 94)], [(94, some 95)], [(173, some 174)], [(753, some 762)], [(42, some 43)], [(43, some 44)], [(44, some 45)], [(45, some 46)], [(46, some 47)], [(47, some 48)], [(673, some 696)], [(48, some 49)], [(49, some 50)], [(50, some 51)], [(51, some 52)], [(52, some 53)], [(55, some 56)], [(965, some 984)], [(53, some 54)], [(54, some 55)], [(56, some 57)], [(57, some 58)], [(58, some 59)], [(59, some 60)], [(95, some 96)], [(124, some 125)], [(1954, some 2014)], [(60, some 61)], [(61, some 62)], [(62, some 63)], [(63, some 64)], [(64, some 65)], [(65, some 66)], [(780, some 798)], [(70, some 71)], [(71, some 72)], [(72, some 73)], [(73, some 74)], [(74, some 75)], [(75, some 76)], [(76, some 77)], [(852, some 871)], [(77, some 78)], [(78, some 79)], [(79, some 80)], [(80, some 81)], [(81, some 82)], [(82, some 83)], [(92, some 93)], [(83, some 84)], [(84, some 85)], [(85, some 86)], [(86, some 87)], [(87, some 88)], [(88, some 89)], [(89, some 90)], [(659, some 673)], [(99, some 100)], [(100, some 101)], [(101, some 102)], [(102, some 103)], [(103, some 104)], [(104, some 105)], [(105, some 106)], [(181, some 182)], [(772, some 780)], [(106, some 107)], [(107, some 108)], [(108, some 109)], [(109, some 110)], [(112, some 113)], [(113, some 114)], [(114, some 115)], [(115, some 116)], [(130, some 131)], [(131, some 132)], [(138, some 139)], [(139, some 140)], [(140, some 141)], [(141, some 142)], [(142, some 143)], [(143, some 144)], [(144, some 145)], [(186, some 187)], [(187, some 188)], [(188, some 189)], [(189, some 190)], [(190, some 191)], [(191, some 192)], [(192, some 193)], [(193, some 194)], [(194, some 195)], [(195, some 196)], [(196, some 197)], [(197, some 198)], [(956, some 965)], [(198, some 199)], [(199, some 200)], [(528, some 574)], [(200, some 528)]] := by rfl
  have h1 : mergeRound [[(1, some 2)], [(993, some 1954)], [(2, some 3)], [(2014, none)], [(3, some 4)], [(6, some 7)], [(9, some 10)], [(156, some 157)], [(157, some 158)], [(158, some 159)], [(159, some 160)], [(160, some 161)], [(170, some 171)], [(171, some 172)], [(172, some 173)], [(174, some 175)], [(175, some 176)], [(176, some 177)], [(177, some 178)], [(178, some 179)], [(179, some 180)], [(180, some 181)], [(182, some 183)], [(183, some 184)], [(184, some 185)], [(185, some 186)], [(17, some 18)], [(20, some 21)], [(132, some 133)], [(133, some 134)], [(134, some 135)], [(135, some 136)], [(136, some 137)], [(137, some 138)], [(744, some 753)], [(4, some 5)], [(5, some 6)], [(7, some 8)], [(8, some 9)], [(22, some 23)], [(903, some 956)], [(23, some 24)], [(574, some 613)], [(25, some 26)], [(125, some 126)], [(126, some 127)], [(127, some 128)], [(128, some 129)], [(129, some 130)], [(10, some 11)], [(11, some 12)], [(12, some 13)], [(145, some 146)], [(146, some 147)], [(147, some 148)], [(148, some 149)], [(149, some 150)], [(150, some 151)], [(151, some 152)], [(152, some 153)], [(153, some 154)], [(154, some 155)], [(155, some 156)], [(762, some 772)], [(29, some 30)], [(30, some 31)], [(41, some 42)], [(110, some 111)], [(111, some 112)], [(162, some 163)], [(984, some 993)], [(13, some 14)], [(14, some 15)], [(15, some 16)], [(116, some 117)], [(117, some 118)], [(118, some 119)], [(119, some 120)], [(120, some 121)], [(121, some 122)], [(122, some 123)], [(123, some 124)], [(16, some 17)], [(18, some 19)], [(696, some 744)], [(19, some 20)], [(161, some 162)], [(163, some 164)], [(164, some 165)], [(165, some 166)], [(166, some 167)], [(167, some 168)], [(168, some 169)], [(169, some 170)], [(21, some 22)], [(91, some 92)], [(96, some 97)], [(97, some 98)], [(98, some 99)], [(647, some 659)], [(24, some 25)], [(26, some 27)], [(27, some 28)], [(798, some 837)], [(28, some 29)], [(613, some 647)], [(68, some 69)], [(69, some 70)], [(90, some 91)], [(837, some 852)], [(31, some 32)], [(32, some 33)], [(33, some 34)], [(34, some 35)], [(35, some 36)], [(871, some 903)], [(66, some 67)], [(67, some 68)], [(36, some 37)], [(37, some 38)], [(38, some 39)], [(39, some 40)], [(40, some 41)], [(93, some 94)], [(94, some 95)], [(173, some 174)], [(753, some 762)], [(42, some 43)], [(43, some 44)], [(44, some 45)], [(45, some 46)], [(46, some 47)], [(47, some 48)], [(673, some 696)], [(48, some 49)], [(49, some 50)], [(50, some 51)], [(51, some 52)], [(52, some 53)], [(55, some 56)], [(965, some 984)], [(53, some 54)], [(54, some 55)], [(56, some 57)], [(57, some 58)], [(58, some 59)], [(59, some 60)], [(95, some 96)], [(124, some 125)], [(1954, some 2014)], [(60, some 61)], [(61, some 62)], [(62, some 63)], [(63, some 64)], [(64, some 65)], [(65, some 66)], [(780, some 798)], [(70, some 71)], [(71, some 72)], [(72, some 73)], [(73, some 74)], [(74, some 75)], [(75, some 76)], [(76, some 77)], [(852, some 871)], [(77, some 78)], [(78, some 79)], [(79, some 80)], [(80, some 81)], [(81, some 82)], [(82, some 83)], [(92, some 93)], [(83, some 84)], [(84, some 85)], [(85, some 86)], [(86, some 87)], [(87, some 88)], [(88, some 89)], [(89, some 90)], [(659, some 673)], [(99, some 100)], [(100, some 101)], [(101, some 102)], [(102, some 103)], [(103, some 104)], [(104, some 105)], [(105, some 106)], [(181, some 182)], [(772, some 780)], [(106, some 107)], [(107, some 108)], [(108, some 109)], [(109, some 110)], [(112, some 113)], [(113, some 114)], [(114, some 115)], [(115, some 116)], [(130, some 131)], [(131, some 132)], [(138, some 139)], [(139, some 140)], [(140, some 141)], [(141, some 142)], [(142, some 143)], [(143, some 144)], [(144, some 145)], [(186, some 187)], [(187, some 188)], [(188, some 189)], [(189, some 190)], [(190, some 191)], [(191, some 192)], [(192, some 193)], [(193, some 194)], [(194, some 195)], [(195, some 196)], [(196, some 197)], [(197, some 198)], [(956, some 965)], [(198, some 199)], [(199, some 200)], [(528, some 574)], [(200, some 528)]] = [[(1, some 2), (993, some 1954)], [(2, some 3), (2014, none)], [(3, some 4), (6, some 7)], [(9, some 10), (156, some 157)], [(157, some 158), (158, some 159)], [(159, some 160), (160, some 161)], [(170, some 171), (171, some 172)], [(172, some 173), (174, some 175)], [(175, some 176), (176, some 177)], [(177, some 178), (178, some 179)], [(179, some 180), (180, some 181)], [(182, some 183), (183, some 184)], [(184, some 185), (185, some 186)], [(17, some 18), (20, some 21)], [(132, some 133), (133, some 134)], [(134, some 135), (135, some 136)], [(136, some 137), (137, some 138)], [(4, some 5), (744, some 753)], [(5, some 6), (7, some 8)], [(8, some 9), (22, some 23)], [(23, some 24), (903, some 956)], [(25, some 26), (574, some 613)], [(125, some 126), (126, some 127)], [(127, some 128), (128, some 129)], [(10, some 11), (129, some 130)], [(11, some 12), (12, some 13)], [(145, some 146), (146, some 147)], [(147, some 148), (148, some 149)], [(149, some 150), (150, some 151)], [(151, some 152), (152, some 153)], [(153, some 154), (154, some 155)], [(155, some 156), (762, some 772)], [(29, some 30), (30, some 31)], [(41, some 42), (110, some 111)], [(111, some 112), (162, some 163)], [(13, some 14), (984, some 993)], [(14, some 15), (15, some 16)], [(116, some 117), (117, some 118)], [(118, some 119), (119, some 120)], [(120, some 121), (121, some 122)], [(122, some 123), (123, some 124)], [(16, some 17), (18, some 19)], [(19, some 20), (696, some 744)], [(161, some 162), (163, some 164)], [(164, some 165), (165, some 166)], [(166, some 167), (167, some 168)], [(168, some 169), (169, some 170)], [(21, some 22), (91, some 92)], [(96, some 97), (97, some 98)], [(98, some 99), (647, some 659)], [(24, some 25), (26, some 27)], [(27, some 28), (798, some 837)], [(28, some 29), (613, some 647)], [(68, some 69), (69, some 70)], [(90, some 91), (837, some 852)], [(31, some 32), (32, some 33)], [(33, some 34), (34, some 35)], [(35, some 36), (871, some 903)], [(66, some 67), (67, some 68)], [(36, some 37), (37, some 38)], [(38, some 39), (39, some 40)], [(40, some 41), (93, some 94)], [(94, some 95), (173, some 174)], [(42, some 43), (753, some 762)], [(43, some 44), (44, some 45)], [(45, some 46), (46, some 47)], [(47, some 48), (673, some 696)], [(48, some 49), (49, some 50)], [(50, some 51), (51, some 52)], [(52, some 53), (55, some 56)], [(53, some 54), (965, some 984)], [(54, some 55), (56, some 57)], [(57, some 58), (58, some 59)], [(59, some 60), (95, some 96)], [(124, some 125), (1954, some 2014)], [(60, some 61), (61, some 62)], [(62, some 63), (63, some 64)], [(64, some 65), (65, some 66)], [(70, some 71), (780, some 798)], [(71, some 72), (72, some 73)], [(73, some 74), (74, some 75)], [(75, some 76), (76, some 77)], [(77, some 78), (852, some 871)], [(78, some 79), (79, some 80)], [(80, some 81), (81, some 82)], [(82, some 83), (92, some 93)], [(83, some 84), (84, some 85)], [(85, some 86), (86, some 87)], [(87, some 88), (88, some 89)], [(89, some 90), (659, some 673)], [(99, some 100), (100, some 101)], [(101, some 102), (102, some 103)], [(103, some 104), (104, some 105)], [(105, some 106), (181, some 182)], [(106, some 107), (772, some 780)], [(107, some 108), (108, some 109)], [(109, some 110), (112, some 113)], [(113, some 114), (114, some 115)], [(115, some 116), (130, some 131)], [(131, some 132), (138, some 139)], [(139, some 140), (140, some 141)], [(141, some 142), (142, some 143)], [(143, some 144), (144, some 145)], [(186, some 187), (187, some 188)], [(188, some 189), (189, some 190)], [(190, some 191), (191, some 192)], [(192, some 193), (193, some 194)], [(194, some 195), (195, some 196)], [(196, some 197), (197, some 198)], [(198, some 199), (956, some 965)], [(199, some 200), (528, some 574)], [(200, some 528)]] := by decide
  have h2 : mergeRound [[(1, some 2), (993, some 1954)], [(2, some 3), (2014, none)], [(3, some 4), (6, some 7)], [(9, some 10), (156, some 157)], [(157, some 158), (158, some 159)], [(159, some 160), (160, some 161)], [(170, some 171), (171, some 172)], [(172, some 173), (174, some 175)], [(175, some 176), (176, some 177)], [(177, some 178), (178, some 179)], [(179, some 180), (180, some 181)], [(182, some 183), (183, some 184)], [(184, some 185), (185, some 186)], [(17, some 18), (20, some 21)], [(132, some 133), (133, some 134)], [(134, some 135), (135, some 136)], [(136, some 137), (137, some 138)], [(4, some 5), (744, some 753)], [(5, some 6), (7, some 8)], [(8, some 9), (22, some 23)], [(23, some 24), (903, some 956)], [(25, some 26), (574, some 613)], [(125, some 126), (126, some 127)], [(127, some 128), (128, some 129)], [(10, some 11), (129, some 130)], [(11, some 12), (12, some 13)], [(145, some 146), (146, some 147)], [(147, some 148), (148, some 149)], [(149, some 150), (150, some 151)], [(151, some 152), (152, some 153)], [(153, some 154), (154, some 155)], [(155, some 156), (762, some 772)], [(29, some 30), (30, some 31)], [(41, some 42), (110, some 111)], [(111, some 112), (162, some 163)], [(13, some 14), (984, some 993)], [(14, some 15), (15, some 16)], [(116, some 117), (117, some 118)], [(118, some 119), (119, some 120)], [(120, some 121), (121, some 122)], [(122, some 123), (123, some 124)], [(16, some 17), (18, some 19)], [(19, some 20), (696, some 744)], [(161, some 162), (163, some 164)], [(164, some 165), (165, some 166)], [(166, some 167), (167, some 168)], [(168, some 169), (169, some 170)], [(21, some 22), (91, some 92)], [(96, some 97), (97, some 98)], [(98, some 99), (647, some 659)], [(24, some 25), (26, some 27)], [(27, some 28), (798, some 837)], [(28, some 29), (613, some 647)], [(68, some 69), (69, some 70)], [(90, some 91), (837, some 852)], [(31, some 32), (32, some 33)], [(33, some 34), (34, some 35)], [(35, some 36), (871, some 903)], [(66, some 67), (67, some 68)], [(36, some 37), (37, some 38)], [(38, some 39), (39, some 40)], [(40, some 41), (93, some 94)], [(94, some 95), (173, some 174)], [(42, some 43), (753, some 762)], [(43, some 44), (44, some 45)], [(45, some 46), (46, some 47)], [(47, some 48), (673, some 696)], [(48, some 49), (49, some 50)], [(50, some 51), (51, some 52)], [(52, some 53), (55, some 56)], [(53, some 54), (965, some 984)], [(54, some 55), (56, some 57)], [(57, some 58), (58, some 59)], [(59, some 60), (95, some 96)], [(124, some 125), (1954, some 2014)], [(60, some 61), (61, some 62)], [(62, some 63), (63, some 64)], [(64, some 65), (65, some 66)], [(70, some 71), (780, some 798)], [(71, some 72), (72, some 73)], [(73, some 74), (74, some 75)], [(75, some 76), (76, some 77)], [(77, some 78), (852, some 871)], [(78, some 79), (79, some 80)], [(80, some 81), (81, some 82)], [(82, some 83), (92, some 93)], [(83, some 84), (84, some 85)], [(85, some 86), (86, some 87)], [(87, some 88), (88, some 89)], [(89, some 90), (659, some 673)], [(99, some 100), (100, some 101)], [(101, some 102), (102, some 103)], [(103, some 104), (104, some 105)], [(105, some 106), (181, some 182)], [(106, some 107), (772, some 780)], [(107, some 108), (108, some 109)], [(109, some 110), (112, some 113)], [(113, some 114), (114, some 115)], [(115, some 116), (130, some 131)], [(131, some 132), (138, some 139)], [(139, some 140), (140, some 141)], [(141, some 142), (142, some 143)], [(143, some 144), (144, some 145)], [(186, some 187), (187, some 188)], [(188, some 189), (189, some 190)], [(190, some 191), (191, some 192)], [(192, some 193), (193, some 194)], [(194, some 195), (195, some 196)], [(196, some 197), (197, some 198)], [(198, some 199), (956, some 965)], [(199, some 200), (528, some 574)], [(200, some 528)]] = [[(1, some 2), (2, some 3), (993, some 1954), (2014, none)], [(3, some 4), (6, some 7), (9, some 10), (156, some 157)], [(157, some 158), (158, some 159), (159, some 160), (160, some 161)], [(170, some 171), (171, some 172), (172, some 173), (174, some 175)], [(175, some 176), (176, some 177), (177, some 178), (178, some 179)], [(179, some 180), (180, some 181), (182, some 183), (183, some 184)], [(17, some 18), (20, some 21), (184, some 185), (185, some 186)], [(132, some 133), (133, some 134), (134, some 135), (135, some 136)], [(4, some 5), (136, some 137), (137, some 138), (744, some 753)], [(5, some 6), (7, some 8), (8, some 9), (22, some 23)], [(23, some 24), (25, some 26), (574, some 613), (903, some 956)], [(125, some 126), (126, some 127), (127, some 128), (128, some 129)], [(10, some 11), (11, some 12), (12, some 13), (129, some 130)], [(145, some 146), (146, some 147), (147, some 148), (148, some 149)], [(149, some 150), (150, some 151), (151, some 152), (152, some 153)], [(153, some 154), (154, some 155), (155, some 156), (762, some 772)], [(29, some 30), (30, some 31), (41, some 42), (110, some 111)], [(13, some 14), (111, some 112), (162, some 163), (984, some 993)], [(14, some 15), (15, some 16), (116, some 117), (117, some 118)], [(118, some 119), (119, some 120), (120, some 121), (121, some 122)], [(16, some 17), (18, some 19), (122, some 123), (123, some 124)], [(19, some 20), (161, some 162), (163, some 164), (696, some 744)], [(164, some 165), (165, some 166), (166, some 167), (167, some 168)], [(21, some 22), (91, some 92), (168, some 169), (169, some 170)], [(96, some 97), (97, some 98), (98, some 99), (647, some 659)], [(24, some 25), (26, some 27), (27, some 28), (798, some 837)], [(28, some 29), (68, some 69), (69, some 70), (613, some 647)], [(31, some 32), (32, some 33), (90, some 91), (837, some 852)], [(33, some 34), (34, some 35), (35, some 36), (871, some 903)], [(36, some 37), (37, some 38), (66, some 67), (67, some 68)], [(38, some 39), (39, some 40), (40, some 41), (93, some 94)], [(42, some 43), (94, some 95), (173, some 174), (753, some 762)], [(43, some 44), (44, some 45), (45, some 46), (46, some 47)], [(47, some 48), (48, some 49), (49, some 50), (673, some 696)], [(50, some 51), (51, some 52), (52, some 53), (55, some 56)], [(53, some 54), (54, some 55), (56, some 57), (965, some 984)], [(57, some 58), (58, some 59), (59, some 60), (95, some 96)], [(60, some 61), (61, some 62), (124, some 125), (1954, some 2014)], [(62, some 63), (63, some 64), (64, some 65), (65, some 66)], [(70, some 71), (71, some 72), (72, some 73), (780, some 798)], [(73, some 74), (74, some 75), (75, some 76), (76, some 77)], [(77, some 78), (78, some 79), (79, some 80), (852, some 871)], [(80, some 81), (81, some 82), (82, some 83), (92, some 93)], [(83, some 84), (84, some 85), (85, some 86), (86, some 87)], [(87, some 88), (88, some 89), (89, some 90), (659, some 673)], [(99, some 100), (100, some 101), (101, some 102), (102, some 103)], [(103, some 104), (104, some 105), (105, some 106), (181, some 182)], [(106, some 107), (107, some 108), (108, some 109), (772, some 780)], [(109, some 110), (112, some 113), (113, some 114), (114, some 115)], [(115, some 116), (130, some 131), (131, some 132), (138, some 139)], [(139, some 140), (140, some 141), (141, some 142), (142, some 143)], [(143, some 144), (144, some 145), (186, some 187), (187, some 188)], [(188, some 189), (189, some 190), (190, some 191), (191, some 192)], [(192, some 193), (193, some 194), (194, some 195), (195, some 196)], [(196, some 197), (197, some 198), (198, some 199), (956, some 965)], [(199, some 200), (200, some 528), (528, some 574)]] := by decide
  have h3 : mergeRound [[(1, some 2), (2, some 3), (993, some 1954), (2014, none)], [(3, some 4), (6, some 7), (9, some 10), (156, some 157)], [(157, some 158), (158, some 159), (159, some 160), (160, some 161)], [(170, some 171), (171, some 172), (172, some 173), (174, some 175)], [(175, some 176), (176, some 177), (177, some 178), (178, some 179)], [(179, some 180), (180, some 181), (182, some 183), (183, some 184)], [(17, some 18), (20, some 21), (184, some 185), (185, some 186)], [(132, some 133), (133, some 134), (134, some 135), (135, some 136)], [(4, some 5), (136, some 137), (137, some 138), (744, some 753)], [(5, some 6), (7, some 8), (8, some 9), (22, some 23)], [(23, some 24), (25, some 26), (574, some 613), (903, some 956)], [(125, some 126), (126, some 127), (127, some 128), (128, some 129)], [(10, some 11), (11, some 12), (12, some 13), (129, some 130)], [(145, some 146), (146, some 147), (147, some 148), (148, some 149)], [(149, some 150), (150, some 151), (151, some 152), (152, some 153)], [(153, some 154), (154, some 155), (155, some 156), (762, some 772)], [(29, some 30), (30, some 31), (41, some 42), (110, some 111)], [(13, some 14), (111, some 112), (162, some 163), (984, some 993)], [(14, some 15), (15, some 16), (116, some 117), (117, some 118)], [(118, some 119), (119, some 120), (120, some 121), (121, some 122)], [(16, some 17), (18, some 19), (122, some 123), (123, some 124)], [(19, some 20), (161, some 162), (163, some 164), (696, some 744)], [(164, some 165), (165, some 166), (166, some 167), (167, some 168)], [(21, some 22), (91, some 92), (168, some 169), (169, some 170)], [(96, some 97), (97, some 98), (98, some 99), (647, some 659)], [(24, some 25), (26, some 27), (27, some 28), (798, some 837)], [(28, some 29), (68, some 69), (69, some 70), (613, some 647)], [(31, some 32), (32, some 33), (90, some 91), (837, some 852)], [(33, some 34), (34, some 35), (35, some 36), (871, some 903)], [(36, some 37), (37, some 38), (66, some 67), (67, some 68)], [(38, some 39), (39, some 40), (40, some 41), (93, some 94)], [(42, some 43), (94, some 95), (173, some 174), (753, some 762)], [(43, some 44), (44, some 45), (45, some 46), (46, some 47)], [(47, some 48), (48, some 49), (49, some 50), (673, some 696)], [(50, some 51), (51, some 52), (52, some 53), (55, some 56)], [(53, some 54), (54, some 55), (56, some 57), (965, some 984)], [(57, some 58), (58, some 59), (59, some 60), (95, some 96)], [(60, some 61), (61, some 62), (124, some 125), (1954, some 2014)], [(62, some 63), (63, some 64), (64, some 65), (65, some 66)], [(70, some 71), (71, some 72), (72, some 73), (780, some 798)], [(73, some 74), (74, some 75), (75, some 76), (76, some 77)], [(77, some 78), (78, some 79), (79, some 80), (852, some 871)], [(80, some 81), (81, some 82), (82, some 83), (92, some 93)], [(83, some 84), (84, some 85), (85, some 86), (86, some 87)], [(87, some 88), (88, some 89), (89, some 90), (659, some 673)], [(99, some 100), (100, some 101), (101, some 102), (102, some 103)], [(103, some 104), (104, some 105), (105, some 106), (181, some 182)], [(106, some 107), (107, some 108), (108, some 109), (772, some 780)], [(109, some 110), (112, some 113), (113, some 114), (114, some 115)], [(115, some 116), (130, some 131), (131, some 132), (138, some 139)], [(139, some 140), (140, some 141), (141, some 142), (142, some 143)], [(143, some 144), (144, some 145), (186, some 187), (187, some 188)], [(188, some 189), (189, some 190), (190, some 191), (191, some 192)], [(192, some 193), (193, some 194), (194, some 195), (195, some 196)], [(196, some 197), (197, some 198), (198, some 199), (956, some 965)], [(199, some 200), (200, some 528), (528, some 574)]] = [[(1, some 2), (2, some 3), (3, some 4), (6, some 7), (9, some 10), (156, some 157), (993, some 1954), (2014, none)], [(157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175)], [(175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184)], [(17, some 18), (20, some 21), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (184, some 185), (185, some 186)], [(4, some 5), (5, some 6), (7, some 8), (8, some 9), (22, some 23), (136, some 137), (137, some 138), (744, some 753)], [(23, some 24), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (574, some 613), (903, some 956)], [(10, some 11), (11, some 12), (12, some 13), (129, some 130), (145, some 146), (146, some 147), (147, some 148), (148, some 149)], [(149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772)], [(13, some 14), (29, some 30), (30, some 31), (41, some 42), (110, some 111), (111, some 112), (162, some 163), (984, some 993)], [(14, some 15), (15, some 16), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122)], [(16, some 17), (18, some 19), (19, some 20), (122, some 123), (123, some 124), (161, some 162), (163, some 164), (696, some 744)], [(21, some 22), (91, some 92), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170)], [(24, some 25), (26, some 27), (27, some 28), (96, some 97), (97, some 98), (98, some 99), (647, some 659), (798, some 837)], [(28, some 29), (31, some 32), (32, some 33), (68, some 69), (69, some 70), (90, some 91), (613, some 647), (837, some 852)], [(33, some 34), (34, some 35), (35, some 36), (36, some 37), (37, some 38), (66, some 67), (67, some 68), (871, some 903)], [(38, some 39), (39, some 40), (40, some 41), (42, some 43), (93, some 94), (94, some 95), (173, some 174), (753, some 762)], [(43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (48, some 49), (49, some 50), (673, some 696)], [(50, some 51), (51, some 52), (52, some 53), (53, some 54), (54, some 55), (55, some 56), (56, some 57), (965, some 984)], [(57, some 58), (58, some 59), (59, some 60), (60, some 61), (61, some 62), (95, some 96), (124, some 125), (1954, some 2014)], [(62, some 63), (63, some 64), (64, some 65), (65, some 66), (70, some 71), (71, some 72), (72, some 73), (780, some 798)], [(73, some 74), (74, some 75), (75, some 76), (76, some 77), (77, some 78), (78, some 79), (79, some 80), (852, some 871)], [(80, some 81), (81, some 82), (82, some 83), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (92, some 93)], [(87, some 88), (88, some 89), (89, some 90), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (659, some 673)], [(103, some 104), (104, some 105), (105, some 106), (106, some 107), (107, some 108), (108, some 109), (181, some 182), (772, some 780)], [(109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139)], [(139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188)], [(188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196)], [(196, some 197), (197, some 198), (198, some 199), (199, some 200), (200, some 528), (528, some 574), (956, some 965)]] := by decide
  have h4 : mergeRound [[(1, some 2), (2, some 3), (3, some 4), (6, some 7), (9, some 10), (156, some 157), (993, some 1954), (2014, none)], [(157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175)], [(175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184)], [(17, some 18), (20, some 21), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (184, some 185), (185, some 186)], [(4, some 5), (5, some 6), (7, some 8), (8, some 9), (22, some 23), (136, some 137), (137, some 138), (744, some 753)], [(23, some 24), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (574, some 613), (903, some 956)], [(10, some 11), (11, some 12), (12, some 13), (129, some 130), (145, some 146), (146, some 147), (147, some 148), (148, some 149)], [(149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772)], [(13, some 14), (29, some 30), (30, some 31), (41, some 42), (110, some 111), (111, some 112), (162, some 163), (984, some 993)], [(14, some 15), (15, some 16), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122)], [(16, some 17), (18, some 19), (19, some 20), (122, some 123), (123, some 124), (161, some 162), (163, some 164), (696, some 744)], [(21, some 22), (91, some 92), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170)], [(24, some 25), (26, some 27), (27, some 28), (96, some 97), (97, some 98), (98, some 99), (647, some 659), (798, some 837)], [(28, some 29), (31, some 32), (32, some 33), (68, some 69), (69, some 70), (90, some 91), (613, some 647), (837, some 852)], [(33, some 34), (34, some 35), (35, some 36), (36, some 37), (37, some 38), (66, some 67), (67, some 68), (871, some 903)], [(38, some 39), (39, some 40), (40, some 41), (42, some 43), (93, some 94), (94, some 95), (173, some 174), (753, some 762)], [(43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (48, some 49), (49, some 50), (673, some 696)], [(50, some 51), (51, some 52), (52, some 53), (53, some 54), (54, some 55), (55, some 56), (56, some 57), (965, some 984)], [(57, some 58), (58, some 59), (59, some 60), (60, some 61), (61, some 62), (95, some 96), (124, some 125), (1954, some 2014)], [(62, some 63), (63, some 64), (64, some 65), (65, some 66), (70, some 71), (71, some 72), (72, some 73), (780, some 798)], [(73, some 74), (74, some 75), (75, some 76), (76, some 77), (77, some 78), (78, some 79), (79, some 80), (852, some 871)], [(80, some 81), (81, some 82), (82, some 83), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (92, some 93)], [(87, some 88), (88, some 89), (89, some 90), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (659, some 673)], [(103, some 104), (104, some 105), (105, some 106), (106, some 107), (107, some 108), (108, some 109), (181, some 182), (772, some 780)], [(109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139)], [(139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188)], [(188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196)], [(196, some 197), (197, some 198), (198, some 199), (199, some 200), (200, some 528), (528, some 574), (956, some 965)]] = [[(1, some 2), (2, some 3), (3, some 4), (6, some 7), (9, some 10), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (993, some 1954), (2014, none)], [(17, some 18), (20, some 21), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186)], [(4, some 5), (5, some 6), (7, some 8), (8, some 9), (22, some 23), (23, some 24), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (136, some 137), (137, some 138), (574, some 613), (744, some 753), (903, some 956)], [(10, some 11), (11, some 12), (12, some 13), (129, some 130), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772)], [(13, some 14), (14, some 15), (15, some 16), (29, some 30), (30, some 31), (41, some 42), (110, some 111), (111, some 112), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (162, some 163), (984, some 993)], [(16, some 17), (18, some 19), (19, some 20), (21, some 22), (91, some 92), (122, some 123), (123, some 124), (161, some 162), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (696, some 744)], [(24, some 25), (26, some 27), (27, some 28), (28, some 29), (31, some 32), (32, some 33), (68, some 69), (69, some 70), (90, some 91), (96, some 97), (97, some 98), (98, some 99), (613, some 647), (647, some 659), (798, some 837), (837, some 852)], [(33, some 34), (34, some 35), (35, some 36), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (42, some 43), (66, some 67), (67, some 68), (93, some 94), (94, some 95), (173, some 174), (753, some 762), (871, some 903)], [(43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (53, some 54), (54, some 55), (55, some 56), (56, some 57), (673, some 696), (965, some 984)], [(57, some 58), (58, some 59), (59, some 60), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (70, some 71), (71, some 72), (72, some 73), (95, some 96), (124, some 125), (780, some 798), (1954, some 2014)], [(73, some 74), (74, some 75), (75, some 76), (76, some 77), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (92, some 93), (852, some 871)], [(87, some 88), (88, some 89), (89, some 90), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (106, some 107), (107, some 108), (108, some 109), (181, some 182), (659, some 673), (772, some 780)], [(109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188)], [(188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (198, some 199), (199, some 200), (200, some 528), (528, some 574), (956, some 965)]] := by decide
  have h5 : mergeRound [[(1, some 2), (2, some 3), (3, some 4), (6, some 7), (9, some 10), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (993, some 1954), (2014, none)], [(17, some 18), (20, some 21), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186)], [(4, some 5), (5, some 6), (7, some 8), (8, some 9), (22, some 23), (23, some 24), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (136, some 137), (137, some 138), (574, some 613), (744, some 753), (903, some 956)], [(10, some 11), (11, some 12), (12, some 13), (129, some 130), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (762, some 772)], [(13, some 14), (14, some 15), (15, some 16), (29, some 30), (30, some 31), (41, some 42), (110, some 111), (111, some 112), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (162, some 163), (984, some 993)], [(16, some 17), (18, some 19), (19, some 20), (21, some 22), (91, some 92), (122, some 123), (123, some 124), (161, some 162), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (696, some 744)], [(24, some 25), (26, some 27), (27, some 28), (28, some 29), (31, some 32), (32, some 33), (68, some 69), (69, some 70), (90, some 91), (96, some 97), (97, some 98), (98, some 99), (613, some 647), (647, some 659), (798, some 837), (837, some 852)], [(33, some 34), (34, some 35), (35, some 36), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (42, some 43), (66, some 67), (67, some 68), (93, some 94), (94, some 95), (173, some 174), (753, some 762), (871, some 903)], [(43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (53, some 54), (54, some 55), (55, some 56), (56, some 57), (673, some 696), (965, some 984)], [(57, some 58), (58, some 59), (59, some 60), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (70, some 71), (71, some 72), (72, some 73), (95, some 96), (124, some 125), (780, some 798), (1954, some 2014)], [(73, some 74), (74, some 75), (75, some 76), (76, some 77), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (92, some 93), (852, some 871)], [(87, some 88), (88, some 89), (89, some 90), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (106, some 107), (107, some 108), (108, some 109), (181, some 182), (659, some 673), (772, some 780)], [(109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188)], [(188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (198, some 199), (199, some 200), (200, some 528), (528, some 574), (956, some 965)]] = [[(1, some 2), (2, some 3), (3, some 4), (6, some 7), (9, some 10), (17, some 18), (20, some 21), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186), (993, some 1954), (2014, none)], [(4, some 5), (5, some 6), (7, some 8), (8, some 9), (10, some 11), (11, some 12), (12, some 13), (22, some 23), (23, some 24), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130), (136, some 137), (137, some 138), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (574, some 613), (744, some 753), (762, some 772), (903, some 956)], [(13, some 14), (14, some 15), (15, some 16), (16, some 17), (18, some 19), (19, some 20), (21, some 22), (29, some 30), (30, some 31), (41, some 42), (91, some 92), (110, some 111), (111, some 112), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124), (161, some 162), (162, some 163), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (696, some 744), (984, some 993)], [(24, some 25), (26, some 27), (27, some 28), (28, some 29), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (42, some 43), (66, some 67), (67, some 68), (68, some 69), (69, some 70), (90, some 91), (93, some 94), (94, some 95), (96, some 97), (97, some 98), (98, some 99), (173, some 174), (613, some 647), (647, some 659), (753, some 762), (798, some 837), (837, some 852), (871, some 903)], [(43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (53, some 54), (54, some 55), (55, some 56), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (70, some 71), (71, some 72), (72, some 73), (95, some 96), (124, some 125), (673, some 696), (780, some 798), (965, some 984), (1954, some 2014)], [(73, some 74), (74, some 75), (75, some 76), (76, some 77), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (92, some 93), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (106, some 107), (107, some 108), (108, some 109), (181, some 182), (659, some 673), (772, some 780), (852, some 871)], [(109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (198, some 199), (199, some 200), (200, some 528), (528, some 574), (956, some 965)]] := by decide
  have h6 : mergeRound [[(1, some 2), (2, some 3), (3, some 4), (6, some 7), (9, some 10), (17, some 18), (20, some 21), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186), (993, some 1954), (2014, none)], [(4, some 5), (5, some 6), (7, some 8), (8, some 9), (10, some 11), (11, some 12), (12, some 13), (22, some 23), (23, some 24), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130), (136, some 137), (137, some 138), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (574, some 613), (744, some 753), (762, some 772), (903, some 956)], [(13, some 14), (14, some 15), (15, some 16), (16, some 17), (18, some 19), (19, some 20), (21, some 22), (29, some 30), (30, some 31), (41, some 42), (91, some 92), (110, some 111), (111, some 112), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124), (161, some 162), (162, some 163), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (696, some 744), (984, some 993)], [(24, some 25), (26, some 27), (27, some 28), (28, some 29), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (42, some 43), (66, some 67), (67, some 68), (68, some 69), (69, some 70), (90, some 91), (93, some 94), (94, some 95), (96, some 97), (97, some 98), (98, some 99), (173, some 174), (613, some 647), (647, some 659), (753, some 762), (798, some 837), (837, some 852), (871, some 903)], [(43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (53, some 54), (54, some 55), (55, some 56), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (70, some 71), (71, some 72), (72, some 73), (95, some 96), (124, some 125), (673, some 696), (780, some 798), (965, some 984), (1954, some 2014)], [(73, some 74), (74, some 75), (75, some 76), (76, some 77), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (92, some 93), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (106, some 107), (107, some 108), (108, some 109), (181, some 182), (659, some 673), (772, some 780), (852, some 871)], [(109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (198, some 199), (199, some 200), (200, some 528), (528, some 574), (956, some 965)]] = [[(1, some 2), (2, some 3), (3, some 4), (4, some 5), (5, some 6), (6, some 7), (7, some 8), (8, some 9), (9, some 10), (10, some 11), (11, some 12), (12, some 13), (17, some 18), (20, some 21), (22, some 23), (23, some 24), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (136, some 137), (137, some 138), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186), (574, some 613), (744, some 753), (762, some 772), (903, some 956), (993, some 1954), (2014, none)], [(13, some 14), (14, some 15), (15, some 16), (16, some 17), (18, some 19), (19, some 20), (21, some 22), (24, some 25), (26, some 27), (27, some 28), (28, some 29), (29, some 30), (30, some 31), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (41, some 42), (42, some 43), (66, some 67), (67, some 68), (68, some 69), (69, some 70), (90, some 91), (91, some 92), (93, some 94), (94, some 95), (96, some 97), (97, some 98), (98, some 99), (110, some 111), (111, some 112), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124), (161, some 162), (162, some 163), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (173, some 174), (613, some 647), (647, some 659), (696, some 744), (753, some 762), (798, some 837), (837, some 852), (871, some 903), (984, some 993)], [(43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (53, some 54), (54, some 55), (55, some 56), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (92, some 93), (95, some 96), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (106, some 107), (107, some 108), (108, some 109), (124, some 125), (181, some 182), (659, some 673), (673, some 696), (772, some 780), (780, some 798), (852, some 871), (965, some 984), (1954, some 2014)], [(109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (198, some 199), (199, some 200), (200, some 528), (528, some 574), (956, some 965)]] := by decide
  have h7 : mergeRound [[(1, some 2), (2, some 3), (3, some 4), (4, some 5), (5, some 6), (6, some 7), (7, some 8), (8, some 9), (9, some 10), (10, some 11), (11, some 12), (12, some 13), (17, some 18), (20, some 21), (22, some 23), (23, some 24), (25, some 26), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (136, some 137), (137, some 138), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (170, some 171), (171, some 172), (172, some 173), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186), (574, some 613), (744, some 753), (762, some 772), (903, some 956), (993, some 1954), (2014, none)], [(13, some 14), (14, some 15), (15, some 16), (16, some 17), (18, some 19), (19, some 20), (21, some 22), (24, some 25), (26, some 27), (27, some 28), (28, some 29), (29, some 30), (30, some 31), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (41, some 42), (42, some 43), (66, some 67), (67, some 68), (68, some 69), (69, some 70), (90, some 91), (91, some 92), (93, some 94), (94, some 95), (96, some 97), (97, some 98), (98, some 99), (110, some 111), (111, some 112), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124), (161, some 162), (162, some 163), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (173, some 174), (613, some 647), (647, some 659), (696, some 744), (753, some 762), (798, some 837), (837, some 852), (871, some 903), (984, some 993)], [(43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (53, some 54), (54, some 55), (55, some 56), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (92, some 93), (95, some 96), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (106, some 107), (107, some 108), (108, some 109), (124, some 125), (181, some 182), (659, some 673), (673, some 696), (772, some 780), (780, some 798), (852, some 871), (965, some 984), (1954, some 2014)], [(109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (198, some 199), (199, some 200), (200, some 528), (528, some 574), (956, some 965)]] = [[(1, some 2), (2, some 3), (3, some 4), (4, some 5), (5, some 6), (6, some 7), (7, some 8), (8, some 9), (9, some 10), (10, some 11), (11, some 12), (12, some 13), (13, some 14), (14, some 15), (15, some 16), (16, some 17), (17, some 18), (18, some 19), (19, some 20), (20, some 21), (21, some 22), (22, some 23), (23, some 24), (24, some 25), (25, some 26), (26, some 27), (27, some 28), (28, some 29), (29, some 30), (30, some 31), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (41, some 42), (42, some 43), (66, some 67), (67, some 68), (68, some 69), (69, some 70), (90, some 91), (91, some 92), (93, some 94), (94, some 95), (96, some 97), (97, some 98), (98, some 99), (110, some 111), (111, some 112), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (136, some 137), (137, some 138), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (161, some 162), (162, some 163), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (170, some 171), (171, some 172), (172, some 173), (173, some 174), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186), (574, some 613), (613, some 647), (647, some 659), (696, some 744), (744, some 753), (753, some 762), (762, some 772), (798, some 837), (837, some 852), (871, some 903), (903, some 956), (984, some 993), (993, some 1954), (2014, none)], [(43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (53, some 54), (54, some 55), (55, some 56), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (92, some 93), (95, some 96), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (124, some 125), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (181, some 182), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (198, some 199), (199, some 200), (200, some 528), (528, some 574), (659, some 673), (673, some 696), (772, some 780), (780, some 798), (852, some 871), (956, some 965), (965, some 984), (1954, some 2014)]] := by decide
  have h8 : mergeRound [[(1, some 2), (2, some 3), (3, some 4), (4, some 5), (5, some 6), (6, some 7), (7, some 8), (8, some 9), (9, some 10), (10, some 11), (11, some 12), (12, some 13), (13, some 14), (14, some 15), (15, some 16), (16, some 17), (17, some 18), (18, some 19), (19, some 20), (20, some 21), (21, some 22), (22, some 23), (23, some 24), (24, some 25), (25, some 26), (26, some 27), (27, some 28), (28, some 29), (29, some 30), (30, some 31), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (41, some 42), (42, some 43), (66, some 67), (67, some 68), (68, some 69), (69, some 70), (90, some 91), (91, some 92), (93, some 94), (94, some 95), (96, some 97), (97, some 98), (98, some 99), (110, some 111), (111, some 112), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (136, some 137), (137, some 138), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (161, some 162), (162, some 163), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (170, some 171), (171, some 172), (172, some 173), (173, some 174), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (182, some 183), (183, some 184), (184, some 185), (185, some 186), (574, some 613), (613, some 647), (647, some 659), (696, some 744), (744, some 753), (753, some 762), (762, some 772), (798, some 837), (837, some 852), (871, some 903), (903, some 956), (984, some 993), (993, some 1954), (2014, none)], [(43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (53, some 54), (54, some 55), (55, some 56), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (92, some 93), (95, some 96), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (124, some 125), (130, some 131), (131, some 132), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (181, some 182), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (198, some 199), (199, some 200), (200, some 528), (528, some 574), (659, some 673), (673, some 696), (772, some 780), (780, some 798), (852, some 871), (956, some 965), (965, some 984), (1954, some 2014)]] = [[(1, some 2), (2, some 3), (3, some 4), (4, some 5), (5, some 6), (6, some 7), (7, some 8), (8, some 9), (9, some 10), (10, some 11), (11, some 12), (12, some 13), (13, some 14), (14, some 15), (15, some 16), (16, some 17), (17, some 18), (18, some 19), (19, some 20), (20, some 21), (21, some 22), (22, some 23), (23, some 24), (24, some 25), (25, some 26), (26, some 27), (27, some 28), (28, some 29), (29, some 30), (30, some 31), (31, some 32), (32, some 33), (33, some 34), (34, some 35), (35, some 36), (36, some 37), (37, some 38), (38, some 39), (39, some 40), (40, some 41), (41, some 42), (42, some 43), (43, some 44), (44, some 45), (45, some 46), (46, some 47), (47, some 48), (48, some 49), (49, some 50), (50, some 51), (51, some 52), (52, some 53), (53, some 54), (54, some 55), (55, some 56), (56, some 57), (57, some 58), (58, some 59), (59, some 60), (60, some 61), (61, some 62), (62, some 63), (63, some 64), (64, some 65), (65, some 66), (66, some 67), (67, some 68), (68, some 69), (69, some 70), (70, some 71), (71, some 72), (72, some 73), (73, some 74), (74, some 75), (75, some 76), (76, some 77), (77, some 78), (78, some 79), (79, some 80), (80, some 81), (81, some 82), (82, some 83), (83, some 84), (84, some 85), (85, some 86), (86, some 87), (87, some 88), (88, some 89), (89, some 90), (90, some 91), (91, some 92), (92, some 93), (93, some 94), (94, some 95), (95, some 96), (96, some 97), (97, some 98), (98, some 99), (99, some 100), (100, some 101), (101, some 102), (102, some 103), (103, some 104), (104, some 105), (105, some 106), (106, some 107), (107, some 108), (108, some 109), (109, some 110), (110, some 111), (111, some 112), (112, some 113), (113, some 114), (114, some 115), (115, some 116), (116, some 117), (117, some 118), (118, some 119), (119, some 120), (120, some 121), (121, some 122), (122, some 123), (123, some 124), (124, some 125), (125, some 126), (126, some 127), (127, some 128), (128, some 129), (129, some 130), (130, some 131), (131, some 132), (132, some 133), (133, some 134), (134, some 135), (135, some 136), (136, some 137), (137, some 138), (138, some 139), (139, some 140), (140, some 141), (141, some 142), (142, some 143), (143, some 144), (144, some 145), (145, some 146), (146, some 147), (147, some 148), (148, some 149), (149, some 150), (150, some 151), (151, some 152), (152, some 153), (153, some 154), (154, some 155), (155, some 156), (156, some 157), (157, some 158), (158, some 159), (159, some 160), (160, some 161), (161, some 162), (162, some 163), (163, some 164), (164, some 165), (165, some 166), (166, some 167), (167, some 168), (168, some 169), (169, some 170), (170, some 171), (171, some 172), (172, some 173), (173, some 174), (174, some 175), (175, some 176), (176, some 177), (177, some 178), (178, some 179), (179, some 180), (180, some 181), (181, some 182), (182, some 183), (183, some 184), (184, some 185), (185, some 186), (186, some 187), (187, some 188), (188, some 189), (189, some 190), (190, some 191), (191, some 192), (192, some 193), (193, some 194), (194, some 195), (195, some 196), (196, some 197), (197, some 198), (198, some 199), (199, some 200), (200, some 528), (528, some 574), (574, some 613), (613, some 647), (647, some 659), (659, some 673), (673, some 696), (696, some 744), (744, some 753), (753, some 762), (762, some 772), (772, some 780), (780, some 798), (798, some 837), (837, some 852), (852, some 871), (871, some 903), (903, some 956), (956, some 965), (965, some 984), (984, some 993), (993, some 1954), (1954, some 2014), (2014, none)]] := by decide
  simp only [sortPairs, mergeAll, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  rfl

lemma rootTree_valid : rootTree.valid 0 0 S_val S_val = true := by decide

lemma rootTree_covers : rootTree.covers = true := by
  rw [GTree.covers, rootTree_ivs, sortPairs_rootIvs]
  decide

end OMA_MO34145

theorem OMA.solution : type_of% @Mathoverflow34145.rectangles_pack_square_501_div_500 :=
  OMA_MO34145.pack_of_valid_covers OMA_MO34145.rootTree
    OMA_MO34145.rootTree_valid OMA_MO34145.rootTree_covers
