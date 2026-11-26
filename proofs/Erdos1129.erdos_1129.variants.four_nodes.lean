import FormalConjectures.ErdosProblems.«1129»

/-! Four-node interpolation is optimized by balancing the three gap maxima. -/

open Erdos1129

lemma OMA.four_coords (x : Fin 4 → ℝ) : x = ![x 0, x 1, x 2, x 3] := by
  funext i
  fin_cases i <;> rfl

lemma OMA.four_strict {a b : ℝ} (ha : -1 < a) (hab : a < b) (hb : b < 1) :
    StrictMono (![(-1 : ℝ), a, b, 1] : Fin 4 → ℝ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at * <;> linarith

lemma OMA.four_canonical {a b : ℝ} (ha : -1 < a) (hab : a < b) (hb : b < 1) :
    IsCanonical (![(-1 : ℝ), a, b, 1] : Fin 4 → ℝ) := by
  refine ⟨⟨OMA.four_strict ha hab hb, ?_⟩, ⟨0, rfl⟩, ⟨3, rfl⟩⟩
  intro i
  fin_cases i <;> norm_num [Set.mem_Icc] <;> constructor <;> linarith

lemma OMA.four_le_const (x : Fin 4 → ℝ) {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    lebesgueFunction x z ≤ lebesgueConstant x := by
  have hc : Continuous (lebesgueFunction x) := by
    unfold lebesgueFunction
    fun_prop
  exact le_csSup (isCompact_Icc.image hc).bddAbove ⟨z, hz, rfl⟩

lemma OMA.four_eval_prod (x : Fin 4 → ℝ) (i : Fin 4) (z : ℝ) :
    (Lagrange.basis Finset.univ x i).eval z =
      ∏ j ∈ Finset.univ.erase i, (z - x j) / (x i - x j) := by
  simp only [Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact (div_eq_inv_mul _ _).symm

noncomputable def OMA.four_values (a b z : ℝ) : Fin 4 → ℝ :=
  ![(z - a) * (z - b) * (1 - z) / (2 * (1 + a) * (1 + b)),
    (1 - z ^ 2) * (b - z) / ((b - a) * (1 - a ^ 2)),
    (1 - z ^ 2) * (z - a) / ((b - a) * (1 - b ^ 2)),
    (z - a) * (z - b) * (z + 1) / (2 * (1 - a) * (1 - b))]

lemma OMA.four_eval_canonical (a b z : ℝ) (ha : -1 < a) (hab : a < b) (hb : b < 1)
    (i : Fin 4) :
    (Lagrange.basis Finset.univ (![(-1 : ℝ), a, b, 1] : Fin 4 → ℝ) i).eval z =
      OMA.four_values a b z i := by
  rw [OMA.four_eval_prod]
  have h₀ : (Finset.univ : Finset (Fin 4)).erase 0 = {1, 2, 3} := by decide
  have h₁ : (Finset.univ : Finset (Fin 4)).erase 1 = {0, 2, 3} := by decide
  have h₂ : (Finset.univ : Finset (Fin 4)).erase 2 = {0, 1, 3} := by decide
  have h₃ : (Finset.univ : Finset (Fin 4)).erase 3 = {0, 1, 2} := by decide
  have ha₁ : 0 < 1 - a := by linarith
  have ha₂ : 0 < 1 + a := by linarith
  have hb₁ : 0 < 1 - b := by linarith
  have hb₂ : 0 < 1 + b := by linarith
  have hab₁ : a - b ≠ 0 := by linarith
  have hab₂ : b - a ≠ 0 := by linarith
  have ha₃ : (-1 : ℝ) - a ≠ 0 := by linarith
  have hb₃ : (-1 : ℝ) - b ≠ 0 := by linarith
  have ha₄ : a - (-1) ≠ 0 := by linarith
  have hb₄ : b - (-1) ≠ 0 := by linarith
  have ha₅ : a - 1 ≠ 0 := by linarith
  have hb₅ : b - 1 ≠ 0 := by linarith
  have hsqA : 1 - a ^ 2 ≠ 0 := by nlinarith [mul_pos ha₁ ha₂]
  have hsqB : 1 - b ^ 2 ≠ 0 := by nlinarith [mul_pos hb₁ hb₂]
  fin_cases i
  · change (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase 0, _) = OMA.four_values a b z 0
    rw [h₀, Finset.prod_insert (by decide : (1 : Fin 4) ∉ ({2, 3} : Finset (Fin 4))),
      Finset.prod_pair (by decide : (2 : Fin 4) ≠ 3)]
    change _ = (z - a) * (z - b) * (1 - z) / (2 * (1 + a) * (1 + b))
    change (z - a) / ((-1 : ℝ) - a) * ((z - b) / ((-1 : ℝ) - b) *
      ((z - 1) / ((-1 : ℝ) - 1))) = _
    field_simp [ha₃, hb₃, ha₂.ne', hb₂.ne']
    ring
  · change (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase 1, _) = OMA.four_values a b z 1
    rw [h₁, Finset.prod_insert (by decide : (0 : Fin 4) ∉ ({2, 3} : Finset (Fin 4))),
      Finset.prod_pair (by decide : (2 : Fin 4) ≠ 3)]
    change (z - (-1)) / (a - (-1)) * ((z - b) / (a - b) * ((z - 1) / (a - 1))) =
      (1 - z ^ 2) * (b - z) / ((b - a) * (1 - a ^ 2))
    field_simp [ha₄, ha₅, hab₁, hab₂, hsqA]
    ring
  · change (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase 2, _) = OMA.four_values a b z 2
    rw [h₂, Finset.prod_insert (by decide : (0 : Fin 4) ∉ ({1, 3} : Finset (Fin 4))),
      Finset.prod_pair (by decide : (1 : Fin 4) ≠ 3)]
    change (z - (-1)) / (b - (-1)) * ((z - a) / (b - a) * ((z - 1) / (b - 1))) =
      (1 - z ^ 2) * (z - a) / ((b - a) * (1 - b ^ 2))
    field_simp [hb₄, hb₅, hab₂, hsqB]
    ring
  · change (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase 3, _) = OMA.four_values a b z 3
    rw [h₃, Finset.prod_insert (by decide : (0 : Fin 4) ∉ ({1, 2} : Finset (Fin 4))),
      Finset.prod_pair (by decide : (1 : Fin 4) ≠ 2)]
    change (z - (-1)) / (1 - (-1)) * ((z - a) / (1 - a) * ((z - b) / (1 - b))) =
      (z - a) * (z - b) * (z + 1) / (2 * (1 - a) * (1 - b))
    field_simp [ha₁.ne', hb₁.ne']
    ring

lemma OMA.four_canonical_abs (a b z : ℝ) (ha : -1 < a) (hab : a < b) (hb : b < 1) :
    lebesgueFunction ![(-1 : ℝ), a, b, 1] z =
      |OMA.four_values a b z 0| + |OMA.four_values a b z 1| +
        |OMA.four_values a b z 2| + |OMA.four_values a b z 3| := by
  unfold lebesgueFunction
  simp only [OMA.four_eval_canonical a b z ha hab hb, Fin.sum_univ_four]

lemma OMA.four_canonical_sum (a b z : ℝ) (ha : -1 < a) (hab : a < b) (hb : b < 1) :
    OMA.four_values a b z 0 + OMA.four_values a b z 1 +
      OMA.four_values a b z 2 + OMA.four_values a b z 3 = 1 := by
  have hinj : Set.InjOn (![(-1 : ℝ), a, b, 1] : Fin 4 → ℝ) (Finset.univ : Finset (Fin 4)) :=
    (OMA.four_strict ha hab hb).injective.injOn
  have h := congrArg (Polynomial.eval z) (Lagrange.sum_basis hinj Finset.univ_nonempty)
  simp only [Polynomial.eval_add, Polynomial.eval_one, Fin.sum_univ_four,
    OMA.four_eval_canonical a b z ha hab hb] at h
  exact h

lemma OMA.four_pieces (a b z : ℝ) (ha : -1 < a) (hab : a < b) (hb : b < 1)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    (z ≤ a → lebesgueFunction ![(-1 : ℝ), a, b, 1] z =
      1 + 2 * ((1 - z ^ 2) * (a - z) / ((b - a) * (1 - b ^ 2)))) ∧
    (a ≤ z → z ≤ b → lebesgueFunction ![(-1 : ℝ), a, b, 1] z =
      1 + 2 * ((z - a) * (b - z) * (1 + a * b + (a + b) * z) /
        ((1 - a ^ 2) * (1 - b ^ 2)))) ∧
    (b ≤ z → lebesgueFunction ![(-1 : ℝ), a, b, 1] z =
      1 + 2 * ((1 - z ^ 2) * (z - b) / ((b - a) * (1 - a ^ 2)))) := by
  let A := OMA.four_values a b z 0
  let B := OMA.four_values a b z 1
  let C := OMA.four_values a b z 2
  let D := OMA.four_values a b z 3
  have hsum : A + B + C + D = 1 := OMA.four_canonical_sum a b z ha hab hb
  have hl : -1 ≤ z := hz.1
  have hr : z ≤ 1 := hz.2
  have hzsq : 0 ≤ 1 - z ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - z by linarith) (show 0 ≤ 1 + z by linarith)]
  have ha₁ : 0 < 1 - a := by linarith
  have ha₂ : 0 < 1 + a := by linarith
  have hb₁ : 0 < 1 - b := by linarith
  have hb₂ : 0 < 1 + b := by linarith
  have hasq : 0 < 1 - a ^ 2 := by nlinarith [mul_pos ha₁ ha₂]
  have hbsq : 0 < 1 - b ^ 2 := by nlinarith [mul_pos hb₁ hb₂]
  have hg : 0 < b - a := sub_pos.mpr hab
  have hBpos (h : z ≤ b) : 0 ≤ B := by
    change 0 ≤ (1 - z ^ 2) * (b - z) / ((b - a) * (1 - a ^ 2))
    exact div_nonneg (mul_nonneg hzsq (sub_nonneg.mpr h)) (mul_nonneg hg.le hasq.le)
  have hCpos (h : a ≤ z) : 0 ≤ C := by
    change 0 ≤ (1 - z ^ 2) * (z - a) / ((b - a) * (1 - b ^ 2))
    exact div_nonneg (mul_nonneg hzsq (sub_nonneg.mpr h)) (mul_nonneg hg.le hbsq.le)
  have hApos (h : 0 ≤ (z - a) * (z - b)) : 0 ≤ A := by
    change 0 ≤ (z - a) * (z - b) * (1 - z) / (2 * (1 + a) * (1 + b))
    exact div_nonneg (mul_nonneg h (by linarith)) (by positivity)
  have hDpos (h : 0 ≤ (z - a) * (z - b)) : 0 ≤ D := by
    change 0 ≤ (z - a) * (z - b) * (z + 1) / (2 * (1 - a) * (1 - b))
    exact div_nonneg (mul_nonneg h (by linarith)) (by positivity)
  rw [OMA.four_canonical_abs a b z ha hab hb]
  change (_ → |A| + |B| + |C| + |D| = _) ∧
    (_ → _ → |A| + |B| + |C| + |D| = _) ∧
    (_ → |A| + |B| + |C| + |D| = _)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hp : 0 ≤ (z - a) * (z - b) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    have hC : C = -((1 - z ^ 2) * (a - z) / ((b - a) * (1 - b ^ 2))) := by
      change (1 - z ^ 2) * (z - a) / ((b - a) * (1 - b ^ 2)) = _
      rw [show z - a = -(a - z) by ring, mul_neg, neg_div]
    have hnC : C ≤ 0 := by
      rw [hC]
      exact neg_nonpos.mpr (div_nonneg (mul_nonneg hzsq (by linarith)) (by positivity))
    rw [abs_of_nonneg (hApos hp), abs_of_nonneg (hBpos (by linarith)),
      abs_of_nonpos hnC, abs_of_nonneg (hDpos hp)]
    linarith only [hsum, hC]
  · intro hza hzb
    have hp : (z - a) * (z - b) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hA : A ≤ 0 := by
      change (z - a) * (z - b) * (1 - z) / (2 * (1 + a) * (1 + b)) ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hp (by linarith)) (by positivity)
    have hD : D ≤ 0 := by
      change (z - a) * (z - b) * (z + 1) / (2 * (1 - a) * (1 - b)) ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hp (by linarith)) (by positivity)
    have hAD : A + D = -((z - a) * (b - z) * (1 + a * b + (a + b) * z) /
        ((1 - a ^ 2) * (1 - b ^ 2))) := by
      change (z - a) * (z - b) * (1 - z) / (2 * (1 + a) * (1 + b)) +
        (z - a) * (z - b) * (z + 1) / (2 * (1 - a) * (1 - b)) = _
      field_simp [ha₁.ne', ha₂.ne', hb₁.ne', hb₂.ne', hasq.ne', hbsq.ne']
      ring
    rw [abs_of_nonpos hA, abs_of_nonneg (hBpos hzb),
      abs_of_nonneg (hCpos hza), abs_of_nonpos hD]
    linarith only [hsum, hAD]
  · intro h
    have hp : 0 ≤ (z - a) * (z - b) := mul_nonneg (by linarith) (by linarith)
    have hB : B = -((1 - z ^ 2) * (z - b) / ((b - a) * (1 - a ^ 2))) := by
      change (1 - z ^ 2) * (b - z) / ((b - a) * (1 - a ^ 2)) = _
      rw [show b - z = -(z - b) by ring, mul_neg, neg_div]
    have hnB : B ≤ 0 := by
      rw [hB]
      exact neg_nonpos.mpr (div_nonneg (mul_nonneg hzsq (by linarith)) (by positivity))
    rw [abs_of_nonneg (hApos hp), abs_of_nonpos hnB,
      abs_of_nonneg (hCpos (by linarith)), abs_of_nonneg (hDpos hp)]
    linarith only [hsum, hB]

lemma OMA.root_lt_half {t : ℝ} (ht : 0 < t)
    (hroot : 25 * t ^ 6 + 17 * t ^ 4 + 2 * t ^ 2 - 1 = 0) : t < 1 / 2 := by
  by_contra! h
  have hpow : (1 / 2 : ℝ) ^ 4 ≤ t ^ 4 := by gcongr
  nlinarith only [hroot, hpow, sq_nonneg t, pow_nonneg ht.le 6]

noncomputable def OMA.outer_profile (t z : ℝ) : ℝ := (1 - z ^ 2) * (z - t)

lemma OMA.outer_location {t : ℝ} (ht : 0 < t)
    (hroot : 25 * t ^ 6 + 17 * t ^ 4 + 2 * t ^ 2 - 1 = 0) :
    ∃ s : ℝ, t < s ∧ s < 1 ∧ OMA.outer_profile t s = 2 * t ^ 3 ∧
      ∀ z ≥ t, OMA.outer_profile t z ≤ 2 * t ^ 3 := by
  let s := t * (4 + 9 * t ^ 2) / (3 + t ^ 2)
  have hden : 0 < 3 + t ^ 2 := by positivity
  have hlin : (3 + t ^ 2) * s = t * (4 + 9 * t ^ 2) := by
    dsimp [s]
    field_simp
  have hcrit : 3 * s ^ 2 - 2 * t * s - 1 = 0 := by
    have h : (3 * s ^ 2 - 2 * t * s - 1) * (3 + t ^ 2) ^ 2 =
        9 * (25 * t ^ 6 + 17 * t ^ 4 + 2 * t ^ 2 - 1) := by
      dsimp [s]
      field_simp
      ring
    rw [hroot, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ hden.ne')
  have hts : t < s := by
    apply (lt_div_iff₀ hden).mpr
    nlinarith [mul_pos ht (show 0 < 1 + 8 * t ^ 2 by positivity)]
  have hmax : OMA.outer_profile t s = 2 * t ^ 3 := by
    calc
      OMA.outer_profile t s = 2 / 9 * ((3 + t ^ 2) * s - 4 * t) -
          (3 * s ^ 2 - 2 * t * s - 1) * (3 * s - t) / 9 := by
        unfold OMA.outer_profile
        ring
      _ = _ := by rw [hcrit, hlin]; ring
  have hs1 : s < 1 := by
    have hp : 0 < (1 - s ^ 2) * (s - t) := by
      change 0 < OMA.outer_profile t s
      rw [hmax]
      positivity
    have hsq : 0 < 1 - s ^ 2 := by
      by_contra! hno
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hno (by linarith))) hp
    nlinarith [sq_nonneg (s - 1)]
  refine ⟨s, hts, hs1, hmax, fun z hz => ?_⟩
  rw [← hmax]
  have heq : OMA.outer_profile t s - OMA.outer_profile t z =
      (z - s) ^ 2 * (z + 2 * s - t) + (z - s) * (3 * s ^ 2 - 2 * t * s - 1) := by
    unfold OMA.outer_profile
    ring
  rw [hcrit, mul_zero, add_zero] at heq
  linarith [mul_nonneg (sq_nonneg (z - s)) (show 0 ≤ z + 2 * s - t by linarith)]

lemma OMA.target_as_outer {t : ℝ} (ht : 0 < t) (ht' : t < 1 / 2) :
    (1 + t ^ 2) / (1 - t ^ 2) = 1 + (2 * t ^ 3) / (t * (1 - t ^ 2)) := by
  have hd : 1 - t ^ 2 ≠ 0 := by nlinarith [mul_pos ht (show 0 < 1 - t by linarith)]
  field_simp [ht.ne', hd]
  ring

lemma OMA.target_as_inner {t : ℝ} (ht : 0 < t) (ht' : t < 1 / 2) :
    (1 + t ^ 2) / (1 - t ^ 2) = 1 + 2 * (t ^ 2 / (1 - t ^ 2)) := by
  have hd : 1 - t ^ 2 ≠ 0 := by nlinarith [mul_pos ht (show 0 < 1 - t by linarith)]
  field_simp [hd]
  ring

lemma OMA.half_gap_scale (u g d : ℝ) (hg : 0 < g) (hd : 0 < d) :
    2 * (u / ((2 * g) * d)) = u / (g * d) := by
  field_simp [hg.ne', hd.ne']

lemma OMA.symmetric_value {t : ℝ} (ht : 0 < t) (ht' : t < 1 / 2)
    (hupper : ∀ z ≥ t, OMA.outer_profile t z ≤ 2 * t ^ 3) :
    lebesgueConstant (![(-1 : ℝ), -t, t, 1] : Fin 4 → ℝ) =
      (1 + t ^ 2) / (1 - t ^ 2) := by
  have htden : 0 < 1 - t ^ 2 := by nlinarith [mul_pos ht (show 0 < 1 - t by linarith)]
  have hmiddle (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) (ha : -t ≤ z) (hb : z ≤ t) :
      lebesgueFunction ![(-1 : ℝ), -t, t, 1] z = 1 + 2 * ((t ^ 2 - z ^ 2) / (1 - t ^ 2)) := by
    rw [(OMA.four_pieces (-t) t z (by linarith) (by linarith) (by linarith) hz).2.1 ha hb]
    rw [neg_sq]
    field_simp [htden.ne']
    ring
  have hcenter : lebesgueFunction ![(-1 : ℝ), -t, t, 1] 0 = (1 + t ^ 2) / (1 - t ^ 2) := by
    rw [hmiddle 0 (by norm_num) (by linarith) ht.le, OMA.target_as_inner ht ht']
    simp
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, 0, by norm_num, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨hl, _, hr⟩ := OMA.four_pieces (-t) t z (by linarith) (by linarith) (by linarith) hz
      by_cases ha : z < -t
      · have heq : (1 - z ^ 2) * (-t - z) = OMA.outer_profile t (-z) := by
          unfold OMA.outer_profile
          ring
        rw [hl ha.le, show t - -t = 2 * t by ring, heq,
          OMA.half_gap_scale _ _ _ ht htden, OMA.target_as_outer ht ht']
        have h := div_le_div_of_nonneg_right (hupper (-z) (by linarith))
          (mul_nonneg ht.le htden.le)
        linarith only [h]
      · by_cases hb : t < z
        · rw [hr hb.le, neg_sq, show t - -t = 2 * t by ring,
            OMA.half_gap_scale _ _ _ ht htden, OMA.target_as_outer ht ht']
          change 1 + OMA.outer_profile t z / _ ≤ _
          have h := div_le_div_of_nonneg_right (hupper z hb.le) (mul_nonneg ht.le htden.le)
          linarith only [h]
        · rw [hmiddle z hz (le_of_not_gt ha) (le_of_not_gt hb), OMA.target_as_inner ht ht']
          have h := div_le_div_of_nonneg_right (show t ^ 2 - z ^ 2 ≤ t ^ 2 by linarith [sq_nonneg z])
            htden.le
          linarith
  · rw [← hcenter]
    exact OMA.four_le_const _ (by norm_num)

lemma OMA.four_affine (x : Fin 4 → ℝ) (z r c : ℝ) (hr : r ≠ 0) :
    lebesgueFunction (fun i => r * x i + c) (r * z + c) = lebesgueFunction x z := by
  simp only [lebesgueFunction_eq]
  have heq (a b : ℝ) : r * a + c - (r * b + c) = r * (a - b) := by ring
  simp_rw [heq, mul_div_mul_left _ _ hr]

lemma OMA.normalize_four (x : Fin 4 → ℝ) (hx : IsNodeSet x) :
    ∃ a b : ℝ, -1 < a ∧ a < b ∧ b < 1 ∧
      lebesgueConstant (![(-1 : ℝ), a, b, 1] : Fin 4 → ℝ) ≤ lebesgueConstant x := by
  let r := (x 3 - x 0) / 2
  let c := (x 3 + x 0) / 2
  let y (i : Fin 4) := (x i - c) / r
  have h03 : x 0 < x 3 := hx.1 (by decide)
  have hr : 0 < r := by dsimp [r]; linarith
  have hy : StrictMono y := by
    intro i j hij
    exact (div_lt_div_iff_of_pos_right hr).mpr (sub_lt_sub_right (hx.1 hij) _)
  have hy0 : y 0 = -1 := by
    apply (div_eq_iff hr.ne').mpr
    dsimp [c, r]
    ring
  have hy3 : y 3 = 1 := by
    apply (div_eq_iff hr.ne').mpr
    dsimp [c, r]
    ring
  have hback : (fun i => r * y i + c) = x := by
    funext i
    dsimp [y]
    field_simp
    ring
  refine ⟨y 1, y 2, hy0 ▸ hy (by decide : (0 : Fin 4) < 1), hy (by decide),
    hy3 ▸ hy (by decide : (2 : Fin 4) < 3), ?_⟩
  have htuple : y = ![(-1 : ℝ), y 1, y 2, 1] := by
    calc
      y = ![y 0, y 1, y 2, y 3] := OMA.four_coords y
      _ = _ := by rw [hy0, hy3]
  rw [← htuple]
  apply csSup_le
  · exact ⟨_, 0, by norm_num, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hzero : r * (-1 : ℝ) + c = x 0 := by dsimp [r, c]; ring
    have hone : r * (1 : ℝ) + c = x 3 := by dsimp [r, c]; ring
    have hL : r * (-1 : ℝ) + c ≤ r * z + c :=
      add_le_add_left (mul_le_mul_of_nonneg_left hz.1 hr.le) c
    have hR : r * z + c ≤ r * (1 : ℝ) + c :=
      add_le_add_left (mul_le_mul_of_nonneg_left hz.2 hr.le) c
    rw [hzero] at hL
    rw [hone] at hR
    have h := OMA.four_affine y z r c hr.ne'
    rw [hback] at h
    rw [← h]
    exact OMA.four_le_const x ⟨(hx.2 0).1.trans hL, hR.trans (hx.2 3).2⟩

lemma OMA.middle_comparison (a b t : ℝ) (ha : -1 < a) (hab : a < b) (hb : b < 1)
    (ht : 0 < t) (ht' : t < 1 / 2) (htg : t ≤ (b - a) / 2)
    (hstrict : t < (b - a) / 2 ∨ a + b ≠ 0) :
    (1 + t ^ 2) / (1 - t ^ 2) < lebesgueConstant (![(-1 : ℝ), a, b, 1] : Fin 4 → ℝ) := by
  let g := (b - a) / 2
  let h := (a + b) / 2
  let u := 1 - g ^ 2
  let d := (1 - a ^ 2) * (1 - b ^ 2)
  let p := g ^ 2 * (u + 3 * h ^ 2)
  change t ≤ g at htg
  change t < g ∨ a + b ≠ 0 at hstrict
  have hg : 0 < g := ht.trans_le htg
  have hh₁ : a ≤ h := by dsimp [h]; linarith
  have hh₂ : h ≤ b := by dsimp [h]; linarith
  have hh : h ∈ Set.Icc (-1 : ℝ) 1 := ⟨ha.le.trans hh₁, hh₂.trans hb.le⟩
  have he₁ : a = h - g := by dsimp [h, g]; ring
  have he₂ : b = h + g := by dsimp [h, g]; ring
  have hAn : 0 < 1 - a ^ 2 := by
    nlinarith [mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 + a by linarith)]
  have hBn : 0 < 1 - b ^ 2 := by
    nlinarith [mul_pos (show 0 < 1 - b by linarith) (show 0 < 1 + b by linarith)]
  have hd : 0 < d := mul_pos hAn hBn
  have hv : 0 < u - h ^ 2 := by
    have heq : (1 - a ^ 2) + (1 - b ^ 2) = 2 * (u - h ^ 2) := by
      rw [he₁, he₂]; dsimp [u]; ring
    linarith
  have hu : 0 < u := by linarith [sq_nonneg h]
  have hd_bdd : d ≤ u ^ 2 := by
    have heq : d = (u - h ^ 2) ^ 2 - 4 * (g ^ 2 * h ^ 2) := by
      dsimp only [d, u]
      rw [he₁, he₂]
      ring
    calc
      d ≤ (u - h ^ 2) ^ 2 := by
        linarith [mul_nonneg (sq_nonneg g) (sq_nonneg h)]
      _ ≤ u ^ 2 := pow_le_pow_left₀ hv.le (by linarith [sq_nonneg h]) 2
  have hcross : g ^ 2 * d ≤ (g ^ 2 * u) * u := by
    have hm := mul_le_mul_of_nonneg_left hd_bdd (sq_nonneg g)
    calc
      g ^ 2 * d ≤ g ^ 2 * u ^ 2 := hm
      _ = _ := by ring
  have hbase : g ^ 2 * u ≤ p :=
    mul_le_mul_of_nonneg_left (by linarith [sq_nonneg h]) (sq_nonneg g)
  have hrat : g ^ 2 / u ≤ p / d :=
    (div_le_div_iff₀ hu hd).mpr (hcross.trans (mul_le_mul_of_nonneg_right hbase hu.le))
  have htden : 0 < 1 - t ^ 2 := by nlinarith [mul_pos ht (show 0 < 1 - t by linarith)]
  have hcompare : t ^ 2 / (1 - t ^ 2) < p / d := by
    rcases hstrict with hgt | hshift
    · refine lt_of_lt_of_le ?_ hrat
      apply (div_lt_div_iff₀ htden hu).mpr
      have hh := pow_lt_pow_left₀ hgt ht.le (by decide : (2 : ℕ) ≠ 0)
      dsimp [u]
      nlinarith only [hh]
    · have hshift' : h ≠ 0 := by dsimp [h]; exact div_ne_zero hshift (by norm_num)
      have hp : g ^ 2 * u < p := by
        apply mul_lt_mul_of_pos_left
        · linarith [sq_pos_of_ne_zero hshift']
        · positivity
      have hrat' : g ^ 2 / u < p / d :=
        (div_lt_div_iff₀ hu hd).mpr (hcross.trans_lt (mul_lt_mul_of_pos_right hp hu))
      refine (show t ^ 2 / (1 - t ^ 2) ≤ g ^ 2 / u from ?_).trans_lt hrat'
      apply (div_le_div_iff₀ htden hu).mpr
      have hh := pow_le_pow_left₀ ht.le htg 2
      dsimp [u]
      nlinarith only [hh]
  have hmid : lebesgueFunction ![(-1 : ℝ), a, b, 1] h = 1 + 2 * (p / d) := by
    rw [(OMA.four_pieces a b h ha hab hb hh).2.1 hh₁ hh₂]
    dsimp only [p, d, u]
    have heq : (h - a) * (b - h) * (1 + a * b + (a + b) * h) =
        g ^ 2 * (1 - g ^ 2 + 3 * h ^ 2) := by
      rw [he₁, he₂]
      ring
    rw [heq]
  refine lt_of_lt_of_le ?_ (OMA.four_le_const _ hh)
  rw [hmid, OMA.target_as_inner ht ht']
  linarith only [hcompare]

lemma OMA.outer_ratio_comparison {t g s a b : ℝ} (ht : 0 < t) (ht' : t < 1 / 2)
    (hg : 0 < g) (hgt : g < t) (hst : t < s) (hs : s < 1)
    (ha : -t < a) (hb₁ : g ≤ b) (hb₂ : b < 1) :
    OMA.outer_profile t s / (t * (1 - t ^ 2)) <
      (1 - s ^ 2) * (s + a) / (g * (1 - b ^ 2)) := by
  have hspos : 0 < s := ht.trans hst
  have hsp : 0 < 1 - s ^ 2 := by nlinarith [mul_pos hspos (show 0 < 1 - s by linarith)]
  have hbp : 0 < 1 - b ^ 2 := by
    nlinarith [mul_pos (hg.trans_le hb₁) (show 0 < 1 - b by linarith)]
  have htp : 0 < 1 - t ^ 2 := by nlinarith [mul_pos ht (show 0 < 1 - t by linarith)]
  have hn : 0 ≤ OMA.outer_profile t s := by
    unfold OMA.outer_profile
    exact mul_nonneg hsp.le (sub_nonneg.mpr hst.le)
  have hn_lt : OMA.outer_profile t s < (1 - s ^ 2) * (s + a) := by
    unfold OMA.outer_profile
    exact mul_lt_mul_of_pos_left (by linarith) hsp
  have hd_le : g * (1 - b ^ 2) ≤ t * (1 - t ^ 2) := by
    calc
      g * (1 - b ^ 2) ≤ g * (1 - g ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (sub_le_sub_left (pow_le_pow_left₀ hg.le hb₁ 2) 1) hg.le
      _ ≤ t * (1 - t ^ 2) := by
        have h₁ : t ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ ht.le ht'.le 2
        have h₂ : g ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hg.le (hgt.trans ht').le 2
        have h₃ : t * g ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) :=
          mul_le_mul ht'.le (hgt.trans ht').le hg.le (by norm_num)
        have h := mul_nonneg (sub_nonneg.mpr hgt.le)
          (show 0 ≤ 1 - (t ^ 2 + t * g + g ^ 2) by nlinarith only [h₁, h₂, h₃])
        nlinarith only [h]
  apply (div_lt_div_iff₀ (mul_pos ht htp) (mul_pos hg hbp)).mpr
  exact (mul_le_mul_of_nonneg_left hd_le hn).trans_lt (mul_lt_mul_of_pos_right hn_lt (mul_pos ht htp))

lemma OMA.four_strict_comparison {t s a b : ℝ} (ha : -1 < a) (hab : a < b) (hb : b < 1)
    (ht : 0 < t) (ht' : t < 1 / 2) (hts : t < s) (hs : s < 1)
    (hmax : OMA.outer_profile t s = 2 * t ^ 3) (hne : ¬ (a = -t ∧ b = t)) :
    (1 + t ^ 2) / (1 - t ^ 2) < lebesgueConstant (![(-1 : ℝ), a, b, 1] : Fin 4 → ℝ) := by
  let g := (b - a) / 2
  have hg : 0 < g := by dsimp [g]; linarith
  have h2g : b - a = 2 * g := by dsimp [g]; ring
  have hspos : 0 < s := ht.trans hts
  by_cases hg_lt : g < t
  · by_cases hsum : 0 ≤ a + b
    · have hlow : -t < a := by dsimp [g] at hg_lt; linarith
      have hhigh : g ≤ b := by dsimp [g]; linarith
      have hza : -s ≤ a := by linarith
      have hz : -s ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have hbd : 0 < 1 - b ^ 2 := by nlinarith [mul_pos (hg.trans_le hhigh) (show 0 < 1 - b by linarith)]
      have hrat := OMA.outer_ratio_comparison ht ht' hg hg_lt hts hs hlow hhigh hb
      refine lt_of_lt_of_le ?_ (OMA.four_le_const _ hz)
      rw [(OMA.four_pieces a b (-s) ha hab hb hz).1 hza, h2g, neg_sq,
        show a - -s = s + a by ring, OMA.half_gap_scale _ _ _ hg hbd,
        OMA.target_as_outer ht ht', ← hmax]
      linarith only [hrat]
    · have hlow : -t < -b := by dsimp [g] at hg_lt; linarith
      have hhigh : g ≤ -a := by dsimp [g]; linarith
      have hzb : b ≤ s := by linarith
      have hz : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, hs.le⟩
      have haneg : -a < 1 := by linarith
      have had : 0 < 1 - a ^ 2 := by nlinarith [mul_pos (hg.trans_le hhigh) (show 0 < 1 + a by linarith)]
      have hrat := OMA.outer_ratio_comparison ht ht' hg hg_lt hts hs hlow hhigh haneg
      rw [neg_sq, show s + -b = s - b by ring] at hrat
      refine lt_of_lt_of_le ?_ (OMA.four_le_const _ hz)
      rw [(OMA.four_pieces a b s ha hab hb hz).2.2 hzb, h2g,
        OMA.half_gap_scale _ _ _ hg had, OMA.target_as_outer ht ht', ← hmax]
      linarith only [hrat]
  · have hge : t ≤ g := le_of_not_gt hg_lt
    refine OMA.middle_comparison a b t ha hab hb ht ht' hge ?_
    by_cases ht_lt : t < g
    · exact Or.inl ht_lt
    · dsimp [g] at ht_lt hge
      refine Or.inr fun heq => hne ⟨?_, ?_⟩
      · linarith
      · linarith

theorem OMA.solution : type_of% @Erdos1129.erdos_1129.variants.four_nodes := by
  intro t ht hroot
  have ht' := OMA.root_lt_half ht hroot
  obtain ⟨s, hts, hs, hsmax, hupper⟩ := OMA.outer_location ht hroot
  have hVal := OMA.symmetric_value ht ht' hupper
  have hcan : IsCanonical (![(-1 : ℝ), -t, t, 1] : Fin 4 → ℝ) :=
    OMA.four_canonical (by linarith) (by linarith) (by linarith)
  refine ⟨?_, hVal⟩
  ext x
  change (IsCanonical x ∧ IsMinimiser x) ↔ x ∈ ({![(-1 : ℝ), -t, t, 1]} : Set (Fin 4 → ℝ))
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hmin⟩
    have hA : x 0 = -1 := by
      obtain ⟨i, hi⟩ := hx.2.1
      refine le_antisymm ?_ (hx.1.2 0).1
      rw [← hi]
      exact hx.1.1.monotone (Fin.zero_le i)
    have hD : x 3 = 1 := by
      obtain ⟨i, hi⟩ := hx.2.2
      refine le_antisymm (hx.1.2 3).2 ?_
      rw [← hi]
      exact hx.1.1.monotone (by fin_cases i <;> decide)
    have ha : -1 < x 1 := hA ▸ hx.1.1 (by decide : (0 : Fin 4) < 1)
    have hab : x 1 < x 2 := hx.1.1 (by decide)
    have hb : x 2 < 1 := hD ▸ hx.1.1 (by decide : (2 : Fin 4) < 3)
    have hx' : x = ![(-1 : ℝ), x 1, x 2, 1] := by
      calc
        x = ![x 0, x 1, x 2, x 3] := OMA.four_coords x
        _ = _ := by rw [hA, hD]
    have hcoords : x 1 = -t ∧ x 2 = t := by
      by_contra hcoords
      have hlt := OMA.four_strict_comparison ha hab hb ht ht' hts hs hsmax hcoords
      have hmin' := hmin.2 _ hcan.1
      rw [hVal, hx'] at hmin'
      exact (not_lt_of_ge hmin') hlt
    obtain ⟨hB, hC⟩ := hcoords
    calc
      x = ![x 0, x 1, x 2, x 3] := OMA.four_coords x
      _ = _ := by rw [hA, hB, hC, hD]
  · rintro rfl
    refine ⟨hcan, hcan.1, ?_⟩
    intro y hy
    obtain ⟨a, b, ha, hab, hb, hle⟩ := OMA.normalize_four y hy
    refine le_trans ?_ hle
    by_cases h : a = -t ∧ b = t
    · rw [h.1, h.2]
    · rw [hVal]
      exact (OMA.four_strict_comparison ha hab hb ht ht' hts hs hsmax h).le