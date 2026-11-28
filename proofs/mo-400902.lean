import OMAStatements.S_mo_400902

-- Problem: Largest disk contained in an ellipsoid
-- Upstream: formal-conjectures statements/mo-400902.lean:0 (declaration OMA.S_mo_400902.main)
-- Credit: @Dolcruz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Mo400902

open OMA.S_mo_400902

private lemma quad_nonneg (a b c : ℝ) (x : Point) : 0 ≤ quad a b c x := by
  unfold quad
  positivity

private lemma quad_eq_zero_iff {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (x : Point) :
    quad a b c x = 0 ↔ x = 0 := by
  constructor
  · intro h
    unfold quad at h
    have h0 : (x 0 / a) ^ 2 = 0 := by nlinarith [sq_nonneg (x 0 / a), sq_nonneg (x 1 / b), sq_nonneg (x 2 / c)]
    have h1 : (x 1 / b) ^ 2 = 0 := by nlinarith [sq_nonneg (x 0 / a), sq_nonneg (x 1 / b), sq_nonneg (x 2 / c)]
    have h2 : (x 2 / c) ^ 2 = 0 := by nlinarith [sq_nonneg (x 0 / a), sq_nonneg (x 1 / b), sq_nonneg (x 2 / c)]
    have hx0 : x 0 = 0 := (div_eq_zero_iff.1 (sq_eq_zero_iff.1 h0)).resolve_right ha
    have hx1 : x 1 = 0 := (div_eq_zero_iff.1 (sq_eq_zero_iff.1 h1)).resolve_right hb
    have hx2 : x 2 = 0 := (div_eq_zero_iff.1 (sq_eq_zero_iff.1 h2)).resolve_right hc
    ext i
    fin_cases i
    · exact hx0
    · exact hx1
    · exact hx2
  · rintro rfl
    simp [quad]

private lemma quad_parallelogram (a b c : ℝ) (o w : Point) :
    quad a b c (o + w) + quad a b c (o - w) = 2 * quad a b c o + 2 * quad a b c w := by
  simp only [quad, Pi.add_apply, Pi.sub_apply]
  ring

private lemma quad_decomp (a b c : ℝ) (x : Point) :
    quad a b c x =
      (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) / b ^ 2 - gapX a b * x 0 ^ 2 + gapZ b c * x 2 ^ 2 := by
  simp only [quad, gapX, gapZ, div_eq_mul_inv]
  ring

private lemma norm_sq_lincomb {u v : Point} (hF : Frame u v) (s t : ℝ) :
    (s • u + t • v) 0 ^ 2 + (s • u + t • v) 1 ^ 2 + (s • u + t • v) 2 ^ 2 = s ^ 2 + t ^ 2 := by
  rcases hF with ⟨hu, hv, huv⟩
  simp only [dotProduct, Fin.sum_univ_three] at hu hv huv
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination s ^ 2 * hu + t ^ 2 * hv + 2 * s * t * huv

private lemma quad_le_of_fits {a b c r : ℝ} {o u v : Point} (hfit : Fits a b c r o u v)
    {s t : ℝ} (hst : s ^ 2 + t ^ 2 ≤ r ^ 2) :
    quad a b c o + quad a b c (s • u + t • v) ≤ 1 := by
  have h1 : quad a b c (o + (s • u + t • v)) ≤ 1 := by
    have := hfit s t hst
    rwa [add_assoc] at this
  have h2 : quad a b c (o - (s • u + t • v)) ≤ 1 := by
    have hst' : (-s) ^ 2 + (-t) ^ 2 ≤ r ^ 2 := by nlinarith
    have := hfit (-s) (-t) hst'
    have heq : o + (-s) • u + (-t) • v = o - (s • u + t • v) := by
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rwa [heq] at this
  have hp := quad_parallelogram a b c o (s • u + t • v)
  linarith

private lemma gapX_nonneg {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) : 0 ≤ gapX a b := by
  unfold gapX
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hinv : a⁻¹ ≤ b⁻¹ := inv_anti₀ hb hba
  have hnn : 0 ≤ a⁻¹ := inv_nonneg.2 ha.le
  nlinarith

private lemma gapZ_nonneg {b c : ℝ} (hc : 0 < c) (hcb : c ≤ b) : 0 ≤ gapZ b c := by
  unfold gapZ
  have hb : 0 < b := lt_of_lt_of_le hc hcb
  have hinv : b⁻¹ ≤ c⁻¹ := inv_anti₀ hc hcb
  have hnn : 0 ≤ b⁻¹ := inv_nonneg.2 hb.le
  nlinarith

private lemma gapZ_pos {b c : ℝ} (hc : 0 < c) (hcb : c < b) : 0 < gapZ b c := by
  unfold gapZ
  have hb : 0 < b := lt_trans hc hcb
  have hinv : b⁻¹ < c⁻¹ := inv_strictAnti₀ hc hcb
  have hnn : 0 ≤ b⁻¹ := inv_nonneg.2 hb.le
  nlinarith

private lemma exists_zero_coord0 (u v : Point) (r : ℝ) :
    ∃ s t : ℝ, s ^ 2 + t ^ 2 = r ^ 2 ∧ (s • u + t • v) 0 = 0 := by
  by_cases h0 : u 0 ^ 2 + v 0 ^ 2 = 0
  · have hu0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (v 0)]
    refine ⟨r, 0, by ring, ?_⟩
    simp [hu0]
  · have hpos : 0 < u 0 ^ 2 + v 0 ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm h0)
    set L := Real.sqrt (u 0 ^ 2 + v 0 ^ 2)
    have hL : 0 < L := Real.sqrt_pos.2 hpos
    have hL2 : L ^ 2 = u 0 ^ 2 + v 0 ^ 2 := Real.sq_sqrt hpos.le
    refine ⟨r * v 0 / L, -(r * u 0) / L, ?_, ?_⟩
    · field_simp [hL.ne']
      nlinarith [hL2]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hL.ne']
      ring

private lemma part1 {a b c : ℝ} (hc : 0 < c) (hcb : c ≤ b)
    (r : ℝ) (o u v : Point) (hr : 0 ≤ r) (hF : Frame u v) (hfit : Fits a b c r o u v) :
    r ≤ b := by
  have hb : 0 < b := lt_of_lt_of_le hc hcb
  obtain ⟨s, t, hst, hw0⟩ := exists_zero_coord0 u v r
  have hle := quad_le_of_fits hfit hst.le
  have ho := quad_nonneg a b c o
  have hd := quad_decomp a b c (s • u + t • v)
  have hns := norm_sq_lincomb hF s t
  have hgz := gapZ_nonneg hc hcb
  have hq : r ^ 2 / b ^ 2 ≤ quad a b c (s • u + t • v) := by
    rw [hd, hns, hst, hw0]
    nlinarith [sq_nonneg ((s • u + t • v) 2)]
  have hr2 : r ^ 2 / b ^ 2 ≤ 1 := by linarith
  have hb2 : 0 < b ^ 2 := by positivity
  have hsq : r ^ 2 ≤ b ^ 2 := (div_le_one hb2).1 hr2
  nlinarith

private lemma part2 {a b c : ℝ} (hc : 0 < c) (hcb : c ≤ b) (hba : b ≤ a)
    (o u v : Point) (hF : Frame u v) :
    Fits a b c b o u v ↔
      o = 0 ∧ (b = c ∨ ∃ m : ℝ, gapZ b c * m ^ 2 ≤ gapX a b ∧
        u 2 = m * u 0 ∧ v 2 = m * v 0) := by
  have hb : 0 < b := lt_of_lt_of_le hc hcb
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hgx := gapX_nonneg hb hba
  have hgz := gapZ_nonneg hc hcb
  constructor
  · intro hfit
    have hzero_dir : ∀ s t : ℝ, s ^ 2 + t ^ 2 = b ^ 2 → (s • u + t • v) 0 = 0 →
        quad a b c o = 0 ∧ gapZ b c * (s • u + t • v) 2 ^ 2 = 0 := by
      intro s t hst hw0
      have hle := quad_le_of_fits hfit hst.le
      have ho := quad_nonneg a b c o
      have hd := quad_decomp a b c (s • u + t • v)
      have hns := norm_sq_lincomb hF s t
      have hbb : b ^ 2 / b ^ 2 = 1 := div_self (pow_ne_zero 2 hb.ne')
      rw [hd, hns, hst, hw0, hbb] at hle
      have hterm : 0 ≤ gapZ b c * (s • u + t • v) 2 ^ 2 := by positivity
      constructor <;> nlinarith
    obtain ⟨s0, t0, hst0, hw0⟩ := exists_zero_coord0 u v b
    have ho0 : o = 0 := (quad_eq_zero_iff ha.ne' hb.ne' hc.ne' o).1 (hzero_dir s0 t0 hst0 hw0).1
    refine ⟨ho0, ?_⟩
    by_cases hbc : b = c
    · exact Or.inl hbc
    · right
      have hcltb : c < b := lt_of_le_of_ne hcb (Ne.symm hbc)
      have hgz_pos : 0 < gapZ b c := gapZ_pos hc hcltb
      by_cases huv0 : u 0 ^ 2 + v 0 ^ 2 = 0
      · have hu0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (v 0)]
        have hv0 : v 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (v 0)]
        have h1 := (hzero_dir b 0 (by ring) (by simp [hu0])).2
        have h2 := (hzero_dir 0 b (by ring) (by simp [hv0])).2
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero, zero_add] at h1 h2
        have hu2 : u 2 = 0 := by
          have : (b * u 2) ^ 2 = 0 := (mul_eq_zero.1 h1).resolve_left hgz_pos.ne'
          exact (mul_eq_zero.1 (sq_eq_zero_iff.1 this)).resolve_left hb.ne'
        have hv2 : v 2 = 0 := by
          have : (b * v 2) ^ 2 = 0 := (mul_eq_zero.1 h2).resolve_left hgz_pos.ne'
          exact (mul_eq_zero.1 (sq_eq_zero_iff.1 this)).resolve_left hb.ne'
        exact ⟨0, by simpa using hgx, by simp [hu0, hu2], by simp [hv0, hv2]⟩
      · have hpos : 0 < u 0 ^ 2 + v 0 ^ 2 :=
          lt_of_le_of_ne (by positivity) (Ne.symm huv0)
        set L := Real.sqrt (u 0 ^ 2 + v 0 ^ 2)
        have hL : 0 < L := Real.sqrt_pos.2 hpos
        have hL2 : L ^ 2 = u 0 ^ 2 + v 0 ^ 2 := Real.sq_sqrt hpos.le
        have hst_perp : (b * v 0 / L) ^ 2 + (-(b * u 0) / L) ^ 2 = b ^ 2 := by
          field_simp [hL.ne']
          nlinarith [hL2]
        have hw0_perp : ((b * v 0 / L) • u + (-(b * u 0) / L) • v) 0 = 0 := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          field_simp [hL.ne']
          ring
        have hperp := (hzero_dir _ _ hst_perp hw0_perp).2
        have hw2_zero : ((b * v 0 / L) • u + (-(b * u 0) / L) • v) 2 = 0 :=
          sq_eq_zero_iff.1 ((mul_eq_zero.1 hperp).resolve_left hgz_pos.ne')
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hw2_zero
        have hdet : v 0 * u 2 - u 0 * v 2 = 0 := by
          have h1 : b * (v 0 * u 2 - u 0 * v 2) / L = 0 := by
            convert hw2_zero using 1
            ring
          have h2 : b * (v 0 * u 2 - u 0 * v 2) = 0 := (div_eq_zero_iff.1 h1).resolve_right hL.ne'
          exact (mul_eq_zero.1 h2).resolve_left hb.ne'
        set m := (u 0 * u 2 + v 0 * v 2) / (u 0 ^ 2 + v 0 ^ 2)
        have hum : u 2 = m * u 0 := by
          simp only [m]
          field_simp [hpos.ne']
          linear_combination v 0 * hdet
        have hvm : v 2 = m * v 0 := by
          simp only [m]
          field_simp [hpos.ne']
          linear_combination -u 0 * hdet
        refine ⟨m, ?_, hum, hvm⟩
        set s1 := b * u 0 / L
        set t1 := b * v 0 / L
        have hst1_eq : s1 ^ 2 + t1 ^ 2 = b ^ 2 := by
          simp only [s1, t1]
          have h1 : (b * u 0 / L) ^ 2 + (b * v 0 / L) ^ 2 = b ^ 2 * (u 0 ^ 2 + v 0 ^ 2) / L ^ 2 := by ring
          rw [h1, ← hL2, mul_div_cancel_right₀ _ (pow_ne_zero 2 hL.ne')]
        have hfit1 := hfit s1 t1 hst1_eq.le
        rw [ho0, zero_add] at hfit1
        have hd := quad_decomp a b c (s1 • u + t1 • v)
        have hns := norm_sq_lincomb hF s1 t1
        have hw0_1 : (s1 • u + t1 • v) 0 = b * L := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, s1, t1]
          have h1 : b * u 0 / L * u 0 + b * v 0 / L * v 0 = b * (u 0 ^ 2 + v 0 ^ 2) / L := by ring
          rw [h1, ← hL2, sq, ← mul_assoc, mul_div_cancel_right₀ _ hL.ne']
        have hw2_1 : (s1 • u + t1 • v) 2 = m * (s1 • u + t1 • v) 0 := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hum, hvm]
          ring
        have hbb : b ^ 2 / b ^ 2 = 1 := div_self (pow_ne_zero 2 hb.ne')
        rw [hd, hns, hst1_eq, hbb, hw2_1, hw0_1] at hfit1
        have hbL2 : 0 < (b * L) ^ 2 := by positivity
        have hdiff : (gapZ b c * m ^ 2 - gapX a b) * (b * L) ^ 2 ≤ 0 := by
          have : (gapZ b c * m ^ 2 - gapX a b) * (b * L) ^ 2 =
              (1 - gapX a b * (b * L) ^ 2 + gapZ b c * (m * (b * L)) ^ 2) - 1 := by ring
          linarith
        exact sub_nonpos.1 (nonpos_of_mul_nonpos_left hdiff hbL2)
  · rintro ⟨rfl, hcases⟩
    intro s t hst
    rw [zero_add, quad_decomp, norm_sq_lincomb hF s t]
    have hdiv : (s ^ 2 + t ^ 2) / b ^ 2 ≤ 1 := (div_le_one (by positivity : 0 < b ^ 2)).2 hst
    rcases hcases with rfl | ⟨m, hm, hum, hvm⟩
    · have hgz0 : gapZ b b = 0 := by simp [gapZ]
      rw [hgz0, zero_mul, add_zero]
      nlinarith [sq_nonneg ((s • u + t • v) 0)]
    · have hw2 : (s • u + t • v) 2 = m * (s • u + t • v) 0 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hum, hvm]
        ring
      rw [hw2]
      have hdiff : gapZ b c * (m * (s • u + t • v) 0) ^ 2 - gapX a b * (s • u + t • v) 0 ^ 2 ≤ 0 := by
        have : gapZ b c * (m * (s • u + t • v) 0) ^ 2 - gapX a b * (s • u + t • v) 0 ^ 2 =
            (gapZ b c * m ^ 2 - gapX a b) * (s • u + t • v) 0 ^ 2 := by ring
        rw [this]
        nlinarith [sq_nonneg ((s • u + t • v) 0)]
      linarith

private lemma part3 {a b c : ℝ} (hc : 0 < c) (hcb : c ≤ b) (hba : b ≤ a) :
    ∃ u v : Point, Frame u v ∧ ∀ s t : ℝ,
      quad a b c (s • u + t • v) = (s ^ 2 + t ^ 2) / b ^ 2 := by
  have hb : 0 < b := lt_of_lt_of_le hc hcb
  have hgx := gapX_nonneg hb hba
  have hgz := gapZ_nonneg hc hcb
  by_cases hD : gapX a b + gapZ b c = 0
  · have hgx0 : gapX a b = 0 := by linarith
    have hgz0 : gapZ b c = 0 := by linarith
    refine ⟨![0, 1, 0], ![1, 0, 0], ?_, ?_⟩
    · simp [Frame, dotProduct, Fin.sum_univ_three]
    · intro s t
      rw [quad_decomp, norm_sq_lincomb (by simp [Frame, dotProduct, Fin.sum_univ_three]), hgx0, hgz0]
      ring
  · set D := gapX a b + gapZ b c
    have hDpos : 0 < D := lt_of_le_of_ne (by linarith) (Ne.symm hD)
    let u : Point := ![0, 1, 0]
    let v : Point := ![Real.sqrt (gapZ b c / D), 0, Real.sqrt (gapX a b / D)]
    have hF : Frame u v := by
      simp only [Frame, u, v, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val]
      refine ⟨by norm_num, ?_, by norm_num⟩
      have h1 : Real.sqrt (gapZ b c / D) * Real.sqrt (gapZ b c / D) = gapZ b c / D :=
        Real.mul_self_sqrt (div_nonneg hgz hDpos.le)
      have h2 : Real.sqrt (gapX a b / D) * Real.sqrt (gapX a b / D) = gapX a b / D :=
        Real.mul_self_sqrt (div_nonneg hgx hDpos.le)
      rw [h1, h2]
      have : gapZ b c / D + 0 * 0 + gapX a b / D = (gapX a b + gapZ b c) / D := by ring
      rw [this]
      exact div_self hDpos.ne'
    refine ⟨u, v, hF, ?_⟩
    intro s t
    rw [quad_decomp, norm_sq_lincomb hF s t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, u, v, Matrix.cons_val_zero,
      Matrix.cons_val]
    have h1 : Real.sqrt (gapZ b c / D) ^ 2 = gapZ b c / D :=
      Real.sq_sqrt (div_nonneg hgz hDpos.le)
    have h2 : Real.sqrt (gapX a b / D) ^ 2 = gapX a b / D :=
      Real.sq_sqrt (div_nonneg hgx hDpos.le)
    have hcancel : gapZ b c * (s * 0 + t * Real.sqrt (gapX a b / D)) ^ 2 =
        gapX a b * (s * 0 + t * Real.sqrt (gapZ b c / D)) ^ 2 := by
      have hl : (s * 0 + t * Real.sqrt (gapX a b / D)) ^ 2 = t ^ 2 * (gapX a b / D) := by
        rw [mul_zero, zero_add, mul_pow, h2]
      have hr : (s * 0 + t * Real.sqrt (gapZ b c / D)) ^ 2 = t ^ 2 * (gapZ b c / D) := by
        rw [mul_zero, zero_add, mul_pow, h1]
      rw [hl, hr]
      ring
    linarith

theorem main_proof : type_of% @OMA.S_mo_400902.main := by
  intro a b c hc hcb hba
  exact ⟨part1 hc hcb, part2 hc hcb hba, part3 hc hcb hba⟩

end OMA.Mo400902

theorem OMA.solution : type_of% @OMA.S_mo_400902.main :=
  OMA.Mo400902.main_proof
