import OMAReductions.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1

/-!
# Proof of H1: Maxwell's conjecture for three equal non-zero charges

Direct elementary proof of `Arxiv.2607.27197.maxwell_conjecture.variants.three_equal_magnitudes.R1.H1`
via Tsai's inverse map `Φ_+(p) = p + F(p) / ‖F(p)‖^(3/2)` in Apollonian `(u, c)` coordinates,
horizontal-slice monotonicity, verified integer-interval certificates on the caustic region,
and implicit-curve branch counting.
-/

-- Credit: @yhay81

namespace MaxwellH1

/- Section 1: Normalization, upper half-plane containment, and Tsai's inverse map -/

noncomputable def r1 (x y : ℝ) : ℝ := Real.sqrt ((x + 1) ^ 2 + y ^ 2)
noncomputable def r2 (x y : ℝ) : ℝ := Real.sqrt ((x - 1) ^ 2 + y ^ 2)

noncomputable def Fx (x y : ℝ) : ℝ := (x + 1) / (r1 x y) ^ 3 + (x - 1) / (r2 x y) ^ 3
noncomputable def Fy0 (x y : ℝ) : ℝ := 1 / (r1 x y) ^ 3 + 1 / (r2 x y) ^ 3
noncomputable def Fy (x y : ℝ) : ℝ := y * Fy0 x y

noncomputable def Fsq (x y : ℝ) : ℝ := (Fx x y) ^ 2 + (Fy x y) ^ 2
noncomputable def Fn (x y : ℝ) : ℝ := Real.sqrt (Fsq x y)
noncomputable def Fq (x y : ℝ) : ℝ := Real.sqrt (Fn x y)

noncomputable def phiU (x y : ℝ) : ℝ := x + Fx x y / (Fq x y) ^ 3
noncomputable def phiV (x y : ℝ) : ℝ := y + Fy x y / (Fq x y) ^ 3

lemma r1_pos (x : ℝ) {y : ℝ} (hy : 0 < y) : 0 < r1 x y :=
  Real.sqrt_pos.mpr (by positivity)

lemma r2_pos (x : ℝ) {y : ℝ} (hy : 0 < y) : 0 < r2 x y :=
  Real.sqrt_pos.mpr (by positivity)

lemma r1_sq (x y : ℝ) : (r1 x y) ^ 2 = (x + 1) ^ 2 + y ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma r2_sq (x y : ℝ) : (r2 x y) ^ 2 = (x - 1) ^ 2 + y ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma Fy_eq (x y : ℝ) : Fy x y = y / (r1 x y) ^ 3 + y / (r2 x y) ^ 3 := by
  unfold Fy Fy0; ring

lemma Fy_pos (x : ℝ) {y : ℝ} (hy : 0 < y) : 0 < Fy x y := by
  have h1 := r1_pos x hy; have h2 := r2_pos x hy; rw [Fy_eq]; positivity

lemma Fsq_pos (x : ℝ) {y : ℝ} (hy : 0 < y) : 0 < Fsq x y := by
  have h := Fy_pos x hy; unfold Fsq; positivity

lemma Fn_pos (x : ℝ) {y : ℝ} (hy : 0 < y) : 0 < Fn x y :=
  Real.sqrt_pos.mpr (Fsq_pos x hy)

lemma Fq_pos (x : ℝ) {y : ℝ} (hy : 0 < y) : 0 < Fq x y :=
  Real.sqrt_pos.mpr (Fn_pos x hy)

lemma Fn_sq (x y : ℝ) : (Fn x y) ^ 2 = Fsq x y :=
  Real.sq_sqrt (by unfold Fsq; positivity)

lemma Fq_sq (x y : ℝ) : (Fq x y) ^ 2 = Fn x y :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

lemma Fq_pow4 (x y : ℝ) : (Fq x y) ^ 4 = Fsq x y := by
  calc (Fq x y) ^ 4 = ((Fq x y) ^ 2) ^ 2 := by ring
    _ = (Fn x y) ^ 2 := by rw [Fq_sq]
    _ = Fsq x y := Fn_sq x y

lemma r1_neg_x (x y : ℝ) : r1 (-x) y = r2 x y := by unfold r1 r2; congr 1; ring
lemma r2_neg_x (x y : ℝ) : r2 (-x) y = r1 x y := by unfold r1 r2; congr 1; ring
lemma Fx_neg_x (x y : ℝ) : Fx (-x) y = -Fx x y := by unfold Fx; rw [r1_neg_x, r2_neg_x]; ring
lemma Fy0_neg_x (x y : ℝ) : Fy0 (-x) y = Fy0 x y := by unfold Fy0; rw [r1_neg_x, r2_neg_x]; ring
lemma Fy_neg_x (x y : ℝ) : Fy (-x) y = Fy x y := by unfold Fy; rw [Fy0_neg_x]
lemma Fsq_neg_x (x y : ℝ) : Fsq (-x) y = Fsq x y := by unfold Fsq; rw [Fx_neg_x, Fy_neg_x]; ring
lemma Fq_neg_x (x y : ℝ) : Fq (-x) y = Fq x y := by unfold Fq Fn; rw [Fsq_neg_x]
lemma phiU_neg_x (x y : ℝ) : phiU (-x) y = -phiU x y := by unfold phiU; rw [Fx_neg_x, Fq_neg_x]; ring
lemma phiV_neg_x (x y : ℝ) : phiV (-x) y = phiV x y := by unfold phiV; rw [Fy_neg_x, Fq_neg_x]
lemma phiU_zero (y : ℝ) : phiU 0 y = 0 := by have h := phiU_neg_x 0 y; simp at h; linarith

lemma encard_le_phi_preimage (q : Fin 3 → ℝ) (u w : ℝ) (hw : w ≠ 0)
    (hq0 : ∀ j, q j ≠ 0) (hqeq : ∀ i j, q i = q j) :
    ∃ u₀ w₀ : ℝ, 0 ≤ u₀ ∧ 0 < w₀ ∧
      {p : ℝ × ℝ | (∀ j, (p.1 - ![0, 1, u] j) ^ 2 + (p.2 - ![0, 0, w] j) ^ 2 ≠ 0) ∧
        ∑ j, q j * (p.1 - ![0, 1, u] j) /
          Real.sqrt ((p.1 - ![0, 1, u] j) ^ 2 + (p.2 - ![0, 0, w] j) ^ 2) ^ 3 = 0 ∧
        ∑ j, q j * (p.2 - ![0, 0, w] j) /
          Real.sqrt ((p.1 - ![0, 1, u] j) ^ 2 + (p.2 - ![0, 0, w] j) ^ 2) ^ 3 = 0}.encard ≤
      {p : ℝ × ℝ | 0 < p.2 ∧ phiU p.1 p.2 = u₀ ∧ phiV p.1 p.2 = w₀}.encard := by
  set sy : ℝ := if 0 < w then 1 else -1
  have hsy_sq : sy ^ 2 = 1 := by by_cases h : 0 < w <;> simp [sy, h]
  have hsy_ne : sy ≠ 0 := by intro h; rw [h] at hsy_sq; norm_num at hsy_sq
  have hsyw : 0 < 2 * sy * w := by
    by_cases h : 0 < w
    · simp only [sy, if_pos h]; linarith
    · simp only [sy, if_neg h]
      have hwlt : w < 0 := lt_of_le_of_ne (not_lt.mp h) hw
      linarith
  set sx : ℝ := if 0 ≤ 2 * u - 1 then 1 else -1
  have hsx_sq : sx ^ 2 = 1 := by by_cases h : 0 ≤ 2 * u - 1 <;> simp [sx, h]
  have hsx_ne : sx ≠ 0 := by intro h; rw [h] at hsx_sq; norm_num at hsx_sq
  set u₀ : ℝ := sx * (2 * u - 1)
  set w₀ : ℝ := 2 * sy * w
  have hu₀ : 0 ≤ u₀ := by
    by_cases h : 0 ≤ 2 * u - 1
    · simp only [u₀, sx, if_pos h]; linarith
    · simp only [u₀, sx, if_neg h]; linarith
  refine ⟨u₀, w₀, hu₀, hsyw, ?_⟩
  let T : ℝ × ℝ → ℝ × ℝ := fun p => (sx * (2 * p.1 - 1), 2 * sy * p.2)
  have hTinj : Function.Injective T := by
    intro a b hab
    simp only [T, Prod.mk.injEq] at hab
    have h1 : 2 * a.1 - 1 = 2 * b.1 - 1 := mul_left_cancel₀ hsx_ne hab.1
    have h2 : a.2 = b.2 := mul_left_cancel₀ (mul_ne_zero two_ne_zero hsy_ne) (by linarith [hab.2])
    exact Prod.ext (by linarith) h2
  refine Set.encard_le_encard_of_injOn ?_ hTinj.injOn
  intro p hp
  rcases hp with ⟨hneq, hxsum, hysum⟩
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, sub_zero] at hxsum hysum
  rw [hqeq 1 0, hqeq 2 0] at hxsum hysum
  have hq0ne : q 0 ≠ 0 := hq0 0
  have hd2 : (p.1 - u) ^ 2 + (p.2 - w) ^ 2 ≠ 0 := by simpa using hneq 2
  set x := sx * (2 * p.1 - 1)
  set y := 2 * sy * p.2
  have hsum_x : p.1 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ^ 3 +
      (p.1 - 1) / Real.sqrt ((p.1 - 1) ^ 2 + p.2 ^ 2) ^ 3 +
      (p.1 - u) / Real.sqrt ((p.1 - u) ^ 2 + (p.2 - w) ^ 2) ^ 3 = 0 := by
    apply mul_left_cancel₀ hq0ne; linear_combination hxsum
  have hsum_y : p.2 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ^ 3 +
      p.2 / Real.sqrt ((p.1 - 1) ^ 2 + p.2 ^ 2) ^ 3 +
      (p.2 - w) / Real.sqrt ((p.1 - u) ^ 2 + (p.2 - w) ^ 2) ^ 3 = 0 := by
    apply mul_left_cancel₀ hq0ne; linear_combination hysum
  have hdist2 : (x - u₀) ^ 2 + (y - w₀) ^ 2 = 4 * ((p.1 - u) ^ 2 + (p.2 - w) ^ 2) := by
    simp only [x, y, u₀, w₀]
    linear_combination 4 * (p.1 - u) ^ 2 * hsx_sq + 4 * (p.2 - w) ^ 2 * hsy_sq
  have hr3_pos : 0 < Real.sqrt ((x - u₀) ^ 2 + (y - w₀) ^ 2) := by
    rw [hdist2]; refine Real.sqrt_pos.mpr ?_
    have : 0 < (p.1 - u) ^ 2 + (p.2 - w) ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hd2)
    linarith
  have hsqrt4 : ∀ (z : ℝ), 0 ≤ z → Real.sqrt (4 * z) = 2 * Real.sqrt z := by
    intro z _
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by norm_num]
  have h0 : Real.sqrt ((x - u₀) ^ 2 + (y - w₀) ^ 2) = 2 * Real.sqrt ((p.1 - u) ^ 2 + (p.2 - w) ^ 2) := by
    rw [hdist2, hsqrt4 _ (by positivity)]
  have hFx_rel : Fx x y + (x - u₀) / Real.sqrt ((x - u₀) ^ 2 + (y - w₀) ^ 2) ^ 3 = 0 := by
    by_cases hs : sx = 1
    · have hr1e : r1 x y = 2 * Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
        unfold r1
        have : (x + 1) ^ 2 + y ^ 2 = 4 * (p.1 ^ 2 + p.2 ^ 2) := by
          simp only [x, y, hs]; linear_combination 4 * p.2 ^ 2 * hsy_sq
        rw [this, hsqrt4 _ (by positivity)]
      have hr2e : r2 x y = 2 * Real.sqrt ((p.1 - 1) ^ 2 + p.2 ^ 2) := by
        unfold r2
        have : (x - 1) ^ 2 + y ^ 2 = 4 * ((p.1 - 1) ^ 2 + p.2 ^ 2) := by
          simp only [x, y, hs]; linear_combination 4 * p.2 ^ 2 * hsy_sq
        rw [this, hsqrt4 _ (by positivity)]
      unfold Fx; rw [hr1e, hr2e, h0]
      have hx1 : x + 1 = 2 * p.1 := by simp only [x, hs]; ring
      have hx2 : x - 1 = 2 * (p.1 - 1) := by simp only [x, hs]; ring
      have hx3 : x - u₀ = 2 * (p.1 - u) := by simp only [x, u₀, hs]; ring
      rw [hx1, hx2, hx3]; linear_combination (1 / 4 : ℝ) * hsum_x
    · have hs' : sx = -1 := by
        by_cases h : 0 ≤ 2 * u - 1
        · exact absurd (if_pos h) hs
        · exact if_neg h
      have hr1e : r1 x y = 2 * Real.sqrt ((p.1 - 1) ^ 2 + p.2 ^ 2) := by
        unfold r1
        have : (x + 1) ^ 2 + y ^ 2 = 4 * ((p.1 - 1) ^ 2 + p.2 ^ 2) := by
          simp only [x, y, hs']; linear_combination 4 * p.2 ^ 2 * hsy_sq
        rw [this, hsqrt4 _ (by positivity)]
      have hr2e : r2 x y = 2 * Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
        unfold r2
        have : (x - 1) ^ 2 + y ^ 2 = 4 * (p.1 ^ 2 + p.2 ^ 2) := by
          simp only [x, y, hs']; linear_combination 4 * p.2 ^ 2 * hsy_sq
        rw [this, hsqrt4 _ (by positivity)]
      unfold Fx; rw [hr1e, hr2e, h0]
      have hx1 : x + 1 = -2 * (p.1 - 1) := by simp only [x, hs']; ring
      have hx2 : x - 1 = -2 * p.1 := by simp only [x, hs']; ring
      have hx3 : x - u₀ = -2 * (p.1 - u) := by simp only [x, u₀, hs']; ring
      rw [hx1, hx2, hx3]; linear_combination (-1 / 4 : ℝ) * hsum_x
  have hFy_rel : Fy x y + (y - w₀) / Real.sqrt ((x - u₀) ^ 2 + (y - w₀) ^ 2) ^ 3 = 0 := by
    rw [Fy_eq]
    by_cases hs : sx = 1
    · have hr1e : r1 x y = 2 * Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
        unfold r1
        have : (x + 1) ^ 2 + y ^ 2 = 4 * (p.1 ^ 2 + p.2 ^ 2) := by
          simp only [x, y, hs]; linear_combination 4 * p.2 ^ 2 * hsy_sq
        rw [this, hsqrt4 _ (by positivity)]
      have hr2e : r2 x y = 2 * Real.sqrt ((p.1 - 1) ^ 2 + p.2 ^ 2) := by
        unfold r2
        have : (x - 1) ^ 2 + y ^ 2 = 4 * ((p.1 - 1) ^ 2 + p.2 ^ 2) := by
          simp only [x, y, hs]; linear_combination 4 * p.2 ^ 2 * hsy_sq
        rw [this, hsqrt4 _ (by positivity)]
      rw [hr1e, hr2e, h0]
      have hy3 : y - w₀ = 2 * sy * (p.2 - w) := by simp only [y, w₀]; ring
      rw [hy3]; simp only [y]; linear_combination (sy / 4 : ℝ) * hsum_y
    · have hs' : sx = -1 := by
        by_cases h : 0 ≤ 2 * u - 1
        · exact absurd (if_pos h) hs
        · exact if_neg h
      have hr1e : r1 x y = 2 * Real.sqrt ((p.1 - 1) ^ 2 + p.2 ^ 2) := by
        unfold r1
        have : (x + 1) ^ 2 + y ^ 2 = 4 * ((p.1 - 1) ^ 2 + p.2 ^ 2) := by
          simp only [x, y, hs']; linear_combination 4 * p.2 ^ 2 * hsy_sq
        rw [this, hsqrt4 _ (by positivity)]
      have hr2e : r2 x y = 2 * Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
        unfold r2
        have : (x - 1) ^ 2 + y ^ 2 = 4 * (p.1 ^ 2 + p.2 ^ 2) := by
          simp only [x, y, hs']; linear_combination 4 * p.2 ^ 2 * hsy_sq
        rw [this, hsqrt4 _ (by positivity)]
      rw [hr1e, hr2e, h0]
      have hy3 : y - w₀ = 2 * sy * (p.2 - w) := by simp only [y, w₀]; ring
      rw [hy3]; simp only [y]; linear_combination (sy / 4 : ℝ) * hsum_y
  have hy_pos : 0 < y := by
    by_contra hyle
    push Not at hyle
    have h1 : y / (r1 x y) ^ 3 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hyle (by unfold r1; positivity)
    have h2 : y / (r2 x y) ^ 3 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hyle (by unfold r2; positivity)
    have h3 : (y - w₀) / Real.sqrt ((x - u₀) ^ 2 + (y - w₀) ^ 2) ^ 3 < 0 :=
      div_neg_of_neg_of_pos (by linarith) (pow_pos hr3_pos 3)
    rw [Fy_eq] at hFy_rel
    linarith
  set R3 := Real.sqrt ((x - u₀) ^ 2 + (y - w₀) ^ 2)
  have hFx_eq : Fx x y = (u₀ - x) / R3 ^ 3 := by
    rw [show u₀ - x = -(x - u₀) by ring, neg_div]; linarith
  have hFy_eq : Fy x y = (w₀ - y) / R3 ^ 3 := by
    rw [show w₀ - y = -(y - w₀) by ring, neg_div]; linarith
  have hR3sq : R3 ^ 2 = (u₀ - x) ^ 2 + (w₀ - y) ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ (x - u₀) ^ 2 + (y - w₀) ^ 2 by positivity)
    linarith
  have hR3ne : R3 ≠ 0 := hr3_pos.ne'
  have hFsq_eq : Fsq x y = 1 / R3 ^ 4 := by
    unfold Fsq; rw [hFx_eq, hFy_eq]; field_simp; linarith [hR3sq]
  have hFn_eq : Fn x y = 1 / R3 ^ 2 := by
    unfold Fn; rw [hFsq_eq, show (1 : ℝ) / R3 ^ 4 = (1 / R3 ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have hFq_eq : Fq x y = 1 / R3 := by
    unfold Fq; rw [hFn_eq, show (1 : ℝ) / R3 ^ 2 = (1 / R3) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  refine ⟨hy_pos, ?_, ?_⟩
  · unfold phiU; rw [hFx_eq, hFq_eq]; field_simp; ring
  · unfold phiV; rw [hFy_eq, hFq_eq]; field_simp; ring

/- Section 2: 2D `HasFDerivAt` combinators and Apollonian `(u, c)` Jacobian identities -/

noncomputable def lin2 (a b : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ

lemma hasFDerivAt_fst_lin2 (p : ℝ × ℝ) : HasFDerivAt (fun q : ℝ × ℝ => q.1) (lin2 1 0) p :=
  (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p)).congr_fderiv (by
    ext <;> simp [lin2])

lemma hasFDerivAt_snd_lin2 (p : ℝ × ℝ) : HasFDerivAt (fun q : ℝ × ℝ => q.2) (lin2 0 1) p :=
  (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p)).congr_fderiv (by
    ext <;> simp [lin2])

lemma hasFDerivAt_const_lin2 (c : ℝ) (p : ℝ × ℝ) : HasFDerivAt (fun _ : ℝ × ℝ => c) (lin2 0 0) p :=
  (hasFDerivAt_const c p).congr_fderiv (by ext <;> simp [lin2])

lemma hasFDerivAt_add_lin2 {f g : ℝ × ℝ → ℝ} {fx fy gx gy : ℝ} {p : ℝ × ℝ}
    (hf : HasFDerivAt f (lin2 fx fy) p) (hg : HasFDerivAt g (lin2 gx gy) p) :
    HasFDerivAt (fun q => f q + g q) (lin2 (fx + gx) (fy + gy)) p :=
  (hf.add hg).congr_fderiv (by ext <;> simp [lin2])

lemma hasFDerivAt_sub_lin2 {f g : ℝ × ℝ → ℝ} {fx fy gx gy : ℝ} {p : ℝ × ℝ}
    (hf : HasFDerivAt f (lin2 fx fy) p) (hg : HasFDerivAt g (lin2 gx gy) p) :
    HasFDerivAt (fun q => f q - g q) (lin2 (fx - gx) (fy - gy)) p :=
  (hf.sub hg).congr_fderiv (by ext <;> simp [lin2])

lemma hasFDerivAt_mul_lin2 {f g : ℝ × ℝ → ℝ} {fx fy gx gy : ℝ} {p : ℝ × ℝ}
    (hf : HasFDerivAt f (lin2 fx fy) p) (hg : HasFDerivAt g (lin2 gx gy) p) :
    HasFDerivAt (fun q => f q * g q) (lin2 (fx * g p + f p * gx) (fy * g p + f p * gy)) p :=
  (hf.mul hg).congr_fderiv (by ext <;> simp [lin2] <;> ring)

lemma hasFDerivAt_div_lin2 {f g : ℝ × ℝ → ℝ} {fx fy gx gy : ℝ} {p : ℝ × ℝ}
    (hf : HasFDerivAt f (lin2 fx fy) p) (hg : HasFDerivAt g (lin2 gx gy) p) (hg0 : g p ≠ 0) :
    HasFDerivAt (fun q => f q / g q)
      (lin2 ((fx * g p - f p * gx) / (g p) ^ 2) ((fy * g p - f p * gy) / (g p) ^ 2)) p := by
  have hfun : (fun q => f q / g q) = fun q => f q * (g q)⁻¹ := by ext q; exact div_eq_mul_inv _ _
  rw [hfun]
  exact (hf.mul ((hasDerivAt_inv hg0).comp_hasFDerivAt p hg)).congr_fderiv (by
    ext <;> simp [lin2] <;> field_simp [hg0] <;> ring)

lemma hasFDerivAt_pow_lin2 {f : ℝ × ℝ → ℝ} {fx fy : ℝ} {p : ℝ × ℝ} (n : ℕ)
    (hf : HasFDerivAt f (lin2 fx fy) p) :
    HasFDerivAt (fun q => (f q) ^ n) (lin2 (n * (f p) ^ (n - 1) * fx) (n * (f p) ^ (n - 1) * fy)) p :=
  ((hasDerivAt_pow n (f p)).comp_hasFDerivAt p hf).congr_fderiv (by
    ext <;> simp [lin2])

lemma hasFDerivAt_sqrt_lin2 {f : ℝ × ℝ → ℝ} {fx fy : ℝ} {p : ℝ × ℝ}
    (hf : HasFDerivAt f (lin2 fx fy) p) (hf0 : f p ≠ 0) :
    HasFDerivAt (fun q => Real.sqrt (f q))
      (lin2 (fx / (2 * Real.sqrt (f p))) (fy / (2 * Real.sqrt (f p)))) p :=
  (hf.sqrt hf0).congr_fderiv (by ext <;> simp [lin2] <;> ring)

lemma hasDerivAt_x_of_lin2 {f : ℝ × ℝ → ℝ} {fx fy x y : ℝ}
    (hf : HasFDerivAt f (lin2 fx fy) (x, y)) :
    HasDerivAt (fun t => f (t, y)) fx x := by
  have h1 : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  exact (hf.comp_hasDerivAt x h1).congr_deriv (by simp [lin2])

lemma hasDerivAt_y_of_lin2 {f : ℝ × ℝ → ℝ} {fx fy x y : ℝ}
    (hf : HasFDerivAt f (lin2 fx fy) (x, y)) :
    HasDerivAt (fun t => f (x, t)) fy y := by
  have h1 : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  exact (hf.comp_hasDerivAt y h1).congr_deriv (by simp [lin2])

lemma hasDerivAt_comp_lin2 {f : ℝ × ℝ → ℝ} {fx fy : ℝ} {g h : ℝ → ℝ} {g' h' t : ℝ}
    (hf : HasFDerivAt f (lin2 fx fy) (g t, h t))
    (hg : HasDerivAt g g' t) (hh : HasDerivAt h h' t) :
    HasDerivAt (fun s => f (g s, h s)) (fx * g' + fy * h') t :=
  (hf.comp_hasDerivAt t (hg.prodMk hh)).congr_deriv (by simp [lin2])

noncomputable def Fxx (x y : ℝ) : ℝ :=
  ((r1 x y) ^ 2 - 3 * (x + 1) ^ 2) / (r1 x y) ^ 5 +
  ((r2 x y) ^ 2 - 3 * (x - 1) ^ 2) / (r2 x y) ^ 5

noncomputable def Fxy0 (x y : ℝ) : ℝ :=
  (-3 * (x + 1)) / (r1 x y) ^ 5 + (-3 * (x - 1)) / (r2 x y) ^ 5

noncomputable def Fxy (x y : ℝ) : ℝ := y * Fxy0 x y

noncomputable def Fyy (x y : ℝ) : ℝ :=
  ((r1 x y) ^ 2 - 3 * y ^ 2) / (r1 x y) ^ 5 +
  ((r2 x y) ^ 2 - 3 * y ^ 2) / (r2 x y) ^ 5

noncomputable def uX_xy (x y : ℝ) : ℝ :=
  1 + (Fxx x y * Fsq x y - (3 / 2 : ℝ) * Fx x y * (Fx x y * Fxx x y + Fy x y * Fxy x y)) / (Fq x y) ^ 7

noncomputable def uY_xy (x y : ℝ) : ℝ :=
  (Fxy x y * Fsq x y - (3 / 2 : ℝ) * Fx x y * (Fx x y * Fxy x y + Fy x y * Fyy x y)) / (Fq x y) ^ 7

noncomputable def vX_xy (x y : ℝ) : ℝ :=
  (Fxy x y * Fsq x y - (3 / 2 : ℝ) * Fy x y * (Fx x y * Fxx x y + Fy x y * Fxy x y)) / (Fq x y) ^ 7

noncomputable def vY_xy (x y : ℝ) : ℝ :=
  1 + (Fyy x y * Fsq x y - (3 / 2 : ℝ) * Fy x y * (Fx x y * Fxy x y + Fy x y * Fyy x y)) / (Fq x y) ^ 7

lemma hasFDerivAt_r1 (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasFDerivAt (fun p : ℝ × ℝ => r1 p.1 p.2) (lin2 ((x + 1) / r1 x y) (y / r1 x y)) (x, y) := by
  have h1 := hasFDerivAt_add_lin2 (hasFDerivAt_fst_lin2 (x, y)) (hasFDerivAt_const_lin2 1 (x, y))
  have h2 := hasFDerivAt_pow_lin2 2 h1
  have h3 := hasFDerivAt_pow_lin2 2 (hasFDerivAt_snd_lin2 (x, y))
  have h4 := hasFDerivAt_add_lin2 h2 h3
  have h5 := hasFDerivAt_sqrt_lin2 h4 (by positivity)
  exact h5.congr_fderiv (by ext <;> simp [lin2, r1] <;> ring)

lemma hasFDerivAt_r2 (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasFDerivAt (fun p : ℝ × ℝ => r2 p.1 p.2) (lin2 ((x - 1) / r2 x y) (y / r2 x y)) (x, y) := by
  have h1 := hasFDerivAt_sub_lin2 (hasFDerivAt_fst_lin2 (x, y)) (hasFDerivAt_const_lin2 1 (x, y))
  have h2 := hasFDerivAt_pow_lin2 2 h1
  have h3 := hasFDerivAt_pow_lin2 2 (hasFDerivAt_snd_lin2 (x, y))
  have h4 := hasFDerivAt_add_lin2 h2 h3
  have h5 := hasFDerivAt_sqrt_lin2 h4 (by positivity)
  exact h5.congr_fderiv (by ext <;> simp [lin2, r2] <;> ring)

lemma hasFDerivAt_Fx (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasFDerivAt (fun p : ℝ × ℝ => Fx p.1 p.2) (lin2 (Fxx x y) (Fxy x y)) (x, y) := by
  have hr1 := r1_pos x hy; have hr2 := r2_pos x hy
  have h1 := hasFDerivAt_div_lin2
    (hasFDerivAt_add_lin2 (hasFDerivAt_fst_lin2 (x, y)) (hasFDerivAt_const_lin2 1 (x, y)))
    (hasFDerivAt_pow_lin2 3 (hasFDerivAt_r1 x hy)) (pow_ne_zero 3 hr1.ne')
  have h2 := hasFDerivAt_div_lin2
    (hasFDerivAt_sub_lin2 (hasFDerivAt_fst_lin2 (x, y)) (hasFDerivAt_const_lin2 1 (x, y)))
    (hasFDerivAt_pow_lin2 3 (hasFDerivAt_r2 x hy)) (pow_ne_zero 3 hr2.ne')
  exact (hasFDerivAt_add_lin2 h1 h2).congr_fderiv (by
    have hr1ne := hr1.ne'; have hr2ne := hr2.ne'
    ext <;> simp [lin2, Fxx, Fxy, Fxy0] <;> field_simp [hr1ne, hr2ne])

lemma hasFDerivAt_Fy (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasFDerivAt (fun p : ℝ × ℝ => Fy p.1 p.2) (lin2 (Fxy x y) (Fyy x y)) (x, y) := by
  have hr1 := r1_pos x hy; have hr2 := r2_pos x hy
  have h1 := hasFDerivAt_div_lin2 (hasFDerivAt_snd_lin2 (x, y))
    (hasFDerivAt_pow_lin2 3 (hasFDerivAt_r1 x hy)) (pow_ne_zero 3 hr1.ne')
  have h2 := hasFDerivAt_div_lin2 (hasFDerivAt_snd_lin2 (x, y))
    (hasFDerivAt_pow_lin2 3 (hasFDerivAt_r2 x hy)) (pow_ne_zero 3 hr2.ne')
  have hsum : (fun p : ℝ × ℝ => Fy p.1 p.2) =
      fun p : ℝ × ℝ => p.2 / (r1 p.1 p.2) ^ 3 + p.2 / (r2 p.1 p.2) ^ 3 := by
    ext p; exact Fy_eq p.1 p.2
  rw [hsum]
  exact (hasFDerivAt_add_lin2 h1 h2).congr_fderiv (by
    have hr1ne := hr1.ne'; have hr2ne := hr2.ne'
    ext <;> simp [lin2, Fxy, Fxy0, Fyy] <;> field_simp [hr1ne, hr2ne])

lemma hasFDerivAt_Fq3 (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasFDerivAt (fun p : ℝ × ℝ => (Fq p.1 p.2) ^ 3)
      (lin2 ((3 / 2 : ℝ) * (Fx x y * Fxx x y + Fy x y * Fxy x y) / Fq x y)
            ((3 / 2 : ℝ) * (Fx x y * Fxy x y + Fy x y * Fyy x y) / Fq x y)) (x, y) := by
  have hFx := hasFDerivAt_Fx x hy
  have hFy := hasFDerivAt_Fy x hy
  have hFsq := hasFDerivAt_add_lin2 (hasFDerivAt_pow_lin2 2 hFx) (hasFDerivAt_pow_lin2 2 hFy)
  have hFn := hasFDerivAt_sqrt_lin2 hFsq (Fsq_pos x hy).ne'
  have hFq := hasFDerivAt_sqrt_lin2 hFn (Fn_pos x hy).ne'
  have hFq3 := hasFDerivAt_pow_lin2 3 hFq
  exact hFq3.congr_fderiv (by
    have hqne := (Fq_pos x hy).ne'
    have hq2 : Real.sqrt ((Fx x y) ^ 2 + (Fy x y) ^ 2) = (Fq x y) ^ 2 := (Fq_sq x y).symm
    have hfq_def : Real.sqrt (Real.sqrt ((Fx x y) ^ 2 + (Fy x y) ^ 2)) = Fq x y := rfl
    ext <;> simp [lin2] <;> rw [hfq_def, hq2] <;> field_simp [hqne])

lemma hasFDerivAt_phiU (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasFDerivAt (fun p : ℝ × ℝ => phiU p.1 p.2) (lin2 (uX_xy x y) (uY_xy x y)) (x, y) := by
  have hq := Fq_pos x hy
  have hdiv := hasFDerivAt_div_lin2 (hasFDerivAt_Fx x hy) (hasFDerivAt_Fq3 x hy) (pow_ne_zero 3 hq.ne')
  exact (hasFDerivAt_add_lin2 (hasFDerivAt_fst_lin2 (x, y)) hdiv).congr_fderiv (by
    have hqne := hq.ne'
    have hq4 : (Fq x y) ^ 4 = Fsq x y := Fq_pow4 x y
    ext
    · simp [lin2, uX_xy]; field_simp [hqne]; rw [hq4]; ring
    · simp [lin2, uY_xy]; field_simp [hqne]; rw [hq4]; ring)

lemma hasFDerivAt_phiV (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasFDerivAt (fun p : ℝ × ℝ => phiV p.1 p.2) (lin2 (vX_xy x y) (vY_xy x y)) (x, y) := by
  have hq := Fq_pos x hy
  have hdiv := hasFDerivAt_div_lin2 (hasFDerivAt_Fy x hy) (hasFDerivAt_Fq3 x hy) (pow_ne_zero 3 hq.ne')
  exact (hasFDerivAt_add_lin2 (hasFDerivAt_snd_lin2 (x, y)) hdiv).congr_fderiv (by
    have hqne := hq.ne'
    have hq4 : (Fq x y) ^ 4 = Fsq x y := Fq_pow4 x y
    ext
    · simp [lin2, vX_xy]; field_simp [hqne]; rw [hq4]; ring
    · simp [lin2, vY_xy]; field_simp [hqne]; rw [hq4]; ring)

/- Apollonian `(u, c)` definitions and division-free `(A, B)` algebraic bridges -/

noncomputable def uc_u (x y : ℝ) : ℝ :=
  ((r1 x y) ^ 2 + (r2 x y) ^ 2) / (r1 x y * r2 x y) - 2

noncomputable def uc_c (x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2 - 1) / (r1 x y * r2 x y)

noncomputable def uc_w (u c : ℝ) : ℝ := 2 + 2 * c + 4 * u + u ^ 2
noncomputable def uc_t (u c : ℝ) : ℝ := Real.sqrt (Real.sqrt (uc_w u c))

def Q11_m (u c : ℝ) : ℝ :=
  (-4 + 19 * u + 32 * u ^ 2 + 14 * u ^ 3 + 2 * u ^ 4) +
  (12 - 3 * u - 13 * u ^ 2 - 4 * u ^ 3) * c +
  (4 + u) * c ^ 2 +
  (-12 - 9 * u - 3 * u ^ 2) * c ^ 3

def Q22_m (u c : ℝ) : ℝ :=
  (2 + 28 * u + 32 * u ^ 2 + 14 * u ^ 3 + 2 * u ^ 4) +
  (6 - 21 * u - 19 * u ^ 2 - 4 * u ^ 3) * c +
  (-2 - 8 * u) * c ^ 2 +
  (-6 + 9 * u + 3 * u ^ 2) * c ^ 3

def R12_m (u c : ℝ) : ℝ :=
  (2 + u) * u + (1 - c) * ((1 + c) * ((2 + u) ^ 2 + (2 + u) - 4) + (3 * (2 + u) + 2))

def R21_m (u c : ℝ) : ℝ :=
  (1 + c ^ 2) * ((2 + u) ^ 2 + (2 + u) + 2) - 2 * c * (3 * (2 + u) + 2)

def T0_m (u c : ℝ) : ℝ :=
  (9 * c ^ 2 + 8 * c - 1) + (24 + 8 * c) * u + 20 * u ^ 2 + 4 * u ^ 3

def D0_m (u c : ℝ) : ℝ :=
  (9 * c ^ 2 - 1) + 18 * u + 12 * u ^ 2 + 2 * u ^ 3

noncomputable def F_det (u c : ℝ) : ℝ :=
  2 * uc_w u c * (uc_t u c) ^ 3 + Real.sqrt (4 + u) * T0_m u c + uc_t u c * D0_m u c

noncomputable def G_uc (u c : ℝ) : ℝ :=
  (2 * (1 - c * (3 + u)) / (uc_t u c) ^ 3 - Real.sqrt (4 + u)) / (2 + u - 2 * c)

noncomputable def uX_uc (u c : ℝ) : ℝ :=
  1 + Real.sqrt (4 + u) * Q11_m u c / (2 * (2 + u - 2 * c) * uc_w u c * (uc_t u c) ^ 3)

noncomputable def vY_uc (u c : ℝ) : ℝ :=
  1 + Real.sqrt (4 + u) * Q22_m u c / (2 * (2 + u - 2 * c) * uc_w u c * (uc_t u c) ^ 3)

noncomputable def det_uc (u c : ℝ) : ℝ :=
  F_det u c / (2 * uc_w u c * (uc_t u c) ^ 3)

lemma uc_u_neg_x (x y : ℝ) : uc_u (-x) y = uc_u x y := by
  unfold uc_u; rw [r1_neg_x, r2_neg_x]; ring

lemma uc_c_neg_x (x y : ℝ) : uc_c (-x) y = uc_c x y := by
  unfold uc_c; rw [r1_neg_x, r2_neg_x]; ring

lemma uc_u_nonneg (x : ℝ) {y : ℝ} (hy : 0 < y) : 0 ≤ uc_u x y := by
  have h1 := r1_pos x hy; have h2 := r2_pos x hy
  unfold uc_u; rw [sub_nonneg, le_div_iff₀ (mul_pos h1 h2)]
  nlinarith [sq_nonneg (r1 x y - r2 x y)]

lemma uc_u_eq_zero_iff (x : ℝ) {y : ℝ} (hy : 0 < y) : uc_u x y = 0 ↔ x = 0 := by
  have h1 := r1_pos x hy; have h2 := r2_pos x hy
  unfold uc_u; rw [sub_eq_zero, div_eq_iff (mul_pos h1 h2).ne']
  constructor
  · intro h
    have heq : r1 x y = r2 x y := sub_eq_zero.mp (sq_eq_zero_iff.mp (by linarith : (r1 x y - r2 x y) ^ 2 = 0))
    have hsq : (r1 x y) ^ 2 = (r2 x y) ^ 2 := by rw [heq]
    rw [r1_sq, r2_sq] at hsq; linarith
  · intro hx
    have hsq : (r1 x y) ^ 2 = (r2 x y) ^ 2 := by rw [r1_sq, r2_sq, hx]; ring
    have heq : r1 x y = r2 x y := by nlinarith
    rw [heq]; ring

lemma uc_c_bounds (x : ℝ) {y : ℝ} (hy : 0 < y) : -1 < uc_c x y ∧ uc_c x y < 1 := by
  have hprod : 0 < r1 x y * r2 x y := mul_pos (r1_pos x hy) (r2_pos x hy)
  have hsq : (r1 x y * r2 x y) ^ 2 = (x ^ 2 + y ^ 2 - 1) ^ 2 + 4 * y ^ 2 := by
    calc (r1 x y * r2 x y) ^ 2 = (r1 x y) ^ 2 * (r2 x y) ^ 2 := by ring
      _ = ((x + 1) ^ 2 + y ^ 2) * ((x - 1) ^ 2 + y ^ 2) := by rw [r1_sq, r2_sq]
      _ = (x ^ 2 + y ^ 2 - 1) ^ 2 + 4 * y ^ 2 := by ring
  unfold uc_c
  constructor
  · rw [lt_div_iff₀ hprod]; nlinarith
  · rw [div_lt_iff₀ hprod]; nlinarith

lemma uc_one_sub_c_sq (x : ℝ) {y : ℝ} (hy : 0 < y) :
    1 - (uc_c x y) ^ 2 = (2 * y / (r1 x y * r2 x y)) ^ 2 := by
  have h1 := (r1_pos x hy).ne'; have h2 := (r2_pos x hy).ne'
  have hsq : (r1 x y * r2 x y) ^ 2 = (x ^ 2 + y ^ 2 - 1) ^ 2 + 4 * y ^ 2 := by
    calc (r1 x y * r2 x y) ^ 2 = (r1 x y) ^ 2 * (r2 x y) ^ 2 := by ring
      _ = ((x + 1) ^ 2 + y ^ 2) * ((x - 1) ^ 2 + y ^ 2) := by rw [r1_sq, r2_sq]
      _ = (x ^ 2 + y ^ 2 - 1) ^ 2 + 4 * y ^ 2 := by ring
  unfold uc_c
  field_simp [h1, h2]
  linear_combination hsq

lemma uc_Lm_eq (x : ℝ) {y : ℝ} (hy : 0 < y) :
    2 + uc_u x y - 2 * uc_c x y = 4 / (r1 x y * r2 x y) := by
  have h1 := (r1_pos x hy).ne'; have h2 := (r2_pos x hy).ne'
  unfold uc_u uc_c
  field_simp [h1, h2]
  linarith [r1_sq x y, r2_sq x y]

lemma uc_w_pos {u c : ℝ} (hu : 0 ≤ u) (hc : -1 < c) : 0 < uc_w u c := by
  unfold uc_w; nlinarith

lemma uc_t_pos {u c : ℝ} (hu : 0 ≤ u) (hc : -1 < c) : 0 < uc_t u c :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (uc_w_pos hu hc))

lemma uc_t_pow4 {u c : ℝ} (hu : 0 ≤ u) (hc : -1 < c) : (uc_t u c) ^ 4 = uc_w u c := by
  unfold uc_t
  calc (Real.sqrt (Real.sqrt (uc_w u c))) ^ 4
      = ((Real.sqrt (Real.sqrt (uc_w u c))) ^ 2) ^ 2 := by ring
    _ = (Real.sqrt (uc_w u c)) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
    _ = uc_w u c := Real.sq_sqrt (uc_w_pos hu hc).le

lemma uc_x_eq (x y : ℝ) : x = ((r1 x y) ^ 2 - (r2 x y) ^ 2) / 4 := by
  linarith [r1_sq x y, r2_sq x y]

lemma uc_y2_eq (x y : ℝ) :
    y ^ 2 = (r1 x y) ^ 2 - (((r1 x y) ^ 2 - (r2 x y) ^ 2) / 4 + 1) ^ 2 := by
  have hx := uc_x_eq x y; have h1 := r1_sq x y; rw [← hx]; linarith

lemma uc_c_eq_r (x : ℝ) {y : ℝ} (hy : 0 < y) :
    uc_c x y = ((r1 x y) ^ 2 + (r2 x y) ^ 2 - 4) / (2 * r1 x y * r2 x y) := by
  have h1 := r1_pos x hy; have h2 := r2_pos x hy
  unfold uc_c
  rw [div_eq_div_iff (mul_pos h1 h2).ne' (by positivity)]
  have hlin : 2 * (x ^ 2 + y ^ 2 - 1) = (r1 x y) ^ 2 + (r2 x y) ^ 2 - 4 := by
    linarith [r1_sq x y, r2_sq x y]
  linear_combination (r1 x y * r2 x y) * hlin

lemma uc_sqrt_four_add_u (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Real.sqrt (4 + uc_u x y) = (r1 x y + r2 x y) / Real.sqrt (r1 x y * r2 x y) := by
  have h1 := r1_pos x hy; have h2 := r2_pos x hy
  have heq : 4 + uc_u x y = (r1 x y + r2 x y) ^ 2 / (r1 x y * r2 x y) := by
    unfold uc_u; field_simp [h1.ne', h2.ne']; ring
  rw [heq, Real.sqrt_div (by positivity), Real.sqrt_sq (by linarith)]

lemma uc_sqrt_u_of_nonpos {x y : ℝ} (hy : 0 < y) (hx : x ≤ 0) :
    Real.sqrt (uc_u x y) = (r2 x y - r1 x y) / Real.sqrt (r1 x y * r2 x y) := by
  have h1 := r1_pos x hy; have h2 := r2_pos x hy
  have hle : r1 x y ≤ r2 x y := by
    have : (r1 x y) ^ 2 ≤ (r2 x y) ^ 2 := by rw [r1_sq, r2_sq]; nlinarith
    nlinarith
  have heq : uc_u x y = (r2 x y - r1 x y) ^ 2 / (r1 x y * r2 x y) := by
    unfold uc_u; field_simp [h1.ne', h2.ne']; ring
  rw [heq, Real.sqrt_div (by positivity), Real.sqrt_sq (by linarith)]

lemma uc_w_eq_r (x : ℝ) {y : ℝ} (hy : 0 < y) :
    uc_w (uc_u x y) (uc_c x y) =
      ((r1 x y) ^ 4 + (r2 x y) ^ 4 + r1 x y * r2 x y * ((r1 x y) ^ 2 + (r2 x y) ^ 2 - 4)) /
      ((r1 x y) ^ 2 * (r2 x y) ^ 2) := by
  have h1 := (r1_pos x hy).ne'; have h2 := (r2_pos x hy).ne'
  unfold uc_w; rw [uc_c_eq_r x hy]; unfold uc_u
  field_simp [h1, h2]; ring

lemma uc_Fsq_eq (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Fsq x y = uc_w (uc_u x y) (uc_c x y) / (r1 x y * r2 x y) ^ 2 := by
  have h1 := (r1_pos x hy).ne'; have h2 := (r2_pos x hy).ne'
  have hx := uc_x_eq x y
  have hy2 := uc_y2_eq x y
  rw [uc_w_eq_r x hy]
  unfold Fsq Fx Fy Fy0
  rw [show (y * (1 / r1 x y ^ 3 + 1 / r2 x y ^ 3)) ^ 2 =
      y ^ 2 * (1 / r1 x y ^ 3 + 1 / r2 x y ^ 3) ^ 2 by ring]
  generalize r1 x y = A at h1 hx hy2 ⊢
  generalize r2 x y = B at h2 hx hy2 ⊢
  rw [hx, hy2]
  field_simp [h1, h2]; ring

lemma uc_Fq_eq (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Fq x y = uc_t (uc_u x y) (uc_c x y) / Real.sqrt (r1 x y * r2 x y) := by
  have hprod : 0 < r1 x y * r2 x y := mul_pos (r1_pos x hy) (r2_pos x hy)
  have hu := uc_u_nonneg x hy; have hc := (uc_c_bounds x hy).1
  have hFn : Fn x y = Real.sqrt (uc_w (uc_u x y) (uc_c x y)) / (r1 x y * r2 x y) := by
    unfold Fn; rw [uc_Fsq_eq x hy, Real.sqrt_div (uc_w_pos hu hc).le, Real.sqrt_sq hprod.le]
  unfold Fq uc_t; rw [hFn, Real.sqrt_div (Real.sqrt_nonneg _)]

lemma uc_Fq_pow7 (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (Fq x y) ^ 7 = uc_w (uc_u x y) (uc_c x y) * (uc_t (uc_u x y) (uc_c x y)) ^ 3 /
      ((r1 x y * r2 x y) ^ 3 * Real.sqrt (r1 x y * r2 x y)) := by
  have hprod : 0 < r1 x y * r2 x y := mul_pos (r1_pos x hy) (r2_pos x hy)
  have hs := Real.sqrt_pos.mpr hprod
  have hs2 : (Real.sqrt (r1 x y * r2 x y)) ^ 2 = r1 x y * r2 x y := Real.sq_sqrt hprod.le
  have ht4 : (uc_t (uc_u x y) (uc_c x y)) ^ 4 = uc_w (uc_u x y) (uc_c x y) :=
    uc_t_pow4 (uc_u_nonneg x hy) (uc_c_bounds x hy).1
  rw [uc_Fq_eq x hy, div_pow, div_eq_div_iff (pow_ne_zero 7 hs.ne') (by positivity)]
  calc (uc_t (uc_u x y) (uc_c x y)) ^ 7 * ((r1 x y * r2 x y) ^ 3 * Real.sqrt (r1 x y * r2 x y))
      = (uc_t (uc_u x y) (uc_c x y)) ^ 4 * (uc_t (uc_u x y) (uc_c x y)) ^ 3 *
          ((Real.sqrt (r1 x y * r2 x y)) ^ 2) ^ 3 * Real.sqrt (r1 x y * r2 x y) := by
            rw [hs2]; ring
    _ = uc_w (uc_u x y) (uc_c x y) * (uc_t (uc_u x y) (uc_c x y)) ^ 3 *
          (Real.sqrt (r1 x y * r2 x y)) ^ 7 := by rw [ht4]; ring

lemma phiU_eq_uc (x : ℝ) {y : ℝ} (hy : 0 < y) :
    phiU x y = (r2 x y - r1 x y) / Real.sqrt (r1 x y * r2 x y) * G_uc (uc_u x y) (uc_c x y) := by
  have h1 := r1_pos x hy; have h2 := r2_pos x hy
  have hprod : 0 < r1 x y * r2 x y := mul_pos h1 h2
  have hs := Real.sqrt_pos.mpr hprod
  have hs2 : (Real.sqrt (r1 x y * r2 x y)) ^ 2 = r1 x y * r2 x y := Real.sq_sqrt hprod.le
  have ht := uc_t_pos (uc_u_nonneg x hy) (uc_c_bounds x hy).1
  have hx := uc_x_eq x y
  unfold phiU G_uc Fx
  rw [uc_Fq_eq x hy, uc_Lm_eq x hy, uc_sqrt_four_add_u x hy, uc_c_eq_r x hy]
  unfold uc_u
  have h1ne := h1.ne'; have h2ne := h2.ne'; have hsne := hs.ne'; have htne := ht.ne'
  generalize uc_t (uc_u x y) (uc_c x y) = t at htne ⊢
  generalize Real.sqrt (r1 x y * r2 x y) = S at hs2 hsne ⊢
  generalize r1 x y = A at h1ne hx hs2 ⊢
  generalize r2 x y = B at h2ne hx hs2 ⊢
  rw [hx]
  have hS3 : S ^ 3 = A * B * S := by
    calc S ^ 3 = S ^ 2 * S := by ring
      _ = A * B * S := by rw [hs2]
  rw [div_pow, hS3]
  field_simp [h1ne, h2ne, htne, hsne]
  rw [hs2]
  ring

/- Pure 2-variable polynomial identities in `(A, B) = (r1, r2)` for `uX`, `vY`, `uY`, `vX` -/

private lemma poly_uX_AB (A B : ℝ) :
    let x := (A ^ 2 - B ^ 2) / 4
    let y2 := A ^ 2 - (x + 1) ^ 2
    let FxN := (x + 1) * B ^ 3 + (x - 1) * A ^ 3
    let Fy0N := B ^ 3 + A ^ 3
    let FxxN := (A ^ 2 - 3 * (x + 1) ^ 2) * B ^ 5 + (B ^ 2 - 3 * (x - 1) ^ 2) * A ^ 5
    let Fxy0N := -3 * (x + 1) * B ^ 5 - 3 * (x - 1) * A ^ 5
    let wN := A ^ 4 + B ^ 4 + A * B * (A ^ 2 + B ^ 2 - 4)
    let U := A ^ 2 + B ^ 2 - 2 * A * B
    let C := A ^ 2 + B ^ 2 - 4
    let P := A * B
    let Q11N :=
      8 * (-4 * P ^ 4 + 19 * U * P ^ 3 + 32 * U ^ 2 * P ^ 2 + 14 * U ^ 3 * P + 2 * U ^ 4) * P +
      4 * (12 * P ^ 3 - 3 * U * P ^ 2 - 13 * U ^ 2 * P - 4 * U ^ 3) * P * C +
      2 * (4 * P + U) * P ^ 2 * C ^ 2 +
      (-12 * P ^ 2 - 9 * U * P - 3 * U ^ 2) * C ^ 3
    64 * (FxxN * wN * P ^ 2 - (3 / 2 : ℝ) * FxN * (FxN * FxxN + y2 * Fy0N * Fxy0N)) =
    (A + B) * Q11N * P ^ 3 := by
  dsimp only; ring

private lemma poly_vY_AB (A B : ℝ) :
    let x := (A ^ 2 - B ^ 2) / 4
    let y2 := A ^ 2 - (x + 1) ^ 2
    let FxN := (x + 1) * B ^ 3 + (x - 1) * A ^ 3
    let Fy0N := B ^ 3 + A ^ 3
    let Fxy0N := -3 * (x + 1) * B ^ 5 - 3 * (x - 1) * A ^ 5
    let FyyN := (A ^ 2 - 3 * y2) * B ^ 5 + (B ^ 2 - 3 * y2) * A ^ 5
    let wN := A ^ 4 + B ^ 4 + A * B * (A ^ 2 + B ^ 2 - 4)
    let U := A ^ 2 + B ^ 2 - 2 * A * B
    let C := A ^ 2 + B ^ 2 - 4
    let P := A * B
    let Q22N :=
      8 * (2 * P ^ 4 + 28 * U * P ^ 3 + 32 * U ^ 2 * P ^ 2 + 14 * U ^ 3 * P + 2 * U ^ 4) * P +
      4 * (6 * P ^ 3 - 21 * U * P ^ 2 - 19 * U ^ 2 * P - 4 * U ^ 3) * P * C +
      2 * (-2 * P - 8 * U) * P ^ 2 * C ^ 2 +
      (-6 * P ^ 2 + 9 * U * P + 3 * U ^ 2) * C ^ 3
    64 * (FyyN * wN * P ^ 2 - (3 / 2 : ℝ) * y2 * Fy0N * (FxN * Fxy0N + Fy0N * FyyN)) =
    (A + B) * Q22N * P ^ 3 := by
  dsimp only; ring

private lemma poly_uY_AB (A B : ℝ) :
    let x := (A ^ 2 - B ^ 2) / 4
    let y2 := A ^ 2 - (x + 1) ^ 2
    let FxN := (x + 1) * B ^ 3 + (x - 1) * A ^ 3
    let Fy0N := B ^ 3 + A ^ 3
    let Fxy0N := -3 * (x + 1) * B ^ 5 - 3 * (x - 1) * A ^ 5
    let FyyN := (A ^ 2 - 3 * y2) * B ^ 5 + (B ^ 2 - 3 * y2) * A ^ 5
    let wN := A ^ 4 + B ^ 4 + A * B * (A ^ 2 + B ^ 2 - 4)
    let M := A ^ 2 + B ^ 2
    let U := A ^ 2 + B ^ 2 - 2 * A * B
    let C := A ^ 2 + B ^ 2 - 4
    let P := A * B
    let R12N :=
      4 * M * U * P ^ 2 +
      (2 * P - C) * ((2 * P + C) * (M ^ 2 + M * P - 4 * P ^ 2) + 2 * P * (3 * M + 2 * P) * P)
    16 * (Fxy0N * wN * P ^ 2 - (3 / 2 : ℝ) * FxN * (FxN * Fxy0N + Fy0N * FyyN)) =
    3 * (A - B) * R12N * P ^ 3 := by
  dsimp only; ring

private lemma poly_vX_AB (A B : ℝ) :
    let x := (A ^ 2 - B ^ 2) / 4
    let y2 := A ^ 2 - (x + 1) ^ 2
    let FxN := (x + 1) * B ^ 3 + (x - 1) * A ^ 3
    let Fy0N := B ^ 3 + A ^ 3
    let FxxN := (A ^ 2 - 3 * (x + 1) ^ 2) * B ^ 5 + (B ^ 2 - 3 * (x - 1) ^ 2) * A ^ 5
    let Fxy0N := -3 * (x + 1) * B ^ 5 - 3 * (x - 1) * A ^ 5
    let wN := A ^ 4 + B ^ 4 + A * B * (A ^ 2 + B ^ 2 - 4)
    let M := A ^ 2 + B ^ 2
    let C := A ^ 2 + B ^ 2 - 4
    let P := A * B
    let R21N :=
      (4 * P ^ 2 + C ^ 2) * (M ^ 2 + M * P + 2 * P ^ 2) - 4 * P ^ 2 * C * (3 * M + 2 * P)
    16 * (Fxy0N * wN * P ^ 2 - (3 / 2 : ℝ) * Fy0N * (FxN * FxxN + y2 * Fy0N * Fxy0N)) =
    -3 * (A - B) * R21N * P ^ 3 := by
  dsimp only; ring

lemma uX_xy_eq_uc (x : ℝ) {y : ℝ} (hy : 0 < y) :
    uX_xy x y = uX_uc (uc_u x y) (uc_c x y) := by
  have h1 := r1_pos x hy; have h2 := r2_pos x hy
  have hprod : 0 < r1 x y * r2 x y := mul_pos h1 h2
  have hs := Real.sqrt_pos.mpr hprod
  have hs2 : (Real.sqrt (r1 x y * r2 x y)) ^ 2 = r1 x y * r2 x y := Real.sq_sqrt hprod.le
  have hu := uc_u_nonneg x hy; have hc := (uc_c_bounds x hy).1
  have hw := uc_w_pos hu hc; have ht := uc_t_pos hu hc
  have hAne := h1.ne'; have hBne := h2.ne'; have hPne : r1 x y * r2 x y ≠ 0 := hprod.ne'
  have hsne := hs.ne'; have hwne := hw.ne'; have htne := ht.ne'
  have hx := uc_x_eq x y; have hy2 := uc_y2_eq x y
  unfold uX_xy uX_uc
  rw [uc_Fq_pow7 x hy, uc_Fsq_eq x hy, uc_Lm_eq x hy, uc_sqrt_four_add_u x hy]
  congr 1
  have hFx : Fx x y = (((r1 x y ^ 2 - r2 x y ^ 2) / 4 + 1) * r2 x y ^ 3 +
      ((r1 x y ^ 2 - r2 x y ^ 2) / 4 - 1) * r1 x y ^ 3) / (r1 x y * r2 x y) ^ 3 := by
    unfold Fx; generalize r1 x y = A at hAne hx ⊢; generalize r2 x y = B at hBne hx ⊢
    rw [hx]; field_simp [hAne, hBne]
  have hFy0 : Fy0 x y = (r2 x y ^ 3 + r1 x y ^ 3) / (r1 x y * r2 x y) ^ 3 := by
    unfold Fy0; field_simp [hAne, hBne]
  have hFxx : Fxx x y = ((r1 x y ^ 2 - 3 * ((r1 x y ^ 2 - r2 x y ^ 2) / 4 + 1) ^ 2) * r2 x y ^ 5 +
      (r2 x y ^ 2 - 3 * ((r1 x y ^ 2 - r2 x y ^ 2) / 4 - 1) ^ 2) * r1 x y ^ 5) / (r1 x y * r2 x y) ^ 5 := by
    unfold Fxx; generalize r1 x y = A at hAne hx ⊢; generalize r2 x y = B at hBne hx ⊢
    rw [hx]; field_simp [hAne, hBne]
  have hFxy0 : Fxy0 x y = (-3 * ((r1 x y ^ 2 - r2 x y ^ 2) / 4 + 1) * r2 x y ^ 5 -
      3 * ((r1 x y ^ 2 - r2 x y ^ 2) / 4 - 1) * r1 x y ^ 5) / (r1 x y * r2 x y) ^ 5 := by
    unfold Fxy0; generalize r1 x y = A at hAne hx ⊢; generalize r2 x y = B at hBne hx ⊢
    rw [hx]; field_simp [hAne, hBne]; ring
  have hw_eq : uc_w (uc_u x y) (uc_c x y) =
      (r1 x y ^ 4 + r2 x y ^ 4 + (r1 x y * r2 x y) * (r1 x y ^ 2 + r2 x y ^ 2 - 4)) / (r1 x y * r2 x y) ^ 2 := by
    rw [uc_w_eq_r x hy]; ring
  have hQ11 : Q11_m (uc_u x y) (uc_c x y) =
      (8 * (-4 * (r1 x y * r2 x y) ^ 4 + 19 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) * (r1 x y * r2 x y) ^ 3 +
          32 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) ^ 2 * (r1 x y * r2 x y) ^ 2 +
          14 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) ^ 3 * (r1 x y * r2 x y) +
          2 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) ^ 4) * (r1 x y * r2 x y) +
        4 * (12 * (r1 x y * r2 x y) ^ 3 - 3 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) * (r1 x y * r2 x y) ^ 2 -
          13 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) ^ 2 * (r1 x y * r2 x y) -
          4 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) ^ 3) * (r1 x y * r2 x y) * (r1 x y ^ 2 + r2 x y ^ 2 - 4) +
        2 * (4 * (r1 x y * r2 x y) + (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y))) *
          (r1 x y * r2 x y) ^ 2 * (r1 x y ^ 2 + r2 x y ^ 2 - 4) ^ 2 +
        (-12 * (r1 x y * r2 x y) ^ 2 - 9 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) * (r1 x y * r2 x y) -
          3 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) ^ 2) *
          (r1 x y ^ 2 + r2 x y ^ 2 - 4) ^ 3) / (8 * (r1 x y * r2 x y) ^ 5) := by
    unfold Q11_m; rw [uc_c_eq_r x hy]; unfold uc_u
    field_simp [hAne, hBne, hPne]; ring
  have hmain : (Fxx x y * (uc_w (uc_u x y) (uc_c x y) / (r1 x y * r2 x y) ^ 2) -
      3 / 2 * Fx x y * (Fx x y * Fxx x y + Fy x y * Fxy x y)) * (r1 x y * r2 x y) ^ 3 =
      (r1 x y + r2 x y) * Q11_m (uc_u x y) (uc_c x y) / 8 := by
    have hFxy_y : Fy x y * Fxy x y = y ^ 2 * (Fy0 x y * Fxy0 x y) := by unfold Fy Fxy; ring
    rw [hFxy_y, hy2, hFx, hFy0, hFxx, hFxy0, hw_eq, hQ11]
    have hpoly := poly_uX_AB (r1 x y) (r2 x y); dsimp only at hpoly
    field_simp [hPne]
    linear_combination hpoly
  calc (Fxx x y * (uc_w (uc_u x y) (uc_c x y) / (r1 x y * r2 x y) ^ 2) -
        3 / 2 * Fx x y * (Fx x y * Fxx x y + Fy x y * Fxy x y)) /
      (uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3 / ((r1 x y * r2 x y) ^ 3 * Real.sqrt (r1 x y * r2 x y)))
      = ((Fxx x y * (uc_w (uc_u x y) (uc_c x y) / (r1 x y * r2 x y) ^ 2) -
          3 / 2 * Fx x y * (Fx x y * Fxx x y + Fy x y * Fxy x y)) * (r1 x y * r2 x y) ^ 3) *
        (Real.sqrt (r1 x y * r2 x y) / (uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3)) := by
          field_simp [hPne, hsne, hwne, htne]
    _ = ((r1 x y + r2 x y) * Q11_m (uc_u x y) (uc_c x y) / 8) *
        (Real.sqrt (r1 x y * r2 x y) / (uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3)) := by
          rw [hmain]
    _ = (r1 x y + r2 x y) / Real.sqrt (r1 x y * r2 x y) * Q11_m (uc_u x y) (uc_c x y) /
        (2 * (4 / (r1 x y * r2 x y)) * uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3) := by
          field_simp [hPne, hsne, hwne, htne]
          rw [hs2]; ring

lemma vY_xy_eq_uc (x : ℝ) {y : ℝ} (hy : 0 < y) :
    vY_xy x y = vY_uc (uc_u x y) (uc_c x y) := by
  have h1 := r1_pos x hy; have h2 := r2_pos x hy
  have hprod : 0 < r1 x y * r2 x y := mul_pos h1 h2
  have hs := Real.sqrt_pos.mpr hprod
  have hs2 : (Real.sqrt (r1 x y * r2 x y)) ^ 2 = r1 x y * r2 x y := Real.sq_sqrt hprod.le
  have hu := uc_u_nonneg x hy; have hc := (uc_c_bounds x hy).1
  have hw := uc_w_pos hu hc; have ht := uc_t_pos hu hc
  have hAne := h1.ne'; have hBne := h2.ne'; have hPne : r1 x y * r2 x y ≠ 0 := hprod.ne'
  have hsne := hs.ne'; have hwne := hw.ne'; have htne := ht.ne'
  have hx := uc_x_eq x y; have hy2 := uc_y2_eq x y
  unfold vY_xy vY_uc
  rw [uc_Fq_pow7 x hy, uc_Fsq_eq x hy, uc_Lm_eq x hy, uc_sqrt_four_add_u x hy]
  congr 1
  have hFx : Fx x y = (((r1 x y ^ 2 - r2 x y ^ 2) / 4 + 1) * r2 x y ^ 3 +
      ((r1 x y ^ 2 - r2 x y ^ 2) / 4 - 1) * r1 x y ^ 3) / (r1 x y * r2 x y) ^ 3 := by
    unfold Fx; generalize r1 x y = A at hAne hx ⊢; generalize r2 x y = B at hBne hx ⊢
    rw [hx]; field_simp [hAne, hBne]
  have hFy0 : Fy0 x y = (r2 x y ^ 3 + r1 x y ^ 3) / (r1 x y * r2 x y) ^ 3 := by
    unfold Fy0; field_simp [hAne, hBne]
  have hFxy0 : Fxy0 x y = (-3 * ((r1 x y ^ 2 - r2 x y ^ 2) / 4 + 1) * r2 x y ^ 5 -
      3 * ((r1 x y ^ 2 - r2 x y ^ 2) / 4 - 1) * r1 x y ^ 5) / (r1 x y * r2 x y) ^ 5 := by
    unfold Fxy0; generalize r1 x y = A at hAne hx ⊢; generalize r2 x y = B at hBne hx ⊢
    rw [hx]; field_simp [hAne, hBne]; ring
  have hFyy : Fyy x y = ((r1 x y ^ 2 - 3 * y ^ 2) * r2 x y ^ 5 +
      (r2 x y ^ 2 - 3 * y ^ 2) * r1 x y ^ 5) / (r1 x y * r2 x y) ^ 5 := by
    unfold Fyy; field_simp [hAne, hBne]
  have hw_eq : uc_w (uc_u x y) (uc_c x y) =
      (r1 x y ^ 4 + r2 x y ^ 4 + (r1 x y * r2 x y) * (r1 x y ^ 2 + r2 x y ^ 2 - 4)) / (r1 x y * r2 x y) ^ 2 := by
    rw [uc_w_eq_r x hy]; ring
  have hQ22 : Q22_m (uc_u x y) (uc_c x y) =
      (8 * (2 * (r1 x y * r2 x y) ^ 4 + 28 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) * (r1 x y * r2 x y) ^ 3 +
          32 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) ^ 2 * (r1 x y * r2 x y) ^ 2 +
          14 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) ^ 3 * (r1 x y * r2 x y) +
          2 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) ^ 4) * (r1 x y * r2 x y) +
        4 * (6 * (r1 x y * r2 x y) ^ 3 - 21 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) * (r1 x y * r2 x y) ^ 2 -
          19 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) ^ 2 * (r1 x y * r2 x y) -
          4 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) ^ 3) * (r1 x y * r2 x y) * (r1 x y ^ 2 + r2 x y ^ 2 - 4) +
        2 * (-2 * (r1 x y * r2 x y) - 8 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y))) *
          (r1 x y * r2 x y) ^ 2 * (r1 x y ^ 2 + r2 x y ^ 2 - 4) ^ 2 +
        (-6 * (r1 x y * r2 x y) ^ 2 + 9 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) * (r1 x y * r2 x y) +
          3 * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) ^ 2) *
          (r1 x y ^ 2 + r2 x y ^ 2 - 4) ^ 3) / (8 * (r1 x y * r2 x y) ^ 5) := by
    unfold Q22_m; rw [uc_c_eq_r x hy]; unfold uc_u
    field_simp [hAne, hBne, hPne]; ring
  have hmain : (Fyy x y * (uc_w (uc_u x y) (uc_c x y) / (r1 x y * r2 x y) ^ 2) -
      3 / 2 * Fy x y * (Fx x y * Fxy x y + Fy x y * Fyy x y)) * (r1 x y * r2 x y) ^ 3 =
      (r1 x y + r2 x y) * Q22_m (uc_u x y) (uc_c x y) / 8 := by
    have hFy_term : 3 / 2 * Fy x y * (Fx x y * Fxy x y + Fy x y * Fyy x y) =
        3 / 2 * y ^ 2 * Fy0 x y * (Fx x y * Fxy0 x y + Fy0 x y * Fyy x y) := by unfold Fy Fxy; ring
    rw [hFy_term, hFx, hFy0, hFxy0, hFyy, hy2, hw_eq, hQ22]
    have hpoly := poly_vY_AB (r1 x y) (r2 x y); dsimp only at hpoly
    field_simp [hPne]
    linear_combination hpoly
  calc (Fyy x y * (uc_w (uc_u x y) (uc_c x y) / (r1 x y * r2 x y) ^ 2) -
        3 / 2 * Fy x y * (Fx x y * Fxy x y + Fy x y * Fyy x y)) /
      (uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3 / ((r1 x y * r2 x y) ^ 3 * Real.sqrt (r1 x y * r2 x y)))
      = ((Fyy x y * (uc_w (uc_u x y) (uc_c x y) / (r1 x y * r2 x y) ^ 2) -
          3 / 2 * Fy x y * (Fx x y * Fxy x y + Fy x y * Fyy x y)) * (r1 x y * r2 x y) ^ 3) *
        (Real.sqrt (r1 x y * r2 x y) / (uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3)) := by
          field_simp [hPne, hsne, hwne, htne]
    _ = ((r1 x y + r2 x y) * Q22_m (uc_u x y) (uc_c x y) / 8) *
        (Real.sqrt (r1 x y * r2 x y) / (uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3)) := by
          rw [hmain]
    _ = (r1 x y + r2 x y) / Real.sqrt (r1 x y * r2 x y) * Q22_m (uc_u x y) (uc_c x y) /
        (2 * (4 / (r1 x y * r2 x y)) * uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3) := by
          field_simp [hPne, hsne, hwne, htne]
          rw [hs2]; ring

lemma uY_xy_eq_uc (x : ℝ) {y : ℝ} (hy : 0 < y) :
    uY_xy x y = 3 * y * (r1 x y - r2 x y) * R12_m (uc_u x y) (uc_c x y) /
      (4 * Real.sqrt (r1 x y * r2 x y) * uc_w (uc_u x y) (uc_c x y) * (uc_t (uc_u x y) (uc_c x y)) ^ 3) := by
  have h1 := r1_pos x hy; have h2 := r2_pos x hy
  have hprod : 0 < r1 x y * r2 x y := mul_pos h1 h2
  have hs := Real.sqrt_pos.mpr hprod
  have hs2 : (Real.sqrt (r1 x y * r2 x y)) ^ 2 = r1 x y * r2 x y := Real.sq_sqrt hprod.le
  have hu := uc_u_nonneg x hy; have hc := (uc_c_bounds x hy).1
  have hw := uc_w_pos hu hc; have ht := uc_t_pos hu hc
  have hAne := h1.ne'; have hBne := h2.ne'; have hPne : r1 x y * r2 x y ≠ 0 := hprod.ne'
  have hsne := hs.ne'; have hwne := hw.ne'; have htne := ht.ne'
  have hx := uc_x_eq x y; have hy2 := uc_y2_eq x y
  unfold uY_xy
  rw [uc_Fq_pow7 x hy, uc_Fsq_eq x hy]
  have hFx : Fx x y = (((r1 x y ^ 2 - r2 x y ^ 2) / 4 + 1) * r2 x y ^ 3 +
      ((r1 x y ^ 2 - r2 x y ^ 2) / 4 - 1) * r1 x y ^ 3) / (r1 x y * r2 x y) ^ 3 := by
    unfold Fx; generalize r1 x y = A at hAne hx ⊢; generalize r2 x y = B at hBne hx ⊢
    rw [hx]; field_simp [hAne, hBne]
  have hFy0 : Fy0 x y = (r2 x y ^ 3 + r1 x y ^ 3) / (r1 x y * r2 x y) ^ 3 := by
    unfold Fy0; field_simp [hAne, hBne]
  have hFxy0 : Fxy0 x y = (-3 * ((r1 x y ^ 2 - r2 x y ^ 2) / 4 + 1) * r2 x y ^ 5 -
      3 * ((r1 x y ^ 2 - r2 x y ^ 2) / 4 - 1) * r1 x y ^ 5) / (r1 x y * r2 x y) ^ 5 := by
    unfold Fxy0; generalize r1 x y = A at hAne hx ⊢; generalize r2 x y = B at hBne hx ⊢
    rw [hx]; field_simp [hAne, hBne]; ring
  have hFyy : Fyy x y = ((r1 x y ^ 2 - 3 * y ^ 2) * r2 x y ^ 5 +
      (r2 x y ^ 2 - 3 * y ^ 2) * r1 x y ^ 5) / (r1 x y * r2 x y) ^ 5 := by
    unfold Fyy; field_simp [hAne, hBne]
  have hw_eq : uc_w (uc_u x y) (uc_c x y) =
      (r1 x y ^ 4 + r2 x y ^ 4 + (r1 x y * r2 x y) * (r1 x y ^ 2 + r2 x y ^ 2 - 4)) / (r1 x y * r2 x y) ^ 2 := by
    rw [uc_w_eq_r x hy]; ring
  have hR12 : R12_m (uc_u x y) (uc_c x y) =
      (4 * (r1 x y ^ 2 + r2 x y ^ 2) * (r1 x y ^ 2 + r2 x y ^ 2 - 2 * (r1 x y * r2 x y)) * (r1 x y * r2 x y) ^ 2 +
        (2 * (r1 x y * r2 x y) - (r1 x y ^ 2 + r2 x y ^ 2 - 4)) *
          ((2 * (r1 x y * r2 x y) + (r1 x y ^ 2 + r2 x y ^ 2 - 4)) *
              ((r1 x y ^ 2 + r2 x y ^ 2) ^ 2 + (r1 x y ^ 2 + r2 x y ^ 2) * (r1 x y * r2 x y) - 4 * (r1 x y * r2 x y) ^ 2) +
            2 * (r1 x y * r2 x y) * (3 * (r1 x y ^ 2 + r2 x y ^ 2) + 2 * (r1 x y * r2 x y)) * (r1 x y * r2 x y))) /
      (4 * (r1 x y * r2 x y) ^ 4) := by
    unfold R12_m; rw [uc_c_eq_r x hy]; unfold uc_u
    field_simp [hAne, hBne, hPne]; ring
  have hmain : (Fxy0 x y * (uc_w (uc_u x y) (uc_c x y) / (r1 x y * r2 x y) ^ 2) -
      3 / 2 * Fx x y * (Fx x y * Fxy0 x y + Fy0 x y * Fyy x y)) * (r1 x y * r2 x y) ^ 3 =
      3 * (r1 x y - r2 x y) * R12_m (uc_u x y) (uc_c x y) / (4 * (r1 x y * r2 x y)) := by
    rw [hFx, hFy0, hFxy0, hFyy, hy2, hw_eq, hR12]
    have hpoly := poly_uY_AB (r1 x y) (r2 x y); dsimp only at hpoly
    field_simp [hPne]
    linear_combination hpoly
  calc (Fxy x y * (uc_w (uc_u x y) (uc_c x y) / (r1 x y * r2 x y) ^ 2) -
        3 / 2 * Fx x y * (Fx x y * Fxy x y + Fy x y * Fyy x y)) /
      (uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3 / ((r1 x y * r2 x y) ^ 3 * Real.sqrt (r1 x y * r2 x y)))
      = ((Fxy0 x y * (uc_w (uc_u x y) (uc_c x y) / (r1 x y * r2 x y) ^ 2) -
          3 / 2 * Fx x y * (Fx x y * Fxy0 x y + Fy0 x y * Fyy x y)) * (r1 x y * r2 x y) ^ 3) *
        (y * Real.sqrt (r1 x y * r2 x y) / (uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3)) := by
          unfold Fxy Fy; field_simp [hPne, hsne, hwne, htne]
    _ = (3 * (r1 x y - r2 x y) * R12_m (uc_u x y) (uc_c x y) / (4 * (r1 x y * r2 x y))) *
        (y * Real.sqrt (r1 x y * r2 x y) / (uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3)) := by
          rw [hmain]
    _ = 3 * y * (r1 x y - r2 x y) * R12_m (uc_u x y) (uc_c x y) /
        (4 * Real.sqrt (r1 x y * r2 x y) * uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3) := by
          field_simp [hPne, hsne, hwne, htne]
          rw [hs2]; ring

lemma vX_xy_eq_uc (x : ℝ) {y : ℝ} (hy : 0 < y) :
    vX_xy x y = -3 * y * (r1 x y - r2 x y) * R21_m (uc_u x y) (uc_c x y) /
      (4 * Real.sqrt (r1 x y * r2 x y) * uc_w (uc_u x y) (uc_c x y) * (uc_t (uc_u x y) (uc_c x y)) ^ 3) := by
  have h1 := r1_pos x hy; have h2 := r2_pos x hy
  have hprod : 0 < r1 x y * r2 x y := mul_pos h1 h2
  have hs := Real.sqrt_pos.mpr hprod
  have hs2 : (Real.sqrt (r1 x y * r2 x y)) ^ 2 = r1 x y * r2 x y := Real.sq_sqrt hprod.le
  have hu := uc_u_nonneg x hy; have hc := (uc_c_bounds x hy).1
  have hw := uc_w_pos hu hc; have ht := uc_t_pos hu hc
  have hAne := h1.ne'; have hBne := h2.ne'; have hPne : r1 x y * r2 x y ≠ 0 := hprod.ne'
  have hsne := hs.ne'; have hwne := hw.ne'; have htne := ht.ne'
  have hx := uc_x_eq x y; have hy2 := uc_y2_eq x y
  unfold vX_xy
  rw [uc_Fq_pow7 x hy, uc_Fsq_eq x hy]
  have hFx : Fx x y = (((r1 x y ^ 2 - r2 x y ^ 2) / 4 + 1) * r2 x y ^ 3 +
      ((r1 x y ^ 2 - r2 x y ^ 2) / 4 - 1) * r1 x y ^ 3) / (r1 x y * r2 x y) ^ 3 := by
    unfold Fx; generalize r1 x y = A at hAne hx ⊢; generalize r2 x y = B at hBne hx ⊢
    rw [hx]; field_simp [hAne, hBne]
  have hFy0 : Fy0 x y = (r2 x y ^ 3 + r1 x y ^ 3) / (r1 x y * r2 x y) ^ 3 := by
    unfold Fy0; field_simp [hAne, hBne]
  have hFxx : Fxx x y = ((r1 x y ^ 2 - 3 * ((r1 x y ^ 2 - r2 x y ^ 2) / 4 + 1) ^ 2) * r2 x y ^ 5 +
      (r2 x y ^ 2 - 3 * ((r1 x y ^ 2 - r2 x y ^ 2) / 4 - 1) ^ 2) * r1 x y ^ 5) / (r1 x y * r2 x y) ^ 5 := by
    unfold Fxx; generalize r1 x y = A at hAne hx ⊢; generalize r2 x y = B at hBne hx ⊢
    rw [hx]; field_simp [hAne, hBne]
  have hFxy0 : Fxy0 x y = (-3 * ((r1 x y ^ 2 - r2 x y ^ 2) / 4 + 1) * r2 x y ^ 5 -
      3 * ((r1 x y ^ 2 - r2 x y ^ 2) / 4 - 1) * r1 x y ^ 5) / (r1 x y * r2 x y) ^ 5 := by
    unfold Fxy0; generalize r1 x y = A at hAne hx ⊢; generalize r2 x y = B at hBne hx ⊢
    rw [hx]; field_simp [hAne, hBne]; ring
  have hw_eq : uc_w (uc_u x y) (uc_c x y) =
      (r1 x y ^ 4 + r2 x y ^ 4 + (r1 x y * r2 x y) * (r1 x y ^ 2 + r2 x y ^ 2 - 4)) / (r1 x y * r2 x y) ^ 2 := by
    rw [uc_w_eq_r x hy]; ring
  have hR21 : R21_m (uc_u x y) (uc_c x y) =
      ((4 * (r1 x y * r2 x y) ^ 2 + (r1 x y ^ 2 + r2 x y ^ 2 - 4) ^ 2) *
          ((r1 x y ^ 2 + r2 x y ^ 2) ^ 2 + (r1 x y ^ 2 + r2 x y ^ 2) * (r1 x y * r2 x y) + 2 * (r1 x y * r2 x y) ^ 2) -
        4 * (r1 x y * r2 x y) ^ 2 * (r1 x y ^ 2 + r2 x y ^ 2 - 4) *
          (3 * (r1 x y ^ 2 + r2 x y ^ 2) + 2 * (r1 x y * r2 x y))) /
      (4 * (r1 x y * r2 x y) ^ 4) := by
    unfold R21_m; rw [uc_c_eq_r x hy]; unfold uc_u
    field_simp [hAne, hBne, hPne]; ring
  have hmain : (Fxy0 x y * (uc_w (uc_u x y) (uc_c x y) / (r1 x y * r2 x y) ^ 2) -
      3 / 2 * Fy0 x y * (Fx x y * Fxx x y + y ^ 2 * Fy0 x y * Fxy0 x y)) * (r1 x y * r2 x y) ^ 3 =
      -3 * (r1 x y - r2 x y) * R21_m (uc_u x y) (uc_c x y) / (4 * (r1 x y * r2 x y)) := by
    rw [hFx, hFy0, hFxx, hFxy0, hy2, hw_eq, hR21]
    have hpoly := poly_vX_AB (r1 x y) (r2 x y); dsimp only at hpoly
    field_simp [hPne]
    linear_combination hpoly
  calc (Fxy x y * (uc_w (uc_u x y) (uc_c x y) / (r1 x y * r2 x y) ^ 2) -
        3 / 2 * Fy x y * (Fx x y * Fxx x y + Fy x y * Fxy x y)) /
      (uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3 / ((r1 x y * r2 x y) ^ 3 * Real.sqrt (r1 x y * r2 x y)))
      = ((Fxy0 x y * (uc_w (uc_u x y) (uc_c x y) / (r1 x y * r2 x y) ^ 2) -
          3 / 2 * Fy0 x y * (Fx x y * Fxx x y + y ^ 2 * Fy0 x y * Fxy0 x y)) * (r1 x y * r2 x y) ^ 3) *
        (y * Real.sqrt (r1 x y * r2 x y) / (uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3)) := by
          unfold Fxy Fy; field_simp [hPne, hsne, hwne, htne]
    _ = (-3 * (r1 x y - r2 x y) * R21_m (uc_u x y) (uc_c x y) / (4 * (r1 x y * r2 x y))) *
        (y * Real.sqrt (r1 x y * r2 x y) / (uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3)) := by
          rw [hmain]
    _ = -3 * y * (r1 x y - r2 x y) * R21_m (uc_u x y) (uc_c x y) /
        (4 * Real.sqrt (r1 x y * r2 x y) * uc_w (uc_u x y) (uc_c x y) * uc_t (uc_u x y) (uc_c x y) ^ 3) := by
          field_simp [hPne, hsne, hwne, htne]
          rw [hs2]; ring

lemma det_xy_eq_uc (x : ℝ) {y : ℝ} (hy : 0 < y) :
    uX_xy x y * vY_xy x y - uY_xy x y * vX_xy x y = det_uc (uc_u x y) (uc_c x y) := by
  rw [uX_xy_eq_uc x hy, vY_xy_eq_uc x hy, uY_xy_eq_uc x hy, vX_xy_eq_uc x hy]
  set u := uc_u x y; set c := uc_c x y
  have hu : 0 ≤ u := uc_u_nonneg x hy
  have hc : -1 < c ∧ c < 1 := uc_c_bounds x hy
  have hLm : 2 + u - 2 * c ≠ 0 := by linarith
  have hw := uc_w_pos hu hc.1; have ht := uc_t_pos hu hc.1
  have hwne := hw.ne'; have htne := ht.ne'
  have hprod : 0 < r1 x y * r2 x y := mul_pos (r1_pos x hy) (r2_pos x hy)
  have hs := Real.sqrt_pos.mpr hprod
  have hsne := hs.ne'; have hPne : r1 x y * r2 x y ≠ 0 := hprod.ne'
  have hs2 : (Real.sqrt (r1 x y * r2 x y)) ^ 2 = r1 x y * r2 x y := Real.sq_sqrt hprod.le
  have hs4u : (Real.sqrt (4 + u)) ^ 2 = 4 + u := Real.sq_sqrt (by linarith)
  have ht4 : (uc_t u c) ^ 4 = uc_w u c := uc_t_pow4 hu hc.1
  have hLm_r : 2 + u - 2 * c = 4 / (r1 x y * r2 x y) := uc_Lm_eq x hy
  have hy2_c : y ^ 2 = 4 * (1 - c ^ 2) / (2 + u - 2 * c) ^ 2 := by
    have h1 : 1 - c ^ 2 = (2 * y / (r1 x y * r2 x y)) ^ 2 := uc_one_sub_c_sq x hy
    rw [hLm_r, h1]
    have h1ne := (r1_pos x hy).ne'; have h2ne := (r2_pos x hy).ne'
    field_simp [h1ne, h2ne]; ring
  have hr12 : (r1 x y - r2 x y) ^ 2 = u * (r1 x y * r2 x y) := by
    change (r1 x y - r2 x y) ^ 2 = (((r1 x y) ^ 2 + (r2 x y) ^ 2) / (r1 x y * r2 x y) - 2) * (r1 x y * r2 x y)
    rw [sub_mul, div_mul_cancel₀ _ hPne]; ring
  have hid1 : Q11_m u c + Q22_m u c = (2 + u - 2 * c) * T0_m u c := by
    unfold Q11_m Q22_m T0_m; ring
  have hid2 : (4 + u) * Q11_m u c * Q22_m u c + 9 * (1 - c ^ 2) * u * R12_m u c * R21_m u c =
      2 * (2 + u - 2 * c) ^ 2 * (uc_w u c) ^ 2 * D0_m u c := by
    unfold Q11_m Q22_m R12_m R21_m uc_w D0_m; ring
  have hcross :
      -(3 * y * (r1 x y - r2 x y) * R12_m u c /
          (4 * Real.sqrt (r1 x y * r2 x y) * uc_w u c * (uc_t u c) ^ 3) *
        (-3 * y * (r1 x y - r2 x y) * R21_m u c /
          (4 * Real.sqrt (r1 x y * r2 x y) * uc_w u c * (uc_t u c) ^ 3))) =
      9 * (1 - c ^ 2) * u * R12_m u c * R21_m u c /
        (4 * (2 + u - 2 * c) ^ 2 * (uc_w u c) ^ 2 * (uc_t u c) ^ 6) := by
    have hmul : 9 * y ^ 2 * (r1 x y - r2 x y) ^ 2 =
        36 * (1 - c ^ 2) * u * (r1 x y * r2 x y) / (2 + u - 2 * c) ^ 2 := by
      rw [hy2_c, hr12]; ring
    rw [show -(3 * y * (r1 x y - r2 x y) * R12_m u c /
          (4 * Real.sqrt (r1 x y * r2 x y) * uc_w u c * (uc_t u c) ^ 3) *
        (-3 * y * (r1 x y - r2 x y) * R21_m u c /
          (4 * Real.sqrt (r1 x y * r2 x y) * uc_w u c * (uc_t u c) ^ 3))) =
        (9 * y ^ 2 * (r1 x y - r2 x y) ^ 2) * R12_m u c * R21_m u c /
          (16 * (Real.sqrt (r1 x y * r2 x y)) ^ 2 * (uc_w u c) ^ 2 * (uc_t u c) ^ 6) by ring]
    rw [hmul, hs2]
    have h1ne := (r1_pos x hy).ne'; have h2ne := (r2_pos x hy).ne'
    field_simp [h1ne, h2ne, hLm, hwne, htne]; ring
  unfold uX_uc vY_uc det_uc F_det
  rw [sub_eq_add_neg, hcross]
  field_simp [hLm, hwne, htne]
  linear_combination
    8 * (2 + u - 2 * c) * uc_w u c * (uc_t u c) ^ 3 * Real.sqrt (4 + u) * hid1 +
    4 * Q11_m u c * Q22_m u c * hs4u + 4 * hid2 -
    8 * (2 + u - 2 * c) ^ 2 * uc_w u c * D0_m u c * ht4

/- Section 3: Pure algebraic sign theorems (Steps A & B) -/

lemma R12_m_pos {u c : ℝ} (hu : 0 ≤ u) (hc1 : -1 < c) (hc2 : c < 1) : 0 < R12_m u c := by
  unfold R12_m
  have h1 : 0 ≤ (2 + u) * u := by positivity
  have h2 : 0 < 1 - c := by linarith
  have h3 : 0 < 1 + c := by linarith
  have h4 : 0 < (2 + u) ^ 2 + (2 + u) - 4 := by nlinarith
  have h5 : 0 < 3 * (2 + u) + 2 := by linarith
  have h6 : 0 < (1 + c) * ((2 + u) ^ 2 + (2 + u) - 4) := mul_pos h3 h4
  have h7 : 0 < (1 - c) * ((1 + c) * ((2 + u) ^ 2 + (2 + u) - 4) + (3 * (2 + u) + 2)) :=
    mul_pos h2 (by linarith)
  linarith

lemma R21_m_pos {u c : ℝ} (hu : 0 ≤ u) (_hc1 : -1 < c) (hc2 : c < 1) : 0 < R21_m u c := by
  unfold R21_m
  set m := 2 + u
  have hm : 2 ≤ m := by linarith
  by_cases hc : c ≤ 0
  · have h1 : 0 < m ^ 2 + m + 2 := by nlinarith
    have h2 : 0 < 3 * m + 2 := by linarith
    nlinarith [sq_nonneg c]
  · push Not at hc
    have hident : (1 + c ^ 2) * (m ^ 2 + m + 2) - 2 * c * (3 * m + 2) =
        (1 - c) ^ 2 * (m ^ 2 + m + 2) + 2 * c * m * (m - 2) := by ring
    rw [hident]
    have h1 : 0 < (1 - c) ^ 2 := sq_pos_of_pos (by linarith)
    have h2 : 0 < m ^ 2 + m + 2 := by nlinarith
    have h3 : 0 ≤ m - 2 := by linarith
    have h4 : 0 ≤ 2 * c * m * (m - 2) := by positivity
    nlinarith

lemma uY_xy_pos_of_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < uY_xy x y := by
  rw [uY_xy_eq_uc x hy]
  have h1 := r1_pos x hy; have h2 := r2_pos x hy
  have hgt : r2 x y < r1 x y := by
    have : (r2 x y) ^ 2 < (r1 x y) ^ 2 := by rw [r1_sq, r2_sq]; nlinarith
    nlinarith
  have hR := R12_m_pos (uc_u_nonneg x hy) (uc_c_bounds x hy).1 (uc_c_bounds x hy).2
  have hw := uc_w_pos (uc_u_nonneg x hy) (uc_c_bounds x hy).1
  have ht := uc_t_pos (uc_u_nonneg x hy) (uc_c_bounds x hy).1
  have hs := Real.sqrt_pos.mpr (mul_pos h1 h2)
  have hdiff : 0 < r1 x y - r2 x y := by linarith
  positivity

lemma uY_xy_neg_of_neg {x y : ℝ} (hx : x < 0) (hy : 0 < y) : uY_xy x y < 0 := by
  rw [uY_xy_eq_uc x hy]
  have h1 := r1_pos x hy; have h2 := r2_pos x hy
  have hlt : r1 x y < r2 x y := by
    have : (r1 x y) ^ 2 < (r2 x y) ^ 2 := by rw [r1_sq, r2_sq]; nlinarith
    nlinarith
  have hR := R12_m_pos (uc_u_nonneg x hy) (uc_c_bounds x hy).1 (uc_c_bounds x hy).2
  have hw := uc_w_pos (uc_u_nonneg x hy) (uc_c_bounds x hy).1
  have ht := uc_t_pos (uc_u_nonneg x hy) (uc_c_bounds x hy).1
  have hs := Real.sqrt_pos.mpr (mul_pos h1 h2)
  have hdiff : 0 < r2 x y - r1 x y := by linarith
  have hpos : 0 < 3 * y * (r2 x y - r1 x y) * R12_m (uc_u x y) (uc_c x y) := by positivity
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

lemma vX_xy_neg_of_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : vX_xy x y < 0 := by
  rw [vX_xy_eq_uc x hy]
  have h1 := r1_pos x hy; have h2 := r2_pos x hy
  have hgt : r2 x y < r1 x y := by
    have : (r2 x y) ^ 2 < (r1 x y) ^ 2 := by rw [r1_sq, r2_sq]; nlinarith
    nlinarith
  have hR := R21_m_pos (uc_u_nonneg x hy) (uc_c_bounds x hy).1 (uc_c_bounds x hy).2
  have hw := uc_w_pos (uc_u_nonneg x hy) (uc_c_bounds x hy).1
  have ht := uc_t_pos (uc_u_nonneg x hy) (uc_c_bounds x hy).1
  have hs := Real.sqrt_pos.mpr (mul_pos h1 h2)
  have hdiff : 0 < r1 x y - r2 x y := by linarith
  have hpos : 0 < 3 * y * (r1 x y - r2 x y) * R21_m (uc_u x y) (uc_c x y) := by positivity
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

lemma vX_xy_pos_of_neg {x y : ℝ} (hx : x < 0) (hy : 0 < y) : 0 < vX_xy x y := by
  rw [vX_xy_eq_uc x hy]
  have h1 := r1_pos x hy; have h2 := r2_pos x hy
  have hlt : r1 x y < r2 x y := by
    have : (r1 x y) ^ 2 < (r2 x y) ^ 2 := by rw [r1_sq, r2_sq]; nlinarith
    nlinarith
  have hR := R21_m_pos (uc_u_nonneg x hy) (uc_c_bounds x hy).1 (uc_c_bounds x hy).2
  have hw := uc_w_pos (uc_u_nonneg x hy) (uc_c_bounds x hy).1
  have ht := uc_t_pos (uc_u_nonneg x hy) (uc_c_bounds x hy).1
  have hs := Real.sqrt_pos.mpr (mul_pos h1 h2)
  have hdiff : 0 < r2 x y - r1 x y := by linarith
  have hpos : 0 < 3 * y * (r2 x y - r1 x y) * R21_m (uc_u x y) (uc_c x y) := by positivity
  exact div_pos (by linarith) (by positivity)

lemma Q22_m_pos_of_c_nonneg {u c : ℝ} (hu : 0 ≤ u) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 < Q22_m u c := by
  unfold Q22_m
  have h0 : 0 < 2 + 6 * c - 2 * c ^ 2 - 6 * c ^ 3 := by
    have : 2 + 6 * c - 2 * c ^ 2 - 6 * c ^ 3 = 2 * (1 - c) * (1 + c) * (1 + 3 * c) := by ring
    rw [this]; have : 0 < 1 - c := by linarith
    positivity
  have h1 : 0 < 28 - 21 * c - 8 * c ^ 2 + 9 * c ^ 3 := by
    have : 28 - 21 * c - 8 * c ^ 2 + 9 * c ^ 3 = (1 - c) * (28 + 7 * c - c ^ 2) + 8 * c ^ 3 := by ring
    rw [this]; have : 0 < 28 + 7 * c - c ^ 2 := by nlinarith
    have : 0 < 1 - c := by linarith
    positivity
  have h2 : 0 < 32 - 19 * c + 3 * c ^ 3 := by nlinarith [pow_nonneg hc0 3]
  have h3 : 0 < 14 - 4 * c := by linarith
  have hcomb :
      (2 + 28 * u + 32 * u ^ 2 + 14 * u ^ 3 + 2 * u ^ 4) +
      (6 - 21 * u - 19 * u ^ 2 - 4 * u ^ 3) * c +
      (-2 - 8 * u) * c ^ 2 +
      (-6 + 9 * u + 3 * u ^ 2) * c ^ 3 =
      (2 + 6 * c - 2 * c ^ 2 - 6 * c ^ 3) +
      u * (28 - 21 * c - 8 * c ^ 2 + 9 * c ^ 3) +
      u ^ 2 * (32 - 19 * c + 3 * c ^ 3) +
      u ^ 3 * (14 - 4 * c) + 2 * u ^ 4 := by ring
  rw [hcomb]; positivity

lemma Q22_sub_Q11_pos_of_c_nonpos {u c : ℝ} (hu : 0 ≤ u) (hc1 : -1 < c) (hc0 : c ≤ 0) :
    0 < Q22_m u c - Q11_m u c := by
  unfold Q22_m Q11_m
  have hident :
      ((2 + 28 * u + 32 * u ^ 2 + 14 * u ^ 3 + 2 * u ^ 4) +
        (6 - 21 * u - 19 * u ^ 2 - 4 * u ^ 3) * c +
        (-2 - 8 * u) * c ^ 2 + (-6 + 9 * u + 3 * u ^ 2) * c ^ 3) -
      ((-4 + 19 * u + 32 * u ^ 2 + 14 * u ^ 3 + 2 * u ^ 4) +
        (12 - 3 * u - 13 * u ^ 2 - 4 * u ^ 3) * c +
        (4 + u) * c ^ 2 + (-12 - 9 * u - 3 * u ^ 2) * c ^ 3) =
      3 * (1 - c ^ 2) * ((2 + 3 * u) + 2 * (-c) * (1 + 3 * u + u ^ 2)) := by ring
  rw [hident]
  have h1 : 0 < 1 - c ^ 2 := by nlinarith
  have h2 : 0 ≤ -c := by linarith
  have h3 : 0 < (2 + 3 * u) + 2 * (-c) * (1 + 3 * u + u ^ 2) := by positivity
  positivity

lemma vY_uc_pos_of_uX_uc_nonneg {u c : ℝ} (hu : 0 ≤ u) (hc1 : -1 < c) (hc2 : c < 1)
    (hux : 0 ≤ uX_uc u c) : 0 < vY_uc u c := by
  have hLm : 0 < 2 + u - 2 * c := by linarith
  have hw : 0 < uc_w u c := uc_w_pos hu hc1
  have ht : 0 < uc_t u c := uc_t_pos hu hc1
  have hs : 0 < Real.sqrt (4 + u) := Real.sqrt_pos.mpr (by linarith)
  have hden : 0 < 2 * (2 + u - 2 * c) * uc_w u c * (uc_t u c) ^ 3 := by positivity
  by_cases hc : 0 ≤ c
  · have hQ := Q22_m_pos_of_c_nonneg hu hc hc2
    unfold vY_uc
    have : 0 < Real.sqrt (4 + u) * Q22_m u c / (2 * (2 + u - 2 * c) * uc_w u c * (uc_t u c) ^ 3) :=
      div_pos (mul_pos hs hQ) hden
    linarith
  · push Not at hc
    have hdiff := Q22_sub_Q11_pos_of_c_nonpos hu hc1 hc.le
    have : uX_uc u c < vY_uc u c := by
      unfold uX_uc vY_uc
      have := div_lt_div_of_pos_right (mul_lt_mul_of_pos_left (by linarith : Q11_m u c < Q22_m u c) hs) hden
      linarith
    linarith

lemma det_pos_of_uX_nonneg {x y : ℝ} (hy : 0 < y) (hux : 0 ≤ uX_xy x y)
    (hne : x ≠ 0 ∨ 0 < uX_xy x y) :
    0 < uX_xy x y * vY_xy x y - uY_xy x y * vX_xy x y := by
  have hvy : 0 < vY_xy x y := by
    rw [vY_xy_eq_uc x hy]
    exact vY_uc_pos_of_uX_uc_nonneg (uc_u_nonneg x hy) (uc_c_bounds x hy).1 (uc_c_bounds x hy).2
      (by rwa [← uX_xy_eq_uc x hy])
  rcases hne with hxne | hux_pos
  · rcases lt_or_gt_of_ne hxne with hxlt | hxgt
    · have h1 := uY_xy_neg_of_neg hxlt hy
      have h2 := vX_xy_pos_of_neg hxlt hy
      nlinarith
    · have h1 := uY_xy_pos_of_pos hxgt hy
      have h2 := vX_xy_neg_of_pos hxgt hy
      nlinarith
  · have hprod : uY_xy x y * vX_xy x y ≤ 0 := by
      rcases lt_trichotomy x 0 with hxlt | rfl | hxgt
      · have h1 := uY_xy_neg_of_neg hxlt hy; have h2 := vX_xy_pos_of_neg hxlt hy; nlinarith
      · rw [uY_xy_eq_uc 0 hy, r1, r2]; simp
      · have h1 := uY_xy_pos_of_pos hxgt hy; have h2 := vX_xy_neg_of_pos hxgt hy; nlinarith
    nlinarith

lemma uX_uc_pos_of_c_nonneg {u c : ℝ} (hu : 0 ≤ u) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 < uX_uc u c := by
  have hcgt : -1 < c := by linarith
  have hLm : 0 < 2 + u - 2 * c := by linarith
  have hw : 0 < uc_w u c := uc_w_pos hu hcgt
  have ht : 0 < uc_t u c := uc_t_pos hu hcgt
  have hs : 0 < Real.sqrt (4 + u) := Real.sqrt_pos.mpr (by linarith)
  have hden : 0 < 2 * (2 + u - 2 * c) * uc_w u c * (uc_t u c) ^ 3 := by positivity
  have hQ_decomp : Q11_m u c =
      -4 * (1 - c ^ 2) * (1 - 3 * c) +
      u * (19 - 3 * c + c ^ 2 - 9 * c ^ 3) +
      u ^ 2 * (32 - 13 * c - 3 * c ^ 3) +
      u ^ 3 * (14 - 4 * c) + 2 * u ^ 4 := by
    unfold Q11_m; ring
  have h1 : 0 < 19 - 3 * c + c ^ 2 - 9 * c ^ 3 := by nlinarith [sq_nonneg c]
  have h2 : 0 < 32 - 13 * c - 3 * c ^ 3 := by nlinarith [sq_nonneg c]
  have h3 : 0 < 14 - 4 * c := by linarith
  have hu_pos_part : 0 ≤ u * (19 - 3 * c + c ^ 2 - 9 * c ^ 3) +
      u ^ 2 * (32 - 13 * c - 3 * c ^ 3) + u ^ 3 * (14 - 4 * c) + 2 * u ^ 4 := by positivity
  by_cases hc3 : 1 / 3 ≤ c
  · have h0 : 0 ≤ -4 * (1 - c ^ 2) * (1 - 3 * c) := by
      have : -4 * (1 - c ^ 2) * (1 - 3 * c) = 4 * (1 - c ^ 2) * (3 * c - 1) := by ring
      rw [this]; have : 0 ≤ 1 - c ^ 2 := by nlinarith
      have : 0 ≤ 3 * c - 1 := by linarith
      positivity
    have hQ : 0 ≤ Q11_m u c := by linarith
    unfold uX_uc
    have : 0 ≤ Real.sqrt (4 + u) * Q11_m u c / (2 * (2 + u - 2 * c) * uc_w u c * (uc_t u c) ^ 3) :=
      div_nonneg (mul_nonneg hs.le hQ) hden.le
    linarith
  · push Not at hc3
    have hQ_ge : -4 ≤ Q11_m u c := by
      have h_c1 : 0 ≤ 1 - c ^ 2 := by nlinarith
      have h_c2 : 1 - c ^ 2 ≤ 1 := by nlinarith
      have h_c3 : 0 < 1 - 3 * c := by linarith
      have h_c4 : 1 - 3 * c ≤ 1 := by linarith
      nlinarith
    have hLm_ge : 4 / 3 ≤ 2 + u - 2 * c := by linarith
    have hw_ge : 2 + 4 * u + u ^ 2 ≤ uc_w u c := by unfold uc_w; linarith
    have hs_le : Real.sqrt (4 + u) ≤ 2 + u / 4 := by
      have : (Real.sqrt (4 + u)) ^ 2 ≤ (2 + u / 4) ^ 2 := by
        rw [Real.sq_sqrt (by linarith)]; nlinarith [sq_nonneg u]
      nlinarith
    have ht_ge : (19 / 16 : ℝ) ≤ uc_t u c := by
      have h1 : (19 / 16 : ℝ) ^ 4 ≤ (uc_t u c) ^ 4 := by
        rw [uc_t_pow4 hu hcgt]; nlinarith
      nlinarith [pow_pos ht 2, pow_pos ht 3]
    have ht3_ge : (6859 / 4096 : ℝ) ≤ (uc_t u c) ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 19 / 16) ht_ge 3
      linarith
    have hnum_lt : 4 * Real.sqrt (4 + u) < 2 * (2 + u - 2 * c) * uc_w u c * (uc_t u c) ^ 3 := by
      have h_rhs1 : (4 / 3 : ℝ) * (2 + 4 * u) ≤ (2 + u - 2 * c) * uc_w u c := by
        have : 2 + 4 * u ≤ uc_w u c := by nlinarith
        nlinarith
      have h_rhs2 : 2 * ((4 / 3 : ℝ) * (2 + 4 * u)) * (6859 / 4096 : ℝ) ≤
          2 * (2 + u - 2 * c) * uc_w u c * (uc_t u c) ^ 3 := by
        have : 0 ≤ 2 * (2 + u - 2 * c) * uc_w u c := by positivity
        nlinarith
      linarith
    unfold uX_uc
    rw [show (1 : ℝ) + Real.sqrt (4 + u) * Q11_m u c /
        (2 * (2 + u - 2 * c) * uc_w u c * (uc_t u c) ^ 3) =
        (2 * (2 + u - 2 * c) * uc_w u c * (uc_t u c) ^ 3 + Real.sqrt (4 + u) * Q11_m u c) /
        (2 * (2 + u - 2 * c) * uc_w u c * (uc_t u c) ^ 3) by field_simp [hden.ne']]
    have hprod_ge : -4 * Real.sqrt (4 + u) ≤ Real.sqrt (4 + u) * Q11_m u c := by
      have := mul_le_mul_of_nonneg_left hQ_ge hs.le; linarith
    exact div_pos (by linarith) hden

/- Section 4: Horizontal slice monotonicity (Fact 4) -/

def D_Q_poly (u c : ℝ) : ℝ :=
  (50 + 125 * u + 71 * u ^ 2 + 12 * u ^ 3) +
  (-36 - 197 * u - 172 * u ^ 2 - 58 * u ^ 3 - 8 * u ^ 4) * c +
  (-40 + 31 * u + 54 * u ^ 2 + 16 * u ^ 3) * c ^ 2 +
  (-28 - 15 * u) * c ^ 3 +
  (54 + 48 * u + 15 * u ^ 2) * c ^ 4

def R_ux_poly (u c : ℝ) : ℝ :=
  (-544 - 604 * u - 214 * u ^ 2 - 24 * u ^ 3) +
  (1056 + 1252 * u + 644 * u ^ 2 + 164 * u ^ 3 + 16 * u ^ 4) * c +
  (-352 - 548 * u - 246 * u ^ 2 - 32 * u ^ 3) * c ^ 2 +
  (-160 - 36 * u) * c ^ 3

lemma D_Q_poly_pos {u c : ℝ} (hu : 0 ≤ u) (hc1 : -1 ≤ c) (hc0 : c ≤ 0) :
    0 < D_Q_poly u c := by
  set b := -c
  have hb0 : 0 ≤ b := by linarith
  have hb1 : b ≤ 1 := by linarith
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have hrew : D_Q_poly u c =
      (50 - 40 * b ^ 2) +
      (125 * u + 71 * u ^ 2 + 12 * u ^ 3) +
      b * (36 + 197 * u + 172 * u ^ 2 + 58 * u ^ 3 + 8 * u ^ 4) +
      b ^ 2 * (31 * u + 54 * u ^ 2 + 16 * u ^ 3) +
      b ^ 3 * (28 + 15 * u) +
      b ^ 4 * (54 + 48 * u + 15 * u ^ 2) := by
    unfold D_Q_poly; simp only [b]; ring
  rw [hrew]
  have hfirst : 0 < 50 - 40 * b ^ 2 := by linarith
  positivity

lemma R_ux_poly_neg {u c : ℝ} (hu : 0 ≤ u) (hc1 : -1 ≤ c) (hc0 : c ≤ 0) :
    R_ux_poly u c < 0 := by
  set b := -c
  have hb0 : 0 ≤ b := by linarith
  have hb1 : b ≤ 1 := by linarith
  have hb3 : b ^ 3 ≤ 1 := by nlinarith [sq_nonneg b]
  have hrew : -R_ux_poly u c =
      (544 - 160 * b ^ 3) + u * (604 - 36 * b ^ 3) +
      (214 * u ^ 2 + 24 * u ^ 3) +
      b * (1056 + 1252 * u + 644 * u ^ 2 + 164 * u ^ 3 + 16 * u ^ 4) +
      b ^ 2 * (352 + 548 * u + 246 * u ^ 2 + 32 * u ^ 3) := by
    unfold R_ux_poly; simp only [b]; ring
  have h1 : 0 < 544 - 160 * b ^ 3 := by linarith
  have h2 : 0 < 604 - 36 * b ^ 3 := by linarith
  have hpos : 0 < -R_ux_poly u c := by rw [hrew]; positivity
  linarith

lemma hasDerivAt_uX_x_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hux : uX_xy x y ≤ 0) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (fun t => uX_xy t y) d x := by
  set u := uc_u x y
  set c := uc_c x y
  have hu : 0 ≤ u := uc_u_nonneg x hy
  have hc : -1 < c ∧ c < 1 := uc_c_bounds x hy
  have hc_neg : c < 0 := by
    by_contra h
    push Not at h
    have hpos := uX_uc_pos_of_c_nonneg hu h hc.2
    rw [uX_xy_eq_uc x hy] at hux
    linarith
  have hQ_neg : Q11_m u c < 0 := by
    by_contra h
    push Not at h
    have hLm : 0 < 2 + u - 2 * c := by linarith
    have hw : 0 < uc_w u c := uc_w_pos hu hc.1
    have ht : 0 < uc_t u c := uc_t_pos hu hc.1
    have hs : 0 < Real.sqrt (4 + u) := Real.sqrt_pos.mpr (by linarith)
    have : 0 ≤ Real.sqrt (4 + u) * Q11_m u c / (2 * (2 + u - 2 * c) * uc_w u c * (uc_t u c) ^ 3) := by
      positivity
    rw [uX_xy_eq_uc x hy] at hux
    unfold uX_uc at hux
    linarith
  have hr1d : HasDerivAt (fun t => r1 t y) ((x + 1) / r1 x y) x :=
    hasDerivAt_x_of_lin2 (hasFDerivAt_r1 x hy)
  have hr2d : HasDerivAt (fun t => r2 t y) ((x - 1) / r2 x y) x :=
    hasDerivAt_x_of_lin2 (hasFDerivAt_r2 x hy)
  have hr1 := r1_pos x hy; have hr2 := r2_pos x hy
  have hP : 0 < r1 x y * r2 x y := mul_pos hr1 hr2
  have h1ne := hr1.ne'; have h2ne := hr2.ne'; have hPne := hP.ne'
  have hsq : (r1 x y * r2 x y) ^ 2 = (x ^ 2 + y ^ 2 - 1) ^ 2 + 4 * y ^ 2 := by
    calc (r1 x y * r2 x y) ^ 2 = (r1 x y) ^ 2 * (r2 x y) ^ 2 := by ring
      _ = ((x + 1) ^ 2 + y ^ 2) * ((x - 1) ^ 2 + y ^ 2) := by rw [r1_sq, r2_sq]
      _ = (x ^ 2 + y ^ 2 - 1) ^ 2 + 4 * y ^ 2 := by ring
  have hPd : HasDerivAt (fun t => r1 t y * r2 t y)
      (2 * x * (x ^ 2 + y ^ 2 - 1) / (r1 x y * r2 x y)) x :=
    (hr1d.mul hr2d).congr_deriv (by
      field_simp [h1ne, h2ne]
      linear_combination (x + 1) * r2_sq x y + (x - 1) * r1_sq x y)
  have h_num_u : HasDerivAt (fun t => (r1 t y) ^ 2 + (r2 t y) ^ 2) (4 * x) x := by
    have hfun : (fun t => (r1 t y) ^ 2 + (r2 t y) ^ 2) = fun t => 2 * t ^ 2 + (2 * y ^ 2 + 2) := by
      ext t; linarith [r1_sq t y, r2_sq t y]
    rw [hfun]
    exact (((hasDerivAt_pow 2 x).const_mul 2).add_const (2 * y ^ 2 + 2)).congr_deriv (by
      norm_num; ring)
  have hud : HasDerivAt (fun t => uc_u t y)
      (8 * x * (1 + y ^ 2 - x ^ 2) / (r1 x y * r2 x y) ^ 3) x := by
    unfold uc_u
    exact ((h_num_u.div hPd hPne).sub_const 2).congr_deriv (by
      have hsum : (r1 x y) ^ 2 + (r2 x y) ^ 2 = 2 * x ^ 2 + 2 * y ^ 2 + 2 := by
        linarith [r1_sq x y, r2_sq x y]
      field_simp [h1ne, h2ne, hPne]
      linear_combination 4 * hsq - 2 * (x ^ 2 + y ^ 2 - 1) * hsum)
  have hcd : HasDerivAt (fun t => uc_c t y) (8 * x * y ^ 2 / (r1 x y * r2 x y) ^ 3) x := by
    unfold uc_c
    have hnum : HasDerivAt (fun t => t ^ 2 + y ^ 2 - 1) (2 * x) x :=
      (((hasDerivAt_pow 2 x).add_const (y ^ 2)).sub_const 1).congr_deriv (by simp)
    exact (hnum.div hPd hPne).congr_deriv (by
      field_simp [h1ne, h2ne, hPne]
      linear_combination 2 * hsq)
  have hdu_rel : 8 * x * (1 + y ^ 2 - x ^ 2) / (r1 x y * r2 x y) ^ 3 =
      (2 * x / (r1 x y * r2 x y)) * (2 - c * (2 + u)) := by
    have h1 : 2 + u = (2 * x ^ 2 + 2 * y ^ 2 + 2) / (r1 x y * r2 x y) := by
      change 2 + (((r1 x y) ^ 2 + (r2 x y) ^ 2) / (r1 x y * r2 x y) - 2) = _
      rw [show 2 + (((r1 x y) ^ 2 + (r2 x y) ^ 2) / (r1 x y * r2 x y) - 2) =
          ((r1 x y) ^ 2 + (r2 x y) ^ 2) / (r1 x y * r2 x y) by ring]
      congr 1; linarith [r1_sq x y, r2_sq x y]
    have h2 : c = (x ^ 2 + y ^ 2 - 1) / (r1 x y * r2 x y) := rfl
    rw [h1, h2]; field_simp [h1ne, h2ne, hPne]; linear_combination -4 * hsq
  have hdc_rel : 8 * x * y ^ 2 / (r1 x y * r2 x y) ^ 3 =
      (2 * x / (r1 x y * r2 x y)) * (1 - c ^ 2) := by
    have h1 : 1 - c ^ 2 = (2 * y / (r1 x y * r2 x y)) ^ 2 := uc_one_sub_c_sq x hy
    rw [h1]; field_simp [h1ne, h2ne, hPne]; ring
  set du := 8 * x * (1 + y ^ 2 - x ^ 2) / (r1 x y * r2 x y) ^ 3
  set dc := 8 * x * y ^ 2 / (r1 x y * r2 x y) ^ 3
  set w := uc_w u c
  set t0 := uc_t u c
  set Lm := 2 + u - 2 * c
  have hw : 0 < w := uc_w_pos hu hc.1
  have ht0 : 0 < t0 := uc_t_pos hu hc.1
  have hLm : 0 < Lm := by linarith
  have hs4 : 0 < Real.sqrt (4 + u) := Real.sqrt_pos.mpr (by linarith)
  have hwd : HasDerivAt (fun s => uc_w (uc_u s y) (uc_c s y)) ((4 + 2 * u) * du + 2 * dc) x := by
    unfold uc_w
    exact ((((hasDerivAt_const x (2 : ℝ)).add (hcd.const_mul 2)).add
      (hud.const_mul 4)).add (hud.pow 2)).congr_deriv (by
        change 0 + 2 * dc + 4 * du + (2 : ℕ) * u ^ (2 - 1) * du = _
        norm_num; ring)
  have hLmd : HasDerivAt (fun s => 2 + uc_u s y - 2 * uc_c s y) (du - 2 * dc) x :=
    (((hasDerivAt_const x (2 : ℝ)).add hud).sub (hcd.const_mul 2)).congr_deriv (by ring)
  have hs4d : HasDerivAt (fun s => Real.sqrt (4 + uc_u s y)) (du / (2 * Real.sqrt (4 + u))) x :=
    (((hasDerivAt_const x (4 : ℝ)).add hud).sqrt (by dsimp; linarith)).congr_deriv (by
      change (0 + du) / (2 * Real.sqrt (4 + u)) = _; ring)
  have ht0d : HasDerivAt (fun s => uc_t (uc_u s y) (uc_c s y))
      (((4 + 2 * u) * du + 2 * dc) / (4 * Real.sqrt w * t0)) x := by
    unfold uc_t
    have hsqw : HasDerivAt (fun s => Real.sqrt (uc_w (uc_u s y) (uc_c s y)))
        (((4 + 2 * u) * du + 2 * dc) / (2 * Real.sqrt w)) x :=
      (hwd.sqrt hw.ne').congr_deriv (by ring)
    exact (hsqw.sqrt (Real.sqrt_pos.mpr hw).ne').congr_deriv (by
      have hne1 : Real.sqrt w ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
      have hne2 : t0 ≠ 0 := ht0.ne'
      change (((4 + 2 * u) * du + 2 * dc) / (2 * Real.sqrt w)) / (2 * t0) = _
      field_simp [hne1, hne2]; ring)
  set Qu := (19 + 64 * u + 42 * u ^ 2 + 8 * u ^ 3) + (-3 - 26 * u - 12 * u ^ 2) * c +
      c ^ 2 + (-9 - 6 * u) * c ^ 3
  set Qc := (12 - 3 * u - 13 * u ^ 2 - 4 * u ^ 3) + 2 * (4 + u) * c +
      3 * (-12 - 9 * u - 3 * u ^ 2) * c ^ 2
  have hQd : HasDerivAt (fun s => Q11_m (uc_u s y) (uc_c s y)) (Qu * du + Qc * dc) x := by
    unfold Q11_m
    have h_p0 : HasDerivAt (fun s => -4 + 19 * uc_u s y + 32 * (uc_u s y) ^ 2 +
        14 * (uc_u s y) ^ 3 + 2 * (uc_u s y) ^ 4)
        ((19 + 64 * u + 42 * u ^ 2 + 8 * u ^ 3) * du) x :=
      (((((hasDerivAt_const x (-4 : ℝ)).add (hud.const_mul 19)).add
        ((hud.pow 2).const_mul 32)).add ((hud.pow 3).const_mul 14)).add ((hud.pow 4).const_mul 2)).congr_deriv
        (by simp; ring)
    have h_p1 : HasDerivAt (fun s => (12 - 3 * uc_u s y - 13 * (uc_u s y) ^ 2 -
        4 * (uc_u s y) ^ 3) * uc_c s y)
        ((-3 - 26 * u - 12 * u ^ 2) * du * c + (12 - 3 * u - 13 * u ^ 2 - 4 * u ^ 3) * dc) x := by
      have ha : HasDerivAt (fun s => 12 - 3 * uc_u s y - 13 * (uc_u s y) ^ 2 - 4 * (uc_u s y) ^ 3)
          ((-3 - 26 * u - 12 * u ^ 2) * du) x :=
        ((((hasDerivAt_const x (12 : ℝ)).sub (hud.const_mul 3)).sub
          ((hud.pow 2).const_mul 13)).sub ((hud.pow 3).const_mul 4)).congr_deriv (by simp; ring)
      exact (ha.mul hcd).congr_deriv (by ring)
    have h_p2 : HasDerivAt (fun s => (4 + uc_u s y) * (uc_c s y) ^ 2)
        (du * c ^ 2 + (4 + u) * (2 * c * dc)) x :=
      (((hasDerivAt_const x (4 : ℝ)).add hud).mul (hcd.pow 2)).congr_deriv (by simp; ring)
    have h_p3 : HasDerivAt (fun s => (-12 - 9 * uc_u s y - 3 * (uc_u s y) ^ 2) * (uc_c s y) ^ 3)
        ((-9 - 6 * u) * du * c ^ 3 + (-12 - 9 * u - 3 * u ^ 2) * (3 * c ^ 2 * dc)) x := by
      have ha : HasDerivAt (fun s => -12 - 9 * uc_u s y - 3 * (uc_u s y) ^ 2)
          ((-9 - 6 * u) * du) x :=
        (((hasDerivAt_const x (-12 : ℝ)).sub (hud.const_mul 9)).sub ((hud.pow 2).const_mul 3)).congr_deriv
          (by simp; ring)
      exact (ha.mul (hcd.pow 3)).congr_deriv (by simp; ring)
    exact (((h_p0.add h_p1).add h_p2).add h_p3).congr_deriv (by simp only [Qu, Qc]; ring)
  have hwt3d : HasDerivAt (fun s => uc_w (uc_u s y) (uc_c s y) * (uc_t (uc_u s y) (uc_c s y)) ^ 3)
      ((7 / 4 : ℝ) * t0 ^ 3 * ((4 + 2 * u) * du + 2 * dc)) x :=
    (hwd.mul (ht0d.pow 3)).congr_deriv (by
      have hsqw : Real.sqrt w = t0 ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg w)).symm
      have hne2 : t0 ≠ 0 := ht0.ne'
      have ht4 : w = t0 ^ 4 := (uc_t_pow4 hu hc.1).symm
      change ((4 + 2 * u) * du + 2 * dc) * t0 ^ 3 +
        w * ((3 : ℕ) * t0 ^ (3 - 1) * (((4 + 2 * u) * du + 2 * dc) / (4 * Real.sqrt w * t0))) = _
      norm_num
      rw [hsqw, ht4]
      field_simp [hne2]
      ring)
  have hden_d : HasDerivAt
      (fun s => 2 * (2 + uc_u s y - 2 * uc_c s y) * uc_w (uc_u s y) (uc_c s y) * (uc_t (uc_u s y) (uc_c s y)) ^ 3)
      (2 * ((du - 2 * dc) * w * t0 ^ 3 + Lm * ((7 / 4 : ℝ) * t0 ^ 3 * ((4 + 2 * u) * du + 2 * dc)))) x := by
    have hfun : (fun s => 2 * (2 + uc_u s y - 2 * uc_c s y) * uc_w (uc_u s y) (uc_c s y) * (uc_t (uc_u s y) (uc_c s y)) ^ 3) =
        fun s => 2 * ((2 + uc_u s y - 2 * uc_c s y) * (uc_w (uc_u s y) (uc_c s y) * (uc_t (uc_u s y) (uc_c s y)) ^ 3)) := by
      ext s; ring
    rw [hfun]
    exact ((hLmd.mul hwt3d).const_mul 2).congr_deriv (by ring)
  have hnum_d : HasDerivAt (fun s => Real.sqrt (4 + uc_u s y) * Q11_m (uc_u s y) (uc_c s y))
      ((du / (2 * Real.sqrt (4 + u))) * Q11_m u c + Real.sqrt (4 + u) * (Qu * du + Qc * dc)) x :=
    hs4d.mul hQd
  have hden_pos : 0 < 2 * Lm * w * t0 ^ 3 := by positivity
  have hfull := (hasDerivAt_const x (1 : ℝ)).add (hnum_d.div hden_d hden_pos.ne')
  have hcongr : (fun s => uX_xy s y) = fun s => uX_uc (uc_u s y) (uc_c s y) := by
    ext s; exact uX_xy_eq_uc s hy
  rw [hcongr]
  refine ⟨_, ?_, hfull⟩
  set scale := 2 * x / (r1 x y * r2 x y)
  have hscale_pos : 0 < scale := div_pos (by linarith) hP
  have hD : 0 < D_Q_poly u c := D_Q_poly_pos hu hc.1.le hc_neg.le
  have hR : R_ux_poly u c < 0 := R_ux_poly_neg hu hc.1.le hc_neg.le
  have hH_pos : 0 < 4 * (4 + u) * Lm * w * D_Q_poly u c + Q11_m u c * R_ux_poly u c := by
    have h1 : 0 < 4 * (4 + u) * Lm * w * D_Q_poly u c := by positivity
    nlinarith
  have hs4sq : (Real.sqrt (4 + u)) ^ 2 = 4 + u := Real.sq_sqrt (by linarith)
  have hfactor : 0 + (((du / (2 * Real.sqrt (4 + u)) * Q11_m u c +
        Real.sqrt (4 + u) * (Qu * du + Qc * dc)) * (2 * Lm * w * t0 ^ 3) -
      Real.sqrt (4 + u) * Q11_m u c *
        (2 * ((du - 2 * dc) * w * t0 ^ 3 + Lm * (7 / 4 * t0 ^ 3 * ((4 + 2 * u) * du + 2 * dc))))) /
      (2 * Lm * w * t0 ^ 3) ^ 2) =
      scale * (4 * (4 + u) * Lm * w * D_Q_poly u c + Q11_m u c * R_ux_poly u c) /
      (8 * Real.sqrt (4 + u) * Lm ^ 2 * w ^ 2 * t0 ^ 3) := by
    have hs4ne := hs4.ne'; have hLmne := hLm.ne'; have hwne := hw.ne'; have ht0ne := ht0.ne'
    have hdu_eq : du = scale * (2 - c * (2 + u)) := hdu_rel
    have hdc_eq : dc = scale * (1 - c ^ 2) := hdc_rel
    rw [hdu_eq, hdc_eq]
    field_simp [hs4ne, hLmne, hwne, ht0ne]
    rw [hs4sq]
    unfold D_Q_poly R_ux_poly Q11_m
    simp only [Qu, Qc, Lm, w, uc_w]
    ring
  rw [hfactor]
  positivity

/- Concluding lemmas of Section 4: axis root `y₀`, unique positive root `x_*(y)`, and `M` strict monotonicity -/

lemma uX_xy_neg_x (x : ℝ) {y : ℝ} (hy : 0 < y) : uX_xy (-x) y = uX_xy x y := by
  rw [uX_xy_eq_uc (-x) hy, uX_xy_eq_uc x hy, uc_u_neg_x, uc_c_neg_x]

lemma uX_xy_continuousOn_x {y : ℝ} (hy : 0 < y) : Continuous (fun x => uX_xy x y) := by
  have h1 : Continuous (fun x => r1 x y) := by
    unfold r1; fun_prop
  have h2 : Continuous (fun x => r2 x y) := by
    unfold r2; fun_prop
  have hFx : Continuous (fun x => Fx x y) := by
    unfold Fx
    exact ((continuous_id.add continuous_const).div (h1.pow 3) fun x => pow_ne_zero 3 (r1_pos x hy).ne').add
      ((continuous_id.sub continuous_const).div (h2.pow 3) fun x => pow_ne_zero 3 (r2_pos x hy).ne')
  have hFy : Continuous (fun x => Fy x y) := by
    have : (fun x => Fy x y) = fun x => y / (r1 x y) ^ 3 + y / (r2 x y) ^ 3 := by ext x; exact Fy_eq x y
    rw [this]
    exact (continuous_const.div (h1.pow 3) fun x => pow_ne_zero 3 (r1_pos x hy).ne').add
      (continuous_const.div (h2.pow 3) fun x => pow_ne_zero 3 (r2_pos x hy).ne')
  have hFsq : Continuous (fun x => Fsq x y) := by
    unfold Fsq; exact (hFx.pow 2).add (hFy.pow 2)
  have hFq : Continuous (fun x => Fq x y) := by
    unfold Fq Fn; exact hFsq.sqrt.sqrt
  have hFxx : Continuous (fun x => Fxx x y) := by
    unfold Fxx
    exact (((h1.pow 2).sub (continuous_const.mul ((continuous_id.add continuous_const).pow 2))).div
        (h1.pow 5) fun x => pow_ne_zero 5 (r1_pos x hy).ne').add
      (((h2.pow 2).sub (continuous_const.mul ((continuous_id.sub continuous_const).pow 2))).div
        (h2.pow 5) fun x => pow_ne_zero 5 (r2_pos x hy).ne')
  have hFxy : Continuous (fun x => Fxy x y) := by
    unfold Fxy Fxy0
    exact continuous_const.mul
      (((continuous_const.mul (continuous_id.add continuous_const)).div
          (h1.pow 5) fun x => pow_ne_zero 5 (r1_pos x hy).ne').add
        ((continuous_const.mul (continuous_id.sub continuous_const)).div
          (h2.pow 5) fun x => pow_ne_zero 5 (r2_pos x hy).ne'))
  unfold uX_xy
  exact continuous_const.add
    (((hFxx.mul hFsq).sub ((continuous_const.mul hFx).mul ((hFx.mul hFxx).add (hFy.mul hFxy)))).div
      (hFq.pow 7) fun x => pow_ne_zero 7 (Fq_pos x hy).ne')

lemma uX_xy_pos_of_ge_one {x y : ℝ} (hx : 1 ≤ x) (hy : 0 < y) : 0 < uX_xy x y := by
  rw [uX_xy_eq_uc x hy]
  have hc0 : 0 ≤ uc_c x y := by
    unfold uc_c; exact div_nonneg (by nlinarith) (mul_pos (r1_pos x hy) (r2_pos x hy)).le
  exact uX_uc_pos_of_c_nonneg (uc_u_nonneg x hy) hc0 (uc_c_bounds x hy).2

/-- General 1D lemma: if `g` is continuous on `[a, ∞)` and `g'(x) > 0` whenever `x > a` and `g(x) ≤ 0`,
    then `g(a) ≥ 0 → ∀ x > a, g(x) > 0`. -/
lemma pos_of_nonneg_of_deriv_pos_on_nonpos {g : ℝ → ℝ} {a : ℝ}
    (hcont : ContinuousOn g (Set.Ici a))
    (hderiv : ∀ x, a < x → g x ≤ 0 → ∃ d, 0 < d ∧ HasDerivAt g d x)
    (ha : 0 ≤ g a) : ∀ x, a < x → 0 < g x := by
  intro x hax
  by_contra hxle
  push Not at hxle
  have hcompact : IsCompact (Set.Icc a x) := isCompact_Icc
  have hne : (Set.Icc a x).Nonempty := ⟨a, le_rfl, hax.le⟩
  obtain ⟨m, hmIcc, hm_min⟩ := hcompact.exists_isMinOn hne (hcont.mono Set.Icc_subset_Ici_self)
  by_cases hma : m = a
  · have hgx0 : g x = 0 := by
      have hmin_x : g m ≤ g x := hm_min ⟨hax.le, le_rfl⟩
      rw [hma] at hmin_x; linarith
    obtain ⟨d, hd, hg'⟩ := hderiv x hax (by linarith)
    have hlt : ∃ t ∈ Set.Ioo a x, g t < g x := by
      have h1 := hg'.tendsto_slope_zero_left
      have h2 := h1.eventually (Ioi_mem_nhds hd)
      have h3 : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Iio 0), a - x < h :=
        nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith))
      obtain ⟨h, ⟨hslope, hh_gt⟩, hh_neg⟩ := ((h2.and h3).and self_mem_nhdsWithin).exists
      refine ⟨x + h, ⟨by linarith, by linarith⟩, ?_⟩
      change 0 < h⁻¹ • (g (x + h) - g x) at hslope
      rw [smul_eq_mul] at hslope
      have hneg : h < 0 := hh_neg
      have hmul := mul_neg_of_pos_of_neg hslope hneg
      rw [show h⁻¹ * (g (x + h) - g x) * h = g (x + h) - g x by field_simp [hneg.ne]] at hmul
      linarith
    obtain ⟨t, htIoo, hgt⟩ := hlt
    have hmin_t : g m ≤ g t := hm_min ⟨htIoo.1.le, htIoo.2.le⟩
    rw [hma] at hmin_t; linarith
  · have hmgt : a < m := lt_of_le_of_ne hmIcc.1 (Ne.symm hma)
    have hgm_le : g m ≤ 0 := le_trans (hm_min ⟨hax.le, le_rfl⟩) hxle
    obtain ⟨d, hd, hg'⟩ := hderiv m hmgt hgm_le
    have h1 := hg'.tendsto_slope_zero_left
    have h2 := h1.eventually (Ioi_mem_nhds hd)
    have h3 : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Iio 0), a - m < h :=
      nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith))
    obtain ⟨h, ⟨hslope, hh_gt⟩, hh_neg⟩ := ((h2.and h3).and self_mem_nhdsWithin).exists
    change 0 < h⁻¹ • (g (m + h) - g m) at hslope
    rw [smul_eq_mul] at hslope
    have hneg : h < 0 := hh_neg
    have hlt : g (m + h) < g m := by
      have hmul := mul_neg_of_pos_of_neg hslope hneg
      rw [show h⁻¹ * (g (m + h) - g m) * h = g (m + h) - g m by field_simp [hneg.ne]] at hmul
      linarith
    have hmem : m + h ∈ Set.Icc a x := ⟨by linarith, by linarith [hmIcc.2]⟩
    have hmin_mh : g m ≤ g (m + h) := hm_min hmem
    linarith

lemma uX_axis_eq {y : ℝ} (hy : 0 < y) :
    uX_xy 0 y = 1 - (1 - 3 * uc_c 0 y) / (uc_t 0 (uc_c 0 y)) ^ 3 := by
  rw [uX_xy_eq_uc 0 hy]
  have hu0 : uc_u 0 y = 0 := (uc_u_eq_zero_iff 0 hy).mpr rfl
  rw [hu0]
  have hc := uc_c_bounds 0 hy
  have ht := uc_t_pos le_rfl hc.1
  have hw_eq : uc_w 0 (uc_c 0 y) = 2 * (1 + uc_c 0 y) := by unfold uc_w; ring
  have h1mc : 1 - uc_c 0 y ≠ 0 := by linarith [hc.2]
  have h1pc : 1 + uc_c 0 y ≠ 0 := by linarith [hc.1]
  unfold uX_uc Q11_m
  rw [show Real.sqrt (4 + 0) = 2 by norm_num, hw_eq]
  rw [show (2 : ℝ) + 0 - 2 * uc_c 0 y = 2 * (1 - uc_c 0 y) by ring]
  field_simp [h1mc, h1pc, ht.ne']
  ring

lemma uc_c_axis_eq {y : ℝ} (hy : 0 < y) : uc_c 0 y = (y ^ 2 - 1) / (y ^ 2 + 1) := by
  unfold uc_c
  have h1 : r1 0 y = Real.sqrt (1 + y ^ 2) := by unfold r1; congr 1; ring
  have h2 : r2 0 y = Real.sqrt (1 + y ^ 2) := by unfold r2; congr 1; ring
  rw [h1, h2, Real.mul_self_sqrt (by positivity)]; ring

lemma exists_unique_y0 :
    ∃ y₀ : ℝ, 1 / 2 < y₀ ∧ y₀ < 1 ∧ uX_xy 0 y₀ = 0 ∧
      (∀ y, 0 < y → y < y₀ → uX_xy 0 y < 0) ∧
      (∀ y, y₀ < y → 0 < uX_xy 0 y) := by
  have hmono : ∀ {y₁ y₂ : ℝ}, 0 < y₁ → y₁ < y₂ → uX_xy 0 y₁ ≤ 0 → uX_xy 0 y₁ < uX_xy 0 y₂ := by
    intro y₁ y₂ hy₁ hlt hle
    have hy₂ : 0 < y₂ := by linarith
    have hc1 := uc_c_bounds 0 hy₁; have hc2 := uc_c_bounds 0 hy₂
    have hclt : uc_c 0 y₁ < uc_c 0 y₂ := by
      rw [uc_c_axis_eq hy₁, uc_c_axis_eq hy₂, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have ht1 : 0 < uc_t 0 (uc_c 0 y₁) := uc_t_pos le_rfl hc1.1
    have ht2 : 0 < uc_t 0 (uc_c 0 y₂) := uc_t_pos le_rfl hc2.1
    have htlt : uc_t 0 (uc_c 0 y₁) < uc_t 0 (uc_c 0 y₂) := by
      unfold uc_t uc_w
      exact Real.sqrt_lt_sqrt (Real.sqrt_nonneg _)
        (Real.sqrt_lt_sqrt (by linarith [hc1.1]) (by linarith))
    have hc1_le : 1 - 3 * uc_c 0 y₁ > 0 := by
      rw [uX_axis_eq hy₁] at hle
      have : (uc_t 0 (uc_c 0 y₁)) ^ 3 ≤ 1 - 3 * uc_c 0 y₁ := by
        rwa [sub_nonpos, le_div_iff₀ (pow_pos ht1 3), one_mul] at hle
      have : 0 < (uc_t 0 (uc_c 0 y₁)) ^ 3 := pow_pos ht1 3
      linarith
    rw [uX_axis_eq hy₁, uX_axis_eq hy₂]
    have hnum_lt : 1 - 3 * uc_c 0 y₂ < 1 - 3 * uc_c 0 y₁ := by linarith
    have hpow_lt : (uc_t 0 (uc_c 0 y₁)) ^ 3 < (uc_t 0 (uc_c 0 y₂)) ^ 3 :=
      pow_lt_pow_left₀ htlt ht1.le (by norm_num)
    have hdiv_lt : (1 - 3 * uc_c 0 y₂) / (uc_t 0 (uc_c 0 y₂)) ^ 3 <
        (1 - 3 * uc_c 0 y₁) / (uc_t 0 (uc_c 0 y₁)) ^ 3 := by
      rw [div_lt_div_iff₀ (pow_pos ht2 3) (pow_pos ht1 3)]
      have ht1_3 : 0 < (uc_t 0 (uc_c 0 y₁)) ^ 3 := pow_pos ht1 3
      have ht2_3 : 0 < (uc_t 0 (uc_c 0 y₂)) ^ 3 := pow_pos ht2 3
      nlinarith
    linarith
  have h_half : uX_xy 0 (1 / 2) < 0 := by
    rw [uX_axis_eq (by norm_num), uc_c_axis_eq (by norm_num)]
    have hc : ((1 / 2 : ℝ) ^ 2 - 1) / ((1 / 2 : ℝ) ^ 2 + 1) = -3 / 5 := by norm_num
    rw [hc]
    have ht_lt : uc_t 0 (-3 / 5) < 1 := by
      unfold uc_t uc_w
      have h1 : Real.sqrt (2 + 2 * (-3 / 5 : ℝ) + 4 * 0 + 0 ^ 2) < 1 := by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num
      rw [Real.sqrt_lt' (by norm_num)]; simpa using h1
    have ht_pos : 0 < uc_t 0 (-3 / 5) := uc_t_pos le_rfl (by norm_num)
    have ht3 : (uc_t 0 (-3 / 5)) ^ 3 < 1 := by nlinarith [pow_pos ht_pos 2]
    have : 1 < (1 - 3 * (-3 / 5 : ℝ)) / (uc_t 0 (-3 / 5)) ^ 3 := by
      rw [lt_div_iff₀ (pow_pos ht_pos 3)]; linarith
    linarith
  have h_one : 0 < uX_xy 0 1 := by
    rw [uX_axis_eq (by norm_num), uc_c_axis_eq (by norm_num)]
    have hc : ((1 : ℝ) ^ 2 - 1) / ((1 : ℝ) ^ 2 + 1) = 0 := by norm_num
    rw [hc]
    have ht_gt : 1 < uc_t 0 0 := by
      unfold uc_t uc_w
      have h1 : 1 < Real.sqrt (2 + 2 * (0 : ℝ) + 4 * 0 + 0 ^ 2) := by
        rw [Real.lt_sqrt (by norm_num)]; norm_num
      rw [Real.lt_sqrt (by norm_num)]; simpa using h1
    have ht3 : 1 < (uc_t 0 0) ^ 3 := by nlinarith [sq_nonneg (uc_t 0 0)]
    have : (1 - 3 * (0 : ℝ)) / (uc_t 0 0) ^ 3 < 1 := by
      rw [div_lt_iff₀ (by positivity)]; linarith
    linarith
  have hcont : ContinuousOn (fun y => uX_xy 0 y) (Set.Icc (1 / 2) 1) := by
    have h_eq : Set.EqOn (fun y => uX_xy 0 y)
        (fun y => 1 - (1 - 3 * ((y ^ 2 - 1) / (y ^ 2 + 1))) /
          (Real.sqrt (Real.sqrt (2 + 2 * ((y ^ 2 - 1) / (y ^ 2 + 1))))) ^ 3)
        (Set.Icc (1 / 2) 1) := by
      intro y hy
      dsimp only
      rw [uX_axis_eq (by linarith [hy.1]), uc_c_axis_eq (by linarith [hy.1])]
      unfold uc_t uc_w; simp
    have hc_cont : ContinuousOn (fun y : ℝ => (y ^ 2 - 1) / (y ^ 2 + 1)) (Set.Icc (1 / 2) 1) :=
      ((continuous_pow 2).sub continuous_const).continuousOn.div
        ((continuous_pow 2).add continuous_const).continuousOn (fun y _ => by positivity)
    have hden_cont : ContinuousOn
        (fun y : ℝ => (Real.sqrt (Real.sqrt (2 + 2 * ((y ^ 2 - 1) / (y ^ 2 + 1))))) ^ 3)
        (Set.Icc (1 / 2) 1) :=
      (((continuousOn_const.add (continuousOn_const.mul hc_cont)).sqrt).sqrt).pow 3
    have hcont2 : ContinuousOn
        (fun y => 1 - (1 - 3 * ((y ^ 2 - 1) / (y ^ 2 + 1))) /
          (Real.sqrt (Real.sqrt (2 + 2 * ((y ^ 2 - 1) / (y ^ 2 + 1))))) ^ 3)
        (Set.Icc (1 / 2) 1) := by
      refine continuousOn_const.sub ((continuousOn_const.sub (continuousOn_const.mul hc_cont)).div hden_cont ?_)
      intro y hy
      have hpos : 0 < 2 + 2 * ((y ^ 2 - 1) / (y ^ 2 + 1)) := by
        have : 2 + 2 * ((y ^ 2 - 1) / (y ^ 2 + 1)) = 4 * y ^ 2 / (y ^ 2 + 1) := by
          field_simp; ring
        rw [this]; have : 0 < y := by linarith [hy.1]
        positivity
      exact pow_ne_zero 3 (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hpos)).ne'
    exact hcont2.congr h_eq
  have hmem : (0 : ℝ) ∈ Set.Icc (uX_xy 0 (1 / 2)) (uX_xy 0 1) := ⟨h_half.le, h_one.le⟩
  obtain ⟨y₀, hy₀Icc, hy₀eq⟩ := intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1) hcont hmem
  dsimp only at hy₀eq
  have hy₀_gt : 1 / 2 < y₀ := lt_of_le_of_ne hy₀Icc.1 (by rintro rfl; linarith)
  have hy₀_lt : y₀ < 1 := lt_of_le_of_ne hy₀Icc.2 (by rintro rfl; linarith)
  refine ⟨y₀, hy₀_gt, hy₀_lt, hy₀eq, ?_, ?_⟩
  · intro y hy hlt
    by_contra hge; push Not at hge
    have hclt : uc_c 0 y < uc_c 0 y₀ := by
      rw [uc_c_axis_eq hy, uc_c_axis_eq (by linarith), div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hc0_neg : uc_c 0 y₀ < 0 := by
      rw [uc_c_axis_eq (by linarith)]; exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)
    have hcy_neg : uc_c 0 y < 0 := by linarith
    have ht1 : 0 < uc_t 0 (uc_c 0 y) := uc_t_pos le_rfl (uc_c_bounds 0 hy).1
    have ht2 : 0 < uc_t 0 (uc_c 0 y₀) := uc_t_pos le_rfl (uc_c_bounds 0 (by linarith)).1
    have htlt : uc_t 0 (uc_c 0 y) < uc_t 0 (uc_c 0 y₀) := by
      unfold uc_t uc_w
      exact Real.sqrt_lt_sqrt (Real.sqrt_nonneg _)
        (Real.sqrt_lt_sqrt (by linarith [(uc_c_bounds 0 hy).1]) (by linarith))
    have hdiv : (1 - 3 * uc_c 0 y₀) / (uc_t 0 (uc_c 0 y₀)) ^ 3 <
        (1 - 3 * uc_c 0 y) / (uc_t 0 (uc_c 0 y)) ^ 3 := by
      rw [div_lt_div_iff₀ (pow_pos ht2 3) (pow_pos ht1 3)]
      have hpow := pow_lt_pow_left₀ htlt ht1.le (by norm_num : 3 ≠ 0)
      have ht1_3 : 0 < (uc_t 0 (uc_c 0 y)) ^ 3 := pow_pos ht1 3
      have ht2_3 : 0 < (uc_t 0 (uc_c 0 y₀)) ^ 3 := pow_pos ht2 3
      nlinarith
    rw [uX_axis_eq hy] at hge; rw [uX_axis_eq (by linarith)] at hy₀eq
    linarith
  · intro y hgt
    have := hmono (by linarith) hgt hy₀eq.le
    linarith

lemma horizontal_slice_ge_y0 {y : ℝ} (hy : 0 < y) (h0 : 0 ≤ uX_xy 0 y) :
    (∀ x, x ≠ 0 → 0 < uX_xy x y) ∧ StrictMono (fun x => phiU x y) := by
  have hpos_pos : ∀ x, 0 < x → 0 < uX_xy x y :=
    pos_of_nonneg_of_deriv_pos_on_nonpos (uX_xy_continuousOn_x hy).continuousOn
      (fun x hx hle => hasDerivAt_uX_x_pos hx hy hle) h0
  have hpos_ne : ∀ x, x ≠ 0 → 0 < uX_xy x y := by
    intro x hx
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · rw [← uX_xy_neg_x x hy]; exact hpos_pos (-x) (by linarith)
    · exact hpos_pos x hgt
  refine ⟨hpos_ne, ?_⟩
  have hmono_nonneg : StrictMonoOn (fun x => phiU x y) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x _ => (hasDerivAt_x_of_lin2 (hasFDerivAt_phiU x hy)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hasDerivAt_x_of_lin2 (hasFDerivAt_phiU x hy)).deriv]
      exact hpos_pos x hx
  have hmono_nonpos : StrictMonoOn (fun x => phiU x y) (Set.Iic 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Iic 0)
    · exact fun x _ => (hasDerivAt_x_of_lin2 (hasFDerivAt_phiU x hy)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Iic] at hx
      rw [(hasDerivAt_x_of_lin2 (hasFDerivAt_phiU x hy)).deriv]
      exact hpos_ne x (ne_of_lt hx)
  intro a b hab
  by_cases ha : a ≤ 0
  · by_cases hb : b ≤ 0
    · exact hmono_nonpos ha hb hab
    · push Not at hb
      rcases eq_or_lt_of_le ha with rfl | hlt
      · exact hmono_nonneg (Set.mem_Ici.mpr le_rfl) hb.le hab
      · exact lt_trans (hmono_nonpos ha (Set.mem_Iic.mpr le_rfl) hlt) (hmono_nonneg (Set.mem_Ici.mpr le_rfl) hb.le hb)
  · push Not at ha
    exact hmono_nonneg ha.le (show 0 ≤ b by linarith) hab

lemma horizontal_slice_lt_y0 {y : ℝ} (hy : 0 < y) (h0 : uX_xy 0 y < 0) :
    ∃ xstar : ℝ, 0 < xstar ∧ xstar < 1 ∧ uX_xy xstar y = 0 ∧
      (∀ x, -xstar < x → x < xstar → uX_xy x y < 0) ∧
      (∀ x, xstar < x → 0 < uX_xy x y) ∧
      (∀ x, x < -xstar → 0 < uX_xy x y) ∧
      StrictMonoOn (fun x => phiU x y) (Set.Iic (-xstar)) ∧
      StrictAntiOn (fun x => phiU x y) (Set.Icc (-xstar) xstar) ∧
      StrictMonoOn (fun x => phiU x y) (Set.Ici xstar) := by
  have h1 : 0 < uX_xy 1 y := uX_xy_pos_of_ge_one le_rfl hy
  have hcont := uX_xy_continuousOn_x hy
  obtain ⟨xstar, hxIcc, hxEq⟩ :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn ⟨h0.le, h1.le⟩
  have hx_pos : 0 < xstar := lt_of_le_of_ne hxIcc.1 (by rintro rfl; linarith)
  have hx_lt : xstar < 1 := lt_of_le_of_ne hxIcc.2 (by rintro rfl; linarith)
  have hgt : ∀ x, xstar < x → 0 < uX_xy x y :=
    pos_of_nonneg_of_deriv_pos_on_nonpos hcont.continuousOn
      (fun x hx hle => hasDerivAt_uX_x_pos (by linarith) hy hle) hxEq.ge
  have hlt : ∀ x, x < -xstar → 0 < uX_xy x y := by
    intro x hx; rw [← uX_xy_neg_x x hy]; exact hgt (-x) (by linarith)
  have hmid : ∀ x, -xstar < x → x < xstar → uX_xy x y < 0 := by
    intro x hx1 hx2
    by_contra hge; push Not at hge
    have hge_abs : 0 ≤ uX_xy |x| y := by
      rcases le_total 0 x with h | h
      · rwa [abs_of_nonneg h]
      · rw [abs_of_nonpos h, uX_xy_neg_x x hy]; exact hge
    have habs_lt : |x| < xstar := abs_lt.mpr ⟨hx1, hx2⟩
    have hgt_abs : 0 < uX_xy xstar y :=
      pos_of_nonneg_of_deriv_pos_on_nonpos hcont.continuousOn
        (fun t ht hle => hasDerivAt_uX_x_pos (by linarith [abs_nonneg x]) hy hle) hge_abs xstar habs_lt
    linarith
  refine ⟨xstar, hx_pos, hx_lt, hxEq, hmid, hgt, hlt, ?_, ?_, ?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Iic (-xstar))
    · exact fun x _ => (hasDerivAt_x_of_lin2 (hasFDerivAt_phiU x hy)).continuousAt.continuousWithinAt
    · intro x hx; rw [interior_Iic] at hx
      rw [(hasDerivAt_x_of_lin2 (hasFDerivAt_phiU x hy)).deriv]; exact hlt x hx
  · apply strictAntiOn_of_deriv_neg (convex_Icc (-xstar) xstar)
    · exact fun x _ => (hasDerivAt_x_of_lin2 (hasFDerivAt_phiU x hy)).continuousAt.continuousWithinAt
    · intro x hx; rw [interior_Icc] at hx
      rw [(hasDerivAt_x_of_lin2 (hasFDerivAt_phiU x hy)).deriv]; exact hmid x hx.1 hx.2
  · apply strictMonoOn_of_deriv_pos (convex_Ici xstar)
    · exact fun x _ => (hasDerivAt_x_of_lin2 (hasFDerivAt_phiU x hy)).continuousAt.continuousWithinAt
    · intro x hx; rw [interior_Ici] at hx
      rw [(hasDerivAt_x_of_lin2 (hasFDerivAt_phiU x hy)).deriv]; exact hgt x hx

/-- On `x < 0`, `y ↦ phiU x y` is strictly decreasing; hence the fold value `M(y) = phiU (-x_*(y)) y`
    is strictly decreasing on `(0, y₀)` with zero envelope-theorem differentiation! -/
lemma phiU_strictAnti_y_of_neg {x : ℝ} (hx : x < 0) :
    StrictAntiOn (fun y => phiU x y) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact fun y hy => (hasDerivAt_y_of_lin2 (hasFDerivAt_phiU x hy)).continuousAt.continuousWithinAt
  · intro y hy; rw [interior_Ioi] at hy
    rw [(hasDerivAt_y_of_lin2 (hasFDerivAt_phiU x hy)).deriv]
    exact uY_xy_neg_of_neg hx hy

lemma fold_val_strictAnti {y₁ y₂ x₁ x₂ : ℝ} (hy₁ : 0 < y₁) (hlt : y₁ < y₂)
    (_hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hL₁ : StrictMonoOn (fun x => phiU x y₁) (Set.Iic (-x₁)))
    (hM₁ : StrictAntiOn (fun x => phiU x y₁) (Set.Icc (-x₁) x₁)) :
    phiU (-x₂) y₂ < phiU (-x₁) y₁ := by
  have h1 : phiU (-x₂) y₂ < phiU (-x₂) y₁ :=
    phiU_strictAnti_y_of_neg (by linarith) hy₁ (show 0 < y₂ by linarith) hlt
  have h2 : phiU (-x₂) y₁ ≤ phiU (-x₁) y₁ := by
    by_cases h : -x₂ ≤ -x₁
    · exact hL₁.monotoneOn h (Set.mem_Iic.mpr le_rfl) h
    · push Not at h
      exact hM₁.antitoneOn ⟨le_rfl, by linarith⟩ ⟨h.le, by linarith⟩ h.le
  linarith

/- Section 5a: Verified Integer-Interval Engine (Iv) & Partial Derivatives of F_det, G_uc -/

def isqrtStep (n x : ℕ) : ℕ :=
  if x = 0 then 0 else (x + n / x) / 2

def isqrtApprox (n : ℕ) : ℕ :=
  let x0 :=
    if n < 256 then 16
    else if n < 65536 then 256
    else if n < 16777216 then 4096
    else if n < 4294967296 then 65536
    else if n < 1099511627776 then 1048576
    else n
  let x1 := isqrtStep n x0
  let x2 := isqrtStep n x1
  let x3 := isqrtStep n x2
  let x4 := isqrtStep n x3
  let x5 := isqrtStep n x4
  let x6 := isqrtStep n x5
  let x7 := isqrtStep n x6
  isqrtStep n x7

def isqrtLo (n : ℕ) : ℕ :=
  let r := isqrtApprox n
  if r * r ≤ n then r
  else if (r - 1) * (r - 1) ≤ n then r - 1
  else 0

def isqrtHi (n : ℕ) : ℕ :=
  let r := isqrtApprox n
  if n ≤ r * r then r
  else if n ≤ (r + 1) * (r + 1) then r + 1
  else n + 1

lemma isqrtLo_sq_le (n : ℕ) : isqrtLo n * isqrtLo n ≤ n := by
  unfold isqrtLo; dsimp only
  split_ifs with h1 h2
  · exact h1
  · exact h2
  · simp

lemma le_isqrtHi_sq (n : ℕ) : n ≤ isqrtHi n * isqrtHi n := by
  unfold isqrtHi; dsimp only
  split_ifs with h1 h2
  · exact h1
  · exact h2
  · nlinarith

structure Iv where
  lo : ℤ
  hi : ℤ
  ok : Bool := true

def Iv.Mem (x : ℝ) (I : Iv) : Prop :=
  I.ok = true → (I.lo : ℝ) ≤ x * 65536 ∧ x * 65536 ≤ (I.hi : ℝ)

def ivInt (k : ℤ) : Iv := ⟨k * 65536, k * 65536, true⟩

def ivRat (p : ℤ) (q : ℕ) : Iv :=
  ⟨(p * 65536) / (q : ℤ), (p * 65536 + (q : ℤ) - 1) / (q : ℤ), decide (0 < q)⟩

def ivAdd (I J : Iv) : Iv := ⟨I.lo + J.lo, I.hi + J.hi, I.ok && J.ok⟩
def ivSub (I J : Iv) : Iv := ⟨I.lo - J.hi, I.hi - J.lo, I.ok && J.ok⟩
def ivNeg (I : Iv) : Iv := ⟨-I.hi, -I.lo, I.ok⟩
def ivSmul (k : ℤ) (I : Iv) : Iv :=
  if 0 ≤ k then ⟨k * I.lo, k * I.hi, I.ok⟩ else ⟨k * I.hi, k * I.lo, I.ok⟩

def ivMul (I J : Iv) : Iv :=
  let p1 := I.lo * J.lo
  let p2 := I.lo * J.hi
  let p3 := I.hi * J.lo
  let p4 := I.hi * J.hi
  let mn := min (min p1 p2) (min p3 p4)
  let mx := max (max p1 p2) (max p3 p4)
  ⟨mn / 65536, (mx + 65535) / 65536, I.ok && J.ok⟩

def ivSq (I : Iv) : Iv :=
  if 0 ≤ I.lo then
    ⟨(I.lo * I.lo) / 65536, (I.hi * I.hi + 65535) / 65536, I.ok⟩
  else if I.hi ≤ 0 then
    ⟨(I.hi * I.hi) / 65536, (I.lo * I.lo + 65535) / 65536, I.ok⟩
  else
    let m := max (-I.lo) I.hi
    ⟨0, (m * m + 65535) / 65536, I.ok⟩

def ivDiv (I J : Iv) : Iv :=
  if 0 < J.lo then
    ⟨if 0 ≤ I.lo then (I.lo * 65536) / J.hi else (I.lo * 65536) / J.lo,
     if 0 ≤ I.hi then (I.hi * 65536 + J.lo - 1) / J.lo else (I.hi * 65536 + J.hi - 1) / J.hi,
     I.ok && J.ok⟩
  else ⟨0, 0, false⟩

def ivSqrt (I : Iv) : Iv :=
  if 0 ≤ I.lo then
    ⟨(isqrtLo (I.lo.toNat * 65536) : ℤ), (isqrtHi (I.hi.toNat * 65536) : ℤ), I.ok⟩
  else ⟨0, 0, false⟩

def Iv.isPos (I : Iv) : Bool := I.ok && decide (0 < I.lo)
def Iv.isNeg (I : Iv) : Bool := I.ok && decide (I.hi < 0)

def gridIvs (A B : ℤ) (n : ℕ) : List Iv :=
  (List.range n).map fun i =>
    let lo := (A * ((n - i : ℕ) : ℤ) + B * (i : ℤ)) / (n : ℤ)
    let hi := (A * ((n - i - 1 : ℕ) : ℤ) + B * ((i + 1 : ℕ) : ℤ) + (n : ℤ) - 1) / (n : ℤ)
    ⟨lo, hi, decide (0 < n)⟩

lemma int_ediv_mul_le {a b : ℤ} (hb : 0 < b) : (a / b) * b ≤ a := by
  have h1 := Int.ediv_mul_add_emod a b
  have h2 := Int.emod_nonneg a hb.ne'
  linarith

lemma int_le_ceil_ediv_mul {a b : ℤ} (hb : 0 < b) : a ≤ ((a + b - 1) / b) * b := by
  have h1 := Int.ediv_mul_add_emod (a + b - 1) b
  have h2 := Int.emod_lt_of_pos (a + b - 1) hb
  linarith

lemma int_ediv_mul_le_real {a b : ℤ} (hb : 0 < b) : ((a / b : ℤ) : ℝ) * (b : ℝ) ≤ (a : ℝ) := by
  exact_mod_cast int_ediv_mul_le hb

lemma int_le_ceil_ediv_mul_real {a b : ℤ} (hb : 0 < b) :
    (a : ℝ) ≤ (((a + b - 1) / b : ℤ) : ℝ) * (b : ℝ) := by
  exact_mod_cast int_le_ceil_ediv_mul hb

lemma Iv.Mem.of_bounds {I : Iv} {x : ℝ} (h1 : (I.lo : ℝ) ≤ x * 65536)
    (h2 : x * 65536 ≤ (I.hi : ℝ)) : I.Mem x := fun _ => ⟨h1, h2⟩

lemma Iv.Mem.pos_of_isPos {I : Iv} {x : ℝ} (h : I.Mem x) (hp : I.isPos = true) : 0 < x := by
  unfold Iv.isPos at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  have ⟨h1, _⟩ := h hp.1
  have hlo : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hp.2
  linarith

lemma Iv.Mem.neg_of_isNeg {I : Iv} {x : ℝ} (h : I.Mem x) (hn : I.isNeg = true) : x < 0 := by
  unfold Iv.isNeg at hn
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
  have ⟨_, h2⟩ := h hn.1
  have hhi : (I.hi : ℝ) < 0 := by exact_mod_cast hn.2
  linarith

lemma ivMem_int (k : ℤ) : (ivInt k).Mem (k : ℝ) := by
  intro _; unfold ivInt; dsimp only; push_cast; constructor <;> linarith

lemma ivMem_rat (p : ℤ) (q : ℕ) : (ivRat p q).Mem ((p : ℝ) / (q : ℝ)) := by
  intro hok; unfold ivRat at hok ⊢; simp only [decide_eq_true_eq] at hok
  have hqz : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hok
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hok
  have h1 := int_ediv_mul_le_real (a := p * 65536) hqz
  have h2 := int_le_ceil_ediv_mul_real (a := p * 65536) hqz
  push_cast at h1 h2
  dsimp only
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ hqr]; linarith
  · rw [div_mul_eq_mul_div, div_le_iff₀ hqr]; linarith

lemma Iv.Mem.add {I J : Iv} {x y : ℝ} (hI : I.Mem x) (hJ : J.Mem y) :
    (ivAdd I J).Mem (x + y) := by
  intro hok; unfold ivAdd at hok ⊢; simp only [Bool.and_eq_true] at hok
  have ⟨hx1, hx2⟩ := hI hok.1; have ⟨hy1, hy2⟩ := hJ hok.2
  dsimp only; push_cast; constructor <;> linarith

lemma Iv.Mem.sub {I J : Iv} {x y : ℝ} (hI : I.Mem x) (hJ : J.Mem y) :
    (ivSub I J).Mem (x - y) := by
  intro hok; unfold ivSub at hok ⊢; simp only [Bool.and_eq_true] at hok
  have ⟨hx1, hx2⟩ := hI hok.1; have ⟨hy1, hy2⟩ := hJ hok.2
  dsimp only; push_cast; constructor <;> linarith

lemma Iv.Mem.neg {I : Iv} {x : ℝ} (hI : I.Mem x) : (ivNeg I).Mem (-x) := by
  intro hok; unfold ivNeg at hok ⊢
  have ⟨hx1, hx2⟩ := hI hok
  dsimp only; push_cast; constructor <;> linarith

lemma Iv.Mem.smul (k : ℤ) {I : Iv} {x : ℝ} (hI : I.Mem x) :
    (ivSmul k I).Mem ((k : ℝ) * x) := by
  intro hok; unfold ivSmul at hok ⊢
  split_ifs at hok ⊢ with hk
  · have ⟨hx1, hx2⟩ := hI hok
    have hkr : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    dsimp only; push_cast; constructor <;> nlinarith
  · have ⟨hx1, hx2⟩ := hI hok
    have hkr : (k : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hk)
    dsimp only; push_cast; constructor <;> nlinarith

lemma mul_mem_corners {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  constructor
  · rcases le_total 0 y with hy0 | hy0
    · rcases le_total 0 a with ha0 | ha0
      · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (by nlinarith))
      · exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (by nlinarith))
    · rcases le_total 0 b with hb0 | hb0
      · exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (by nlinarith))
      · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (by nlinarith))
  · rcases le_total 0 y with hy0 | hy0
    · rcases le_total 0 b with hb0 | hb0
      · exact le_trans (by nlinarith) (le_trans (le_max_right _ _) (le_max_right _ _))
      · exact le_trans (by nlinarith) (le_trans (le_max_left _ _) (le_max_right _ _))
    · rcases le_total 0 a with ha0 | ha0
      · exact le_trans (by nlinarith) (le_trans (le_max_right _ _) (le_max_left _ _))
      · exact le_trans (by nlinarith) (le_trans (le_max_left _ _) (le_max_left _ _))

lemma Iv.Mem.mul {I J : Iv} {x y : ℝ} (hI : I.Mem x) (hJ : J.Mem y) :
    (ivMul I J).Mem (x * y) := by
  intro hok; unfold ivMul at hok ⊢; dsimp only at hok ⊢
  simp only [Bool.and_eq_true] at hok
  have hx := hI hok.1; have hy := hJ hok.2
  have hc := mul_mem_corners hx hy
  have hS : (0 : ℤ) < 65536 := by norm_num
  set mn := min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))
  set mx := max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))
  have hmn : (mn : ℝ) ≤ (x * 65536) * (y * 65536) := by
    have : (mn : ℝ) = min (min ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi))
        (min ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi)) := by
      simp only [mn, Int.cast_min, Int.cast_mul]
    rw [this]; exact hc.1
  have hmx : (x * 65536) * (y * 65536) ≤ (mx : ℝ) := by
    have : (mx : ℝ) = max (max ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi))
        (max ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi)) := by
      simp only [mx, Int.cast_max, Int.cast_mul]
    rw [this]; exact hc.2
  have h1 := int_ediv_mul_le_real (a := mn) hS
  have h2 := int_le_ceil_ediv_mul_real (a := mx) hS
  have h2' : (mx : ℝ) ≤ (((mx + 65535) / 65536 : ℤ) : ℝ) * 65536 := by
    have : mx + 65536 - 1 = mx + 65535 := by ring
    rw [this] at h2; exact_mod_cast h2
  push_cast at h1
  have hS_pos : (0 : ℝ) < 65536 := by norm_num
  constructor
  · have : (((mn / 65536 : ℤ) : ℝ) * 65536) ≤ (x * y * 65536) * 65536 := by linarith
    linarith
  · have : (x * y * 65536) * 65536 ≤ (((mx + 65535) / 65536 : ℤ) : ℝ) * 65536 := by linarith
    linarith

lemma Iv.Mem.sq {I : Iv} {x : ℝ} (hI : I.Mem x) : (ivSq I).Mem (x ^ 2) := by
  intro hok; unfold ivSq at hok ⊢
  have hS : (0 : ℤ) < 65536 := by norm_num
  split_ifs at hok ⊢ with hlo hhi
  · have ⟨hx1, hx2⟩ := hI hok
    have hloR : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hlo
    have h1 := int_ediv_mul_le_real (a := I.lo * I.lo) hS
    have h2 := int_le_ceil_ediv_mul_real (a := I.hi * I.hi) hS
    have h2' : ((I.hi * I.hi : ℤ) : ℝ) ≤ (((I.hi * I.hi + 65535) / 65536 : ℤ) : ℝ) * 65536 := by
      have : I.hi * I.hi + 65536 - 1 = I.hi * I.hi + 65535 := by ring
      rw [this] at h2; exact_mod_cast h2
    have hsq1 : (I.lo : ℝ) * (I.lo : ℝ) ≤ (x * 65536) * (x * 65536) :=
      mul_le_mul hx1 hx1 hloR (by linarith)
    have hsq2 : (x * 65536) * (x * 65536) ≤ (I.hi : ℝ) * (I.hi : ℝ) :=
      mul_le_mul hx2 hx2 (by linarith) (by linarith)
    dsimp only; push_cast at h1 h2' ⊢
    constructor <;> linarith [show (x * 65536) * (x * 65536) = (x ^ 2 * 65536) * 65536 by ring]
  · have ⟨hx1, hx2⟩ := hI hok
    have hhiR : (I.hi : ℝ) ≤ 0 := by exact_mod_cast hhi
    have h1 := int_ediv_mul_le_real (a := I.hi * I.hi) hS
    have h2 := int_le_ceil_ediv_mul_real (a := I.lo * I.lo) hS
    have h2' : ((I.lo * I.lo : ℤ) : ℝ) ≤ (((I.lo * I.lo + 65535) / 65536 : ℤ) : ℝ) * 65536 := by
      have : I.lo * I.lo + 65536 - 1 = I.lo * I.lo + 65535 := by ring
      rw [this] at h2; exact_mod_cast h2
    have hsq1 : (-(I.hi : ℝ)) * (-(I.hi : ℝ)) ≤ (-(x * 65536)) * (-(x * 65536)) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have hsq2 : (-(x * 65536)) * (-(x * 65536)) ≤ (-(I.lo : ℝ)) * (-(I.lo : ℝ)) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    dsimp only; push_cast at h1 h2' ⊢
    constructor <;> linarith [show (-(x * 65536)) * (-(x * 65536)) = (x ^ 2 * 65536) * 65536 by ring,
      show (-(I.hi : ℝ)) * (-(I.hi : ℝ)) = (I.hi : ℝ) * (I.hi : ℝ) by ring,
      show (-(I.lo : ℝ)) * (-(I.lo : ℝ)) = (I.lo : ℝ) * (I.lo : ℝ) by ring]
  · have ⟨hx1, hx2⟩ := hI hok
    set m := max (-I.lo) I.hi
    have hmR : (m : ℝ) = max (-(I.lo : ℝ)) (I.hi : ℝ) := by simp [m]
    have hxm1 : -(m : ℝ) ≤ x * 65536 := by
      rw [hmR]; linarith [le_max_left (-(I.lo : ℝ)) (I.hi : ℝ)]
    have hxm2 : x * 65536 ≤ (m : ℝ) := by
      rw [hmR]; linarith [le_max_right (-(I.lo : ℝ)) (I.hi : ℝ)]
    have habs : |x * 65536| ≤ (m : ℝ) := abs_le.mpr ⟨hxm1, hxm2⟩
    have hsq2 : (x * 65536) * (x * 65536) ≤ (m : ℝ) * (m : ℝ) := by
      have := mul_le_mul habs habs (abs_nonneg _) (le_trans (abs_nonneg _) habs)
      rwa [abs_mul_abs_self] at this
    have h2 := int_le_ceil_ediv_mul_real (a := m * m) hS
    have h2' : ((m * m : ℤ) : ℝ) ≤ (((m * m + 65535) / 65536 : ℤ) : ℝ) * 65536 := by
      have : m * m + 65536 - 1 = m * m + 65535 := by ring
      rw [this] at h2; exact_mod_cast h2
    dsimp only; push_cast at h2' ⊢
    constructor
    · positivity
    · linarith [show (x * 65536) * (x * 65536) = (x ^ 2 * 65536) * 65536 by ring]

lemma Iv.Mem.div {I J : Iv} {x y : ℝ} (hI : I.Mem x) (hJ : J.Mem y) :
    (ivDiv I J).Mem (x / y) := by
  intro hok; unfold ivDiv at hok ⊢
  by_cases hJlo : 0 < J.lo
  · simp only [hJlo, ↓reduceIte, Bool.and_eq_true] at hok ⊢
    have ⟨hx1, hx2⟩ := hI hok.1; have ⟨hy1, hy2⟩ := hJ hok.2
    have hJloR : (0 : ℝ) < (J.lo : ℝ) := by exact_mod_cast hJlo
    have hJhi : 0 < J.hi := by
      have : (J.lo : ℝ) ≤ (J.hi : ℝ) := by linarith
      have : J.lo ≤ J.hi := by exact_mod_cast this
      omega
    have hypos : 0 < y := by linarith
    have hys : 0 < y * 65536 := by positivity
    have hmul : (x / y * 65536) * (y * 65536) = (x * 65536) * 65536 := by
      field_simp [hypos.ne']
    constructor
    · split_ifs with hIlo
      · have hq0 : 0 ≤ (I.lo * 65536) / J.hi := Int.ediv_nonneg (by omega) hJhi.le
        have hq0R : (0 : ℝ) ≤ (((I.lo * 65536) / J.hi : ℤ) : ℝ) := by exact_mod_cast hq0
        have h1 := int_ediv_mul_le_real (a := I.lo * 65536) hJhi
        push_cast at h1
        have hstep : (((I.lo * 65536) / J.hi : ℤ) : ℝ) * (y * 65536) ≤
            (((I.lo * 65536) / J.hi : ℤ) : ℝ) * (J.hi : ℝ) :=
          mul_le_mul_of_nonneg_left hy2 hq0R
        exact le_of_mul_le_mul_right (by linarith) hys
      · have hIlo_lt : I.lo < 0 := lt_of_not_ge hIlo
        have h1z := int_ediv_mul_le (a := I.lo * 65536) hJlo
        have hq0 : (I.lo * 65536) / J.lo ≤ 0 := by
          by_contra hpos; push Not at hpos
          have : 1 * J.lo ≤ ((I.lo * 65536) / J.lo) * J.lo :=
            mul_le_mul_of_nonneg_right (by omega) hJlo.le
          omega
        have hq0R : (((I.lo * 65536) / J.lo : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hq0
        have h1 : (((I.lo * 65536) / J.lo : ℤ) : ℝ) * (J.lo : ℝ) ≤ (I.lo : ℝ) * 65536 := by
          exact_mod_cast h1z
        have hstep : (((I.lo * 65536) / J.lo : ℤ) : ℝ) * (y * 65536) ≤
            (((I.lo * 65536) / J.lo : ℤ) : ℝ) * (J.lo : ℝ) :=
          mul_le_mul_of_nonpos_left hy1 hq0R
        exact le_of_mul_le_mul_right (by linarith) hys
    · split_ifs with hIhi
      · have hq0 : 0 ≤ (I.hi * 65536 + J.lo - 1) / J.lo := Int.ediv_nonneg (by omega) hJlo.le
        have hq0R : (0 : ℝ) ≤ (((I.hi * 65536 + J.lo - 1) / J.lo : ℤ) : ℝ) := by exact_mod_cast hq0
        have h2 := int_le_ceil_ediv_mul_real (a := I.hi * 65536) hJlo
        push_cast at h2
        have hstep : (((I.hi * 65536 + J.lo - 1) / J.lo : ℤ) : ℝ) * (J.lo : ℝ) ≤
            (((I.hi * 65536 + J.lo - 1) / J.lo : ℤ) : ℝ) * (y * 65536) :=
          mul_le_mul_of_nonneg_left hy1 hq0R
        exact le_of_mul_le_mul_right (by linarith) hys
      · have hIhi_lt : I.hi < 0 := lt_of_not_ge hIhi
        have h1z := int_ediv_mul_le (a := I.hi * 65536 + J.hi - 1) hJhi
        have hq0 : (I.hi * 65536 + J.hi - 1) / J.hi ≤ 0 := by
          by_contra hpos; push Not at hpos
          have : 1 * J.hi ≤ ((I.hi * 65536 + J.hi - 1) / J.hi) * J.hi :=
            mul_le_mul_of_nonneg_right (by omega) hJhi.le
          omega
        have hq0R : (((I.hi * 65536 + J.hi - 1) / J.hi : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hq0
        have h2 := int_le_ceil_ediv_mul_real (a := I.hi * 65536) hJhi
        push_cast at h2
        have hstep : (((I.hi * 65536 + J.hi - 1) / J.hi : ℤ) : ℝ) * (J.hi : ℝ) ≤
            (((I.hi * 65536 + J.hi - 1) / J.hi : ℤ) : ℝ) * (y * 65536) :=
          mul_le_mul_of_nonpos_left hy2 hq0R
        exact le_of_mul_le_mul_right (by linarith) hys
  · simp only [hJlo, ↓reduceIte] at hok; exact absurd hok (by decide)

lemma Iv.Mem.sqrt {I : Iv} {x : ℝ} (hI : I.Mem x) : (ivSqrt I).Mem (Real.sqrt x) := by
  intro hok; unfold ivSqrt at hok ⊢
  by_cases hlo : 0 ≤ I.lo
  · simp only [hlo, ↓reduceIte] at hok ⊢
    have ⟨hx1, hx2⟩ := hI hok
    have hloR : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hlo
    have hhi0 : 0 ≤ I.hi := by
      have : (0 : ℝ) ≤ (I.hi : ℝ) := by linarith
      exact_mod_cast this
    have hx0 : 0 ≤ x := by linarith
    have hlo_eq : ((I.lo.toNat : ℤ) : ℝ) = (I.lo : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hlo
    have hhi_eq : ((I.hi.toNat : ℤ) : ℝ) = (I.hi : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hhi0
    have hsq : (Real.sqrt x * 65536) ^ 2 = x * 65536 * 65536 := by
      rw [mul_pow, Real.sq_sqrt hx0]; ring
    have h1n := isqrtLo_sq_le (I.lo.toNat * 65536)
    have h2n := le_isqrtHi_sq (I.hi.toNat * 65536)
    have h1R : ((isqrtLo (I.lo.toNat * 65536) : ℕ) : ℝ) ^ 2 ≤ (I.lo : ℝ) * 65536 := by
      have h1' : ((isqrtLo (I.lo.toNat * 65536) : ℕ) : ℝ) * (isqrtLo (I.lo.toNat * 65536) : ℕ) ≤
          ((I.lo.toNat : ℕ) : ℝ) * 65536 := by exact_mod_cast h1n
      have hlo_nat : ((I.lo.toNat : ℕ) : ℝ) = (I.lo : ℝ) := by exact_mod_cast hlo_eq
      rw [hlo_nat] at h1'; rw [pow_two]; exact h1'
    have h2R : (I.hi : ℝ) * 65536 ≤ ((isqrtHi (I.hi.toNat * 65536) : ℕ) : ℝ) ^ 2 := by
      have h2' : ((I.hi.toNat : ℕ) : ℝ) * 65536 ≤
          ((isqrtHi (I.hi.toNat * 65536) : ℕ) : ℝ) * (isqrtHi (I.hi.toNat * 65536) : ℕ) := by
        exact_mod_cast h2n
      have hhi_nat : ((I.hi.toNat : ℕ) : ℝ) = (I.hi : ℝ) := by exact_mod_cast hhi_eq
      rw [hhi_nat] at h2'; rw [pow_two]; exact h2'
    push_cast
    have hsq0 : 0 ≤ Real.sqrt x * 65536 := by positivity
    have hH0 : (0 : ℝ) ≤ (isqrtHi (I.hi.toNat * 65536) : ℕ) := Nat.cast_nonneg _
    constructor
    · exact le_of_sq_le_sq (by linarith) hsq0
    · exact le_of_sq_le_sq (by linarith) hH0
  · simp only [hlo, ↓reduceIte] at hok; exact absurd hok (by decide)

lemma mem_gridIvs {A B : ℤ} {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hlo : (A : ℝ) ≤ x * 65536) (hhi : x * 65536 ≤ (B : ℝ)) :
    ∃ I ∈ gridIvs A B n, I.Mem x := by
  set t := x * 65536
  have hnz : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  suffices h : ∃ i < n,
      (A : ℝ) * ((n - i : ℕ) : ℝ) + (B : ℝ) * (i : ℝ) ≤ t * (n : ℝ) ∧
      t * (n : ℝ) ≤ (A : ℝ) * ((n - i - 1 : ℕ) : ℝ) + (B : ℝ) * ((i + 1 : ℕ) : ℝ) by
    obtain ⟨i, hi, h1, h2⟩ := h
    refine ⟨⟨(A * ((n - i : ℕ) : ℤ) + B * (i : ℤ)) / (n : ℤ),
             (A * ((n - i - 1 : ℕ) : ℤ) + B * ((i + 1 : ℕ) : ℤ) + (n : ℤ) - 1) / (n : ℤ),
             decide (0 < n)⟩, ?_, ?_⟩
    · unfold gridIvs; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
    · intro _; dsimp only
      have hl := int_ediv_mul_le_real (a := A * ((n - i : ℕ) : ℤ) + B * (i : ℤ)) hnz
      have hr := int_le_ceil_ediv_mul_real (a := A * ((n - i - 1 : ℕ) : ℤ) + B * ((i + 1 : ℕ) : ℤ)) hnz
      push_cast at h1 h2 hl hr ⊢
      constructor
      · exact le_of_mul_le_mul_right (by linarith) hnr
      · exact le_of_mul_le_mul_right (by linarith) hnr
  by_cases htB : t = (B : ℝ)
  · refine ⟨n - 1, Nat.sub_lt hn Nat.one_pos, ?_, ?_⟩
    · rw [htB, show n - (n - 1) = 1 by omega, Nat.cast_one, Nat.cast_sub hn, Nat.cast_one]
      nlinarith
    · rw [htB, show n - (n - 1) - 1 = 0 by omega, show n - 1 + 1 = n by omega]
      simp
  · have htlt : t < (B : ℝ) := lt_of_le_of_ne hhi htB
    have hAB : (0 : ℝ) < (B : ℝ) - (A : ℝ) := by linarith
    set q := (t - (A : ℝ)) / ((B : ℝ) - (A : ℝ)) * (n : ℝ)
    have hq0 : 0 ≤ q := by positivity
    have hqn : q < (n : ℝ) := by
      have : (t - (A : ℝ)) / ((B : ℝ) - (A : ℝ)) < 1 := (div_lt_one hAB).mpr (by linarith)
      nlinarith
    set i := Nat.floor q
    have hi_lt : i < n := by
      exact_mod_cast (lt_of_le_of_lt (Nat.floor_le hq0) hqn)
    have hi_le : (i : ℝ) ≤ q := Nat.floor_le hq0
    have hq_lt : q < (i : ℝ) + 1 := Nat.lt_floor_add_one q
    have hq_mul : q * ((B : ℝ) - (A : ℝ)) = (t - (A : ℝ)) * (n : ℝ) := by
      simp only [q]; field_simp [hAB.ne']
    have hsub1 : ((n - i : ℕ) : ℝ) = (n : ℝ) - (i : ℝ) := Nat.cast_sub hi_lt.le
    have hsub2 : ((n - i - 1 : ℕ) : ℝ) = (n : ℝ) - (i : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n - i), hsub1]; norm_num
    refine ⟨i, hi_lt, ?_, ?_⟩
    · rw [hsub1]; nlinarith
    · rw [hsub2]; push_cast; nlinarith

lemma all_grid1 {A B : ℤ} {n : ℕ} (hn : 0 < n) (check : Iv → Bool)
    (hcheck : (gridIvs A B n).all check = true)
    {x : ℝ} (hlo : (A : ℝ) ≤ x * 65536) (hhi : x * 65536 ≤ (B : ℝ)) :
    ∃ I, I.Mem x ∧ check I = true := by
  obtain ⟨I, hmem, hx⟩ := mem_gridIvs hn hlo hhi
  exact ⟨I, hx, List.all_eq_true.mp hcheck I hmem⟩

lemma all_grid2 {Au Bu Ac Bc : ℤ} {nu nc : ℕ} (hnu : 0 < nu) (hnc : 0 < nc)
    (check : Iv → Iv → Bool)
    (hcheck : (gridIvs Au Bu nu).all (fun Iu => (gridIvs Ac Bc nc).all (fun Ic => check Iu Ic)) = true)
    {u c : ℝ} (hu1 : (Au : ℝ) ≤ u * 65536) (hu2 : u * 65536 ≤ (Bu : ℝ))
    (hc1 : (Ac : ℝ) ≤ c * 65536) (hc2 : c * 65536 ≤ (Bc : ℝ)) :
    ∃ Iu Ic, Iu.Mem u ∧ Ic.Mem c ∧ check Iu Ic = true := by
  obtain ⟨Iu, hmu, hu⟩ := mem_gridIvs hnu hu1 hu2
  obtain ⟨Ic, hmc, hc⟩ := mem_gridIvs hnc hc1 hc2
  have h1 := List.all_eq_true.mp hcheck Iu hmu
  exact ⟨Iu, Ic, hu, hc, List.all_eq_true.mp h1 Ic hmc⟩

/- Exact partial derivatives of F_det and G_uc -/

def T0_u (u c : ℝ) : ℝ := 24 + 8 * c + u * (40 + 12 * u)
def T0_c (u c : ℝ) : ℝ := 18 * c + 8 + 8 * u
def D0_u (u : ℝ) : ℝ := 18 + u * (24 + 6 * u)
def D0_c (c : ℝ) : ℝ := 18 * c

noncomputable def F_u (u c : ℝ) : ℝ :=
  7 * (2 + u) * (uc_t u c) ^ 3 +
  (T0_m u c + 2 * (4 + u) * T0_u u c) / (2 * Real.sqrt (4 + u)) +
  ((2 + u) * D0_m u c + 2 * uc_w u c * D0_u u) / (2 * (uc_t u c) ^ 3)

noncomputable def F_c (u c : ℝ) : ℝ :=
  7 * (uc_t u c) ^ 3 + Real.sqrt (4 + u) * T0_c u c +
  (D0_m u c + 2 * uc_w u c * D0_c c) / (2 * (uc_t u c) ^ 3)

noncomputable def F_uu (u c : ℝ) : ℝ :=
  (7 * (uc_t u c) ^ 3 + 21 * (2 + u) ^ 2 / (2 * uc_t u c)) +
  (-T0_m u c / (4 * (4 + u) * Real.sqrt (4 + u)) + T0_u u c / Real.sqrt (4 + u) +
    Real.sqrt (4 + u) * (40 + 24 * u)) +
  ((2 * uc_w u c - 3 * (2 + u) ^ 2) / (4 * uc_w u c * (uc_t u c) ^ 3) * D0_m u c +
    2 * ((2 + u) / (2 * (uc_t u c) ^ 3)) * D0_u u + uc_t u c * (24 + 12 * u))

noncomputable def F_uc (u c : ℝ) : ℝ :=
  21 * (2 + u) / (2 * uc_t u c) +
  (T0_c u c / (2 * Real.sqrt (4 + u)) + 8 * Real.sqrt (4 + u)) +
  (-(3 * (2 + u)) / (4 * uc_w u c * (uc_t u c) ^ 3) * D0_m u c +
    (2 + u) / (2 * (uc_t u c) ^ 3) * D0_c c + 1 / (2 * (uc_t u c) ^ 3) * D0_u u)

noncomputable def F_cc (u c : ℝ) : ℝ :=
  21 / (2 * uc_t u c) + 18 * Real.sqrt (4 + u) +
  (-3 * D0_m u c + 4 * uc_w u c * D0_c c + 72 * (uc_w u c) ^ 2) / (4 * uc_w u c * (uc_t u c) ^ 3)

noncomputable def hor_F (u c : ℝ) : ℝ := (2 - c * (2 + u)) * F_u u c + (1 - c ^ 2) * F_c u c

def G_A (u c : ℝ) : ℝ := 2 * (1 - c * (3 + u))
noncomputable def G_B (u c : ℝ) : ℝ := G_A u c * (1 / (uc_t u c) ^ 3) - Real.sqrt (4 + u)
noncomputable def G_Bu (u c : ℝ) : ℝ :=
  (-2 * c) * (1 / (uc_t u c) ^ 3) + G_A u c * (-(3 * (2 + u)) / (2 * uc_w u c * (uc_t u c) ^ 3)) -
  1 / (2 * Real.sqrt (4 + u))
noncomputable def G_Bc (u c : ℝ) : ℝ :=
  (-2 * (3 + u)) * (1 / (uc_t u c) ^ 3) + G_A u c * (-3 / (2 * uc_w u c * (uc_t u c) ^ 3))
noncomputable def G_Buu (u c : ℝ) : ℝ :=
  2 * ((-2 * c) * (-(3 * (2 + u)) / (2 * uc_w u c * (uc_t u c) ^ 3))) +
  G_A u c * ((-6 * uc_w u c + 21 * (2 + u) ^ 2) / (4 * (uc_w u c) ^ 2 * (uc_t u c) ^ 3)) +
  1 / (4 * (4 + u) * Real.sqrt (4 + u))
noncomputable def G_Buc (u c : ℝ) : ℝ :=
  -2 * (1 / (uc_t u c) ^ 3) +
  (-2 * c) * (-3 / (2 * uc_w u c * (uc_t u c) ^ 3)) +
  (-2 * (3 + u)) * (-(3 * (2 + u)) / (2 * uc_w u c * (uc_t u c) ^ 3)) +
  G_A u c * (21 * (2 + u) / (4 * (uc_w u c) ^ 2 * (uc_t u c) ^ 3))
noncomputable def G_Bcc (u c : ℝ) : ℝ :=
  2 * ((-2 * (3 + u)) * (-3 / (2 * uc_w u c * (uc_t u c) ^ 3))) +
  G_A u c * (21 / (4 * (uc_w u c) ^ 2 * (uc_t u c) ^ 3))

noncomputable def G_u (u c : ℝ) : ℝ := (G_Bu u c - G_uc u c) / (2 + u - 2 * c)
noncomputable def G_c (u c : ℝ) : ℝ := (G_Bc u c + 2 * G_uc u c) / (2 + u - 2 * c)
noncomputable def G_uu (u c : ℝ) : ℝ := (G_Buu u c - 2 * G_u u c) / (2 + u - 2 * c)
noncomputable def G_uc2 (u c : ℝ) : ℝ := (G_Buc u c + 2 * G_u u c - G_c u c) / (2 + u - 2 * c)
noncomputable def G_cc (u c : ℝ) : ℝ := (G_Bcc u c + 4 * G_c u c) / (2 + u - 2 * c)

noncomputable def N1_uc (u c : ℝ) : ℝ :=
  -(F_c u c * G_uc u c) + 2 * u * (G_c u c * F_u u c - G_u u c * F_c u c)

noncomputable def PeakD2_uc (u c : ℝ) : ℝ :=
  let up := (-F_c u c) / F_u u c
  let upp := (-(F_uu u c * up ^ 2 + 2 * (F_uc u c * up) + F_cc u c)) / F_u u c
  let up_u := up / u
  let term1 := (upp / u - up_u ^ 2) / 2
  let g_dd := G_uu u c * up ^ 2 + 2 * (G_uc2 u c * up) + G_cc u c + G_u u c * upp
  let g_d := G_u u c * up + G_c u c
  let term2 := g_dd / G_uc u c - (g_d / G_uc u c) ^ 2
  term1 + term2

lemma hasFDerivAt_const_mul_lin2 (k : ℝ) {f : ℝ × ℝ → ℝ} {fx fy : ℝ} {p : ℝ × ℝ}
    (hf : HasFDerivAt f (lin2 fx fy) p) :
    HasFDerivAt (fun q => k * f q) (lin2 (k * fx) (k * fy)) p :=
  (hf.const_mul k).congr_fderiv (by ext <;> simp [lin2])

lemma hasFDerivAt_uc_w (u c : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => uc_w p.1 p.2) (lin2 (4 + 2 * u) 2) (u, c) := by
  unfold uc_w
  have hx := hasFDerivAt_fst_lin2 (u, c)
  have hy := hasFDerivAt_snd_lin2 (u, c)
  exact (hasFDerivAt_add_lin2
    (hasFDerivAt_add_lin2
      (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 2 (u, c)) (hasFDerivAt_const_mul_lin2 2 hy))
      (hasFDerivAt_const_mul_lin2 4 hx))
    (hasFDerivAt_pow_lin2 2 hx)).congr_fderiv (by
      ext <;> simp [lin2])

lemma hasFDerivAt_uc_t {u c : ℝ} (hw : 0 < uc_w u c) :
    HasFDerivAt (fun p : ℝ × ℝ => uc_t p.1 p.2)
      (lin2 ((2 + u) / (2 * (uc_t u c) ^ 3)) (1 / (2 * (uc_t u c) ^ 3))) (u, c) := by
  unfold uc_t
  have hsw : 0 < Real.sqrt (uc_w u c) := Real.sqrt_pos.mpr hw
  have ht : 0 < Real.sqrt (Real.sqrt (uc_w u c)) := Real.sqrt_pos.mpr hsw
  have hsq : Real.sqrt (Real.sqrt (uc_w u c)) ^ 2 = Real.sqrt (uc_w u c) := Real.sq_sqrt hsw.le
  have h1 := hasFDerivAt_sqrt_lin2 (hasFDerivAt_uc_w u c) hw.ne'
  have h2 := hasFDerivAt_sqrt_lin2 h1 hsw.ne'
  exact h2.congr_fderiv (by
    ext <;> simp [lin2] <;>
    · generalize Real.sqrt (Real.sqrt (uc_w u c)) = t at ht hsq ⊢
      field_simp [hsw.ne', ht.ne']; rw [← hsq]; try ring)

lemma hasFDerivAt_uc_t3 {u c : ℝ} (hw : 0 < uc_w u c) :
    HasFDerivAt (fun p : ℝ × ℝ => (uc_t p.1 p.2) ^ 3)
      (lin2 (3 * (2 + u) / (2 * uc_t u c)) (3 / (2 * uc_t u c))) (u, c) := by
  have ht : 0 < uc_t u c := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hw)
  exact (hasFDerivAt_pow_lin2 3 (hasFDerivAt_uc_t hw)).congr_fderiv (by
    ext <;> simp [lin2] <;> field_simp [ht.ne'])

lemma hasFDerivAt_inv_t3 {u c : ℝ} (hw : 0 < uc_w u c) :
    HasFDerivAt (fun p : ℝ × ℝ => 1 / (uc_t p.1 p.2) ^ 3)
      (lin2 (-(3 * (2 + u)) / (2 * uc_w u c * (uc_t u c) ^ 3))
            (-3 / (2 * uc_w u c * (uc_t u c) ^ 3))) (u, c) := by
  have ht : 0 < uc_t u c := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hw)
  have ht4 : (uc_t u c) ^ 4 = uc_w u c := by
    unfold uc_t
    calc (Real.sqrt (Real.sqrt (uc_w u c))) ^ 4
        = ((Real.sqrt (Real.sqrt (uc_w u c))) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (uc_w u c)) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = uc_w u c := Real.sq_sqrt hw.le
  exact (hasFDerivAt_div_lin2 (hasFDerivAt_const_lin2 1 (u, c)) (hasFDerivAt_uc_t3 hw)
    (pow_ne_zero 3 ht.ne')).congr_fderiv (by
      ext <;> simp [lin2] <;>
      · generalize uc_t u c = t at ht ht4 ⊢
        field_simp [hw.ne', ht.ne']; rw [← ht4])

lemma hasFDerivAt_s4u {u c : ℝ} (hu : -4 < u) :
    HasFDerivAt (fun p : ℝ × ℝ => Real.sqrt (4 + p.1))
      (lin2 (1 / (2 * Real.sqrt (4 + u))) 0) (u, c) := by
  have h1 := hasFDerivAt_sqrt_lin2
    (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 4 (u, c)) (hasFDerivAt_fst_lin2 (u, c)))
    (by dsimp; linarith)
  exact h1.congr_fderiv (by ext <;> simp [lin2])

lemma hasFDerivAt_T0 (u c : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => T0_m p.1 p.2) (lin2 (T0_u u c) (T0_c u c)) (u, c) := by
  unfold T0_m
  have hx := hasFDerivAt_fst_lin2 (u, c)
  have hy := hasFDerivAt_snd_lin2 (u, c)
  have h1 := hasFDerivAt_sub_lin2
    (hasFDerivAt_add_lin2 (hasFDerivAt_const_mul_lin2 9 (hasFDerivAt_pow_lin2 2 hy))
      (hasFDerivAt_const_mul_lin2 8 hy))
    (hasFDerivAt_const_lin2 1 (u, c))
  have h2 := hasFDerivAt_mul_lin2
    (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 24 (u, c)) (hasFDerivAt_const_mul_lin2 8 hy)) hx
  have h3 := hasFDerivAt_const_mul_lin2 20 (hasFDerivAt_pow_lin2 2 hx)
  have h4 := hasFDerivAt_const_mul_lin2 4 (hasFDerivAt_pow_lin2 3 hx)
  exact (hasFDerivAt_add_lin2 (hasFDerivAt_add_lin2 (hasFDerivAt_add_lin2 h1 h2) h3) h4).congr_fderiv (by
    unfold T0_u T0_c; ext <;> simp [lin2] <;> ring)

lemma hasFDerivAt_D0 (u c : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => D0_m p.1 p.2) (lin2 (D0_u u) (D0_c c)) (u, c) := by
  unfold D0_m
  have hx := hasFDerivAt_fst_lin2 (u, c)
  have hy := hasFDerivAt_snd_lin2 (u, c)
  have h1 := hasFDerivAt_sub_lin2 (hasFDerivAt_const_mul_lin2 9 (hasFDerivAt_pow_lin2 2 hy))
    (hasFDerivAt_const_lin2 1 (u, c))
  have h2 := hasFDerivAt_const_mul_lin2 18 hx
  have h3 := hasFDerivAt_const_mul_lin2 12 (hasFDerivAt_pow_lin2 2 hx)
  have h4 := hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_pow_lin2 3 hx)
  exact (hasFDerivAt_add_lin2 (hasFDerivAt_add_lin2 (hasFDerivAt_add_lin2 h1 h2) h3) h4).congr_fderiv (by
    unfold D0_u D0_c; ext <;> simp [lin2] <;> ring)

lemma hasFDerivAt_F_det {u c : ℝ} (hu : -4 < u) (hw : 0 < uc_w u c) :
    HasFDerivAt (fun p : ℝ × ℝ => F_det p.1 p.2) (lin2 (F_u u c) (F_c u c)) (u, c) := by
  have ht : 0 < uc_t u c := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hw)
  have hs : 0 < Real.sqrt (4 + u) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt (4 + u) ^ 2 = 4 + u := Real.sq_sqrt (by linarith)
  have ht4 : (uc_t u c) ^ 4 = uc_w u c := by
    unfold uc_t
    calc (Real.sqrt (Real.sqrt (uc_w u c))) ^ 4
        = ((Real.sqrt (Real.sqrt (uc_w u c))) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (uc_w u c)) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = uc_w u c := Real.sq_sqrt hw.le
  unfold F_det
  have h1 := hasFDerivAt_mul_lin2 (hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_uc_w u c)) (hasFDerivAt_uc_t3 hw)
  have h2 := hasFDerivAt_mul_lin2 (hasFDerivAt_s4u hu) (hasFDerivAt_T0 u c)
  have h3 := hasFDerivAt_mul_lin2 (hasFDerivAt_uc_t hw) (hasFDerivAt_D0 u c)
  exact (hasFDerivAt_add_lin2 (hasFDerivAt_add_lin2 h1 h2) h3).congr_fderiv (by
    unfold F_u F_c; ext <;> simp [lin2]
    · generalize uc_t u c = t at ht ht4 ⊢
      generalize Real.sqrt (4 + u) = s at hs hs2 ⊢
      field_simp [hs.ne', ht.ne']; rw [← ht4, ← hs2]; ring
    · generalize uc_t u c = t at ht ht4 ⊢
      field_simp [hs.ne', ht.ne']; rw [← ht4]; ring)

lemma hasFDerivAt_F_u {u c : ℝ} (hu : -4 < u) (hw : 0 < uc_w u c) :
    HasFDerivAt (fun p : ℝ × ℝ => F_u p.1 p.2) (lin2 (F_uu u c) (F_uc u c)) (u, c) := by
  have ht : 0 < uc_t u c := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hw)
  have hs : 0 < Real.sqrt (4 + u) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt (4 + u) ^ 2 = 4 + u := Real.sq_sqrt (by linarith)
  have ht4 : (uc_t u c) ^ 4 = uc_w u c := by
    unfold uc_t
    calc (Real.sqrt (Real.sqrt (uc_w u c))) ^ 4
        = ((Real.sqrt (Real.sqrt (uc_w u c))) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (uc_w u c)) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = uc_w u c := Real.sq_sqrt hw.le
  have hx := hasFDerivAt_fst_lin2 (u, c)
  have hy := hasFDerivAt_snd_lin2 (u, c)
  have hT0u : HasFDerivAt (fun p : ℝ × ℝ => T0_u p.1 p.2) (lin2 (40 + 24 * u) 8) (u, c) := by
    unfold T0_u
    exact (hasFDerivAt_add_lin2
      (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 24 (u, c)) (hasFDerivAt_const_mul_lin2 8 hy))
      (hasFDerivAt_mul_lin2 hx
        (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 40 (u, c)) (hasFDerivAt_const_mul_lin2 12 hx)))).congr_fderiv (by
          ext <;> simp [lin2]; ring)
  have hD0u : HasFDerivAt (fun p : ℝ × ℝ => D0_u p.1) (lin2 (24 + 12 * u) 0) (u, c) := by
    unfold D0_u
    exact (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 18 (u, c))
      (hasFDerivAt_mul_lin2 hx
        (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 24 (u, c)) (hasFDerivAt_const_mul_lin2 6 hx)))).congr_fderiv (by
          ext <;> simp [lin2]; ring)
  unfold F_u
  have h1 := hasFDerivAt_mul_lin2
    (hasFDerivAt_const_mul_lin2 7 (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 2 (u, c)) hx))
    (hasFDerivAt_uc_t3 hw)
  have h2num := hasFDerivAt_add_lin2 (hasFDerivAt_T0 u c)
    (hasFDerivAt_mul_lin2
      (hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 4 (u, c)) hx)) hT0u)
  have h2 := hasFDerivAt_div_lin2 h2num (hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_s4u hu)) (by positivity)
  have h3num := hasFDerivAt_add_lin2
    (hasFDerivAt_mul_lin2 (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 2 (u, c)) hx) (hasFDerivAt_D0 u c))
    (hasFDerivAt_mul_lin2 (hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_uc_w u c)) hD0u)
  have h3 := hasFDerivAt_div_lin2 h3num (hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_uc_t3 hw)) (by positivity)
  exact (hasFDerivAt_add_lin2 (hasFDerivAt_add_lin2 h1 h2) h3).congr_fderiv (by
    unfold F_uu F_uc
    ext <;> simp [lin2]
    · generalize uc_t u c = t at ht ht4 ⊢
      generalize Real.sqrt (4 + u) = s at hs hs2 ⊢
      field_simp [hs.ne', ht.ne', hw.ne', show (4 + u : ℝ) ≠ 0 by linarith]
      rw [← ht4, ← hs2]; ring
    · generalize uc_t u c = t at ht ht4 ⊢
      generalize Real.sqrt (4 + u) = s at hs hs2 ⊢
      field_simp [hs.ne', ht.ne', hw.ne']
      rw [← ht4, ← hs2]; ring)

lemma hasFDerivAt_F_c {u c : ℝ} (hu : -4 < u) (hw : 0 < uc_w u c) :
    HasFDerivAt (fun p : ℝ × ℝ => F_c p.1 p.2) (lin2 (F_uc u c) (F_cc u c)) (u, c) := by
  have ht : 0 < uc_t u c := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hw)
  have hs : 0 < Real.sqrt (4 + u) := Real.sqrt_pos.mpr (by linarith)
  have ht4 : (uc_t u c) ^ 4 = uc_w u c := by
    unfold uc_t
    calc (Real.sqrt (Real.sqrt (uc_w u c))) ^ 4
        = ((Real.sqrt (Real.sqrt (uc_w u c))) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (uc_w u c)) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = uc_w u c := Real.sq_sqrt hw.le
  have hx := hasFDerivAt_fst_lin2 (u, c)
  have hy := hasFDerivAt_snd_lin2 (u, c)
  have hT0c : HasFDerivAt (fun p : ℝ × ℝ => T0_c p.1 p.2) (lin2 8 18) (u, c) := by
    unfold T0_c
    exact (hasFDerivAt_add_lin2
      (hasFDerivAt_add_lin2 (hasFDerivAt_const_mul_lin2 18 hy) (hasFDerivAt_const_lin2 8 (u, c)))
      (hasFDerivAt_const_mul_lin2 8 hx)).congr_fderiv (by ext <;> simp [lin2])
  have hD0c : HasFDerivAt (fun p : ℝ × ℝ => D0_c p.2) (lin2 0 18) (u, c) := by
    unfold D0_c
    exact (hasFDerivAt_const_mul_lin2 18 hy).congr_fderiv (by ext <;> simp [lin2])
  unfold F_c
  have h1 := hasFDerivAt_const_mul_lin2 7 (hasFDerivAt_uc_t3 hw)
  have h2 := hasFDerivAt_mul_lin2 (hasFDerivAt_s4u hu) hT0c
  have h3num := hasFDerivAt_add_lin2 (hasFDerivAt_D0 u c)
    (hasFDerivAt_mul_lin2 (hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_uc_w u c)) hD0c)
  have h3 := hasFDerivAt_div_lin2 h3num (hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_uc_t3 hw)) (by positivity)
  exact (hasFDerivAt_add_lin2 (hasFDerivAt_add_lin2 h1 h2) h3).congr_fderiv (by
    unfold F_uc F_cc; ext <;> simp [lin2] <;>
    · generalize uc_t u c = t at ht ht4 ⊢
      field_simp [hs.ne', ht.ne', hw.ne']; rw [← ht4]; ring)

lemma hasFDerivAt_G_A (u c : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => G_A p.1 p.2) (lin2 (-2 * c) (-2 * (3 + u))) (u, c) := by
  unfold G_A
  have hx := hasFDerivAt_fst_lin2 (u, c)
  have hy := hasFDerivAt_snd_lin2 (u, c)
  exact (hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_sub_lin2 (hasFDerivAt_const_lin2 1 (u, c))
    (hasFDerivAt_mul_lin2 hy (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 3 (u, c)) hx)))).congr_fderiv (by
      ext <;> simp [lin2]; ring)

lemma hasFDerivAt_G_B {u c : ℝ} (hu : -4 < u) (hw : 0 < uc_w u c) :
    HasFDerivAt (fun p : ℝ × ℝ => G_B p.1 p.2) (lin2 (G_Bu u c) (G_Bc u c)) (u, c) := by
  unfold G_B
  exact (hasFDerivAt_sub_lin2
    (hasFDerivAt_mul_lin2 (hasFDerivAt_G_A u c) (hasFDerivAt_inv_t3 hw))
    (hasFDerivAt_s4u hu)).congr_fderiv (by
      unfold G_Bu G_Bc; ext <;> simp [lin2])

lemma G_uc_eq_G_B_div (u c : ℝ) : G_uc u c = G_B u c / (2 + u - 2 * c) := by
  unfold G_uc G_B G_A; ring

lemma hasFDerivAt_G_uc {u c : ℝ} (hu : -4 < u) (hw : 0 < uc_w u c) (hLm : 0 < 2 + u - 2 * c) :
    HasFDerivAt (fun p : ℝ × ℝ => G_uc p.1 p.2) (lin2 (G_u u c) (G_c u c)) (u, c) := by
  have hfun : (fun p : ℝ × ℝ => G_uc p.1 p.2) = fun p => G_B p.1 p.2 / (2 + p.1 - 2 * p.2) := by
    ext p; exact G_uc_eq_G_B_div p.1 p.2
  rw [hfun]
  have hLmd : HasFDerivAt (fun p : ℝ × ℝ => 2 + p.1 - 2 * p.2) (lin2 1 (-2)) (u, c) :=
    (hasFDerivAt_sub_lin2
      (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 2 (u, c)) (hasFDerivAt_fst_lin2 (u, c)))
      (hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_snd_lin2 (u, c)))).congr_fderiv (by ext <;> simp [lin2])
  exact (hasFDerivAt_div_lin2 (hasFDerivAt_G_B hu hw) hLmd hLm.ne').congr_fderiv (by
    unfold G_u G_c; rw [G_uc_eq_G_B_div]
    ext <;> simp [lin2] <;> field_simp [hLm.ne'])

lemma hasFDerivAt_G_Bu {u c : ℝ} (hu : -4 < u) (hw : 0 < uc_w u c) :
    HasFDerivAt (fun p : ℝ × ℝ => G_Bu p.1 p.2) (lin2 (G_Buu u c) (G_Buc u c)) (u, c) := by
  have ht : 0 < uc_t u c := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hw)
  have hs : 0 < Real.sqrt (4 + u) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt (4 + u) ^ 2 = 4 + u := Real.sq_sqrt (by linarith)
  have ht4 : (uc_t u c) ^ 4 = uc_w u c := by
    unfold uc_t
    calc (Real.sqrt (Real.sqrt (uc_w u c))) ^ 4
        = ((Real.sqrt (Real.sqrt (uc_w u c))) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (uc_w u c)) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = uc_w u c := Real.sq_sqrt hw.le
  have hx := hasFDerivAt_fst_lin2 (u, c)
  have hy := hasFDerivAt_snd_lin2 (u, c)
  have hwt3 := hasFDerivAt_mul_lin2 (hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_uc_w u c)) (hasFDerivAt_uc_t3 hw)
  have hneg3 : HasFDerivAt (fun p : ℝ × ℝ => -(3 * (2 + p.1))) (lin2 (-3) 0) (u, c) := by
    have hfun : (fun p : ℝ × ℝ => -(3 * (2 + p.1))) = fun p => (-3 : ℝ) * (2 + p.1) := by ext p; ring
    rw [hfun]
    exact (hasFDerivAt_const_mul_lin2 (-3)
      (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 2 (u, c)) hx)).congr_fderiv (by ext <;> simp [lin2])
  have hinv_u := hasFDerivAt_div_lin2 hneg3 hwt3 (by positivity)
  have h1 := hasFDerivAt_mul_lin2 (hasFDerivAt_const_mul_lin2 (-2) hy) (hasFDerivAt_inv_t3 hw)
  have h2 := hasFDerivAt_mul_lin2 (hasFDerivAt_G_A u c) hinv_u
  have h3 := hasFDerivAt_div_lin2 (hasFDerivAt_const_lin2 1 (u, c))
    (hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_s4u hu)) (by positivity)
  unfold G_Bu
  exact (hasFDerivAt_sub_lin2 (hasFDerivAt_add_lin2 h1 h2) h3).congr_fderiv (by
    unfold G_Buu G_Buc
    ext <;> simp [lin2]
    · generalize uc_t u c = t at ht ht4 ⊢
      generalize Real.sqrt (4 + u) = s at hs hs2 ⊢
      field_simp [hs.ne', ht.ne', hw.ne', show (4 + u : ℝ) ≠ 0 by linarith]
      rw [← ht4, ← hs2]; ring
    · generalize uc_t u c = t at ht ht4 ⊢
      field_simp [hs.ne', ht.ne', hw.ne']
      rw [← ht4]; ring)

lemma hasFDerivAt_G_Bc {u c : ℝ} (hw : 0 < uc_w u c) :
    HasFDerivAt (fun p : ℝ × ℝ => G_Bc p.1 p.2) (lin2 (G_Buc u c) (G_Bcc u c)) (u, c) := by
  have ht : 0 < uc_t u c := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hw)
  have ht4 : (uc_t u c) ^ 4 = uc_w u c := by
    unfold uc_t
    calc (Real.sqrt (Real.sqrt (uc_w u c))) ^ 4
        = ((Real.sqrt (Real.sqrt (uc_w u c))) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (uc_w u c)) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = uc_w u c := Real.sq_sqrt hw.le
  have hx := hasFDerivAt_fst_lin2 (u, c)
  have hwt3 := hasFDerivAt_mul_lin2 (hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_uc_w u c)) (hasFDerivAt_uc_t3 hw)
  have hinv_c := hasFDerivAt_div_lin2 (hasFDerivAt_const_lin2 (-3) (u, c)) hwt3 (by positivity)
  have h1 := hasFDerivAt_mul_lin2
    (hasFDerivAt_const_mul_lin2 (-2) (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 3 (u, c)) hx))
    (hasFDerivAt_inv_t3 hw)
  have h2 := hasFDerivAt_mul_lin2 (hasFDerivAt_G_A u c) hinv_c
  unfold G_Bc
  exact (hasFDerivAt_add_lin2 h1 h2).congr_fderiv (by
    unfold G_Buc G_Bcc; ext <;> simp [lin2] <;>
    · generalize uc_t u c = t at ht ht4 ⊢
      field_simp [ht.ne', hw.ne']; rw [← ht4]; ring)

lemma hasFDerivAt_G_u {u c : ℝ} (hu : -4 < u) (hw : 0 < uc_w u c) (hLm : 0 < 2 + u - 2 * c) :
    HasFDerivAt (fun p : ℝ × ℝ => G_u p.1 p.2) (lin2 (G_uu u c) (G_uc2 u c)) (u, c) := by
  unfold G_u
  have hLmd : HasFDerivAt (fun p : ℝ × ℝ => 2 + p.1 - 2 * p.2) (lin2 1 (-2)) (u, c) :=
    (hasFDerivAt_sub_lin2
      (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 2 (u, c)) (hasFDerivAt_fst_lin2 (u, c)))
      (hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_snd_lin2 (u, c)))).congr_fderiv (by ext <;> simp [lin2])
  exact (hasFDerivAt_div_lin2
    (hasFDerivAt_sub_lin2 (hasFDerivAt_G_Bu hu hw) (hasFDerivAt_G_uc hu hw hLm))
    hLmd hLm.ne').congr_fderiv (by
      unfold G_uu G_uc2 G_u G_c; ext <;> simp [lin2] <;> field_simp [hLm.ne'] <;> ring)

lemma hasFDerivAt_G_c {u c : ℝ} (hu : -4 < u) (hw : 0 < uc_w u c) (hLm : 0 < 2 + u - 2 * c) :
    HasFDerivAt (fun p : ℝ × ℝ => G_c p.1 p.2) (lin2 (G_uc2 u c) (G_cc u c)) (u, c) := by
  unfold G_c
  have hLmd : HasFDerivAt (fun p : ℝ × ℝ => 2 + p.1 - 2 * p.2) (lin2 1 (-2)) (u, c) :=
    (hasFDerivAt_sub_lin2
      (hasFDerivAt_add_lin2 (hasFDerivAt_const_lin2 2 (u, c)) (hasFDerivAt_fst_lin2 (u, c)))
      (hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_snd_lin2 (u, c)))).congr_fderiv (by ext <;> simp [lin2])
  exact (hasFDerivAt_div_lin2
    (hasFDerivAt_add_lin2 (hasFDerivAt_G_Bc hw)
      (hasFDerivAt_const_mul_lin2 2 (hasFDerivAt_G_uc hu hw hLm)))
    hLmd hLm.ne').congr_fderiv (by
      unfold G_uc2 G_cc G_u G_c; ext <;> simp [lin2] <;> field_simp [hLm.ne']; ring)

/- Section 5b: Verified Interval Evaluators, 11 decide Certificates, Analytic Tails & Unimodality -/

lemma Iv.Mem.smul' (k : ℤ) (r : ℝ) {I : Iv} {x : ℝ} (hI : I.Mem x) (hr : (k : ℝ) = r := by norm_num) :
    (ivSmul k I).Mem (r * x) := hr ▸ hI.smul k

lemma ivMem_int' (k : ℤ) (r : ℝ) (hr : (k : ℝ) = r := by norm_num) : (ivInt k).Mem r :=
  hr ▸ ivMem_int k

lemma ivMem_rat' (p : ℤ) (q : ℕ) (r : ℝ) (hr : (p : ℝ) / (q : ℝ) = r := by norm_num) :
    (ivRat p q).Mem r := hr ▸ ivMem_rat p q

def evalF (u c : Iv) : Iv :=
  let up2 := ivAdd (ivInt 2) u
  let w := ivAdd (ivSub (ivSq up2) (ivInt 2)) (ivSmul 2 c)
  let sw := ivSqrt w
  let t := ivSqrt sw
  let t3 := ivMul sw t
  let s := ivSqrt (ivAdd (ivInt 4) u)
  let t0c := ivSub (ivSq (ivAdd (ivSmul 3 c) (ivRat 4 3))) (ivRat 25 9)
  let t0 := ivAdd t0c (ivMul u (ivAdd (ivAdd (ivInt 24) (ivSmul 8 c)) (ivMul u (ivAdd (ivInt 20) (ivSmul 4 u)))))
  let d0 := ivAdd (ivSub (ivSmul 9 (ivSq c)) (ivInt 1)) (ivMul u (ivAdd (ivInt 18) (ivMul u (ivAdd (ivInt 12) (ivSmul 2 u)))))
  ivAdd (ivAdd (ivSmul 2 (ivMul w t3)) (ivMul s t0)) (ivMul t d0)

def evalFuFc (u c : Iv) : Iv × Iv :=
  let up2 := ivAdd (ivInt 2) u
  let w := ivAdd (ivSub (ivSq up2) (ivInt 2)) (ivSmul 2 c)
  let sw := ivSqrt w
  let t := ivSqrt sw
  let t3 := ivMul sw t
  let s := ivSqrt (ivAdd (ivInt 4) u)
  let t0c := ivSub (ivSq (ivAdd (ivSmul 3 c) (ivRat 4 3))) (ivRat 25 9)
  let t0 := ivAdd t0c (ivMul u (ivAdd (ivAdd (ivInt 24) (ivSmul 8 c)) (ivMul u (ivAdd (ivInt 20) (ivSmul 4 u)))))
  let d0 := ivAdd (ivSub (ivSmul 9 (ivSq c)) (ivInt 1)) (ivMul u (ivAdd (ivInt 18) (ivMul u (ivAdd (ivInt 12) (ivSmul 2 u)))))
  let T0u := ivAdd (ivAdd (ivInt 24) (ivSmul 8 c)) (ivMul u (ivAdd (ivInt 40) (ivSmul 12 u)))
  let T0c := ivAdd (ivAdd (ivSmul 18 c) (ivInt 8)) (ivSmul 8 u)
  let D0u := ivAdd (ivInt 18) (ivMul u (ivAdd (ivInt 24) (ivSmul 6 u)))
  let D0c := ivSmul 18 c
  let Fu := ivAdd (ivAdd (ivSmul 7 (ivMul up2 t3))
      (ivDiv (ivAdd t0 (ivSmul 2 (ivMul (ivAdd (ivInt 4) u) T0u))) (ivSmul 2 s)))
    (ivDiv (ivAdd (ivMul up2 d0) (ivSmul 2 (ivMul w D0u))) (ivSmul 2 t3))
  let Fc := ivAdd (ivAdd (ivSmul 7 t3) (ivMul s T0c))
    (ivDiv (ivAdd d0 (ivSmul 2 (ivMul w D0c))) (ivSmul 2 t3))
  (Fu, Fc)

def evalFcc0 (c : Iv) : Iv :=
  let w := ivAdd (ivInt 2) (ivSmul 2 c)
  let sw := ivSqrt w
  let t := ivSqrt sw
  let t3 := ivMul sw t
  let s := ivInt 2
  let d0 := ivSub (ivSmul 9 (ivSq c)) (ivInt 1)
  let D0c := ivSmul 18 c
  ivAdd (ivAdd (ivDiv (ivInt 21) (ivSmul 2 t)) (ivSmul 18 s))
    (ivDiv (ivAdd (ivAdd (ivSmul (-3) d0) (ivSmul 4 (ivMul w D0c))) (ivSmul 72 (ivSq w)))
      (ivSmul 4 (ivMul w t3)))

def evalHor (u c : Iv) : Iv :=
  let (Fu, Fc) := evalFuFc u c
  let a := ivSub (ivInt 2) (ivMul c (ivAdd (ivInt 2) u))
  let b := ivSub (ivInt 1) (ivSq c)
  ivAdd (ivMul a Fu) (ivMul b Fc)

def evalGGuGc (u c : Iv) : Iv × Iv × Iv :=
  let up2 := ivAdd (ivInt 2) u
  let w := ivAdd (ivSub (ivSq up2) (ivInt 2)) (ivSmul 2 c)
  let sw := ivSqrt w
  let t := ivSqrt sw
  let t3 := ivMul sw t
  let s := ivSqrt (ivAdd (ivInt 4) u)
  let Lm := ivSub up2 (ivSmul 2 c)
  let A := ivSmul 2 (ivSub (ivInt 1) (ivMul c (ivAdd (ivInt 3) u)))
  let Au := ivSmul (-2) c
  let Ac := ivSmul (-2) (ivAdd (ivInt 3) u)
  let wt3 := ivMul w t3
  let invt3 := ivDiv (ivInt 1) t3
  let invt3u := ivDiv (ivNeg (ivSmul 3 up2)) (ivSmul 2 wt3)
  let invt3c := ivDiv (ivInt (-3)) (ivSmul 2 wt3)
  let B := ivSub (ivMul A invt3) s
  let Bu := ivSub (ivAdd (ivMul Au invt3) (ivMul A invt3u)) (ivDiv (ivInt 1) (ivSmul 2 s))
  let Bc := ivAdd (ivMul Ac invt3) (ivMul A invt3c)
  let G := ivDiv B Lm
  let Gu := ivDiv (ivSub Bu G) Lm
  let Gc := ivDiv (ivAdd Bc (ivSmul 2 G)) Lm
  (G, Gu, Gc)

def evalN1 (u c : Iv) : Iv :=
  let (Fu, Fc) := evalFuFc u c
  let (G, Gu, Gc) := evalGGuGc u c
  ivAdd (ivNeg (ivMul Fc G)) (ivSmul 2 (ivMul u (ivSub (ivMul Gc Fu) (ivMul Gu Fc))))

def evalPeakD2 (u c : Iv) : Iv :=
  let up2 := ivAdd (ivInt 2) u
  let w := ivAdd (ivSub (ivSq up2) (ivInt 2)) (ivSmul 2 c)
  let sw := ivSqrt w
  let t := ivSqrt sw
  let t3 := ivMul sw t
  let s := ivSqrt (ivAdd (ivInt 4) u)
  let t0c := ivSub (ivSq (ivAdd (ivSmul 3 c) (ivRat 4 3))) (ivRat 25 9)
  let t0 := ivAdd t0c (ivMul u (ivAdd (ivAdd (ivInt 24) (ivSmul 8 c)) (ivMul u (ivAdd (ivInt 20) (ivSmul 4 u)))))
  let d0 := ivAdd (ivSub (ivSmul 9 (ivSq c)) (ivInt 1)) (ivMul u (ivAdd (ivInt 18) (ivMul u (ivAdd (ivInt 12) (ivSmul 2 u)))))
  let T0u := ivAdd (ivAdd (ivInt 24) (ivSmul 8 c)) (ivMul u (ivAdd (ivInt 40) (ivSmul 12 u)))
  let T0c := ivAdd (ivAdd (ivSmul 18 c) (ivInt 8)) (ivSmul 8 u)
  let D0u := ivAdd (ivInt 18) (ivMul u (ivAdd (ivInt 24) (ivSmul 6 u)))
  let D0c := ivSmul 18 c
  let Fu := ivAdd (ivAdd (ivSmul 7 (ivMul up2 t3))
      (ivDiv (ivAdd t0 (ivSmul 2 (ivMul (ivAdd (ivInt 4) u) T0u))) (ivSmul 2 s)))
    (ivDiv (ivAdd (ivMul up2 d0) (ivSmul 2 (ivMul w D0u))) (ivSmul 2 t3))
  let Fc := ivAdd (ivAdd (ivSmul 7 t3) (ivMul s T0c))
    (ivDiv (ivAdd d0 (ivSmul 2 (ivMul w D0c))) (ivSmul 2 t3))
  let T0uu := ivAdd (ivInt 40) (ivSmul 24 u)
  let D0uu := ivAdd (ivInt 24) (ivSmul 12 u)
  let wt3 := ivMul w t3
  let tu := ivDiv up2 (ivSmul 2 t3)
  let tc := ivDiv (ivInt 1) (ivSmul 2 t3)
  let tuu := ivDiv (ivSub (ivSmul 2 w) (ivSmul 3 (ivSq up2))) (ivSmul 4 wt3)
  let tuc := ivDiv (ivNeg (ivSmul 3 up2)) (ivSmul 4 wt3)
  let Fuu := ivAdd (ivAdd
      (ivAdd (ivSmul 7 t3) (ivDiv (ivSmul 21 (ivSq up2)) (ivSmul 2 t)))
      (ivAdd (ivAdd (ivDiv (ivNeg t0) (ivSmul 4 (ivMul (ivAdd (ivInt 4) u) s))) (ivDiv T0u s)) (ivMul s T0uu)))
    (ivAdd (ivAdd (ivMul tuu d0) (ivSmul 2 (ivMul tu D0u))) (ivMul t D0uu))
  let Fuc := ivAdd (ivAdd
      (ivDiv (ivSmul 21 up2) (ivSmul 2 t))
      (ivAdd (ivDiv T0c (ivSmul 2 s)) (ivSmul 8 s)))
    (ivAdd (ivAdd (ivMul tuc d0) (ivMul tu D0c)) (ivMul tc D0u))
  let Fcc := ivAdd (ivAdd (ivDiv (ivInt 21) (ivSmul 2 t)) (ivSmul 18 s))
    (ivDiv (ivAdd (ivAdd (ivSmul (-3) d0) (ivSmul 4 (ivMul w D0c))) (ivSmul 72 (ivSq w))) (ivSmul 4 wt3))
  let Lm := ivSub up2 (ivSmul 2 c)
  let A := ivSmul 2 (ivSub (ivInt 1) (ivMul c (ivAdd (ivInt 3) u)))
  let Au := ivSmul (-2) c
  let Ac := ivSmul (-2) (ivAdd (ivInt 3) u)
  let invt3 := ivDiv (ivInt 1) t3
  let invt3u := ivDiv (ivNeg (ivSmul 3 up2)) (ivSmul 2 wt3)
  let invt3c := ivDiv (ivInt (-3)) (ivSmul 2 wt3)
  let w2t3 := ivMul w wt3
  let invt3uu := ivDiv (ivAdd (ivSmul (-6) w) (ivSmul 21 (ivSq up2))) (ivSmul 4 w2t3)
  let invt3uc := ivDiv (ivSmul 21 up2) (ivSmul 4 w2t3)
  let invt3cc := ivDiv (ivInt 21) (ivSmul 4 w2t3)
  let B := ivSub (ivMul A invt3) s
  let Bu := ivSub (ivAdd (ivMul Au invt3) (ivMul A invt3u)) (ivDiv (ivInt 1) (ivSmul 2 s))
  let Bc := ivAdd (ivMul Ac invt3) (ivMul A invt3c)
  let Buu := ivAdd (ivAdd (ivSmul 2 (ivMul Au invt3u)) (ivMul A invt3uu)) (ivDiv (ivInt 1) (ivSmul 4 (ivMul (ivAdd (ivInt 4) u) s)))
  let Buc := ivAdd (ivAdd (ivAdd (ivSmul (-2) invt3) (ivMul Au invt3c)) (ivMul Ac invt3u)) (ivMul A invt3uc)
  let Bcc := ivAdd (ivSmul 2 (ivMul Ac invt3c)) (ivMul A invt3cc)
  let G := ivDiv B Lm
  let Gu := ivDiv (ivSub Bu G) Lm
  let Gc := ivDiv (ivAdd Bc (ivSmul 2 G)) Lm
  let Guu := ivDiv (ivSub Buu (ivSmul 2 Gu)) Lm
  let Guc := ivDiv (ivSub (ivAdd Buc (ivSmul 2 Gu)) Gc) Lm
  let Gcc := ivDiv (ivAdd Bcc (ivSmul 4 Gc)) Lm
  let up := ivDiv (ivNeg Fc) Fu
  let upp := ivDiv (ivNeg (ivAdd (ivAdd (ivMul Fuu (ivSq up)) (ivSmul 2 (ivMul Fuc up))) Fcc)) Fu
  let up_u := ivDiv up u
  let term1 := ivDiv (ivSub (ivDiv upp u) (ivSq up_u)) (ivInt 2)
  let g_dd := ivAdd (ivAdd (ivAdd (ivMul Guu (ivSq up)) (ivSmul 2 (ivMul Guc up))) Gcc) (ivMul Gu upp)
  let g_d := ivAdd (ivMul Gu up) Gc
  let term2 := ivSub (ivDiv g_dd G) (ivSq (ivDiv g_d G))
  ivAdd term1 term2

def evalQ (c : Iv) : Iv :=
  let sh := ivAdd c (ivRat 453 1000)
  ivSub (ivRat 304 10000) (ivMul (ivRat 359 1000) (ivSq sh))

def cert1 : Bool :=
  (gridIvs 0 (ivRat 16 100).hi 4).all fun u =>
    (gridIvs (ivRat (-85) 100).lo (ivRat 34 100).hi 16).all fun c =>
      (evalFuFc u c).1.isPos

def cert2 : Bool :=
  (gridIvs (ivRat (-85) 100).lo (ivRat 34 100).hi 20).all fun c =>
    (evalF (ivRat 4 100) c).isPos

def cert3a : Bool :=
  (gridIvs (ivRat (-85) 100).lo (ivRat (-75) 100).hi 8).all fun c =>
    (evalF (ivInt 0) c).isPos

def cert3b : Bool :=
  (gridIvs (ivRat (-15) 100).lo (ivRat 34 100).hi 16).all fun c =>
    (evalF (ivInt 0) c).isPos

def cert4 : Bool :=
  (gridIvs (ivRat (-75) 100).lo (ivRat (-15) 100).hi 8).all fun c =>
    (evalFcc0 c).isPos

def cert4mid : Bool := (evalF (ivInt 0) (ivRat (-1) 2)).isNeg

def cert5 : Bool :=
  (gridIvs 0 (ivRat 4 100).hi 2).all fun u =>
    (gridIvs (ivRat (-75) 100).lo (ivRat (-15) 100).hi 12).all fun c =>
      (evalHor u c).isPos

def cert6a : Bool :=
  let eps := ivRat 2 1000
  (gridIvs (ivRat (-75) 100).lo (ivRat (-68) 100).hi 12).all fun c =>
    let q := evalQ c
    let ulo0 := max 0 (ivSub q eps).lo
    let uhi := max 0 (ivAdd q eps).hi
    let okHi := (evalF ⟨uhi, uhi, true⟩ c).isPos
    let ulo := if 0 < ulo0 && (evalF ⟨ulo0, ulo0, true⟩ c).isNeg then ulo0 else 0
    let um := (ulo + uhi) / 2
    okHi && (evalN1 ⟨ulo, um, true⟩ c).isPos && (evalN1 ⟨um, uhi, true⟩ c).isPos

def cert6b : Bool :=
  let eps := ivRat 2 1000
  (gridIvs (ivRat (-68) 100).lo (ivRat (-60) 100).hi 8).all fun c =>
    let q := evalQ c
    let ulo := (ivSub q eps).lo
    let uhi := (ivAdd q eps).hi
    let u : Iv := ⟨ulo, uhi, true⟩
    decide (0 < ulo) && decide (0 < uhi) && (evalF ⟨ulo, ulo, true⟩ c).isNeg && (evalF ⟨uhi, uhi, true⟩ c).isPos &&
      (evalGGuGc u c).1.isPos && (evalPeakD2 u c).isNeg

def cert6c : Bool :=
  let eps := ivRat 2 1000
  (gridIvs (ivRat (-60) 100).lo (ivRat (-38) 100).hi 20).all fun c =>
    let q := evalQ c
    let ulo := (ivSub q eps).lo
    let uhi := (ivAdd q eps).hi
    let u : Iv := ⟨ulo, uhi, true⟩
    decide (0 < ulo) && decide (0 < uhi) && (evalF ⟨ulo, ulo, true⟩ c).isNeg && (evalF ⟨uhi, uhi, true⟩ c).isPos &&
      (evalN1 u c).isNeg

def cert6d : Bool :=
  (gridIvs 0 (ivRat 4 100).hi 2).all fun u =>
    (gridIvs (ivRat (-38) 100).lo (ivRat (-15) 100).hi 8).all fun c =>
      let (Fu, Fc) := evalFuFc u c
      let (_, Gu, Gc) := evalGGuGc u c
      Fc.isPos && (ivSub (ivMul Gc Fu) (ivMul Gu Fc)).isNeg

set_option maxHeartbeats 800000 in
lemma cert1_ok : cert1 = true := by decide
set_option maxHeartbeats 800000 in
lemma cert2_ok : cert2 = true := by decide
set_option maxHeartbeats 800000 in
lemma cert3a_ok : cert3a = true := by decide
set_option maxHeartbeats 800000 in
lemma cert3b_ok : cert3b = true := by decide
set_option maxHeartbeats 800000 in
lemma cert4_ok : cert4 = true := by decide
lemma cert4mid_ok : cert4mid = true := by decide
set_option maxHeartbeats 800000 in
lemma cert5_ok : cert5 = true := by decide
set_option maxHeartbeats 800000 in
lemma cert6a_ok : cert6a = true := by decide
set_option maxHeartbeats 800000 in
lemma cert6b_ok : cert6b = true := by decide
set_option maxHeartbeats 800000 in
lemma cert6c_ok : cert6c = true := by decide
set_option maxHeartbeats 800000 in
lemma cert6d_ok : cert6d = true := by decide

lemma uc_w_sq_form (u c : ℝ) : uc_w u c = (2 + u) ^ 2 - 2 + 2 * c := by unfold uc_w; ring
lemma T0_m_sq_form (u c : ℝ) :
    T0_m u c = (3 * c + 4 / 3) ^ 2 - 25 / 9 + u * (24 + 8 * c + u * (20 + 4 * u)) := by
  unfold T0_m; ring
lemma D0_m_sq_form (u c : ℝ) :
    D0_m u c = 9 * c ^ 2 - 1 + u * (18 + u * (12 + 2 * u)) := by
  unfold D0_m; ring
lemma uc_t_pow3_eq {u c : ℝ} : (uc_t u c) ^ 3 = Real.sqrt (uc_w u c) * uc_t u c := by
  unfold uc_t
  calc (Real.sqrt (Real.sqrt (uc_w u c))) ^ 3
      = (Real.sqrt (Real.sqrt (uc_w u c))) ^ 2 * Real.sqrt (Real.sqrt (uc_w u c)) := by ring
    _ = Real.sqrt (uc_w u c) * Real.sqrt (Real.sqrt (uc_w u c)) := by
        rw [Real.sq_sqrt (Real.sqrt_nonneg _)]

lemma evalF_sound {Iu Ic : Iv} {u c : ℝ} (hu : Iu.Mem u) (hc : Ic.Mem c) :
    (evalF Iu Ic).Mem (F_det u c) := by
  unfold evalF; dsimp only
  have hup2 := (ivMem_int' 2 2).add hu
  have hw := (hup2.sq.sub (ivMem_int' 2 2)).add (hc.smul' 2 2)
  rw [← uc_w_sq_form] at hw
  have hsw := hw.sqrt
  have ht := hsw.sqrt
  change Iv.Mem (uc_t u c) _ at ht
  have ht3 := hsw.mul ht
  rw [← uc_t_pow3_eq] at ht3
  have hs := ((ivMem_int' 4 4).add hu).sqrt
  have ht0 := (((hc.smul' 3 3).add (ivMem_rat' 4 3 (4 / 3))).sq.sub
    (ivMem_rat' 25 9 (25 / 9))).add
    (hu.mul (((ivMem_int' 24 24).add (hc.smul' 8 8)).add
      (hu.mul ((ivMem_int' 20 20).add (hu.smul' 4 4)))))
  rw [← T0_m_sq_form] at ht0
  have hd0 := ((hc.sq.smul' 9 9).sub (ivMem_int' 1 1)).add
    (hu.mul ((ivMem_int' 18 18).add
      (hu.mul ((ivMem_int' 12 12).add (hu.smul' 2 2)))))
  rw [← D0_m_sq_form] at hd0
  have hres := (((hw.mul ht3).smul' 2 2).add (hs.mul ht0)).add (ht.mul hd0)
  rw [show 2 * (uc_w u c * (uc_t u c) ^ 3) + Real.sqrt (4 + u) * T0_m u c +
      uc_t u c * D0_m u c = F_det u c by unfold F_det; ring] at hres
  exact hres

lemma evalFuFc_sound {Iu Ic : Iv} {u c : ℝ} (hu : Iu.Mem u) (hc : Ic.Mem c) :
    (evalFuFc Iu Ic).1.Mem (F_u u c) ∧ (evalFuFc Iu Ic).2.Mem (F_c u c) := by
  unfold evalFuFc; dsimp only
  have hup2 := (ivMem_int' 2 2).add hu
  have hw := (hup2.sq.sub (ivMem_int' 2 2)).add (hc.smul' 2 2)
  rw [← uc_w_sq_form] at hw
  have hsw := hw.sqrt
  have ht := hsw.sqrt
  change Iv.Mem (uc_t u c) _ at ht
  have ht3 := hsw.mul ht
  rw [← uc_t_pow3_eq] at ht3
  have h4u := (ivMem_int' 4 4).add hu
  have hs := h4u.sqrt
  have ht0 := (((hc.smul' 3 3).add (ivMem_rat' 4 3 (4 / 3))).sq.sub
    (ivMem_rat' 25 9 (25 / 9))).add
    (hu.mul (((ivMem_int' 24 24).add (hc.smul' 8 8)).add
      (hu.mul ((ivMem_int' 20 20).add (hu.smul' 4 4)))))
  rw [← T0_m_sq_form] at ht0
  have hd0 := ((hc.sq.smul' 9 9).sub (ivMem_int' 1 1)).add
    (hu.mul ((ivMem_int' 18 18).add
      (hu.mul ((ivMem_int' 12 12).add (hu.smul' 2 2)))))
  rw [← D0_m_sq_form] at hd0
  have hT0u := ((ivMem_int' 24 24).add (hc.smul' 8 8)).add
    (hu.mul ((ivMem_int' 40 40).add (hu.smul' 12 12)))
  have hT0c := ((hc.smul' 18 18).add (ivMem_int' 8 8)).add (hu.smul' 8 8)
  have hD0u := (ivMem_int' 18 18).add
    (hu.mul ((ivMem_int' 24 24).add (hu.smul' 6 6)))
  have hD0c := hc.smul' 18 18
  constructor
  · have hres := (((hup2.mul ht3).smul' 7 7).add
      ((ht0.add ((h4u.mul hT0u).smul' 2 2)).div (hs.smul' 2 2))).add
      (((hup2.mul hd0).add ((hw.mul hD0u).smul' 2 2)).div (ht3.smul' 2 2))
    rw [show 7 * ((2 + u) * (uc_t u c) ^ 3) +
        (T0_m u c + 2 * ((4 + u) * (24 + 8 * c + u * (40 + 12 * u)))) / (2 * Real.sqrt (4 + u)) +
        ((2 + u) * D0_m u c + 2 * (uc_w u c * (18 + u * (24 + 6 * u)))) / (2 * (uc_t u c) ^ 3) =
        F_u u c by unfold F_u T0_u D0_u; ring] at hres
    exact hres
  · have hres := ((ht3.smul' 7 7).add (hs.mul hT0c)).add
      ((hd0.add ((hw.mul hD0c).smul' 2 2)).div (ht3.smul' 2 2))
    rw [show 7 * (uc_t u c) ^ 3 + Real.sqrt (4 + u) * (18 * c + 8 + 8 * u) +
        (D0_m u c + 2 * (uc_w u c * (18 * c))) / (2 * (uc_t u c) ^ 3) =
        F_c u c by unfold F_c T0_c D0_c; ring] at hres
    exact hres

lemma evalFcc0_sound {Ic : Iv} {c : ℝ} (hc : Ic.Mem c) :
    (evalFcc0 Ic).Mem (F_cc 0 c) := by
  unfold evalFcc0; dsimp only
  have hw := (ivMem_int' 2 2).add (hc.smul' 2 2)
  rw [show 2 + 2 * c = uc_w 0 c by unfold uc_w; ring] at hw
  have hsw := hw.sqrt
  have ht := hsw.sqrt
  change Iv.Mem (uc_t 0 c) _ at ht
  have ht3 := hsw.mul ht
  rw [← uc_t_pow3_eq] at ht3
  have hs := ivMem_int' 2 2
  have hd0 := (hc.sq.smul' 9 9).sub (ivMem_int' 1 1)
  rw [show 9 * c ^ 2 - 1 = D0_m 0 c by unfold D0_m; ring] at hd0
  have hD0c := hc.smul' 18 18
  have hres := (((ivMem_int' 21 21).div (ht.smul' 2 2)).add (hs.smul' 18 18)).add
    ((((hd0.smul' (-3) (-3)).add ((hw.mul hD0c).smul' 4 4)).add
      (hw.sq.smul' 72 72)).div ((hw.mul ht3).smul' 4 4))
  rw [show 21 / (2 * uc_t 0 c) + 18 * 2 +
      ((-3) * D0_m 0 c + 4 * (uc_w 0 c * (18 * c)) + 72 * (uc_w 0 c) ^ 2) /
        (4 * (uc_w 0 c * (uc_t 0 c) ^ 3)) = F_cc 0 c by
      unfold F_cc D0_c; rw [show Real.sqrt (4 + 0) = 2 by norm_num]; ring] at hres
  exact hres

lemma evalHor_sound {Iu Ic : Iv} {u c : ℝ} (hu : Iu.Mem u) (hc : Ic.Mem c) :
    (evalHor Iu Ic).Mem (hor_F u c) := by
  unfold evalHor; dsimp only
  have ⟨hFu, hFc⟩ := evalFuFc_sound hu hc
  have ha := (ivMem_int' 2 2).sub (hc.mul ((ivMem_int' 2 2).add hu))
  have hb := (ivMem_int' 1 1).sub hc.sq
  exact (ha.mul hFu).add (hb.mul hFc)

lemma evalGGuGc_sound {Iu Ic : Iv} {u c : ℝ} (hu : Iu.Mem u) (hc : Ic.Mem c) :
    (evalGGuGc Iu Ic).1.Mem (G_uc u c) ∧
    (evalGGuGc Iu Ic).2.1.Mem (G_u u c) ∧
    (evalGGuGc Iu Ic).2.2.Mem (G_c u c) := by
  unfold evalGGuGc; dsimp only
  have hup2 := (ivMem_int' 2 2).add hu
  have hw := (hup2.sq.sub (ivMem_int' 2 2)).add (hc.smul' 2 2)
  rw [← uc_w_sq_form] at hw
  have hsw := hw.sqrt
  have ht := hsw.sqrt
  change Iv.Mem (uc_t u c) _ at ht
  have ht3 := hsw.mul ht
  rw [← uc_t_pow3_eq] at ht3
  have hs := ((ivMem_int' 4 4).add hu).sqrt
  have hLm := hup2.sub (hc.smul' 2 2)
  have h3u := (ivMem_int' 3 3).add hu
  have hA := ((ivMem_int' 1 1).sub (hc.mul h3u)).smul' 2 2
  have hAu := hc.smul' (-2) (-2)
  have hAc := h3u.smul' (-2) (-2)
  have hwt3 := hw.mul ht3
  have hinv := (ivMem_int' 1 1).div ht3
  have hinvu := (hup2.smul' 3 3).neg.div (hwt3.smul' 2 2)
  have hinvc := (ivMem_int' (-3) (-3)).div (hwt3.smul' 2 2)
  have hB := (hA.mul hinv).sub hs
  have hBu := ((hAu.mul hinv).add (hA.mul hinvu)).sub ((ivMem_int' 1 1).div (hs.smul' 2 2))
  have hBc := (hAc.mul hinv).add (hA.mul hinvc)
  have hG := hB.div hLm
  rw [show (2 * (1 - c * (3 + u)) * (1 / (uc_t u c) ^ 3) - Real.sqrt (4 + u)) / (2 + u - 2 * c) =
      G_uc u c by rw [G_uc_eq_G_B_div]; unfold G_B G_A; ring] at hG
  have hGu := (hBu.sub hG).div hLm
  rw [show ((-2 * c * (1 / (uc_t u c) ^ 3) +
        2 * (1 - c * (3 + u)) * (-(3 * (2 + u)) / (2 * (uc_w u c * (uc_t u c) ^ 3))) -
        1 / (2 * Real.sqrt (4 + u))) - G_uc u c) / (2 + u - 2 * c) = G_u u c by
      unfold G_u G_Bu G_A; ring] at hGu
  have hGc := (hBc.add (hG.smul' 2 2)).div hLm
  rw [show (-2 * (3 + u) * (1 / (uc_t u c) ^ 3) +
        2 * (1 - c * (3 + u)) * (-3 / (2 * (uc_w u c * (uc_t u c) ^ 3))) + 2 * G_uc u c) /
      (2 + u - 2 * c) = G_c u c by unfold G_c G_Bc G_A; ring] at hGc
  exact ⟨hG, hGu, hGc⟩

lemma evalN1_sound {Iu Ic : Iv} {u c : ℝ} (hu : Iu.Mem u) (hc : Ic.Mem c) :
    (evalN1 Iu Ic).Mem (N1_uc u c) := by
  unfold evalN1; dsimp only
  have ⟨hFu, hFc⟩ := evalFuFc_sound hu hc
  have ⟨hG, hGu, hGc⟩ := evalGGuGc_sound hu hc
  have hres := (hFc.mul hG).neg.add ((hu.mul ((hGc.mul hFu).sub (hGu.mul hFc))).smul' 2 2)
  rw [show -(F_c u c * G_uc u c) + 2 * (u * (G_c u c * F_u u c - G_u u c * F_c u c)) = N1_uc u c by
    unfold N1_uc; ring] at hres
  exact hres

lemma evalPeakD2_sound {Iu Ic : Iv} {u c : ℝ} (hu : Iu.Mem u) (hc : Ic.Mem c) :
    (evalPeakD2 Iu Ic).Mem (PeakD2_uc u c) := by
  unfold evalPeakD2 PeakD2_uc; dsimp only
  have hup2 := (ivMem_int' 2 2).add hu
  have hw := (hup2.sq.sub (ivMem_int' 2 2)).add (hc.smul' 2 2)
  rw [← uc_w_sq_form] at hw
  have hsw := hw.sqrt
  have ht := hsw.sqrt
  change Iv.Mem (uc_t u c) _ at ht
  have ht3 := hsw.mul ht
  rw [← uc_t_pow3_eq] at ht3
  have h4u := (ivMem_int' 4 4).add hu
  have hs := h4u.sqrt
  have ht0 := (((hc.smul' 3 3).add (ivMem_rat' 4 3 (4 / 3))).sq.sub
    (ivMem_rat' 25 9 (25 / 9))).add
    (hu.mul (((ivMem_int' 24 24).add (hc.smul' 8 8)).add
      (hu.mul ((ivMem_int' 20 20).add (hu.smul' 4 4)))))
  rw [← T0_m_sq_form] at ht0
  have hd0 := ((hc.sq.smul' 9 9).sub (ivMem_int' 1 1)).add
    (hu.mul ((ivMem_int' 18 18).add
      (hu.mul ((ivMem_int' 12 12).add (hu.smul' 2 2)))))
  rw [← D0_m_sq_form] at hd0
  have hT0u := ((ivMem_int' 24 24).add (hc.smul' 8 8)).add
    (hu.mul ((ivMem_int' 40 40).add (hu.smul' 12 12)))
  have hT0c := ((hc.smul' 18 18).add (ivMem_int' 8 8)).add (hu.smul' 8 8)
  have hD0u := (ivMem_int' 18 18).add
    (hu.mul ((ivMem_int' 24 24).add (hu.smul' 6 6)))
  have hD0c := hc.smul' 18 18
  have hFu := (((hup2.mul ht3).smul' 7 7).add
    ((ht0.add ((h4u.mul hT0u).smul' 2 2)).div (hs.smul' 2 2))).add
    (((hup2.mul hd0).add ((hw.mul hD0u).smul' 2 2)).div (ht3.smul' 2 2))
  rw [show 7 * ((2 + u) * (uc_t u c) ^ 3) +
      (T0_m u c + 2 * ((4 + u) * (24 + 8 * c + u * (40 + 12 * u)))) / (2 * Real.sqrt (4 + u)) +
      ((2 + u) * D0_m u c + 2 * (uc_w u c * (18 + u * (24 + 6 * u)))) / (2 * (uc_t u c) ^ 3) =
      F_u u c by unfold F_u T0_u D0_u; ring] at hFu
  have hFc := ((ht3.smul' 7 7).add (hs.mul hT0c)).add
    ((hd0.add ((hw.mul hD0c).smul' 2 2)).div (ht3.smul' 2 2))
  rw [show 7 * (uc_t u c) ^ 3 + Real.sqrt (4 + u) * (18 * c + 8 + 8 * u) +
      (D0_m u c + 2 * (uc_w u c * (18 * c))) / (2 * (uc_t u c) ^ 3) =
      F_c u c by unfold F_c T0_c D0_c; ring] at hFc
  have hT0uu := (ivMem_int' 40 40).add (hu.smul' 24 24)
  have hD0uu := (ivMem_int' 24 24).add (hu.smul' 12 12)
  have hwt3 := hw.mul ht3
  have htu := hup2.div (ht3.smul' 2 2)
  have htc := (ivMem_int' 1 1).div (ht3.smul' 2 2)
  have htuu := ((hw.smul' 2 2).sub (hup2.sq.smul' 3 3)).div (hwt3.smul' 4 4)
  have htuc := (hup2.smul' 3 3).neg.div (hwt3.smul' 4 4)
  have hFuu := (((ht3.smul' 7 7).add ((hup2.sq.smul' 21 21).div (ht.smul' 2 2))).add
    (((ht0.neg.div ((h4u.mul hs).smul' 4 4)).add (hT0u.div hs)).add (hs.mul hT0uu))).add
    (((htuu.mul hd0).add ((htu.mul hD0u).smul' 2 2)).add (ht.mul hD0uu))
  rw [show 7 * (uc_t u c) ^ 3 + 21 * (2 + u) ^ 2 / (2 * uc_t u c) +
      (-T0_m u c / (4 * ((4 + u) * Real.sqrt (4 + u))) +
        (24 + 8 * c + u * (40 + 12 * u)) / Real.sqrt (4 + u) + Real.sqrt (4 + u) * (40 + 24 * u)) +
      ((2 * uc_w u c - 3 * (2 + u) ^ 2) / (4 * (uc_w u c * (uc_t u c) ^ 3)) * D0_m u c +
        2 * ((2 + u) / (2 * (uc_t u c) ^ 3) * (18 + u * (24 + 6 * u))) + uc_t u c * (24 + 12 * u)) =
      F_uu u c by unfold F_uu T0_u D0_u; ring] at hFuu
  have hFuc := (((hup2.smul' 21 21).div (ht.smul' 2 2)).add
    ((hT0c.div (hs.smul' 2 2)).add (hs.smul' 8 8))).add
    (((htuc.mul hd0).add (htu.mul hD0c)).add (htc.mul hD0u))
  rw [show 21 * (2 + u) / (2 * uc_t u c) +
      ((18 * c + 8 + 8 * u) / (2 * Real.sqrt (4 + u)) + 8 * Real.sqrt (4 + u)) +
      (-(3 * (2 + u)) / (4 * (uc_w u c * (uc_t u c) ^ 3)) * D0_m u c +
        (2 + u) / (2 * (uc_t u c) ^ 3) * (18 * c) +
        1 / (2 * (uc_t u c) ^ 3) * (18 + u * (24 + 6 * u))) =
      F_uc u c by unfold F_uc T0_c D0_c D0_u; ring] at hFuc
  have hFcc := (((ivMem_int' 21 21).div (ht.smul' 2 2)).add (hs.smul' 18 18)).add
    ((((hd0.smul' (-3) (-3)).add ((hw.mul hD0c).smul' 4 4)).add
      (hw.sq.smul' 72 72)).div (hwt3.smul' 4 4))
  rw [show 21 / (2 * uc_t u c) + 18 * Real.sqrt (4 + u) +
      (-3 * D0_m u c + 4 * (uc_w u c * (18 * c)) + 72 * (uc_w u c) ^ 2) /
        (4 * (uc_w u c * (uc_t u c) ^ 3)) = F_cc u c by unfold F_cc D0_c; ring] at hFcc
  have hLm := hup2.sub (hc.smul' 2 2)
  have h3u := (ivMem_int' 3 3).add hu
  have hA := ((ivMem_int' 1 1).sub (hc.mul h3u)).smul' 2 2
  have hAu := hc.smul' (-2) (-2)
  have hAc := h3u.smul' (-2) (-2)
  have hinv := (ivMem_int' 1 1).div ht3
  have hinvu := (hup2.smul' 3 3).neg.div (hwt3.smul' 2 2)
  have hinvc := (ivMem_int' (-3) (-3)).div (hwt3.smul' 2 2)
  have hw2t3 := hw.mul hwt3
  have hinvuu := ((hw.smul' (-6) (-6)).add (hup2.sq.smul' 21 21)).div (hw2t3.smul' 4 4)
  have hinvuc := (hup2.smul' 21 21).div (hw2t3.smul' 4 4)
  have hinvcc := (ivMem_int' 21 21).div (hw2t3.smul' 4 4)
  have hB := (hA.mul hinv).sub hs
  have hBu := ((hAu.mul hinv).add (hA.mul hinvu)).sub ((ivMem_int' 1 1).div (hs.smul' 2 2))
  have hBc := (hAc.mul hinv).add (hA.mul hinvc)
  have hBuu := (((hAu.mul hinvu).smul' 2 2).add (hA.mul hinvuu)).add
    ((ivMem_int' 1 1).div ((h4u.mul hs).smul' 4 4))
  have hBuc := (((hinv.smul' (-2) (-2)).add (hAu.mul hinvc)).add (hAc.mul hinvu)).add (hA.mul hinvuc)
  have hBcc := ((hAc.mul hinvc).smul' 2 2).add (hA.mul hinvcc)
  have hG := hB.div hLm
  rw [show (2 * (1 - c * (3 + u)) * (1 / (uc_t u c) ^ 3) - Real.sqrt (4 + u)) / (2 + u - 2 * c) =
      G_uc u c by rw [G_uc_eq_G_B_div]; unfold G_B G_A; ring] at hG
  have hGu := (hBu.sub hG).div hLm
  rw [show ((-2 * c * (1 / (uc_t u c) ^ 3) +
        2 * (1 - c * (3 + u)) * (-(3 * (2 + u)) / (2 * (uc_w u c * (uc_t u c) ^ 3))) -
        1 / (2 * Real.sqrt (4 + u))) - G_uc u c) / (2 + u - 2 * c) = G_u u c by
      unfold G_u G_Bu G_A; ring] at hGu
  have hGc := (hBc.add (hG.smul' 2 2)).div hLm
  rw [show (-2 * (3 + u) * (1 / (uc_t u c) ^ 3) +
        2 * (1 - c * (3 + u)) * (-3 / (2 * (uc_w u c * (uc_t u c) ^ 3))) + 2 * G_uc u c) /
      (2 + u - 2 * c) = G_c u c by unfold G_c G_Bc G_A; ring] at hGc
  have hGuu := (hBuu.sub (hGu.smul' 2 2)).div hLm
  rw [show ((2 * (-2 * c * (-(3 * (2 + u)) / (2 * (uc_w u c * (uc_t u c) ^ 3)))) +
        2 * (1 - c * (3 + u)) * ((-6 * uc_w u c + 21 * (2 + u) ^ 2) /
          (4 * (uc_w u c * (uc_w u c * (uc_t u c) ^ 3)))) +
        1 / (4 * ((4 + u) * Real.sqrt (4 + u)))) - 2 * G_u u c) / (2 + u - 2 * c) = G_uu u c by
      unfold G_uu G_Buu G_A; ring] at hGuu
  have hGuc := ((hBuc.add (hGu.smul' 2 2)).sub hGc).div hLm
  rw [show (-2 * (1 / (uc_t u c) ^ 3) +
        -2 * c * (-3 / (2 * (uc_w u c * (uc_t u c) ^ 3))) +
        -2 * (3 + u) * (-(3 * (2 + u)) / (2 * (uc_w u c * (uc_t u c) ^ 3))) +
        2 * (1 - c * (3 + u)) * (21 * (2 + u) / (4 * (uc_w u c * (uc_w u c * (uc_t u c) ^ 3)))) +
        2 * G_u u c - G_c u c) / (2 + u - 2 * c) = G_uc2 u c by
      unfold G_uc2 G_Buc G_A; ring] at hGuc
  have hGcc := (hBcc.add (hGc.smul' 4 4)).div hLm
  rw [show (2 * (-2 * (3 + u) * (-3 / (2 * (uc_w u c * (uc_t u c) ^ 3)))) +
        2 * (1 - c * (3 + u)) * (21 / (4 * (uc_w u c * (uc_w u c * (uc_t u c) ^ 3)))) +
        4 * G_c u c) / (2 + u - 2 * c) = G_cc u c by
      unfold G_cc G_Bcc G_A; ring] at hGcc
  have hup := hFc.neg.div hFu
  have hupp := (((hFuu.mul hup.sq).add ((hFuc.mul hup).smul' 2 2)).add hFcc).neg.div hFu
  have hup_u := hup.div hu
  have hterm1 := ((hupp.div hu).sub hup_u.sq).div (ivMem_int' 2 2)
  have hgdd := (((hGuu.mul hup.sq).add ((hGuc.mul hup).smul' 2 2)).add hGcc).add (hGu.mul hupp)
  have hgd := (hGu.mul hup).add hGc
  have hterm2 := (hgdd.div hG).sub (hgd.div hG).sq
  exact hterm1.add hterm2

/- Verified bounds from certificates + 3 analytic tails -/

lemma F_u_pos_on_grid {u c : ℝ} (hu1 : 0 ≤ u) (hu2 : u ≤ 16 / 100)
    (hc1 : -85 / 100 ≤ c) (hc2 : c ≤ 34 / 100) : 0 < F_u u c := by
  have h1 : ((0 : ℤ) : ℝ) ≤ u * 65536 := by push_cast; linarith
  have h2 : u * 65536 ≤ ((ivRat 16 100).hi : ℝ) := by
    have := (ivMem_rat 16 100) (by decide); push_cast at this; linarith
  have h3 : ((ivRat (-85) 100).lo : ℝ) ≤ c * 65536 := by
    have := (ivMem_rat (-85) 100) (by decide); push_cast at this; linarith
  have h4 : c * 65536 ≤ ((ivRat 34 100).hi : ℝ) := by
    have := (ivMem_rat 34 100) (by decide); push_cast at this; linarith
  obtain ⟨Iu, Ic, hIu, hIc, hpos⟩ := all_grid2 (by norm_num) (by norm_num) _ cert1_ok h1 h2 h3 h4
  exact (evalFuFc_sound hIu hIc).1.pos_of_isPos hpos

lemma F_det_pos_at_004 {c : ℝ} (hc1 : -85 / 100 ≤ c) (hc2 : c ≤ 34 / 100) :
    0 < F_det (4 / 100) c := by
  have h3 : ((ivRat (-85) 100).lo : ℝ) ≤ c * 65536 := by
    have := (ivMem_rat (-85) 100) (by decide); push_cast at this; linarith
  have h4 : c * 65536 ≤ ((ivRat 34 100).hi : ℝ) := by
    have := (ivMem_rat 34 100) (by decide); push_cast at this; linarith
  obtain ⟨Ic, hIc, hpos⟩ := all_grid1 (by norm_num) _ cert2_ok h3 h4
  exact (evalF_sound (ivMem_rat' 4 100 (4 / 100)) hIc).pos_of_isPos hpos

lemma F_det_pos_zero_left {c : ℝ} (hc1 : -85 / 100 ≤ c) (hc2 : c ≤ -75 / 100) :
    0 < F_det 0 c := by
  have h3 : ((ivRat (-85) 100).lo : ℝ) ≤ c * 65536 := by
    have := (ivMem_rat (-85) 100) (by decide); push_cast at this; linarith
  have h4 : c * 65536 ≤ ((ivRat (-75) 100).hi : ℝ) := by
    have := (ivMem_rat (-75) 100) (by decide); push_cast at this; linarith
  obtain ⟨Ic, hIc, hpos⟩ := all_grid1 (by norm_num) _ cert3a_ok h3 h4
  exact (evalF_sound (ivMem_int' 0 0) hIc).pos_of_isPos hpos

lemma F_det_pos_zero_right {c : ℝ} (hc1 : -15 / 100 ≤ c) (hc2 : c ≤ 34 / 100) :
    0 < F_det 0 c := by
  have h3 : ((ivRat (-15) 100).lo : ℝ) ≤ c * 65536 := by
    have := (ivMem_rat (-15) 100) (by decide); push_cast at this; linarith
  have h4 : c * 65536 ≤ ((ivRat 34 100).hi : ℝ) := by
    have := (ivMem_rat 34 100) (by decide); push_cast at this; linarith
  obtain ⟨Ic, hIc, hpos⟩ := all_grid1 (by norm_num) _ cert3b_ok h3 h4
  exact (evalF_sound (ivMem_int' 0 0) hIc).pos_of_isPos hpos

lemma F_cc_zero_pos {c : ℝ} (hc1 : -75 / 100 ≤ c) (hc2 : c ≤ -15 / 100) :
    0 < F_cc 0 c := by
  have h3 : ((ivRat (-75) 100).lo : ℝ) ≤ c * 65536 := by
    have := (ivMem_rat (-75) 100) (by decide); push_cast at this; linarith
  have h4 : c * 65536 ≤ ((ivRat (-15) 100).hi : ℝ) := by
    have := (ivMem_rat (-15) 100) (by decide); push_cast at this; linarith
  obtain ⟨Ic, hIc, hpos⟩ := all_grid1 (by norm_num) _ cert4_ok h3 h4
  exact (evalFcc0_sound hIc).pos_of_isPos hpos

lemma F_det_zero_mid_neg : F_det 0 (-1 / 2) < 0 :=
  (evalF_sound (ivMem_int' 0 0) (ivMem_rat' (-1) 2 (-1 / 2))).neg_of_isNeg cert4mid_ok

lemma hor_F_pos_on_B {u c : ℝ} (hu1 : 0 ≤ u) (hu2 : u ≤ 4 / 100)
    (hc1 : -75 / 100 ≤ c) (hc2 : c ≤ -15 / 100) : 0 < hor_F u c := by
  have h1 : ((0 : ℤ) : ℝ) ≤ u * 65536 := by push_cast; linarith
  have h2 : u * 65536 ≤ ((ivRat 4 100).hi : ℝ) := by
    have := (ivMem_rat 4 100) (by decide); push_cast at this; linarith
  have h3 : ((ivRat (-75) 100).lo : ℝ) ≤ c * 65536 := by
    have := (ivMem_rat (-75) 100) (by decide); push_cast at this; linarith
  have h4 : c * 65536 ≤ ((ivRat (-15) 100).hi : ℝ) := by
    have := (ivMem_rat (-15) 100) (by decide); push_cast at this; linarith
  obtain ⟨Iu, Ic, hIu, hIc, hpos⟩ := all_grid2 (by norm_num) (by norm_num) _ cert5_ok h1 h2 h3 h4
  exact (evalHor_sound hIu hIc).pos_of_isPos hpos

lemma F_det_pos_of_u_ge {u c : ℝ} (hu : 16 / 100 ≤ u) (hc1 : -1 < c) : 0 < F_det u c := by
  have hu0 : 0 ≤ u := by linarith
  have hw := uc_w_pos hu0 hc1; have ht := uc_t_pos hu0 hc1
  have hs : 0 < Real.sqrt (4 + u) := Real.sqrt_pos.mpr (by linarith)
  have hD0 : 0 < D0_m u c := by unfold D0_m; nlinarith [sq_nonneg c, sq_nonneg u]
  have hT0 : 0 < T0_m u c := by
    rw [T0_m_sq_form]
    have h1 : 0 ≤ (3 * c + 4 / 3) ^ 2 := sq_nonneg _
    have h2 : 16 < 24 + 8 * c := by linarith
    have hu20 : 16 / 100 * 20 ≤ u * (20 + 4 * u) := by nlinarith
    have h3 : 16 / 100 * (16 + 16 / 100 * 20) ≤ u * (24 + 8 * c + u * (20 + 4 * u)) := by nlinarith
    linarith
  unfold F_det; positivity

lemma F_det_pos_of_c_ge {u c : ℝ} (hu : 0 ≤ u) (hc : 34 / 100 ≤ c) : 0 < F_det u c := by
  have hc1 : -1 < c := by linarith
  have hw := uc_w_pos hu hc1; have ht := uc_t_pos hu hc1
  have hs : 0 < Real.sqrt (4 + u) := Real.sqrt_pos.mpr (by linarith)
  have hD0 : 0 < D0_m u c := by unfold D0_m; nlinarith [sq_nonneg u]
  have hT0 : 0 < T0_m u c := by unfold T0_m; nlinarith [sq_nonneg u]
  unfold F_det; positivity

lemma F_det_pos_of_c_le {u c : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 16 / 100)
    (hc1 : -1 < c) (hc2 : c ≤ -85 / 100) : 0 < F_det u c := by
  set a := 1 + c
  have ha0 : 0 < a := by linarith
  have ha1 : a ≤ 15 / 100 := by linarith
  have hc_eq : c = a - 1 := by ring
  have hw := uc_w_pos hu0 hc1; have ht := uc_t_pos hu0 hc1
  have hs_pos : 0 < Real.sqrt (4 + u) := Real.sqrt_pos.mpr (by linarith)
  have hs_le : Real.sqrt (4 + u) ≤ 21 / 10 := by
    have : (Real.sqrt (4 + u)) ^ 2 ≤ (21 / 10 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt (by linarith)]; linarith
    exact le_of_sq_le_sq this (by norm_num)
  have hD0 : 5 < D0_m u c := by
    unfold D0_m; rw [hc_eq]
    have : 9 * (a - 1) ^ 2 - 1 = 8 - 18 * a + 9 * a ^ 2 := by ring
    nlinarith [sq_nonneg a, sq_nonneg u]
  have hT0 : -10 * a ≤ T0_m u c := by
    unfold T0_m; rw [hc_eq]
    have : 9 * (a - 1) ^ 2 + 8 * (a - 1) - 1 + (24 + 8 * (a - 1)) * u + 20 * u ^ 2 + 4 * u ^ 3 =
        -10 * a + 9 * a ^ 2 + (16 + 8 * a) * u + 20 * u ^ 2 + 4 * u ^ 3 := by ring
    nlinarith [sq_nonneg a, sq_nonneg u]
  have h1 : -21 * a ≤ Real.sqrt (4 + u) * T0_m u c := by
    have hmul : Real.sqrt (4 + u) * (-10 * a) ≤ Real.sqrt (4 + u) * T0_m u c :=
      mul_le_mul_of_nonneg_left hT0 hs_pos.le
    nlinarith
  have hw_ge : 2 * a ≤ uc_w u c := by unfold uc_w; rw [hc_eq]; nlinarith [sq_nonneg u]
  have h5t : 21 * a < 5 * uc_t u c := by
    have ha3 : a ^ 3 ≤ (15 / 100 : ℝ) ^ 3 := pow_le_pow_left₀ ha0.le ha1 3
    have hpow : (21 * a) ^ 4 < (5 * uc_t u c) ^ 4 := by
      rw [mul_pow, mul_pow, uc_t_pow4 hu0 hc1]
      have : 21 ^ 4 * a ^ 4 = 194481 * a ^ 3 * a := by ring
      nlinarith
    by_contra hge; push Not at hge
    have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 5 * uc_t u c) hge 4
    linarith
  have h2 : 21 * a < uc_t u c * D0_m u c := by nlinarith
  unfold F_det
  have h3 : 0 < 2 * uc_w u c * (uc_t u c) ^ 3 := by positivity
  linarith

lemma F_det_strictMono_u {c : ℝ} (hc1 : -85 / 100 ≤ c) (hc2 : c ≤ 34 / 100) :
    StrictMonoOn (fun u => F_det u c) (Set.Icc 0 (16 / 100)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (16 / 100))
  · intro u hu
    have hw : 0 < uc_w u c := uc_w_pos hu.1 (by linarith)
    exact (hasDerivAt_x_of_lin2 (hasFDerivAt_F_det (by linarith [hu.1]) hw)).continuousAt.continuousWithinAt
  · intro u hu; rw [interior_Icc] at hu
    have hw : 0 < uc_w u c := uc_w_pos hu.1.le (by linarith)
    rw [(hasDerivAt_x_of_lin2 (hasFDerivAt_F_det (by linarith [hu.1]) hw)).deriv]
    exact F_u_pos_on_grid hu.1.le hu.2.le hc1 hc2

lemma F_det_pos_outside_B {u c : ℝ} (hu : 0 ≤ u) (hc1 : -1 < c) (_hc2 : c < 1)
    (hout : 4 / 100 ≤ u ∨ c ≤ -75 / 100 ∨ -15 / 100 ≤ c) : 0 < F_det u c := by
  by_cases hu16 : 16 / 100 ≤ u
  · exact F_det_pos_of_u_ge hu16 hc1
  push Not at hu16
  by_cases hc34 : 34 / 100 ≤ c
  · exact F_det_pos_of_c_ge hu hc34
  push Not at hc34
  by_cases hc85 : c ≤ -85 / 100
  · exact F_det_pos_of_c_le hu hu16.le hc1 hc85
  push Not at hc85
  have hmono := F_det_strictMono_u hc85.le hc34.le
  rcases hout with hu04 | hc75 | hc15
  · exact lt_of_lt_of_le (F_det_pos_at_004 hc85.le hc34.le)
      (hmono.monotoneOn ⟨by norm_num, by norm_num⟩ ⟨hu, hu16.le⟩ hu04)
  · exact lt_of_lt_of_le (F_det_pos_zero_left hc85.le hc75)
      (hmono.monotoneOn ⟨le_rfl, by norm_num⟩ ⟨hu, hu16.le⟩ hu)
  · exact lt_of_lt_of_le (F_det_pos_zero_right hc15 hc34.le)
      (hmono.monotoneOn ⟨le_rfl, by norm_num⟩ ⟨hu, hu16.le⟩ hu)

/- Universal 15-line elementary implicit-curve differentiation lemma -/

lemma implicit_hasDerivAt {Φ : ℝ × ℝ → ℝ} {a b K : ℝ} {g : ℝ → ℝ} {t₀ : ℝ}
    (hΦ : HasFDerivAt Φ (lin2 a b) (g t₀, t₀)) (ha : a ≠ 0)
    (heq : ∀ᶠ t in nhds t₀, Φ (g t, t) = K)
    (hcont : ContinuousAt g t₀) :
    HasDerivAt g (-b / a) t₀ := by
  have h0 : Φ (g t₀, t₀) = K := heq.self_of_nhds
  have hq : Filter.Tendsto (fun t => (g t, t)) (nhds t₀) (nhds (g t₀, t₀)) :=
    hcont.prodMk continuousAt_id
  have hlo1 : (fun t => Φ (g t, t) - Φ (g t₀, t₀) - (a * (g t - g t₀) + b * (t - t₀))) =o[nhds t₀]
      (fun t => (g t, t) - (g t₀, t₀)) := by
    have h := hΦ.isLittleO.comp_tendsto hq
    refine h.congr' (Filter.Eventually.of_forall fun t => ?_) (Filter.Eventually.of_forall fun _ => rfl)
    simp [lin2]
  have hlo2 : (fun t => -(a * (g t - g t₀) + b * (t - t₀))) =o[nhds t₀]
      (fun t => (g t, t) - (g t₀, t₀)) := by
    refine hlo1.congr' (heq.mono fun t ht => ?_) (Filter.Eventually.of_forall fun _ => rfl)
    dsimp only; rw [ht, h0, sub_self, zero_sub]
  have hbig : (fun t => (g t, t) - (g t₀, t₀)) =O[nhds t₀] (fun t => t - t₀) := by
    have ha_pos : 0 < |a| / 2 := by positivity
    have hbd := hlo2.bound ha_pos
    rw [Asymptotics.isBigO_iff]
    refine ⟨(2 * |b| + |a|) / |a| + 1, hbd.mono fun t ht => ?_⟩
    have hnorm_prod : ‖(g t, t) - (g t₀, t₀)‖ = max |g t - g t₀| |t - t₀| := by
      simp [Prod.norm_def, Real.norm_eq_abs]
    have hnorm_lhs : ‖-(a * (g t - g t₀) + b * (t - t₀))‖ = |a * (g t - g t₀) + b * (t - t₀)| := by
      rw [norm_neg, Real.norm_eq_abs]
    rw [hnorm_prod, hnorm_lhs] at ht
    have hle_sum : max |g t - g t₀| |t - t₀| ≤ |g t - g t₀| + |t - t₀| :=
      max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
    have htri : |a| * |g t - g t₀| - |b| * |t - t₀| ≤ |a * (g t - g t₀) + b * (t - t₀)| := by
      have h1 := abs_sub_abs_le_abs_add (a * (g t - g t₀)) (b * (t - t₀))
      rw [abs_mul, abs_mul] at h1; exact h1
    have hstep : |a| / 2 * |g t - g t₀| ≤ (|b| + |a| / 2) * |t - t₀| := by nlinarith
    have hdg : |g t - g t₀| ≤ ((2 * |b| + |a|) / |a|) * |t - t₀| := by
      have ha' : 0 < |a| := abs_pos.mpr ha
      rw [show ((2 * |b| + |a|) / |a|) * |t - t₀| = ((|b| + |a| / 2) * |t - t₀|) / (|a| / 2) by
        field_simp [ha'.ne']]
      exact (le_div_iff₀ ha_pos).mpr (by linarith)
    rw [hnorm_prod, Real.norm_eq_abs]
    have hnn : 0 ≤ (2 * |b| + |a|) / |a| := by positivity
    exact max_le (by nlinarith [abs_nonneg (t - t₀)]) (by nlinarith [abs_nonneg (t - t₀)])
  have hlo3 := hlo2.trans_isBigO hbig
  have hlo4 := hlo3.const_mul_left (-(1 / a))
  rw [hasDerivAt_iff_isLittleO]
  refine hlo4.congr' (Filter.Eventually.of_forall fun t => ?_) (Filter.Eventually.of_forall fun _ => rfl)
  simp only [smul_eq_mul]; field_simp [ha]; ring

/- Exact inverse map (u, c) ↦ (x, y) for u > 0, c ∈ (-1, 1) -/

lemma exists_xy_of_uc {u c : ℝ} (hu : 0 < u) (hc1 : -1 < c) (hc2 : c < 1) :
    ∃ x y : ℝ, x < 0 ∧ 0 < y ∧ uc_u x y = u ∧ uc_c x y = c := by
  set Lm := 2 + u - 2 * c
  have hLm : 0 < Lm := by linarith
  have h1c : 0 < 1 - c ^ 2 := by nlinarith
  have h4u : 0 < u * (4 + u) := by positivity
  set x := -Real.sqrt (u * (4 + u)) / Lm
  set y := 2 * Real.sqrt (1 - c ^ 2) / Lm
  have hx_neg : x < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr (Real.sqrt_pos.mpr h4u)) hLm
  have hy_pos : 0 < y := div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr h1c)) hLm
  have hx2y2 : x ^ 2 + y ^ 2 = (2 + u + 2 * c) / Lm := by
    simp only [x, y, div_pow, neg_sq, mul_pow, Real.sq_sqrt h4u.le, Real.sq_sqrt h1c.le]
    field_simp [hLm.ne']; unfold Lm; ring
  have hLm_sq : (Real.sqrt Lm) ^ 2 = Lm := Real.sq_sqrt hLm.le
  have hsu : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt hu.le
  have hs4u : (Real.sqrt (4 + u)) ^ 2 = 4 + u := Real.sq_sqrt (by linarith)
  have hdiff_pos : 0 < Real.sqrt (4 + u) - Real.sqrt u := by
    have : Real.sqrt u < Real.sqrt (4 + u) := Real.sqrt_lt_sqrt hu.le (by linarith)
    linarith
  have hmul_sq : Real.sqrt (u * (4 + u)) = Real.sqrt u * Real.sqrt (4 + u) :=
    Real.sqrt_mul hu.le (4 + u)
  have hr1_eq : r1 x y = (Real.sqrt (4 + u) - Real.sqrt u) / Real.sqrt Lm := by
    have h1 : (r1 x y) ^ 2 = ((Real.sqrt (4 + u) - Real.sqrt u) / Real.sqrt Lm) ^ 2 := by
      rw [r1_sq]
      calc (x + 1) ^ 2 + y ^ 2 = (x ^ 2 + y ^ 2) + 2 * x + 1 := by ring
        _ = (2 + u + 2 * c) / Lm + 2 * (-Real.sqrt (u * (4 + u)) / Lm) + 1 := by rw [hx2y2]
        _ = ((4 + u) + u - 2 * (Real.sqrt u * Real.sqrt (4 + u))) / Lm := by
            rw [hmul_sq]; field_simp [hLm.ne']; unfold Lm; ring
        _ = ((Real.sqrt (4 + u) - Real.sqrt u) / Real.sqrt Lm) ^ 2 := by
            rw [div_pow, hLm_sq]; congr 1; nlinarith [hsu, hs4u]
    have hr1p := r1_pos x hy_pos
    have hrhs : 0 < (Real.sqrt (4 + u) - Real.sqrt u) / Real.sqrt Lm :=
      div_pos hdiff_pos (Real.sqrt_pos.mpr hLm)
    nlinarith
  have hr2_eq : r2 x y = (Real.sqrt (4 + u) + Real.sqrt u) / Real.sqrt Lm := by
    have h2 : (r2 x y) ^ 2 = ((Real.sqrt (4 + u) + Real.sqrt u) / Real.sqrt Lm) ^ 2 := by
      rw [r2_sq]
      calc (x - 1) ^ 2 + y ^ 2 = (x ^ 2 + y ^ 2) - 2 * x + 1 := by ring
        _ = (2 + u + 2 * c) / Lm - 2 * (-Real.sqrt (u * (4 + u)) / Lm) + 1 := by rw [hx2y2]
        _ = ((4 + u) + u + 2 * (Real.sqrt u * Real.sqrt (4 + u))) / Lm := by
            rw [hmul_sq]; field_simp [hLm.ne']; unfold Lm; ring
        _ = ((Real.sqrt (4 + u) + Real.sqrt u) / Real.sqrt Lm) ^ 2 := by
            rw [div_pow, hLm_sq]; congr 1; nlinarith [hsu, hs4u]
    have hr2p := r2_pos x hy_pos
    have hrhs : 0 < (Real.sqrt (4 + u) + Real.sqrt u) / Real.sqrt Lm :=
      div_pos (by positivity) (Real.sqrt_pos.mpr hLm)
    nlinarith
  have hP : r1 x y * r2 x y = 4 / Lm := by
    rw [hr1_eq, hr2_eq, div_mul_div_comm, ← sq, hLm_sq]
    congr 1; nlinarith [hsu, hs4u]
  refine ⟨x, y, hx_neg, hy_pos, ?_, ?_⟩
  · unfold uc_u; rw [r1_sq, r2_sq, hP]
    calc ((x + 1) ^ 2 + y ^ 2 + ((x - 1) ^ 2 + y ^ 2)) / (4 / Lm) - 2
        = (2 * (x ^ 2 + y ^ 2) + 2) / (4 / Lm) - 2 := by ring
      _ = (2 * ((2 + u + 2 * c) / Lm) + 2) / (4 / Lm) - 2 := by rw [hx2y2]
      _ = u := by field_simp [hLm.ne']; unfold Lm; ring
  · unfold uc_c; rw [hP, hx2y2]; field_simp [hLm.ne']; unfold Lm; ring

/- Section 5c: Axis roots (c_bot, c_top), curve (u_Γ, y_Γ, U_Γ), unimodality & convexity -/

lemma strict_convex_neg_between {f f' f'' : ℝ → ℝ} {a b c₁ c c₂ : ℝ}
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a b, HasDerivAt f' (f'' x) x)
    (hpos : ∀ x ∈ Set.Icc a b, 0 < f'' x)
    (ha : a ≤ c₁) (h1 : c₁ < c) (h2 : c < c₂) (hb : c₂ ≤ b)
    (hf1 : f c₁ ≤ 0) (hf2 : f c₂ ≤ 0) : f c < 0 := by
  have hmono : StrictMonoOn f' (Set.Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    · exact fun x hx => (hf' x hx).continuousAt.continuousWithinAt
    · intro x hx; rw [interior_Icc] at hx
      rw [(hf' x ⟨hx.1.le, hx.2.le⟩).deriv]; exact hpos x ⟨hx.1.le, hx.2.le⟩
  have hc1 : ContinuousOn f (Set.Icc c₁ c) := fun x hx =>
    (hf x ⟨le_trans ha hx.1, le_trans hx.2 (le_trans h2.le hb)⟩).continuousAt.continuousWithinAt
  have hd1 : ∀ x ∈ Set.Ioo c₁ c, HasDerivAt f (f' x) x := fun x hx =>
    hf x ⟨le_trans ha hx.1.le, le_trans hx.2.le (le_trans h2.le hb)⟩
  obtain ⟨ξ₁, hξ₁, hslope1⟩ := exists_hasDerivAt_eq_slope f f' h1 hc1 hd1
  have hc2 : ContinuousOn f (Set.Icc c c₂) := fun x hx =>
    (hf x ⟨le_trans ha (le_trans h1.le hx.1), le_trans hx.2 hb⟩).continuousAt.continuousWithinAt
  have hd2 : ∀ x ∈ Set.Ioo c c₂, HasDerivAt f (f' x) x := fun x hx =>
    hf x ⟨le_trans ha (le_trans h1.le hx.1.le), le_trans hx.2.le hb⟩
  obtain ⟨ξ₂, hξ₂, hslope2⟩ := exists_hasDerivAt_eq_slope f f' h2 hc2 hd2
  have hlt : f' ξ₁ < f' ξ₂ :=
    hmono ⟨le_trans ha hξ₁.1.le, le_trans hξ₁.2.le (le_trans h2.le hb)⟩
      ⟨le_trans ha (le_trans h1.le hξ₂.1.le), le_trans hξ₂.2.le hb⟩ (lt_trans hξ₁.2 hξ₂.1)
  rw [hslope1, hslope2, div_lt_div_iff₀ (by linarith) (by linarith)] at hlt
  have hstep : f c * (c₂ - c₁) < f c₁ * (c₂ - c) + f c₂ * (c - c₁) := by linarith
  have hrhs : f c₁ * (c₂ - c) + f c₂ * (c - c₁) ≤ 0 := by nlinarith
  nlinarith

lemma exists_c_bot_c_top :
    ∃ c_bot c_top : ℝ,
      -75 / 100 < c_bot ∧ c_bot < -1 / 2 ∧ -1 / 2 < c_top ∧ c_top < -15 / 100 ∧
      F_det 0 c_bot = 0 ∧ F_det 0 c_top = 0 ∧
      (∀ c, -1 < c → c < 1 →
        (F_det 0 c < 0 ↔ c_bot < c ∧ c < c_top) ∧
        (0 < F_det 0 c ↔ c < c_bot ∨ c_top < c) ∧
        (F_det 0 c = 0 ↔ c = c_bot ∨ c = c_top)) := by
  have hf : ∀ c ∈ Set.Icc (-75 / 100 : ℝ) (-15 / 100),
      HasDerivAt (fun t => F_det 0 t) (F_c 0 c) c := fun c hc =>
    hasDerivAt_y_of_lin2 (hasFDerivAt_F_det (by norm_num) (uc_w_pos le_rfl (by linarith [hc.1])))
  have hf' : ∀ c ∈ Set.Icc (-75 / 100 : ℝ) (-15 / 100),
      HasDerivAt (fun t => F_c 0 t) (F_cc 0 c) c := fun c hc =>
    hasDerivAt_y_of_lin2 (hasFDerivAt_F_c (by norm_num) (uc_w_pos le_rfl (by linarith [hc.1])))
  have hf'' : ∀ c ∈ Set.Icc (-75 / 100 : ℝ) (-15 / 100), 0 < F_cc 0 c := fun c hc =>
    F_cc_zero_pos hc.1 hc.2
  have hcont : ContinuousOn (fun t => F_det 0 t) (Set.Icc (-75 / 100) (-15 / 100)) :=
    fun c hc => (hf c hc).continuousAt.continuousWithinAt
  have hL : 0 < F_det 0 (-75 / 100) := F_det_pos_zero_left (by norm_num) le_rfl
  have hM : F_det 0 (-1 / 2) < 0 := F_det_zero_mid_neg
  have hR : 0 < F_det 0 (-15 / 100) := F_det_pos_zero_right le_rfl (by norm_num)
  obtain ⟨c_bot, hcb_Icc, hcb_eq⟩ := intermediate_value_Icc' (by norm_num : (-75 / 100 : ℝ) ≤ -1 / 2)
    (hcont.mono (Set.Icc_subset_Icc le_rfl (by norm_num))) ⟨hM.le, hL.le⟩
  obtain ⟨c_top, hct_Icc, hct_eq⟩ := intermediate_value_Icc (by norm_num : (-1 / 2 : ℝ) ≤ -15 / 100)
    (hcont.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)) ⟨hM.le, hR.le⟩
  dsimp only at hcb_eq hct_eq
  have hcb1 : -75 / 100 < c_bot := lt_of_le_of_ne hcb_Icc.1 (by rintro rfl; linarith)
  have hcb2 : c_bot < -1 / 2 := lt_of_le_of_ne hcb_Icc.2 (by rintro rfl; linarith)
  have hct1 : -1 / 2 < c_top := lt_of_le_of_ne hct_Icc.1 (by rintro rfl; linarith)
  have hct2 : c_top < -15 / 100 := lt_of_le_of_ne hct_Icc.2 (by rintro rfl; linarith)
  refine ⟨c_bot, c_top, hcb1, hcb2, hct1, hct2, hcb_eq, hct_eq, ?_⟩
  intro c hc1 hc2
  have hneg : c_bot < c → c < c_top → F_det 0 c < 0 := fun h1 h2 =>
    strict_convex_neg_between hf hf' hf'' hcb1.le h1 h2 hct2.le hcb_eq.le hct_eq.le
  have hpos_l : c < c_bot → 0 < F_det 0 c := by
    intro hlt
    by_cases h75 : c ≤ -75 / 100
    · exact F_det_pos_outside_B le_rfl hc1 hc2 (Or.inr (Or.inl h75))
    push Not at h75
    by_contra hle; push Not at hle
    have := strict_convex_neg_between hf hf' hf'' h75.le hlt (lt_trans hcb2 hct1) hct2.le hle hct_eq.le
    linarith
  have hpos_r : c_top < c → 0 < F_det 0 c := by
    intro hgt
    by_cases h15 : -15 / 100 ≤ c
    · exact F_det_pos_outside_B le_rfl hc1 hc2 (Or.inr (Or.inr h15))
    push Not at h15
    by_contra hle; push Not at hle
    have := strict_convex_neg_between hf hf' hf'' hcb1.le (lt_trans hcb2 hct1) hgt h15.le hcb_eq.le hle
    linarith
  refine ⟨⟨?_, fun ⟨h1, h2⟩ => hneg h1 h2⟩, ⟨?_, fun h => h.elim hpos_l hpos_r⟩, ⟨?_, ?_⟩⟩
  · intro h; constructor
    · by_contra hle; push Not at hle
      rcases eq_or_lt_of_le hle with rfl | hlt
      · linarith
      · linarith [hpos_l hlt]
    · by_contra hge; push Not at hge
      rcases eq_or_lt_of_le hge with rfl | hgt
      · linarith
      · linarith [hpos_r hgt]
  · intro h
    by_contra hnot; push Not at hnot
    rcases eq_or_lt_of_le hnot.1 with rfl | h1
    · linarith
    · rcases eq_or_lt_of_le hnot.2 with rfl | h2
      · linarith
      · linarith [hneg h1 h2]
  · intro h
    rcases lt_trichotomy c c_bot with h1 | rfl | h1
    · linarith [hpos_l h1]
    · exact Or.inl rfl
    · rcases lt_trichotomy c c_top with h2 | rfl | h2
      · linarith [hneg h1 h2]
      · exact Or.inr rfl
      · linarith [hpos_r h2]
  · rintro (rfl | rfl) <;> assumption

noncomputable def c_bot_val : ℝ := Classical.choose exists_c_bot_c_top
noncomputable def c_top_val : ℝ := Classical.choose (Classical.choose_spec exists_c_bot_c_top)
noncomputable def y_bot_val : ℝ := Real.sqrt ((1 + c_bot_val) / (1 - c_bot_val))
noncomputable def y0_val : ℝ := Classical.choose exists_unique_y0

lemma c_bot_top_spec :
    -75 / 100 < c_bot_val ∧ c_bot_val < -1 / 2 ∧ -1 / 2 < c_top_val ∧ c_top_val < -15 / 100 ∧
    F_det 0 c_bot_val = 0 ∧ F_det 0 c_top_val = 0 ∧
    (∀ c, -1 < c → c < 1 →
      (F_det 0 c < 0 ↔ c_bot_val < c ∧ c < c_top_val) ∧
      (0 < F_det 0 c ↔ c < c_bot_val ∨ c_top_val < c) ∧
      (F_det 0 c = 0 ↔ c = c_bot_val ∨ c = c_top_val)) :=
  Classical.choose_spec (Classical.choose_spec exists_c_bot_c_top)

lemma y0_val_spec :
    1 / 2 < y0_val ∧ y0_val < 1 ∧ uX_xy 0 y0_val = 0 ∧
    (∀ y, 0 < y → y < y0_val → uX_xy 0 y < 0) ∧
    (∀ y, y0_val < y → 0 < uX_xy 0 y) :=
  Classical.choose_spec exists_unique_y0

lemma uc_c_y_bot : 0 < y_bot_val ∧ uc_c 0 y_bot_val = c_bot_val := by
  have hcb := c_bot_top_spec
  have hpos : 0 < (1 + c_bot_val) / (1 - c_bot_val) := div_pos (by linarith) (by linarith)
  have hyb : 0 < y_bot_val := Real.sqrt_pos.mpr hpos
  refine ⟨hyb, ?_⟩
  rw [uc_c_axis_eq hyb]
  have hsq : y_bot_val ^ 2 = (1 + c_bot_val) / (1 - c_bot_val) := Real.sq_sqrt hpos.le
  rw [hsq]
  have h1 : 1 - c_bot_val ≠ 0 := by linarith
  field_simp [h1]; ring

lemma uc_c_y0_eq_c_top : uc_c 0 y0_val = c_top_val := by
  have hy0 := y0_val_spec
  have hy0p : 0 < y0_val := by linarith
  have hdet0 : det_uc (uc_u 0 y0_val) (uc_c 0 y0_val) = 0 := by
    rw [← det_xy_eq_uc 0 hy0p, hy0.2.2.1, zero_mul, uY_xy_eq_uc 0 hy0p, r1, r2]; simp
  have hu0 : uc_u 0 y0_val = 0 := (uc_u_eq_zero_iff 0 hy0p).mpr rfl
  rw [hu0] at hdet0
  have hc := uc_c_bounds 0 hy0p
  have hw := uc_w_pos le_rfl hc.1; have ht := uc_t_pos le_rfl hc.1
  have hF0 : F_det 0 (uc_c 0 y0_val) = 0 := by
    unfold det_uc at hdet0
    have hden : 2 * uc_w 0 (uc_c 0 y0_val) * (uc_t 0 (uc_c 0 y0_val)) ^ 3 ≠ 0 := by positivity
    exact (div_eq_zero_iff.mp hdet0).resolve_right hden
  have hroots := (c_bot_top_spec.2.2.2.2.2.2 (uc_c 0 y0_val) hc.1 hc.2).2.2.mp hF0
  have hy_s3 : 1 / Real.sqrt 3 < y0_val := by
    set ys := 1 / Real.sqrt 3
    have hys : 0 < ys := by positivity
    have hcs : uc_c 0 ys = -1 / 2 := by
      rw [uc_c_axis_eq hys]
      have hsq : ys ^ 2 = 1 / 3 := by simp [ys]
      rw [hsq]; norm_num
    have huxs : uX_xy 0 ys < 0 := by
      rw [uX_axis_eq hys, hcs]
      have ht1 : uc_t 0 (-1 / 2) = 1 := by unfold uc_t uc_w; norm_num
      rw [ht1]; norm_num
    by_contra hge; push Not at hge
    rcases eq_or_lt_of_le hge with heq | hgt
    · rw [← heq] at huxs; linarith [hy0.2.2.1]
    · linarith [hy0.2.2.2.2 ys hgt]
  have hcgt : -1 / 2 < uc_c 0 y0_val := by
    rw [uc_c_axis_eq hy0p]
    have hsq : 1 / 3 < y0_val ^ 2 := by
      have : (1 / Real.sqrt 3 : ℝ) ^ 2 = 1 / 3 := by rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
      nlinarith [show (0 : ℝ) < 1 / Real.sqrt 3 by positivity]
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  rcases hroots with h | h
  · linarith [c_bot_top_spec.2.1]
  · exact h

lemma y_bot_lt_y0 : y_bot_val < y0_val := by
  have hyb := uc_c_y_bot
  have hy0p : 0 < y0_val := by linarith [y0_val_spec.1]
  have hclt : uc_c 0 y_bot_val < uc_c 0 y0_val := by
    rw [hyb.2, uc_c_y0_eq_c_top]; linarith [c_bot_top_spec.2.1, c_bot_top_spec.2.2.1]
  rw [uc_c_axis_eq hyb.1, uc_c_axis_eq hy0p, div_lt_div_iff₀ (by positivity) (by positivity)] at hclt
  nlinarith

lemma det_xy_axis_sign {y : ℝ} (hy : 0 < y) :
    (uX_xy 0 y * vY_xy 0 y - uY_xy 0 y * vX_xy 0 y < 0 ↔ y_bot_val < y ∧ y < y0_val) ∧
    (0 < uX_xy 0 y * vY_xy 0 y - uY_xy 0 y * vX_xy 0 y ↔ y < y_bot_val ∨ y0_val < y) := by
  rw [det_xy_eq_uc 0 hy, (uc_u_eq_zero_iff 0 hy).mpr rfl]
  have hc := uc_c_bounds 0 hy
  have hw := uc_w_pos le_rfl hc.1; have ht := uc_t_pos le_rfl hc.1
  have hden : 0 < 2 * uc_w 0 (uc_c 0 y) * (uc_t 0 (uc_c 0 y)) ^ 3 := by positivity
  have hspec := c_bot_top_spec.2.2.2.2.2.2 (uc_c 0 y) hc.1 hc.2
  have hcy_iff : ∀ y' > 0, (uc_c 0 y < uc_c 0 y' ↔ y < y') := by
    intro y' hy'
    rw [uc_c_axis_eq hy, uc_c_axis_eq hy', div_lt_div_iff₀ (by positivity) (by positivity)]
    constructor <;> intro h <;> nlinarith
  have hcy_iff2 : ∀ y' > 0, (uc_c 0 y' < uc_c 0 y ↔ y' < y) := by
    intro y' hy'
    rw [uc_c_axis_eq hy, uc_c_axis_eq hy', div_lt_div_iff₀ (by positivity) (by positivity)]
    constructor <;> intro h <;> nlinarith
  have hy0p : 0 < y0_val := by linarith [y0_val_spec.1]
  unfold det_uc
  rw [div_neg_iff, div_pos_iff]
  constructor
  · constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
      · linarith
      · have ⟨ha, hb⟩ := hspec.1.mp h1
        rw [← uc_c_y_bot.2] at ha; rw [← uc_c_y0_eq_c_top] at hb
        exact ⟨(hcy_iff2 y_bot_val uc_c_y_bot.1).mp ha, (hcy_iff y0_val hy0p).mp hb⟩
    · rintro ⟨h1, h2⟩
      right; refine ⟨hspec.1.mpr ⟨?_, ?_⟩, hden⟩
      · rw [← uc_c_y_bot.2]; exact (hcy_iff2 y_bot_val uc_c_y_bot.1).mpr h1
      · rw [← uc_c_y0_eq_c_top]; exact (hcy_iff y0_val hy0p).mpr h2
  · constructor
    · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · rcases hspec.2.1.mp h1 with h | h
        · rw [← uc_c_y_bot.2] at h; exact Or.inl ((hcy_iff y_bot_val uc_c_y_bot.1).mp h)
        · rw [← uc_c_y0_eq_c_top] at h; exact Or.inr ((hcy_iff2 y0_val hy0p).mp h)
      · linarith
    · intro h; left; refine ⟨hspec.2.1.mpr ?_, hden⟩
      rcases h with h | h
      · left; rw [← uc_c_y_bot.2]; exact (hcy_iff y_bot_val uc_c_y_bot.1).mpr h
      · right; rw [← uc_c_y0_eq_c_top]; exact (hcy_iff2 y0_val hy0p).mpr h

/- Horizontal derivative of F_det (uc_u x y) (uc_c x y) & horizontal det_xy sign structure -/

lemma hasDerivAt_F_det_x {x y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => F_det (uc_u t y) (uc_c t y))
      (2 * x / (r1 x y * r2 x y) * hor_F (uc_u x y) (uc_c x y)) x := by
  have hr1 := r1_pos x hy; have hr2 := r2_pos x hy
  have hP : 0 < r1 x y * r2 x y := mul_pos hr1 hr2
  have h1ne := hr1.ne'; have h2ne := hr2.ne'; have hPne := hP.ne'
  have hr1d : HasDerivAt (fun t => r1 t y) ((x + 1) / r1 x y) x := by
    unfold r1
    have h0 : (x + 1) ^ 2 + y ^ 2 ≠ 0 := by positivity
    exact ((((hasDerivAt_id x).add_const 1).pow 2).add_const (y ^ 2)).sqrt h0 |>.congr_deriv (by
      simp; field_simp [h1ne])
  have hr2d : HasDerivAt (fun t => r2 t y) ((x - 1) / r2 x y) x := by
    unfold r2
    have h0 : (x - 1) ^ 2 + y ^ 2 ≠ 0 := by positivity
    exact ((((hasDerivAt_id x).sub_const 1).pow 2).add_const (y ^ 2)).sqrt h0 |>.congr_deriv (by
      simp; field_simp [h2ne])
  have hsq : (r1 x y * r2 x y) ^ 2 = (x ^ 2 + y ^ 2 - 1) ^ 2 + 4 * y ^ 2 := by
    rw [mul_pow, r1_sq, r2_sq]; ring
  have hPd : HasDerivAt (fun t => r1 t y * r2 t y)
      (2 * x * (x ^ 2 + y ^ 2 - 1) / (r1 x y * r2 x y)) x :=
    (hr1d.mul hr2d).congr_deriv (by
      field_simp [h1ne, h2ne]; linear_combination (x + 1) * r2_sq x y + (x - 1) * r1_sq x y)
  have h_num_u : HasDerivAt (fun t => (r1 t y) ^ 2 + (r2 t y) ^ 2) (4 * x) x := by
    have hfun : (fun t => (r1 t y) ^ 2 + (r2 t y) ^ 2) = fun t => 2 * t ^ 2 + (2 * y ^ 2 + 2) := by
      ext t; linarith [r1_sq t y, r2_sq t y]
    rw [hfun]
    exact (((hasDerivAt_pow 2 x).const_mul 2).add_const (2 * y ^ 2 + 2)).congr_deriv (by norm_num; ring)
  have hud : HasDerivAt (fun t => uc_u t y)
      (2 * x / (r1 x y * r2 x y) * (2 - uc_c x y * (2 + uc_u x y))) x := by
    unfold uc_u
    exact ((h_num_u.div hPd hPne).sub_const 2).congr_deriv (by
      have hc_eq : uc_c x y = (x ^ 2 + y ^ 2 - 1) / (r1 x y * r2 x y) := rfl
      rw [hc_eq]; field_simp [h1ne, h2ne, hPne]; ring)
  have hcd : HasDerivAt (fun t => uc_c t y)
      (2 * x / (r1 x y * r2 x y) * (1 - (uc_c x y) ^ 2)) x := by
    unfold uc_c
    have hnum : HasDerivAt (fun t => t ^ 2 + y ^ 2 - 1) (2 * x) x :=
      (((hasDerivAt_pow 2 x).add_const (y ^ 2)).sub_const 1).congr_deriv (by simp)
    exact (hnum.div hPd hPne).congr_deriv (by
      have h1 : 1 - ((x ^ 2 + y ^ 2 - 1) / (r1 x y * r2 x y)) ^ 2 = (2 * y / (r1 x y * r2 x y)) ^ 2 :=
        uc_one_sub_c_sq x hy
      rw [h1]; field_simp [h1ne, h2ne, hPne]
      rw [r1_sq, r2_sq]; ring)
  have hu := uc_u_nonneg x hy; have hc := uc_c_bounds x hy
  have hw := uc_w_pos hu hc.1
  exact (hasDerivAt_comp_lin2 (g := fun t => uc_u t y) (h := fun t => uc_c t y)
    (hasFDerivAt_F_det (by linarith) hw) hud hcd).congr_deriv (by unfold hor_F; ring)

lemma F_det_pos_of_nonneg_x_ge {y a : ℝ} (hy : 0 < y) (ha : 0 ≤ a)
    (hge : 0 ≤ F_det (uc_u a y) (uc_c a y)) :
    ∀ x, a < x → 0 < F_det (uc_u x y) (uc_c x y) := by
  apply pos_of_nonneg_of_deriv_pos_on_nonpos
  · exact fun x _ => (hasDerivAt_F_det_x hy).continuousAt.continuousWithinAt
  · intro x hax hle
    have hxpos : 0 < x := by linarith
    have hu := uc_u_nonneg x hy; have hc := uc_c_bounds x hy
    have hB : uc_u x y < 4 / 100 ∧ -75 / 100 < uc_c x y ∧ uc_c x y < -15 / 100 := by
      by_contra hnot
      have hout : 4 / 100 ≤ uc_u x y ∨ uc_c x y ≤ -75 / 100 ∨ -15 / 100 ≤ uc_c x y := by
        by_cases h1 : 4 / 100 ≤ uc_u x y
        · exact Or.inl h1
        · by_cases h2 : uc_c x y ≤ -75 / 100
          · exact Or.inr (Or.inl h2)
          · by_cases h3 : -15 / 100 ≤ uc_c x y
            · exact Or.inr (Or.inr h3)
            · exact absurd ⟨lt_of_not_ge h1, lt_of_not_ge h2, lt_of_not_ge h3⟩ hnot
      linarith [F_det_pos_outside_B hu hc.1 hc.2 hout]
    have hhor := hor_F_pos_on_B hu hB.1.le hB.2.1.le hB.2.2.le
    refine ⟨_, mul_pos (div_pos (by linarith) (mul_pos (r1_pos x hy) (r2_pos x hy))) hhor,
      hasDerivAt_F_det_x hy⟩
  · exact hge

lemma det_xy_pos_outside_y_band {x y : ℝ} (hy : 0 < y) (hx : x ≠ 0)
    (hout : y ≤ y_bot_val ∨ y0_val ≤ y) :
    0 < uX_xy x y * vY_xy x y - uY_xy x y * vX_xy x y := by
  have h0 : 0 ≤ F_det (uc_u 0 y) (uc_c 0 y) := by
    have hneg := (det_xy_axis_sign hy).1
    have hge : 0 ≤ uX_xy 0 y * vY_xy 0 y - uY_xy 0 y * vX_xy 0 y := by
      by_contra hlt; push Not at hlt
      have ⟨h1, h2⟩ := hneg.mp hlt; rcases hout with h | h <;> linarith
    rw [det_xy_eq_uc 0 hy] at hge; unfold det_uc at hge
    have hc := uc_c_bounds 0 hy; have hu := uc_u_nonneg 0 hy
    have hden : 0 < 2 * uc_w (uc_u 0 y) (uc_c 0 y) * (uc_t (uc_u 0 y) (uc_c 0 y)) ^ 3 := by
      have := uc_w_pos hu hc.1; have := uc_t_pos hu hc.1; positivity
    have hmul := mul_nonneg hge hden.le
    rwa [div_mul_cancel₀ _ hden.ne'] at hmul
  have hFpos : 0 < F_det (uc_u x y) (uc_c x y) := by
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · rw [← uc_u_neg_x x y, ← uc_c_neg_x x y]
      exact F_det_pos_of_nonneg_x_ge hy le_rfl h0 (-x) (by linarith)
    · exact F_det_pos_of_nonneg_x_ge hy le_rfl h0 x hgt
  rw [det_xy_eq_uc x hy]; unfold det_uc
  have hu := uc_u_nonneg x hy; have hc := uc_c_bounds x hy
  have := uc_w_pos hu hc.1; have := uc_t_pos hu hc.1
  exact div_pos hFpos (by positivity)

/- Implicit curve u_Γ(c), y_Γ(c), U_Γ(c) on (c_bot, c_top) -/

lemma exists_unique_u_Gamma {c : ℝ} (hc1 : c_bot_val < c) (hc2 : c < c_top_val) :
    ∃! u : ℝ, 0 < u ∧ u < 4 / 100 ∧ F_det u c = 0 := by
  have hcb := c_bot_top_spec
  have hc_lo : -75 / 100 < c := by linarith
  have hc_hi : c < -15 / 100 := by linarith
  have hF0 : F_det 0 c < 0 := (hcb.2.2.2.2.2.2 c (by linarith) (by linarith)).1.mpr ⟨hc1, hc2⟩
  have hF4 : 0 < F_det (4 / 100) c := F_det_pos_at_004 (by linarith) (by linarith)
  have hmono : StrictMonoOn (fun u => F_det u c) (Set.Icc 0 (4 / 100)) :=
    (F_det_strictMono_u (by linarith) (by linarith)).mono (Set.Icc_subset_Icc le_rfl (by norm_num))
  have hcont : ContinuousOn (fun u => F_det u c) (Set.Icc 0 (4 / 100)) := fun u hu =>
    (hasDerivAt_x_of_lin2 (hasFDerivAt_F_det (by linarith [hu.1]) (uc_w_pos hu.1 (by linarith)))).continuousAt.continuousWithinAt
  obtain ⟨u, huIcc, huEq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 4 / 100) hcont ⟨hF0.le, hF4.le⟩
  dsimp only at huEq
  have hu1 : 0 < u := lt_of_le_of_ne huIcc.1 (by rintro rfl; linarith)
  have hu2 : u < 4 / 100 := lt_of_le_of_ne huIcc.2 (by rintro rfl; linarith)
  refine ⟨u, ⟨hu1, hu2, huEq⟩, ?_⟩
  rintro u' ⟨h1, h2, heq⟩
  rcases lt_trichotomy u' u with hlt | rfl | hgt
  · linarith [hmono ⟨h1.le, h2.le⟩ ⟨hu1.le, hu2.le⟩ hlt]
  · rfl
  · linarith [hmono ⟨hu1.le, hu2.le⟩ ⟨h1.le, h2.le⟩ hgt]

noncomputable def u_Gamma (c : ℝ) : ℝ :=
  if h : c_bot_val < c ∧ c < c_top_val then
    Classical.choose (exists_unique_u_Gamma h.1 h.2)
  else 0

lemma u_Gamma_spec {c : ℝ} (hc1 : c_bot_val < c) (hc2 : c < c_top_val) :
    0 < u_Gamma c ∧ u_Gamma c < 4 / 100 ∧ F_det (u_Gamma c) c = 0 := by
  unfold u_Gamma; rw [dif_pos ⟨hc1, hc2⟩]
  exact (Classical.choose_spec (exists_unique_u_Gamma hc1 hc2)).1

lemma u_Gamma_unique {c u : ℝ} (hc1 : c_bot_val < c) (hc2 : c < c_top_val)
    (hu1 : 0 < u) (hu2 : u < 4 / 100) (hF : F_det u c = 0) : u = u_Gamma c := by
  unfold u_Gamma; rw [dif_pos ⟨hc1, hc2⟩]
  exact (Classical.choose_spec (exists_unique_u_Gamma hc1 hc2)).2 u ⟨hu1, hu2, hF⟩

lemma u_Gamma_continuousAt {c : ℝ} (hc1 : c_bot_val < c) (hc2 : c < c_top_val) :
    ContinuousAt u_Gamma c := by
  have ⟨hu1, hu2, huF⟩ := u_Gamma_spec hc1 hc2
  have hcb := c_bot_top_spec
  rw [Metric.continuousAt_iff]
  intro ε hε
  set a := max 0 (u_Gamma c - ε / 2)
  set b := min (4 / 100) (u_Gamma c + ε / 2)
  have ha0 : 0 ≤ a := le_max_left _ _
  have ha_ge : u_Gamma c - ε / 2 ≤ a := le_max_right _ _
  have ha_lt : a < u_Gamma c := max_lt hu1 (by linarith)
  have hb_gt : u_Gamma c < b := lt_min hu2 (by linarith)
  have hb0 : 0 < b := lt_trans hu1 hb_gt
  have hb_le4 : b ≤ 4 / 100 := min_le_left _ _
  have hb_le : b ≤ u_Gamma c + ε / 2 := min_le_right _ _
  have hmono_c := F_det_strictMono_u (by linarith : -85 / 100 ≤ c) (by linarith : c ≤ 34 / 100)
  have hFa : F_det a c < 0 := by
    rw [← huF]; exact hmono_c ⟨ha0, by linarith⟩ ⟨hu1.le, by linarith⟩ ha_lt
  have hFb : 0 < F_det b c := by
    rw [← huF]; exact hmono_c ⟨hu1.le, by linarith⟩ ⟨hb0.le, by linarith⟩ hb_gt
  have hca : ContinuousAt (fun t => F_det a t) c :=
    (hasDerivAt_y_of_lin2 (hasFDerivAt_F_det (by linarith) (uc_w_pos ha0 (by linarith)))).continuousAt
  have hcb_cont : ContinuousAt (fun t => F_det b t) c :=
    (hasDerivAt_y_of_lin2 (hasFDerivAt_F_det (by linarith) (uc_w_pos hb0.le (by linarith)))).continuousAt
  have hev1 : ∀ᶠ t in nhds c, F_det a t < 0 := hca.eventually (Iio_mem_nhds hFa)
  have hev2 : ∀ᶠ t in nhds c, 0 < F_det b t := hcb_cont.eventually (Ioi_mem_nhds hFb)
  have hev3 : ∀ᶠ t in nhds c, c_bot_val < t ∧ t < c_top_val :=
    Filter.eventually_of_mem (Ioo_mem_nhds hc1 hc2) fun _ ht => ht
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp ((hev1.and hev2).and hev3)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨⟨hFat, hFbt⟩, ⟨ht1, ht2⟩⟩ := hball ht
  have ⟨hut1, hut2, hutF⟩ := u_Gamma_spec ht1 ht2
  have hmonot := F_det_strictMono_u (by linarith : -85 / 100 ≤ t) (by linarith : t ≤ 34 / 100)
  have hgt_a : a < u_Gamma t := by
    by_contra hle; push Not at hle
    have := hmonot.monotoneOn ⟨hut1.le, by linarith⟩ ⟨ha0, by linarith⟩ hle
    linarith
  have hlt_b : u_Gamma t < b := by
    by_contra hge; push Not at hge
    have := hmonot.monotoneOn ⟨hb0.le, by linarith⟩ ⟨hut1.le, by linarith⟩ hge
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

lemma hasDerivAt_u_Gamma {c : ℝ} (hc1 : c_bot_val < c) (hc2 : c < c_top_val) :
    HasDerivAt u_Gamma (-F_c (u_Gamma c) c / F_u (u_Gamma c) c) c := by
  have ⟨hu1, hu2, _⟩ := u_Gamma_spec hc1 hc2
  have hcb := c_bot_top_spec
  have hFu : 0 < F_u (u_Gamma c) c := F_u_pos_on_grid hu1.le (by linarith) (by linarith) (by linarith)
  have hΦ := hasFDerivAt_F_det (by linarith) (uc_w_pos (c := c) hu1.le (by linarith))
  have heq : ∀ᶠ t in nhds c, F_det (u_Gamma t) t = 0 :=
    Filter.eventually_of_mem (Ioo_mem_nhds hc1 hc2) fun t ⟨h1, h2⟩ => (u_Gamma_spec h1 h2).2.2
  exact implicit_hasDerivAt hΦ hFu.ne' heq (u_Gamma_continuousAt hc1 hc2)

noncomputable def y_Gamma (c : ℝ) : ℝ :=
  2 * Real.sqrt (1 - c ^ 2) / (2 + u_Gamma c - 2 * c)

lemma y_Gamma_pos {c : ℝ} (hc1 : c_bot_val < c) (hc2 : c < c_top_val) : 0 < y_Gamma c := by
  have ⟨hu1, _, _⟩ := u_Gamma_spec hc1 hc2
  have hcb := c_bot_top_spec
  unfold y_Gamma
  have h1c : 0 < 1 - c ^ 2 := by nlinarith
  have hLm : 0 < 2 + u_Gamma c - 2 * c := by linarith
  positivity

lemma y_Gamma_strictMono : StrictMonoOn y_Gamma (Set.Ioo c_bot_val c_top_val) := by
  have hsq_mono : StrictMonoOn (fun c => (y_Gamma c) ^ 2) (Set.Ioo c_bot_val c_top_val) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo c_bot_val c_top_val)
    · intro c hc
      have hcb := c_bot_top_spec
      have ⟨hu1, _, _⟩ := u_Gamma_spec hc.1 hc.2
      have h1c : 0 < 1 - c ^ 2 := by nlinarith [hc.1, hc.2]
      have hLm : 0 < 2 + u_Gamma c - 2 * c := by linarith [hc.1, hc.2]
      have hfun : ∀ᶠ t in nhds c, (y_Gamma t) ^ 2 = 4 * (1 - t ^ 2) / (2 + u_Gamma t - 2 * t) ^ 2 :=
        Filter.eventually_of_mem (Ioo_mem_nhds hc.1 hc.2) fun t ht => by
          unfold y_Gamma
          have : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2, hcb.1, hcb.2.2.2.1]
          rw [div_pow, mul_pow, Real.sq_sqrt this]; ring
      have hnum : ContinuousAt (fun t => 4 * (1 - t ^ 2)) c := by fun_prop
      have hden : ContinuousAt (fun t => (2 + u_Gamma t - 2 * t) ^ 2) c :=
        (((continuousAt_const.add (u_Gamma_continuousAt hc.1 hc.2)).sub (continuousAt_const.mul continuousAt_id)).pow 2)
      exact ((hnum.div hden (pow_ne_zero 2 hLm.ne')).congr (hfun.mono fun t ht => ht.symm)).continuousWithinAt
    · intro c hc; rw [interior_Ioo] at hc
      have hcb := c_bot_top_spec
      have ⟨hu1, hu2, _⟩ := u_Gamma_spec hc.1 hc.2
      have hFu : 0 < F_u (u_Gamma c) c :=
        F_u_pos_on_grid hu1.le (by linarith) (by linarith [hc.1]) (by linarith [hc.2])
      have hhor : 0 < hor_F (u_Gamma c) c :=
        hor_F_pos_on_B hu1.le hu2.le (by linarith [hc.1]) (by linarith [hc.2])
      have hLm : 0 < 2 + u_Gamma c - 2 * c := by linarith [hc.1, hc.2]
      have hud := hasDerivAt_u_Gamma hc.1 hc.2
      have hnum : HasDerivAt (fun t => 4 * (1 - t ^ 2)) (-8 * c) c :=
        (((hasDerivAt_const c (1 : ℝ)).sub (hasDerivAt_pow 2 c)).const_mul 4).congr_deriv (by norm_num; ring)
      have hLmd : HasDerivAt (fun t => 2 + u_Gamma t - 2 * t)
          (-F_c (u_Gamma c) c / F_u (u_Gamma c) c - 2) c :=
        (((hasDerivAt_const c (2 : ℝ)).add hud).sub ((hasDerivAt_id c).const_mul 2)).congr_deriv (by ring)
      have hden : HasDerivAt (fun t => (2 + u_Gamma t - 2 * t) ^ 2)
          (2 * (2 + u_Gamma c - 2 * c) * (-F_c (u_Gamma c) c / F_u (u_Gamma c) c - 2)) c :=
        (hLmd.pow 2).congr_deriv (by norm_num)
      have hdiv : HasDerivAt (fun t => 4 * (1 - t ^ 2) / (2 + u_Gamma t - 2 * t) ^ 2)
          (8 * hor_F (u_Gamma c) c / ((2 + u_Gamma c - 2 * c) ^ 3 * F_u (u_Gamma c) c)) c :=
        (hnum.div hden (pow_ne_zero 2 hLm.ne')).congr_deriv (by
          unfold hor_F; field_simp [hLm.ne', hFu.ne']; ring)
      have hfun : (fun t => (y_Gamma t) ^ 2) =ᶠ[nhds c] (fun t => 4 * (1 - t ^ 2) / (2 + u_Gamma t - 2 * t) ^ 2) :=
        Filter.eventually_of_mem (Ioo_mem_nhds hc.1 hc.2) fun t ht => by
          dsimp only; unfold y_Gamma
          have : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2, hcb.1, hcb.2.2.2.1]
          rw [div_pow, mul_pow, Real.sq_sqrt this]; ring
      rw [(hdiv.congr_of_eventuallyEq hfun).deriv]
      positivity
  intro c₁ hc₁ c₂ hc₂ hlt
  have h1 := y_Gamma_pos hc₁.1 hc₁.2; have h2 := y_Gamma_pos hc₂.1 hc₂.2
  have hsq := hsq_mono hc₁ hc₂ hlt
  nlinarith

lemma G_uc_pos_on_Gamma {c : ℝ} (hc1 : c_bot_val < c) (hc2 : c < c_top_val) :
    0 < G_uc (u_Gamma c) c := by
  have ⟨hu1, _, huF⟩ := u_Gamma_spec hc1 hc2
  have hcb := c_bot_top_spec
  obtain ⟨x, y, hxneg, hypos, hux, hcx⟩ := exists_xy_of_uc (c := c) hu1 (by linarith) (by linarith)
  have hdet0 : uX_xy x y * vY_xy x y - uY_xy x y * vX_xy x y = 0 := by
    rw [det_xy_eq_uc x hypos, hux, hcx]; unfold det_uc; rw [huF, zero_div]
  have hux_neg : uX_xy x y < 0 := by
    by_contra hge; push Not at hge
    linarith [det_pos_of_uX_nonneg hypos hge (Or.inl hxneg.ne)]
  have hux0_neg : uX_xy 0 y < 0 := by
    by_contra hge; push Not at hge
    linarith [(horizontal_slice_ge_y0 hypos hge).1 x hxneg.ne]
  obtain ⟨xstar, hxsp, _, hxs_eq, _, _, hlt_xs, _, hanti, _⟩ := horizontal_slice_lt_y0 hypos hux0_neg
  have hx_gt : -xstar < x := by
    by_contra hle; push Not at hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · have : uX_xy (-xstar) y = 0 := by rw [uX_xy_neg_x xstar hypos]; exact hxs_eq
      linarith
    · linarith [hlt_xs x hlt]
  have hphi_pos : 0 < phiU x y := by
    have h0 : phiU 0 y = 0 := phiU_zero y
    rw [← h0]; exact hanti ⟨hx_gt.le, by linarith⟩ ⟨by linarith, hxsp.le⟩ hxneg
  rw [phiU_eq_uc x hypos, hux, hcx] at hphi_pos
  have hr12 : 0 < r2 x y - r1 x y := by
    have h1 := r1_pos x hypos; have h2 := r2_pos x hypos
    have : (r1 x y) ^ 2 < (r2 x y) ^ 2 := by rw [r1_sq, r2_sq]; nlinarith
    nlinarith
  have hcoef : 0 < (r2 x y - r1 x y) / Real.sqrt (r1 x y * r2 x y) :=
    div_pos hr12 (Real.sqrt_pos.mpr (mul_pos (r1_pos x hypos) (r2_pos x hypos)))
  exact pos_of_mul_pos_right hphi_pos hcoef.le

noncomputable def U_Gamma (c : ℝ) : ℝ := Real.sqrt (u_Gamma c) * G_uc (u_Gamma c) c

lemma hasDerivAt_U_Gamma {c : ℝ} (hc1 : c_bot_val < c) (hc2 : c < c_top_val) :
    HasDerivAt U_Gamma
      (N1_uc (u_Gamma c) c / (2 * Real.sqrt (u_Gamma c) * F_u (u_Gamma c) c)) c := by
  have ⟨hu1, hu2, _⟩ := u_Gamma_spec hc1 hc2
  have hcb := c_bot_top_spec
  have hFu : 0 < F_u (u_Gamma c) c := F_u_pos_on_grid hu1.le (by linarith) (by linarith) (by linarith)
  have hw : 0 < uc_w (u_Gamma c) c := uc_w_pos hu1.le (by linarith)
  have hLm : 0 < 2 + u_Gamma c - 2 * c := by linarith
  have hs : 0 < Real.sqrt (u_Gamma c) := Real.sqrt_pos.mpr hu1
  have hs2 : Real.sqrt (u_Gamma c) ^ 2 = u_Gamma c := Real.sq_sqrt hu1.le
  have hud := hasDerivAt_u_Gamma hc1 hc2
  have hsd := hud.sqrt hu1.ne'
  have hGd := hasDerivAt_comp_lin2 (g := u_Gamma) (h := id)
    (hasFDerivAt_G_uc (by linarith) hw hLm) hud (hasDerivAt_id c)
  unfold U_Gamma
  exact (hsd.mul hGd).congr_deriv (by
    unfold N1_uc; simp only [id_eq]
    generalize Real.sqrt (u_Gamma c) = s at hs hs2 ⊢
    field_simp [hs.ne', hFu.ne']; rw [← hs2]; ring)

lemma N1_pos_left {c : ℝ} (hc1 : c_bot_val < c) (hc2 : c ≤ -68 / 100) :
    0 < N1_uc (u_Gamma c) c := by
  have hcb := c_bot_top_spec
  have hct : c < c_top_val := by linarith
  have ⟨hu1, hu2, huF⟩ := u_Gamma_spec hc1 hct
  have h3 : ((ivRat (-75) 100).lo : ℝ) ≤ c * 65536 := by
    have := (ivMem_rat (-75) 100) (by decide); push_cast at this; linarith
  have h4 : c * 65536 ≤ ((ivRat (-68) 100).hi : ℝ) := by
    have := (ivMem_rat (-68) 100) (by decide); push_cast at this; linarith
  obtain ⟨Ic, hIc, hok⟩ := all_grid1 (by norm_num) _ cert6a_ok h3 h4
  dsimp only at hok
  set eps := ivRat 2 1000
  set q := evalQ Ic
  set ulo0 := max 0 (ivSub q eps).lo
  set uhi := max 0 (ivAdd q eps).hi
  set ulo := if 0 < ulo0 && (evalF ⟨ulo0, ulo0, true⟩ Ic).isNeg then ulo0 else 0
  set um := (ulo + uhi) / 2
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨hokHi, hokL⟩, hokR⟩ := hok
  have hFhi : 0 < F_det ((uhi : ℝ) / 65536) c := by
    have hu_mem : (⟨uhi, uhi, true⟩ : Iv).Mem ((uhi : ℝ) / 65536) :=
      Iv.Mem.of_bounds (by ring_nf; linarith) (by ring_nf; linarith)
    exact (evalF_sound hu_mem hIc).pos_of_isPos hokHi
  have hmono := F_det_strictMono_u (by linarith : -85 / 100 ≤ c) (by linarith : c ≤ 34 / 100)
  have huhi0 : 0 ≤ (uhi : ℝ) / 65536 := by
    have : (0 : ℤ) ≤ uhi := le_max_left _ _
    have : (0 : ℝ) ≤ (uhi : ℝ) := by exact_mod_cast this
    positivity
  have hle_uhi : u_Gamma c * 65536 ≤ (uhi : ℝ) := by
    by_cases h16 : (uhi : ℝ) / 65536 ≤ 16 / 100
    · by_contra hgt; push Not at hgt
      have := hmono.monotoneOn ⟨huhi0, h16⟩ ⟨hu1.le, by linarith⟩ (by linarith)
      linarith
    · push Not at h16; linarith
  have hge_ulo : (ulo : ℝ) ≤ u_Gamma c * 65536 := by
    dsimp only [ulo]
    split_ifs with hcond
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      have hFlo : F_det ((ulo0 : ℝ) / 65536) c < 0 := by
        have hu_mem : (⟨ulo0, ulo0, true⟩ : Iv).Mem ((ulo0 : ℝ) / 65536) :=
          Iv.Mem.of_bounds (by ring_nf; linarith) (by ring_nf; linarith)
        exact (evalF_sound hu_mem hIc).neg_of_isNeg hcond.2
      have hulo0_nn : 0 ≤ (ulo0 : ℝ) / 65536 := by
        have : (0 : ℝ) ≤ (ulo0 : ℝ) := by exact_mod_cast hcond.1.le
        positivity
      have hulo0_le : (ulo0 : ℝ) / 65536 < 4 / 100 := by
        by_contra hge; push Not at hge
        linarith [F_det_pos_outside_B (c := c) hulo0_nn (by linarith) (by linarith) (Or.inl hge)]
      by_contra hlt; push Not at hlt
      have := hmono.monotoneOn ⟨hu1.le, by linarith⟩ ⟨hulo0_nn, by linarith⟩ (by linarith)
      linarith
    · push_cast; linarith
  by_cases hmid : u_Gamma c * 65536 ≤ (um : ℝ)
  · exact (evalN1_sound (Iv.Mem.of_bounds (I := ⟨ulo, um, true⟩) hge_ulo hmid) hIc).pos_of_isPos hokL
  · push Not at hmid
    exact (evalN1_sound (Iv.Mem.of_bounds (I := ⟨um, uhi, true⟩) hmid.le hle_uhi) hIc).pos_of_isPos hokR

lemma peak_cert_bounds {c : ℝ} (hc1 : -68 / 100 ≤ c) (hc2 : c ≤ -60 / 100) :
    PeakD2_uc (u_Gamma c) c < 0 := by
  have hcb := c_bot_top_spec
  have hc1' : c_bot_val < c := by
    have h68 : F_det 0 (-68 / 100) < 0 := by
      have : (evalF (ivInt 0) (ivRat (-68) 100)).isNeg = true := by decide
      exact (evalF_sound (ivMem_int' 0 0) (ivMem_rat' (-68) 100 (-68 / 100))).neg_of_isNeg this
    have := (hcb.2.2.2.2.2.2 (-68 / 100) (by norm_num) (by norm_num)).1.mp h68
    linarith
  have hc2' : c < c_top_val := by linarith
  have ⟨hu1, hu2, huF⟩ := u_Gamma_spec hc1' hc2'
  have h3 : ((ivRat (-68) 100).lo : ℝ) ≤ c * 65536 := by
    have := (ivMem_rat (-68) 100) (by decide); push_cast at this; linarith
  have h4 : c * 65536 ≤ ((ivRat (-60) 100).hi : ℝ) := by
    have := (ivMem_rat (-60) 100) (by decide); push_cast at this; linarith
  obtain ⟨Ic, hIc, hok⟩ := all_grid1 (by norm_num) _ cert6b_ok h3 h4
  dsimp only at hok
  set eps := ivRat 2 1000
  set q := evalQ Ic
  set ulo := (ivSub q eps).lo
  set uhi := (ivAdd q eps).hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hulo_pos, huhi_pos⟩, hokLo⟩, hokHi⟩, _⟩, hokD2⟩ := hok
  have hFlo : F_det ((ulo : ℝ) / 65536) c < 0 :=
    (evalF_sound (Iv.Mem.of_bounds (I := ⟨ulo, ulo, true⟩) (by ring_nf; linarith) (by ring_nf; linarith)) hIc).neg_of_isNeg hokLo
  have hFhi : 0 < F_det ((uhi : ℝ) / 65536) c :=
    (evalF_sound (Iv.Mem.of_bounds (I := ⟨uhi, uhi, true⟩) (by ring_nf; linarith) (by ring_nf; linarith)) hIc).pos_of_isPos hokHi
  have hmono := F_det_strictMono_u (by linarith : -85 / 100 ≤ c) (by linarith : c ≤ 34 / 100)
  have huloR : 0 < (ulo : ℝ) / 65536 := by
    have : (0 : ℝ) < (ulo : ℝ) := by exact_mod_cast hulo_pos
    positivity
  have huhiR : 0 < (uhi : ℝ) / 65536 := by
    have : (0 : ℝ) < (uhi : ℝ) := by exact_mod_cast huhi_pos
    positivity
  have hulo_lt4 : (ulo : ℝ) / 65536 < 4 / 100 := by
    by_contra hge; push Not at hge
    linarith [F_det_pos_outside_B (c := c) huloR.le (by linarith) (by linarith) (Or.inl hge)]
  have hge_ulo : (ulo : ℝ) ≤ u_Gamma c * 65536 := by
    by_contra hlt; push Not at hlt
    have := hmono.monotoneOn ⟨hu1.le, by linarith⟩ ⟨huloR.le, by linarith⟩ (by linarith)
    linarith
  have hle_uhi : u_Gamma c * 65536 ≤ (uhi : ℝ) := by
    by_cases h16 : (uhi : ℝ) / 65536 ≤ 16 / 100
    · by_contra hgt; push Not at hgt
      have := hmono.monotoneOn ⟨huhiR.le, h16⟩ ⟨hu1.le, by linarith⟩ (by linarith)
      linarith
    · push Not at h16; linarith
  exact (evalPeakD2_sound (Iv.Mem.of_bounds (I := ⟨ulo, uhi, true⟩) hge_ulo hle_uhi) hIc).neg_of_isNeg hokD2

lemma N1_neg_mid {c : ℝ} (hc1 : -60 / 100 ≤ c) (hc2 : c ≤ -38 / 100) :
    N1_uc (u_Gamma c) c < 0 := by
  have hcb := c_bot_top_spec
  have hc1' : c_bot_val < c := by
    have h68 : F_det 0 (-68 / 100) < 0 := by
      have : (evalF (ivInt 0) (ivRat (-68) 100)).isNeg = true := by decide
      exact (evalF_sound (ivMem_int' 0 0) (ivMem_rat' (-68) 100 (-68 / 100))).neg_of_isNeg this
    have := (hcb.2.2.2.2.2.2 (-68 / 100) (by norm_num) (by norm_num)).1.mp h68
    linarith
  have hc2' : c < c_top_val := by
    have h38 : F_det 0 (-38 / 100) < 0 := by
      have : (evalF (ivInt 0) (ivRat (-38) 100)).isNeg = true := by decide
      exact (evalF_sound (ivMem_int' 0 0) (ivMem_rat' (-38) 100 (-38 / 100))).neg_of_isNeg this
    have := (hcb.2.2.2.2.2.2 (-38 / 100) (by norm_num) (by norm_num)).1.mp h38
    linarith
  have ⟨hu1, hu2, huF⟩ := u_Gamma_spec hc1' hc2'
  have h3 : ((ivRat (-60) 100).lo : ℝ) ≤ c * 65536 := by
    have := (ivMem_rat (-60) 100) (by decide); push_cast at this; linarith
  have h4 : c * 65536 ≤ ((ivRat (-38) 100).hi : ℝ) := by
    have := (ivMem_rat (-38) 100) (by decide); push_cast at this; linarith
  obtain ⟨Ic, hIc, hok⟩ := all_grid1 (by norm_num) _ cert6c_ok h3 h4
  dsimp only at hok
  set eps := ivRat 2 1000
  set q := evalQ Ic
  set ulo := (ivSub q eps).lo
  set uhi := (ivAdd q eps).hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hulo_pos, huhi_pos⟩, hokLo⟩, hokHi⟩, hokN1⟩ := hok
  have hFlo : F_det ((ulo : ℝ) / 65536) c < 0 :=
    (evalF_sound (Iv.Mem.of_bounds (I := ⟨ulo, ulo, true⟩) (by ring_nf; linarith) (by ring_nf; linarith)) hIc).neg_of_isNeg hokLo
  have hFhi : 0 < F_det ((uhi : ℝ) / 65536) c :=
    (evalF_sound (Iv.Mem.of_bounds (I := ⟨uhi, uhi, true⟩) (by ring_nf; linarith) (by ring_nf; linarith)) hIc).pos_of_isPos hokHi
  have hmono := F_det_strictMono_u (by linarith : -85 / 100 ≤ c) (by linarith : c ≤ 34 / 100)
  have huloR : 0 < (ulo : ℝ) / 65536 := by
    have : (0 : ℝ) < (ulo : ℝ) := by exact_mod_cast hulo_pos
    positivity
  have huhiR : 0 < (uhi : ℝ) / 65536 := by
    have : (0 : ℝ) < (uhi : ℝ) := by exact_mod_cast huhi_pos
    positivity
  have hulo_lt4 : (ulo : ℝ) / 65536 < 4 / 100 := by
    by_contra hge; push Not at hge
    linarith [F_det_pos_outside_B (c := c) huloR.le (by linarith) (by linarith) (Or.inl hge)]
  have hge_ulo : (ulo : ℝ) ≤ u_Gamma c * 65536 := by
    by_contra hlt; push Not at hlt
    have := hmono.monotoneOn ⟨hu1.le, by linarith⟩ ⟨huloR.le, by linarith⟩ (by linarith)
    linarith
  have hle_uhi : u_Gamma c * 65536 ≤ (uhi : ℝ) := by
    by_cases h16 : (uhi : ℝ) / 65536 ≤ 16 / 100
    · by_contra hgt; push Not at hgt
      have := hmono.monotoneOn ⟨huhiR.le, h16⟩ ⟨hu1.le, by linarith⟩ (by linarith)
      linarith
    · push Not at h16; linarith
  exact (evalN1_sound (Iv.Mem.of_bounds (I := ⟨ulo, uhi, true⟩) hge_ulo hle_uhi) hIc).neg_of_isNeg hokN1

lemma N1_neg_high {c : ℝ} (hc1 : -38 / 100 ≤ c) (hc2 : c < c_top_val) :
    N1_uc (u_Gamma c) c < 0 := by
  have hcb := c_bot_top_spec
  have hc1' : c_bot_val < c := by linarith
  have ⟨hu1, hu2, _⟩ := u_Gamma_spec hc1' hc2
  have hGpos := G_uc_pos_on_Gamma hc1' hc2
  have h1 : ((0 : ℤ) : ℝ) ≤ u_Gamma c * 65536 := by push_cast; linarith
  have h2 : u_Gamma c * 65536 ≤ ((ivRat 4 100).hi : ℝ) := by
    have := (ivMem_rat 4 100) (by decide); push_cast at this; linarith
  have h3 : ((ivRat (-38) 100).lo : ℝ) ≤ c * 65536 := by
    have := (ivMem_rat (-38) 100) (by decide); push_cast at this; linarith
  have h4 : c * 65536 ≤ ((ivRat (-15) 100).hi : ℝ) := by
    have := (ivMem_rat (-15) 100) (by decide); push_cast at this; linarith
  obtain ⟨Iu, Ic, hIu, hIc, hok⟩ := all_grid2 (by norm_num) (by norm_num) _ cert6d_ok h1 h2 h3 h4
  dsimp only at hok; simp only [Bool.and_eq_true] at hok
  have ⟨hFu, hFc⟩ := evalFuFc_sound hIu hIc
  have ⟨_, hGu, hGc⟩ := evalGGuGc_sound hIu hIc
  have hFc_pos : 0 < F_c (u_Gamma c) c := hFc.pos_of_isPos hok.1
  have hJ_neg : G_c (u_Gamma c) c * F_u (u_Gamma c) c - G_u (u_Gamma c) c * F_c (u_Gamma c) c < 0 :=
    ((hGc.mul hFu).sub (hGu.mul hFc)).neg_of_isNeg hok.2
  unfold N1_uc; nlinarith

lemma hasDerivAt_logU_ratio {c : ℝ} (hc1 : c_bot_val < c) (hc2 : c < c_top_val) :
    HasDerivAt
      (fun t => N1_uc (u_Gamma t) t / (2 * u_Gamma t * F_u (u_Gamma t) t * G_uc (u_Gamma t) t))
      (PeakD2_uc (u_Gamma c) c) c := by
  have ⟨hu1, hu2, _⟩ := u_Gamma_spec hc1 hc2
  have hcb := c_bot_top_spec
  have hFu : 0 < F_u (u_Gamma c) c := F_u_pos_on_grid hu1.le (by linarith) (by linarith) (by linarith)
  have hG : 0 < G_uc (u_Gamma c) c := G_uc_pos_on_Gamma hc1 hc2
  have hw : 0 < uc_w (u_Gamma c) c := uc_w_pos hu1.le (by linarith)
  have hLm : 0 < 2 + u_Gamma c - 2 * c := by linarith
  have hud := hasDerivAt_u_Gamma hc1 hc2
  set up := -F_c (u_Gamma c) c / F_u (u_Gamma c) c
  have hFud := hasDerivAt_comp_lin2 (g := u_Gamma) (h := id) (hasFDerivAt_F_u (by linarith) hw) hud (hasDerivAt_id c)
  have hFcd := hasDerivAt_comp_lin2 (g := u_Gamma) (h := id) (hasFDerivAt_F_c (by linarith) hw) hud (hasDerivAt_id c)
  have hGd := hasDerivAt_comp_lin2 (g := u_Gamma) (h := id) (hasFDerivAt_G_uc (by linarith) hw hLm) hud (hasDerivAt_id c)
  have hGud := hasDerivAt_comp_lin2 (g := u_Gamma) (h := id) (hasFDerivAt_G_u (by linarith) hw hLm) hud (hasDerivAt_id c)
  have hGcd := hasDerivAt_comp_lin2 (g := u_Gamma) (h := id) (hasFDerivAt_G_c (by linarith) hw hLm) hud (hasDerivAt_id c)
  set upp := -(F_uu (u_Gamma c) c * up ^ 2 + 2 * (F_uc (u_Gamma c) c * up) + F_cc (u_Gamma c) c) / F_u (u_Gamma c) c
  have hupd : HasDerivAt (fun t => -F_c (u_Gamma t) t / F_u (u_Gamma t) t) upp c :=
    (hFcd.neg.div hFud hFu.ne').congr_deriv (by
      simp only [id_eq, Pi.neg_apply, upp, up]; field_simp [hFu.ne']; ring)
  have hterm1d : HasDerivAt (fun t => (-F_c (u_Gamma t) t / F_u (u_Gamma t) t) / (2 * u_Gamma t))
      ((upp / u_Gamma c - (up / u_Gamma c) ^ 2) / 2) c :=
    (hupd.div (hud.const_mul 2) (by positivity)).congr_deriv (by
      simp only [up]; field_simp [hu1.ne', hFu.ne'])
  have hgd_deriv : HasDerivAt (fun t => G_u (u_Gamma t) t * (-F_c (u_Gamma t) t / F_u (u_Gamma t) t) + G_c (u_Gamma t) t)
      (G_uu (u_Gamma c) c * up ^ 2 + 2 * (G_uc2 (u_Gamma c) c * up) + G_cc (u_Gamma c) c + G_u (u_Gamma c) c * upp) c :=
    ((hGud.mul hupd).add hGcd).congr_deriv (by simp only [id_eq, up]; ring)
  have hterm2d : HasDerivAt
      (fun t => (G_u (u_Gamma t) t * (-F_c (u_Gamma t) t / F_u (u_Gamma t) t) + G_c (u_Gamma t) t) / G_uc (u_Gamma t) t)
      ((G_uu (u_Gamma c) c * up ^ 2 + 2 * (G_uc2 (u_Gamma c) c * up) + G_cc (u_Gamma c) c + G_u (u_Gamma c) c * upp) / G_uc (u_Gamma c) c -
        ((G_u (u_Gamma c) c * up + G_c (u_Gamma c) c) / G_uc (u_Gamma c) c) ^ 2) c :=
    (hgd_deriv.div hGd hG.ne').congr_deriv (by
      simp only [id_eq, up]; field_simp [hG.ne'])
  have hsum : HasDerivAt
      (fun t => (-F_c (u_Gamma t) t / F_u (u_Gamma t) t) / (2 * u_Gamma t) +
        (G_u (u_Gamma t) t * (-F_c (u_Gamma t) t / F_u (u_Gamma t) t) + G_c (u_Gamma t) t) / G_uc (u_Gamma t) t)
      (PeakD2_uc (u_Gamma c) c) c :=
    (hterm1d.add hterm2d).congr_deriv (by unfold PeakD2_uc; simp only [upp, up])
  refine hsum.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioo_mem_nhds hc1 hc2) fun t ⟨ht1, ht2⟩ => ?_)
  have ⟨hut1, hut2, _⟩ := u_Gamma_spec ht1 ht2
  have hFut : 0 < F_u (u_Gamma t) t := F_u_pos_on_grid hut1.le (by linarith) (by linarith) (by linarith)
  have hGt := G_uc_pos_on_Gamma ht1 ht2
  unfold N1_uc; field_simp [hut1.ne', hFut.ne', hGt.ne']; ring

lemma U_Gamma_unimodal :
    ∃ c_peak : ℝ, c_bot_val < c_peak ∧ c_peak < c_top_val ∧
      StrictMonoOn U_Gamma (Set.Ioc c_bot_val c_peak) ∧
      StrictAntiOn U_Gamma (Set.Ico c_peak c_top_val) := by
  have hcb := c_bot_top_spec
  have h68_gt : c_bot_val < -68 / 100 := by
    have h68 : F_det 0 (-68 / 100) < 0 := by
      have : (evalF (ivInt 0) (ivRat (-68) 100)).isNeg = true := by decide
      exact (evalF_sound (ivMem_int' 0 0) (ivMem_rat' (-68) 100 (-68 / 100))).neg_of_isNeg this
    exact ((hcb.2.2.2.2.2.2 (-68 / 100) (by norm_num) (by norm_num)).1.mp h68).1
  have h60_lt : -60 / 100 < c_top_val := by linarith
  set f : ℝ → ℝ := fun t => N1_uc (u_Gamma t) t / (2 * u_Gamma t * F_u (u_Gamma t) t * G_uc (u_Gamma t) t)
  have hf_anti : StrictAntiOn f (Set.Icc (-68 / 100) (-60 / 100)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc (-68 / 100) (-60 / 100))
    · exact fun c hc => (hasDerivAt_logU_ratio (by linarith [hc.1]) (by linarith [hc.2])).continuousAt.continuousWithinAt
    · intro c hc; rw [interior_Icc] at hc
      rw [(hasDerivAt_logU_ratio (by linarith [hc.1]) (by linarith [hc.2])).deriv]
      exact peak_cert_bounds hc.1.le hc.2.le
  have hf_pos : 0 < f (-68 / 100) := by
    have ⟨hu1, hu2, _⟩ := u_Gamma_spec h68_gt (by linarith)
    have hFu : 0 < F_u (u_Gamma (-68 / 100)) (-68 / 100) :=
      F_u_pos_on_grid hu1.le (by linarith) (by norm_num) (by norm_num)
    have hG := G_uc_pos_on_Gamma h68_gt (by linarith)
    have hN1 := N1_pos_left h68_gt le_rfl
    exact div_pos hN1 (by positivity)
  have hf_neg : f (-60 / 100) < 0 := by
    have ⟨hu1, hu2, _⟩ := u_Gamma_spec (by linarith) h60_lt
    have hFu : 0 < F_u (u_Gamma (-60 / 100)) (-60 / 100) :=
      F_u_pos_on_grid hu1.le (by linarith) (by norm_num) (by norm_num)
    have hG := G_uc_pos_on_Gamma (by linarith) h60_lt
    have hN1 := N1_neg_mid le_rfl (by norm_num)
    exact div_neg_of_neg_of_pos hN1 (by positivity)
  have hf_cont : ContinuousOn f (Set.Icc (-68 / 100) (-60 / 100)) :=
    fun c hc => (hasDerivAt_logU_ratio (by linarith [hc.1]) (by linarith [hc.2])).continuousAt.continuousWithinAt
  obtain ⟨c_peak, hcpIcc, hcpEq⟩ := intermediate_value_Icc' (by norm_num : (-68 / 100 : ℝ) ≤ -60 / 100)
    hf_cont ⟨hf_neg.le, hf_pos.le⟩
  have hcp1 : -68 / 100 < c_peak := lt_of_le_of_ne hcpIcc.1 (by rintro rfl; linarith)
  have hcp2 : c_peak < -60 / 100 := lt_of_le_of_ne hcpIcc.2 (by rintro rfl; linarith)
  refine ⟨c_peak, by linarith, by linarith, ?_, ?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Ioc c_bot_val c_peak)
    · exact fun c hc => (hasDerivAt_U_Gamma hc.1 (by linarith [hc.2])).continuousAt.continuousWithinAt
    · intro c hc; rw [interior_Ioc] at hc
      rw [(hasDerivAt_U_Gamma hc.1 (by linarith [hc.2])).deriv]
      have ⟨hu1, hu2, _⟩ := u_Gamma_spec hc.1 (by linarith [hc.2])
      have hFu : 0 < F_u (u_Gamma c) c :=
        F_u_pos_on_grid hu1.le (by linarith) (by linarith [hc.1]) (by linarith [hc.2])
      have hN1 : 0 < N1_uc (u_Gamma c) c := by
        by_cases h68 : c ≤ -68 / 100
        · exact N1_pos_left hc.1 h68
        · push Not at h68
          have hfgt : 0 < f c := by
            rw [← hcpEq]; exact hf_anti ⟨h68.le, by linarith [hc.2]⟩ hcpIcc hc.2
          have hG := G_uc_pos_on_Gamma hc.1 (by linarith [hc.2])
          have hden : 0 < 2 * u_Gamma c * F_u (u_Gamma c) c * G_uc (u_Gamma c) c := by positivity
          exact (div_pos_iff_of_pos_right hden).mp hfgt
      exact div_pos hN1 (by positivity)
  · apply strictAntiOn_of_deriv_neg (convex_Ico c_peak c_top_val)
    · exact fun c hc => (hasDerivAt_U_Gamma (by linarith [hc.1]) hc.2).continuousAt.continuousWithinAt
    · intro c hc; rw [interior_Ico] at hc
      rw [(hasDerivAt_U_Gamma (by linarith [hc.1]) hc.2).deriv]
      have ⟨hu1, hu2, _⟩ := u_Gamma_spec (by linarith [hc.1]) hc.2
      have hFu : 0 < F_u (u_Gamma c) c :=
        F_u_pos_on_grid hu1.le (by linarith) (by linarith [hc.1]) (by linarith [hc.2])
      have hN1 : N1_uc (u_Gamma c) c < 0 := by
        by_cases h60 : c ≤ -60 / 100
        · have hflt : f c < 0 := by
            rw [← hcpEq]; exact hf_anti hcpIcc ⟨by linarith [hc.1], h60⟩ hc.1
          have hG := G_uc_pos_on_Gamma (by linarith [hc.1]) hc.2
          have hden : 0 < 2 * u_Gamma c * F_u (u_Gamma c) c * G_uc (u_Gamma c) c := by positivity
          exact (div_neg_iff.mp hflt).elim (fun h => by linarith) (fun h => h.1)
        · push Not at h60
          by_cases h38 : c ≤ -38 / 100
          · exact N1_neg_mid h60.le h38
          · push Not at h38; exact N1_neg_high h38.le hc.2
      exact div_neg_of_neg_of_pos hN1 (by positivity)

/- Killer Convexity Lemma for Section 6: {y : det_xy (x_M y) y ≤ 0} is strictly convex! -/

lemma exists_unique_x_Gamma {y : ℝ} (hy1 : y_bot_val < y) (hy2 : y < y0_val) :
    ∃ x_Γ : ℝ, x_Γ < 0 ∧
      uX_xy x_Γ y < 0 ∧
      (uX_xy x_Γ y * vY_xy x_Γ y - uY_xy x_Γ y * vX_xy x_Γ y = 0) ∧
      (∀ x, x < x_Γ → 0 < uX_xy x y * vY_xy x y - uY_xy x y * vX_xy x y) ∧
      (∀ x, x_Γ < x → x ≤ 0 → uX_xy x y * vY_xy x y - uY_xy x y * vX_xy x y < 0) := by
  have hy : 0 < y := lt_trans uc_c_y_bot.1 hy1
  have hux0 : uX_xy 0 y < 0 := y0_val_spec.2.2.2.1 y hy hy2
  obtain ⟨xstar, hxsp, _, hxseq, _, _, _, _, _, _⟩ := horizontal_slice_lt_y0 hy hux0
  have hF0 : F_det (uc_u 0 y) (uc_c 0 y) < 0 := by
    have hdet := (det_xy_axis_sign hy).1.mpr ⟨hy1, hy2⟩
    rw [det_xy_eq_uc 0 hy] at hdet; unfold det_uc at hdet
    have hc := uc_c_bounds 0 hy; have hu := uc_u_nonneg 0 hy
    have hden : 0 < 2 * uc_w (uc_u 0 y) (uc_c 0 y) * (uc_t (uc_u 0 y) (uc_c 0 y)) ^ 3 := by
      have := uc_w_pos hu hc.1; have := uc_t_pos hu hc.1; positivity
    exact (div_neg_iff.mp hdet).elim (fun h => by linarith) (fun h => h.1)
  have hFxs : 0 < F_det (uc_u xstar y) (uc_c xstar y) := by
    have hdet := det_pos_of_uX_nonneg hy hxseq.ge (Or.inl hxsp.ne')
    rw [det_xy_eq_uc xstar hy] at hdet; unfold det_uc at hdet
    have hc := uc_c_bounds xstar hy; have hu := uc_u_nonneg xstar hy
    have hden : 0 < 2 * uc_w (uc_u xstar y) (uc_c xstar y) * (uc_t (uc_u xstar y) (uc_c xstar y)) ^ 3 := by
      have := uc_w_pos hu hc.1; have := uc_t_pos hu hc.1; positivity
    exact (div_pos_iff_of_pos_right hden).mp hdet
  have hcont : ContinuousOn (fun t => F_det (uc_u t y) (uc_c t y)) (Set.Icc 0 xstar) :=
    fun t _ => (hasDerivAt_F_det_x hy).continuousAt.continuousWithinAt
  obtain ⟨xg, hxgIcc, hxgEq⟩ := intermediate_value_Icc hxsp.le hcont ⟨hF0.le, hFxs.le⟩
  dsimp only at hxgEq
  have hxg1 : 0 < xg := lt_of_le_of_ne hxgIcc.1 (by rintro rfl; linarith)
  have hxg2 : xg < xstar := lt_of_le_of_ne hxgIcc.2 (by rintro rfl; linarith)
  have hFgt : ∀ t, xg < t → 0 < F_det (uc_u t y) (uc_c t y) :=
    F_det_pos_of_nonneg_x_ge hy hxg1.le hxgEq.ge
  have hFlt : ∀ t, 0 ≤ t → t < xg → F_det (uc_u t y) (uc_c t y) < 0 := by
    intro t ht0 htlt
    by_contra hge; push Not at hge
    linarith [F_det_pos_of_nonneg_x_ge hy ht0 hge xg htlt]
  refine ⟨-xg, by linarith, ?_, ?_, ?_, ?_⟩
  · by_contra hge; push Not at hge
    have hdet := det_pos_of_uX_nonneg hy hge (Or.inl (by linarith))
    rw [det_xy_eq_uc (-xg) hy, uc_u_neg_x, uc_c_neg_x] at hdet; unfold det_uc at hdet
    rw [hxgEq, zero_div] at hdet; linarith
  · rw [det_xy_eq_uc (-xg) hy, uc_u_neg_x, uc_c_neg_x]; unfold det_uc; rw [hxgEq, zero_div]
  · intro x hxlt
    rw [det_xy_eq_uc x hy, ← uc_u_neg_x x y, ← uc_c_neg_x x y]; unfold det_uc
    have hu := uc_u_nonneg (-x) hy; have hc := uc_c_bounds (-x) hy
    have := uc_w_pos hu hc.1; have := uc_t_pos hu hc.1
    exact div_pos (hFgt (-x) (by linarith)) (by positivity)
  · intro x hxgt hxle
    rw [det_xy_eq_uc x hy, ← uc_u_neg_x x y, ← uc_c_neg_x x y]; unfold det_uc
    have hu := uc_u_nonneg (-x) hy; have hc := uc_c_bounds (-x) hy
    have := uc_w_pos hu hc.1; have := uc_t_pos hu hc.1
    exact div_neg_of_neg_of_pos (hFlt (-x) (by linarith) (by linarith)) (by positivity)

lemma det_zero_on_Gamma_eq {x y : ℝ} (hx : x < 0) (hy : 0 < y)
    (hdet : uX_xy x y * vY_xy x y - uY_xy x y * vX_xy x y = 0) :
    c_bot_val < uc_c x y ∧ uc_c x y < c_top_val ∧
    uc_u x y = u_Gamma (uc_c x y) ∧
    y = y_Gamma (uc_c x y) ∧
    phiU x y = U_Gamma (uc_c x y) := by
  have hu0 := uc_u_nonneg x hy; have hc := uc_c_bounds x hy
  have hu_pos : 0 < uc_u x y := lt_of_le_of_ne hu0 (Ne.symm (mt (uc_u_eq_zero_iff x hy).mp hx.ne))
  rw [det_xy_eq_uc x hy] at hdet; unfold det_uc at hdet
  have hden : 2 * uc_w (uc_u x y) (uc_c x y) * (uc_t (uc_u x y) (uc_c x y)) ^ 3 ≠ 0 := by
    have := uc_w_pos hu0 hc.1; have := uc_t_pos hu0 hc.1; positivity
  have hF0 : F_det (uc_u x y) (uc_c x y) = 0 := (div_eq_zero_iff.mp hdet).resolve_right hden
  have hB : uc_u x y < 4 / 100 ∧ -75 / 100 < uc_c x y ∧ uc_c x y < -15 / 100 := by
    by_contra hnot
    have hout : 4 / 100 ≤ uc_u x y ∨ uc_c x y ≤ -75 / 100 ∨ -15 / 100 ≤ uc_c x y := by
      by_cases h1 : 4 / 100 ≤ uc_u x y
      · exact Or.inl h1
      · by_cases h2 : uc_c x y ≤ -75 / 100
        · exact Or.inr (Or.inl h2)
        · by_cases h3 : -15 / 100 ≤ uc_c x y
          · exact Or.inr (Or.inr h3)
          · exact absurd ⟨lt_of_not_ge h1, lt_of_not_ge h2, lt_of_not_ge h3⟩ hnot
    linarith [F_det_pos_outside_B hu0 hc.1 hc.2 hout]
  have hF_zero_neg : F_det 0 (uc_c x y) < 0 := by
    have hmono := F_det_strictMono_u (by linarith [hB.2.1] : -85 / 100 ≤ uc_c x y) (by linarith [hB.2.2])
    have hlt := hmono ⟨le_rfl, by norm_num⟩ ⟨hu0, by linarith [hB.1]⟩ hu_pos
    linarith
  have ⟨hc1, hc2⟩ := (c_bot_top_spec.2.2.2.2.2.2 (uc_c x y) hc.1 hc.2).1.mp hF_zero_neg
  have hu_eq : uc_u x y = u_Gamma (uc_c x y) := u_Gamma_unique hc1 hc2 hu_pos hB.1 hF0
  have hy_eq : y = y_Gamma (uc_c x y) := by
    unfold y_Gamma; rw [← hu_eq]
    have hLm_r := uc_Lm_eq x hy
    have h1c := uc_one_sub_c_sq x hy
    have hLm_pos : 0 < 2 + uc_u x y - 2 * uc_c x y := by linarith [hc.2]
    have h1ne := (r1_pos x hy).ne'; have h2ne := (r2_pos x hy).ne'
    have hP_pos : 0 < r1 x y * r2 x y := mul_pos (r1_pos x hy) (r2_pos x hy)
    have hsq : Real.sqrt (1 - (uc_c x y) ^ 2) = 2 * y / (r1 x y * r2 x y) := by
      rw [h1c, Real.sqrt_sq (by positivity)]
    rw [hsq, hLm_r]; field_simp [h1ne, h2ne, hP_pos.ne']; ring
  have hU_eq : phiU x y = U_Gamma (uc_c x y) := by
    unfold U_Gamma; rw [← hu_eq, phiU_eq_uc x hy]
    congr 1
    have h1 := r1_pos x hy; have h2 := r2_pos x hy
    have hP : 0 < r1 x y * r2 x y := mul_pos h1 h2
    have hr12 : 0 < r2 x y - r1 x y := by
      have : (r1 x y) ^ 2 < (r2 x y) ^ 2 := by rw [r1_sq, r2_sq]; nlinarith
      nlinarith
    have hsq : ((r2 x y - r1 x y) / Real.sqrt (r1 x y * r2 x y)) ^ 2 = (Real.sqrt (uc_u x y)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hP.le, Real.sq_sqrt hu0]
      unfold uc_u; field_simp [hP.ne']; ring
    have hL : 0 < (r2 x y - r1 x y) / Real.sqrt (r1 x y * r2 x y) := div_pos hr12 (Real.sqrt_pos.mpr hP)
    have hR : 0 ≤ Real.sqrt (uc_u x y) := Real.sqrt_nonneg _
    nlinarith
  exact ⟨hc1, hc2, hu_eq, hy_eq, hU_eq⟩

lemma det_neg_between_of_phiU_eq {u₀ x₁ x₂ x₃ y₁ y₂ y₃ : ℝ}
    (hu₀ : 0 < u₀)
    (hy₁ : 0 < y₁) (h12 : y₁ < y₂) (h23 : y₂ < y₃) (hy₃ : y₃ < y0_val)
    (hx₁_le : x₁ ≤ 0) (hx₂_le : x₂ ≤ 0) (hx₃_le : x₃ ≤ 0)
    (hux₁ : uX_xy x₁ y₁ < 0) (hux₂ : uX_xy x₂ y₂ < 0) (hux₃ : uX_xy x₃ y₃ < 0)
    (hphi₁ : phiU x₁ y₁ = u₀) (hphi₂ : phiU x₂ y₂ = u₀) (hphi₃ : phiU x₃ y₃ = u₀)
    (hdet₁ : uX_xy x₁ y₁ * vY_xy x₁ y₁ - uY_xy x₁ y₁ * vX_xy x₁ y₁ ≤ 0)
    (hdet₃ : uX_xy x₃ y₃ * vY_xy x₃ y₃ - uY_xy x₃ y₃ * vX_xy x₃ y₃ ≤ 0) :
    uX_xy x₂ y₂ * vY_xy x₂ y₂ - uY_xy x₂ y₂ * vX_xy x₂ y₂ < 0 := by
  have hy₂ : 0 < y₂ := lt_trans hy₁ h12
  have hy₃p : 0 < y₃ := lt_trans hy₂ h23
  have hx₁_ne : x₁ ≠ 0 := by rintro rfl; linarith [phiU_zero y₁]
  have hy₁_gt : y_bot_val < y₁ := by
    by_contra hle; push Not at hle
    linarith [det_xy_pos_outside_y_band hy₁ hx₁_ne (Or.inl hle)]
  have hy₂_gt : y_bot_val < y₂ := lt_trans hy₁_gt h12
  have hy₃_gt : y_bot_val < y₃ := lt_trans hy₂_gt h23
  obtain ⟨xg1, hxg1_neg, _, hdetg1, hgt1, _⟩ := exists_unique_x_Gamma hy₁_gt (lt_trans h12 (lt_trans h23 hy₃))
  obtain ⟨xg2, hxg2_neg, _, hdetg2, _, hlt2⟩ := exists_unique_x_Gamma hy₂_gt (lt_trans h23 hy₃)
  obtain ⟨xg3, hxg3_neg, _, hdetg3, hgt3, _⟩ := exists_unique_x_Gamma hy₃_gt hy₃
  have hx1_ge : xg1 ≤ x₁ := by by_contra hlt; push Not at hlt; linarith [hgt1 x₁ hlt]
  have hx3_ge : xg3 ≤ x₃ := by by_contra hlt; push Not at hlt; linarith [hgt3 x₃ hlt]
  have ⟨hc1_lo, hc1_hi, _, hy1_eq, hU1_eq⟩ := det_zero_on_Gamma_eq hxg1_neg hy₁ hdetg1
  have ⟨hc2_lo, hc2_hi, _, hy2_eq, hU2_eq⟩ := det_zero_on_Gamma_eq hxg2_neg hy₂ hdetg2
  have ⟨hc3_lo, hc3_hi, _, hy3_eq, hU3_eq⟩ := det_zero_on_Gamma_eq hxg3_neg hy₃p hdetg3
  have hc12 : uc_c xg1 y₁ < uc_c xg2 y₂ := by
    by_contra hge; push Not at hge
    have := y_Gamma_strictMono.monotoneOn ⟨hc2_lo, hc2_hi⟩ ⟨hc1_lo, hc1_hi⟩ hge
    linarith
  have hc23 : uc_c xg2 y₂ < uc_c xg3 y₃ := by
    by_contra hge; push Not at hge
    have := y_Gamma_strictMono.monotoneOn ⟨hc3_lo, hc3_hi⟩ ⟨hc2_lo, hc2_hi⟩ hge
    linarith
  have hanti_of : ∀ {y x : ℝ} (hy0 : 0 < y) (hylt : y < y0_val) (hxle : x ≤ 0) (hux : uX_xy x y < 0),
      ∀ {x' : ℝ}, x' ≤ x → uX_xy x' y < 0 → phiU x y ≤ phiU x' y := by
    intro y x hy0 hylt hxle hux x' hle hux'
    obtain ⟨xs, hxs_p, _, hxs_eq, _, _, hlt_xs, _, hanti, _⟩ := horizontal_slice_lt_y0 hy0 (y0_val_spec.2.2.2.1 y hy0 hylt)
    have hgt' : -xs < x' := by
      by_contra h; push Not at h
      rcases eq_or_lt_of_le h with rfl | hlt
      · have : uX_xy (-xs) y = 0 := by rw [uX_xy_neg_x xs hy0]; exact hxs_eq
        linarith
      · linarith [hlt_xs x' hlt]
    exact hanti.antitoneOn ⟨hgt'.le, by linarith⟩ ⟨by linarith, by linarith⟩ hle
  have hu0_le1 : u₀ ≤ U_Gamma (uc_c xg1 y₁) := by
    rw [← hU1_eq, ← hphi₁]
    exact hanti_of hy₁ (lt_trans h12 (lt_trans h23 hy₃)) hx₁_le hux₁ hx1_ge
      (by by_contra h; push Not at h; linarith [det_pos_of_uX_nonneg hy₁ h (Or.inl hxg1_neg.ne)])
  have hu0_le3 : u₀ ≤ U_Gamma (uc_c xg3 y₃) := by
    rw [← hU3_eq, ← hphi₃]
    exact hanti_of hy₃p hy₃ hx₃_le hux₃ hx3_ge
      (by by_contra h; push Not at h; linarith [det_pos_of_uX_nonneg hy₃p h (Or.inl hxg3_neg.ne)])
  obtain ⟨c_peak, hcp1, hcp2, hU_mono, hU_anti⟩ := U_Gamma_unimodal
  have hu0_lt2 : u₀ < U_Gamma (uc_c xg2 y₂) := by
    by_cases hle : uc_c xg2 y₂ ≤ c_peak
    · exact lt_of_le_of_lt hu0_le1 (hU_mono ⟨hc1_lo, by linarith⟩ ⟨hc2_lo, hle⟩ hc12)
    · push Not at hle
      exact lt_of_le_of_lt hu0_le3 (hU_anti ⟨hle.le, hc2_hi⟩ ⟨by linarith, hc3_hi⟩ hc23)
  rw [← hU2_eq, ← hphi₂] at hu0_lt2
  have hxg2_lt : xg2 < x₂ := by
    by_contra hge; push Not at hge
    have := hanti_of hy₂ (lt_trans h23 hy₃) hxg2_neg.le
      (by by_contra h; push Not at h; linarith [det_pos_of_uX_nonneg hy₂ h (Or.inl hxg2_neg.ne)]) hge hux₂
    linarith
  exact hlt2 x₂ hxg2_lt hx₂_le

/- Section 6: Implicit-curve branch counting and final theorem `OMA.solution` -/

lemma encard_le_one_of_strictMonoOn {f : ℝ → ℝ} {S : Set ℝ} (hf : StrictMonoOn f S) (w : ℝ) :
    {y ∈ S | f y = w}.encard ≤ 1 := by
  rw [Set.encard_le_one_iff]
  rintro a b ⟨haS, haw⟩ ⟨hbS, hbw⟩
  rcases lt_trichotomy a b with h | rfl | h
  · linarith [hf haS hbS h]
  · rfl
  · linarith [hf hbS haS h]

lemma encard_le_one_of_strictAntiOn {f : ℝ → ℝ} {S : Set ℝ} (hf : StrictAntiOn f S) (w : ℝ) :
    {y ∈ S | f y = w}.encard ≤ 1 := by
  rw [Set.encard_le_one_iff]
  rintro a b ⟨haS, haw⟩ ⟨hbS, hbw⟩
  rcases lt_trichotomy a b with h | rfl | h
  · linarith [hf haS hbS h]
  · rfl
  · linarith [hf hbS haS h]

lemma encard_graph_le {E : Set (ℝ × ℝ)} {T : Set ℝ} {g : ℝ → ℝ}
    (hsub : ∀ p ∈ E, p.2 ∈ T ∧ p.1 = g p.2) : E.encard ≤ T.encard := by
  have h1 : E ⊆ (fun y => (g y, y)) '' T := fun p hp =>
    ⟨p.2, (hsub p hp).1, Prod.ext (hsub p hp).2.symm rfl⟩
  exact le_trans (Set.encard_le_encard h1) (Set.encard_image_le _ _)

lemma encard_union4_le_four {A B C D : Set (ℝ × ℝ)}
    (hA : A.encard ≤ 1) (hB : B.encard ≤ 1) (hC : C.encard ≤ 1) (hD : D.encard ≤ 1) :
    (A ∪ B ∪ C ∪ D).encard ≤ 4 := by
  calc (A ∪ B ∪ C ∪ D).encard
      ≤ (A ∪ B ∪ C).encard + D.encard := Set.encard_union_le _ _
    _ ≤ ((A ∪ B).encard + C.encard) + D.encard := by gcongr; exact Set.encard_union_le _ _
    _ ≤ ((A.encard + B.encard) + C.encard) + D.encard := by gcongr; exact Set.encard_union_le _ _
    _ ≤ ((1 + 1) + 1) + 1 := by gcongr
    _ = 4 := by norm_num

lemma implicit_phiV_deriv {g : ℝ → ℝ} {y u₀ : ℝ} (hy : 0 < y)
    (heq : ∀ᶠ t in nhds y, phiU (g t) t = u₀)
    (hcont : ContinuousAt g y) (hux : uX_xy (g y) y ≠ 0) :
    HasDerivAt (fun t => phiV (g t) t)
      ((uX_xy (g y) y * vY_xy (g y) y - uY_xy (g y) y * vX_xy (g y) y) / uX_xy (g y) y) y := by
  have hg := implicit_hasDerivAt (hasFDerivAt_phiU (g y) hy) hux heq hcont
  have hv := hasDerivAt_comp_lin2 (g := g) (h := id) (hasFDerivAt_phiV (g y) hy) hg (hasDerivAt_id y)
  exact hv.congr_deriv (by simp only [id_eq]; field_simp [hux]; ring)

lemma phiU_gt_x_of_gt_one {x y : ℝ} (hx : 1 < x) (hy : 0 < y) : x < phiU x y := by
  unfold phiU
  have h1 := r1_pos x hy; have h2 := r2_pos x hy; have hq := Fq_pos x hy
  have hFx : 0 < Fx x y := by unfold Fx; positivity
  have : 0 < Fx x y / (Fq x y) ^ 3 := div_pos hFx (pow_pos hq 3)
  linarith

lemma phiU_lt_x_of_lt_neg_one {x y : ℝ} (hx : x < -1) (hy : 0 < y) : phiU x y < x := by
  have h := phiU_gt_x_of_gt_one (by linarith : 1 < -x) hy
  rw [phiU_neg_x] at h; linarith

lemma phiU_continuousAt {x y : ℝ} (hy : 0 < y) :
    ContinuousAt (fun p : ℝ × ℝ => phiU p.1 p.2) (x, y) :=
  (hasFDerivAt_phiU x hy).continuousAt

lemma phiV_continuousAt {x y : ℝ} (hy : 0 < y) :
    ContinuousAt (fun p : ℝ × ℝ => phiV p.1 p.2) (x, y) :=
  (hasFDerivAt_phiV x hy).continuousAt

lemma continuousAt_phiV_comp {g : ℝ → ℝ} {y : ℝ} (hy : 0 < y) (hg : ContinuousAt g y) :
    ContinuousAt (fun t => phiV (g t) t) y := by
  have h1 : ContinuousAt (fun t => (g t, t)) y := hg.prodMk continuousAt_id
  have h2 : ContinuousAt ((fun p : ℝ × ℝ => phiV p.1 p.2) ∘ fun t => (g t, t)) y :=
    ContinuousAt.comp (g := fun p : ℝ × ℝ => phiV p.1 p.2) (f := fun t => (g t, t))
      (phiV_continuousAt (x := g y) hy) h1
  simpa only [Function.comp_def] using h2

lemma tendsto_phiV_comp {g : ℝ → ℝ} {y x₀ : ℝ} {l : Filter ℝ} (hy : 0 < y)
    (hg : Filter.Tendsto g l (nhds x₀)) (ht : Filter.Tendsto id l (nhds y)) :
    Filter.Tendsto (fun t => phiV (g t) t) l (nhds (phiV x₀ y)) := by
  have h1 : Filter.Tendsto (fun t => (g t, t)) l (nhds (x₀, y)) := hg.prodMk_nhds ht
  have h2 : Filter.Tendsto ((fun p : ℝ × ℝ => phiV p.1 p.2) ∘ fun t => (g t, t)) l (nhds (phiV x₀ y)) :=
    (phiV_continuousAt (x := x₀) hy).tendsto.comp h1
  simpa only [Function.comp_def] using h2

lemma phiU_continuousOn_x {y : ℝ} (hy : 0 < y) : Continuous (fun x => phiU x y) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_x_of_lin2 (hasFDerivAt_phiU x hy)).continuousAt

lemma phiU_continuousAt_y (x : ℝ) {y : ℝ} (hy : 0 < y) : ContinuousAt (fun t => phiU x t) y :=
  (hasDerivAt_y_of_lin2 (hasFDerivAt_phiU x hy)).continuousAt

/- Case 1: u₀ = 0 -/

lemma exists_unique_xR0 {y : ℝ} (hy : 0 < y) (hylt : y < y0_val) :
    ∃! x : ℝ, 0 < x ∧ phiU x y = 0 ∧ 0 < uX_xy x y ∧
      (∀ t, 0 < t → t < x → phiU t y < 0) ∧ (∀ t, x < t → 0 < phiU t y) := by
  have hux0 : uX_xy 0 y < 0 := y0_val_spec.2.2.2.1 y hy hylt
  obtain ⟨xs, hxs_p, hxs_lt, _, _, hgt_xs, _, _, hanti, hmono⟩ := horizontal_slice_lt_y0 hy hux0
  have hphi_xs : phiU xs y < 0 := by
    rw [← phiU_zero y]; exact hanti ⟨by linarith, hxs_p.le⟩ ⟨by linarith, le_rfl⟩ hxs_p
  have hphi_2 : 0 < phiU 2 y := by linarith [phiU_gt_x_of_gt_one (by norm_num : (1 : ℝ) < 2) hy]
  obtain ⟨xr, hxrIcc, hxrEq⟩ := intermediate_value_Icc (by linarith : xs ≤ 2)
    (phiU_continuousOn_x hy).continuousOn ⟨hphi_xs.le, hphi_2.le⟩
  dsimp only at hxrEq
  have hxr_gt : xs < xr := lt_of_le_of_ne hxrIcc.1 (by rintro rfl; linarith)
  have hlt_neg : ∀ t, 0 < t → t < xr → phiU t y < 0 := by
    intro t ht0 htlt
    by_cases hts : t ≤ xs
    · rw [← phiU_zero y]; exact hanti ⟨by linarith, hxs_p.le⟩ ⟨by linarith, hts⟩ ht0
    · push Not at hts; rw [← hxrEq]; exact hmono hts.le hxr_gt.le htlt
  have hgt_pos : ∀ t, xr < t → 0 < phiU t y := by
    intro t htgt; rw [← hxrEq]; exact hmono hxr_gt.le (le_trans hxr_gt.le htgt.le) htgt
  refine ⟨xr, ⟨lt_trans hxs_p hxr_gt, hxrEq, hgt_xs xr hxr_gt, hlt_neg, hgt_pos⟩, ?_⟩
  rintro x' ⟨hx'0, hx'eq, _, _, _⟩
  rcases lt_trichotomy x' xr with h | rfl | h
  · linarith [hlt_neg x' hx'0 h]
  · rfl
  · linarith [hgt_pos x' h]

noncomputable def xR0_val (y : ℝ) : ℝ :=
  if h : 0 < y ∧ y < y0_val then Classical.choose (exists_unique_xR0 h.1 h.2) else 0

lemma xR0_val_spec {y : ℝ} (hy : 0 < y) (hylt : y < y0_val) :
    0 < xR0_val y ∧ phiU (xR0_val y) y = 0 ∧ 0 < uX_xy (xR0_val y) y ∧
    (∀ t, 0 < t → t < xR0_val y → phiU t y < 0) ∧ (∀ t, xR0_val y < t → 0 < phiU t y) := by
  unfold xR0_val; rw [dif_pos ⟨hy, hylt⟩]
  exact (Classical.choose_spec (exists_unique_xR0 hy hylt)).1

lemma xR0_val_cont {y : ℝ} (hy : 0 < y) (hylt : y < y0_val) : ContinuousAt xR0_val y := by
  have ⟨hxp, _, _, hlt_neg, hgt_pos⟩ := xR0_val_spec hy hylt
  rw [Metric.continuousAt_iff]; intro ε hε
  set a := max (xR0_val y / 2) (xR0_val y - ε / 2)
  set b := xR0_val y + ε / 2 with hb_def
  have ha0 : 0 < a := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have ha_lt : a < xR0_val y := max_lt (by linarith) (by linarith)
  have ha_ge : xR0_val y - ε / 2 ≤ a := le_max_right _ _
  have hb_gt : xR0_val y < b := by linarith [hb_def]
  have hFa : phiU a y < 0 := hlt_neg a ha0 ha_lt
  have hFb : 0 < phiU b y := hgt_pos b hb_gt
  have hev1 : ∀ᶠ t in nhds y, phiU a t < 0 := (phiU_continuousAt_y a hy).eventually (Iio_mem_nhds hFa)
  have hev2 : ∀ᶠ t in nhds y, 0 < phiU b t := (phiU_continuousAt_y b hy).eventually (Ioi_mem_nhds hFb)
  have hev3 : ∀ᶠ t in nhds y, 0 < t ∧ t < y0_val :=
    Filter.eventually_of_mem (Ioo_mem_nhds hy hylt) fun _ ht => ht
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp ((hev1.and hev2).and hev3)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨⟨hFat, hFbt⟩, ⟨ht1, ht2⟩⟩ := hball ht
  have ⟨_, hteq, _, hlt_t, hgt_t⟩ := xR0_val_spec ht1 ht2
  have h1 : a < xR0_val t := by
    by_contra hle; push Not at hle
    rcases eq_or_lt_of_le hle with heq | hgt
    · rw [heq] at hteq; linarith
    · linarith [hgt_t a hgt]
  have h2 : xR0_val t < b := by
    by_contra hge; push Not at hge
    rcases eq_or_lt_of_le hge with heq | hlt
    · rw [← heq] at hteq; linarith
    · linarith [hlt_t b (by linarith) hlt]
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hb_def]

lemma phi_preimage_encard_le_four_zero (w₀ : ℝ) :
    {p : ℝ × ℝ | 0 < p.2 ∧ phiU p.1 p.2 = 0 ∧ phiV p.1 p.2 = w₀}.encard ≤ 4 := by
  set S := {p : ℝ × ℝ | 0 < p.2 ∧ phiU p.1 p.2 = 0 ∧ phiV p.1 p.2 = w₀}
  set S1 := {p ∈ S | p.1 = 0 ∧ p.2 ≤ y_bot_val}
  set S2 := {p ∈ S | p.1 = 0 ∧ y_bot_val < p.2}
  set S3 := {p ∈ S | 0 < p.1}
  set S4 := {p ∈ S | p.1 < 0}
  have hsub : S ⊆ S1 ∪ S2 ∪ S3 ∪ S4 := by
    intro p hp
    rcases lt_trichotomy p.1 0 with hlt | heq | hgt
    · exact Or.inr ⟨hp, hlt⟩
    · by_cases hy : p.2 ≤ y_bot_val
      · exact Or.inl (Or.inl (Or.inl ⟨hp, heq, hy⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hp, heq, lt_of_not_ge hy⟩))
    · exact Or.inl (Or.inr ⟨hp, hgt⟩)
  have hS1 : S1.encard ≤ 1 := by
    have hanti : StrictAntiOn (fun y => phiV 0 y) (Set.Ioc 0 y_bot_val) := by
      apply strictAntiOn_of_deriv_neg (convex_Ioc 0 y_bot_val)
      · exact fun y hy => (hasDerivAt_y_of_lin2 (hasFDerivAt_phiV 0 hy.1)).continuousAt.continuousWithinAt
      · intro y hy; rw [interior_Ioc] at hy
        rw [(hasDerivAt_y_of_lin2 (hasFDerivAt_phiV 0 hy.1)).deriv]
        have hux : uX_xy 0 y < 0 := y0_val_spec.2.2.2.1 y hy.1 (lt_trans hy.2 y_bot_lt_y0)
        have hdet : 0 < uX_xy 0 y * vY_xy 0 y - uY_xy 0 y * vX_xy 0 y :=
          (det_xy_axis_sign hy.1).2.mpr (Or.inl hy.2)
        have huy : uY_xy 0 y = 0 := by rw [uY_xy_eq_uc 0 hy.1, r1, r2]; simp
        rw [huy, zero_mul, sub_zero] at hdet
        nlinarith
    have hgr : S1.encard ≤ {y ∈ Set.Ioc 0 y_bot_val | phiV 0 y = w₀}.encard :=
      encard_graph_le (g := fun _ => 0) fun p ⟨⟨hy, _, hV⟩, hx0, hyle⟩ =>
        ⟨⟨⟨hy, hyle⟩, by rwa [← hx0]⟩, hx0⟩
    exact le_trans hgr (encard_le_one_of_strictAntiOn hanti w₀)
  have hS2 : S2.encard ≤ 1 := by
    have hmono : StrictMonoOn (fun y => phiV 0 y) (Set.Ioi y_bot_val) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioi y_bot_val)
      · exact fun y hy =>
          (hasDerivAt_y_of_lin2 (hasFDerivAt_phiV 0 (lt_trans uc_c_y_bot.1 hy))).continuousAt.continuousWithinAt
      · intro y hy; rw [interior_Ioi] at hy
        have hypos : 0 < y := lt_trans uc_c_y_bot.1 hy
        rw [(hasDerivAt_y_of_lin2 (hasFDerivAt_phiV 0 hypos)).deriv]
        by_cases hlt : y < y0_val
        · have hux : uX_xy 0 y < 0 := y0_val_spec.2.2.2.1 y hypos hlt
          have hdet : uX_xy 0 y * vY_xy 0 y - uY_xy 0 y * vX_xy 0 y < 0 :=
            (det_xy_axis_sign hypos).1.mpr ⟨hy, hlt⟩
          have huy : uY_xy 0 y = 0 := by rw [uY_xy_eq_uc 0 hypos, r1, r2]; simp
          rw [huy, zero_mul, sub_zero] at hdet
          nlinarith
        · push Not at hlt
          have hux : 0 ≤ uX_xy 0 y := by
            rcases eq_or_lt_of_le hlt with rfl | hgt
            · exact y0_val_spec.2.2.1.ge
            · exact (y0_val_spec.2.2.2.2 y hgt).le
          rw [vY_xy_eq_uc 0 hypos]
          exact vY_uc_pos_of_uX_uc_nonneg (uc_u_nonneg 0 hypos) (uc_c_bounds 0 hypos).1 (uc_c_bounds 0 hypos).2
            (by rwa [← uX_xy_eq_uc 0 hypos])
    have hgr : S2.encard ≤ {y ∈ Set.Ioi y_bot_val | phiV 0 y = w₀}.encard :=
      encard_graph_le (g := fun _ => 0) fun p ⟨⟨_, _, hV⟩, hx0, hygt⟩ =>
        ⟨⟨hygt, by rwa [← hx0]⟩, hx0⟩
    exact le_trans hgr (encard_le_one_of_strictMonoOn hmono w₀)
  have hS3 : S3.encard ≤ 1 := by
    have hmono : StrictMonoOn (fun y => phiV (xR0_val y) y) (Set.Ioo 0 y0_val) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioo 0 y0_val)
      · intro y hy
        exact (continuousAt_phiV_comp hy.1 (xR0_val_cont hy.1 hy.2)).continuousWithinAt
      · intro y hy; rw [interior_Ioo] at hy
        have ⟨_, _, hux, _, _⟩ := xR0_val_spec hy.1 hy.2
        have heq : ∀ᶠ t in nhds y, phiU (xR0_val t) t = 0 :=
          Filter.eventually_of_mem (Ioo_mem_nhds hy.1 hy.2) fun t ht => (xR0_val_spec ht.1 ht.2).2.1
        have hd := implicit_phiV_deriv hy.1 heq (xR0_val_cont hy.1 hy.2) hux.ne'
        rw [hd.deriv]
        exact div_pos (det_pos_of_uX_nonneg hy.1 hux.le (Or.inr hux)) hux
    have hgr : S3.encard ≤ {y ∈ Set.Ioo 0 y0_val | phiV (xR0_val y) y = w₀}.encard := by
      refine encard_graph_le (g := xR0_val) fun p ⟨⟨hy, hU, hV⟩, hxp⟩ => ?_
      have hylt : p.2 < y0_val := by
        by_contra hge; push Not at hge
        have hux0 : 0 ≤ uX_xy 0 p.2 := by
          rcases eq_or_lt_of_le hge with heq | hgt
          · rw [← heq]; exact y0_val_spec.2.2.1.ge
          · exact (y0_val_spec.2.2.2.2 p.2 hgt).le
        have hsm := (horizontal_slice_ge_y0 hy hux0).2
        have := hsm hxp; dsimp only at this; rw [phiU_zero] at this; linarith
      have ⟨_, _, _, hlt_n, hgt_p⟩ := xR0_val_spec hy hylt
      have hx_eq : p.1 = xR0_val p.2 := by
        rcases lt_trichotomy p.1 (xR0_val p.2) with h | h | h
        · linarith [hlt_n p.1 hxp h]
        · exact h
        · linarith [hgt_p p.1 h]
      exact ⟨⟨⟨hy, hylt⟩, by rwa [← hx_eq]⟩, hx_eq⟩
    exact le_trans hgr (encard_le_one_of_strictMonoOn hmono w₀)
  have hS4 : S4.encard ≤ 1 := by
    have hinj : Function.Injective (fun p : ℝ × ℝ => (-p.1, p.2)) := fun a b h => by
      simp only [Prod.mk.injEq, neg_inj] at h; exact Prod.ext h.1 h.2
    have hmap : Set.MapsTo (fun p : ℝ × ℝ => (-p.1, p.2)) S4 S3 := fun p ⟨⟨hy, hU, hV⟩, hxn⟩ =>
      ⟨⟨hy, by rw [phiU_neg_x, hU, neg_zero], by rw [phiV_neg_x, hV]⟩, by linarith⟩
    exact le_trans (Set.encard_le_encard_of_injOn hmap hinj.injOn) hS3
  exact le_trans (Set.encard_le_encard hsub) (encard_union4_le_four hS1 hS2 hS3 hS4)

/- Case 2: u₀ > 0 -/

lemma exists_y_lt_of_forall_Icc_lt {y_a u₀ : ℝ} (hy_a : 0 < y_a)
    (hlt : ∀ x ∈ Set.Icc (-1 : ℝ) 0, phiU x y_a < u₀) :
    ∃ y' : ℝ, 0 < y' ∧ y' < y_a ∧ ∀ y ∈ Set.Icc y' y_a, ∀ x ∈ Set.Icc (-1 : ℝ) 0, phiU x y < u₀ := by
  have hK1 : IsCompact (Set.Icc (-1 : ℝ) 0) := isCompact_Icc
  have hK2 : IsCompact (Set.Icc (y_a / 2) y_a) := isCompact_Icc
  have hne : (Set.Icc (-1 : ℝ) 0).Nonempty := Set.nonempty_Icc.mpr (by norm_num)
  have hcont_x : ContinuousOn (fun x => phiU x y_a) (Set.Icc (-1) 0) :=
    (phiU_continuousOn_x hy_a).continuousOn
  obtain ⟨xm, hxm_mem, hxm_max⟩ := hK1.exists_isMaxOn hne hcont_x
  set ε := (u₀ - phiU xm y_a) / 2 with hε_def
  have hε : 0 < ε := by linarith [hlt xm hxm_mem, hε_def]
  have hcont_prod : ContinuousOn (fun p : ℝ × ℝ => phiU p.1 p.2) (Set.Icc (-1) 0 ×ˢ Set.Icc (y_a / 2) y_a) :=
    fun p hp => (phiU_continuousAt (by linarith [hp.2.1])).continuousWithinAt
  have huc := (hK1.prod hK2).uniformContinuousOn_of_continuous hcont_prod
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ_prop⟩ := huc ε hε
  set y' := max (y_a / 2) (y_a - δ / 2)
  have hy'0 : 0 < y' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hy'lt : y' < y_a := max_lt (by linarith) (by linarith)
  refine ⟨y', hy'0, hy'lt, fun y hy x hx => ?_⟩
  have hy_mem : y ∈ Set.Icc (y_a / 2) y_a := ⟨le_trans (le_max_left _ _) hy.1, hy.2⟩
  have hya_mem : y_a ∈ Set.Icc (y_a / 2) y_a := ⟨by linarith, le_rfl⟩
  have hdist : dist (x, y) (x, y_a) < δ := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, abs_of_nonpos (by linarith [hy.2])]
    exact max_lt hδ (by linarith [le_max_right (y_a / 2) (y_a - δ / 2), hy.1])
  have hdiff := hδ_prop (x, y) ⟨hx, hy_mem⟩ (x, y_a) ⟨hx, hya_mem⟩ hdist
  rw [Real.dist_eq, abs_lt] at hdiff; dsimp only at hdiff
  have hle_m : phiU x y_a ≤ phiU xm y_a := hxm_max hx
  linarith [hε_def]

noncomputable def xstar_val (y : ℝ) : ℝ :=
  if h : 0 < y ∧ y < y0_val then
    Classical.choose (horizontal_slice_lt_y0 h.1 (y0_val_spec.2.2.2.1 y h.1 h.2))
  else 0

lemma xstar_val_spec {y : ℝ} (hy1 : 0 < y) (hy2 : y < y0_val) :
    0 < xstar_val y ∧ xstar_val y < 1 ∧ uX_xy (xstar_val y) y = 0 ∧
    (∀ x, -xstar_val y < x → x < xstar_val y → uX_xy x y < 0) ∧
    (∀ x, xstar_val y < x → 0 < uX_xy x y) ∧
    (∀ x, x < -xstar_val y → 0 < uX_xy x y) ∧
    StrictMonoOn (fun x => phiU x y) (Set.Iic (-xstar_val y)) ∧
    StrictAntiOn (fun x => phiU x y) (Set.Icc (-xstar_val y) (xstar_val y)) ∧
    StrictMonoOn (fun x => phiU x y) (Set.Ici (xstar_val y)) := by
  unfold xstar_val; rw [dif_pos ⟨hy1, hy2⟩]
  exact Classical.choose_spec (horizontal_slice_lt_y0 hy1 (y0_val_spec.2.2.2.1 y hy1 hy2))

noncomputable def M_val (y : ℝ) : ℝ := phiU (-xstar_val y) y

lemma M_val_strictAnti : StrictAntiOn M_val (Set.Ioo 0 y0_val) := by
  intro y₁ hy₁ y₂ hy₂ hlt
  have hs1 := xstar_val_spec hy₁.1 hy₁.2
  have hs2 := xstar_val_spec hy₂.1 hy₂.2
  exact fold_val_strictAnti hy₁.1 hlt hs1.1 hs2.1 hs1.2.2.2.2.2.2.1 hs1.2.2.2.2.2.2.2.1

lemma phiU_le_M_val {y x : ℝ} (hy1 : 0 < y) (hy2 : y < y0_val) (hx : x ≤ 0) :
    phiU x y ≤ M_val y := by
  have hs := xstar_val_spec hy1 hy2
  unfold M_val
  by_cases h : x ≤ -xstar_val y
  · exact hs.2.2.2.2.2.2.1.monotoneOn h (Set.mem_Iic.mpr le_rfl) h
  · push Not at h
    exact hs.2.2.2.2.2.2.2.1.antitoneOn ⟨le_rfl, by linarith [hs.1]⟩ ⟨h.le, by linarith [hs.1]⟩ h.le

lemma exists_unique_xR {u₀ y : ℝ} (hu₀ : 0 < u₀) (hy : 0 < y) :
    ∃! x : ℝ, 0 < x ∧ phiU x y = u₀ ∧ 0 < uX_xy x y ∧
      (∀ t, 0 ≤ t → t < x → phiU t y < u₀) ∧ (∀ t, x < t → u₀ < phiU t y) := by
  set X := max 2 (u₀ + 1)
  have hX1 : 1 < X := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hXu : u₀ < phiU X y := lt_trans (lt_of_lt_of_le (by linarith) (le_max_right _ _))
    (phiU_gt_x_of_gt_one hX1 hy)
  by_cases hlt : y < y0_val
  · have hs := xstar_val_spec hy hlt
    have hphi_xs : phiU (xstar_val y) y < 0 := by
      rw [← phiU_zero y]
      exact hs.2.2.2.2.2.2.2.1 ⟨by linarith [hs.1], hs.1.le⟩ ⟨by linarith [hs.1], le_rfl⟩ hs.1
    have hxs_le_X : xstar_val y ≤ X := by linarith [hs.2.1, le_max_left (2 : ℝ) (u₀ + 1)]
    obtain ⟨xr, hxrIcc, hxrEq⟩ := intermediate_value_Icc hxs_le_X
      (phiU_continuousOn_x hy).continuousOn ⟨by linarith, hXu.le⟩
    dsimp only at hxrEq
    have hxr_gt : xstar_val y < xr := lt_of_le_of_ne hxrIcc.1 (by rintro rfl; linarith)
    have hlt_u : ∀ t, 0 ≤ t → t < xr → phiU t y < u₀ := by
      intro t ht0 htlt
      by_cases hts : t ≤ xstar_val y
      · have hle0 : phiU t y ≤ 0 := by
          rw [← phiU_zero y]
          exact hs.2.2.2.2.2.2.2.1.antitoneOn ⟨by linarith [hs.1], hs.1.le⟩ ⟨by linarith [hs.1], hts⟩ ht0
        linarith
      · push Not at hts; rw [← hxrEq]; exact hs.2.2.2.2.2.2.2.2 hts.le hxr_gt.le htlt
    have hgt_u : ∀ t, xr < t → u₀ < phiU t y := by
      intro t htgt; rw [← hxrEq]; exact hs.2.2.2.2.2.2.2.2 hxr_gt.le (le_trans hxr_gt.le htgt.le) htgt
    refine ⟨xr, ⟨lt_trans hs.1 hxr_gt, hxrEq, hs.2.2.2.2.1 xr hxr_gt, hlt_u, hgt_u⟩, ?_⟩
    rintro x' ⟨hx'0, hx'eq, _, _, _⟩
    rcases lt_trichotomy x' xr with h | rfl | h
    · linarith [hlt_u x' hx'0.le h]
    · rfl
    · linarith [hgt_u x' h]
  · push Not at hlt
    have hux0 : 0 ≤ uX_xy 0 y := by
      rcases eq_or_lt_of_le hlt with rfl | hgt
      · exact y0_val_spec.2.2.1.ge
      · exact (y0_val_spec.2.2.2.2 y hgt).le
    have ⟨hpos_ne, hsm⟩ := horizontal_slice_ge_y0 hy hux0
    obtain ⟨xr, hxrIcc, hxrEq⟩ := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ X)
      (phiU_continuousOn_x hy).continuousOn ⟨by rw [phiU_zero]; exact hu₀.le, hXu.le⟩
    dsimp only at hxrEq
    have hxr_pos : 0 < xr := lt_of_le_of_ne hxrIcc.1 (by rintro rfl; rw [phiU_zero] at hxrEq; linarith)
    refine ⟨xr, ⟨hxr_pos, hxrEq, hpos_ne xr hxr_pos.ne',
      fun t _ ht => by rw [← hxrEq]; exact hsm ht,
      fun t ht => by rw [← hxrEq]; exact hsm ht⟩, ?_⟩
    rintro x' ⟨_, hx'eq, _, _, _⟩
    rcases lt_trichotomy x' xr with h | rfl | h
    · linarith [hsm h]
    · rfl
    · linarith [hsm h]

noncomputable def xR_val (u₀ y : ℝ) : ℝ :=
  if h : 0 < u₀ ∧ 0 < y then Classical.choose (exists_unique_xR h.1 h.2) else 0

lemma xR_val_spec {u₀ y : ℝ} (hu₀ : 0 < u₀) (hy : 0 < y) :
    0 < xR_val u₀ y ∧ phiU (xR_val u₀ y) y = u₀ ∧ 0 < uX_xy (xR_val u₀ y) y ∧
    (∀ t, 0 ≤ t → t < xR_val u₀ y → phiU t y < u₀) ∧ (∀ t, xR_val u₀ y < t → u₀ < phiU t y) := by
  unfold xR_val; rw [dif_pos ⟨hu₀, hy⟩]
  exact (Classical.choose_spec (exists_unique_xR hu₀ hy)).1

lemma xR_val_cont {u₀ y : ℝ} (hu₀ : 0 < u₀) (hy : 0 < y) : ContinuousAt (xR_val u₀) y := by
  have ⟨hxp, _, _, hlt_u, hgt_u⟩ := xR_val_spec hu₀ hy
  rw [Metric.continuousAt_iff]; intro ε hε
  set a := max 0 (xR_val u₀ y - ε / 2)
  set b := xR_val u₀ y + ε / 2 with hb_def
  have ha0 : 0 ≤ a := le_max_left _ _
  have ha_lt : a < xR_val u₀ y := max_lt hxp (by linarith)
  have ha_ge : xR_val u₀ y - ε / 2 ≤ a := le_max_right _ _
  have hb_gt : xR_val u₀ y < b := by linarith [hb_def]
  have hFa : phiU a y < u₀ := hlt_u a ha0 ha_lt
  have hFb : u₀ < phiU b y := hgt_u b hb_gt
  have hev1 : ∀ᶠ t in nhds y, phiU a t < u₀ := (phiU_continuousAt_y a hy).eventually (Iio_mem_nhds hFa)
  have hev2 : ∀ᶠ t in nhds y, u₀ < phiU b t := (phiU_continuousAt_y b hy).eventually (Ioi_mem_nhds hFb)
  have hev3 : ∀ᶠ t in nhds y, 0 < t := Ioi_mem_nhds hy
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp ((hev1.and hev2).and hev3)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨⟨hFat, hFbt⟩, ht0⟩ := hball ht
  have ⟨_, hteq, _, hlt_t, hgt_t⟩ := xR_val_spec hu₀ ht0
  have h1 : a < xR_val u₀ t := by
    by_contra hle; push Not at hle
    rcases eq_or_lt_of_le hle with heq | hgt
    · rw [heq] at hteq; linarith
    · linarith [hgt_t a hgt]
  have h2 : xR_val u₀ t < b := by
    by_contra hge; push Not at hge
    rcases eq_or_lt_of_le hge with heq | hlt
    · rw [← heq] at hteq; linarith
    · linarith [hlt_t b (by linarith) hlt]
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hb_def]

lemma exists_xLM {u₀ y : ℝ} (hu₀ : 0 < u₀) (hy1 : 0 < y) (hy2 : y < y0_val) (hMu : u₀ < M_val y) :
    ∃ xL xM : ℝ, xL < -xstar_val y ∧ -xstar_val y < xM ∧ xM < 0 ∧
      phiU xL y = u₀ ∧ phiU xM y = u₀ ∧
      0 < uX_xy xL y ∧ uX_xy xM y < 0 ∧
      (∀ t, t < xL → phiU t y < u₀) ∧
      (∀ t, xL < t → t < xM → u₀ < phiU t y) ∧
      (∀ t, xM < t → t ≤ 0 → phiU t y < u₀) := by
  have hMu' : u₀ < phiU (-xstar_val y) y := hMu
  have hs := xstar_val_spec hy1 hy2
  have hX_lt : -2 < -xstar_val y := by linarith [hs.2.1]
  have hphi_neg2 : phiU (-2) y < u₀ := by
    have := phiU_lt_x_of_lt_neg_one (by norm_num : (-2 : ℝ) < -1) hy1; linarith
  obtain ⟨xL, hxLIcc, hxLeq⟩ := intermediate_value_Icc hX_lt.le
    (phiU_continuousOn_x hy1).continuousOn ⟨hphi_neg2.le, hMu'.le⟩
  dsimp only at hxLeq
  have hxL_lt : xL < -xstar_val y := lt_of_le_of_ne hxLIcc.2 (by rintro rfl; linarith)
  obtain ⟨xM, hxMIcc, hxMeq⟩ := intermediate_value_Icc' (by linarith [hs.1] : -xstar_val y ≤ 0)
    (phiU_continuousOn_x hy1).continuousOn ⟨by rw [phiU_zero]; exact hu₀.le, hMu'.le⟩
  dsimp only at hxMeq
  have hxM_gt : -xstar_val y < xM := lt_of_le_of_ne hxMIcc.1 (by rintro rfl; linarith)
  have hxM_lt : xM < 0 := lt_of_le_of_ne hxMIcc.2 (by rintro rfl; rw [phiU_zero] at hxMeq; linarith)
  refine ⟨xL, xM, hxL_lt, hxM_gt, hxM_lt, hxLeq, hxMeq,
    hs.2.2.2.2.2.1 xL hxL_lt, hs.2.2.2.1 xM hxM_gt (by linarith [hs.1]), ?_, ?_, ?_⟩
  · intro t ht; rw [← hxLeq]; exact hs.2.2.2.2.2.2.1 (le_trans ht.le hxL_lt.le) hxL_lt.le ht
  · intro t ht1 ht2
    by_cases hts : t ≤ -xstar_val y
    · rw [← hxLeq]; exact hs.2.2.2.2.2.2.1 hxL_lt.le hts ht1
    · push Not at hts; rw [← hxMeq]
      exact hs.2.2.2.2.2.2.2.1 ⟨hts.le, by linarith [hs.1]⟩ ⟨hxM_gt.le, by linarith [hs.1]⟩ ht2
  · intro t ht1 ht2; rw [← hxMeq]
    exact hs.2.2.2.2.2.2.2.1 ⟨hxM_gt.le, by linarith [hs.1]⟩ ⟨by linarith, by linarith [hs.1]⟩ ht1

noncomputable def xL_val (u₀ y : ℝ) : ℝ :=
  if h : 0 < u₀ ∧ 0 < y ∧ y < y0_val ∧ u₀ < M_val y then
    Classical.choose (exists_xLM h.1 h.2.1 h.2.2.1 h.2.2.2)
  else 0

noncomputable def xM_val (u₀ y : ℝ) : ℝ :=
  if h : 0 < u₀ ∧ 0 < y ∧ y < y0_val ∧ u₀ < M_val y then
    Classical.choose (Classical.choose_spec (exists_xLM h.1 h.2.1 h.2.2.1 h.2.2.2))
  else 0

lemma xLM_val_spec {u₀ y : ℝ} (hu₀ : 0 < u₀) (hy1 : 0 < y) (hy2 : y < y0_val) (hMu : u₀ < M_val y) :
    xL_val u₀ y < -xstar_val y ∧ -xstar_val y < xM_val u₀ y ∧ xM_val u₀ y < 0 ∧
    phiU (xL_val u₀ y) y = u₀ ∧ phiU (xM_val u₀ y) y = u₀ ∧
    0 < uX_xy (xL_val u₀ y) y ∧ uX_xy (xM_val u₀ y) y < 0 ∧
    (∀ t, t < xL_val u₀ y → phiU t y < u₀) ∧
    (∀ t, xL_val u₀ y < t → t < xM_val u₀ y → u₀ < phiU t y) ∧
    (∀ t, xM_val u₀ y < t → t ≤ 0 → phiU t y < u₀) := by
  have hcond : 0 < u₀ ∧ 0 < y ∧ y < y0_val ∧ u₀ < M_val y := ⟨hu₀, hy1, hy2, hMu⟩
  unfold xL_val xM_val
  simp only [dif_pos hcond]
  exact Classical.choose_spec (Classical.choose_spec (exists_xLM hu₀ hy1 hy2 hMu))

lemma xL_val_cont {u₀ y1 y : ℝ} (hu₀ : 0 < u₀) (hy1_pos : 0 < y1) (hy1_lt : y1 < y0_val)
    (hM_y1 : M_val y1 = u₀) (hy1 : 0 < y) (hy2 : y < y1) : ContinuousAt (xL_val u₀) y := by
  have hMu : ∀ {t}, 0 < t → t < y1 → u₀ < M_val t := fun {t} ht1 ht2 => by
    rw [← hM_y1]; exact M_val_strictAnti ⟨ht1, lt_trans ht2 hy1_lt⟩ ⟨hy1_pos, hy1_lt⟩ ht2
  have hsp := xLM_val_spec hu₀ hy1 (lt_trans hy2 hy1_lt) (hMu hy1 hy2)
  rw [Metric.continuousAt_iff]; intro ε hε
  set a := xL_val u₀ y - ε / 2 with ha_def
  set b := min (-xstar_val y) (xL_val u₀ y + ε / 2)
  have hb_gt : xL_val u₀ y < b := lt_min hsp.1 (by linarith)
  have hb_ltM : b < xM_val u₀ y := lt_of_le_of_lt (min_le_left _ _) hsp.2.1
  have hFa : phiU a y < u₀ := hsp.2.2.2.2.2.2.2.1 a (by linarith [ha_def])
  have hFb : u₀ < phiU b y := hsp.2.2.2.2.2.2.2.2.1 b hb_gt hb_ltM
  have hev1 : ∀ᶠ t in nhds y, phiU a t < u₀ := (phiU_continuousAt_y a hy1).eventually (Iio_mem_nhds hFa)
  have hev2 : ∀ᶠ t in nhds y, u₀ < phiU b t := (phiU_continuousAt_y b hy1).eventually (Ioi_mem_nhds hFb)
  have hev3 : ∀ᶠ t in nhds y, 0 < t ∧ t < y1 :=
    Filter.eventually_of_mem (Ioo_mem_nhds hy1 hy2) fun _ ht => ht
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp ((hev1.and hev2).and hev3)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨⟨hFat, hFbt⟩, ⟨ht1, ht2⟩⟩ := hball ht
  have hst := xLM_val_spec hu₀ ht1 (lt_trans ht2 hy1_lt) (hMu ht1 ht2)
  have hb_in : xL_val u₀ t < b ∧ b < xM_val u₀ t := by
    constructor
    · by_contra hle; push Not at hle
      rcases eq_or_lt_of_le hle with heq | hlt
      · rw [← heq] at hst; linarith [hst.2.2.2.1]
      · linarith [hst.2.2.2.2.2.2.2.1 b hlt]
    · by_contra hge; push Not at hge
      rcases eq_or_lt_of_le hge with heq | hgt
      · rw [heq] at hst; linarith [hst.2.2.2.2.1]
      · have hb_le0 : b ≤ 0 := le_trans (min_le_left _ _) (by linarith [(xstar_val_spec hy1 (lt_trans hy2 hy1_lt)).1])
        linarith [hst.2.2.2.2.2.2.2.2.2 b hgt hb_le0]
  have ha_lt : a < xL_val u₀ t := by
    by_contra hge; push Not at hge
    rcases eq_or_lt_of_le hge with heq | hgt
    · rw [heq] at hst; linarith [hst.2.2.2.1]
    · linarith [hst.2.2.2.2.2.2.2.2.1 a hgt (by linarith [hb_in.2])]
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ha_def, min_le_right (-xstar_val y) (xL_val u₀ y + ε / 2)]

lemma xM_val_cont {u₀ y1 y : ℝ} (hu₀ : 0 < u₀) (hy1_pos : 0 < y1) (hy1_lt : y1 < y0_val)
    (hM_y1 : M_val y1 = u₀) (hy1 : 0 < y) (hy2 : y < y1) : ContinuousAt (xM_val u₀) y := by
  have hMu : ∀ {t}, 0 < t → t < y1 → u₀ < M_val t := fun {t} ht1 ht2 => by
    rw [← hM_y1]; exact M_val_strictAnti ⟨ht1, lt_trans ht2 hy1_lt⟩ ⟨hy1_pos, hy1_lt⟩ ht2
  have hsp := xLM_val_spec hu₀ hy1 (lt_trans hy2 hy1_lt) (hMu hy1 hy2)
  rw [Metric.continuousAt_iff]; intro ε hε
  set b := max (-xstar_val y) (xM_val u₀ y - ε / 2)
  set d := min 0 (xM_val u₀ y + ε / 2)
  have hb_gtL : xL_val u₀ y < b := lt_of_lt_of_le hsp.1 (le_max_left _ _)
  have hb_lt : b < xM_val u₀ y := max_lt hsp.2.1 (by linarith)
  have hd_gt : xM_val u₀ y < d := lt_min hsp.2.2.1 (by linarith)
  have hd_le0 : d ≤ 0 := min_le_left _ _
  have hFb : u₀ < phiU b y := hsp.2.2.2.2.2.2.2.2.1 b hb_gtL hb_lt
  have hFd : phiU d y < u₀ := hsp.2.2.2.2.2.2.2.2.2 d hd_gt hd_le0
  have hev1 : ∀ᶠ t in nhds y, u₀ < phiU b t := (phiU_continuousAt_y b hy1).eventually (Ioi_mem_nhds hFb)
  have hev2 : ∀ᶠ t in nhds y, phiU d t < u₀ := (phiU_continuousAt_y d hy1).eventually (Iio_mem_nhds hFd)
  have hev3 : ∀ᶠ t in nhds y, 0 < t ∧ t < y1 :=
    Filter.eventually_of_mem (Ioo_mem_nhds hy1 hy2) fun _ ht => ht
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp ((hev1.and hev2).and hev3)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨⟨hFbt, hFdt⟩, ⟨ht1, ht2⟩⟩ := hball ht
  have hst := xLM_val_spec hu₀ ht1 (lt_trans ht2 hy1_lt) (hMu ht1 ht2)
  have hb_in : xL_val u₀ t < b ∧ b < xM_val u₀ t := by
    constructor
    · by_contra hle; push Not at hle
      rcases eq_or_lt_of_le hle with heq | hlt
      · rw [← heq] at hst; linarith [hst.2.2.2.1]
      · linarith [hst.2.2.2.2.2.2.2.1 b hlt]
    · by_contra hge; push Not at hge
      rcases eq_or_lt_of_le hge with heq | hgt
      · rw [heq] at hst; linarith [hst.2.2.2.2.1]
      · have hb_le0 : b ≤ 0 := by linarith [hb_lt, hsp.2.2.1]
        linarith [hst.2.2.2.2.2.2.2.2.2 b hgt hb_le0]
  have hd_gtM : xM_val u₀ t < d := by
    by_contra hle; push Not at hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [← heq] at hst; linarith [hst.2.2.2.2.1]
    · linarith [hst.2.2.2.2.2.2.2.2.1 d (by linarith [hb_in.1]) hlt]
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [le_max_right (-xstar_val y) (xM_val u₀ y - ε / 2), min_le_right (0 : ℝ) (xM_val u₀ y + ε / 2)]

lemma xLM_val_tendsto {u₀ y1 : ℝ} (hu₀ : 0 < u₀) (hy1_pos : 0 < y1) (hy1_lt : y1 < y0_val)
    (hM_y1 : M_val y1 = u₀) :
    Filter.Tendsto (xL_val u₀) (nhdsWithin y1 (Set.Iio y1)) (nhds (-xstar_val y1)) ∧
    Filter.Tendsto (xM_val u₀) (nhdsWithin y1 (Set.Iio y1)) (nhds (-xstar_val y1)) := by
  have hMu : ∀ {t}, 0 < t → t < y1 → u₀ < M_val t := fun {t} ht1 ht2 => by
    rw [← hM_y1]; exact M_val_strictAnti ⟨ht1, lt_trans ht2 hy1_lt⟩ ⟨hy1_pos, hy1_lt⟩ ht2
  have hM_y1' : phiU (-xstar_val y1) y1 = u₀ := hM_y1
  have hs1 := xstar_val_spec hy1_pos hy1_lt
  have hboth : ∀ ε > 0, ∀ᶠ t in nhdsWithin y1 (Set.Iio y1),
      |xL_val u₀ t - (-xstar_val y1)| < ε ∧ |xM_val u₀ t - (-xstar_val y1)| < ε := by
    intro ε hε
    set a := -xstar_val y1 - ε / 2 with ha_def
    set d := min 0 (-xstar_val y1 + ε / 2)
    have ha_lt : a < -xstar_val y1 := by linarith [ha_def]
    have hd_gt : -xstar_val y1 < d := lt_min (by linarith [hs1.1]) (by linarith)
    have hd_le0 : d ≤ 0 := min_le_left _ _
    have hFa : phiU a y1 < u₀ := by
      rw [← hM_y1']; exact hs1.2.2.2.2.2.2.1 ha_lt.le (Set.mem_Iic.mpr le_rfl) ha_lt
    have hFd : phiU d y1 < u₀ := by
      rw [← hM_y1']
      exact hs1.2.2.2.2.2.2.2.1 ⟨le_rfl, by linarith [hs1.1]⟩ ⟨hd_gt.le, by linarith [hs1.1]⟩ hd_gt
    have hev1 : ∀ᶠ t in nhdsWithin y1 (Set.Iio y1), phiU a t < u₀ :=
      nhdsWithin_le_nhds ((phiU_continuousAt_y a hy1_pos).eventually (Iio_mem_nhds hFa))
    have hev2 : ∀ᶠ t in nhdsWithin y1 (Set.Iio y1), phiU d t < u₀ :=
      nhdsWithin_le_nhds ((phiU_continuousAt_y d hy1_pos).eventually (Iio_mem_nhds hFd))
    have hev3 : ∀ᶠ t in nhdsWithin y1 (Set.Iio y1), t ∈ Set.Ioo 0 y1 :=
      Ioo_mem_nhdsLT hy1_pos
    refine ((hev1.and hev2).and hev3).mono fun t ⟨⟨hFat, hFdt⟩, ⟨ht1, ht2⟩⟩ => ?_
    have hst := xLM_val_spec hu₀ ht1 (lt_trans ht2 hy1_lt) (hMu ht1 ht2)
    have hmid_gt : u₀ < phiU (-xstar_val y1) t := by
      rw [← hM_y1']
      exact phiU_strictAnti_y_of_neg (by linarith [hs1.1]) ht1 hy1_pos ht2
    have hmid_in : xL_val u₀ t < -xstar_val y1 ∧ -xstar_val y1 < xM_val u₀ t := by
      constructor
      · by_contra hle; push Not at hle
        rcases eq_or_lt_of_le hle with heq | hlt
        · rw [← heq] at hst; linarith [hst.2.2.2.1]
        · linarith [hst.2.2.2.2.2.2.2.1 (-xstar_val y1) hlt]
      · by_contra hge; push Not at hge
        rcases eq_or_lt_of_le hge with heq | hgt
        · rw [heq] at hst; linarith [hst.2.2.2.2.1]
        · linarith [hst.2.2.2.2.2.2.2.2.2 (-xstar_val y1) hgt (by linarith [hs1.1])]
    have ha_ltL : a < xL_val u₀ t := by
      by_contra hge; push Not at hge
      rcases eq_or_lt_of_le hge with heq | hgt
      · rw [heq] at hst; linarith [hst.2.2.2.1]
      · linarith [hst.2.2.2.2.2.2.2.2.1 a hgt (lt_trans ha_lt hmid_in.2)]
    have hd_gtM : xM_val u₀ t < d := by
      by_contra hle; push Not at hle
      rcases eq_or_lt_of_le hle with heq | hlt
      · rw [← heq] at hst; linarith [hst.2.2.2.2.1]
      · linarith [hst.2.2.2.2.2.2.2.2.1 d (lt_trans hmid_in.1 hd_gt) hlt]
    have hd_le_r : d ≤ -xstar_val y1 + ε / 2 := min_le_right _ _
    exact ⟨abs_lt.mpr ⟨by linarith [ha_def], by linarith⟩, abs_lt.mpr ⟨by linarith [ha_def], by linarith⟩⟩
  constructor
  · rw [Metric.tendsto_nhds]; intro ε hε
    exact (hboth ε hε).mono fun t ht => by rw [Real.dist_eq]; exact ht.1
  · rw [Metric.tendsto_nhds]; intro ε hε
    exact (hboth ε hε).mono fun t ht => by rw [Real.dist_eq]; exact ht.2

lemma phi_preimage_encard_le_four_pos {u₀ : ℝ} (hu₀ : 0 < u₀) (w₀ : ℝ) :
    {p : ℝ × ℝ | 0 < p.2 ∧ phiU p.1 p.2 = u₀ ∧ phiV p.1 p.2 = w₀}.encard ≤ 4 := by
  set S := {p : ℝ × ℝ | 0 < p.2 ∧ phiU p.1 p.2 = u₀ ∧ phiV p.1 p.2 = w₀}
  set SR := {p ∈ S | 0 < p.1}
  have hSR : SR.encard ≤ 1 := by
    have hmono : StrictMonoOn (fun y => phiV (xR_val u₀ y) y) (Set.Ioi 0) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
      · exact fun y hy => (continuousAt_phiV_comp hy (xR_val_cont hu₀ hy)).continuousWithinAt
      · intro y hy; rw [interior_Ioi] at hy
        have ⟨_, _, hux, _, _⟩ := xR_val_spec hu₀ hy
        have heq : ∀ᶠ t in nhds y, phiU (xR_val u₀ t) t = u₀ :=
          Filter.eventually_of_mem (Ioi_mem_nhds hy) fun t ht => (xR_val_spec hu₀ ht).2.1
        have hd := implicit_phiV_deriv hy heq (xR_val_cont hu₀ hy) hux.ne'
        rw [hd.deriv]
        exact div_pos (det_pos_of_uX_nonneg hy hux.le (Or.inr hux)) hux
    have hgr : SR.encard ≤ {y ∈ Set.Ioi 0 | phiV (xR_val u₀ y) y = w₀}.encard := by
      refine encard_graph_le (g := xR_val u₀) fun p ⟨⟨hy, hU, hV⟩, hxp⟩ => ?_
      have ⟨_, _, _, hlt_u, hgt_u⟩ := xR_val_spec hu₀ hy
      have hx_eq : p.1 = xR_val u₀ p.2 := by
        rcases lt_trichotomy p.1 (xR_val u₀ p.2) with h | h | h
        · linarith [hlt_u p.1 hxp.le h]
        · exact h
        · linarith [hgt_u p.1 h]
      exact ⟨⟨hy, by rwa [← hx_eq]⟩, hx_eq⟩
    exact le_trans hgr (encard_le_one_of_strictMonoOn hmono w₀)
  -- Analyze the fold set S_M = {y ∈ (0, y₀) | u₀ < M_val y}
  set SM_set := {y ∈ Set.Ioo 0 y0_val | u₀ < M_val y}
  by_cases hSM_ne : SM_set.Nonempty
  · have hSM_bdd : BddAbove SM_set := ⟨y0_val, fun y hy => hy.1.2.le⟩
    set y1 := sSup SM_set
    have hy1_pos : 0 < y1 := by
      obtain ⟨y0', hy0'⟩ := hSM_ne
      exact lt_of_lt_of_le hy0'.1.1 (le_csSup hSM_bdd hy0')
    have hy1_lt : y1 < y0_val := by
      have hy0p : 0 < y0_val := by linarith [y0_val_spec.1]
      have hsm0 := (horizontal_slice_ge_y0 hy0p y0_val_spec.2.2.1.ge).2
      have hlt0 : ∀ x ∈ Set.Icc (-1 : ℝ) 0, phiU x y0_val < u₀ := fun x hx => by
        have hle0 : phiU x y0_val ≤ 0 := by
          rw [← phiU_zero y0_val]; exact hsm0.monotone hx.2
        linarith
      obtain ⟨y', hy'0, hy'lt, hy'prop⟩ := exists_y_lt_of_forall_Icc_lt hy0p hlt0
      have hle_y' : y1 ≤ y' := csSup_le hSM_ne fun y hy => by
        by_contra hgt; push Not at hgt
        have hxs := xstar_val_spec hy.1.1 hy.1.2
        have hMlt : M_val y < u₀ :=
          hy'prop y ⟨hgt.le, hy.1.2.le⟩ (-xstar_val y) ⟨by linarith [hxs.2.1], by linarith [hxs.1]⟩
        linarith [hy.2]
      exact lt_of_le_of_lt hle_y' hy'lt
    have hM_y1 : M_val y1 = u₀ := by
      apply le_antisymm
      · by_contra hgt; push Not at hgt
        have hcont : ContinuousAt (fun t => phiU (-xstar_val y1) t) y1 :=
          phiU_continuousAt_y (-xstar_val y1) hy1_pos
        obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually (Ioi_mem_nhds hgt))
        set y2 := min ((y1 + y0_val) / 2) (y1 + δ / 2)
        have hy2_gt : y1 < y2 := lt_min (by linarith) (by linarith)
        have hy2_lt : y2 < y0_val := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hdist : dist y2 y1 < δ := by
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          linarith [min_le_right ((y1 + y0_val) / 2) (y1 + δ / 2)]
        have hphi2 : u₀ < phiU (-xstar_val y1) y2 := hball hdist
        have hM2 : u₀ < M_val y2 :=
          lt_of_lt_of_le hphi2 (phiU_le_M_val (lt_trans hy1_pos hy2_gt) hy2_lt (by linarith [(xstar_val_spec hy1_pos hy1_lt).1]))
        have hle : y2 ≤ y1 := le_csSup hSM_bdd ⟨⟨lt_trans hy1_pos hy2_gt, hy2_lt⟩, hM2⟩
        linarith
      · by_contra hlt; push Not at hlt
        have hlt1 : ∀ x ∈ Set.Icc (-1 : ℝ) 0, phiU x y1 < u₀ := fun x hx =>
          lt_of_le_of_lt (phiU_le_M_val hy1_pos hy1_lt hx.2) hlt
        obtain ⟨y', hy'0, hy'lt, hy'prop⟩ := exists_y_lt_of_forall_Icc_lt hy1_pos hlt1
        have hle_y' : y1 ≤ y' := csSup_le hSM_ne fun y hy => by
          by_contra hgt; push Not at hgt
          have hyl1 : y ≤ y1 := le_csSup hSM_bdd hy
          have hxs := xstar_val_spec hy.1.1 hy.1.2
          have hMlt : M_val y < u₀ :=
            hy'prop y ⟨hgt.le, hyl1⟩ (-xstar_val y) ⟨by linarith [hxs.2.1], by linarith [hxs.1]⟩
          linarith [hy.2]
        linarith
    have hMu_lt : ∀ {t}, 0 < t → t < y1 → u₀ < M_val t := fun {t} ht1 ht2 => by
      rw [← hM_y1]; exact M_val_strictAnti ⟨ht1, lt_trans ht2 hy1_lt⟩ ⟨hy1_pos, hy1_lt⟩ ht2
    have hxLM_tendsto := xLM_val_tendsto hu₀ hy1_pos hy1_lt hM_y1
    set V1 := phiV (-xstar_val y1) y1
    have hvL_tend : Filter.Tendsto (fun t => phiV (xL_val u₀ t) t) (nhdsWithin y1 (Set.Iio y1)) (nhds V1) :=
      tendsto_phiV_comp hy1_pos hxLM_tendsto.1 (Filter.tendsto_id.mono_left nhdsWithin_le_nhds)
    have hvM_tend : Filter.Tendsto (fun t => phiV (xM_val u₀ t) t) (nhdsWithin y1 (Set.Iio y1)) (nhds V1) :=
      tendsto_phiV_comp hy1_pos hxLM_tendsto.2 (Filter.tendsto_id.mono_left nhdsWithin_le_nhds)
    -- Left branch: strictly increasing on (0, y1), strictly below V1
    have hvL_mono : StrictMonoOn (fun y => phiV (xL_val u₀ y) y) (Set.Ioo 0 y1) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioo 0 y1)
      · exact fun y hy =>
          (continuousAt_phiV_comp hy.1 (xL_val_cont hu₀ hy1_pos hy1_lt hM_y1 hy.1 hy.2)).continuousWithinAt
      · intro y hy; rw [interior_Ioo] at hy
        have hst := xLM_val_spec hu₀ hy.1 (lt_trans hy.2 hy1_lt) (hMu_lt hy.1 hy.2)
        have heq : ∀ᶠ t in nhds y, phiU (xL_val u₀ t) t = u₀ :=
          Filter.eventually_of_mem (Ioo_mem_nhds hy.1 hy.2) fun t ht =>
            (xLM_val_spec hu₀ ht.1 (lt_trans ht.2 hy1_lt) (hMu_lt ht.1 ht.2)).2.2.2.1
        have hd := implicit_phiV_deriv hy.1 heq (xL_val_cont hu₀ hy1_pos hy1_lt hM_y1 hy.1 hy.2) hst.2.2.2.2.2.1.ne'
        rw [hd.deriv]
        exact div_pos (det_pos_of_uX_nonneg hy.1 hst.2.2.2.2.2.1.le (Or.inr hst.2.2.2.2.2.1)) hst.2.2.2.2.2.1
    have hvL_lt_V1 : ∀ y, 0 < y → y < y1 → phiV (xL_val u₀ y) y < V1 := by
      intro y hy1 hy2
      set ym := (y + y1) / 2 with hym_def
      have h1 : phiV (xL_val u₀ y) y < phiV (xL_val u₀ ym) ym :=
        hvL_mono ⟨hy1, hy2⟩ ⟨by linarith [hym_def], by linarith [hym_def]⟩ (by linarith [hym_def])
      have h2 : phiV (xL_val u₀ ym) ym ≤ V1 := by
        have : (nhdsWithin y1 (Set.Iio y1)).NeBot := nhdsLT_neBot y1
        apply ge_of_tendsto hvL_tend
        exact Filter.eventually_of_mem (Ioo_mem_nhdsLT (by linarith [hym_def] : ym < y1)) fun t ht =>
          (hvL_mono ⟨by linarith [hym_def], by linarith [hym_def]⟩ ⟨by linarith [ht.1, hym_def], ht.2⟩ ht.1).le
      linarith
    -- Middle branch: partition by Z = {y ∈ (0, y1) | det(xM y, y) ≤ 0}
    set Z := {y ∈ Set.Ioo 0 y1 |
      uX_xy (xM_val u₀ y) y * vY_xy (xM_val u₀ y) y - uY_xy (xM_val u₀ y) y * vX_xy (xM_val u₀ y) y ≤ 0}
    have hvM_deriv : ∀ {y}, 0 < y → y < y1 →
        HasDerivAt (fun t => phiV (xM_val u₀ t) t)
          ((uX_xy (xM_val u₀ y) y * vY_xy (xM_val u₀ y) y - uY_xy (xM_val u₀ y) y * vX_xy (xM_val u₀ y) y) /
            uX_xy (xM_val u₀ y) y) y := by
      intro y hy1 hy2
      have hst := xLM_val_spec hu₀ hy1 (lt_trans hy2 hy1_lt) (hMu_lt hy1 hy2)
      have heq : ∀ᶠ t in nhds y, phiU (xM_val u₀ t) t = u₀ :=
        Filter.eventually_of_mem (Ioo_mem_nhds hy1 hy2) fun t ht =>
          (xLM_val_spec hu₀ ht.1 (lt_trans ht.2 hy1_lt) (hMu_lt ht.1 ht.2)).2.2.2.2.1
      exact implicit_phiV_deriv hy1 heq (xM_val_cont hu₀ hy1_pos hy1_lt hM_y1 hy1 hy2) hst.2.2.2.2.2.2.1.ne
    -- Every point p ∈ S with p.1 ≤ 0 must have p.2 ≤ y1
    have hnonpos_cases : ∀ p ∈ S, p.1 ≤ 0 →
        (p.2 < y1 ∧ (p.1 = xL_val u₀ p.2 ∨ p.1 = xM_val u₀ p.2)) ∨ p = (-xstar_val y1, y1) := by
      intro p ⟨hy, hU, _⟩ hxle
      have hylt0 : p.2 < y0_val := by
        by_contra hge; push Not at hge
        have hux0 : 0 ≤ uX_xy 0 p.2 := by
          rcases eq_or_lt_of_le hge with heq | hgt
          · rw [← heq]; exact y0_val_spec.2.2.1.ge
          · exact (y0_val_spec.2.2.2.2 p.2 hgt).le
        have hsm := (horizontal_slice_ge_y0 hy hux0).2
        have hle0 : phiU p.1 p.2 ≤ 0 := by rw [← phiU_zero p.2]; exact hsm.monotone hxle
        linarith
      rcases lt_trichotomy p.2 y1 with hlt | heq | hgt
      · left; refine ⟨hlt, ?_⟩
        have hst := xLM_val_spec hu₀ hy (lt_trans hlt hy1_lt) (hMu_lt hy hlt)
        rcases lt_trichotomy p.1 (xL_val u₀ p.2) with h1 | h1 | h1
        · linarith [hst.2.2.2.2.2.2.2.1 p.1 h1]
        · exact Or.inl h1
        · rcases lt_trichotomy p.1 (xM_val u₀ p.2) with h2 | h2 | h2
          · linarith [hst.2.2.2.2.2.2.2.2.1 p.1 h1 h2]
          · exact Or.inr h2
          · linarith [hst.2.2.2.2.2.2.2.2.2 p.1 h2 hxle]
      · right
        have hs1 := xstar_val_spec hy1_pos hy1_lt
        have hx_eq : p.1 = -xstar_val y1 := by
          rw [heq] at hU
          rcases lt_trichotomy p.1 (-xstar_val y1) with h1 | h1 | h1
          · have := hs1.2.2.2.2.2.2.1 h1.le (Set.mem_Iic.mpr le_rfl) h1
            change phiU p.1 y1 < M_val y1 at this; linarith
          · exact h1
          · have := hs1.2.2.2.2.2.2.2.1 ⟨le_rfl, by linarith [hs1.1]⟩ ⟨h1.le, by linarith [hs1.1]⟩ h1
            change phiU p.1 y1 < M_val y1 at this; linarith
        exact Prod.ext hx_eq heq
      · have hMlt : M_val p.2 < u₀ := by
          rw [← hM_y1]; exact M_val_strictAnti ⟨hy1_pos, hy1_lt⟩ ⟨hy, hylt0⟩ hgt
        linarith [phiU_le_M_val hy hylt0 hxle]
    set SL := {p ∈ S | p.2 < y1 ∧ p.1 = xL_val u₀ p.2}
    set SF : Set (ℝ × ℝ) := {(-xstar_val y1, y1)}
    have hSL : SL.encard ≤ 1 := by
      have hgr : SL.encard ≤ {y ∈ Set.Ioo 0 y1 | phiV (xL_val u₀ y) y = w₀}.encard :=
        encard_graph_le (g := xL_val u₀) fun p ⟨⟨hy, _, hV⟩, hlt, hx⟩ => ⟨⟨⟨hy, hlt⟩, by rwa [← hx]⟩, hx⟩
      exact le_trans hgr (encard_le_one_of_strictMonoOn hvL_mono w₀)
    have hSF : SF.encard ≤ 1 := by rw [Set.encard_singleton]
    by_cases hZ_ne : Z.Nonempty
    · have hZ_bdd_below : BddBelow Z := ⟨0, fun y hy => hy.1.1.le⟩
      have hZ_bdd_above : BddAbove Z := ⟨y1, fun y hy => hy.1.2.le⟩
      set y_in := sInf Z
      set y_out := sSup Z
      set SM1 := {p ∈ S | p.2 < y1 ∧ p.2 ≤ y_in ∧ p.1 = xM_val u₀ p.2}
      set SM2 := {p ∈ S | p.2 < y1 ∧ y_in ≤ p.2 ∧ p.2 ≤ y_out ∧ p.1 = xM_val u₀ p.2}
      set SM3 := {p ∈ S | y_out < p.2 ∧ p.2 < y1 ∧ p.1 = xM_val u₀ p.2}
      have hvM_anti1 : StrictAntiOn (fun y => phiV (xM_val u₀ y) y) (Set.Ioo 0 y1 ∩ Set.Iic y_in) := by
        apply strictAntiOn_of_deriv_neg ((convex_Ioo 0 y1).inter (convex_Iic y_in))
        · exact fun y hy =>
            (continuousAt_phiV_comp hy.1.1 (xM_val_cont hu₀ hy1_pos hy1_lt hM_y1 hy.1.1 hy.1.2)).continuousWithinAt
        · intro y hy
          rw [interior_inter, interior_Ioo, interior_Iic] at hy
          rw [(hvM_deriv hy.1.1 hy.1.2).deriv]
          have hnotZ : y ∉ Z := fun hmem => not_lt.mpr (csInf_le hZ_bdd_below hmem) hy.2
          have hdet : 0 < uX_xy (xM_val u₀ y) y * vY_xy (xM_val u₀ y) y - uY_xy (xM_val u₀ y) y * vX_xy (xM_val u₀ y) y := by
            by_contra hle; push Not at hle; exact hnotZ ⟨hy.1, hle⟩
          exact div_neg_of_pos_of_neg hdet (xLM_val_spec hu₀ hy.1.1 (lt_trans hy.1.2 hy1_lt) (hMu_lt hy.1.1 hy.1.2)).2.2.2.2.2.2.1
      have hvM_mono2 : StrictMonoOn (fun y => phiV (xM_val u₀ y) y) (Set.Ioo 0 y1 ∩ Set.Icc y_in y_out) := by
        apply strictMonoOn_of_deriv_pos ((convex_Ioo 0 y1).inter (convex_Icc y_in y_out))
        · exact fun y hy =>
            (continuousAt_phiV_comp hy.1.1 (xM_val_cont hu₀ hy1_pos hy1_lt hM_y1 hy.1.1 hy.1.2)).continuousWithinAt
        · intro y hy
          rw [interior_inter, interior_Ioo, interior_Icc] at hy
          rw [(hvM_deriv hy.1.1 hy.1.2).deriv]
          obtain ⟨z1, hz1Z, hz1lt⟩ := (csInf_lt_iff hZ_bdd_below hZ_ne).mp hy.2.1
          obtain ⟨z3, hz3Z, hz3gt⟩ := (lt_csSup_iff hZ_bdd_above hZ_ne).mp hy.2.2
          have hs1 := xLM_val_spec hu₀ hz1Z.1.1 (lt_trans hz1Z.1.2 hy1_lt) (hMu_lt hz1Z.1.1 hz1Z.1.2)
          have hs2 := xLM_val_spec hu₀ hy.1.1 (lt_trans hy.1.2 hy1_lt) (hMu_lt hy.1.1 hy.1.2)
          have hs3 := xLM_val_spec hu₀ hz3Z.1.1 (lt_trans hz3Z.1.2 hy1_lt) (hMu_lt hz3Z.1.1 hz3Z.1.2)
          have hdet : uX_xy (xM_val u₀ y) y * vY_xy (xM_val u₀ y) y - uY_xy (xM_val u₀ y) y * vX_xy (xM_val u₀ y) y < 0 :=
            det_neg_between_of_phiU_eq hu₀ hz1Z.1.1 hz1lt hz3gt (lt_trans hz3Z.1.2 hy1_lt)
              hs1.2.2.1.le hs2.2.2.1.le hs3.2.2.1.le
              hs1.2.2.2.2.2.2.1 hs2.2.2.2.2.2.2.1 hs3.2.2.2.2.2.2.1
              hs1.2.2.2.2.1 hs2.2.2.2.2.1 hs3.2.2.2.2.1 hz1Z.2 hz3Z.2
          exact div_pos_of_neg_of_neg hdet hs2.2.2.2.2.2.2.1
      have hvM_anti3 : StrictAntiOn (fun y => phiV (xM_val u₀ y) y) (Set.Ioo y_out y1) := by
        apply strictAntiOn_of_deriv_neg (convex_Ioo y_out y1)
        · intro y hy
          have hy0 : 0 < y := lt_of_le_of_lt (le_trans hZ_ne.some_mem.1.1.le (le_csSup hZ_bdd_above hZ_ne.some_mem)) hy.1
          exact (continuousAt_phiV_comp hy0 (xM_val_cont hu₀ hy1_pos hy1_lt hM_y1 hy0 hy.2)).continuousWithinAt
        · intro y hy; rw [interior_Ioo] at hy
          have hy0 : 0 < y := lt_of_le_of_lt (le_trans hZ_ne.some_mem.1.1.le (le_csSup hZ_bdd_above hZ_ne.some_mem)) hy.1
          rw [(hvM_deriv hy0 hy.2).deriv]
          have hnotZ : y ∉ Z := fun hmem => not_lt.mpr (le_csSup hZ_bdd_above hmem) hy.1
          have hdet : 0 < uX_xy (xM_val u₀ y) y * vY_xy (xM_val u₀ y) y - uY_xy (xM_val u₀ y) y * vX_xy (xM_val u₀ y) y := by
            by_contra hle; push Not at hle; exact hnotZ ⟨⟨hy0, hy.2⟩, hle⟩
          exact div_neg_of_pos_of_neg hdet (xLM_val_spec hu₀ hy0 (lt_trans hy.2 hy1_lt) (hMu_lt hy0 hy.2)).2.2.2.2.2.2.1
      have hvM3_gt_V1 : ∀ y, y_out < y → y < y1 → V1 < phiV (xM_val u₀ y) y := by
        intro y hy1 hy2
        set ym := (y + y1) / 2 with hym_def
        have h1 : phiV (xM_val u₀ ym) ym < phiV (xM_val u₀ y) y :=
          hvM_anti3 ⟨hy1, hy2⟩ ⟨by linarith [hym_def], by linarith [hym_def]⟩ (by linarith [hym_def])
        have h2 : V1 ≤ phiV (xM_val u₀ ym) ym := by
          have : (nhdsWithin y1 (Set.Iio y1)).NeBot := nhdsLT_neBot y1
          apply le_of_tendsto hvM_tend
          exact Filter.eventually_of_mem (Ioo_mem_nhdsLT (by linarith [hym_def] : ym < y1)) fun t ht =>
            (hvM_anti3 ⟨by linarith [hym_def], by linarith [hym_def]⟩ ⟨by linarith [ht.1, hym_def], ht.2⟩ ht.1).le
        linarith
      have hSM1 : SM1.encard ≤ 1 := by
        have hgr : SM1.encard ≤ {y ∈ Set.Ioo 0 y1 ∩ Set.Iic y_in | phiV (xM_val u₀ y) y = w₀}.encard :=
          encard_graph_le (g := xM_val u₀) fun p ⟨⟨hy, _, hV⟩, hlt, hle, hx⟩ => ⟨⟨⟨⟨hy, hlt⟩, hle⟩, by rwa [← hx]⟩, hx⟩
        exact le_trans hgr (encard_le_one_of_strictAntiOn hvM_anti1 w₀)
      have hSM2 : SM2.encard ≤ 1 := by
        have hgr : SM2.encard ≤ {y ∈ Set.Ioo 0 y1 ∩ Set.Icc y_in y_out | phiV (xM_val u₀ y) y = w₀}.encard :=
          encard_graph_le (g := xM_val u₀) fun p ⟨⟨hy, _, hV⟩, hlt, h1, h2, hx⟩ => ⟨⟨⟨⟨hy, hlt⟩, h1, h2⟩, by rwa [← hx]⟩, hx⟩
        exact le_trans hgr (encard_le_one_of_strictMonoOn hvM_mono2 w₀)
      have hSM3 : SM3.encard ≤ 1 := by
        have hgr : SM3.encard ≤ {y ∈ Set.Ioo y_out y1 | phiV (xM_val u₀ y) y = w₀}.encard :=
          encard_graph_le (g := xM_val u₀) fun p ⟨⟨_, _, hV⟩, h1, h2, hx⟩ => ⟨⟨⟨h1, h2⟩, by rwa [← hx]⟩, hx⟩
        exact le_trans hgr (encard_le_one_of_strictAntiOn hvM_anti3 w₀)
      rcases lt_trichotomy w₀ V1 with hwlt | rfl | hwgt
      · have hcov : S ⊆ SR ∪ SL ∪ SM1 ∪ SM2 := by
          intro p hp
          by_cases hxp : 0 < p.1
          · exact Or.inl (Or.inl (Or.inl ⟨hp, hxp⟩))
          push Not at hxp
          rcases hnonpos_cases p hp hxp with ⟨hlt, hxL | hxM⟩ | rfl
          · exact Or.inl (Or.inl (Or.inr ⟨hp, hlt, hxL⟩))
          · by_cases h1 : p.2 ≤ y_in
            · exact Or.inl (Or.inr ⟨hp, hlt, h1, hxM⟩)
            · by_cases h2 : p.2 ≤ y_out
              · exact Or.inr ⟨hp, hlt, le_of_not_ge h1, h2, hxM⟩
              · exfalso; have := hvM3_gt_V1 p.2 (lt_of_not_ge h2) hlt; rw [← hxM, hp.2.2] at this; linarith
          · exfalso; dsimp only [V1] at hwlt; linarith [hp.2.2]
        exact le_trans (Set.encard_le_encard hcov) (encard_union4_le_four hSR hSL hSM1 hSM2)
      · have hcov : S ⊆ SR ∪ SM1 ∪ SM2 ∪ SF := by
          intro p hp
          by_cases hxp : 0 < p.1
          · exact Or.inl (Or.inl (Or.inl ⟨hp, hxp⟩))
          push Not at hxp
          rcases hnonpos_cases p hp hxp with ⟨hlt, hxL | hxM⟩ | hfold
          · exfalso; have := hvL_lt_V1 p.2 hp.1 hlt; rw [← hxL, hp.2.2] at this; linarith
          · by_cases h1 : p.2 ≤ y_in
            · exact Or.inl (Or.inl (Or.inr ⟨hp, hlt, h1, hxM⟩))
            · by_cases h2 : p.2 ≤ y_out
              · exact Or.inl (Or.inr ⟨hp, hlt, le_of_not_ge h1, h2, hxM⟩)
              · exfalso; have := hvM3_gt_V1 p.2 (lt_of_not_ge h2) hlt; rw [← hxM, hp.2.2] at this; linarith
          · exact Or.inr hfold
        exact le_trans (Set.encard_le_encard hcov) (encard_union4_le_four hSR hSM1 hSM2 hSF)
      · have hcov : S ⊆ SR ∪ SM1 ∪ SM2 ∪ SM3 := by
          intro p hp
          by_cases hxp : 0 < p.1
          · exact Or.inl (Or.inl (Or.inl ⟨hp, hxp⟩))
          push Not at hxp
          rcases hnonpos_cases p hp hxp with ⟨hlt, hxL | hxM⟩ | rfl
          · exfalso; have := hvL_lt_V1 p.2 hp.1 hlt; rw [← hxL, hp.2.2] at this; linarith
          · by_cases h1 : p.2 ≤ y_in
            · exact Or.inl (Or.inl (Or.inr ⟨hp, hlt, h1, hxM⟩))
            · by_cases h2 : p.2 ≤ y_out
              · exact Or.inl (Or.inr ⟨hp, hlt, le_of_not_ge h1, h2, hxM⟩)
              · exact Or.inr ⟨hp, lt_of_not_ge h2, hlt, hxM⟩
          · exfalso; dsimp only [V1] at hwgt; linarith [hp.2.2]
        exact le_trans (Set.encard_le_encard hcov) (encard_union4_le_four hSR hSM1 hSM2 hSM3)
    · -- Z is empty: vM is strictly decreasing on ALL of (0, y1)
      have hvM_anti : StrictAntiOn (fun y => phiV (xM_val u₀ y) y) (Set.Ioo 0 y1) := by
        apply strictAntiOn_of_deriv_neg (convex_Ioo 0 y1)
        · exact fun y hy =>
            (continuousAt_phiV_comp hy.1 (xM_val_cont hu₀ hy1_pos hy1_lt hM_y1 hy.1 hy.2)).continuousWithinAt
        · intro y hy; rw [interior_Ioo] at hy
          rw [(hvM_deriv hy.1 hy.2).deriv]
          have hdet : 0 < uX_xy (xM_val u₀ y) y * vY_xy (xM_val u₀ y) y - uY_xy (xM_val u₀ y) y * vX_xy (xM_val u₀ y) y := by
            by_contra hle; push Not at hle; exact hZ_ne ⟨y, hy, hle⟩
          exact div_neg_of_pos_of_neg hdet (xLM_val_spec hu₀ hy.1 (lt_trans hy.2 hy1_lt) (hMu_lt hy.1 hy.2)).2.2.2.2.2.2.1
      set SMall := {p ∈ S | p.2 < y1 ∧ p.1 = xM_val u₀ p.2}
      have hSMall : SMall.encard ≤ 1 := by
        have hgr : SMall.encard ≤ {y ∈ Set.Ioo 0 y1 | phiV (xM_val u₀ y) y = w₀}.encard :=
          encard_graph_le (g := xM_val u₀) fun p ⟨⟨hy, _, hV⟩, hlt, hx⟩ => ⟨⟨⟨hy, hlt⟩, by rwa [← hx]⟩, hx⟩
        exact le_trans hgr (encard_le_one_of_strictAntiOn hvM_anti w₀)
      have hcov : S ⊆ SR ∪ SL ∪ SMall ∪ SF := by
        intro p hp
        by_cases hxp : 0 < p.1
        · exact Or.inl (Or.inl (Or.inl ⟨hp, hxp⟩))
        push Not at hxp
        rcases hnonpos_cases p hp hxp with ⟨hlt, hxL | hxM⟩ | hfold
        · exact Or.inl (Or.inl (Or.inr ⟨hp, hlt, hxL⟩))
        · exact Or.inl (Or.inr ⟨hp, hlt, hxM⟩)
        · exact Or.inr hfold
      exact le_trans (Set.encard_le_encard hcov) (encard_union4_le_four hSR hSL hSMall hSF)
  · -- SM_set is empty: every solution has x > 0, so S ⊆ SR
    have hcov : S ⊆ SR := by
      intro p hp
      refine ⟨hp, ?_⟩
      by_contra hle; push Not at hle
      by_cases hlt : p.2 < y0_val
      · have hM_lt : M_val p.2 < u₀ := by
          by_contra hge; push Not at hge
          have hhalf : u₀ < M_val (p.2 / 2) :=
            lt_of_le_of_lt hge (M_val_strictAnti ⟨by linarith [hp.1], by linarith [hp.1, hlt]⟩ ⟨hp.1, hlt⟩ (by linarith [hp.1]))
          exact hSM_ne ⟨p.2 / 2, ⟨by linarith [hp.1], by linarith [hp.1, hlt]⟩, hhalf⟩
        linarith [phiU_le_M_val hp.1 hlt hle, hp.2.1]
      · push Not at hlt
        have hux0 : 0 ≤ uX_xy 0 p.2 := by
          rcases eq_or_lt_of_le hlt with heq | hgt
          · rw [← heq]; exact y0_val_spec.2.2.1.ge
          · exact (y0_val_spec.2.2.2.2 p.2 hgt).le
        have hsm := (horizontal_slice_ge_y0 hp.1 hux0).2
        have hle0 : phiU p.1 p.2 ≤ 0 := by rw [← phiU_zero p.2]; exact hsm.monotone hle
        linarith [hp.2.1]
    calc S.encard ≤ SR.encard := Set.encard_le_encard hcov
      _ ≤ 1 := hSR
      _ ≤ 4 := by norm_num

lemma phi_preimage_encard_le_four {u₀ : ℝ} (hu₀ : 0 ≤ u₀) (w₀ : ℝ) :
    {p : ℝ × ℝ | 0 < p.2 ∧ phiU p.1 p.2 = u₀ ∧ phiV p.1 p.2 = w₀}.encard ≤ 4 := by
  rcases eq_or_lt_of_le hu₀ with rfl | hpos
  · exact phi_preimage_encard_le_four_zero w₀
  · exact phi_preimage_encard_le_four_pos hpos w₀

end MaxwellH1

theorem OMA.solution : OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1.H1 := by
  intro q u w hw hq0 hqeq _
  obtain ⟨u₀, w₀, hu₀, _, hle⟩ := MaxwellH1.encard_le_phi_preimage q u w hw hq0 hqeq
  exact le_trans hle (MaxwellH1.phi_preimage_encard_le_four hu₀ w₀)
