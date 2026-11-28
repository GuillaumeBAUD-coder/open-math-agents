import OMAStatements.S_mo_499635
import Mathlib

/-!
# Proof of MathOverflow 499635

We prove that for nondegenerate planar triangles `ABC` and `ABC'` with `C' ≠ C`, their Gaussian
centers of mass differ: `center A B C' ≠ center A B C`.

## Architecture
1. **Joint convexity of `G(w, c) = I₁(1/w)/I₂(1/w)` on `(0, ∞) × ℝ`:**
   Via Gaussian integration by parts in `L = 1/w`, the Hessian entries `G_ww`, `G_wc`, `G_cc`
   and determinant `G_ww G_cc - G_wc^2` are expressed in terms of 4 positive functions
   `(t, y, u, g)` satisfying a closed polynomial ODE system in `D_L = L d/dL`. Two exact
   algebraic sum-of-squares identities on the zero loci `W₁ = 0` and `t D₁ = 0`, paired with
   elementary `L → 0+` Taylor expansions, show `G_ww > 0` and `G_ww G_cc - G_wc^2 > 0` everywhere.
2. **Strictly nested case (`C ∈ int(ΔABC')`):**
   The perspective function `H(t, w, c) = t G(w/t, c/t)` is 1-homogeneous, subadditive, and
   strictly increasing in `t` and `w`. Thus the ray-centroid gauge
   `p(v) = H(‖v‖, w(v), -⟪C, v⟫)` is strictly subadditive on linearly independent vectors,
   producing an explicit line `ℓ(x - C) = 1` that strictly separates `center(ΔABC)` from
   `center(ΔACC' ∪ ΔBCC')`, proved via the smooth `(s, λ) ∈ (0, 1)²` triangle parametrization.
3. **Non-nested and boundary cases:**
   Barycentric coordinates of `C` in `(A, B, C')` give an exact 4-way split into nested,
   reverse-nested, boundary (separated by edge `BC` or `AC`), and crossing (separated by the
   line through `P = (BC) ∩ (AC')` and the common center `M`).
-/

namespace OMA.Mo499635

open MeasureTheory Set Filter Topology Real
open scoped RealInnerProductSpace

noncomputable section

/-! ### Part 1: 1D Gaussian moments, ODE barriers, and joint convexity of `G(w, c)` -/

/-- Helper to rewrite the derivative value in `HasDerivAt` without creating typeclass goals. -/
lemma hasDerivAt_congr_val {f : ℝ → ℝ} {a b x : ℝ} (h : HasDerivAt f a x) (heq : a = b) :
    HasDerivAt f b x :=
  heq ▸ h

/-- The 1D Gaussian weight `φ(c, u) = exp (-(u - c)² / 2)`. -/
def phi (c u : ℝ) : ℝ := Real.exp (-(u - c) ^ 2 / 2)

/-- The `k`-th 1D Gaussian moment on `[0, L]`. -/
def Imom (k : ℕ) (c L : ℝ) : ℝ := ∫ u in (0 : ℝ)..L, u ^ k * phi c u

/-- The ratio `G(w, c) = I₁(1/w) / I₂(1/w)`. -/
def Gfun (w c : ℝ) : ℝ := Imom 1 c (1 / w) / Imom 2 c (1 / w)

/-- Rescaled moment `J_k(c, L) = ∫₀¹ s^k exp(c L s - L² s² / 2) ds`. -/
def Jmom (k : ℕ) (c L : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, s ^ k * Real.exp (c * L * s - L ^ 2 * s ^ 2 / 2)

lemma phi_pos (c u : ℝ) : 0 < phi c u := Real.exp_pos _

lemma continuous_phi (c : ℝ) : Continuous (phi c) := by
  unfold phi
  fun_prop

lemma hasDerivAt_phi (c u : ℝ) : HasDerivAt (phi c) (-(u - c) * phi c u) u := by
  unfold phi
  have h1 : HasDerivAt (fun x : ℝ => -(x - c) ^ 2 / 2) (-(u - c)) u := by
    have h0 : HasDerivAt (fun x : ℝ => x - c) 1 u := (hasDerivAt_id u).sub_const c
    exact hasDerivAt_congr_val (((h0.pow 2).neg).div_const 2) (by ring)
  exact hasDerivAt_congr_val h1.exp (by ring)

lemma Imom_pos (k : ℕ) (c : ℝ) {L : ℝ} (hL : 0 < L) : 0 < Imom k c L := by
  unfold Imom
  refine intervalIntegral.integral_pos hL ?_ ?_ ?_
  · exact ((continuous_pow k).mul (continuous_phi c)).continuousOn
  · intro u hu
    exact mul_nonneg (pow_nonneg (le_of_lt hu.1) k) (le_of_lt (phi_pos c u))
  · refine ⟨L / 2, ⟨by linarith, by linarith⟩, ?_⟩
    exact mul_pos (pow_pos (by linarith) k) (phi_pos c (L / 2))

lemma hasDerivAt_Imom_L (k : ℕ) (c L : ℝ) :
    HasDerivAt (fun x => Imom k c x) (L ^ k * phi c L) L := by
  unfold Imom
  have hc : Continuous (fun u : ℝ => u ^ k * phi c u) :=
    (continuous_pow k).mul (continuous_phi c)
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 L)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt

/-- Gaussian integration by parts: `I_{k+2} - c I_{k+1} = (k+1) I_k - L^{k+1} φ(c, L)`. -/
lemma Imom_ibp (k : ℕ) (c L : ℝ) :
    Imom (k + 2) c L - c * Imom (k + 1) c L =
      ((k : ℝ) + 1) * Imom k c L - L ^ (k + 1) * phi c L := by
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) L,
      HasDerivAt (fun x : ℝ => x ^ (k + 1) * phi c x)
        (((k : ℝ) + 1) * u ^ k * phi c u - (u ^ (k + 2) * phi c u - c * (u ^ (k + 1) * phi c u))) u := by
    intro u _
    have hp : HasDerivAt (fun x : ℝ => x ^ (k + 1)) (((k : ℝ) + 1) * u ^ k) u := by
      simpa [Nat.cast_add, Nat.cast_one] using hasDerivAt_pow (k + 1) u
    exact hasDerivAt_congr_val (hp.mul (hasDerivAt_phi c u)) (by ring)
  have hint : IntervalIntegrable
      (fun u : ℝ => ((k : ℝ) + 1) * u ^ k * phi c u -
        (u ^ (k + 2) * phi c u - c * (u ^ (k + 1) * phi c u))) volume 0 L := by
    have hc : Continuous (fun u : ℝ => ((k : ℝ) + 1) * u ^ k * phi c u -
        (u ^ (k + 2) * phi c u - c * (u ^ (k + 1) * phi c u))) := by
      have hphi := continuous_phi c
      fun_prop
    exact hc.intervalIntegrable 0 L
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have h0 : (0 : ℝ) ^ (k + 1) * phi c 0 = 0 := by simp
  rw [h0, sub_zero] at hftc
  have hi0 : IntervalIntegrable (fun u : ℝ => u ^ k * phi c u) volume 0 L :=
    ((continuous_pow k).mul (continuous_phi c)).intervalIntegrable 0 L
  have hi1 : IntervalIntegrable (fun u : ℝ => u ^ (k + 1) * phi c u) volume 0 L :=
    ((continuous_pow (k + 1)).mul (continuous_phi c)).intervalIntegrable 0 L
  have hi2 : IntervalIntegrable (fun u : ℝ => u ^ (k + 2) * phi c u) volume 0 L :=
    ((continuous_pow (k + 2)).mul (continuous_phi c)).intervalIntegrable 0 L
  have hsplit :
      (∫ u in (0 : ℝ)..L, ((k : ℝ) + 1) * u ^ k * phi c u -
        (u ^ (k + 2) * phi c u - c * (u ^ (k + 1) * phi c u))) =
      ((k : ℝ) + 1) * Imom k c L - (Imom (k + 2) c L - c * Imom (k + 1) c L) := by
    have hA : (fun u : ℝ => ((k : ℝ) + 1) * u ^ k * phi c u) =
        fun u => ((k : ℝ) + 1) * (u ^ k * phi c u) := by ext u; ring
    rw [intervalIntegral.integral_sub (by rw [hA]; exact hi0.const_mul _)
        (hi2.sub (hi1.const_mul _)),
      hA, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hi2 (hi1.const_mul _),
      intervalIntegral.integral_const_mul]
    rfl
  linarith

/-- Strict Cauchy-Schwarz on `(0, L)`: `I₂² < I₁ I₃`. -/
lemma Imom2_sq_lt_Imom1_mul_Imom3 (c : ℝ) {L : ℝ} (hL : 0 < L) :
    Imom 2 c L ^ 2 < Imom 1 c L * Imom 3 c L := by
  set a := Imom 2 c L
  set b := Imom 1 c L
  have hb : 0 < b := Imom_pos 1 c hL
  have hpos : 0 < ∫ u in (0 : ℝ)..L, u * (a - u * b) ^ 2 * phi c u := by
    refine intervalIntegral.integral_pos hL ?_ ?_ ?_
    · have hphi := continuous_phi c
      fun_prop
    · intro u hu
      exact mul_nonneg (mul_nonneg (le_of_lt hu.1) (sq_nonneg _)) (le_of_lt (phi_pos c u))
    · by_cases h1 : a - (L / 3) * b = 0
      · refine ⟨2 * L / 3, ⟨by linarith, by linarith⟩, ?_⟩
        have hne : a - (2 * L / 3) * b ≠ 0 := by nlinarith
        exact mul_pos (mul_pos (by linarith) (sq_pos_of_ne_zero hne)) (phi_pos c _)
      · refine ⟨L / 3, ⟨by linarith, by linarith⟩, ?_⟩
        exact mul_pos (mul_pos (by linarith) (sq_pos_of_ne_zero h1)) (phi_pos c _)
  have hi1 : IntervalIntegrable (fun u : ℝ => u ^ 1 * phi c u) volume 0 L :=
    ((continuous_pow 1).mul (continuous_phi c)).intervalIntegrable 0 L
  have hi2 : IntervalIntegrable (fun u : ℝ => u ^ 2 * phi c u) volume 0 L :=
    ((continuous_pow 2).mul (continuous_phi c)).intervalIntegrable 0 L
  have hi3 : IntervalIntegrable (fun u : ℝ => u ^ 3 * phi c u) volume 0 L :=
    ((continuous_pow 3).mul (continuous_phi c)).intervalIntegrable 0 L
  have hexp : (∫ u in (0 : ℝ)..L, u * (a - u * b) ^ 2 * phi c u) =
      a ^ 2 * Imom 1 c L - 2 * a * b * Imom 2 c L + b ^ 2 * Imom 3 c L := by
    have hfun : (fun u : ℝ => u * (a - u * b) ^ 2 * phi c u) =
        fun u => (a ^ 2 * (u ^ 1 * phi c u) - 2 * a * b * (u ^ 2 * phi c u)) +
          b ^ 2 * (u ^ 3 * phi c u) := by
      ext u; ring
    rw [hfun,
      intervalIntegral.integral_add ((hi1.const_mul _).sub (hi2.const_mul _)) (hi3.const_mul _),
      intervalIntegral.integral_sub (hi1.const_mul _) (hi2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    rfl
  have hval : a ^ 2 * Imom 1 c L - 2 * a * b * Imom 2 c L + b ^ 2 * Imom 3 c L =
      b * (Imom 1 c L * Imom 3 c L - Imom 2 c L ^ 2) := by
    simp only [a, b]; ring
  rw [hexp, hval] at hpos
  nlinarith

/-- Rescaling identity `Imom k c L = L^(k+1) * exp(-c²/2) * Jmom k c L`. -/
lemma Imom_eq_Jmom (k : ℕ) (c : ℝ) {L : ℝ} (hL : 0 < L) :
    Imom k c L = L ^ (k + 1) * Real.exp (-c ^ 2 / 2) * Jmom k c L := by
  unfold Imom Jmom phi
  have hcomp := intervalIntegral.integral_comp_mul_left
    (fun u : ℝ => u ^ k * Real.exp (-(u - c) ^ 2 / 2)) (ne_of_gt hL) (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one] at hcomp
  have hinner : (∫ s in (0 : ℝ)..1, (L * s) ^ k * Real.exp (-(L * s - c) ^ 2 / 2)) =
      L ^ k * Real.exp (-c ^ 2 / 2) *
        ∫ s in (0 : ℝ)..1, s ^ k * Real.exp (c * L * s - L ^ 2 * s ^ 2 / 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [mul_pow]
    have hexp : -(L * s - c) ^ 2 / 2 = -c ^ 2 / 2 + (c * L * s - L ^ 2 * s ^ 2 / 2) := by ring
    rw [hexp, Real.exp_add]
    ring
  rw [hinner] at hcomp
  have hLne : L ≠ 0 := ne_of_gt hL
  have hmul := congrArg (L * ·) hcomp
  simp only [smul_eq_mul] at hmul
  have hcancel : L * (L⁻¹ * ∫ u in (0 : ℝ)..L, u ^ k * Real.exp (-(u - c) ^ 2 / 2)) =
      ∫ u in (0 : ℝ)..L, u ^ k * Real.exp (-(u - c) ^ 2 / 2) := by
    field_simp
  rw [hcancel] at hmul
  rw [← hmul]
  ring

lemma Jmom_pos (k : ℕ) (c L : ℝ) : 0 < Jmom k c L := by
  unfold Jmom
  refine intervalIntegral.integral_pos (by norm_num) ?_ ?_ ?_
  · fun_prop
  · intro s hs
    exact mul_nonneg (pow_nonneg (le_of_lt hs.1) k) (le_of_lt (Real.exp_pos _))
  · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    exact mul_pos (pow_pos (by norm_num) k) (Real.exp_pos _)

/-- The 4 dimensionless state variables `(tf, yf, uf, gf)` and auxiliary `xf, Zf`. -/
def xf (c L : ℝ) : ℝ := L * Imom 1 c L / Imom 2 c L
def tf (c L : ℝ) : ℝ := xf c L - 1
def yf (c L : ℝ) : ℝ := L ^ 3 * phi c L / Imom 2 c L
def Zf (c L : ℝ) : ℝ := L * Imom 3 c L / Imom 2 c L
def uf (c L : ℝ) : ℝ := L ^ 2 - Zf c L
def gf (c L : ℝ) : ℝ := xf c L * Zf c L - L ^ 2

lemma tf_pos (c : ℝ) {L : ℝ} (hL : 0 < L) : 0 < tf c L := by
  unfold tf xf
  have hI2 : 0 < Imom 2 c L := Imom_pos 2 c hL
  rw [sub_pos, one_lt_div hI2]
  have hdiff : 0 < ∫ u in (0 : ℝ)..L, u * (L - u) * phi c u := by
    refine intervalIntegral.integral_pos hL ?_ ?_ ?_
    · have hphi := continuous_phi c; fun_prop
    · intro u hu
      exact mul_nonneg (mul_nonneg (le_of_lt hu.1) (sub_nonneg.mpr hu.2)) (le_of_lt (phi_pos c u))
    · refine ⟨L / 2, ⟨by linarith, by linarith⟩, ?_⟩
      exact mul_pos (mul_pos (by linarith) (by linarith)) (phi_pos c _)
  have hi1 : IntervalIntegrable (fun u : ℝ => u ^ 1 * phi c u) volume 0 L :=
    ((continuous_pow 1).mul (continuous_phi c)).intervalIntegrable 0 L
  have hi2 : IntervalIntegrable (fun u : ℝ => u ^ 2 * phi c u) volume 0 L :=
    ((continuous_pow 2).mul (continuous_phi c)).intervalIntegrable 0 L
  have hrew : (∫ u in (0 : ℝ)..L, u * (L - u) * phi c u) = L * Imom 1 c L - Imom 2 c L := by
    have hf : (fun u : ℝ => u * (L - u) * phi c u) =
        fun u => L * (u ^ 1 * phi c u) - u ^ 2 * phi c u := by ext u; ring
    rw [hf, intervalIntegral.integral_sub (hi1.const_mul _) hi2,
      intervalIntegral.integral_const_mul]
    rfl
  linarith

lemma yf_pos (c : ℝ) {L : ℝ} (hL : 0 < L) : 0 < yf c L := by
  unfold yf
  exact div_pos (mul_pos (pow_pos hL 3) (phi_pos c L)) (Imom_pos 2 c hL)

lemma uf_pos (c : ℝ) {L : ℝ} (hL : 0 < L) : 0 < uf c L := by
  unfold uf Zf
  have hI2 : 0 < Imom 2 c L := Imom_pos 2 c hL
  rw [sub_pos, div_lt_iff₀ hI2]
  have hdiff : 0 < ∫ u in (0 : ℝ)..L, u ^ 2 * (L - u) * phi c u := by
    refine intervalIntegral.integral_pos hL ?_ ?_ ?_
    · have hphi := continuous_phi c; fun_prop
    · intro u hu
      exact mul_nonneg (mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu.2)) (le_of_lt (phi_pos c u))
    · refine ⟨L / 2, ⟨by linarith, by linarith⟩, ?_⟩
      exact mul_pos (mul_pos (sq_pos_of_pos (by linarith)) (by linarith)) (phi_pos c _)
  have hi2 : IntervalIntegrable (fun u : ℝ => u ^ 2 * phi c u) volume 0 L :=
    ((continuous_pow 2).mul (continuous_phi c)).intervalIntegrable 0 L
  have hi3 : IntervalIntegrable (fun u : ℝ => u ^ 3 * phi c u) volume 0 L :=
    ((continuous_pow 3).mul (continuous_phi c)).intervalIntegrable 0 L
  have hrew : (∫ u in (0 : ℝ)..L, u ^ 2 * (L - u) * phi c u) = L * Imom 2 c L - Imom 3 c L := by
    have hf : (fun u : ℝ => u ^ 2 * (L - u) * phi c u) =
        fun u => L * (u ^ 2 * phi c u) - u ^ 3 * phi c u := by ext u; ring
    rw [hf, intervalIntegral.integral_sub (hi2.const_mul _) hi3,
      intervalIntegral.integral_const_mul]
    rfl
  nlinarith

lemma gf_pos (c : ℝ) {L : ℝ} (hL : 0 < L) : 0 < gf c L := by
  unfold gf xf Zf
  have hI2 : 0 < Imom 2 c L := Imom_pos 2 c hL
  have hcs := Imom2_sq_lt_Imom1_mul_Imom3 c hL
  have h1 : L * Imom 1 c L / Imom 2 c L * (L * Imom 3 c L / Imom 2 c L) - L ^ 2 =
      L ^ 2 * (Imom 1 c L * Imom 3 c L - Imom 2 c L ^ 2) / Imom 2 c L ^ 2 := by
    field_simp
  rw [h1]
  exact div_pos (mul_pos (sq_pos_of_pos hL) (sub_pos.mpr hcs)) (sq_pos_of_pos hI2)

lemma Zf_eq (c : ℝ) {L : ℝ} (hL : 0 < L) :
    Zf c L = L * c + 2 * xf c L - yf c L := by
  have hibp := Imom_ibp 1 c L
  norm_num at hibp
  have hI2 : Imom 2 c L ≠ 0 := ne_of_gt (Imom_pos 2 c hL)
  unfold Zf xf yf
  field_simp
  nlinarith

lemma Lc_eq (c : ℝ) {L : ℝ} (hL : 0 < L) :
    L * c = Zf c L - 2 * xf c L + yf c L := by
  linarith [Zf_eq c hL]

lemma Lsq_eq (c L : ℝ) :
    L ^ 2 * tf c L = (tf c L + 1) * uf c L + gf c L := by
  unfold tf uf gf
  ring

lemma Zf_mul_tf_eq (c L : ℝ) :
    Zf c L * tf c L = uf c L + gf c L := by
  unfold tf uf gf
  ring

/-! #### Exact closed ODE system in `D_L = L d/dL` -/

lemma hasDerivAt_xf (c : ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (xf c) ((tf c L + 1 - tf c L * yf c L) / L) L := by
  unfold xf
  have hI2 : Imom 2 c L ≠ 0 := ne_of_gt (Imom_pos 2 c hL)
  have hLne : L ≠ 0 := ne_of_gt hL
  have hnum : HasDerivAt (fun x => x * Imom 1 c x) (1 * Imom 1 c L + L * (L ^ 1 * phi c L)) L :=
    (hasDerivAt_id L).mul (hasDerivAt_Imom_L 1 c L)
  refine hasDerivAt_congr_val (hnum.div (hasDerivAt_Imom_L 2 c L) hI2) ?_
  unfold tf xf yf
  field_simp
  ring

lemma hasDerivAt_tf (c : ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (tf c) ((tf c L + 1 - tf c L * yf c L) / L) L := by
  have h : (fun x => xf c x - 1) = tf c := rfl
  rw [← h]
  exact (hasDerivAt_xf c hL).sub_const 1

lemma hasDerivAt_yf (c : ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (yf c) (yf c L * (1 - uf c L - 2 * tf c L) / L) L := by
  unfold yf
  have hI2 : Imom 2 c L ≠ 0 := ne_of_gt (Imom_pos 2 c hL)
  have hLne : L ≠ 0 := ne_of_gt hL
  have hnum : HasDerivAt (fun x => x ^ 3 * phi c x)
      ((3 * L ^ 2) * phi c L + L ^ 3 * (-(L - c) * phi c L)) L := by
    have hp : HasDerivAt (fun x : ℝ => x ^ 3) (3 * L ^ 2) L := by
      simpa using hasDerivAt_pow 3 L
    exact hp.mul (hasDerivAt_phi c L)
  have hLc := Lc_eq c hL
  refine hasDerivAt_congr_val (hnum.div (hasDerivAt_Imom_L 2 c L) hI2) ?_
  unfold yf xf Zf at hLc
  unfold uf tf xf Zf
  field_simp at hLc ⊢
  linear_combination L * phi c L * hLc

lemma hasDerivAt_Zf (c : ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (Zf c) ((Zf c L + uf c L * yf c L) / L) L := by
  unfold Zf
  have hI2 : Imom 2 c L ≠ 0 := ne_of_gt (Imom_pos 2 c hL)
  have hLne : L ≠ 0 := ne_of_gt hL
  have hnum : HasDerivAt (fun x => x * Imom 3 c x) (1 * Imom 3 c L + L * (L ^ 3 * phi c L)) L :=
    (hasDerivAt_id L).mul (hasDerivAt_Imom_L 3 c L)
  refine hasDerivAt_congr_val (hnum.div (hasDerivAt_Imom_L 2 c L) hI2) ?_
  unfold uf yf Zf
  field_simp
  ring

lemma hasDerivAt_uf (c : ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (uf c) ((gf c L + (2 * tf c L + 1 - tf c L * yf c L) * uf c L) / (tf c L * L)) L := by
  unfold uf
  have hLne : L ≠ 0 := ne_of_gt hL
  have htne : tf c L ≠ 0 := ne_of_gt (tf_pos c hL)
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * L) L := by
    simpa using hasDerivAt_pow 2 L
  have hL2 := Lsq_eq c L
  have hZ := Zf_mul_tf_eq c L
  refine hasDerivAt_congr_val (hsq.sub (hasDerivAt_Zf c hL)) ?_
  unfold uf at hL2 hZ ⊢
  field_simp
  nlinarith

lemma hasDerivAt_gf (c : ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (gf c) (((2 - yf c L) * gf c L + tf c L * uf c L * yf c L) / L) L := by
  unfold gf
  have hLne : L ≠ 0 := ne_of_gt hL
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * L) L := by
    simpa using hasDerivAt_pow 2 L
  refine hasDerivAt_congr_val (((hasDerivAt_xf c hL).mul (hasDerivAt_Zf c hL)).sub hsq) ?_
  unfold tf uf
  field_simp
  ring

/-! #### Hessian factor polynomials `W₁, M₁, tC, C, D₁, tD₁` -/

def W1 (c L : ℝ) : ℝ :=
  tf c L * uf c L + tf c L * yf c L + 2 * tf c L ^ 2 - 2 * tf c L - 1

def M1 (c L : ℝ) : ℝ :=
  tf c L * uf c L - gf c L

def tC (c L : ℝ) : ℝ :=
  gf c L ^ 2 + (uf c L + 2 * tf c L ^ 2 + tf c L - 1) * gf c L +
    uf c L * (tf c L + 1) * (tf c L * yf c L - tf c L - 1)

def Cfun (c L : ℝ) : ℝ := tC c L / tf c L

def D1 (c L : ℝ) : ℝ := W1 c L * Cfun c L - yf c L * M1 c L ^ 2

def tD1 (c L : ℝ) : ℝ := W1 c L * tC c L - tf c L * yf c L * M1 c L ^ 2

lemma tD1_eq_tf_mul_D1 (c : ℝ) {L : ℝ} (hL : 0 < L) :
    tD1 c L = tf c L * D1 c L := by
  unfold tD1 D1 Cfun
  have ht : tf c L ≠ 0 := ne_of_gt (tf_pos c hL)
  field_simp

/-- Direct moment formula for `Cfun`: `Cfun c L = L³ * (2 I₁ I₃² - I₂² I₃ - I₁ I₂ I₄) / I₂³`. -/
lemma Cfun_eq_moments (c : ℝ) {L : ℝ} (hL : 0 < L) :
    Cfun c L =
      L ^ 3 * (2 * Imom 1 c L * Imom 3 c L ^ 2 - Imom 2 c L ^ 2 * Imom 3 c L -
        Imom 1 c L * Imom 2 c L * Imom 4 c L) / Imom 2 c L ^ 3 := by
  have hI2 : Imom 2 c L ≠ 0 := ne_of_gt (Imom_pos 2 c hL)
  have ht : tf c L ≠ 0 := ne_of_gt (tf_pos c hL)
  have hibp1 := Imom_ibp 1 c L
  have hibp2 := Imom_ibp 2 c L
  norm_num at hibp1 hibp2
  have hI4 : Imom 4 c L = c * Imom 3 c L + 3 * Imom 2 c L - L ^ 3 * phi c L := by
    linarith
  have hcI2 : c * Imom 2 c L = Imom 3 c L - 2 * Imom 1 c L + L ^ 2 * phi c L := by
    linarith
  have ht_unfold : L * Imom 1 c L / Imom 2 c L - 1 ≠ 0 := ht
  have ht_num : L * Imom 1 c L - Imom 2 c L ≠ 0 := by
    intro h0; apply ht_unfold; rw [sub_eq_zero, div_eq_iff hI2, one_mul]; linarith
  unfold Cfun tC gf uf Zf tf xf yf
  rw [hI4]
  have hsub : Imom 1 c L * Imom 2 c L * (c * Imom 3 c L + 3 * Imom 2 c L - L ^ 3 * phi c L) =
      Imom 1 c L * Imom 3 c L * (c * Imom 2 c L) +
        Imom 1 c L * Imom 2 c L * (3 * Imom 2 c L - L ^ 3 * phi c L) := by ring
  rw [hsub, hcI2]
  field_simp [ht_num]
  ring

lemma Cfun_eq_Jmom (c : ℝ) {L : ℝ} (hL : 0 < L) :
    Cfun c L = L ^ 4 *
      ((2 * Jmom 1 c L * Jmom 3 c L ^ 2 - Jmom 2 c L ^ 2 * Jmom 3 c L -
        Jmom 1 c L * Jmom 2 c L * Jmom 4 c L) / Jmom 2 c L ^ 3) := by
  rw [Cfun_eq_moments c hL,
    Imom_eq_Jmom 1 c hL, Imom_eq_Jmom 2 c hL, Imom_eq_Jmom 3 c hL, Imom_eq_Jmom 4 c hL]
  have hJ2 : Jmom 2 c L ≠ 0 := ne_of_gt (Jmom_pos 2 c L)
  have hexp : Real.exp (-c ^ 2 / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hLne : L ≠ 0 := ne_of_gt hL
  field_simp
  ring

/-! #### General 1D ODE Barrier Lemma -/

lemma pos_of_ode_barrier {F : ℝ → ℝ}
    (hdiff : ∀ L > 0, DifferentiableAt ℝ F L)
    (hinit : ∃ ε > 0, ∀ L ∈ Ioo 0 ε, 0 < F L)
    (hbar : ∀ L > 0, F L = 0 → 0 < deriv F L) :
    ∀ L > 0, 0 < F L := by
  by_contra hnot
  push Not at hnot
  obtain ⟨L₁, hL₁pos, hL₁le⟩ := hnot
  obtain ⟨ε, hεpos, hε⟩ := hinit
  set S : Set ℝ := {L : ℝ | 0 < L ∧ F L ≤ 0}
  have hSne : S.Nonempty := ⟨L₁, hL₁pos, hL₁le⟩
  have hSbd : ∀ L ∈ S, ε ≤ L := by
    intro L ⟨hLp, hFle⟩
    by_contra hlt
    push Not at hlt
    exact not_lt_of_ge hFle (hε L ⟨hLp, hlt⟩)
  have hSbdd : BddBelow S := ⟨ε, hSbd⟩
  set L₀ := sInf S
  have hεle : ε ≤ L₀ := le_csInf hSne hSbd
  have hL₀pos : 0 < L₀ := lt_of_lt_of_le hεpos hεle
  have hpos_left : ∀ L ∈ Ioo 0 L₀, 0 < F L := by
    intro L ⟨hLp, hLlt⟩
    by_contra hle
    push Not at hle
    exact not_le_of_gt hLlt (csInf_le hSbdd ⟨hLp, hle⟩)
  have hcont : ContinuousAt F L₀ := (hdiff L₀ hL₀pos).continuousAt
  have hFL₀_le : F L₀ ≤ 0 := by
    by_contra hgt
    push Not at hgt
    have hev : ∀ᶠ L in 𝓝 L₀, 0 < F L := hcont.eventually (Ioi_mem_nhds hgt)
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδpos, hδ⟩ := hev
    obtain ⟨L₂, hL₂S, hL₂lt⟩ := Real.lt_sInf_add_pos hSne hδpos
    have hL₂ge : L₀ ≤ L₂ := csInf_le hSbdd hL₂S
    have hdist : dist L₂ L₀ < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hL₂ge)]
      linarith
    exact not_lt_of_ge hL₂S.2 (hδ hdist)
  have hFL₀_ge : 0 ≤ F L₀ := by
    have hlim : Tendsto F (𝓝[<] L₀) (𝓝 (F L₀)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ L in 𝓝[<] L₀, 0 ≤ F L := by
      have hmem : Ioo 0 L₀ ∈ 𝓝[<] L₀ := Ioo_mem_nhdsLT hL₀pos
      exact Filter.mem_of_superset hmem fun L hL => le_of_lt (hpos_left L hL)
    exact ge_of_tendsto hlim hev
  have hFL₀_eq : F L₀ = 0 := le_antisymm hFL₀_le hFL₀_ge
  have hder_pos : 0 < deriv F L₀ := hbar L₀ hL₀pos hFL₀_eq
  have hslope : Tendsto (fun L => (F L - F L₀) / (L - L₀)) (𝓝[<] L₀) (𝓝 (deriv F L₀)) := by
    have hd := (hdiff L₀ hL₀pos).hasDerivAt.tendsto_slope_zero_left
    have hcomp : Tendsto (fun L : ℝ => L - L₀) (𝓝[<] L₀) (𝓝[<] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : Continuous (fun L : ℝ => L - L₀) := continuous_id.sub continuous_const
        have hct : Tendsto (fun L : ℝ => L - L₀) (𝓝 L₀) (𝓝 (L₀ - L₀)) := hc.continuousAt.tendsto
        rw [sub_self] at hct
        exact hct.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun L (hL : L < L₀) => sub_neg.mpr hL
    have h1 := hd.comp hcomp
    refine h1.congr' (eventually_nhdsWithin_of_forall fun L _ => ?_)
    simp only [Function.comp_apply, smul_eq_mul, add_sub_cancel, div_eq_inv_mul]
  have hslope_le : deriv F L₀ ≤ 0 := by
    refine le_of_tendsto hslope ?_
    have hmem : Ioo 0 L₀ ∈ 𝓝[<] L₀ := Ioo_mem_nhdsLT hL₀pos
    refine Filter.mem_of_superset hmem fun L hL => ?_
    show (F L - F L₀) / (L - L₀) ≤ 0
    rw [hFL₀_eq, sub_zero]
    exact div_nonpos_of_nonneg_of_nonpos (le_of_lt (hpos_left L hL)) (sub_nonpos.mpr (le_of_lt hL.2))
  linarith

/-! #### `L → 0+` asymptotics for `W₁`, `M₁`, `Cfun`, `D₁` -/

lemma Jmom_taylor_bound (k : ℕ) (c : ℝ) :
    ∃ K > 0, ∃ δ > 0, ∀ L ∈ Ioo 0 δ,
      |Jmom k c L - (1 / ((k : ℝ) + 1) + c / ((k : ℝ) + 2) * L +
        (c ^ 2 - 1) / (2 * ((k : ℝ) + 3)) * L ^ 2)| ≤ K * L ^ 3 := by
  set M := |c| + 1
  have hM : 0 < M := by positivity
  set δ := min 1 (1 / (2 * M))
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  set K := 2 * M ^ 3 + |c| + 1
  have hK : 0 < K := by positivity
  refine ⟨K, hK, δ, hδ, fun L ⟨hLpos, hLlt⟩ => ?_⟩
  have hL1 : L ≤ 1 := le_trans (le_of_lt hLlt) (min_le_left _ _)
  have hLM : M * L ≤ 1 := by
    have h2 : L ≤ 1 / (2 * M) := le_trans (le_of_lt hLlt) (min_le_right _ _)
    have h3 : 2 * M * L ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * M)
      rwa [mul_one_div_cancel (by positivity : (2 : ℝ) * M ≠ 0)] at this
    linarith
  have hpoly : (1 / ((k : ℝ) + 1) + c / ((k : ℝ) + 2) * L +
      (c ^ 2 - 1) / (2 * ((k : ℝ) + 3)) * L ^ 2) =
      ∫ s in (0 : ℝ)..1,
        s ^ k * (1 + c * L * s + (c ^ 2 - 1) / 2 * L ^ 2 * s ^ 2) := by
    have hp0 : (∫ s in (0 : ℝ)..1, s ^ k) = 1 / ((k : ℝ) + 1) := by
      rw [integral_pow]; simp
    have hp1 : (∫ s in (0 : ℝ)..1, s ^ (k + 1)) = 1 / ((k : ℝ) + 2) := by
      rw [integral_pow]; simp [Nat.cast_add]; ring
    have hp2 : (∫ s in (0 : ℝ)..1, s ^ (k + 2)) = 1 / ((k : ℝ) + 3) := by
      rw [integral_pow]; simp [Nat.cast_add]; ring
    have hfun : (fun s : ℝ => s ^ k * (1 + c * L * s + (c ^ 2 - 1) / 2 * L ^ 2 * s ^ 2)) =
        fun s => (s ^ k + (c * L) * s ^ (k + 1)) + ((c ^ 2 - 1) / 2 * L ^ 2) * s ^ (k + 2) := by
      ext s; ring
    rw [hfun,
      intervalIntegral.integral_add
        (((continuous_pow k).intervalIntegrable 0 1).add
          (((continuous_pow (k + 1)).intervalIntegrable 0 1).const_mul _))
        (((continuous_pow (k + 2)).intervalIntegrable 0 1).const_mul _),
      intervalIntegral.integral_add ((continuous_pow k).intervalIntegrable 0 1)
        (((continuous_pow (k + 1)).intervalIntegrable 0 1).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hp0, hp1, hp2]
    field_simp
  rw [hpoly]
  unfold Jmom
  have hint1 : IntervalIntegrable (fun s : ℝ => s ^ k * Real.exp (c * L * s - L ^ 2 * s ^ 2 / 2)) volume 0 1 :=
    (by fun_prop : Continuous fun s : ℝ => s ^ k * Real.exp (c * L * s - L ^ 2 * s ^ 2 / 2)).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun s : ℝ => s ^ k * (1 + c * L * s + (c ^ 2 - 1) / 2 * L ^ 2 * s ^ 2)) volume 0 1 :=
    (by fun_prop : Continuous fun s : ℝ => s ^ k * (1 + c * L * s + (c ^ 2 - 1) / 2 * L ^ 2 * s ^ 2)).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_sub hint1 hint2]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := K * L ^ 3) (f := fun s : ℝ =>
      s ^ k * Real.exp (c * L * s - L ^ 2 * s ^ 2 / 2) -
        s ^ k * (1 + c * L * s + (c ^ 2 - 1) / 2 * L ^ 2 * s ^ 2)) ?_
  · simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hnorm
  · intro s hs
    have hs0 : 0 ≤ s := le_of_lt (by rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs; exact hs.1)
    have hs1 : s ≤ 1 := by rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs; exact hs.2
    rw [Real.norm_eq_abs]
    have hfac : s ^ k * Real.exp (c * L * s - L ^ 2 * s ^ 2 / 2) -
        s ^ k * (1 + c * L * s + (c ^ 2 - 1) / 2 * L ^ 2 * s ^ 2) =
        s ^ k * (Real.exp (c * L * s - L ^ 2 * s ^ 2 / 2) -
          (1 + c * L * s + (c ^ 2 - 1) / 2 * L ^ 2 * s ^ 2)) := by ring
    rw [hfac, abs_mul]
    have hsk : |s ^ k| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hs0 k)]
      exact pow_le_one₀ hs0 hs1
    set z := c * L * s - L ^ 2 * s ^ 2 / 2
    have hz_le : |z| ≤ M * L := by
      have h1 : |c * L * s| ≤ |c| * L := by
        rw [abs_mul, abs_mul, abs_of_pos hLpos, abs_of_nonneg hs0]
        calc |c| * L * s ≤ |c| * L * 1 :=
              mul_le_mul_of_nonneg_left hs1 (mul_nonneg (abs_nonneg c) (le_of_lt hLpos))
          _ = |c| * L := mul_one _
      have h2 : |L ^ 2 * s ^ 2 / 2| ≤ L := by
        rw [abs_of_nonneg (by positivity)]
        have hs2 : s ^ 2 ≤ 1 := by nlinarith
        have hL2 : L ^ 2 ≤ L := by nlinarith
        nlinarith
      calc |z| = |c * L * s - L ^ 2 * s ^ 2 / 2| := rfl
        _ ≤ |c * L * s| + |L ^ 2 * s ^ 2 / 2| := abs_sub _ _
        _ ≤ |c| * L + L := add_le_add h1 h2
        _ = M * L := by simp only [M]; ring
    have hz1 : |z| ≤ 1 := le_trans hz_le hLM
    have heb := Real.exp_bound hz1 (n := 3) (by norm_num)
    have hsum3 : (∑ m ∈ Finset.range 3, z ^ m / (m.factorial : ℝ)) = 1 + z + z ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [hsum3] at heb
    have hconst3 : ((Nat.succ 3 : ℝ) / ((Nat.factorial 3 : ℝ) * 3)) ≤ 2 := by
      norm_num [Nat.factorial]
    have heb2 : |Real.exp z - (1 + z + z ^ 2 / 2)| ≤ 2 * (M * L) ^ 3 := by
      have hz3 : |z| ^ 3 ≤ (M * L) ^ 3 := pow_le_pow_left₀ (abs_nonneg z) hz_le 3
      calc |Real.exp z - (1 + z + z ^ 2 / 2)|
          ≤ |z| ^ 3 * (↑(Nat.succ 3) / (↑(Nat.factorial 3) * 3)) := heb
        _ ≤ (M * L) ^ 3 * 2 := mul_le_mul hz3 hconst3 (by positivity) (by positivity)
        _ = 2 * (M * L) ^ 3 := by ring
    have hrem : (1 + z + z ^ 2 / 2) - (1 + c * L * s + (c ^ 2 - 1) / 2 * L ^ 2 * s ^ 2) =
        (-c / 2 * s ^ 3 + L * s ^ 4 / 8) * L ^ 3 := by
      simp only [z]; ring
    have hrem_abs : |(1 + z + z ^ 2 / 2) - (1 + c * L * s + (c ^ 2 - 1) / 2 * L ^ 2 * s ^ 2)| ≤
        (|c| + 1) * L ^ 3 := by
      rw [hrem, abs_mul, abs_of_pos (pow_pos hLpos 3)]
      have h1 : |-c / 2 * s ^ 3| ≤ |c| := by
        rw [abs_mul, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_nonneg (pow_nonneg hs0 3)]
        have hs3 : s ^ 3 ≤ 1 := pow_le_one₀ hs0 hs1
        nlinarith [abs_nonneg c]
      have h2 : |L * s ^ 4 / 8| ≤ 1 := by
        rw [abs_of_nonneg (by positivity)]
        have hs4 : s ^ 4 ≤ 1 := pow_le_one₀ hs0 hs1
        nlinarith
      have htri := abs_add_le (-c / 2 * s ^ 3) (L * s ^ 4 / 8)
      nlinarith [pow_pos hLpos 3]
    have htot : |Real.exp z - (1 + c * L * s + (c ^ 2 - 1) / 2 * L ^ 2 * s ^ 2)| ≤ K * L ^ 3 := by
      have htri : Real.exp z - (1 + c * L * s + (c ^ 2 - 1) / 2 * L ^ 2 * s ^ 2) =
          (Real.exp z - (1 + z + z ^ 2 / 2)) +
          ((1 + z + z ^ 2 / 2) - (1 + c * L * s + (c ^ 2 - 1) / 2 * L ^ 2 * s ^ 2)) := by ring
      rw [htri]
      have ha1 := abs_add_le (Real.exp z - (1 + z + z ^ 2 / 2))
        ((1 + z + z ^ 2 / 2) - (1 + c * L * s + (c ^ 2 - 1) / 2 * L ^ 2 * s ^ 2))
      have hK_eq : 2 * (M * L) ^ 3 + (|c| + 1) * L ^ 3 = K * L ^ 3 := by simp only [K]; ring
      linarith
    calc |s ^ k| * |Real.exp z - (1 + c * L * s + (c ^ 2 - 1) / 2 * L ^ 2 * s ^ 2)|
        ≤ 1 * (K * L ^ 3) := mul_le_mul hsk htot (abs_nonneg _) zero_le_one
      _ = K * L ^ 3 := one_mul _

lemma exp_quad_taylor_bound (c : ℝ) :
    ∃ K > 0, ∃ δ > 0, ∀ L ∈ Ioo 0 δ,
      |Real.exp (c * L - L ^ 2 / 2) - (1 + c * L + (c ^ 2 - 1) / 2 * L ^ 2)| ≤ K * L ^ 3 := by
  set M := |c| + 1
  set δ := min 1 (1 / (2 * M))
  set K := 2 * M ^ 3 + |c| + 1
  refine ⟨K, by positivity, δ, lt_min zero_lt_one (by positivity), fun L ⟨hLpos, hLlt⟩ => ?_⟩
  have hL1 : L ≤ 1 := le_trans (le_of_lt hLlt) (min_le_left _ _)
  have hLM : M * L ≤ 1 := by
    have h2 : L ≤ 1 / (2 * M) := le_trans (le_of_lt hLlt) (min_le_right _ _)
    have h3 : 2 * M * L ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * M)
      rwa [mul_one_div_cancel (by positivity : (2 : ℝ) * M ≠ 0)] at this
    linarith
  set z := c * L - L ^ 2 / 2
  have hz_le : |z| ≤ M * L := by
    have h1 : |c * L| = |c| * L := by rw [abs_mul, abs_of_pos hLpos]
    have h2 : |L ^ 2 / 2| ≤ L := by rw [abs_of_nonneg (by positivity)]; nlinarith
    calc |z| ≤ |c * L| + |L ^ 2 / 2| := abs_sub _ _
      _ ≤ |c| * L + L := by linarith
      _ = M * L := by ring
  have heb := Real.exp_bound (le_trans hz_le hLM) (n := 3) (by norm_num)
  have hsum3 : (∑ m ∈ Finset.range 3, z ^ m / (m.factorial : ℝ)) = 1 + z + z ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum3] at heb
  have hconst3 : ((Nat.succ 3 : ℝ) / ((Nat.factorial 3 : ℝ) * 3)) ≤ 2 := by
    norm_num [Nat.factorial]
  have heb2 : |Real.exp z - (1 + z + z ^ 2 / 2)| ≤ 2 * (M * L) ^ 3 :=
    le_trans heb (by
      have := mul_le_mul (pow_le_pow_left₀ (abs_nonneg z) hz_le 3) hconst3 (by positivity) (by positivity)
      linarith)
  have hrem : (1 + z + z ^ 2 / 2) - (1 + c * L + (c ^ 2 - 1) / 2 * L ^ 2) =
      (-c / 2 + L / 8) * L ^ 3 := by simp only [z]; ring
  have hrem_abs : |(1 + z + z ^ 2 / 2) - (1 + c * L + (c ^ 2 - 1) / 2 * L ^ 2)| ≤
      (|c| + 1) * L ^ 3 := by
    rw [hrem, abs_mul, abs_of_pos (pow_pos hLpos 3)]
    have h1 : |-c / 2| ≤ |c| := by
      rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith [abs_nonneg c]
    have h2 : |L / 8| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; linarith
    nlinarith [abs_add_le (-c / 2) (L / 8), pow_pos hLpos 3]
  have htri : Real.exp z - (1 + c * L + (c ^ 2 - 1) / 2 * L ^ 2) =
      (Real.exp z - (1 + z + z ^ 2 / 2)) +
      ((1 + z + z ^ 2 / 2) - (1 + c * L + (c ^ 2 - 1) / 2 * L ^ 2)) := by ring
  rw [htri]
  have ha1 := abs_add_le (Real.exp z - (1 + z + z ^ 2 / 2))
    ((1 + z + z ^ 2 / 2) - (1 + c * L + (c ^ 2 - 1) / 2 * L ^ 2))
  have hK_eq : 2 * (M * L) ^ 3 + (|c| + 1) * L ^ 3 = K * L ^ 3 := by simp only [K]; ring
  linarith

lemma tendsto_Jmom_zero (k : ℕ) (c : ℝ) :
    Tendsto (Jmom k c) (𝓝[>] 0) (𝓝 (1 / ((k : ℝ) + 1))) := by
  obtain ⟨K, hK, δ, hδ, hbd⟩ := Jmom_taylor_bound k c
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set B := |c| / ((k : ℝ) + 2) + |c ^ 2 - 1| / (2 * ((k : ℝ) + 3)) + K
  have hB : 0 < B := by positivity
  refine ⟨min δ (min 1 (ε / B)), lt_min hδ (lt_min zero_lt_one (div_pos hε hB)), fun L hLpos hLdist => ?_⟩
  have hLp : 0 < L := hLpos
  rw [Real.dist_eq, sub_zero, abs_of_pos hLp] at hLdist
  have hLδ : L < δ := lt_of_lt_of_le hLdist (min_le_left _ _)
  have hL1 : L < 1 := lt_of_lt_of_le hLdist (le_trans (min_le_right _ _) (min_le_left _ _))
  have hLε : L < ε / B := lt_of_lt_of_le hLdist (le_trans (min_le_right _ _) (min_le_right _ _))
  have h1 := hbd L ⟨hLp, hLδ⟩
  rw [Real.dist_eq]
  have htri : Jmom k c L - 1 / ((k : ℝ) + 1) =
      (Jmom k c L - (1 / ((k : ℝ) + 1) + c / ((k : ℝ) + 2) * L +
        (c ^ 2 - 1) / (2 * ((k : ℝ) + 3)) * L ^ 2)) +
      (c / ((k : ℝ) + 2) * L + (c ^ 2 - 1) / (2 * ((k : ℝ) + 3)) * L ^ 2) := by ring
  rw [htri]
  have h2 : |c / ((k : ℝ) + 2) * L| = |c| / ((k : ℝ) + 2) * L := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 2), abs_of_pos hLp]
  have h3 : |(c ^ 2 - 1) / (2 * ((k : ℝ) + 3)) * L ^ 2| ≤ |c ^ 2 - 1| / (2 * ((k : ℝ) + 3)) * L := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * ((k : ℝ) + 3)),
      abs_of_pos (sq_pos_of_pos hLp)]
    have hL2 : L ^ 2 ≤ L := by nlinarith
    exact mul_le_mul_of_nonneg_left hL2 (by positivity)
  have h4 : K * L ^ 3 ≤ K * L := by
    have hL3 : L ^ 3 ≤ L := by nlinarith
    exact mul_le_mul_of_nonneg_left hL3 (le_of_lt hK)
  have hBL : B * L < ε := by
    have := mul_lt_mul_of_pos_left hLε hB
    rwa [mul_div_cancel₀ _ (ne_of_gt hB)] at this
  have ha1 := abs_add_le
    (Jmom k c L - (1 / ((k : ℝ) + 1) + c / ((k : ℝ) + 2) * L +
      (c ^ 2 - 1) / (2 * ((k : ℝ) + 3)) * L ^ 2))
    (c / ((k : ℝ) + 2) * L + (c ^ 2 - 1) / (2 * ((k : ℝ) + 3)) * L ^ 2)
  have ha2 := abs_add_le (c / ((k : ℝ) + 2) * L) ((c ^ 2 - 1) / (2 * ((k : ℝ) + 3)) * L ^ 2)
  have hBeq : (|c| / ((k : ℝ) + 2) + |c ^ 2 - 1| / (2 * ((k : ℝ) + 3)) + K) * L = B * L := rfl
  linarith

lemma tendsto_Jmom_rem2 (k : ℕ) (c : ℝ) :
    Tendsto (fun L => (Jmom k c L - (1 / ((k : ℝ) + 1) + c / ((k : ℝ) + 2) * L +
        (c ^ 2 - 1) / (2 * ((k : ℝ) + 3)) * L ^ 2)) / L ^ 2) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K, hK, δ, hδ, hbd⟩ := Jmom_taylor_bound k c
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min δ (ε / K), lt_min hδ (div_pos hε hK), fun L hLpos hLdist => ?_⟩
  have hLp : 0 < L := hLpos
  rw [Real.dist_eq, sub_zero, abs_of_pos hLp] at hLdist
  have hLδ : L < δ := lt_of_lt_of_le hLdist (min_le_left _ _)
  have hLε : L < ε / K := lt_of_lt_of_le hLdist (min_le_right _ _)
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (sq_pos_of_pos hLp)]
  calc _ ≤ K * L ^ 3 / L ^ 2 := div_le_div_of_nonneg_right (hbd L ⟨hLp, hLδ⟩) (by positivity)
    _ = K * L := by field_simp
    _ < ε := by
        have := mul_lt_mul_of_pos_left hLε hK
        rwa [mul_div_cancel₀ _ (ne_of_gt hK)] at this

lemma tendsto_exp_quad_rem2 (c : ℝ) :
    Tendsto (fun L => (Real.exp (c * L - L ^ 2 / 2) -
        (1 + c * L + (c ^ 2 - 1) / 2 * L ^ 2)) / L ^ 2) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K, hK, δ, hδ, hbd⟩ := exp_quad_taylor_bound c
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min δ (ε / K), lt_min hδ (div_pos hε hK), fun L hLpos hLdist => ?_⟩
  have hLp : 0 < L := hLpos
  rw [Real.dist_eq, sub_zero, abs_of_pos hLp] at hLdist
  have hLδ : L < δ := lt_of_lt_of_le hLdist (min_le_left _ _)
  have hLε : L < ε / K := lt_of_lt_of_le hLdist (min_le_right _ _)
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (sq_pos_of_pos hLp)]
  calc _ ≤ K * L ^ 3 / L ^ 2 := div_le_div_of_nonneg_right (hbd L ⟨hLp, hLδ⟩) (by positivity)
    _ = K * L := by field_simp
    _ < ε := by
        have := mul_lt_mul_of_pos_left hLε hK
        rwa [mul_div_cancel₀ _ (ne_of_gt hK)] at this

lemma tendsto_Jmom_rem1 (k : ℕ) (c : ℝ) :
    Tendsto (fun L => (Jmom k c L - (1 / ((k : ℝ) + 1) + c / ((k : ℝ) + 2) * L)) / L)
      (𝓝[>] 0) (𝓝 0) := by
  have h2 := tendsto_Jmom_rem2 k c
  have hid : Tendsto (fun L : ℝ => L) (𝓝[>] 0) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hmul := (h2.mul hid).add (hid.const_mul ((c ^ 2 - 1) / (2 * ((k : ℝ) + 3))))
  simp only [mul_zero, add_zero] at hmul
  refine hmul.congr' (eventually_nhdsWithin_of_forall fun L (hL : 0 < L) => ?_)
  have hLne : L ≠ 0 := ne_of_gt hL
  field_simp
  ring

lemma tendsto_Cfun_div_L4 (c : ℝ) :
    Tendsto (fun L => Cfun c L / L ^ 4) (𝓝[>] 0) (𝓝 (3 / 80)) := by
  have h1 := tendsto_Jmom_zero 1 c
  have h2 := tendsto_Jmom_zero 2 c
  have h3 := tendsto_Jmom_zero 3 c
  have h4 := tendsto_Jmom_zero 4 c
  have hlim : Tendsto (fun L =>
      (2 * Jmom 1 c L * Jmom 3 c L ^ 2 - Jmom 2 c L ^ 2 * Jmom 3 c L -
        Jmom 1 c L * Jmom 2 c L * Jmom 4 c L) / Jmom 2 c L ^ 3)
      (𝓝[>] 0) (𝓝 (3 / 80)) := by
    have hnum := (((h1.const_mul 2).mul (h3.pow 2)).sub ((h2.pow 2).mul h3)).sub
      ((h1.mul h2).mul h4)
    have hden := h2.pow 3
    have hdne : (1 / ((2 : ℕ) + 1 : ℝ)) ^ 3 ≠ 0 := by norm_num
    have hdiv := hnum.div hden hdne
    have hval : ((2 * (1 / ((1 : ℕ) + 1 : ℝ)) * (1 / ((3 : ℕ) + 1 : ℝ)) ^ 2 -
        (1 / ((2 : ℕ) + 1 : ℝ)) ^ 2 * (1 / ((3 : ℕ) + 1 : ℝ)) -
        (1 / ((1 : ℕ) + 1 : ℝ)) * (1 / ((2 : ℕ) + 1 : ℝ)) * (1 / ((4 : ℕ) + 1 : ℝ))) /
        (1 / ((2 : ℕ) + 1 : ℝ)) ^ 3) = 3 / 80 := by norm_num
    rwa [hval] at hdiv
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun L (hL : 0 < L) => ?_)
  dsimp only
  symm
  rw [Cfun_eq_Jmom c hL]
  have hL4 : L ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt hL)
  field_simp

lemma tendsto_W1_div_L2 (c : ℝ) :
    Tendsto (fun L => W1 c L / L ^ 2) (𝓝[>] 0) (𝓝 (c ^ 2 / 80 + 1 / 20)) := by
  set r1 := fun L => (Jmom 1 c L - (1 / 2 + c / 3 * L + (c ^ 2 - 1) / 8 * L ^ 2)) / L ^ 2
  set r2 := fun L => (Jmom 2 c L - (1 / 3 + c / 4 * L + (c ^ 2 - 1) / 10 * L ^ 2)) / L ^ 2
  set re := fun L => (Real.exp (c * L - L ^ 2 / 2) - (1 + c * L + (c ^ 2 - 1) / 2 * L ^ 2)) / L ^ 2
  have hr1 : Tendsto r1 (𝓝[>] 0) (𝓝 0) :=
    (tendsto_Jmom_rem2 1 c).congr fun L => by simp only [r1]; norm_num
  have hr2 : Tendsto r2 (𝓝[>] 0) (𝓝 0) :=
    (tendsto_Jmom_rem2 2 c).congr fun L => by simp only [r2]; norm_num
  have hre : Tendsto re (𝓝[>] 0) (𝓝 0) := tendsto_exp_quad_rem2 c
  have hj1 := tendsto_Jmom_zero 1 c
  have hj2 := tendsto_Jmom_zero 2 c
  have hj3 := tendsto_Jmom_zero 3 c
  have hid : Tendsto (fun L : ℝ => L) (𝓝[>] 0) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hpoly_lim : Tendsto (fun L =>
      ((Jmom 1 c L - Jmom 2 c L) * (Jmom 2 c L - Jmom 3 c L) +
        (r1 L * (1 + 5 * c / 6 * L + (2 * c ^ 2 / 5 - 2 / 5) * L ^ 2 +
          (re L + 2 * r1 L - 6 * r2 L) * L ^ 2) +
         r2 L * (-2 - 3 * c / 2 * L + (-13 * c ^ 2 / 20 + 13 / 20) * L ^ 2 +
          (-re L + 3 * r2 L) * L ^ 2) +
         re L * (1 / 6 + c / 12 * L + (c ^ 2 - 1) / 40 * L ^ 2) +
         (c ^ 2 / 720 - 1 / 120) +
         (-c ^ 3 / 240 + c / 240) * L +
         (-c ^ 4 / 800 + c ^ 2 / 400 - 1 / 800) * L ^ 2)) / Jmom 2 c L ^ 2)
      (𝓝[>] 0) (𝓝 (c ^ 2 / 80 + 1 / 20)) := by
    have hA : Tendsto (fun L => (Jmom 1 c L - Jmom 2 c L) * (Jmom 2 c L - Jmom 3 c L))
        (𝓝[>] 0) (𝓝 ((1 / ((1 : ℕ) + 1 : ℝ) - 1 / ((2 : ℕ) + 1 : ℝ)) *
          (1 / ((2 : ℕ) + 1 : ℝ) - 1 / ((3 : ℕ) + 1 : ℝ)))) :=
      (hj1.sub hj2).mul (hj2.sub hj3)
    have hB1 : Tendsto (fun L => r1 L * (1 + 5 * c / 6 * L + (2 * c ^ 2 / 5 - 2 / 5) * L ^ 2 +
          (re L + 2 * r1 L - 6 * r2 L) * L ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      have hfac : Tendsto (fun L => 1 + 5 * c / 6 * L + (2 * c ^ 2 / 5 - 2 / 5) * L ^ 2 +
          (re L + 2 * r1 L - 6 * r2 L) * L ^ 2) (𝓝[>] 0) (𝓝 1) := by
        have h1 := (((tendsto_const_nhds (x := (1 : ℝ))).add (hid.const_mul (5 * c / 6))).add
          ((hid.pow 2).const_mul (2 * c ^ 2 / 5 - 2 / 5))).add
          (((hre.add (hr1.const_mul 2)).sub (hr2.const_mul 6)).mul (hid.pow 2))
        simpa using h1
      simpa using hr1.mul hfac
    have hB2 : Tendsto (fun L => r2 L * (-2 - 3 * c / 2 * L + (-13 * c ^ 2 / 20 + 13 / 20) * L ^ 2 +
          (-re L + 3 * r2 L) * L ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      have hfac : Tendsto (fun L => -2 - 3 * c / 2 * L + (-13 * c ^ 2 / 20 + 13 / 20) * L ^ 2 +
          (-re L + 3 * r2 L) * L ^ 2) (𝓝[>] 0) (𝓝 (-2)) := by
        have h1 := (((tendsto_const_nhds (x := (-2 : ℝ))).sub (hid.const_mul (3 * c / 2))).add
          ((hid.pow 2).const_mul (-13 * c ^ 2 / 20 + 13 / 20))).add
          ((hre.neg.add (hr2.const_mul 3)).mul (hid.pow 2))
        simpa using h1
      simpa using hr2.mul hfac
    have hB3 : Tendsto (fun L => re L * (1 / 6 + c / 12 * L + (c ^ 2 - 1) / 40 * L ^ 2))
        (𝓝[>] 0) (𝓝 0) := by
      have hfac : Tendsto (fun L => 1 / 6 + c / 12 * L + (c ^ 2 - 1) / 40 * L ^ 2)
          (𝓝[>] 0) (𝓝 (1 / 6)) := by
        have h1 := ((tendsto_const_nhds (x := (1 / 6 : ℝ))).add (hid.const_mul (c / 12))).add
          ((hid.pow 2).const_mul ((c ^ 2 - 1) / 40))
        simpa using h1
      simpa using hre.mul hfac
    have hB4 : Tendsto (fun L => (c ^ 2 / 720 - 1 / 120) +
         (-c ^ 3 / 240 + c / 240) * L +
         (-c ^ 4 / 800 + c ^ 2 / 400 - 1 / 800) * L ^ 2)
        (𝓝[>] 0) (𝓝 (c ^ 2 / 720 - 1 / 120)) := by
      have h1 := ((tendsto_const_nhds (x := c ^ 2 / 720 - 1 / 120)).add
        (hid.const_mul (-c ^ 3 / 240 + c / 240))).add
        ((hid.pow 2).const_mul (-c ^ 4 / 800 + c ^ 2 / 400 - 1 / 800))
      simpa using h1
    have hB1234 : Tendsto (fun L =>
        r1 L * (1 + 5 * c / 6 * L + (2 * c ^ 2 / 5 - 2 / 5) * L ^ 2 +
          (re L + 2 * r1 L - 6 * r2 L) * L ^ 2) +
        r2 L * (-2 - 3 * c / 2 * L + (-13 * c ^ 2 / 20 + 13 / 20) * L ^ 2 +
          (-re L + 3 * r2 L) * L ^ 2) +
        re L * (1 / 6 + c / 12 * L + (c ^ 2 - 1) / 40 * L ^ 2) +
        (c ^ 2 / 720 - 1 / 120) +
        (-c ^ 3 / 240 + c / 240) * L +
        (-c ^ 4 / 800 + c ^ 2 / 400 - 1 / 800) * L ^ 2)
        (𝓝[>] 0) (𝓝 (0 + 0 + 0 + (c ^ 2 / 720 - 1 / 120))) := by
      have h := (((hB1.add hB2).add hB3).add hB4)
      refine h.congr fun L => by ring
    have hnum := hA.add hB1234
    have hden := hj2.pow 2
    have hdne : (1 / ((2 : ℕ) + 1 : ℝ)) ^ 2 ≠ 0 := by norm_num
    have hdiv := hnum.div hden hdne
    have hval : (((1 / ((1 : ℕ) + 1 : ℝ) - 1 / ((2 : ℕ) + 1 : ℝ)) *
        (1 / ((2 : ℕ) + 1 : ℝ) - 1 / ((3 : ℕ) + 1 : ℝ)) +
        (0 + 0 + 0 + (c ^ 2 / 720 - 1 / 120))) /
        (1 / ((2 : ℕ) + 1 : ℝ)) ^ 2) = c ^ 2 / 80 + 1 / 20 := by norm_num; ring
    rwa [hval] at hdiv
  refine hpoly_lim.congr' (eventually_nhdsWithin_of_forall fun L (hL : 0 < L) => ?_)
  dsimp only
  symm
  have hLne : L ≠ 0 := ne_of_gt hL
  have hJ2ne : Jmom 2 c L ≠ 0 := ne_of_gt (Jmom_pos 2 c L)
  have hexp : Real.exp (-c ^ 2 / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hxf : xf c L = Jmom 1 c L / Jmom 2 c L := by
    unfold xf
    rw [Imom_eq_Jmom 1 c hL, Imom_eq_Jmom 2 c hL]
    field_simp; ring
  have hyf : yf c L = Real.exp (c * L - L ^ 2 / 2) / Jmom 2 c L := by
    unfold yf phi
    rw [Imom_eq_Jmom 2 c hL]
    have hsplit : -(L - c) ^ 2 / 2 = -c ^ 2 / 2 + (c * L - L ^ 2 / 2) := by ring
    rw [hsplit, Real.exp_add]
    field_simp
  have huf : uf c L = L ^ 2 * (1 - Jmom 3 c L / Jmom 2 c L) := by
    unfold uf Zf
    rw [Imom_eq_Jmom 2 c hL, Imom_eq_Jmom 3 c hL]
    field_simp; ring
  have hJ1_eq : Jmom 1 c L = 1 / 2 + c / 3 * L + (c ^ 2 - 1) / 8 * L ^ 2 + r1 L * L ^ 2 := by
    simp only [r1]; field_simp; ring
  have hJ2_eq : Jmom 2 c L = 1 / 3 + c / 4 * L + (c ^ 2 - 1) / 10 * L ^ 2 + r2 L * L ^ 2 := by
    simp only [r2]; field_simp; ring
  have hE_eq : Real.exp (c * L - L ^ 2 / 2) = 1 + c * L + (c ^ 2 - 1) / 2 * L ^ 2 + re L * L ^ 2 := by
    simp only [re]; field_simp; ring
  unfold W1 tf
  rw [hxf, hyf, huf]
  have hrewrite :
      ((Jmom 1 c L / Jmom 2 c L - 1) * (L ^ 2 * (1 - Jmom 3 c L / Jmom 2 c L)) +
       (Jmom 1 c L / Jmom 2 c L - 1) * (Real.exp (c * L - L ^ 2 / 2) / Jmom 2 c L) +
       2 * (Jmom 1 c L / Jmom 2 c L - 1) ^ 2 - 2 * (Jmom 1 c L / Jmom 2 c L - 1) - 1) / L ^ 2 =
      ((Jmom 1 c L - Jmom 2 c L) * (Jmom 2 c L - Jmom 3 c L) +
        ((Jmom 1 c L - Jmom 2 c L) * (Real.exp (c * L - L ^ 2 / 2) + 2 * Jmom 1 c L - 4 * Jmom 2 c L) -
          Jmom 2 c L ^ 2) / L ^ 2) / Jmom 2 c L ^ 2 := by
    field_simp; ring
  rw [hrewrite]
  congr 1
  congr 1
  rw [hJ1_eq, hJ2_eq, hE_eq]
  field_simp
  ring

lemma tendsto_M1_div_L3 (c : ℝ) :
    Tendsto (fun L => M1 c L / L ^ 3) (𝓝[>] 0) (𝓝 (-c / 80)) := by
  set q1 := fun L => (Jmom 1 c L - (1 / 2 + c / 3 * L)) / L
  set q2 := fun L => (Jmom 2 c L - (1 / 3 + c / 4 * L)) / L
  set q3 := fun L => (Jmom 3 c L - (1 / 4 + c / 5 * L)) / L
  have hq1 : Tendsto q1 (𝓝[>] 0) (𝓝 0) :=
    (tendsto_Jmom_rem1 1 c).congr fun L => by simp only [q1]; norm_num
  have hq2 : Tendsto q2 (𝓝[>] 0) (𝓝 0) :=
    (tendsto_Jmom_rem1 2 c).congr fun L => by simp only [q2]; norm_num
  have hq3 : Tendsto q3 (𝓝[>] 0) (𝓝 0) :=
    (tendsto_Jmom_rem1 3 c).congr fun L => by simp only [q3]; norm_num
  have hj2 := tendsto_Jmom_zero 2 c
  have hid : Tendsto (fun L : ℝ => L) (𝓝[>] 0) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun L =>
      (q1 L * (-1 / 6 - 3 * c / 20 * L + (q2 L - 2 * q3 L) * L) +
       q2 L * (3 / 4 + 8 * c / 15 * L + q3 L * L) +
       q3 L * (-2 / 3 - 5 * c / 12 * L) +
       (-c / 720)) / Jmom 2 c L ^ 2)
      (𝓝[>] 0) (𝓝 (-c / 80)) := by
    have h1 : Tendsto (fun L => q1 L * (-1 / 6 - 3 * c / 20 * L + (q2 L - 2 * q3 L) * L))
        (𝓝[>] 0) (𝓝 0) := by
      have hf : Tendsto (fun L => -1 / 6 - 3 * c / 20 * L + (q2 L - 2 * q3 L) * L)
          (𝓝[>] 0) (𝓝 (-1 / 6)) := by
        simpa using (tendsto_const_nhds.sub (hid.const_mul (3 * c / 20))).add
          ((hq2.sub (hq3.const_mul 2)).mul hid)
      simpa using hq1.mul hf
    have h2 : Tendsto (fun L => q2 L * (3 / 4 + 8 * c / 15 * L + q3 L * L))
        (𝓝[>] 0) (𝓝 0) := by
      have hf : Tendsto (fun L => 3 / 4 + 8 * c / 15 * L + q3 L * L)
          (𝓝[>] 0) (𝓝 (3 / 4)) := by
        simpa using (tendsto_const_nhds.add (hid.const_mul (8 * c / 15))).add (hq3.mul hid)
      simpa using hq2.mul hf
    have h3 : Tendsto (fun L => q3 L * (-2 / 3 - 5 * c / 12 * L)) (𝓝[>] 0) (𝓝 0) := by
      have hf : Tendsto (fun L => -2 / 3 - 5 * c / 12 * L) (𝓝[>] 0) (𝓝 (-2 / 3)) := by
        simpa using tendsto_const_nhds.sub (hid.const_mul (5 * c / 12))
      simpa using hq3.mul hf
    have h4 : Tendsto (fun _ : ℝ => -c / 720) (𝓝[>] 0) (𝓝 (-c / 720)) := tendsto_const_nhds
    have hnum := ((h1.add h2).add h3).add h4
    have hdne : (1 / ((2 : ℕ) + 1 : ℝ)) ^ 2 ≠ 0 := by norm_num
    have hdiv := hnum.div (hj2.pow 2) hdne
    have hval : (0 + 0 + 0 + -c / 720) / (1 / ((2 : ℕ) + 1 : ℝ)) ^ 2 = -c / 80 := by
      norm_num; ring
    rwa [hval] at hdiv
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun L (hL : 0 < L) => ?_)
  dsimp only
  symm
  have hLne : L ≠ 0 := ne_of_gt hL
  have hJ2ne : Jmom 2 c L ≠ 0 := ne_of_gt (Jmom_pos 2 c L)
  have hexp : Real.exp (-c ^ 2 / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hxf : xf c L = Jmom 1 c L / Jmom 2 c L := by
    unfold xf; rw [Imom_eq_Jmom 1 c hL, Imom_eq_Jmom 2 c hL]; field_simp; ring
  have hZf : Zf c L = L ^ 2 * (Jmom 3 c L / Jmom 2 c L) := by
    unfold Zf; rw [Imom_eq_Jmom 2 c hL, Imom_eq_Jmom 3 c hL]; field_simp; ring
  have hM : M1 c L / L ^ 3 =
      ((Jmom 1 c L * Jmom 2 c L - 2 * Jmom 1 c L * Jmom 3 c L + Jmom 2 c L * Jmom 3 c L) / L) /
        Jmom 2 c L ^ 2 := by
    unfold M1 gf uf tf
    rw [hxf, hZf]
    field_simp; ring
  rw [hM]
  have hJ1_eq : Jmom 1 c L = 1 / 2 + c / 3 * L + q1 L * L := by simp only [q1]; field_simp; ring
  have hJ2_eq : Jmom 2 c L = 1 / 3 + c / 4 * L + q2 L * L := by simp only [q2]; field_simp; ring
  have hJ3_eq : Jmom 3 c L = 1 / 4 + c / 5 * L + q3 L * L := by simp only [q3]; field_simp; ring
  congr 1
  rw [hJ1_eq, hJ2_eq, hJ3_eq]
  field_simp
  ring

lemma tendsto_yf_zero (c : ℝ) : Tendsto (yf c) (𝓝[>] 0) (𝓝 3) := by
  have he : Tendsto (fun L : ℝ => Real.exp (c * L - L ^ 2 / 2)) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous (fun L : ℝ => Real.exp (c * L - L ^ 2 / 2)) := by fun_prop
    have hct : Tendsto (fun L : ℝ => Real.exp (c * L - L ^ 2 / 2)) (𝓝 (0 : ℝ))
        (𝓝 (Real.exp (c * 0 - 0 ^ 2 / 2))) := hc.continuousAt.tendsto
    simp only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_zero, Real.exp_zero] at hct
    exact hct.mono_left nhdsWithin_le_nhds
  have hj2 := tendsto_Jmom_zero 2 c
  have hlim : Tendsto (fun L => Real.exp (c * L - L ^ 2 / 2) / Jmom 2 c L) (𝓝[>] 0) (𝓝 3) := by
    have hdiv := he.div hj2 (by norm_num : (1 / ((2 : ℕ) + 1 : ℝ)) ≠ 0)
    have hval : (1 : ℝ) / (1 / ((2 : ℕ) + 1 : ℝ)) = 3 := by norm_num
    rwa [hval] at hdiv
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun L (hL : 0 < L) => ?_)
  symm
  unfold yf phi
  rw [Imom_eq_Jmom 2 c hL]
  have hsplit : -(L - c) ^ 2 / 2 = -c ^ 2 / 2 + (c * L - L ^ 2 / 2) := by ring
  rw [hsplit, Real.exp_add]
  have hexp : Real.exp (-c ^ 2 / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hLne : L ≠ 0 := ne_of_gt hL
  have hJ2ne : Jmom 2 c L ≠ 0 := ne_of_gt (Jmom_pos 2 c L)
  field_simp

lemma tendsto_D1_div_L6 (c : ℝ) :
    Tendsto (fun L => D1 c L / L ^ 6) (𝓝[>] 0) (𝓝 (3 / 1600)) := by
  have hW := tendsto_W1_div_L2 c
  have hC := tendsto_Cfun_div_L4 c
  have hy := tendsto_yf_zero c
  have hM := tendsto_M1_div_L3 c
  have hlim : Tendsto (fun L => (W1 c L / L ^ 2) * (Cfun c L / L ^ 4) -
      yf c L * (M1 c L / L ^ 3) ^ 2) (𝓝[>] 0) (𝓝 (3 / 1600)) := by
    have hsub := (hW.mul hC).sub (hy.mul (hM.pow 2))
    have hval : (c ^ 2 / 80 + 1 / 20) * (3 / 80) - 3 * (-c / 80) ^ 2 = 3 / 1600 := by ring
    rwa [hval] at hsub
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun L (hL : 0 < L) => ?_)
  dsimp only
  symm
  unfold D1
  have hLne : L ≠ 0 := ne_of_gt hL
  field_simp

/-! #### Pure algebraic identities for the two ODE barriers -/

/-- Pure 3-variable polynomial core of the `t D₁ = 0` barrier identity. -/
lemma alg_tD1_core (t r s : ℝ) :
    let D := (s - 1) * ((t + 1) * s - t)
    let U := (2 * t - 1) * (t + 1) * s - (2 * t ^ 2 - 2 * t - 1)
    let Dty := (s * (1 - r) - 1) * t * U - (2 * t ^ 2 - 2 * t - 1) * D
    let Dg := r * t * U
    let DM := (1 - r) * t * U
    let Ddt := (t + 1) * D - Dty
    let D2tdy := Dty * ((1 - 2 * t) * D - U)
    let D2tdu := D * Dg + ((2 * t + 1) * D - Dty) * U
    let D2tdg := (2 * t * D - Dty) * Dg + t * U * Dty
    let D2tdW := t * Ddt * U + t * D2tdu + Ddt * Dty + t * D2tdy + (4 * t ^ 2 - 2 * t) * D * Ddt
    let D2tdM := t * Ddt * U + t * D2tdu - D2tdg
    let D3tdC0 := 2 * Dg * D2tdg + (D2tdu + (4 * t ^ 2 + t) * D * Ddt) * Dg +
      (U + (2 * t ^ 2 + t - 1) * D) * D2tdg + (D2tdu * (t + 1) + t * U * Ddt) * (Dty - (t + 1) * D) +
      U * (t + 1) * (Ddt * Dty + t * D2tdy - t * D * Ddt)
    Dty * D2tdW + s ^ 2 * D3tdC0 - s * DM * (Ddt * Dty + t * D2tdy) - 2 * s * Dty * D2tdM =
      t ^ 2 * Dty * ((s - 1) ^ 2 * (t * U + Dg + 2 * U) + 6 * t * D) := by
  intro D U Dty Dg DM Ddt D2tdy D2tdu D2tdg D2tdW D2tdM D3tdC0
  -- Collect coefficients of powers of r (at most cubic in r) so each `ring` is tiny!
  set q := 1 - r
  have hr : r = 1 - q := by simp only [q]; ring
  set A0 := -t * U - (2 * t ^ 2 - 2 * t - 1) * D
  set A1 := s * t * U
  have hDty : Dty = A0 + A1 * q := by simp only [Dty, A0, A1, q]; ring
  have hDg : Dg = t * U - t * U * q := by simp only [Dg, q]; ring
  have hDM : DM = t * U * q := by simp only [DM, q]; ring
  set B0 := (t + 1) * D - A0
  have hDdt : Ddt = B0 - A1 * q := by rw [show Ddt = (t + 1) * D - Dty from rfl, hDty]; simp only [B0]; ring
  set E0 := (1 - 2 * t) * D - U
  have hD2tdy : D2tdy = A0 * E0 + A1 * E0 * q := by rw [show D2tdy = Dty * E0 from rfl, hDty]; ring
  set F0 := D * (t * U) + ((2 * t + 1) * D - A0) * U
  set F1 := -(D * (t * U) + A1 * U)
  have hD2tdu : D2tdu = F0 + F1 * q := by
    rw [show D2tdu = D * Dg + ((2 * t + 1) * D - Dty) * U from rfl, hDg, hDty]; simp only [F0, F1]; ring
  set G0 := (2 * t * D - A0) * (t * U) + t * U * A0
  set G1 := (-(2 * t * D - A0) + (t * U - A1)) * (t * U) + t * U * A1 - t * U * (t * U)
  set G2 := A1 * (t * U)
  have hD2tdg : D2tdg = G0 + G1 * q + G2 * q ^ 2 := by
    rw [show D2tdg = (2 * t * D - Dty) * Dg + t * U * Dty from rfl, hDty, hDg]; simp only [G0, G1, G2]; ring
  have hW_poly : D2tdW =
      (t * B0 * U + t * F0 + B0 * A0 + t * A0 * E0 + (4 * t ^ 2 - 2 * t) * D * B0) +
      (-t * A1 * U + t * F1 + (B0 * A1 - A1 * A0) + t * A1 * E0 - (4 * t ^ 2 - 2 * t) * D * A1) * q +
      (-A1 * A1) * q ^ 2 := by
    rw [show D2tdW = t * Ddt * U + t * D2tdu + Ddt * Dty + t * D2tdy + (4 * t ^ 2 - 2 * t) * D * Ddt from rfl,
      hDdt, hD2tdu, hDty, hD2tdy]; ring
  have hM_poly : D2tdM =
      (t * B0 * U + t * F0 - G0) + (-t * A1 * U + t * F1 - G1) * q + (-G2) * q ^ 2 := by
    rw [show D2tdM = t * Ddt * U + t * D2tdu - D2tdg from rfl, hDdt, hD2tdu, hD2tdg]; ring
  have hLHS : Dty * D2tdW + s ^ 2 * D3tdC0 - s * DM * (Ddt * Dty + t * D2tdy) - 2 * s * Dty * D2tdM -
      t ^ 2 * Dty * ((s - 1) ^ 2 * (t * U + Dg + 2 * U) + 6 * t * D) =
      (A0 * (t * B0 * U + t * F0 + B0 * A0 + t * A0 * E0 + (4 * t ^ 2 - 2 * t) * D * B0) +
        s ^ 2 * (2 * (t * U) * G0 + (F0 + (4 * t ^ 2 + t) * D * B0) * (t * U) +
          (U + (2 * t ^ 2 + t - 1) * D) * G0 + (F0 * (t + 1) + t * U * B0) * (A0 - (t + 1) * D) +
          U * (t + 1) * (B0 * A0 + t * A0 * E0 - t * D * B0)) -
        2 * s * A0 * (t * B0 * U + t * F0 - G0) -
        t ^ 2 * A0 * ((s - 1) ^ 2 * (2 * t * U + 2 * U) + 6 * t * D)) +
      (A1 * (t * B0 * U + t * F0 + B0 * A0 + t * A0 * E0 + (4 * t ^ 2 - 2 * t) * D * B0) +
        A0 * (-t * A1 * U + t * F1 + (B0 * A1 - A1 * A0) + t * A1 * E0 - (4 * t ^ 2 - 2 * t) * D * A1) +
        s ^ 2 * (2 * (t * U) * G1 - 2 * (t * U) * G0 +
          (F1 - (4 * t ^ 2 + t) * D * A1) * (t * U) - (F0 + (4 * t ^ 2 + t) * D * B0) * (t * U) +
          (U + (2 * t ^ 2 + t - 1) * D) * G1 +
          (F1 * (t + 1) - t * U * A1) * (A0 - (t + 1) * D) + (F0 * (t + 1) + t * U * B0) * A1 +
          U * (t + 1) * (B0 * A1 - A1 * A0 + t * A1 * E0 + t * D * A1)) -
        s * (t * U) * (B0 * A0 + t * A0 * E0) -
        2 * s * (A1 * (t * B0 * U + t * F0 - G0) + A0 * (-t * A1 * U + t * F1 - G1)) -
        t ^ 2 * (A1 * ((s - 1) ^ 2 * (2 * t * U + 2 * U) + 6 * t * D) +
          A0 * (-(s - 1) ^ 2 * (t * U)))) * q +
      (A0 * (-A1 * A1) +
        A1 * (-t * A1 * U + t * F1 + (B0 * A1 - A1 * A0) + t * A1 * E0 - (4 * t ^ 2 - 2 * t) * D * A1) +
        s ^ 2 * (2 * (t * U) * G2 - 2 * (t * U) * G1 -
          (F1 - (4 * t ^ 2 + t) * D * A1) * (t * U) +
          (U + (2 * t ^ 2 + t - 1) * D) * G2 +
          (F1 * (t + 1) - t * U * A1) * A1 +
          U * (t + 1) * (-A1 * A1)) -
        s * (t * U) * (B0 * A1 - A1 * A0 + t * A1 * E0) -
        2 * s * (A1 * (-t * A1 * U + t * F1 - G1) + A0 * (-G2)) -
        t ^ 2 * (A1 * (-(s - 1) ^ 2 * (t * U)))) * q ^ 2 +
      (A1 * (-A1 * A1) + s ^ 2 * (-2 * (t * U) * G2) - s * (t * U) * (-A1 * A1) -
        2 * s * (A1 * (-G2))) * q ^ 3 := by
    rw [show D3tdC0 = 2 * Dg * D2tdg + (D2tdu + (4 * t ^ 2 + t) * D * Ddt) * Dg +
      (U + (2 * t ^ 2 + t - 1) * D) * D2tdg + (D2tdu * (t + 1) + t * U * Ddt) * (Dty - (t + 1) * D) +
      U * (t + 1) * (Ddt * Dty + t * D2tdy - t * D * Ddt) from rfl,
      hW_poly, hM_poly, hDty, hDg, hDM, hDdt, hD2tdy, hD2tdu, hD2tdg]
    ring
  have hc0 : A0 * (t * B0 * U + t * F0 + B0 * A0 + t * A0 * E0 + (4 * t ^ 2 - 2 * t) * D * B0) +
      s ^ 2 * (2 * (t * U) * G0 + (F0 + (4 * t ^ 2 + t) * D * B0) * (t * U) +
        (U + (2 * t ^ 2 + t - 1) * D) * G0 + (F0 * (t + 1) + t * U * B0) * (A0 - (t + 1) * D) +
        U * (t + 1) * (B0 * A0 + t * A0 * E0 - t * D * B0)) -
      2 * s * A0 * (t * B0 * U + t * F0 - G0) -
      t ^ 2 * A0 * ((s - 1) ^ 2 * (2 * t * U + 2 * U) + 6 * t * D) = 0 := by
    simp only [G0, F0, E0, B0, A0, D, U]; ring
  have hc1 : A1 * (t * B0 * U + t * F0 + B0 * A0 + t * A0 * E0 + (4 * t ^ 2 - 2 * t) * D * B0) +
      A0 * (-t * A1 * U + t * F1 + (B0 * A1 - A1 * A0) + t * A1 * E0 - (4 * t ^ 2 - 2 * t) * D * A1) +
      s ^ 2 * (2 * (t * U) * G1 - 2 * (t * U) * G0 +
        (F1 - (4 * t ^ 2 + t) * D * A1) * (t * U) - (F0 + (4 * t ^ 2 + t) * D * B0) * (t * U) +
        (U + (2 * t ^ 2 + t - 1) * D) * G1 +
        (F1 * (t + 1) - t * U * A1) * (A0 - (t + 1) * D) + (F0 * (t + 1) + t * U * B0) * A1 +
        U * (t + 1) * (B0 * A1 - A1 * A0 + t * A1 * E0 + t * D * A1)) -
      s * (t * U) * (B0 * A0 + t * A0 * E0) -
      2 * s * (A1 * (t * B0 * U + t * F0 - G0) + A0 * (-t * A1 * U + t * F1 - G1)) -
      t ^ 2 * (A1 * ((s - 1) ^ 2 * (2 * t * U + 2 * U) + 6 * t * D) +
        A0 * (-(s - 1) ^ 2 * (t * U))) = 0 := by
    simp only [G1, G0, F1, F0, E0, B0, A1, A0, D, U]; ring
  have hc2 : A0 * (-A1 * A1) +
      A1 * (-t * A1 * U + t * F1 + (B0 * A1 - A1 * A0) + t * A1 * E0 - (4 * t ^ 2 - 2 * t) * D * A1) +
      s ^ 2 * (2 * (t * U) * G2 - 2 * (t * U) * G1 -
        (F1 - (4 * t ^ 2 + t) * D * A1) * (t * U) +
        (U + (2 * t ^ 2 + t - 1) * D) * G2 +
        (F1 * (t + 1) - t * U * A1) * A1 +
        U * (t + 1) * (-A1 * A1)) -
      s * (t * U) * (B0 * A1 - A1 * A0 + t * A1 * E0) -
      2 * s * (A1 * (-t * A1 * U + t * F1 - G1) + A0 * (-G2)) -
      t ^ 2 * (A1 * (-(s - 1) ^ 2 * (t * U))) = 0 := by
    simp only [G2, G1, F1, E0, B0, A1, A0, D, U]; ring
  have hc3 : A1 * (-A1 * A1) + s ^ 2 * (-2 * (t * U) * G2) - s * (t * U) * (-A1 * A1) -
      2 * s * (A1 * (-G2)) = 0 := by
    simp only [G2, A1]; ring
  rw [hc0, hc1, hc2, hc3] at hLHS
  linarith only [hLHS]

lemma alg_tD1_scale_P {t y u g s r : ℝ} (ht : t ≠ 0)
    (hDu : ((s - 1) * ((t + 1) * s - t)) * u = (2 * t - 1) * (t + 1) * s - (2 * t ^ 2 - 2 * t - 1))
    (hg : g = r * t * u)
    (hty : t * y = (s * (1 - r) - 1) * t * u - (2 * t ^ 2 - 2 * t - 1)) :
    let D := (s - 1) * ((t + 1) * s - t)
    let U := (2 * t - 1) * (t + 1) * s - (2 * t ^ 2 - 2 * t - 1)
    let M := t * u - g
    let dt := t + 1 - t * y
    let dy := y * (1 - u - 2 * t)
    let du := (g + (2 * t + 1 - t * y) * u) / t
    let dg := (2 - y) * g + t * u * y
    let dW := dt * u + t * du + dt * y + t * dy + 4 * t * dt - 2 * dt
    let dM := dt * u + t * du - dg
    let dC0 := 2 * g * dg + (du + 4 * t * dt + dt) * g + (u + 2 * t ^ 2 + t - 1) * dg +
      (du * (t + 1) + u * dt) * (t * y - t - 1) + u * (t + 1) * (dt * y + t * dy - dt)
    let P := t * y * dW + s ^ 2 * dC0 - s * M * (dt * y + t * dy) - 2 * s * t * y * dM
    let Dty := (s * (1 - r) - 1) * t * U - (2 * t ^ 2 - 2 * t - 1) * D
    let Dg := r * t * U
    let DM := (1 - r) * t * U
    let Ddt := (t + 1) * D - Dty
    let D2tdy := Dty * ((1 - 2 * t) * D - U)
    let D2tdu := D * Dg + ((2 * t + 1) * D - Dty) * U
    let D2tdg := (2 * t * D - Dty) * Dg + t * U * Dty
    let D2tdW := t * Ddt * U + t * D2tdu + Ddt * Dty + t * D2tdy + (4 * t ^ 2 - 2 * t) * D * Ddt
    let D2tdM := t * Ddt * U + t * D2tdu - D2tdg
    let D3tdC0 := 2 * Dg * D2tdg + (D2tdu + (4 * t ^ 2 + t) * D * Ddt) * Dg +
      (U + (2 * t ^ 2 + t - 1) * D) * D2tdg + (D2tdu * (t + 1) + t * U * Ddt) * (Dty - (t + 1) * D) +
      U * (t + 1) * (Ddt * Dty + t * D2tdy - t * D * Ddt)
    D ^ 3 * (t * P) =
      Dty * D2tdW + s ^ 2 * D3tdC0 - s * DM * (Ddt * Dty + t * D2tdy) - 2 * s * Dty * D2tdM := by
  intro D U M dt dy du dg dW dM dC0 P Dty Dg DM Ddt D2tdy D2tdu D2tdg D2tdW D2tdM D3tdC0
  set ty := t * y
  have hM_eq : M = (1 - r) * t * u := by simp only [M]; rw [hg]; ring
  have htdy : t * dy = ty * (1 - u - 2 * t) := by simp only [dy, ty]; ring
  have htdu : t * du = g + (2 * t + 1 - ty) * u := by simp only [du, ty]; field_simp
  have htdg : t * dg = (2 * t - ty) * g + t * u * ty := by simp only [dg, ty]; ring
  have htdW : t * dW = t * dt * u + t * (t * du) + dt * ty + t * (t * dy) +
      4 * t ^ 2 * dt - 2 * t * dt := by simp only [dW, ty]; ring
  have htdM : t * dM = t * dt * u + t * (t * du) - t * dg := by simp only [dM]; ring
  have htdC0 : t * dC0 = 2 * g * (t * dg) + (t * du + 4 * t ^ 2 * dt + t * dt) * g +
      (u + 2 * t ^ 2 + t - 1) * (t * dg) + ((t * du) * (t + 1) + t * u * dt) * (ty - t - 1) +
      u * (t + 1) * (dt * ty + t * (t * dy) - t * dt) := by simp only [dC0, ty]; ring
  have htP : t * P = ty * (t * dW) + s ^ 2 * (t * dC0) - s * M * (dt * ty + t * (t * dy)) -
      2 * s * ty * (t * dM) := by simp only [P, ty]; ring
  have hDty : D * ty = Dty := by
    rw [show ty = (s * (1 - r) - 1) * t * u - (2 * t ^ 2 - 2 * t - 1) from hty]
    simp only [Dty]; linear_combination (s * (1 - r) - 1) * t * hDu
  have hDg : D * g = Dg := by rw [hg]; simp only [Dg]; linear_combination r * t * hDu
  have hDM : D * M = DM := by rw [hM_eq]; simp only [DM]; linear_combination (1 - r) * t * hDu
  have hDdt : D * dt = Ddt := by simp only [dt, Ddt]; rw [show t * y = ty from rfl]; linear_combination -hDty
  have hD2tdy : D ^ 2 * (t * dy) = D2tdy := by
    rw [htdy]; simp only [D2tdy]; linear_combination ((1 - 2 * t) * D - U) * hDty - D * ty * hDu
  have hD2tdu : D ^ 2 * (t * du) = D2tdu := by
    rw [htdu]; simp only [D2tdu]; linear_combination D * hDg + ((2 * t + 1) * D - Dty) * hDu - D * u * hDty
  have hD2tdg : D ^ 2 * (t * dg) = D2tdg := by
    rw [htdg]; simp only [D2tdg]
    linear_combination (2 * t * D - Dty) * hDg + (t * U - D * g) * hDty + t * D * ty * hDu
  have hD2tdW : D ^ 2 * (t * dW) = D2tdW := by
    rw [htdW]; simp only [D2tdW]
    linear_combination t * U * hDdt + t * D * dt * hDu + t * hD2tdu + Dty * hDdt +
      D * dt * hDty + t * hD2tdy + (4 * t ^ 2 - 2 * t) * D * hDdt
  have hD2tdM : D ^ 2 * (t * dM) = D2tdM := by
    rw [htdM]; simp only [D2tdM]
    linear_combination t * U * hDdt + t * D * dt * hDu + t * hD2tdu - hD2tdg
  have hD3tdC0 : D ^ 3 * (t * dC0) = D3tdC0 := by
    rw [htdC0]; simp only [D3tdC0]
    linear_combination 2 * D2tdg * hDg + 2 * D * g * hD2tdg +
      Dg * hD2tdu + D ^ 2 * (t * du) * hDg +
      (4 * t ^ 2 + t) * D * Dg * hDdt + (4 * t ^ 2 + t) * D ^ 2 * dt * hDg +
      (U + (2 * t ^ 2 + t - 1) * D) * hD2tdg + D ^ 2 * (t * dg) * hDu +
      (Dty - (t + 1) * D) * ((t + 1) * hD2tdu + t * U * hDdt + t * D * dt * hDu) +
      (D ^ 2 * (t * du) * (t + 1) + t * (D * u) * (D * dt)) * hDty +
      (t + 1) * (Ddt * Dty + t * D2tdy - t * D * Ddt) * hDu +
      (t + 1) * (D * u) * (Dty * hDdt + D * dt * hDty + t * hD2tdy - t * D * hDdt)
  rw [htP]
  linear_combination D2tdW * hDty + D * ty * hD2tdW + s ^ 2 * hD3tdC0 -
    s * (Ddt * Dty + t * D2tdy) * hDM -
    s * (D * M) * (Dty * hDdt + D * dt * hDty + t * hD2tdy) -
    2 * s * D2tdM * hDty - 2 * s * (D * ty) * hD2tdM

/-- Pure polynomial barrier identity on `t D₁ = 0` (kept free of `Imom` definitions for instant `ring`). -/
lemma alg_tD1_barrier {t y u g s r : ℝ} (ht : t ≠ 0) (_hr1 : 1 - r ≠ 0) (_hs : s ≠ 0)
    (hDne : (s - 1) * ((t + 1) * s - t) ≠ 0)
    (hg : g = r * t * u)
    (hty : t * y = (s * (1 - r) - 1) * t * u - (2 * t ^ 2 - 2 * t - 1))
    (hu : u = ((2 * t - 1) * (t + 1) * s - (2 * t ^ 2 - 2 * t - 1)) / ((s - 1) * ((t + 1) * s - t))) :
    let W := t * u + t * y + 2 * t ^ 2 - 2 * t - 1
    let M := t * u - g
    let C0 := g ^ 2 + (u + 2 * t ^ 2 + t - 1) * g + u * (t + 1) * (t * y - t - 1)
    let dt := t + 1 - t * y
    let dy := y * (1 - u - 2 * t)
    let du := (g + (2 * t + 1 - t * y) * u) / t
    let dg := (2 - y) * g + t * u * y
    let dW := dt * u + t * du + dt * y + t * dy + 4 * t * dt - 2 * dt
    let dM := dt * u + t * du - dg
    let dC0 := 2 * g * dg + (du + 4 * t * dt + dt) * g + (u + 2 * t ^ 2 + t - 1) * dg +
      (du * (t + 1) + u * dt) * (t * y - t - 1) + u * (t + 1) * (dt * y + t * dy - dt)
    let dtD := dW * C0 + W * dC0 - (dt * y + t * dy) * M ^ 2 - t * y * (2 * M * dM)
    t * dtD * (W * ((s - 1) * ((t + 1) * s - t))) =
      t ^ 3 * y * M ^ 2 * ((s - 1) ^ 2 * (t * u + g + 2 * u) + 6 * t) := by
  intro W M C0 dt dy du dg dW dM dC0 dtD
  set D := (s - 1) * ((t + 1) * s - t)
  set U := (2 * t - 1) * (t + 1) * s - (2 * t ^ 2 - 2 * t - 1)
  have hDu : D * u = U := by rw [hu, mul_div_cancel₀ _ hDne]
  have hM_eq : M = (1 - r) * t * u := by simp only [M]; rw [hg]; ring
  have hW_eq : W = s * M := by simp only [W]; rw [hM_eq, hty]; ring
  have hWC0 : W * C0 = t * y * M ^ 2 := by
    have hD_zero : D * u - U = 0 := sub_eq_zero.mpr hDu
    have hfact : W * C0 - t * y * M ^ 2 = t ^ 2 * (1 - r) ^ 2 * u ^ 2 * (D * u - U) := by
      rw [hW_eq, hM_eq]; simp only [C0]; rw [hg, hty]; simp only [D, U]; ring
    linarith [show t ^ 2 * (1 - r) ^ 2 * u ^ 2 * (D * u - U) = 0 by rw [hD_zero, mul_zero]]
  set P := t * y * dW + s ^ 2 * dC0 - s * M * (dt * y + t * dy) - 2 * s * t * y * dM
  have hWdtD : W * dtD = M ^ 2 * P := by
    have h1 : W * dtD = dW * (W * C0) + W ^ 2 * dC0 - W * (dt * y + t * dy) * M ^ 2 -
        2 * W * t * y * M * dM := by simp only [dtD]; ring
    rw [h1, hWC0, hW_eq]; simp only [P]; ring
  have hLHS : t * dtD * (W * D) = M ^ 2 * (t * P * D) := by
    have : t * dtD * (W * D) = t * (W * dtD) * D := by ring
    rw [this, hWdtD]; ring
  rw [hLHS]
  suffices hP : t * P * D = t ^ 3 * y * ((s - 1) ^ 2 * (t * u + g + 2 * u) + 6 * t) by
    rw [hP]; ring
  have hD2ne : D ^ 2 ≠ 0 := pow_ne_zero 2 hDne
  apply mul_left_cancel₀ hD2ne
  set Dty := (s * (1 - r) - 1) * t * U - (2 * t ^ 2 - 2 * t - 1) * D
  set Dg := r * t * U
  have hDty : D * (t * y) = Dty := by
    rw [hty]; simp only [Dty]; linear_combination (s * (1 - r) - 1) * t * hDu
  have hDg : D * g = Dg := by rw [hg]; simp only [Dg]; linear_combination r * t * hDu
  have hD3tP := alg_tD1_scale_P ht hDu hg hty
  have hcore := alg_tD1_core t r s
  have hRHS : D ^ 2 * (t ^ 3 * y * ((s - 1) ^ 2 * (t * u + g + 2 * u) + 6 * t)) =
      t ^ 2 * Dty * ((s - 1) ^ 2 * (t * U + Dg + 2 * U) + 6 * t * D) := by
    linear_combination t ^ 2 * ((s - 1) ^ 2 * (t * U + Dg + 2 * U) + 6 * t * D) * hDty +
      t ^ 2 * (D * (t * y)) * ((s - 1) ^ 2 * ((t + 2) * hDu + hDg))
  calc D ^ 2 * (t * P * D) = D ^ 3 * (t * P) := by ring
    _ = _ := hD3tP
    _ = t ^ 2 * Dty * ((s - 1) ^ 2 * (t * U + Dg + 2 * U) + 6 * t * D) := hcore
    _ = D ^ 2 * (t ^ 3 * y * ((s - 1) ^ 2 * (t * u + g + 2 * u) + 6 * t)) := hRHS.symm

/-! #### Proofs of `W₁ > 0` (Lemma 1.4) and `D₁ > 0` (Lemma 1.5) via ODE barriers -/

lemma W1_pos (c : ℝ) {L : ℝ} (hL : 0 < L) : 0 < W1 c L := by
  refine pos_of_ode_barrier ?_ ?_ ?_ L hL
  · intro x hx
    unfold W1
    have hdt := (hasDerivAt_tf c hx).differentiableAt
    have hdu := (hasDerivAt_uf c hx).differentiableAt
    have hdy := (hasDerivAt_yf c hx).differentiableAt
    fun_prop
  · have hlim := tendsto_W1_div_L2 c
    have hpos : (0 : ℝ) < c ^ 2 / 80 + 1 / 20 := by positivity
    have hev := hlim.eventually (Ioi_mem_nhds hpos)
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhdsWithin_iff.mp hev
    refine ⟨ε, hεpos, fun x ⟨hxp, hxlt⟩ => ?_⟩
    have h1 : 0 < W1 c x / x ^ 2 :=
      hε ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hxp]; exact hxlt, hxp⟩
    have := mul_pos h1 (sq_pos_of_pos hxp)
    rwa [div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hxp))] at this
  · intro x hx hW0
    have ht := tf_pos c hx
    have hu := uf_pos c hx
    have hg := gf_pos c hx
    have hdt := hasDerivAt_tf c hx
    have hdu := hasDerivAt_uf c hx
    have hdy := hasDerivAt_yf c hx
    have hdW : HasDerivAt (W1 c)
        ((tf c x + 1 - tf c x * yf c x) / x * uf c x +
         tf c x * ((gf c x + (2 * tf c x + 1 - tf c x * yf c x) * uf c x) / (tf c x * x)) +
         ((tf c x + 1 - tf c x * yf c x) / x * yf c x +
          tf c x * (yf c x * (1 - uf c x - 2 * tf c x) / x)) +
         (2 * (2 * tf c x * ((tf c x + 1 - tf c x * yf c x) / x))) -
         2 * ((tf c x + 1 - tf c x * yf c x) / x)) x := by
      have hsq : HasDerivAt (fun z => tf c z ^ 2)
          (2 * tf c x * ((tf c x + 1 - tf c x * yf c x) / x)) x :=
        hasDerivAt_congr_val (hdt.pow 2) (by ring)
      have hW_eq : (fun z => tf c z * uf c z + tf c z * yf c z + 2 * tf c z ^ 2 - 2 * tf c z - 1) = W1 c := rfl
      rw [← hW_eq]
      exact ((((hdt.mul hdu).add (hdt.mul hdy)).add (hsq.const_mul 2)).sub (hdt.const_mul 2)).sub_const 1
    rw [hdW.deriv]
    have hxne : x ≠ 0 := ne_of_gt hx
    have htne : tf c x ≠ 0 := ne_of_gt ht
    have hty : tf c x * yf c x = 1 + 2 * tf c x - 2 * tf c x ^ 2 - tf c x * uf c x := by
      unfold W1 at hW0; linarith
    have hy_eq : yf c x = (1 + 2 * tf c x - 2 * tf c x ^ 2 - tf c x * uf c x) / tf c x :=
      eq_div_of_mul_eq htne (by linarith)
    have hid :
        ((tf c x + 1 - tf c x * yf c x) / x * uf c x +
         tf c x * ((gf c x + (2 * tf c x + 1 - tf c x * yf c x) * uf c x) / (tf c x * x)) +
         ((tf c x + 1 - tf c x * yf c x) / x * yf c x +
          tf c x * (yf c x * (1 - uf c x - 2 * tf c x) / x)) +
         (2 * (2 * tf c x * ((tf c x + 1 - tf c x * yf c x) / x))) -
         2 * ((tf c x + 1 - tf c x * yf c x) / x)) =
        (gf c x + tf c x * (2 * (uf c x + 2 * tf c x - 1) ^ 2 + uf c x)) / x := by
      rw [hy_eq]
      field_simp
      ring
    rw [hid]
    exact div_pos (by positivity) hx

lemma tD1_pos (c : ℝ) {L : ℝ} (hL : 0 < L) : 0 < tD1 c L := by
  refine pos_of_ode_barrier ?_ ?_ ?_ L hL
  · intro x hx
    unfold tD1 W1 tC M1
    have hdt := (hasDerivAt_tf c hx).differentiableAt
    have hdu := (hasDerivAt_uf c hx).differentiableAt
    have hdy := (hasDerivAt_yf c hx).differentiableAt
    have hdg := (hasDerivAt_gf c hx).differentiableAt
    fun_prop
  · have hlim := tendsto_D1_div_L6 c
    have hev := hlim.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 3 / 1600))
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhdsWithin_iff.mp hev
    refine ⟨ε, hεpos, fun x ⟨hxp, hxlt⟩ => ?_⟩
    have h1 : 0 < D1 c x / x ^ 6 :=
      hε ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hxp]; exact hxlt, hxp⟩
    have hD1 : 0 < D1 c x := by
      have := mul_pos h1 (pow_pos hxp 6)
      rwa [div_mul_cancel₀ _ (ne_of_gt (pow_pos hxp 6))] at this
    rw [tD1_eq_tf_mul_D1 c hxp]
    exact mul_pos (tf_pos c hxp) hD1
  · intro x hx htD0
    set t := tf c x
    set y := yf c x
    set u := uf c x
    set g := gf c x
    have ht : 0 < t := tf_pos c hx
    have hy : 0 < y := yf_pos c hx
    have hu : 0 < u := uf_pos c hx
    have hg : 0 < g := gf_pos c hx
    have hW : 0 < W1 c x := W1_pos c hx
    have hMne : M1 c x ≠ 0 := by
      intro hM0
      have hgtu : g = t * u := by
        have : t * u - g = 0 := hM0
        linarith
      have htC_eq : tC c x = u * (t + 1) * W1 c x := by
        change g ^ 2 + (u + 2 * t ^ 2 + t - 1) * g + u * (t + 1) * (t * y - t - 1) =
          u * (t + 1) * (t * u + t * y + 2 * t ^ 2 - 2 * t - 1)
        rw [hgtu]; ring
      have htD_eq : tD1 c x = W1 c x * (u * (t + 1) * W1 c x) := by
        unfold tD1; rw [hM0, htC_eq]; ring
      have : 0 < tD1 c x := by rw [htD_eq]; positivity
      linarith
    set dt := t + 1 - t * y
    set dy := y * (1 - u - 2 * t)
    set du := (g + (2 * t + 1 - t * y) * u) / t
    set dg := (2 - y) * g + t * u * y
    have hdt : HasDerivAt (tf c) (dt / x) x := hasDerivAt_tf c hx
    have hdy : HasDerivAt (yf c) (dy / x) x := hasDerivAt_yf c hx
    have hdu : HasDerivAt (uf c) (du / x) x :=
      hasDerivAt_congr_val (hasDerivAt_uf c hx) (by simp only [du]; ring)
    have hdg : HasDerivAt (gf c) (dg / x) x := hasDerivAt_gf c hx
    set dW := dt * u + t * du + dt * y + t * dy + 4 * t * dt - 2 * dt
    set dM := dt * u + t * du - dg
    set dtC := 2 * g * dg + (du + 4 * t * dt + dt) * g + (u + 2 * t ^ 2 + t - 1) * dg +
      (du * (t + 1) + u * dt) * (t * y - t - 1) + u * (t + 1) * (dt * y + t * dy - dt)
    set dtD := dW * tC c x + W1 c x * dtC -
      (dt * y + t * dy) * M1 c x ^ 2 - t * y * (2 * M1 c x * dM)
    have hdW : HasDerivAt (W1 c) (dW / x) x := by
      have hfun : (fun z => tf c z * uf c z + tf c z * yf c z + 2 * tf c z ^ 2 - 2 * tf c z - 1) = W1 c := rfl
      rw [← hfun]
      have h1 := (((hdt.mul hdu).add (hdt.mul hdy)).add ((hdt.pow 2).const_mul 2)).sub (hdt.const_mul 2)
      exact hasDerivAt_congr_val (h1.sub_const 1) (by
        change dt / x * u + t * (du / x) + (dt / x * y + t * (dy / x)) +
          2 * (2 * t ^ (2 - 1) * (dt / x)) - 2 * (dt / x) = dW / x
        simp only [dW]; ring)
    have hdM : HasDerivAt (M1 c) (dM / x) x := by
      have hfun : (fun z => tf c z * uf c z - gf c z) = M1 c := rfl
      rw [← hfun]
      exact hasDerivAt_congr_val ((hdt.mul hdu).sub hdg) (by
        change dt / x * u + t * (du / x) - dg / x = dM / x
        simp only [dM]; ring)
    have hdtC : HasDerivAt (tC c) (dtC / x) x := by
      have hfun : (fun z => gf c z ^ 2 + (uf c z + 2 * tf c z ^ 2 + tf c z - 1) * gf c z +
          uf c z * (tf c z + 1) * (tf c z * yf c z - tf c z - 1)) = tC c := rfl
      rw [← hfun]
      have h1 := hdg.pow 2
      have h2 := ((hdu.add ((hdt.pow 2).const_mul 2)).add hdt).sub_const 1
      have h3 := h2.mul hdg
      have h4 := (hdu.mul (hdt.add_const 1)).mul (((hdt.mul hdy).sub hdt).sub_const 1)
      exact hasDerivAt_congr_val ((h1.add h3).add h4) (by
        change 2 * g ^ (2 - 1) * (dg / x) +
          ((du / x + 2 * (2 * t ^ (2 - 1) * (dt / x)) + dt / x) * g +
            (u + 2 * t ^ 2 + t - 1) * (dg / x)) +
          ((du / x * (t + 1) + u * (dt / x)) * (t * y - t - 1) +
            u * (t + 1) * (dt / x * y + t * (dy / x) - dt / x)) = dtC / x
        simp only [dtC]; ring)
    have hdtD : HasDerivAt (tD1 c) (dtD / x) x := by
      have hfun : (fun z => W1 c z * tC c z - tf c z * yf c z * M1 c z ^ 2) = tD1 c := rfl
      rw [← hfun]
      have h1 := hdW.mul hdtC
      have h2 := (hdt.mul hdy).mul (hdM.pow 2)
      exact hasDerivAt_congr_val (h1.sub h2) (by
        change dW / x * tC c x + W1 c x * (dtC / x) -
          ((dt / x * y + t * (dy / x)) * M1 c x ^ 2 +
            t * y * (2 * M1 c x ^ (2 - 1) * (dM / x))) = dtD / x
        simp only [dtD]; ring)
    rw [hdtD.deriv]
    set s := W1 c x / M1 c x
    set r := g / (t * u)
    have hr_pos : 0 < r := div_pos hg (mul_pos ht hu)
    have h1mr : 1 - r ≠ 0 := by
      intro h0
      have hr1 : r = 1 := by linarith
      have : g = t * u := by
        have := congrArg (· * (t * u)) hr1
        rw [div_mul_cancel₀ _ (ne_of_gt (mul_pos ht hu)), one_mul] at this
        exact this
      exact hMne (by change t * u - g = 0; linarith)
    have hg_eq : g = r * t * u := by
      simp only [r]; field_simp
    have hM_eq : M1 c x = (1 - r) * t * u := by
      change t * u - g = (1 - r) * t * u
      rw [hg_eq]; ring
    have hW_eq : W1 c x = s * (1 - r) * t * u := by
      have : W1 c x = s * M1 c x := by simp only [s]; field_simp
      rw [this, hM_eq]; ring
    have hty_eq : t * y = (s * (1 - r) - 1) * t * u - (2 * t ^ 2 - 2 * t - 1) := by
      have : W1 c x = t * u + t * y + 2 * t ^ 2 - 2 * t - 1 := rfl
      linarith
    set D := (s - 1) * ((t + 1) * s - t)
    set U := (2 * t - 1) * (t + 1) * s - (2 * t ^ 2 - 2 * t - 1)
    have hsne : s ≠ 0 := div_ne_zero (ne_of_gt hW) hMne
    have hDuU : D * u = U := by
      have hfact : tD1 c x = t ^ 2 * (1 - r) ^ 2 * u ^ 2 * (D * u - U) := by
        have htC_val : tC c x = g ^ 2 + (u + 2 * t ^ 2 + t - 1) * g + u * (t + 1) * (t * y - t - 1) := rfl
        have htD_val : tD1 c x = W1 c x * tC c x - t * y * M1 c x ^ 2 := rfl
        rw [htD_val, htC_val, hW_eq, hM_eq, hg_eq, hty_eq]
        dsimp only [D, U]
        ring
      rw [hfact] at htD0
      have hcoeff : t ^ 2 * (1 - r) ^ 2 * u ^ 2 ≠ 0 :=
        mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (ne_of_gt ht))
          (pow_ne_zero 2 h1mr)) (pow_ne_zero 2 (ne_of_gt hu))
      have h0 : D * u - U = 0 := (mul_eq_zero.mp htD0).resolve_left hcoeff
      linarith
    have hD_pos : 0 < D := by
      have hUid : U = (t + 1) ^ 2 * (1 - s) + 3 * t * ((t + 1) * s - t) := by
        simp only [U]; ring
      by_contra hDle
      push Not at hDle
      have h1ms : 0 ≤ 1 - s := by
        by_contra hlt; push Not at hlt
        have hs2 : 0 < (t + 1) * s - t := by nlinarith
        have : 0 < D := mul_pos (by linarith) hs2
        linarith
      have hts : 0 ≤ (t + 1) * s - t := by
        by_contra hlt; push Not at hlt
        have : 0 < D := mul_pos_of_neg_of_neg (by nlinarith) hlt
        linarith
      have hUpos : 0 < U := by
        rw [hUid]
        by_cases h0 : 1 - s = 0
        · have hs1 : s = 1 := by linarith
          rw [h0, hs1]; nlinarith
        · have : 0 < 1 - s := lt_of_le_of_ne h1ms (Ne.symm h0)
          nlinarith
      have : U ≤ 0 := by rw [← hDuU]; exact mul_nonpos_of_nonpos_of_nonneg hDle (le_of_lt hu)
      linarith
    have hu_eq : u = U / D := eq_div_of_mul_eq (ne_of_gt hD_pos) (by linarith)
    have hbar := alg_tD1_barrier (ne_of_gt ht) h1mr hsne (ne_of_gt hD_pos) hg_eq hty_eq hu_eq
    have hrhs_pos : 0 < t ^ 3 * y * M1 c x ^ 2 * ((s - 1) ^ 2 * (t * u + g + 2 * u) + 6 * t) := by
      have hM2 : 0 < M1 c x ^ 2 := sq_pos_of_ne_zero hMne
      positivity
    have hprod_pos : 0 < t * dtD * (W1 c x * D) := by
      simpa only [W1, M1, tC, dtD, dW, dM, dtC, dt, dy, du, dg, D] using
        hbar.symm ▸ hrhs_pos
    have hWD_pos : 0 < W1 c x * D := mul_pos hW hD_pos
    have ht_dtD_pos : 0 < t * dtD := pos_of_mul_pos_left hprod_pos (le_of_lt hWD_pos)
    have hdtD_pos : 0 < dtD := pos_of_mul_pos_right ht_dtD_pos (le_of_lt ht)
    exact div_pos hdtD_pos hx

lemma D1_pos (c : ℝ) {L : ℝ} (hL : 0 < L) : 0 < D1 c L := by
  have h1 := tD1_pos c hL
  rw [tD1_eq_tf_mul_D1 c hL] at h1
  exact pos_of_mul_pos_right h1 (le_of_lt (tf_pos c hL))

lemma Cfun_pos (c : ℝ) {L : ℝ} (hL : 0 < L) : 0 < Cfun c L := by
  have hD := D1_pos c hL
  have hW := W1_pos c hL
  have hy := yf_pos c hL
  unfold D1 at hD
  nlinarith [sq_nonneg (M1 c L)]

/-! #### Joint convexity of `Gfun(w, c)` along every line segment in `(0, ∞) × ℝ` -/

/-- Derivative of `τ ↦ Imom k (c₀ + τ dc) (1 / (w₀ + τ dw))` at any `τ₀` with `w₀ + τ₀ dw > 0`. -/
lemma hasDerivAt_Imom_line (k : ℕ) (w₀ dw c₀ dc τ₀ : ℝ) (hw : 0 < w₀ + τ₀ * dw) :
    let w := fun τ : ℝ => w₀ + τ * dw
    let c := fun τ : ℝ => c₀ + τ * dc
    let L := fun τ : ℝ => 1 / w τ
    HasDerivAt (fun τ => Imom k (c τ) (L τ))
      ((-dw / w τ₀ ^ 2) * L τ₀ ^ k * phi (c τ₀) (L τ₀) +
        dc * (Imom (k + 1) (c τ₀) (L τ₀) - c τ₀ * Imom k (c τ₀) (L τ₀))) τ₀ := by
  intro w c L
  have hw_cont : Continuous w := by simp only [w]; fun_prop
  have hev : ∀ᶠ τ in 𝓝 τ₀, w τ₀ / 2 < w τ :=
    hw_cont.continuousAt.eventually (Ioi_mem_nhds (by linarith))
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  set sset : Set ℝ := Metric.ball τ₀ (δ / 2)
  have hsset_mem : sset ∈ 𝓝 τ₀ := Metric.ball_mem_nhds τ₀ (half_pos hδpos)
  have hw_on : ∀ τ ∈ sset, w τ₀ / 2 < w τ := fun τ hτ =>
    hδ (lt_trans hτ (half_lt_self hδpos))
  set F : ℝ → ℝ → ℝ := fun τ s => s ^ k * Real.exp (-(L τ * s - c τ) ^ 2 / 2)
  set L' : ℝ → ℝ := fun τ => -dw / w τ ^ 2
  set F' : ℝ → ℝ → ℝ := fun τ s =>
    s ^ k * (-(L τ * s - c τ) * (L' τ * s - dc)) * Real.exp (-(L τ * s - c τ) ^ 2 / 2)
  have hL_bd : ∀ τ ∈ sset, |L τ| ≤ 2 / w τ₀ := by
    intro τ hτ
    have hwp : 0 < w τ := lt_trans (half_pos hw) (hw_on τ hτ)
    simp only [L]
    rw [abs_of_pos (div_pos one_pos hwp)]
    have h1 := one_div_le_one_div_of_le (half_pos hw) (le_of_lt (hw_on τ hτ))
    linarith [show 1 / (w τ₀ / 2) = 2 / w τ₀ by field_simp]
  have hL'_bd : ∀ τ ∈ sset, |L' τ| ≤ 4 * |dw| / w τ₀ ^ 2 := by
    intro τ hτ
    have hwp : 0 < w τ := lt_trans (half_pos hw) (hw_on τ hτ)
    simp only [L']
    rw [abs_div, abs_neg, abs_of_pos (sq_pos_of_pos hwp)]
    have hsq : (w τ₀ / 2) ^ 2 ≤ w τ ^ 2 := by nlinarith [hw_on τ hτ]
    have h1 := div_le_div_of_nonneg_left (abs_nonneg dw) (sq_pos_of_pos (half_pos hw)) hsq
    calc |dw| / w τ ^ 2 ≤ |dw| / (w τ₀ / 2) ^ 2 := h1
      _ = 4 * |dw| / w τ₀ ^ 2 := by field_simp; ring
  have hc_bd : ∀ τ ∈ sset, |c τ| ≤ |c₀| + (|τ₀| + δ / 2) * |dc| := by
    intro τ hτ
    have hτd : |τ - τ₀| < δ / 2 := by simpa [sset, Metric.mem_ball, Real.dist_eq] using hτ
    have hτ_le : |τ| ≤ |τ₀| + δ / 2 := by linarith [abs_sub_abs_le_abs_sub τ τ₀]
    simp only [c]
    calc |c₀ + τ * dc| ≤ |c₀| + |τ * dc| := abs_add_le _ _
      _ = |c₀| + |τ| * |dc| := by rw [abs_mul]
      _ ≤ |c₀| + (|τ₀| + δ / 2) * |dc| := by nlinarith [abs_nonneg dc]
  set B_arg : ℝ := 2 / w τ₀ + (|c₀| + (|τ₀| + δ / 2) * |dc|)
  set B_der : ℝ := 4 * |dw| / w τ₀ ^ 2 + |dc|
  set C_bd : ℝ := B_arg * B_der
  have hF_deriv : ∀ τ ∈ sset, ∀ s : ℝ, HasDerivAt (fun x => F x s) (F' τ s) τ := by
    intro τ hτ s
    have hwp : 0 < w τ := lt_trans (half_pos hw) (hw_on τ hτ)
    have hdw_at : HasDerivAt w dw τ :=
      hasDerivAt_congr_val (((hasDerivAt_id τ).mul_const dw).const_add w₀) (one_mul dw)
    have hdL_at : HasDerivAt L (L' τ) τ :=
      hasDerivAt_congr_val ((hasDerivAt_const τ (1 : ℝ)).div hdw_at (ne_of_gt hwp))
        (by simp only [L']; ring)
    have hdc_at : HasDerivAt c dc τ :=
      hasDerivAt_congr_val (((hasDerivAt_id τ).mul_const dc).const_add c₀) (one_mul dc)
    have hlin : HasDerivAt (fun x => L x * s - c x) (L' τ * s - dc) τ :=
      (hdL_at.mul_const s).sub hdc_at
    have hexp_arg : HasDerivAt (fun x => -(L x * s - c x) ^ 2 / 2)
        (-(L τ * s - c τ) * (L' τ * s - dc)) τ :=
      hasDerivAt_congr_val (((hlin.pow 2).neg).div_const 2) (by ring)
    simp only [F, F']
    exact hasDerivAt_congr_val ((hexp_arg.exp).const_mul (s ^ k)) (by ring)
  have hleib := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1) (F := F) (F' := F') (bound := fun _ => C_bd)
    (s := sset) (x₀ := τ₀) hsset_mem
    (Filter.eventually_of_mem hsset_mem fun τ _ => by
      have hcF : Continuous (F τ) := by simp only [F]; fun_prop
      exact hcF.aestronglyMeasurable)
    (by
      have hcF : Continuous (F τ₀) := by simp only [F]; fun_prop
      exact hcF.intervalIntegrable 0 1)
    (by
      have hcF' : Continuous (F' τ₀) := by simp only [F']; fun_prop
      exact hcF'.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun s hs => by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      intro τ hτ
      rw [Real.norm_eq_abs]
      simp only [F']
      have hs0 : 0 ≤ s := le_of_lt hs.1
      have hs1 : s ≤ 1 := hs.2
      have hsk : |s ^ k| ≤ 1 := by
        rw [abs_of_nonneg (pow_nonneg hs0 k)]; exact pow_le_one₀ hs0 hs1
      have hexp_le : Real.exp (-(L τ * s - c τ) ^ 2 / 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (L τ * s - c τ)])
      have harg_le : |L τ * s - c τ| ≤ B_arg := by
        calc |L τ * s - c τ| ≤ |L τ * s| + |c τ| := abs_sub _ _
          _ = |L τ| * s + |c τ| := by rw [abs_mul, abs_of_nonneg hs0]
          _ ≤ |L τ| * 1 + |c τ| := by nlinarith [abs_nonneg (L τ)]
          _ ≤ B_arg := by simp only [B_arg]; linarith [hL_bd τ hτ, hc_bd τ hτ]
      have hder_le : |L' τ * s - dc| ≤ B_der := by
        calc |L' τ * s - dc| ≤ |L' τ * s| + |dc| := abs_sub _ _
          _ = |L' τ| * s + |dc| := by rw [abs_mul, abs_of_nonneg hs0]
          _ ≤ |L' τ| * 1 + |dc| := by nlinarith [abs_nonneg (L' τ)]
          _ ≤ B_der := by simp only [B_der]; linarith [hL'_bd τ hτ]
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
      have hB_nn : 0 ≤ B_arg := by positivity
      calc |s ^ k| * (|L τ * s - c τ| * |L' τ * s - dc|) * Real.exp (-(L τ * s - c τ) ^ 2 / 2)
          ≤ 1 * (B_arg * B_der) * 1 := by
            have h1 := mul_le_mul harg_le hder_le (abs_nonneg _) hB_nn
            have h2 := mul_le_mul hsk h1 (by positivity) zero_le_one
            exact mul_le_mul h2 hexp_le (le_of_lt (Real.exp_pos _)) (by positivity)
        _ = C_bd := by simp only [C_bd]; ring)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun s _ τ hτ => hF_deriv τ hτ s)
  have hI_deriv := hleib.2
  have hImom_eq : ∀ τ ∈ sset, Imom k (c τ) (L τ) = L τ ^ (k + 1) * ∫ s in (0 : ℝ)..1, F τ s := by
    intro τ hτ
    have hwp : 0 < w τ := lt_trans (half_pos hw) (hw_on τ hτ)
    have hLp : 0 < L τ := div_pos one_pos hwp
    unfold Imom phi
    have hcomp := intervalIntegral.integral_comp_mul_left
      (fun u : ℝ => u ^ k * Real.exp (-(u - c τ) ^ 2 / 2)) (ne_of_gt hLp) (a := (0 : ℝ)) (b := 1)
    simp only [mul_zero, mul_one, smul_eq_mul] at hcomp
    have hinner : (∫ s in (0 : ℝ)..1, (L τ * s) ^ k * Real.exp (-(L τ * s - c τ) ^ 2 / 2)) =
        L τ ^ k * ∫ s in (0 : ℝ)..1, F τ s := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [F]; rw [mul_pow]; ring
    rw [hinner] at hcomp
    have hLne : L τ ≠ 0 := ne_of_gt hLp
    have hmul := congrArg (L τ * ·) hcomp
    have hcancel : L τ * ((L τ)⁻¹ * ∫ u in (0 : ℝ)..L τ, u ^ k * Real.exp (-(u - c τ) ^ 2 / 2)) =
        ∫ u in (0 : ℝ)..L τ, u ^ k * Real.exp (-(u - c τ) ^ 2 / 2) := by field_simp
    rw [hcancel] at hmul
    rw [← hmul]; ring
  have hdL0 : HasDerivAt L (L' τ₀) τ₀ := by
    have hdw_at : HasDerivAt w dw τ₀ :=
      hasDerivAt_congr_val (((hasDerivAt_id τ₀).mul_const dw).const_add w₀) (one_mul dw)
    exact hasDerivAt_congr_val ((hasDerivAt_const τ₀ (1 : ℝ)).div hdw_at (ne_of_gt hw))
      (by simp only [L']; ring)
  have hprod_deriv := (hdL0.pow (k + 1)).mul hI_deriv
  have hmain := hprod_deriv.congr_of_eventuallyEq (Filter.eventually_of_mem hsset_mem hImom_eq)
  have hLp0 : 0 < L τ₀ := div_pos one_pos hw
  have hLne0 : L τ₀ ≠ 0 := ne_of_gt hLp0
  have hInt_eq : ∀ m : ℕ, L τ₀ ^ (m + 1) * ∫ s in (0 : ℝ)..1, s ^ m * Real.exp (-(L τ₀ * s - c τ₀) ^ 2 / 2) =
      Imom m (c τ₀) (L τ₀) := by
    intro m
    unfold Imom phi
    have hcomp := intervalIntegral.integral_comp_mul_left
      (fun u : ℝ => u ^ m * Real.exp (-(u - c τ₀) ^ 2 / 2)) hLne0 (a := (0 : ℝ)) (b := 1)
    simp only [mul_zero, mul_one, smul_eq_mul] at hcomp
    have hinner : (∫ s in (0 : ℝ)..1, (L τ₀ * s) ^ m * Real.exp (-(L τ₀ * s - c τ₀) ^ 2 / 2)) =
        L τ₀ ^ m * ∫ s in (0 : ℝ)..1, s ^ m * Real.exp (-(L τ₀ * s - c τ₀) ^ 2 / 2) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [mul_pow]; ring
    rw [hinner] at hcomp
    have hmul := congrArg (L τ₀ * ·) hcomp
    have hcancel : L τ₀ * ((L τ₀)⁻¹ * ∫ u in (0 : ℝ)..L τ₀, u ^ m * Real.exp (-(u - c τ₀) ^ 2 / 2)) =
        ∫ u in (0 : ℝ)..L τ₀, u ^ m * Real.exp (-(u - c τ₀) ^ 2 / 2) := by field_simp
    rw [hcancel] at hmul
    rw [← hmul]; ring
  have hF'_split :
      L τ₀ ^ (k + 1) * ∫ s in (0 : ℝ)..1, F' τ₀ s =
      -L' τ₀ / L τ₀ * (Imom (k + 2) (c τ₀) (L τ₀) - c τ₀ * Imom (k + 1) (c τ₀) (L τ₀)) +
      dc * (Imom (k + 1) (c τ₀) (L τ₀) - c τ₀ * Imom k (c τ₀) (L τ₀)) := by
    set g := fun m s => s ^ m * Real.exp (-(L τ₀ * s - c τ₀) ^ 2 / 2)
    have hg_int : ∀ m, IntervalIntegrable (g m) volume 0 1 := fun m =>
      (by simp only [g]; fun_prop : Continuous (g m)).intervalIntegrable 0 1
    have hrew : (fun s => F' τ₀ s) = fun s =>
        (-L' τ₀ * L τ₀) * g (k + 2) s + (L' τ₀ * c τ₀ + dc * L τ₀) * g (k + 1) s +
          (-dc * c τ₀) * g k s := by
      ext s; simp only [F', g]; ring
    rw [hrew,
      intervalIntegral.integral_add
        (((hg_int (k + 2)).const_mul _).add ((hg_int (k + 1)).const_mul _))
        ((hg_int k).const_mul _),
      intervalIntegral.integral_add ((hg_int (k + 2)).const_mul _) ((hg_int (k + 1)).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    have h0 := hInt_eq k
    have h1 := hInt_eq (k + 1)
    have h2 := hInt_eq (k + 2)
    simp only [g]
    have hr0 : ∫ s in (0 : ℝ)..1, s ^ k * Real.exp (-(L τ₀ * s - c τ₀) ^ 2 / 2) =
        Imom k (c τ₀) (L τ₀) / L τ₀ ^ (k + 1) := eq_div_of_mul_eq (pow_ne_zero _ hLne0) (by linarith)
    have hr1 : ∫ s in (0 : ℝ)..1, s ^ (k + 1) * Real.exp (-(L τ₀ * s - c τ₀) ^ 2 / 2) =
        Imom (k + 1) (c τ₀) (L τ₀) / L τ₀ ^ (k + 2) := eq_div_of_mul_eq (pow_ne_zero _ hLne0) (by linarith)
    have hr2 : ∫ s in (0 : ℝ)..1, s ^ (k + 2) * Real.exp (-(L τ₀ * s - c τ₀) ^ 2 / 2) =
        Imom (k + 2) (c τ₀) (L τ₀) / L τ₀ ^ (k + 3) := eq_div_of_mul_eq (pow_ne_zero _ hLne0) (by linarith)
    rw [hr0, hr1, hr2]
    field_simp
    ring
  have hibp := Imom_ibp k (c τ₀) (L τ₀)
  refine hasDerivAt_congr_val hmain ?_
  have h0 := hInt_eq k
  simp only [F, L'] at hF'_split ⊢
  rw [Nat.cast_add, Nat.cast_one]
  have hr0 : ∫ s in (0 : ℝ)..1, s ^ k * Real.exp (-(L τ₀ * s - c τ₀) ^ 2 / 2) =
      Imom k (c τ₀) (L τ₀) / L τ₀ ^ (k + 1) := eq_div_of_mul_eq (pow_ne_zero _ hLne0) (by linarith)
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  rw [hF'_split, hr0, hibp]
  have hwne0 : w τ₀ ≠ 0 := ne_of_gt hw
  field_simp
  ring

/-- First and second directional derivatives of `Gfun` along any affine line in `(0, ∞) × ℝ`. -/
lemma hasDerivAt_Gfun_line (w₀ dw c₀ dc τ₀ : ℝ) (hw : 0 < w₀ + τ₀ * dw) :
    let w := fun τ : ℝ => w₀ + τ * dw
    let c := fun τ : ℝ => c₀ + τ * dc
    let L := fun τ : ℝ => 1 / w τ
    HasDerivAt (fun τ => Gfun (w τ) (c τ))
      (dw * (yf (c τ₀) (L τ₀) * tf (c τ₀) (L τ₀)) +
        dc * (-gf (c τ₀) (L τ₀) / L τ₀ ^ 2)) τ₀ := by
  intro w c L
  have hLp : 0 < L τ₀ := div_pos one_pos hw
  have hI2 : Imom 2 (c τ₀) (L τ₀) ≠ 0 := ne_of_gt (Imom_pos 2 (c τ₀) hLp)
  have hd1 : HasDerivAt (fun τ => Imom 1 (c τ) (L τ))
      (-dw / w τ₀ ^ 2 * L τ₀ ^ 1 * phi (c τ₀) (L τ₀) +
        dc * (Imom 2 (c τ₀) (L τ₀) - c τ₀ * Imom 1 (c τ₀) (L τ₀))) τ₀ :=
    hasDerivAt_Imom_line 1 w₀ dw c₀ dc τ₀ hw
  have hd2 : HasDerivAt (fun τ => Imom 2 (c τ) (L τ))
      (-dw / w τ₀ ^ 2 * L τ₀ ^ 2 * phi (c τ₀) (L τ₀) +
        dc * (Imom 3 (c τ₀) (L τ₀) - c τ₀ * Imom 2 (c τ₀) (L τ₀))) τ₀ :=
    hasDerivAt_Imom_line 2 w₀ dw c₀ dc τ₀ hw
  have hdG : HasDerivAt (fun τ => Gfun (w τ) (c τ)) _ τ₀ := hd1.div hd2 hI2
  refine hasDerivAt_congr_val hdG ?_
  unfold gf Zf tf xf yf
  have hwne : w τ₀ ≠ 0 := ne_of_gt hw
  have hLne : L τ₀ ≠ 0 := ne_of_gt hLp
  have hwinv : w τ₀ = 1 / L τ₀ := by simp only [L]; field_simp
  rw [hwinv]
  field_simp
  ring

/-- Pure algebraic identity for the second directional derivative of `Gfun`. -/
lemma alg_Gfun_hessian {L c dw dc I1 I2 I3 I4 phiL : ℝ} (hL : L ≠ 0) (hI2 : I2 ≠ 0)
    (hibp1 : I3 - c * I2 = 2 * I1 - L ^ 2 * phiL)
    (hibp2 : I4 - c * I3 = 3 * I2 - L ^ 3 * phiL) :
    let w := 1 / L
    let dL := -dw / w ^ 2
    let dphi := -(L - c) * (dL - dc) * phiL
    let dI1 := dL * L ^ 1 * phiL + dc * (I2 - c * I1)
    let dI2 := dL * L ^ 2 * phiL + dc * (I3 - c * I2)
    let dI3 := dL * L ^ 3 * phiL + dc * (I4 - c * I3)
    let y := L ^ 3 * phiL / I2
    let x := L * I1 / I2
    let t := x - 1
    let Z := L * I3 / I2
    let u := L ^ 2 - Z
    let g := x * Z - L ^ 2
    let W := t * u + t * y + 2 * t ^ 2 - 2 * t - 1
    let M := t * u - g
    let C := L ^ 3 * (2 * I1 * I3 ^ 2 - I2 ^ 2 * I3 - I1 * I2 * I4) / I2 ^ 3
    let dy := ((3 * L ^ 2 * dL * phiL + L ^ 3 * dphi) * I2 - L ^ 3 * phiL * dI2) / I2 ^ 2
    let dt := ((dL * I1 + L * dI1) * I2 - L * I1 * dI2) / I2 ^ 2
    let dg_div := -(((dI1 * I3 + I1 * dI3) * I2 ^ 2 - I1 * I3 * (2 * I2 * dI2)) / (I2 ^ 2) ^ 2)
    dw * (dy * t + y * dt) + dc * dg_div =
      dw ^ 2 * (L * y * W) + 2 * dw * dc * (y * M / L) + dc ^ 2 * (C / L ^ 3) := by
  intro w dL dphi dI1 dI2 dI3 y x t Z u g W M C dy dt dg_div
  have hI4 : I4 = c * I3 + 3 * I2 - L ^ 3 * phiL := by linarith
  have hI3 : I3 = c * I2 + 2 * I1 - L ^ 2 * phiL := by linarith
  simp only [dy, dt, dg_div, W, M, C, g, u, Z, t, x, y, dI1, dI2, dI3, dphi, dL, w]
  rw [hI4, hI3]
  field_simp
  ring

lemma hasDerivAt_Gfun_line_deriv (w₀ dw c₀ dc τ₀ : ℝ) (hw : 0 < w₀ + τ₀ * dw) :
    let w := fun τ : ℝ => w₀ + τ * dw
    let c := fun τ : ℝ => c₀ + τ * dc
    let L := fun τ : ℝ => 1 / w τ
    HasDerivAt (fun τ => dw * (yf (c τ) (L τ) * tf (c τ) (L τ)) +
        dc * (-gf (c τ) (L τ) / L τ ^ 2))
      (dw ^ 2 * (L τ₀ * yf (c τ₀) (L τ₀) * W1 (c τ₀) (L τ₀)) +
        2 * dw * dc * (yf (c τ₀) (L τ₀) * M1 (c τ₀) (L τ₀) / L τ₀) +
        dc ^ 2 * (Cfun (c τ₀) (L τ₀) / L τ₀ ^ 3)) τ₀ := by
  intro w c L
  have hLp : 0 < L τ₀ := div_pos one_pos hw
  have hLne : L τ₀ ≠ 0 := ne_of_gt hLp
  have hwne : w τ₀ ≠ 0 := ne_of_gt hw
  have hI2 : Imom 2 (c τ₀) (L τ₀) ≠ 0 := ne_of_gt (Imom_pos 2 (c τ₀) hLp)
  have hd1 : HasDerivAt (fun τ => Imom 1 (c τ) (L τ))
      (-dw / w τ₀ ^ 2 * L τ₀ ^ 1 * phi (c τ₀) (L τ₀) +
        dc * (Imom 2 (c τ₀) (L τ₀) - c τ₀ * Imom 1 (c τ₀) (L τ₀))) τ₀ :=
    hasDerivAt_Imom_line 1 w₀ dw c₀ dc τ₀ hw
  have hd2 : HasDerivAt (fun τ => Imom 2 (c τ) (L τ))
      (-dw / w τ₀ ^ 2 * L τ₀ ^ 2 * phi (c τ₀) (L τ₀) +
        dc * (Imom 3 (c τ₀) (L τ₀) - c τ₀ * Imom 2 (c τ₀) (L τ₀))) τ₀ :=
    hasDerivAt_Imom_line 2 w₀ dw c₀ dc τ₀ hw
  have hd3 : HasDerivAt (fun τ => Imom 3 (c τ) (L τ))
      (-dw / w τ₀ ^ 2 * L τ₀ ^ 3 * phi (c τ₀) (L τ₀) +
        dc * (Imom 4 (c τ₀) (L τ₀) - c τ₀ * Imom 3 (c τ₀) (L τ₀))) τ₀ :=
    hasDerivAt_Imom_line 3 w₀ dw c₀ dc τ₀ hw
  have hdw_at : HasDerivAt w dw τ₀ :=
    hasDerivAt_congr_val (((hasDerivAt_id τ₀).mul_const dw).const_add w₀) (one_mul dw)
  have hdL : HasDerivAt L (-dw / w τ₀ ^ 2) τ₀ :=
    hasDerivAt_congr_val ((hasDerivAt_const τ₀ (1 : ℝ)).div hdw_at hwne) (by ring)
  have hdc : HasDerivAt c dc τ₀ :=
    hasDerivAt_congr_val (((hasDerivAt_id τ₀).mul_const dc).const_add c₀) (one_mul dc)
  have hdphi : HasDerivAt (fun τ => phi (c τ) (L τ))
      (-(L τ₀ - c τ₀) * (-dw / w τ₀ ^ 2 - dc) * phi (c τ₀) (L τ₀)) τ₀ := by
    unfold phi
    have hsub := hdL.sub hdc
    have hexp_arg : HasDerivAt (fun τ => -(L τ - c τ) ^ 2 / 2)
        (-(L τ₀ - c τ₀) * (-dw / w τ₀ ^ 2 - dc)) τ₀ :=
      hasDerivAt_congr_val (((hsub.pow 2).neg).div_const 2) (by simp only [Pi.sub_apply]; ring)
    exact hasDerivAt_congr_val hexp_arg.exp (by ring)
  have hdyf := ((hdL.pow 3).mul hdphi).div hd2 hI2
  have hdtf := ((hdL.mul hd1).div hd2 hI2).sub_const 1
  have hdgf_div := by
    have heq : ∀ᶠ τ in 𝓝 τ₀, -gf (c τ) (L τ) / L τ ^ 2 =
        1 - Imom 1 (c τ) (L τ) * Imom 3 (c τ) (L τ) / Imom 2 (c τ) (L τ) ^ 2 := by
      have hev : ∀ᶠ τ in 𝓝 τ₀, 0 < w τ :=
        (by simp only [w]; fun_prop : Continuous w).continuousAt.eventually (Ioi_mem_nhds hw)
      refine hev.mono fun τ hτ => ?_
      have hLτ : L τ ≠ 0 := ne_of_gt (div_pos one_pos hτ)
      have hI2τ : Imom 2 (c τ) (L τ) ≠ 0 := ne_of_gt (Imom_pos 2 (c τ) (div_pos one_pos hτ))
      unfold gf xf Zf
      field_simp; ring
    have hd_rhs := (hasDerivAt_const τ₀ (1 : ℝ)).sub
      ((hd1.mul hd3).div (hd2.pow 2) (pow_ne_zero 2 hI2))
    exact hd_rhs.congr_of_eventuallyEq heq
  have hsum := ((hdyf.mul hdtf).const_mul dw).add (hdgf_div.const_mul dc)
  refine hasDerivAt_congr_val hsum ?_
  have hC := Cfun_eq_moments (c τ₀) hLp
  have hibp1 := Imom_ibp 1 (c τ₀) (L τ₀)
  have hibp2 := Imom_ibp 2 (c τ₀) (L τ₀)
  norm_num at hibp1 hibp2
  have halg := alg_Gfun_hessian hLne hI2 hibp1 hibp2 (dw := dw) (dc := dc)
  rw [hC]
  have hw_eq : w τ₀ = 1 / L τ₀ := by simp only [L]; field_simp
  unfold W1 M1 gf uf Zf tf xf yf
  simpa only [hw_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat, zero_sub, Pi.pow_apply, Pi.mul_apply,
    Pi.div_apply, Pi.sub_apply] using halg

/-- **Main Analytic Theorem:** `G(w, c)` is jointly convex on `(0, ∞) × ℝ`. -/
theorem convexOn_Gfun :
    ConvexOn ℝ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) (fun p : ℝ × ℝ => Gfun p.1 p.2) := by
  refine ⟨(convex_Ioi (0 : ℝ)).prod convex_univ, ?_⟩
  rintro ⟨w₁, c₁⟩ ⟨hw₁, _⟩ ⟨w₂, c₂⟩ ⟨hw₂, _⟩ a b ha hb hab
  rw [Set.mem_Ioi] at hw₁ hw₂
  set dw := w₂ - w₁
  set dc := c₂ - c₁
  set g : ℝ → ℝ := fun τ => Gfun (w₁ + τ * dw) (c₁ + τ * dc)
  have hw_pos : ∀ τ ∈ Icc (0 : ℝ) 1, 0 < w₁ + τ * dw := by
    intro τ ⟨h0, h1⟩
    have : w₁ + τ * dw = (1 - τ) * w₁ + τ * w₂ := by simp only [dw]; ring
    rw [this]
    by_cases hτ0 : τ = 0
    · rw [hτ0]; linarith
    · have hτp : 0 < τ := lt_of_le_of_ne h0 (Ne.symm hτ0)
      nlinarith
  have hg_deriv : ∀ τ ∈ Icc (0 : ℝ) 1,
      HasDerivAt g
        (dw * (yf (c₁ + τ * dc) (1 / (w₁ + τ * dw)) * tf (c₁ + τ * dc) (1 / (w₁ + τ * dw))) +
          dc * (-gf (c₁ + τ * dc) (1 / (w₁ + τ * dw)) / (1 / (w₁ + τ * dw)) ^ 2)) τ :=
    fun τ hτ => hasDerivAt_Gfun_line w₁ dw c₁ dc τ (hw_pos τ hτ)
  have hg_cont : ContinuousOn g (Icc 0 1) := fun τ hτ =>
    (hg_deriv τ hτ).continuousAt.continuousWithinAt
  have hg_diff : DifferentiableOn ℝ g (interior (Icc (0 : ℝ) 1)) := fun τ hτ =>
    (hg_deriv τ (interior_subset hτ)).differentiableAt.differentiableWithinAt
  have hg_deriv_eq : ∀ τ ∈ interior (Icc (0 : ℝ) 1),
      deriv g τ =
        dw * (yf (c₁ + τ * dc) (1 / (w₁ + τ * dw)) * tf (c₁ + τ * dc) (1 / (w₁ + τ * dw))) +
          dc * (-gf (c₁ + τ * dc) (1 / (w₁ + τ * dw)) / (1 / (w₁ + τ * dw)) ^ 2) :=
    fun τ hτ => (hg_deriv τ (interior_subset hτ)).deriv
  have hg_deriv2 : ∀ τ ∈ interior (Icc (0 : ℝ) 1),
      HasDerivAt (deriv g)
        (dw ^ 2 * ((1 / (w₁ + τ * dw)) * yf (c₁ + τ * dc) (1 / (w₁ + τ * dw)) *
            W1 (c₁ + τ * dc) (1 / (w₁ + τ * dw))) +
          2 * dw * dc * (yf (c₁ + τ * dc) (1 / (w₁ + τ * dw)) *
            M1 (c₁ + τ * dc) (1 / (w₁ + τ * dw)) / (1 / (w₁ + τ * dw))) +
          dc ^ 2 * (Cfun (c₁ + τ * dc) (1 / (w₁ + τ * dw)) / (1 / (w₁ + τ * dw)) ^ 3)) τ := by
    intro τ hτ
    have hd2 := hasDerivAt_Gfun_line_deriv w₁ dw c₁ dc τ (hw_pos τ (interior_subset hτ))
    refine hd2.congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem (isOpen_interior.mem_nhds hτ) hg_deriv_eq
  have hg_conv : ConvexOn ℝ (Icc (0 : ℝ) 1) g := by
    refine convexOn_of_deriv2_nonneg (convex_Icc 0 1) hg_cont hg_diff
      (fun τ hτ => (hg_deriv2 τ hτ).differentiableAt.differentiableWithinAt) ?_
    intro τ hτ
    have h2 := (hg_deriv2 τ hτ).deriv
    change 0 ≤ deriv (deriv g) τ
    rw [h2]
    set L := 1 / (w₁ + τ * dw)
    set c := c₁ + τ * dc
    have hLp : 0 < L := div_pos one_pos (hw_pos τ (interior_subset hτ))
    have hy : 0 < yf c L := yf_pos c hLp
    have hW : 0 < W1 c L := W1_pos c hLp
    have hD : 0 < D1 c L := D1_pos c hLp
    have hGww : 0 < L * yf c L * W1 c L := by positivity
    have hquad :
        dw ^ 2 * (L * yf c L * W1 c L) +
          2 * dw * dc * (yf c L * M1 c L / L) +
          dc ^ 2 * (Cfun c L / L ^ 3) =
        (dw * (L * yf c L * W1 c L) + dc * (yf c L * M1 c L / L)) ^ 2 / (L * yf c L * W1 c L) +
          dc ^ 2 * (yf c L * D1 c L / L ^ 2) / (L * yf c L * W1 c L) := by
      unfold D1
      field_simp
      ring
    rw [hquad]
    positivity
  have hconv_ab := hg_conv.2 (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) ha hb hab
  dsimp only [g] at hconv_ab
  simp only [smul_eq_mul, mul_zero, mul_one, zero_mul, one_mul, zero_add, add_zero] at hconv_ab
  have hw_ab : a * w₁ + b * w₂ = w₁ + b * dw := by
    simp only [dw]; rw [show a = 1 - b by linarith]; ring
  have hc_ab : a * c₁ + b * c₂ = c₁ + b * dc := by
    simp only [dc]; rw [show a = 1 - b by linarith]; ring
  have h1w : w₁ + dw = w₂ := by simp only [dw]; ring
  have h1c : c₁ + dc = c₂ := by simp only [dc]; ring
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  rw [hw_ab, hc_ab]
  rw [h1w, h1c] at hconv_ab
  exact hconv_ab

/-! ### Part 2: Perspective function `H(t, w, c)`, ray gauge `p(v)`, and strictly nested case -/

/-- Perspective function `H(t, w, c) = t * G(w / t, c / t)`. -/
def Hfun (t w c : ℝ) : ℝ := t * Gfun (w / t) (c / t)

lemma Hfun_eq_integral {t w : ℝ} (ht : 0 < t) (hw : 0 < w) (c : ℝ) :
    Hfun t w c =
      (∫ s in (0 : ℝ)..(1 / w), s * Real.exp (-t ^ 2 * s ^ 2 / 2 + c * s)) /
      (∫ s in (0 : ℝ)..(1 / w), s ^ 2 * Real.exp (-t ^ 2 * s ^ 2 / 2 + c * s)) := by
  unfold Hfun Gfun Imom phi
  have h1 : 1 / (w / t) = t * (1 / w) := by field_simp
  rw [h1]
  have hsub : ∀ k : ℕ,
      (∫ u in (0 : ℝ)..(t * (1 / w)), u ^ k * Real.exp (-(u - c / t) ^ 2 / 2)) =
      t ^ (k + 1) * Real.exp (-(c / t) ^ 2 / 2) *
        ∫ s in (0 : ℝ)..(1 / w), s ^ k * Real.exp (-t ^ 2 * s ^ 2 / 2 + c * s) := by
    intro k
    have hcomp := intervalIntegral.integral_comp_mul_left
      (fun u : ℝ => u ^ k * Real.exp (-(u - c / t) ^ 2 / 2)) (ne_of_gt ht)
      (a := (0 : ℝ)) (b := 1 / w)
    simp only [mul_zero, smul_eq_mul] at hcomp
    have hinner : (∫ s in (0 : ℝ)..(1 / w), (t * s) ^ k * Real.exp (-(t * s - c / t) ^ 2 / 2)) =
        t ^ k * Real.exp (-(c / t) ^ 2 / 2) *
          ∫ s in (0 : ℝ)..(1 / w), s ^ k * Real.exp (-t ^ 2 * s ^ 2 / 2 + c * s) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [mul_pow]
      have hexp : -(t * s - c / t) ^ 2 / 2 = -(c / t) ^ 2 / 2 + (-t ^ 2 * s ^ 2 / 2 + c * s) := by
        field_simp; ring
      rw [hexp, Real.exp_add]; ring
    rw [hinner] at hcomp
    have hmul := congrArg (t * ·) hcomp
    have hcancel : t * (t⁻¹ * ∫ u in (0 : ℝ)..(t * (1 / w)),
        u ^ k * Real.exp (-(u - c / t) ^ 2 / 2)) =
        ∫ u in (0 : ℝ)..(t * (1 / w)), u ^ k * Real.exp (-(u - c / t) ^ 2 / 2) := by
      field_simp
    rw [hcancel] at hmul
    rw [← hmul]; ring
  rw [hsub 1, hsub 2]
  have htne : t ≠ 0 := ne_of_gt ht
  have hexp : Real.exp (-(c / t) ^ 2 / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hden_pos : 0 < ∫ s in (0 : ℝ)..(1 / w), s ^ 2 * Real.exp (-t ^ 2 * s ^ 2 / 2 + c * s) := by
    refine intervalIntegral.integral_pos (div_pos one_pos hw) (by fun_prop) ?_ ?_
    · intro s hs; exact mul_nonneg (sq_nonneg s) (le_of_lt (Real.exp_pos _))
    · refine ⟨1 / (2 * w), ⟨by positivity, by
        rw [div_le_div_iff₀ (by positivity) hw]; linarith⟩,
        mul_pos (sq_pos_of_pos (by positivity)) (Real.exp_pos _)⟩
  have hden_ne : (∫ s in (0 : ℝ)..(1 / w), s ^ 2 * Real.exp (-t ^ 2 * s ^ 2 / 2 + c * s)) ≠ 0 :=
    ne_of_gt hden_pos
  field_simp
  ring

lemma Hfun_pos {t w : ℝ} (ht : 0 < t) (hw : 0 < w) (c : ℝ) : 0 < Hfun t w c := by
  unfold Hfun Gfun
  have hL : 0 < 1 / (w / t) := div_pos one_pos (div_pos hw ht)
  exact mul_pos ht (div_pos (Imom_pos 1 (c / t) hL) (Imom_pos 2 (c / t) hL))

lemma Hfun_smul {lam t w : ℝ} (hlam : 0 < lam) (c : ℝ) :
    Hfun (lam * t) (lam * w) (lam * c) = lam * Hfun t w c := by
  unfold Hfun
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have h1 : lam * w / (lam * t) = w / t := by
    by_cases ht : t = 0
    · simp [ht]
    · field_simp
  have h2 : lam * c / (lam * t) = c / t := by
    by_cases ht : t = 0
    · simp [ht]
    · field_simp
  rw [h1, h2]; ring

lemma Hfun_subadd {t₁ t₂ w₁ w₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (c₁ c₂ : ℝ) :
    Hfun (t₁ + t₂) (w₁ + w₂) (c₁ + c₂) ≤ Hfun t₁ w₁ c₁ + Hfun t₂ w₂ c₂ := by
  unfold Hfun
  set a := t₁ / (t₁ + t₂)
  set b := t₂ / (t₁ + t₂)
  have ht12 : 0 < t₁ + t₂ := add_pos ht₁ ht₂
  have ha : 0 ≤ a := le_of_lt (div_pos ht₁ ht12)
  have hb : 0 ≤ b := le_of_lt (div_pos ht₂ ht12)
  have hab : a + b = 1 := by simp only [a, b]; field_simp
  have hconv := convexOn_Gfun.2
    (show ((w₁ / t₁, c₁ / t₁) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ univ from ⟨div_pos hw₁ ht₁, trivial⟩)
    (show ((w₂ / t₂, c₂ / t₂) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ univ from ⟨div_pos hw₂ ht₂, trivial⟩)
    ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hconv
  have h1 : a * (w₁ / t₁) + b * (w₂ / t₂) = (w₁ + w₂) / (t₁ + t₂) := by
    simp only [a, b]; field_simp
  have h2 : a * (c₁ / t₁) + b * (c₂ / t₂) = (c₁ + c₂) / (t₁ + t₂) := by
    simp only [a, b]; field_simp
  rw [h1, h2] at hconv
  have hmul := mul_le_mul_of_nonneg_left hconv (le_of_lt ht12)
  have hrhs : (t₁ + t₂) * (a * Gfun (w₁ / t₁) (c₁ / t₁) + b * Gfun (w₂ / t₂) (c₂ / t₂)) =
      t₁ * Gfun (w₁ / t₁) (c₁ / t₁) + t₂ * Gfun (w₂ / t₂) (c₂ / t₂) := by
    simp only [a, b]; field_simp
  linarith

lemma Hfun_strictMono_t {t₁ t₂ w : ℝ} (ht₁ : 0 < t₁) (ht : t₁ < t₂) (hw : 0 < w) (c : ℝ) :
    Hfun t₁ w c < Hfun t₂ w c := by
  have ht₂ : 0 < t₂ := lt_trans ht₁ ht
  rw [Hfun_eq_integral ht₁ hw c, Hfun_eq_integral ht₂ hw c]
  set L := 1 / w
  have hL : 0 < L := div_pos one_pos hw
  set f₁ := fun s : ℝ => Real.exp (-t₁ ^ 2 * s ^ 2 / 2 + c * s)
  set f₂ := fun s : ℝ => Real.exp (-t₂ ^ 2 * s ^ 2 / 2 + c * s)
  have hd1 : 0 < ∫ s in (0 : ℝ)..L, s ^ 2 * f₁ s := by
    refine intervalIntegral.integral_pos hL (by simp only [f₁]; fun_prop)
      (fun s hs => mul_nonneg (sq_nonneg s) (le_of_lt (Real.exp_pos _)))
      ⟨L / 2, ⟨by linarith, by linarith⟩, mul_pos (sq_pos_of_pos (by linarith)) (Real.exp_pos _)⟩
  have hd2 : 0 < ∫ s in (0 : ℝ)..L, s ^ 2 * f₂ s := by
    refine intervalIntegral.integral_pos hL (by simp only [f₂]; fun_prop)
      (fun s hs => mul_nonneg (sq_nonneg s) (le_of_lt (Real.exp_pos _)))
      ⟨L / 2, ⟨by linarith, by linarith⟩, mul_pos (sq_pos_of_pos (by linarith)) (Real.exp_pos _)⟩
  rw [div_lt_div_iff₀ hd1 hd2]
  set a := (t₂ ^ 2 - t₁ ^ 2) / 2
  have ha : 0 < a := by simp only [a]; nlinarith
  have hfac_all : ∀ s r : ℝ, f₂ s * f₁ r - f₁ s * f₂ r =
      f₂ s * f₂ r * (Real.exp (a * r ^ 2) - Real.exp (a * s ^ 2)) := by
    intro s r
    simp only [f₁, f₂, a]
    rw [mul_sub]
    simp only [← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  set K : ℝ → ℝ → ℝ := fun s r => s * r * (r - s) * (f₂ s * f₁ r - f₁ s * f₂ r)
  have hK_cont : Continuous (fun p : ℝ × ℝ => K p.1 p.2) := by
    simp only [K, f₁, f₂]; fun_prop
  have hK_nn : ∀ s ∈ Icc (0 : ℝ) L, ∀ r ∈ Icc (0 : ℝ) L, 0 ≤ K s r := by
    intro s hs r hr
    simp only [K]
    rw [hfac_all s r]
    have hsign : 0 ≤ (r - s) * (Real.exp (a * r ^ 2) - Real.exp (a * s ^ 2)) := by
      rcases le_total s r with hsr | hrs
      · exact mul_nonneg (sub_nonneg.mpr hsr)
          (sub_nonneg.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
            (by nlinarith [hs.1, hr.1]) (le_of_lt ha))))
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hrs)
          (sub_nonpos.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
            (by nlinarith [hs.1, hr.1]) (le_of_lt ha))))
    have hprod : s * r * (r - s) * (f₂ s * f₂ r * (Real.exp (a * r ^ 2) - Real.exp (a * s ^ 2))) =
        (s * r * f₂ s * f₂ r) * ((r - s) * (Real.exp (a * r ^ 2) - Real.exp (a * s ^ 2))) := by ring
    rw [hprod]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hs.1 hr.1) (le_of_lt (Real.exp_pos _)))
      (le_of_lt (Real.exp_pos _))) hsign
  have hK_pos_pt : 0 < K (L / 3) (2 * L / 3) := by
    simp only [K]
    rw [hfac_all (L / 3) (2 * L / 3)]
    have hsq_lt : (L / 3) ^ 2 < (2 * L / 3) ^ 2 := by nlinarith
    have hexp_lt : Real.exp (a * (L / 3) ^ 2) < Real.exp (a * (2 * L / 3) ^ 2) :=
      Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hsq_lt ha)
    have h1 : 0 < f₂ (L / 3) := Real.exp_pos _
    have h2 : 0 < f₂ (2 * L / 3) := Real.exp_pos _
    have h3 : 0 < 2 * L / 3 - L / 3 := by linarith
    have h4 : 0 < Real.exp (a * (2 * L / 3) ^ 2) - Real.exp (a * (L / 3) ^ 2) := sub_pos.mpr hexp_lt
    positivity
  have hdouble_pos : 0 < ∫ s in (0 : ℝ)..L, ∫ r in (0 : ℝ)..L, K s r := by
    refine intervalIntegral.integral_pos hL ?_ ?_ ?_
    · have hcont_in : Continuous (fun s : ℝ => ∫ r in (0 : ℝ)..L, K s r) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hK_cont 0 L
      exact hcont_in.continuousOn
    · intro s hs
      exact intervalIntegral.integral_nonneg (le_of_lt hL) fun r hr =>
        hK_nn s ⟨le_of_lt hs.1, hs.2⟩ r hr
    · refine ⟨L / 3, ⟨by linarith, by linarith⟩, ?_⟩
      refine intervalIntegral.integral_pos hL
        (hK_cont.comp (continuous_const.prodMk continuous_id)).continuousOn
        (fun r hr => hK_nn (L / 3) ⟨by linarith, by linarith⟩ r ⟨le_of_lt hr.1, hr.2⟩)
        ⟨2 * L / 3, ⟨by linarith, by linarith⟩, hK_pos_pt⟩
  have h_eq : (∫ s in (0 : ℝ)..L, ∫ r in (0 : ℝ)..L, K s r) =
      2 * ((∫ s in (0 : ℝ)..L, s * f₂ s) * (∫ r in (0 : ℝ)..L, r ^ 2 * f₁ r) -
           (∫ s in (0 : ℝ)..L, s * f₁ s) * (∫ r in (0 : ℝ)..L, r ^ 2 * f₂ r)) := by
    have hsplit : ∀ s, (∫ r in (0 : ℝ)..L, K s r) =
        (s * f₂ s) * (∫ r in (0 : ℝ)..L, r ^ 2 * f₁ r) -
        (s * f₁ s) * (∫ r in (0 : ℝ)..L, r ^ 2 * f₂ r) -
        (s ^ 2 * f₂ s) * (∫ r in (0 : ℝ)..L, r * f₁ r) +
        (s ^ 2 * f₁ s) * (∫ r in (0 : ℝ)..L, r * f₂ r) := by
      intro s
      have h1 : IntervalIntegrable (fun r => r ^ 2 * f₁ r) volume 0 L :=
        (by simp only [f₁]; fun_prop : Continuous _).intervalIntegrable 0 L
      have h2 : IntervalIntegrable (fun r => r ^ 2 * f₂ r) volume 0 L :=
        (by simp only [f₂]; fun_prop : Continuous _).intervalIntegrable 0 L
      have h3 : IntervalIntegrable (fun r => r * f₁ r) volume 0 L :=
        (by simp only [f₁]; fun_prop : Continuous _).intervalIntegrable 0 L
      have h4 : IntervalIntegrable (fun r => r * f₂ r) volume 0 L :=
        (by simp only [f₂]; fun_prop : Continuous _).intervalIntegrable 0 L
      have hf : (fun r => K s r) = fun r =>
          (((s * f₂ s) * (r ^ 2 * f₁ r) - (s * f₁ s) * (r ^ 2 * f₂ r)) -
            (s ^ 2 * f₂ s) * (r * f₁ r)) + (s ^ 2 * f₁ s) * (r * f₂ r) := by
        ext r; simp only [K]; ring
      rw [hf,
        intervalIntegral.integral_add
          (((h1.const_mul _).sub (h2.const_mul _)).sub (h3.const_mul _)) (h4.const_mul _),
        intervalIntegral.integral_sub ((h1.const_mul _).sub (h2.const_mul _)) (h3.const_mul _),
        intervalIntegral.integral_sub (h1.const_mul _) (h2.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    simp_rw [hsplit]
    have g1 : IntervalIntegrable (fun s => s * f₂ s) volume 0 L :=
      (by simp only [f₂]; fun_prop : Continuous _).intervalIntegrable 0 L
    have g2 : IntervalIntegrable (fun s => s * f₁ s) volume 0 L :=
      (by simp only [f₁]; fun_prop : Continuous _).intervalIntegrable 0 L
    have g3 : IntervalIntegrable (fun s => s ^ 2 * f₂ s) volume 0 L :=
      (by simp only [f₂]; fun_prop : Continuous _).intervalIntegrable 0 L
    have g4 : IntervalIntegrable (fun s => s ^ 2 * f₁ s) volume 0 L :=
      (by simp only [f₁]; fun_prop : Continuous _).intervalIntegrable 0 L
    rw [intervalIntegral.integral_add
        (((g1.mul_const _).sub (g2.mul_const _)).sub (g3.mul_const _)) (g4.mul_const _),
      intervalIntegral.integral_sub ((g1.mul_const _).sub (g2.mul_const _)) (g3.mul_const _),
      intervalIntegral.integral_sub (g1.mul_const _) (g2.mul_const _),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
    ring
  linarith

lemma Hfun_mono_w {t w₁ w₂ : ℝ} (ht : 0 < t) (hw₁ : 0 < w₁) (hw : w₁ ≤ w₂) (c : ℝ) :
    Hfun t w₁ c ≤ Hfun t w₂ c := by
  rcases eq_or_lt_of_le hw with rfl | hlt
  · exact le_rfl
  have hw₂ : 0 < w₂ := lt_trans hw₁ hlt
  rw [Hfun_eq_integral ht hw₁ c, Hfun_eq_integral ht hw₂ c]
  set L₁ := 1 / w₁
  set L₂ := 1 / w₂
  have hL₂ : 0 < L₂ := div_pos one_pos hw₂
  have hL : L₂ < L₁ := one_div_lt_one_div_of_lt hw₁ hlt
  set f := fun s : ℝ => Real.exp (-t ^ 2 * s ^ 2 / 2 + c * s)
  have hf1_int : ∀ a b, IntervalIntegrable (fun s => s * f s) volume a b := fun a b =>
    (by simp only [f]; fun_prop : Continuous _).intervalIntegrable a b
  have hf2_int : ∀ a b, IntervalIntegrable (fun s => s ^ 2 * f s) volume a b := fun a b =>
    (by simp only [f]; fun_prop : Continuous _).intervalIntegrable a b
  have hd1 : 0 < ∫ s in (0 : ℝ)..L₁, s ^ 2 * f s :=
    intervalIntegral.integral_pos (lt_trans hL₂ hL) (by simp only [f]; fun_prop)
      (fun s hs => mul_nonneg (sq_nonneg s) (le_of_lt (Real.exp_pos _)))
      ⟨L₂ / 2, ⟨by linarith, by linarith⟩, mul_pos (sq_pos_of_pos (by linarith)) (Real.exp_pos _)⟩
  have hd2 : 0 < ∫ s in (0 : ℝ)..L₂, s ^ 2 * f s :=
    intervalIntegral.integral_pos hL₂ (by simp only [f]; fun_prop)
      (fun s hs => mul_nonneg (sq_nonneg s) (le_of_lt (Real.exp_pos _)))
      ⟨L₂ / 2, ⟨by linarith, by linarith⟩, mul_pos (sq_pos_of_pos (by linarith)) (Real.exp_pos _)⟩
  rw [div_le_div_iff₀ hd1 hd2]
  have hs1 := (intervalIntegral.integral_add_adjacent_intervals (hf1_int 0 L₂) (hf1_int L₂ L₁)).symm
  have hs2 := (intervalIntegral.integral_add_adjacent_intervals (hf2_int 0 L₂) (hf2_int L₂ L₁)).symm
  rw [hs1, hs2]
  have hbound : (∫ s in (0 : ℝ)..L₂, s ^ 2 * f s) * (∫ r in L₂..L₁, r * f r) ≤
      (∫ s in (0 : ℝ)..L₂, s * f s) * (∫ r in L₂..L₁, r ^ 2 * f r) := by
    have h1 : (∫ s in (0 : ℝ)..L₂, s ^ 2 * f s) ≤ L₂ * ∫ s in (0 : ℝ)..L₂, s * f s := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on (le_of_lt hL₂) (hf2_int 0 L₂) ((hf1_int 0 L₂).const_mul _) ?_
      intro s hs
      have hfpos : 0 ≤ f s := le_of_lt (Real.exp_pos _)
      have hsq : s ^ 2 ≤ L₂ * s := by nlinarith [hs.1, hs.2]
      calc s ^ 2 * f s ≤ (L₂ * s) * f s := mul_le_mul_of_nonneg_right hsq hfpos
        _ = L₂ * (s * f s) := by ring
    have h2 : L₂ * (∫ r in L₂..L₁, r * f r) ≤ ∫ r in L₂..L₁, r ^ 2 * f r := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on (le_of_lt hL) ((hf1_int L₂ L₁).const_mul _) (hf2_int L₂ L₁) ?_
      intro r hr
      have hfpos : 0 ≤ f r := le_of_lt (Real.exp_pos _)
      have hsq : L₂ * r ≤ r ^ 2 := by nlinarith [hr.1, hr.2]
      calc L₂ * (r * f r) = (L₂ * r) * f r := by ring
        _ ≤ r ^ 2 * f r := mul_le_mul_of_nonneg_right hsq hfpos
    have hnn1 : 0 ≤ ∫ s in (0 : ℝ)..L₂, s * f s :=
      intervalIntegral.integral_nonneg (le_of_lt hL₂) fun s hs =>
        mul_nonneg hs.1 (le_of_lt (Real.exp_pos _))
    have hnn2 : 0 ≤ ∫ r in L₂..L₁, r * f r :=
      intervalIntegral.integral_nonneg (le_of_lt hL) fun r hr =>
        mul_nonneg (le_trans (le_of_lt hL₂) hr.1) (le_of_lt (Real.exp_pos _))
    calc (∫ s in (0 : ℝ)..L₂, s ^ 2 * f s) * (∫ r in L₂..L₁, r * f r)
        ≤ (L₂ * ∫ s in (0 : ℝ)..L₂, s * f s) * (∫ r in L₂..L₁, r * f r) :=
          mul_le_mul_of_nonneg_right h1 hnn2
      _ = (∫ s in (0 : ℝ)..L₂, s * f s) * (L₂ * ∫ r in L₂..L₁, r * f r) := by ring
      _ ≤ (∫ s in (0 : ℝ)..L₂, s * f s) * (∫ r in L₂..L₁, r ^ 2 * f r) :=
          mul_le_mul_of_nonneg_left h2 hnn1
  linarith

/-! ### Part 2 & 3: Planar triangles, Haar parametrization, nested and non-nested cases -/

abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- 2D determinant `u₀ v₁ - u₁ v₀`. -/
def det2 (u v : E2) : ℝ := u 0 * v 1 - u 1 * v 0

lemma det2_antisymm (u v : E2) : det2 u v = -det2 v u := by
  unfold det2; ring

lemma det2_self (u : E2) : det2 u u = 0 := by
  unfold det2; ring

lemma det2_add_left (u₁ u₂ v : E2) : det2 (u₁ + u₂) v = det2 u₁ v + det2 u₂ v := by
  unfold det2; simp; ring

lemma det2_add_right (u v₁ v₂ : E2) : det2 u (v₁ + v₂) = det2 u v₁ + det2 u v₂ := by
  unfold det2; simp; ring

lemma det2_sub_left (u₁ u₂ v : E2) : det2 (u₁ - u₂) v = det2 u₁ v - det2 u₂ v := by
  unfold det2; simp; ring

lemma det2_sub_right (u v₁ v₂ : E2) : det2 u (v₁ - v₂) = det2 u v₁ - det2 u v₂ := by
  unfold det2; simp; ring

lemma det2_smul_left (a : ℝ) (u v : E2) : det2 (a • u) v = a * det2 u v := by
  unfold det2; simp; ring

lemma det2_smul_right (a : ℝ) (u v : E2) : det2 u (a • v) = a * det2 u v := by
  unfold det2; simp; ring

lemma e2_ext {u v : E2} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- Cramer's rule in `E2`: any vector `x` expands uniquely in a basis `(u, v)` with `det2 u v ≠ 0`. -/
lemma cramer_e2 {u v : E2} (hdet : det2 u v ≠ 0) (x : E2) :
    x = (det2 x v / det2 u v) • u + (det2 u x / det2 u v) • v := by
  apply e2_ext <;>
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    apply mul_right_cancel₀ hdet
    rw [add_mul, mul_right_comm _ (u _), div_mul_cancel₀ _ hdet,
      mul_right_comm _ (v _), div_mul_cancel₀ _ hdet]
    unfold det2; ring

lemma linear_combo_eq_zero_of_det2_ne_zero {u v : E2} (hdet : det2 u v ≠ 0)
    {a b : ℝ} (h : a • u + b • v = 0) : a = 0 ∧ b = 0 := by
  have h1 : det2 (a • u + b • v) v = 0 := by rw [h]; unfold det2; simp
  have h2 : det2 u (a • u + b • v) = 0 := by rw [h]; unfold det2; simp
  rw [det2_add_left, det2_smul_left, det2_smul_left, det2_self, mul_zero, add_zero] at h1
  rw [det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, zero_add] at h2
  exact ⟨(mul_eq_zero.mp h1).resolve_right hdet, (mul_eq_zero.mp h2).resolve_right hdet⟩

lemma det2_ne_zero_of_affineIndependent {A B C : E2}
    (h : AffineIndependent ℝ ![A, B, C]) : det2 (B - A) (C - A) ≠ 0 := by
  intro h0
  have hli := (affineIndependent_iff_linearIndependent_vsub ℝ ![A, B, C] (0 : Fin 3)).mp h
  rw [Fintype.linearIndependent_iff] at hli
  -- Construct a nontrivial linear relation between (B - A) and (C - A)
  by_cases hBA : B - A = 0
  · let g : {i : Fin 3 // i ≠ 0} → ℝ := fun i => if i.1 = 1 then 1 else 0
    have hsum : ∑ i : {i : Fin 3 // i ≠ 0}, g i • (![A, B, C] i.1 -ᵥ ![A, B, C] 0) = 0 := by
      have hfin : (Finset.univ : Finset {i : Fin 3 // i ≠ 0}) =
          {⟨1, by decide⟩, ⟨2, by decide⟩} := by decide
      rw [hfin, Finset.sum_pair (by decide)]
      simp [g, vsub_eq_sub, hBA]
    have hg1 := hli g hsum ⟨1, by decide⟩
    simp [g] at hg1
  · have hcoord : (B - A) 0 ≠ 0 ∨ (B - A) 1 ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hBA (e2_ext hall.1 hall.2)
    -- If (B - A) 0 ≠ 0, then (C - A) 0 • (B - A) - (B - A) 0 • (C - A) = 0
    rcases hcoord with hB0 | hB1
    · let g : {i : Fin 3 // i ≠ 0} → ℝ := fun i =>
        if i.1 = 1 then (C - A) 0 else -((B - A) 0)
      have hsum : ∑ i : {i : Fin 3 // i ≠ 0}, g i • (![A, B, C] i.1 -ᵥ ![A, B, C] 0) = 0 := by
        have hfin : (Finset.univ : Finset {i : Fin 3 // i ≠ 0}) =
            {⟨1, by decide⟩, ⟨2, by decide⟩} := by decide
        rw [hfin, Finset.sum_pair (by decide)]
        simp only [g, ↓reduceIte, Fin.reduceEq, Matrix.cons_val_one, Matrix.cons_val_zero,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, vsub_eq_sub]
        apply e2_ext
        · simp; ring
        · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
          unfold det2 at h0; linarith
      have hg2 := hli g hsum ⟨2, by decide⟩
      simp [g] at hg2
      exact hB0 (by simp only [PiLp.sub_apply]; linarith)
    · let g : {i : Fin 3 // i ≠ 0} → ℝ := fun i =>
        if i.1 = 1 then (C - A) 1 else -((B - A) 1)
      have hsum : ∑ i : {i : Fin 3 // i ≠ 0}, g i • (![A, B, C] i.1 -ᵥ ![A, B, C] 0) = 0 := by
        have hfin : (Finset.univ : Finset {i : Fin 3 // i ≠ 0}) =
            {⟨1, by decide⟩, ⟨2, by decide⟩} := by decide
        rw [hfin, Finset.sum_pair (by decide)]
        simp only [g, ↓reduceIte, Fin.reduceEq, Matrix.cons_val_one, Matrix.cons_val_zero,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, vsub_eq_sub]
        apply e2_ext
        · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
          unfold det2 at h0; linarith
        · simp; ring
      have hg2 := hli g hsum ⟨2, by decide⟩
      simp [g] at hg2
      exact hB1 (by simp only [PiLp.sub_apply]; linarith)

/-- Closed triangle `tri A B C = convexHull ℝ {A, B, C}` and its open interior `triInt A B C`. -/
def tri (A B C : E2) : Set E2 := convexHull ℝ {A, B, C}

def triInt (A B C : E2) : Set E2 :=
  {x : E2 | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 1 ∧
    x = a • A + b • B + c • C}

lemma mem_tri_iff (A B C x : E2) :
    x ∈ tri A B C ↔
      ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ x = a • A + b • B + c • C := by
  constructor
  · intro hx
    set S : Set E2 :=
      {y : E2 | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧
        y = a • A + b • B + c • C}
    have hSconv : Convex ℝ S := by
      rintro y₁ ⟨a₁, b₁, c₁, ha₁, hb₁, hc₁, h1, rfl⟩ y₂ ⟨a₂, b₂, c₂, ha₂, hb₂, hc₂, h2, rfl⟩
        p q hp hq hpq
      refine ⟨p * a₁ + q * a₂, p * b₁ + q * b₂, p * c₁ + q * c₂,
        by positivity, by positivity, by positivity, by nlinarith, ?_⟩
      simp only [smul_add, smul_smul, add_smul]
      abel
    have hsub : ({A, B, C} : Set E2) ⊆ S := by
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨1, 0, 0, zero_le_one, le_rfl, le_rfl, by ring, by simp⟩
      · exact ⟨0, 1, 0, le_rfl, zero_le_one, le_rfl, by ring, by simp⟩
      · exact ⟨0, 0, 1, le_rfl, le_rfl, zero_le_one, by ring, by simp⟩
    exact convexHull_min hsub hSconv hx
  · rintro ⟨a, b, c, ha, hb, hc, habc, rfl⟩
    have hA : A ∈ tri A B C := subset_convexHull ℝ _ (by simp)
    have hB : B ∈ tri A B C := subset_convexHull ℝ _ (by simp)
    have hC : C ∈ tri A B C := subset_convexHull ℝ _ (by simp)
    have hconv : Convex ℝ (tri A B C) := convex_convexHull ℝ _
    by_cases hbc : b + c = 0
    · have hb0 : b = 0 := by linarith
      have hc0 : c = 0 := by linarith
      have ha1 : a = 1 := by linarith
      simpa [ha1, hb0, hc0] using hA
    · have hbc_pos : 0 < b + c := lt_of_le_of_ne (add_nonneg hb hc) (Ne.symm hbc)
      have hBC : (b / (b + c)) • B + (c / (b + c)) • C ∈ tri A B C :=
        hconv hB hC (div_nonneg hb (le_of_lt hbc_pos)) (div_nonneg hc (le_of_lt hbc_pos))
          (by field_simp)
      have hABC := hconv hA hBC ha (le_of_lt hbc_pos) (by linarith)
      convert hABC using 1
      rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hbc, mul_div_cancel₀ _ hbc, add_assoc]

lemma triInt_subset_tri (A B C : E2) : triInt A B C ⊆ tri A B C := by
  rintro x ⟨a, b, c, ha, hb, hc, habc, rfl⟩
  exact (mem_tri_iff A B C _).mpr ⟨a, b, c, le_of_lt ha, le_of_lt hb, le_of_lt hc, habc, rfl⟩

lemma isCompact_tri (A B C : E2) : IsCompact (tri A B C) :=
  ((Set.finite_singleton C).insert B |>.insert A).isCompact_convexHull ℝ

lemma measurableSet_tri (A B C : E2) : MeasurableSet (tri A B C) :=
  (isCompact_tri A B C).isClosed.measurableSet

lemma tri_perm_swap23 (A B C : E2) : tri A B C = tri A C B := by
  unfold tri; congr 1; ext x; simp [or_comm]

lemma tri_perm_swap12 (A B C : E2) : tri A B C = tri B A C := by
  unfold tri; congr 1; ext x; simp [or_left_comm]

lemma tri_perm_rot (A B C : E2) : tri A B C = tri C A B := by
  unfold tri; congr 1; ext x; simp [or_comm, or_left_comm]

lemma line_measure_zero (P Q R : E2) (hdet : det2 (Q - P) (R - P) ≠ 0) :
    volume ((affineSpan ℝ ({P, Q} : Set E2)) : Set E2) = 0 := by
  apply MeasureTheory.Measure.addHaar_affineSubspace
  intro htop
  have hR : R ∈ affineSpan ℝ ({P, Q} : Set E2) := by rw [htop]; trivial
  have hmem : R -ᵥ P ∈ vectorSpan ℝ ({P, Q} : Set E2) :=
    vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hR
      (subset_affineSpan ℝ _ (by simp))
  have hvs : vectorSpan ℝ ({P, Q} : Set E2) = Submodule.span ℝ {Q - P} := by
    rw [vectorSpan_pair, Submodule.span_singleton_eq_span_singleton]
    refine ⟨-1, ?_⟩
    simp [vsub_eq_sub]
  rw [hvs, Submodule.mem_span_singleton] at hmem
  obtain ⟨t, ht⟩ := hmem
  have hRP : R - P = t • (Q - P) := by simpa [vsub_eq_sub] using ht.symm
  apply hdet
  rw [hRP, det2_smul_right, det2_self, mul_zero]

lemma tri_diff_triInt_measure_zero {A B C : E2} (hdet : det2 (B - A) (C - A) ≠ 0) :
    volume (tri A B C \ triInt A B C) = 0 := by
  have hsub : tri A B C \ triInt A B C ⊆
      ((affineSpan ℝ ({B, C} : Set E2)) : Set E2) ∪
      ((affineSpan ℝ ({A, C} : Set E2)) : Set E2) ∪
      ((affineSpan ℝ ({A, B} : Set E2)) : Set E2) := by
    rintro x ⟨hx, hnot⟩
    rw [mem_tri_iff] at hx
    obtain ⟨a, b, c, ha, hb, hc, habc, rfl⟩ := hx
    have hor : a = 0 ∨ b = 0 ∨ c = 0 := by
      by_contra h
      push Not at h
      exact hnot ⟨a, b, c, lt_of_le_of_ne ha (Ne.symm h.1),
        lt_of_le_of_ne hb (Ne.symm h.2.1), lt_of_le_of_ne hc (Ne.symm h.2.2), habc, rfl⟩
    have hmem_pair : ∀ (P Q : E2) (p q : ℝ), p + q = 1 →
        p • P + q • Q ∈ affineSpan ℝ ({P, Q} : Set E2) := by
      intro P Q p q hpq
      have h1 : p • P + q • Q = q • (Q -ᵥ P) +ᵥ P := by
        simp only [vsub_eq_sub, vadd_eq_add, smul_sub]
        have hp : p = 1 - q := by linarith
        rw [hp, sub_smul, one_smul]; abel
      rw [h1]
      exact AffineSubspace.vadd_mem_of_mem_direction
        (Submodule.smul_mem _ _ (AffineSubspace.vsub_mem_direction
          (right_mem_affineSpan_pair ℝ P Q) (left_mem_affineSpan_pair ℝ P Q)))
        (left_mem_affineSpan_pair ℝ P Q)
    rcases hor with rfl | rfl | rfl
    · left; left
      simpa using hmem_pair B C b c (by linarith)
    · left; right
      simpa using hmem_pair A C a c (by linarith)
    · right
      simpa using hmem_pair A B a b (by linarith)
  have h1 : volume ((affineSpan ℝ ({B, C} : Set E2)) : Set E2) = 0 := by
    apply line_measure_zero B C A
    have hrew : det2 (C - B) (A - B) = det2 (B - A) (C - A) := by unfold det2; simp; ring
    rwa [hrew]
  have h2 : volume ((affineSpan ℝ ({A, C} : Set E2)) : Set E2) = 0 := by
    apply line_measure_zero A C B
    rw [det2_antisymm]; exact neg_ne_zero.mpr hdet
  have h3 : volume ((affineSpan ℝ ({A, B} : Set E2)) : Set E2) = 0 :=
    line_measure_zero A B C hdet
  exact measure_mono_null hsub (measure_union_null (measure_union_null h1 h2) h3)

/-- Explicit continuous linear equivalence `ℝ × ℝ ≃L[ℝ] E2`. -/
def toE2LinearEquiv : (ℝ × ℝ) ≃ₗ[ℝ] E2 where
  toFun p := WithLp.toLp 2 ![p.1, p.2]
  invFun x := (x 0, x 1)
  map_add' p q := by apply e2_ext <;> simp
  map_smul' a p := by apply e2_ext <;> simp
  left_inv p := by ext <;> simp
  right_inv x := by apply e2_ext <;> simp

def toE2 : (ℝ × ℝ) ≃L[ℝ] E2 := toE2LinearEquiv.toContinuousLinearEquiv

@[simp] lemma toE2_apply_zero (p : ℝ × ℝ) : toE2 p 0 = p.1 := rfl
@[simp] lemma toE2_apply_one (p : ℝ × ℝ) : toE2 p 1 = p.2 := rfl
@[simp] lemma toE2_symm_apply (x : E2) : toE2.symm x = (x 0, x 1) := rfl

/-- Haar measure on `E2` pulls back via `toE2` to a positive multiple of `volume` on `ℝ × ℝ`. -/
lemma exists_haar_factor_E2 :
    ∃ c : ℝ, 0 < c ∧ ∀ (S : Set E2) (_hS : MeasurableSet S) (F : E2 → ℝ),
      ∫ x in S, F x = c * ∫ p in toE2 ⁻¹' S, F (toE2 p) := by
  set μ' : Measure (ℝ × ℝ) := Measure.map toE2.symm (volume : Measure E2)
  have htend : Tendsto toE2.symm (Filter.cocompact E2) (Filter.cocompact (ℝ × ℝ)) := by
    intro s hs
    obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.mp hs
    refine Filter.mem_cocompact.mpr ⟨toE2 '' K, hK.image toE2.continuous, ?_⟩
    intro x hx
    by_contra hnot
    have hmemK : toE2.symm x ∈ K := by
      by_contra hnotK
      exact hnot (hKs hnotK)
    exact hx ⟨toE2.symm x, hmemK, toE2.apply_symm_apply x⟩
  have hμ'_haar : μ'.IsAddHaarMeasure :=
    MeasureTheory.Measure.isAddHaarMeasure_map (volume : Measure E2)
      toE2.symm.toAddMonoidHom toE2.symm.continuous toE2.symm.surjective htend
  set c_nn : NNReal := μ'.addHaarScalarFactor (volume : Measure (ℝ × ℝ))
  have hc_nn_pos : 0 < c_nn :=
    MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' volume
  set c : ℝ := (c_nn : ℝ)
  have hc_pos : 0 < c := NNReal.coe_pos.mpr hc_nn_pos
  have hμ'_eq : μ' = ENNReal.ofReal c • (volume : Measure (ℝ × ℝ)) := by
    have h := MeasureTheory.Measure.isAddLeftInvariant_eq_smul μ' (volume : Measure (ℝ × ℝ))
    ext s _
    rw [h, Measure.smul_apply, Measure.smul_apply, ENNReal.ofReal_coe_nnreal,
      ENNReal.smul_def, smul_eq_mul]
  refine ⟨c, hc_pos, fun S hS F => ?_⟩
  let e : E2 ≃ᵐ (ℝ × ℝ) := toE2.symm.toHomeomorph.toMeasurableEquiv
  have hS_pre : MeasurableSet (toE2 ⁻¹' S) := hS.preimage toE2.continuous.measurable
  have hind : (fun x : E2 => S.indicator F x) =
      fun x => (toE2 ⁻¹' S).indicator (fun p => F (toE2 p)) (e x) := by
    ext x
    have hre : toE2 (e x) = x := toE2.apply_symm_apply x
    by_cases hx : x ∈ S
    · simp [Set.indicator, hre, hx]
    · simp [Set.indicator, hre, hx]
  have h1 : ∫ x in S, F x = ∫ p in toE2 ⁻¹' S, F (toE2 p) ∂μ' := by
    rw [← MeasureTheory.integral_indicator hS, ← MeasureTheory.integral_indicator hS_pre, hind]
    exact (MeasureTheory.integral_map_equiv e
      ((toE2 ⁻¹' S).indicator (fun p => F (toE2 p)))).symm
  rw [h1, hμ'_eq, MeasureTheory.Measure.restrict_smul, MeasureTheory.integral_smul_measure,
    ENNReal.toReal_ofReal (le_of_lt hc_pos), smul_eq_mul]

lemma measurableSet_triInt {A B C : E2} (hdet : det2 (B - A) (C - A) ≠ 0) :
    MeasurableSet (triInt A B C) := by
  -- triInt A B C is open (the intersection of 3 strict half-planes!)
  set d := det2 (B - A) (C - A)
  have hEq : triInt A B C =
      {x : E2 | 0 < det2 (x - A) (C - A) / d} ∩
      {x : E2 | 0 < det2 (B - A) (x - A) / d} ∩
      {x : E2 | 0 < 1 - det2 (x - A) (C - A) / d - det2 (B - A) (x - A) / d} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, b, c, ha, hb, hc, hs, rfl⟩
      have hsub : a • A + b • B + c • C - A = b • (B - A) + c • (C - A) := by
        have : a = 1 - b - c := by linarith
        rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
      have h1 : det2 (a • A + b • B + c • C - A) (C - A) / d = b := by
        rw [hsub, det2_add_left, det2_smul_left, det2_smul_left, det2_self, mul_zero, add_zero,
          mul_div_cancel_right₀ _ hdet]
      have h2 : det2 (B - A) (a • A + b • B + c • C - A) / d = c := by
        rw [hsub, det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, zero_add,
          mul_div_cancel_right₀ _ hdet]
      rw [h1, h2]
      exact ⟨⟨hb, hc⟩, by linarith⟩
    · rintro ⟨⟨hb, hc⟩, ha⟩
      refine ⟨1 - det2 (x - A) (C - A) / d - det2 (B - A) (x - A) / d,
        det2 (x - A) (C - A) / d, det2 (B - A) (x - A) / d, ha, hb, hc, by ring, ?_⟩
      have hcr := cramer_e2 hdet (x - A)
      have h1 : x = A + (x - A) := by abel
      conv_lhs => rw [h1, hcr]
      simp only [d, sub_smul, one_smul, smul_sub]; abel
  rw [hEq]
  have hc1 : Continuous (fun x : E2 => det2 (x - A) (C - A) / d) := by
    unfold det2; fun_prop
  have hc2 : Continuous (fun x : E2 => det2 (B - A) (x - A) / d) := by
    unfold det2; fun_prop
  have hc3 : Continuous (fun x : E2 => 1 - det2 (x - A) (C - A) / d - det2 (B - A) (x - A) / d) := by
    fun_prop
  exact ((isOpen_lt continuous_const hc1).inter (isOpen_lt continuous_const hc2) |>.inter
    (isOpen_lt continuous_const hc3)).measurableSet

/-- Exact triangle integral parametrization `(lam, s) ∈ (0, 1)² ↦ C + s ((1 - lam)(P - C) + lam (Q - C))`. -/
lemma integral_tri_eq_iterated (C P Q : E2) (hdet : det2 (P - C) (Q - C) ≠ 0)
    (F : E2 → ℝ) (hF : Continuous F) :
    ∃ K > 0, ∫ x in tri C P Q, F x =
      K * ∫ lam in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
        s * F (C + s • ((1 - lam) • (P - C) + lam • (Q - C))) := by
  obtain ⟨c_haar, hc_pos, hhaar⟩ := exists_haar_factor_E2
  -- Replace tri by triInt (measure-0 boundary)
  have htri_eq : ∫ x in tri C P Q, F x = ∫ x in triInt C P Q, F x := by
    refine MeasureTheory.setIntegral_congr_set ?_
    rw [MeasureTheory.ae_eq_set]
    exact ⟨tri_diff_triInt_measure_zero hdet,
      by rw [Set.sdiff_eq_empty.mpr (triInt_subset_tri C P Q), measure_empty]⟩
  rw [htri_eq, hhaar (triInt C P Q) (measurableSet_triInt hdet)]
  set u := P - C
  set v := Q - C
  set sq : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1
  set Ψ : ℝ × ℝ → ℝ × ℝ := fun z =>
    (C 0 + z.2 * ((1 - z.1) * u 0 + z.1 * v 0),
     C 1 + z.2 * ((1 - z.1) * u 1 + z.1 * v 1))
  have hΨ_toE2 : ∀ z : ℝ × ℝ, toE2 (Ψ z) = C + z.2 • ((1 - z.1) • u + z.1 • v) := by
    intro z; apply e2_ext <;> (simp [Ψ]; ring)
  have hΨ_image : Ψ '' sq = toE2 ⁻¹' triInt C P Q := by
    ext p
    simp only [Set.mem_image, Set.mem_preimage, sq, Set.mem_prod, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨lam, s⟩, ⟨⟨hlam0, hlam1⟩, ⟨hs0, hs1⟩⟩, rfl⟩
      rw [hΨ_toE2]
      refine ⟨1 - s, s * (1 - lam), s * lam, by linarith, mul_pos hs0 (by linarith),
        mul_pos hs0 hlam0, by ring, ?_⟩
      simp only [u, v, smul_add, smul_sub, mul_sub, mul_one, sub_smul, one_smul, smul_smul]
      abel
    · intro hp
      obtain ⟨a, b, d, ha, hb, hd, habd, hEq⟩ := hp
      set s := b + d
      have hs0 : 0 < s := add_pos hb hd
      have hs1 : s < 1 := by linarith
      set lam := d / s
      have hlam0 : 0 < lam := div_pos hd hs0
      have hlam1 : lam < 1 := by rw [div_lt_one hs0]; linarith
      refine ⟨(lam, s), ⟨⟨hlam0, hlam1⟩, ⟨hs0, hs1⟩⟩, ?_⟩
      apply toE2.injective
      rw [hΨ_toE2, hEq]
      have ha_eq : a = 1 - s := by linarith
      have hsne : s ≠ 0 := ne_of_gt hs0
      have h1mlam : s * (1 - lam) = b := by simp only [lam, s]; field_simp; ring
      have hslam : s * lam = d := by simp only [lam, s]; field_simp
      rw [ha_eq, ← h1mlam, ← hslam]
      simp only [u, v, smul_add, smul_sub, mul_sub, mul_one, sub_smul, one_smul, smul_smul]
      abel
  have hΨ_inj : Set.InjOn Ψ sq := by
    rintro ⟨l₁, s₁⟩ ⟨⟨hl10, hl11⟩, ⟨hs10, hs11⟩⟩ ⟨l₂, s₂⟩ ⟨⟨hl20, hl21⟩, ⟨hs20, hs21⟩⟩ hEq
    have hE := congrArg toE2 hEq
    rw [hΨ_toE2, hΨ_toE2] at hE
    have hdiff : (s₁ * (1 - l₁) - s₂ * (1 - l₂)) • u + (s₁ * l₁ - s₂ * l₂) • v = 0 := by
      have h1 : s₁ • ((1 - l₁) • u + l₁ • v) = s₂ • ((1 - l₂) • u + l₂ • v) :=
        add_left_cancel hE
      rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul] at h1
      rw [sub_smul, sub_smul]
      have h2 := sub_eq_zero.mpr h1
      convert h2 using 1; abel
    obtain ⟨hc1, hc2⟩ := linear_combo_eq_zero_of_det2_ne_zero hdet hdiff
    have hs_eq : s₁ = s₂ := by linarith
    have hl_eq : l₁ = l₂ := by
      rw [hs_eq] at hc2
      have : s₂ * l₁ = s₂ * l₂ := by linarith
      exact mul_left_cancel₀ (ne_of_gt hs20) this
    exact Prod.ext hl_eq hs_eq
  -- Explicit Fréchet derivative of Ψ at (lam, s)
  let DΨ : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ × ℝ) := fun z =>
    LinearMap.toContinuousLinearMap
      { toFun := fun w =>
          (z.2 * (v 0 - u 0) * w.1 + ((1 - z.1) * u 0 + z.1 * v 0) * w.2,
           z.2 * (v 1 - u 1) * w.1 + ((1 - z.1) * u 1 + z.1 * v 1) * w.2)
        map_add' := fun w₁ w₂ => by ext <;> simp <;> ring
        map_smul' := fun r w => by ext <;> simp <;> ring }
  have hΨ_deriv : ∀ z ∈ sq, HasFDerivWithinAt Ψ (DΨ z) sq z := by
    intro z _
    have hfst := hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := z)
    have hsnd := hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := z)
    have h1 := (hasFDerivAt_const (1 : ℝ) z).sub hfst
    have hd1 := (hasFDerivAt_const (C 0) z).add (hsnd.mul ((h1.mul_const (u 0)).add (hfst.mul_const (v 0))))
    have hd2 := (hasFDerivAt_const (C 1) z).add (hsnd.mul ((h1.mul_const (u 1)).add (hfst.mul_const (v 1))))
    have hprod := (hd1.prodMk hd2).hasFDerivWithinAt (s := sq)
    refine (?_ : _ = DΨ z) ▸ hprod
    apply ContinuousLinearMap.ext
    rintro ⟨w₁, w₂⟩
    apply Prod.ext <;> (simp [DΨ]; ring)
  have hDΨ_det : ∀ z : ℝ × ℝ, (DΨ z).det = -z.2 * det2 u v := by
    intro z
    let e : (ℝ × ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
      { toFun := fun p => ![p.1, p.2]
        invFun := fun f => (f 0, f 1)
        map_add' := fun p q => by ext i; fin_cases i <;> simp
        map_smul' := fun r p => by ext i; fin_cases i <;> simp
        left_inv := fun p => by ext <;> simp
        right_inv := fun f => by ext i; fin_cases i <;> simp }
    let b : Module.Basis (Fin 2) ℝ (ℝ × ℝ) := Module.Basis.ofEquivFun e
    change LinearMap.det (DΨ z).toLinearMap = -z.2 * det2 u v
    rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, b, Module.Basis.coe_ofEquivFun,
      Module.Basis.ofEquivFun_repr_apply, e, LinearEquiv.coe_mk, LinearEquiv.coe_symm_mk,
      LinearMap.coe_mk, AddHom.coe_mk, DΨ, ContinuousLinearMap.coe_coe,
      LinearMap.coe_toContinuousLinearMap']
    simp [det2]
    ring
  rw [← hΨ_image]
  have hchg := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
    (volume : Measure (ℝ × ℝ)) (measurableSet_Ioo.prod measurableSet_Ioo) hΨ_deriv hΨ_inj
    (fun p => F (toE2 p))
  rw [hchg]
  have hcongr : ∫ z in sq, |(DΨ z).det| • F (toE2 (Ψ z)) =
      |det2 u v| * ∫ z in sq, z.2 * F (C + z.2 • ((1 - z.1) • u + z.1 • v)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) fun z hz => ?_
    rw [hDΨ_det z, hΨ_toE2 z, smul_eq_mul, abs_mul, abs_neg, abs_of_pos hz.2.1]
    ring
  rw [hcongr]
  have hprod_int : IntegrableOn (fun z : ℝ × ℝ => z.2 * F (C + z.2 • ((1 - z.1) • u + z.1 • v))) sq volume := by
    have hcont : Continuous (fun z : ℝ × ℝ => z.2 * F (C + z.2 • ((1 - z.1) • u + z.1 • v))) := by
      fun_prop
    exact (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hfub := MeasureTheory.setIntegral_prod
    (f := fun z : ℝ × ℝ => z.2 * F (C + z.2 • ((1 - z.1) • u + z.1 • v)))
    (s := Ioo (0 : ℝ) 1) (t := Ioo (0 : ℝ) 1) hprod_int
  have hIoo_eq : ∀ g : ℝ → ℝ, ∫ x in Ioo (0 : ℝ) 1, g x = ∫ x in (0 : ℝ)..1, g x := fun g => by
    rw [intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  refine ⟨c_haar * |det2 u v|, mul_pos hc_pos (abs_pos.mpr hdet), ?_⟩
  change c_haar * (|det2 u v| * ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
    z.2 * F (C + z.2 • ((1 - z.1) • u + z.1 • v)) ∂volume.prod volume) = _
  rw [hfub]
  simp_rw [hIoo_eq]
  ring

/-- Basic Gaussian positivity and affine functional evaluation at `center A B C`. -/
lemma continuous_gamma : Continuous OMA.S_mo_499635.γ := by
  unfold OMA.S_mo_499635.γ; fun_prop

lemma gamma_pos (x : E2) : 0 < OMA.S_mo_499635.γ x := Real.exp_pos _

lemma integral_tri_pos_of_pos_on_triInt {A B C : E2} (hdet : det2 (B - A) (C - A) ≠ 0)
    {F : E2 → ℝ} (hF : Continuous F) (hpos : ∀ x ∈ triInt A B C, 0 < F x) :
    0 < ∫ x in tri A B C, F x := by
  obtain ⟨K, hK, heq⟩ := integral_tri_eq_iterated A B C hdet F hF
  rw [heq]
  refine mul_pos hK ?_
  have hcont2 : Continuous (fun p : ℝ × ℝ =>
      p.2 * F (A + p.2 • ((1 - p.1) • (B - A) + p.1 • (C - A)))) := by fun_prop
  have hpt_pos : ∀ lam ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Ioo (0 : ℝ) 1,
      0 < s * F (A + s • ((1 - lam) • (B - A) + lam • (C - A))) := by
    intro lam hlam s hs
    refine mul_pos hs.1 (hpos _ ?_)
    refine ⟨1 - s, s * (1 - lam), s * lam, by linarith [hs.2],
      mul_pos hs.1 (by linarith [hlam.2]), mul_pos hs.1 hlam.1, by ring, ?_⟩
    simp only [smul_add, smul_sub, mul_sub, mul_one, sub_smul, one_smul, smul_smul]; abel
  have hpt_nn : ∀ lam ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      0 ≤ s * F (A + s • ((1 - lam) • (B - A) + lam • (C - A))) := by
    intro lam hlam s hs
    have hmem : A + s • ((1 - lam) • (B - A) + lam • (C - A)) ∈ closure (triInt A B C) := by
      have hseq : Tendsto (fun n : ℕ =>
          let lam' := (lam + 1 / (n + 2 : ℝ)) / (1 + 2 / (n + 2 : ℝ))
          let s' := (s + 1 / (n + 2 : ℝ)) / (1 + 2 / (n + 2 : ℝ))
          A + s' • ((1 - lam') • (B - A) + lam' • (C - A)))
          atTop (𝓝 (A + s • ((1 - lam) • (B - A) + lam • (C - A)))) := by
        have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 2 : ℝ)) atTop (𝓝 0) := by
          have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have h := h0.comp (tendsto_add_atTop_nat 1)
          refine h.congr fun n => ?_
          simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
          ring
        have hden : Tendsto (fun n : ℕ => 1 + 2 / (n + 2 : ℝ)) atTop (𝓝 1) := by
          have h1 : Tendsto (fun n : ℕ => 1 + (2 : ℝ) * ((1 : ℝ) / (n + 2 : ℝ))) atTop (𝓝 (1 + (2 : ℝ) * 0)) :=
            tendsto_const_nhds.add (hinv.const_mul (2 : ℝ))
          rw [mul_zero, add_zero] at h1
          exact h1.congr fun n => by ring
        have hlam_t : Tendsto (fun n : ℕ => (lam + 1 / (n + 2 : ℝ)) / (1 + 2 / (n + 2 : ℝ)))
            atTop (𝓝 lam) := by
          have hnum : Tendsto (fun n : ℕ => lam + 1 / (n + 2 : ℝ)) atTop (𝓝 lam) := by
            have h := tendsto_const_nhds (x := lam).add hinv
            rwa [add_zero] at h
          have h := hnum.div hden one_ne_zero
          rw [div_one] at h
          exact h
        have hs_t : Tendsto (fun n : ℕ => (s + 1 / (n + 2 : ℝ)) / (1 + 2 / (n + 2 : ℝ)))
            atTop (𝓝 s) := by
          have hnum : Tendsto (fun n : ℕ => s + 1 / (n + 2 : ℝ)) atTop (𝓝 s) := by
            have h := tendsto_const_nhds (x := s).add hinv
            rwa [add_zero] at h
          have h := hnum.div hden one_ne_zero
          rw [div_one] at h
          exact h
        exact tendsto_const_nhds.add (hs_t.smul (((tendsto_const_nhds.sub hlam_t).smul tendsto_const_nhds).add
          (hlam_t.smul tendsto_const_nhds)))
      refine mem_closure_of_tendsto hseq (Filter.Eventually.of_forall fun n => ?_)
      have hn : (0 : ℝ) < (n + 2 : ℝ) := by positivity
      have hden : 0 < 1 + 2 / (n + 2 : ℝ) := by positivity
      have h12 : (1 : ℝ) / (n + 2 : ℝ) < 2 / (n + 2 : ℝ) := by
        exact div_lt_div_of_pos_right one_lt_two hn
      set lam' := (lam + 1 / (n + 2 : ℝ)) / (1 + 2 / (n + 2 : ℝ))
      set s' := (s + 1 / (n + 2 : ℝ)) / (1 + 2 / (n + 2 : ℝ))
      have hl0 : 0 < lam' := div_pos (by linarith [hlam.1, div_pos one_pos hn]) hden
      have hl1 : lam' < 1 := by
        rw [div_lt_one hden]; linarith [hlam.2, h12]
      have hs0 : 0 < s' := div_pos (by linarith [hs.1, div_pos one_pos hn]) hden
      have hs1 : s' < 1 := by
        rw [div_lt_one hden]; linarith [hs.2, h12]
      refine ⟨1 - s', s' * (1 - lam'), s' * lam', by linarith, mul_pos hs0 (by linarith),
        mul_pos hs0 hl0, by ring, ?_⟩
      simp only [smul_add, smul_sub, mul_sub, mul_one, sub_smul, one_smul, smul_smul]; abel
    have hFnn : 0 ≤ F (A + s • ((1 - lam) • (B - A) + lam • (C - A))) := by
      have hcl : F '' closure (triInt A B C) ⊆ closure (F '' triInt A B C) :=
        image_closure_subset_closure_image hF
      have hmem2 := hcl ⟨_, hmem, rfl⟩
      have hsub : F '' triInt A B C ⊆ Ici 0 := by rintro _ ⟨y, hy, rfl⟩; exact le_of_lt (hpos y hy)
      exact (isClosed_Ici.closure_subset_iff.mpr hsub) hmem2
    exact mul_nonneg hs.1 hFnn
  refine intervalIntegral.integral_pos zero_lt_one
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont2 0 1).continuousOn
    (fun lam hlam => intervalIntegral.integral_nonneg zero_le_one fun s hs =>
      hpt_nn lam ⟨le_of_lt hlam.1, hlam.2⟩ s hs)
    ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
  refine intervalIntegral.integral_pos zero_lt_one
    (hcont2.comp (continuous_const.prodMk continuous_id)).continuousOn
    (fun s hs => hpt_nn (1 / 2) ⟨by norm_num, by norm_num⟩ s ⟨le_of_lt hs.1, hs.2⟩)
    ⟨1 / 2, ⟨by norm_num, by norm_num⟩, hpt_pos (1 / 2) ⟨by norm_num, by norm_num⟩
      (1 / 2) ⟨by norm_num, by norm_num⟩⟩

lemma integral_gamma_pos {A B C : E2} (hdet : det2 (B - A) (C - A) ≠ 0) :
    0 < ∫ x in tri A B C, OMA.S_mo_499635.γ x :=
  integral_tri_pos_of_pos_on_triInt hdet continuous_gamma fun x _ => gamma_pos x

/-- For any continuous linear functional `L : E2 →L[ℝ] ℝ` and constant `r`,
`∫_T (L x + r) γ(x) = (L (center A B C) + r) * ∫_T γ(x)`. -/
lemma integral_affine_gamma_eq (A B C : E2) (hdet : det2 (B - A) (C - A) ≠ 0)
    (L : E2 →L[ℝ] ℝ) (r : ℝ) :
    ∫ x in tri A B C, (L x + r) * OMA.S_mo_499635.γ x =
      (L (OMA.S_mo_499635.center A B C) + r) * ∫ x in tri A B C, OMA.S_mo_499635.γ x := by
  have hint_vec : IntegrableOn (fun x : E2 => OMA.S_mo_499635.γ x • x) (tri A B C) volume :=
    (continuous_gamma.smul continuous_id).continuousOn.integrableOn_compact (isCompact_tri A B C)
  have hint_g : IntegrableOn OMA.S_mo_499635.γ (tri A B C) volume :=
    continuous_gamma.continuousOn.integrableOn_compact (isCompact_tri A B C)
  have hL_int : L (∫ x in tri A B C, OMA.S_mo_499635.γ x • x) =
      ∫ x in tri A B C, L (OMA.S_mo_499635.γ x • x) :=
    (L.integral_comp_comm hint_vec).symm
  have hrew : (fun x : E2 => (L x + r) * OMA.S_mo_499635.γ x) =
      fun x => L (OMA.S_mo_499635.γ x • x) + r * OMA.S_mo_499635.γ x := by
    ext x; rw [map_smul, smul_eq_mul]; ring
  rw [hrew, MeasureTheory.integral_add (L.integrable_comp hint_vec) (hint_g.const_mul r),
    ← hL_int, MeasureTheory.integral_const_mul]
  unfold OMA.S_mo_499635.center
  rw [map_smul, smul_eq_mul]
  have hZne : (∫ x in tri A B C, OMA.S_mo_499635.γ x) ≠ 0 :=
    ne_of_gt (integral_gamma_pos hdet)
  change _ = _ * ∫ x in tri A B C, OMA.S_mo_499635.γ x
  have hZ : ∫ x in convexHull ℝ {A, B, C}, OMA.S_mo_499635.γ x =
      ∫ x in tri A B C, OMA.S_mo_499635.γ x := rfl
  have hV : ∫ x in convexHull ℝ {A, B, C}, OMA.S_mo_499635.γ x • x =
      ∫ x in tri A B C, OMA.S_mo_499635.γ x • x := rfl
  rw [hZ, hV]
  field_simp

lemma affine_pos_at_center {A B C : E2} (hdet : det2 (B - A) (C - A) ≠ 0)
    (L : E2 →L[ℝ] ℝ) (r : ℝ) (hpos : ∀ x ∈ triInt A B C, 0 < L x + r) :
    0 < L (OMA.S_mo_499635.center A B C) + r := by
  have hI : 0 < ∫ x in tri A B C, (L x + r) * OMA.S_mo_499635.γ x :=
    integral_tri_pos_of_pos_on_triInt hdet
      ((L.continuous.add continuous_const).mul continuous_gamma)
      fun x hx => mul_pos (hpos x hx) (gamma_pos x)
  rw [integral_affine_gamma_eq A B C hdet L r] at hI
  exact pos_of_mul_pos_left hI (le_of_lt (integral_gamma_pos hdet))

/-- The Gaussian center of a nondegenerate triangle lies strictly inside its interior `triInt`. -/
lemma center_mem_triInt {A B C : E2} (hdet : det2 (B - A) (C - A) ≠ 0) :
    OMA.S_mo_499635.center A B C ∈ triInt A B C := by
  set M := OMA.S_mo_499635.center A B C
  set d := det2 (B - A) (C - A)
  -- Barycentric coordinates of x in (A, B, C):
  --   b(x) = det2 (x - A) (C - A) / d,  c(x) = det2 (B - A) (x - A) / d,  a(x) = 1 - b(x) - c(x)
  let Lb : E2 →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun x => det2 x (C - A) / d
      map_add' := fun x y => by rw [det2_add_left, add_div]
      map_smul' := fun r x => by rw [det2_smul_left]; simp [mul_div_assoc] }
  let Lc : E2 →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun x => det2 (B - A) x / d
      map_add' := fun x y => by rw [det2_add_right, add_div]
      map_smul' := fun r x => by rw [det2_smul_right]; simp [mul_div_assoc] }
  have hb_val : ∀ x : E2, Lb x + (-Lb A) = det2 (x - A) (C - A) / d := by
    intro x
    simp only [Lb, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    rw [det2_sub_left]; ring
  have hc_val : ∀ x : E2, Lc x + (-Lc A) = det2 (B - A) (x - A) / d := by
    intro x
    simp only [Lc, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    rw [det2_sub_right]; ring
  have ha_val : ∀ x : E2, (-(Lb + Lc)) x + (1 + Lb A + Lc A) =
      1 - det2 (x - A) (C - A) / d - det2 (B - A) (x - A) / d := by
    intro x
    have h1 := hb_val x
    have h2 := hc_val x
    simp only [FunLike.coe_neg, FunLike.coe_add, Pi.neg_apply, Pi.add_apply]
    linarith
  have hb_pos : 0 < det2 (M - A) (C - A) / d := by
    rw [← hb_val M]
    refine affine_pos_at_center hdet Lb (-Lb A) fun x hx => ?_
    rw [hb_val x]
    obtain ⟨a, b, c, ha, hb, hc, habc, rfl⟩ := hx
    have hsub : a • A + b • B + c • C - A = b • (B - A) + c • (C - A) := by
      have ha1 : a = 1 - b - c := by linarith
      rw [ha1]; simp only [sub_smul, one_smul, smul_sub]; abel
    rw [hsub, det2_add_left, det2_smul_left, det2_smul_left, det2_self, mul_zero, add_zero,
      mul_div_cancel_right₀ _ hdet]
    exact hb
  have hc_pos : 0 < det2 (B - A) (M - A) / d := by
    rw [← hc_val M]
    refine affine_pos_at_center hdet Lc (-Lc A) fun x hx => ?_
    rw [hc_val x]
    obtain ⟨a, b, c, ha, hb, hc, habc, rfl⟩ := hx
    have hsub : a • A + b • B + c • C - A = b • (B - A) + c • (C - A) := by
      have ha1 : a = 1 - b - c := by linarith
      rw [ha1]; simp only [sub_smul, one_smul, smul_sub]; abel
    rw [hsub, det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, zero_add,
      mul_div_cancel_right₀ _ hdet]
    exact hc
  have ha_pos : 0 < 1 - det2 (M - A) (C - A) / d - det2 (B - A) (M - A) / d := by
    rw [← ha_val M]
    refine affine_pos_at_center hdet (-(Lb + Lc)) (1 + Lb A + Lc A) fun x hx => ?_
    rw [ha_val x]
    obtain ⟨a, b, c, ha, hb, hc, habc, rfl⟩ := hx
    have hsub : a • A + b • B + c • C - A = b • (B - A) + c • (C - A) := by
      have ha1 : a = 1 - b - c := by linarith
      rw [ha1]; simp only [sub_smul, one_smul, smul_sub]; abel
    rw [hsub, det2_add_left, det2_smul_left, det2_smul_left, det2_self, mul_zero, add_zero,
      mul_div_cancel_right₀ _ hdet,
      det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, zero_add,
      mul_div_cancel_right₀ _ hdet]
    linarith
  refine ⟨1 - det2 (M - A) (C - A) / d - det2 (B - A) (M - A) / d,
    det2 (M - A) (C - A) / d, det2 (B - A) (M - A) / d, ha_pos, hb_pos, hc_pos, by ring, ?_⟩
  have hcr := cramer_e2 hdet (M - A)
  have h1 : M = A + (M - A) := by abel
  conv_lhs => rw [h1, hcr]
  simp only [d, sub_smul, one_smul, smul_sub]
  abel

/-! #### Part 2: Strictly Nested Case (`C ∈ triInt A B C'`) -/

lemma norm_add_lt_of_det2_ne_zero {v₁ v₂ : E2} (hdet12 : det2 v₁ v₂ ≠ 0) :
    ‖v₁ + v₂‖ < ‖v₁‖ + ‖v₂‖ := by
  have hsq : ‖v₁ + v₂‖ ^ 2 < (‖v₁‖ + ‖v₂‖) ^ 2 := by
    have h1 : ‖v₁ + v₂‖ ^ 2 = (v₁ 0 + v₂ 0) ^ 2 + (v₁ 1 + v₂ 1) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]; simp [Real.norm_eq_abs]
    have h2 : ‖v₁‖ ^ 2 = v₁ 0 ^ 2 + v₁ 1 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]; simp [Real.norm_eq_abs]
    have h3 : ‖v₂‖ ^ 2 = v₂ 0 ^ 2 + v₂ 1 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]; simp [Real.norm_eq_abs]
    have hcs : (v₁ 0 * v₂ 0 + v₁ 1 * v₂ 1) ^ 2 < (v₁ 0 ^ 2 + v₁ 1 ^ 2) * (v₂ 0 ^ 2 + v₂ 1 ^ 2) := by
      have hid : (v₁ 0 ^ 2 + v₁ 1 ^ 2) * (v₂ 0 ^ 2 + v₂ 1 ^ 2) - (v₁ 0 * v₂ 0 + v₁ 1 * v₂ 1) ^ 2 =
          det2 v₁ v₂ ^ 2 := by unfold det2; ring
      have hd2 : 0 < det2 v₁ v₂ ^ 2 := sq_pos_of_ne_zero hdet12
      linarith only [hid, hd2]
    have hprod : v₁ 0 * v₂ 0 + v₁ 1 * v₂ 1 < ‖v₁‖ * ‖v₂‖ := by
      have hnn : 0 ≤ ‖v₁‖ * ‖v₂‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have hsq2 : (v₁ 0 * v₂ 0 + v₁ 1 * v₂ 1) ^ 2 < (‖v₁‖ * ‖v₂‖) ^ 2 := by
        rw [mul_pow, h2, h3]; exact hcs
      nlinarith only [hsq2, hnn]
    nlinarith only [h1, h2, h3, hprod]
  nlinarith only [hsq, norm_nonneg (v₁ + v₂), norm_nonneg v₁, norm_nonneg v₂]

lemma tri_partition_of_mem_triInt {A B C C' : E2}
    (hdet_CAB : det2 (A - C) (B - C) ≠ 0)
    (hdet_CAC' : det2 (A - C) (C' - C) ≠ 0)
    (hdet_CBC' : det2 (B - C) (C' - C) ≠ 0)
    {α β δ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ) (hsum : α + β + δ = 1)
    (hC_eq : C = α • A + β • B + δ • C')
    (hCp_eq : C' - C = (-α / δ) • (A - C) + (-β / δ) • (B - C)) :
    tri A B C' = tri C A B ∪ (tri C A C' ∪ tri C B C') ∧
    AEDisjoint volume (tri C A C') (tri C B C') ∧
    AEDisjoint volume (tri C A B) (tri C A C' ∪ tri C B C') := by
  let xcoord : E2 → ℝ := fun v => det2 v (B - C) / det2 (A - C) (B - C)
  let ycoord : E2 → ℝ := fun v => det2 (A - C) v / det2 (A - C) (B - C)
  have hxy_add : ∀ v₁ v₂, xcoord (v₁ + v₂) = xcoord v₁ + xcoord v₂ ∧
      ycoord (v₁ + v₂) = ycoord v₁ + ycoord v₂ := fun v₁ v₂ => by
    constructor <;> simp only [xcoord, ycoord, det2_add_left, det2_add_right, add_div]
  have hxy_smul : ∀ r v, xcoord (r • v) = r * xcoord v ∧ ycoord (r • v) = r * ycoord v :=
    fun r v => by
      constructor <;> simp only [xcoord, ycoord, det2_smul_left, det2_smul_right, mul_div_assoc]
  have hxy_AC : xcoord (A - C) = 1 ∧ ycoord (A - C) = 0 := by
    constructor <;> simp only [xcoord, ycoord, div_self hdet_CAB, det2_self, zero_div]
  have hxy_BC : xcoord (B - C) = 0 ∧ ycoord (B - C) = 1 := by
    constructor <;> simp only [xcoord, ycoord, div_self hdet_CAB, det2_self, zero_div]
  have hxy_CpC : xcoord (C' - C) = -α / δ ∧ ycoord (C' - C) = -β / δ := by
    rw [hCp_eq]
    have ha1 := hxy_add ((-α / δ) • (A - C)) ((-β / δ) • (B - C))
    rw [ha1.1, ha1.2, (hxy_smul _ _).1, (hxy_smul _ _).2, (hxy_smul _ _).1, (hxy_smul _ _).2,
      hxy_AC.1, hxy_AC.2, hxy_BC.1, hxy_BC.2]
    exact ⟨by ring, by ring⟩
  have hpart : tri A B C' = tri C A B ∪ (tri C A C' ∪ tri C B C') := by
    ext x
    constructor
    · intro hx
      rw [mem_tri_iff] at hx
      obtain ⟨p, q, r, hp, hq, hr, hpqr, rfl⟩ := hx
      set t := min (p / α) (min (q / β) (r / δ))
      have ht_nn : 0 ≤ t := le_min (div_nonneg hp (le_of_lt hα))
        (le_min (div_nonneg hq (le_of_lt hβ)) (div_nonneg hr (le_of_lt hδ)))
      have ht_le_p : t ≤ p / α := min_le_left _ _
      have ht_le_q : t ≤ q / β := le_trans (min_le_right _ _) (min_le_left _ _)
      have ht_le_r : t ≤ r / δ := le_trans (min_le_right _ _) (min_le_right _ _)
      have hp' : 0 ≤ p - t * α := by
        have := mul_le_mul_of_nonneg_right ht_le_p (le_of_lt hα)
        rw [div_mul_cancel₀ _ (ne_of_gt hα)] at this; linarith
      have hq' : 0 ≤ q - t * β := by
        have := mul_le_mul_of_nonneg_right ht_le_q (le_of_lt hβ)
        rw [div_mul_cancel₀ _ (ne_of_gt hβ)] at this; linarith
      have hr' : 0 ≤ r - t * δ := by
        have := mul_le_mul_of_nonneg_right ht_le_r (le_of_lt hδ)
        rw [div_mul_cancel₀ _ (ne_of_gt hδ)] at this; linarith
      have hdecomp_x : p • A + q • B + r • C' =
          t • C + (p - t * α) • A + (q - t * β) • B + (r - t * δ) • C' := by
        rw [hC_eq]; simp only [smul_add, smul_smul, sub_smul]; abel
      rcases le_total (p / α) (min (q / β) (r / δ)) with h1 | h1
      · have ht_eq : t = p / α := min_eq_left h1
        have hp0 : p - t * α = 0 := by rw [ht_eq, div_mul_cancel₀ _ (ne_of_gt hα), sub_self]
        right; right
        rw [mem_tri_iff]
        refine ⟨t, q - t * β, r - t * δ, ht_nn, hq', hr', by linear_combination hpqr - t * hsum - hp0, ?_⟩
        rw [hdecomp_x, hp0, zero_smul, add_zero]
      · have ht_eq : t = min (q / β) (r / δ) := min_eq_right h1
        rcases le_total (q / β) (r / δ) with h2 | h2
        · have ht_eq2 : t = q / β := by rw [ht_eq, min_eq_left h2]
          have hq0 : q - t * β = 0 := by rw [ht_eq2, div_mul_cancel₀ _ (ne_of_gt hβ), sub_self]
          right; left
          rw [mem_tri_iff]
          refine ⟨t, p - t * α, r - t * δ, ht_nn, hp', hr', by linear_combination hpqr - t * hsum - hq0, ?_⟩
          rw [hdecomp_x, hq0, zero_smul, add_zero]
        · have ht_eq2 : t = r / δ := by rw [ht_eq, min_eq_right h2]
          have hr0 : r - t * δ = 0 := by rw [ht_eq2, div_mul_cancel₀ _ (ne_of_gt hδ), sub_self]
          left
          rw [mem_tri_iff]
          refine ⟨t, p - t * α, q - t * β, ht_nn, hp', hq', by linear_combination hpqr - t * hsum - hr0, ?_⟩
          rw [hdecomp_x, hr0, zero_smul, add_zero]
    · intro hx
      have hC_mem : C ∈ tri A B C' := triInt_subset_tri A B C' ⟨α, β, δ, hα, hβ, hδ, hsum, hC_eq⟩
      have hA_mem : A ∈ tri A B C' := subset_convexHull ℝ _ (by simp)
      have hB_mem : B ∈ tri A B C' := subset_convexHull ℝ _ (by simp)
      have hCp_mem : C' ∈ tri A B C' := subset_convexHull ℝ _ (by simp)
      have hconv := convex_convexHull ℝ ({A, B, C'} : Set E2)
      rcases hx with hx | hx | hx
      · exact convexHull_min (by intro y hy; rcases hy with rfl | rfl | rfl <;> assumption) hconv hx
      · exact convexHull_min (by intro y hy; rcases hy with rfl | rfl | rfl <;> assumption) hconv hx
      · exact convexHull_min (by intro y hy; rcases hy with rfl | rfl | rfl <;> assumption) hconv hx
  have hdisj_12 : AEDisjoint volume (tri C A C') (tri C B C') := by
    change volume (tri C A C' ∩ tri C B C') = 0
    have hsub : tri C A C' ∩ tri C B C' ⊆
        (tri C A C' \ triInt C A C') ∪ (tri C B C' \ triInt C B C') := by
      rintro x ⟨h1, h2⟩
      by_contra hnot
      simp only [Set.mem_union, Set.mem_sdiff, not_or, not_and, not_not] at hnot
      obtain ⟨a₁, b₁, c₁, ha₁, hb₁, hc₁, hs1, heq1⟩ := hnot.1 h1
      obtain ⟨a₂, b₂, c₂, ha₂, hb₂, hc₂, hs2, heq2⟩ := hnot.2 h2
      have hsub1 : x - C = b₁ • (A - C) + c₁ • (C' - C) := by
        rw [heq1]; have : a₁ = 1 - b₁ - c₁ := by linarith
        rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
      have hsub2 : x - C = b₂ • (B - C) + c₂ • (C' - C) := by
        rw [heq2]; have : a₂ = 1 - b₂ - c₂ := by linarith
        rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
      have hdet1 : det2 (x - C) (C' - C) = b₁ * det2 (A - C) (C' - C) := by
        rw [hsub1, det2_add_left, det2_smul_left, det2_smul_left, det2_self, mul_zero, add_zero]
      have hdet2 : det2 (x - C) (C' - C) = b₂ * det2 (B - C) (C' - C) := by
        rw [hsub2, det2_add_left, det2_smul_left, det2_smul_left, det2_self, mul_zero, add_zero]
      have hrel : det2 (A - C) (C' - C) = (-β / δ) * det2 (A - C) (B - C) := by
        rw [hCp_eq, det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, zero_add]
      have hrel2 : det2 (B - C) (C' - C) = (α / δ) * det2 (A - C) (B - C) := by
        rw [hCp_eq, det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, add_zero,
          det2_antisymm (B - C) (A - C)]
        ring
      have hEq : (b₁ * (-β / δ) - b₂ * (α / δ)) * det2 (A - C) (B - C) = 0 := by
        have : b₁ * ((-β / δ) * det2 (A - C) (B - C)) = b₂ * ((α / δ) * det2 (A - C) (B - C)) := by
          rw [← hrel, ← hrel2, ← hdet1, ← hdet2]
        linarith
      have h0 : b₁ * (-β / δ) - b₂ * (α / δ) = 0 := (mul_eq_zero.mp hEq).resolve_right hdet_CAB
      have hneg1 : b₁ * (-β / δ) < 0 := mul_neg_of_pos_of_neg hb₁ (div_neg_of_neg_of_pos (by linarith) hδ)
      have hpos2 : 0 < b₂ * (α / δ) := mul_pos hb₂ (div_pos hα hδ)
      linarith
    exact measure_mono_null hsub (measure_union_null (tri_diff_triInt_measure_zero hdet_CAC')
      (tri_diff_triInt_measure_zero hdet_CBC'))
  have hdisj_01 : AEDisjoint volume (tri C A B) (tri C A C') := by
    change volume (tri C A B ∩ tri C A C') = 0
    have hsub : tri C A B ∩ tri C A C' ⊆
        (tri C A B \ triInt C A B) ∪ (tri C A C' \ triInt C A C') := by
      rintro x ⟨h1, h2⟩
      by_contra hnot
      simp only [Set.mem_union, Set.mem_sdiff, not_or, not_and, not_not] at hnot
      obtain ⟨a₁, b₁, c₁, ha₁, hb₁, hc₁, hs1, heq1⟩ := hnot.1 h1
      obtain ⟨a₂, b₂, c₂, ha₂, hb₂, hc₂, hs2, heq2⟩ := hnot.2 h2
      have hsub1 : x - C = b₁ • (A - C) + c₁ • (B - C) := by
        rw [heq1]; have : a₁ = 1 - b₁ - c₁ := by linarith
        rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
      have hsub2 : x - C = b₂ • (A - C) + c₂ • (C' - C) := by
        rw [heq2]; have : a₂ = 1 - b₂ - c₂ := by linarith
        rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
      have hy1 : ycoord (x - C) = c₁ := by
        rw [hsub1, (hxy_add _ _).2, (hxy_smul _ _).2, (hxy_smul _ _).2, hxy_AC.2, hxy_BC.2]; ring
      have hy2 : ycoord (x - C) = c₂ * (-β / δ) := by
        rw [hsub2, (hxy_add _ _).2, (hxy_smul _ _).2, (hxy_smul _ _).2, hxy_AC.2, hxy_CpC.2]; ring
      have : c₂ * (-β / δ) < 0 := mul_neg_of_pos_of_neg hc₂ (div_neg_of_neg_of_pos (by linarith) hδ)
      linarith
    exact measure_mono_null hsub (measure_union_null (tri_diff_triInt_measure_zero hdet_CAB)
      (tri_diff_triInt_measure_zero hdet_CAC'))
  have hdisj_02 : AEDisjoint volume (tri C A B) (tri C B C') := by
    change volume (tri C A B ∩ tri C B C') = 0
    have hsub : tri C A B ∩ tri C B C' ⊆
        (tri C A B \ triInt C A B) ∪ (tri C B C' \ triInt C B C') := by
      rintro x ⟨h1, h2⟩
      by_contra hnot
      simp only [Set.mem_union, Set.mem_sdiff, not_or, not_and, not_not] at hnot
      obtain ⟨a₁, b₁, c₁, ha₁, hb₁, hc₁, hs1, heq1⟩ := hnot.1 h1
      obtain ⟨a₂, b₂, c₂, ha₂, hb₂, hc₂, hs2, heq2⟩ := hnot.2 h2
      have hsub1 : x - C = b₁ • (A - C) + c₁ • (B - C) := by
        rw [heq1]; have : a₁ = 1 - b₁ - c₁ := by linarith
        rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
      have hsub2 : x - C = b₂ • (B - C) + c₂ • (C' - C) := by
        rw [heq2]; have : a₂ = 1 - b₂ - c₂ := by linarith
        rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
      have hx1 : xcoord (x - C) = b₁ := by
        rw [hsub1, (hxy_add _ _).1, (hxy_smul _ _).1, (hxy_smul _ _).1, hxy_AC.1, hxy_BC.1]; ring
      have hx2 : xcoord (x - C) = c₂ * (-α / δ) := by
        rw [hsub2, (hxy_add _ _).1, (hxy_smul _ _).1, (hxy_smul _ _).1, hxy_BC.1, hxy_CpC.1]; ring
      have : c₂ * (-α / δ) < 0 := mul_neg_of_pos_of_neg hc₂ (div_neg_of_neg_of_pos (by linarith) hδ)
      linarith
    exact measure_mono_null hsub (measure_union_null (tri_diff_triInt_measure_zero hdet_CAB)
      (tri_diff_triInt_measure_zero hdet_CBC'))
  have hdisj_0_12 : AEDisjoint volume (tri C A B) (tri C A C' ∪ tri C B C') := by
    change volume (tri C A B ∩ (tri C A C' ∪ tri C B C')) = 0
    rw [Set.inter_union_distrib_left]
    exact measure_union_null hdisj_01 hdisj_02
  exact ⟨hpart, hdisj_12, hdisj_0_12⟩

lemma tri_ray_integral_pos {C P Q : E2} (hdet : det2 (P - C) (Q - C) ≠ 0)
    {F : E2 → ℝ} (hF : Continuous F)
    (hinner : ∀ lam ∈ Ioo (0 : ℝ) 1,
      0 < ∫ s in (0 : ℝ)..1, s * F (C + s • ((1 - lam) • (P - C) + lam • (Q - C)))) :
    0 < ∫ x in tri C P Q, F x := by
  obtain ⟨K, hK, heq⟩ := integral_tri_eq_iterated C P Q hdet F hF
  rw [heq]
  refine mul_pos hK ?_
  have hcont2 : Continuous (fun p : ℝ × ℝ =>
      p.2 * F (C + p.2 • ((1 - p.1) • (P - C) + p.1 • (Q - C)))) := by
    have := hF; fun_prop
  have houter_cont : Continuous (fun lam : ℝ =>
      ∫ s in (0 : ℝ)..1, s * F (C + s • ((1 - lam) • (P - C) + lam • (Q - C)))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont2 0 1
  refine intervalIntegral.integral_pos zero_lt_one houter_cont.continuousOn ?_
    ⟨1 / 2, ⟨by norm_num, by norm_num⟩, hinner (1 / 2) ⟨by norm_num, by norm_num⟩⟩
  intro lam hlam
  rcases eq_or_lt_of_le hlam.2 with rfl | hlt
  · have hlim : Tendsto (fun x : ℝ =>
        ∫ s in (0 : ℝ)..1, s * F (C + s • ((1 - x) • (P - C) + x • (Q - C))))
        (𝓝[<] 1) (𝓝 _) := houter_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsLT zero_lt_one)
      fun x hx => le_of_lt (hinner x hx))
  · exact le_of_lt (hinner lam ⟨hlam.1, hlt⟩)

lemma tri_ray_integral_neg {C P Q : E2} (hdet : det2 (P - C) (Q - C) ≠ 0)
    {F : E2 → ℝ} (hF : Continuous F)
    (hinner : ∀ lam ∈ Ioo (0 : ℝ) 1,
      ∫ s in (0 : ℝ)..1, s * F (C + s • ((1 - lam) • (P - C) + lam • (Q - C))) < 0) :
    ∫ x in tri C P Q, F x < 0 := by
  have hp : 0 < ∫ x in tri C P Q, -F x := by
    refine tri_ray_integral_pos hdet hF.neg fun lam hlam => ?_
    have hrew : (fun s : ℝ => s * -F (C + s • ((1 - lam) • (P - C) + lam • (Q - C)))) =
        fun s => -(s * F (C + s • ((1 - lam) • (P - C) + lam • (Q - C)))) := by ext s; ring
    rw [hrew, intervalIntegral.integral_neg]
    exact neg_pos.mpr (hinner lam hlam)
  rw [MeasureTheory.integral_neg] at hp
  linarith

lemma nested_gauge_exists {A B C C' : E2} (hdet_CAB : det2 (A - C) (B - C) ≠ 0)
    {α β δ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ) (hsum : α + β + δ = 1)
    (hCp_eq : C' - C = (-α / δ) • (A - C) + (-β / δ) • (B - C)) :
    ∃ wg : E2 → ℝ,
      (∀ v : E2, v ≠ 0 → 0 < wg v) ∧
      (∀ {r : ℝ}, 0 < r → ∀ v : E2, wg (r • v) = r * wg v) ∧
      (∀ v₁ v₂ : E2, wg (v₁ + v₂) ≤ wg v₁ + wg v₂) ∧
      (∀ lam ∈ Icc (0 : ℝ) 1, wg ((1 - lam) • (A - C) + lam • (B - C)) = 1) ∧
      (∀ lam ∈ Icc (0 : ℝ) 1, wg ((1 - lam) • (A - C) + lam • (C' - C)) = 1) ∧
      (∀ lam ∈ Icc (0 : ℝ) 1, wg ((1 - lam) • (B - C) + lam • (C' - C)) = 1) := by
  let xcoord : E2 → ℝ := fun v => det2 v (B - C) / det2 (A - C) (B - C)
  let ycoord : E2 → ℝ := fun v => det2 (A - C) v / det2 (A - C) (B - C)
  have hxy_add : ∀ v₁ v₂, xcoord (v₁ + v₂) = xcoord v₁ + xcoord v₂ ∧
      ycoord (v₁ + v₂) = ycoord v₁ + ycoord v₂ := fun v₁ v₂ => by
    constructor <;> simp only [xcoord, ycoord, det2_add_left, det2_add_right, add_div]
  have hxy_smul : ∀ r v, xcoord (r • v) = r * xcoord v ∧ ycoord (r • v) = r * ycoord v :=
    fun r v => by
      constructor <;> simp only [xcoord, ycoord, det2_smul_left, det2_smul_right, mul_div_assoc]
  have hxy_AC : xcoord (A - C) = 1 ∧ ycoord (A - C) = 0 := by
    constructor <;> simp only [xcoord, ycoord, div_self hdet_CAB, det2_self, zero_div]
  have hxy_BC : xcoord (B - C) = 0 ∧ ycoord (B - C) = 1 := by
    constructor <;> simp only [xcoord, ycoord, div_self hdet_CAB, det2_self, zero_div]
  have hxy_CpC : xcoord (C' - C) = -α / δ ∧ ycoord (C' - C) = -β / δ := by
    rw [hCp_eq]
    have ha1 := hxy_add ((-α / δ) • (A - C)) ((-β / δ) • (B - C))
    rw [ha1.1, ha1.2, (hxy_smul _ _).1, (hxy_smul _ _).2, (hxy_smul _ _).1, (hxy_smul _ _).2,
      hxy_AC.1, hxy_AC.2, hxy_BC.1, hxy_BC.2]
    exact ⟨by ring, by ring⟩
  let fAB : E2 → ℝ := fun v => xcoord v + ycoord v
  let fACp : E2 → ℝ := fun v => xcoord v - ((α + δ) / β) * ycoord v
  let fBCp : E2 → ℝ := fun v => -((β + δ) / α) * xcoord v + ycoord v
  let wg : E2 → ℝ := fun v => max (fAB v) (max (fACp v) (fBCp v))
  have hf_add : ∀ v₁ v₂, fAB (v₁ + v₂) = fAB v₁ + fAB v₂ ∧
      fACp (v₁ + v₂) = fACp v₁ + fACp v₂ ∧ fBCp (v₁ + v₂) = fBCp v₁ + fBCp v₂ := by
    intro v₁ v₂
    have h := hxy_add v₁ v₂
    simp only [fAB, fACp, fBCp, h.1, h.2]; exact ⟨by ring, by ring, by ring⟩
  have hf_smul : ∀ r v, fAB (r • v) = r * fAB v ∧ fACp (r • v) = r * fACp v ∧
      fBCp (r • v) = r * fBCp v := by
    intro r v
    have h := hxy_smul r v
    simp only [fAB, fACp, fBCp, h.1, h.2]; exact ⟨by ring, by ring, by ring⟩
  have hwg_pos : ∀ v : E2, v ≠ 0 → 0 < wg v := by
    intro v hv
    have hcomb : α * fBCp v + β * fACp v + δ * fAB v = 0 := by
      simp only [fAB, fACp, fBCp]
      have hαne : α ≠ 0 := ne_of_gt hα
      have hβne : β ≠ 0 := ne_of_gt hβ
      field_simp; ring
    by_contra hle
    push Not at hle
    have h1 : fAB v ≤ 0 := le_trans (le_max_left _ _) hle
    have h2 : fACp v ≤ 0 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle
    have h3 : fBCp v ≤ 0 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hle
    have hAB0 : fAB v = 0 := by nlinarith only [hcomb, hα, hβ, hδ, h1, h2, h3]
    have hAC0 : fACp v = 0 := by nlinarith only [hcomb, hα, hβ, hδ, h1, h2, h3]
    have hy0 : ycoord v = 0 := by
      have : (1 + (α + δ) / β) * ycoord v = fAB v - fACp v := by simp only [fAB, fACp]; ring
      rw [hAB0, hAC0, sub_self] at this
      have hcpos : 0 < 1 + (α + δ) / β := by positivity
      exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hcpos)
    have hx0 : xcoord v = 0 := by simp only [fAB] at hAB0; linarith
    have hv0 : v = 0 := by
      rw [cramer_e2 hdet_CAB v]
      change xcoord v • (A - C) + ycoord v • (B - C) = 0
      rw [hx0, hy0, zero_smul, zero_smul, add_zero]
    exact hv hv0
  have hwg_smul : ∀ {r : ℝ}, 0 < r → ∀ v : E2, wg (r • v) = r * wg v := by
    intro r hr v
    simp only [wg, (hf_smul r v).1, (hf_smul r v).2.1, (hf_smul r v).2.2,
      mul_max_of_nonneg _ _ (le_of_lt hr)]
  have hwg_subadd : ∀ v₁ v₂ : E2, wg (v₁ + v₂) ≤ wg v₁ + wg v₂ := by
    intro v₁ v₂
    simp only [wg, (hf_add v₁ v₂).1, (hf_add v₁ v₂).2.1, (hf_add v₁ v₂).2.2]
    refine max_le ?_ (max_le ?_ ?_)
    · exact add_le_add (le_max_left _ _) (le_max_left _ _)
    · exact add_le_add (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact add_le_add (le_trans (le_max_right _ _) (le_max_right _ _))
        (le_trans (le_max_right _ _) (le_max_right _ _))
  have hvals_AC : fAB (A - C) = 1 ∧ fACp (A - C) = 1 ∧ fBCp (A - C) < 1 := by
    simp only [fAB, fACp, fBCp, hxy_AC.1, hxy_AC.2]
    refine ⟨by ring, by ring, ?_⟩
    have : 0 < (β + δ) / α := by positivity
    linarith
  have hvals_BC : fAB (B - C) = 1 ∧ fACp (B - C) < 1 ∧ fBCp (B - C) = 1 := by
    simp only [fAB, fACp, fBCp, hxy_BC.1, hxy_BC.2]
    refine ⟨by ring, ?_, by ring⟩
    have : 0 < (α + δ) / β := by positivity
    linarith
  have hvals_CpC : fAB (C' - C) < 1 ∧ fACp (C' - C) = 1 ∧ fBCp (C' - C) = 1 := by
    simp only [fAB, fACp, fBCp, hxy_CpC.1, hxy_CpC.2]
    have hαne : α ≠ 0 := ne_of_gt hα
    have hβne : β ≠ 0 := ne_of_gt hβ
    have hδne : δ ≠ 0 := ne_of_gt hδ
    refine ⟨?_, by field_simp; linarith, by field_simp; linarith⟩
    have : -α / δ + -β / δ = -(α + β) / δ := by ring
    have hneg : -(α + β) / δ < 0 := div_neg_of_neg_of_pos (by linarith) hδ
    linarith
  refine ⟨wg, hwg_pos, hwg_smul, hwg_subadd, ?_, ?_, ?_⟩
  · intro lam ⟨h0, h1⟩
    simp only [wg, (hf_add _ _).1, (hf_add _ _).2.1, (hf_add _ _).2.2,
      (hf_smul _ _).1, (hf_smul _ _).2.1, (hf_smul _ _).2.2]
    have e1 : (1 - lam) * fAB (A - C) + lam * fAB (B - C) = 1 := by
      rw [hvals_AC.1, hvals_BC.1]; ring
    have e2 : (1 - lam) * fACp (A - C) + lam * fACp (B - C) ≤ 1 := by
      rw [hvals_AC.2.1]; nlinarith only [h0, h1, hvals_BC.2.1]
    have e3 : (1 - lam) * fBCp (A - C) + lam * fBCp (B - C) ≤ 1 := by
      rw [hvals_BC.2.2]; nlinarith only [h0, h1, hvals_AC.2.2]
    rw [e1]
    exact max_eq_left (max_le e2 e3)
  · intro lam ⟨h0, h1⟩
    simp only [wg, (hf_add _ _).1, (hf_add _ _).2.1, (hf_add _ _).2.2,
      (hf_smul _ _).1, (hf_smul _ _).2.1, (hf_smul _ _).2.2]
    have e1 : (1 - lam) * fAB (A - C) + lam * fAB (C' - C) ≤ 1 := by
      rw [hvals_AC.1]; nlinarith only [h0, h1, hvals_CpC.1]
    have e2 : (1 - lam) * fACp (A - C) + lam * fACp (C' - C) = 1 := by
      rw [hvals_AC.2.1, hvals_CpC.2.1]; ring
    have e3 : (1 - lam) * fBCp (A - C) + lam * fBCp (C' - C) ≤ 1 := by
      rw [hvals_CpC.2.2]; nlinarith only [h0, h1, hvals_AC.2.2]
    rw [e2]
    exact le_antisymm (max_le e1 (max_le le_rfl e3)) (le_trans (le_max_left _ _) (le_max_right _ _))
  · intro lam ⟨h0, h1⟩
    simp only [wg, (hf_add _ _).1, (hf_add _ _).2.1, (hf_add _ _).2.2,
      (hf_smul _ _).1, (hf_smul _ _).2.1, (hf_smul _ _).2.2]
    have e1 : (1 - lam) * fAB (B - C) + lam * fAB (C' - C) ≤ 1 := by
      rw [hvals_BC.1]; nlinarith only [h0, h1, hvals_CpC.1]
    have e2 : (1 - lam) * fACp (B - C) + lam * fACp (C' - C) ≤ 1 := by
      rw [hvals_CpC.2.1]; nlinarith only [h0, h1, hvals_BC.2.1]
    have e3 : (1 - lam) * fBCp (B - C) + lam * fBCp (C' - C) = 1 := by
      rw [hvals_BC.2.2, hvals_CpC.2.2]; ring
    rw [e3]
    exact le_antisymm (max_le e1 (max_le e2 le_rfl)) (le_trans (le_max_right _ _) (le_max_right _ _))

lemma nested_case_ne {A B C C' : E2}
    (hdet : det2 (B - A) (C - A) ≠ 0) (hdet' : det2 (B - A) (C' - A) ≠ 0)
    (hC_in : C ∈ triInt A B C') :
    OMA.S_mo_499635.center A B C' ≠ OMA.S_mo_499635.center A B C := by
  obtain ⟨α, β, δ, hα, hβ, hδ, hsum, hC_eq⟩ := hC_in
  -- Write C' - C = (-α/δ)(A - C) + (-β/δ)(B - C)
  have hCp_eq : C' - C = (-α / δ) • (A - C) + (-β / δ) • (B - C) := by
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have h1 : δ • (C' - C) = (-α) • (A - C) + (-β) • (B - C) := by
      have h2 : α • (A - C) + β • (B - C) + δ • (C' - C) = 0 := by
        simp only [smul_sub]
        have hCsum : α • C + β • C + δ • C = α • A + β • B + δ • C' := by
          rw [← add_smul, ← add_smul, hsum, one_smul, hC_eq]
        have h3 : (α • A - α • C) + (β • B - β • C) + (δ • C' - δ • C) =
            (α • A + β • B + δ • C') - (α • C + β • C + δ • C) := by abel
        rw [h3, hCsum, sub_self]
      have h4 := eq_neg_of_add_eq_zero_right h2
      rw [h4, neg_add, neg_smul, neg_smul]
    have h2 := congrArg (δ⁻¹ • ·) h1
    rw [smul_smul, inv_mul_cancel₀ hδne, one_smul, smul_add, smul_smul, smul_smul] at h2
    simpa [div_eq_inv_mul] using h2
  -- Nonzero determinants of the 3 sub-triangles (C, A, B), (C, A, C'), (C, B, C')
  have hdet_CAB : det2 (A - C) (B - C) ≠ 0 := by
    have : det2 (A - C) (B - C) = det2 (B - A) (C - A) := by unfold det2; simp; ring
    rwa [this]
  have hdet_CAC' : det2 (A - C) (C' - C) ≠ 0 := by
    rw [hCp_eq, det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, zero_add]
    exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr (ne_of_gt hβ)) (ne_of_gt hδ)) hdet_CAB
  have hdet_CBC' : det2 (B - C) (C' - C) ≠ 0 := by
    rw [hCp_eq, det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, add_zero,
      det2_antisymm (B - C) (A - C)]
    exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr (ne_of_gt hα)) (ne_of_gt hδ))
      (neg_ne_zero.mpr hdet_CAB)
  let xcoord : E2 → ℝ := fun v => det2 v (B - C) / det2 (A - C) (B - C)
  let ycoord : E2 → ℝ := fun v => det2 (A - C) v / det2 (A - C) (B - C)
  have hxy_add : ∀ v₁ v₂, xcoord (v₁ + v₂) = xcoord v₁ + xcoord v₂ ∧
      ycoord (v₁ + v₂) = ycoord v₁ + ycoord v₂ := fun v₁ v₂ => by
    constructor <;> simp only [xcoord, ycoord, det2_add_left, det2_add_right, add_div]
  have hxy_smul : ∀ r v, xcoord (r • v) = r * xcoord v ∧ ycoord (r • v) = r * ycoord v :=
    fun r v => by
      constructor <;> simp only [xcoord, ycoord, det2_smul_left, det2_smul_right, mul_div_assoc]
  have hxy_AC : xcoord (A - C) = 1 ∧ ycoord (A - C) = 0 := by
    constructor <;> simp only [xcoord, ycoord, div_self hdet_CAB, det2_self, zero_div]
  have hxy_BC : xcoord (B - C) = 0 ∧ ycoord (B - C) = 1 := by
    constructor <;> simp only [xcoord, ycoord, div_self hdet_CAB, det2_self, zero_div]
  have hxy_CpC : xcoord (C' - C) = -α / δ ∧ ycoord (C' - C) = -β / δ := by
    rw [hCp_eq]
    have ha1 := hxy_add ((-α / δ) • (A - C)) ((-β / δ) • (B - C))
    rw [ha1.1, ha1.2, (hxy_smul _ _).1, (hxy_smul _ _).2, (hxy_smul _ _).1, (hxy_smul _ _).2,
      hxy_AC.1, hxy_AC.2, hxy_BC.1, hxy_BC.2]
    exact ⟨by ring, by ring⟩
  obtain ⟨wg, hwg_pos, hwg_smul, hwg_subadd, hwg_edge_AB, hwg_edge_ACp, hwg_edge_BCp⟩ :=
    nested_gauge_exists hdet_CAB hα hβ hδ hsum hCp_eq
  -- Define ray-centroid gauge p(v) = Hfun ‖v‖ (wg v) (-⟪C, v⟫)
  let pfun : E2 → ℝ := fun v => Hfun ‖v‖ (wg v) (-⟪C, v⟫)
  have hp_pos : ∀ v : E2, v ≠ 0 → 0 < pfun v := fun v hv =>
    Hfun_pos (norm_pos_iff.mpr hv) (hwg_pos v hv) _
  have hp_smul : ∀ {r : ℝ} (hr : 0 < r) (v : E2), pfun (r • v) = r * pfun v := by
    intro r hr v
    simp only [pfun, norm_smul, Real.norm_of_nonneg (le_of_lt hr), hwg_smul hr v,
      inner_smul_right, neg_mul_eq_mul_neg]
    exact Hfun_smul hr _
  -- Strict subadditivity of pfun on linearly independent vectors (det2 v₁ v₂ ≠ 0)!
  have hp_strict_subadd : ∀ {v₁ v₂ : E2}, det2 v₁ v₂ ≠ 0 → pfun (v₁ + v₂) < pfun v₁ + pfun v₂ := by
    intro v₁ v₂ hdet12
    have hv1 : v₁ ≠ 0 := by intro h; rw [h] at hdet12; unfold det2 at hdet12; simp at hdet12
    have hv2 : v₂ ≠ 0 := by intro h; rw [h] at hdet12; unfold det2 at hdet12; simp at hdet12
    have hv12 : v₁ + v₂ ≠ 0 := by
      intro h
      have h2 : v₂ = -v₁ := eq_neg_of_add_eq_zero_right h
      rw [h2] at hdet12; unfold det2 at hdet12; simp at hdet12; apply hdet12; ring
    -- Strict triangle inequality in EuclideanSpace: ‖v₁ + v₂‖ < ‖v₁‖ + ‖v₂‖
    have hnorm_lt : ‖v₁ + v₂‖ < ‖v₁‖ + ‖v₂‖ := norm_add_lt_of_det2_ne_zero hdet12
    have hstep1 : Hfun ‖v₁ + v₂‖ (wg (v₁ + v₂)) (-⟪C, v₁ + v₂⟫) <
        Hfun (‖v₁‖ + ‖v₂‖) (wg (v₁ + v₂)) (-⟪C, v₁ + v₂⟫) :=
      Hfun_strictMono_t (norm_pos_iff.mpr hv12) hnorm_lt (hwg_pos _ hv12) _
    have hstep2 : Hfun (‖v₁‖ + ‖v₂‖) (wg (v₁ + v₂)) (-⟪C, v₁ + v₂⟫) ≤
        Hfun (‖v₁‖ + ‖v₂‖) (wg v₁ + wg v₂) (-⟪C, v₁ + v₂⟫) :=
      Hfun_mono_w (add_pos (norm_pos_iff.mpr hv1) (norm_pos_iff.mpr hv2))
        (hwg_pos _ hv12) (hwg_subadd v₁ v₂) _
    have hstep3 : Hfun (‖v₁‖ + ‖v₂‖) (wg v₁ + wg v₂) (-⟪C, v₁ + v₂⟫) ≤
        pfun v₁ + pfun v₂ := by
      have hinn : -⟪C, v₁ + v₂⟫ = -⟪C, v₁⟫ + -⟪C, v₂⟫ := by rw [inner_add_right]; ring
      rw [hinn]
      exact Hfun_subadd (norm_pos_iff.mpr hv1) (norm_pos_iff.mpr hv2)
        (hwg_pos v₁ hv1) (hwg_pos v₂ hv2) _ _
    exact lt_of_lt_of_le hstep1 (le_trans hstep2 hstep3)
  -- Separating linear functional ell(v) = p(A - C) * xcoord v + p(B - C) * ycoord v!
  have hAC_ne : A - C ≠ 0 := by
    intro h; rw [h] at hdet_CAB; unfold det2 at hdet_CAB; simp at hdet_CAB
  have hBC_ne : B - C ≠ 0 := by
    intro h; rw [h] at hdet_CAB; unfold det2 at hdet_CAB; simp at hdet_CAB
  set pA := pfun (A - C)
  set pB := pfun (B - C)
  have hpA : 0 < pA := hp_pos (A - C) hAC_ne
  have hpB : 0 < pB := hp_pos (B - C) hBC_ne
  let ell : E2 →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun v => pA * xcoord v + pB * ycoord v
      map_add' := fun v₁ v₂ => by
        have h := hxy_add v₁ v₂; rw [h.1, h.2]; ring
      map_smul' := fun r v => by
        have h := hxy_smul r v; rw [h.1, h.2]; simp; ring }
  -- Sign of ell(v) - pfun(v) on the three open boundary edges:
  have hell_gt_on_AB : ∀ lam ∈ Ioo (0 : ℝ) 1,
      0 < ell ((1 - lam) • (A - C) + lam • (B - C)) -
        pfun ((1 - lam) • (A - C) + lam • (B - C)) := by
    intro lam ⟨h0, h1⟩
    have hd : det2 ((1 - lam) • (A - C)) (lam • (B - C)) ≠ 0 := by
      rw [det2_smul_left, det2_smul_right]
      exact mul_ne_zero (by linarith) (mul_ne_zero (ne_of_gt h0) hdet_CAB)
    have hsub := hp_strict_subadd hd
    rw [hp_smul (by linarith : 0 < 1 - lam), hp_smul h0] at hsub
    have hell_eq : ell ((1 - lam) • (A - C) + lam • (B - C)) = (1 - lam) * pA + lam * pB := by
      simp only [ell, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
      have h := hxy_add ((1 - lam) • (A - C)) (lam • (B - C))
      rw [h.1, h.2, (hxy_smul _ _).1, (hxy_smul _ _).2, (hxy_smul _ _).1, (hxy_smul _ _).2,
        hxy_AC.1, hxy_AC.2, hxy_BC.1, hxy_BC.2]; ring
    linarith
  have hell_lt_of_neg_coord : ∀ v : E2, v ≠ 0 → (xcoord v < 0 ∨ ycoord v < 0) →
      ell v - pfun v < 0 := by
    intro v hv hneg
    set xv := xcoord v
    set yv := ycoord v
    have hdecomp : v = xv • (A - C) + yv • (B - C) := cramer_e2 hdet_CAB v
    have hell_eq : ell v = pA * xv + pB * yv := rfl
    rcases le_or_gt xv 0 with hxle | hxgt
    · rcases le_or_gt yv 0 with hyle | hygt
      · have hell_le : ell v ≤ 0 := by rw [hell_eq]; nlinarith only [hpA, hpB, hxle, hyle]
        linarith only [hell_le, hp_pos v hv]
      · have hxlt : xv < 0 := hneg.resolve_right (not_lt.mpr (le_of_lt hygt))
        have hsum_v : v + (-xv) • (A - C) = yv • (B - C) := by
          rw [hdecomp, neg_smul]; abel
        have hd : det2 v ((-xv) • (A - C)) ≠ 0 := by
          rw [det2_smul_right, hdecomp, det2_add_left, det2_smul_left, det2_smul_left,
            det2_self, mul_zero, zero_add, det2_antisymm (B - C) (A - C)]
          exact mul_ne_zero (by linarith only [hxlt])
            (mul_ne_zero (ne_of_gt hygt) (neg_ne_zero.mpr hdet_CAB))
        have hsub := hp_strict_subadd hd
        rw [hsum_v, hp_smul hygt, hp_smul (by linarith only [hxlt] : 0 < -xv)] at hsub
        linarith only [hsub, hell_eq]
    · have hylt : yv < 0 := hneg.resolve_left (not_lt.mpr (le_of_lt hxgt))
      have hsum_v : v + (-yv) • (B - C) = xv • (A - C) := by
        rw [hdecomp, neg_smul]; abel
      have hd : det2 v ((-yv) • (B - C)) ≠ 0 := by
        rw [det2_smul_right, hdecomp, det2_add_left, det2_smul_left, det2_smul_left,
          det2_self, mul_zero, add_zero]
        exact mul_ne_zero (by linarith only [hylt]) (mul_ne_zero (ne_of_gt hxgt) hdet_CAB)
      have hsub := hp_strict_subadd hd
      rw [hsum_v, hp_smul hxgt, hp_smul (by linarith only [hylt] : 0 < -yv)] at hsub
      linarith only [hsub, hell_eq]
  -- Relation between ∫_0^1 s (ell(s v) - 1) γ(C + s v) ds and (ell v - pfun v) when wg v = 1!
  have hray_int : ∀ v : E2, v ≠ 0 → wg v = 1 →
      (∫ s in (0 : ℝ)..1, s * (ell (s • v) - 1) * OMA.S_mo_499635.γ (C + s • v)) =
        (ell v - pfun v) *
          (∫ s in (0 : ℝ)..1, s ^ 2 * OMA.S_mo_499635.γ (C + s • v)) := by
    intro v hv hwg1
    have hgamma_eq : ∀ s : ℝ, OMA.S_mo_499635.γ (C + s • v) =
        Real.exp (-‖C‖ ^ 2 / 2) * Real.exp (-‖v‖ ^ 2 * s ^ 2 / 2 + (-⟪C, v⟫) * s) := by
      intro s
      unfold OMA.S_mo_499635.γ
      rw [← Real.exp_add]
      congr 1
      rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, inner_smul_right]
      have hsq : |s| ^ 2 = s ^ 2 := sq_abs s
      nlinarith [mul_pow |s| ‖v‖ 2]
    have hp_eq := Hfun_eq_integral (w := wg v) (norm_pos_iff.mpr hv)
      (by rw [hwg1]; exact zero_lt_one) (-⟪C, v⟫)
    simp only [hwg1, div_one] at hp_eq
    have hp_val : pfun v =
        (∫ s in (0 : ℝ)..1, s * Real.exp (-‖v‖ ^ 2 * s ^ 2 / 2 + (-⟪C, v⟫) * s)) /
        (∫ s in (0 : ℝ)..1, s ^ 2 * Real.exp (-‖v‖ ^ 2 * s ^ 2 / 2 + (-⟪C, v⟫) * s)) := by
      simpa only [pfun, hwg1] using hp_eq
    have hden_pos : 0 < ∫ s in (0 : ℝ)..1, s ^ 2 * Real.exp (-‖v‖ ^ 2 * s ^ 2 / 2 + (-⟪C, v⟫) * s) :=
      intervalIntegral.integral_pos zero_lt_one (by fun_prop)
        (fun s hs => mul_nonneg (sq_nonneg s) (le_of_lt (Real.exp_pos _)))
        ⟨1 / 2, ⟨by norm_num, by norm_num⟩, mul_pos (by norm_num) (Real.exp_pos _)⟩
    have hnum_eq : (∫ s in (0 : ℝ)..1, s * Real.exp (-‖v‖ ^ 2 * s ^ 2 / 2 + (-⟪C, v⟫) * s)) =
        pfun v * ∫ s in (0 : ℝ)..1, s ^ 2 * Real.exp (-‖v‖ ^ 2 * s ^ 2 / 2 + (-⟪C, v⟫) * s) := by
      rw [hp_val, div_mul_cancel₀ _ (ne_of_gt hden_pos)]
    have hi1 : IntervalIntegrable (fun s : ℝ => s * OMA.S_mo_499635.γ (C + s • v)) volume 0 1 :=
      (continuous_id.mul (continuous_gamma.comp (continuous_const.add (continuous_id.smul continuous_const)))).intervalIntegrable 0 1
    have hi2 : IntervalIntegrable (fun s : ℝ => s ^ 2 * OMA.S_mo_499635.γ (C + s • v)) volume 0 1 :=
      ((continuous_pow 2).mul (continuous_gamma.comp (continuous_const.add (continuous_id.smul continuous_const)))).intervalIntegrable 0 1
    have hrew : (fun s : ℝ => s * (ell (s • v) - 1) * OMA.S_mo_499635.γ (C + s • v)) =
        fun s => ell v * (s ^ 2 * OMA.S_mo_499635.γ (C + s • v)) -
          s * OMA.S_mo_499635.γ (C + s • v) := by
      ext s; rw [map_smul, smul_eq_mul]; ring
    rw [hrew, intervalIntegral.integral_sub (hi2.const_mul _) hi1,
      intervalIntegral.integral_const_mul]
    have hI1 : (∫ s in (0 : ℝ)..1, s * OMA.S_mo_499635.γ (C + s • v)) =
        Real.exp (-‖C‖ ^ 2 / 2) *
          ∫ s in (0 : ℝ)..1, s * Real.exp (-‖v‖ ^ 2 * s ^ 2 / 2 + (-⟪C, v⟫) * s) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [hgamma_eq s]; ring
    have hI2 : (∫ s in (0 : ℝ)..1, s ^ 2 * OMA.S_mo_499635.γ (C + s • v)) =
        Real.exp (-‖C‖ ^ 2 / 2) *
          ∫ s in (0 : ℝ)..1, s ^ 2 * Real.exp (-‖v‖ ^ 2 * s ^ 2 / 2 + (-⟪C, v⟫) * s) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [hgamma_eq s]; ring
    rw [hI1, hI2, hnum_eq]; ring
  -- Evaluate the sign of ∫ (ell(x - C) - 1) γ(x) on T = tri C A B, T₁ = tri C A C', T₂ = tri C B C'!
  let Fsep : E2 → ℝ := fun x => (ell (x - C) - 1) * OMA.S_mo_499635.γ x
  have hFsep_cont : Continuous Fsep := by
    simp only [Fsep]
    exact ((ell.continuous.comp (continuous_id.sub continuous_const)).sub continuous_const).mul
      continuous_gamma
  have hpos_T : 0 < ∫ x in tri C A B, Fsep x := by
    refine tri_ray_integral_pos hdet_CAB hFsep_cont fun lam hlam => ?_
    have hvne : (1 - lam) • (A - C) + lam • (B - C) ≠ 0 := by
      intro h0
      have := linear_combo_eq_zero_of_det2_ne_zero hdet_CAB h0
      linarith [hlam.1]
    have hwg1 := hwg_edge_AB lam ⟨le_of_lt hlam.1, le_of_lt hlam.2⟩
    have hray : (∫ s in (0 : ℝ)..1, s * Fsep (C + s • ((1 - lam) • (A - C) + lam • (B - C)))) =
        (ell ((1 - lam) • (A - C) + lam • (B - C)) - pfun ((1 - lam) • (A - C) + lam • (B - C))) *
          ∫ s in (0 : ℝ)..1, s ^ 2 * OMA.S_mo_499635.γ (C + s • ((1 - lam) • (A - C) + lam • (B - C))) := by
      simpa only [Fsep, add_sub_cancel_left, ← mul_assoc] using hray_int _ hvne hwg1
    rw [hray]
    refine mul_pos (hell_gt_on_AB lam hlam) ?_
    refine intervalIntegral.integral_pos zero_lt_one (by have := continuous_gamma; fun_prop)
      (fun s _ => mul_nonneg (sq_nonneg s) (le_of_lt (gamma_pos _)))
      ⟨1 / 2, ⟨by norm_num, by norm_num⟩, mul_pos (by norm_num) (gamma_pos _)⟩
  have hneg_T1 : ∫ x in tri C A C', Fsep x < 0 := by
    refine tri_ray_integral_neg hdet_CAC' hFsep_cont fun lam hlam => ?_
    set v := (1 - lam) • (A - C) + lam • (C' - C)
    have hvne : v ≠ 0 := by
      intro h0
      have := linear_combo_eq_zero_of_det2_ne_zero hdet_CAC' h0
      linarith [hlam.1]
    have hwg1 := hwg_edge_ACp lam ⟨le_of_lt hlam.1, le_of_lt hlam.2⟩
    have hray := hray_int v hvne hwg1
    simp only [Fsep, add_sub_cancel_left, ← mul_assoc]
    rw [hray]
    have hy_neg : ycoord v < 0 := by
      simp only [v, (hxy_add _ _).2, (hxy_smul _ _).2, hxy_AC.2, hxy_CpC.2]
      have : lam * (-β / δ) < 0 := mul_neg_of_pos_of_neg hlam.1 (div_neg_of_neg_of_pos (by linarith) hδ)
      linarith
    have hden_p : 0 < ∫ s in (0 : ℝ)..1, s ^ 2 * OMA.S_mo_499635.γ (C + s • v) :=
      intervalIntegral.integral_pos zero_lt_one (by have := continuous_gamma; fun_prop)
        (fun s _ => mul_nonneg (sq_nonneg s) (le_of_lt (gamma_pos _)))
        ⟨1 / 2, ⟨by norm_num, by norm_num⟩, mul_pos (by norm_num) (gamma_pos _)⟩
    exact mul_neg_of_neg_of_pos (hell_lt_of_neg_coord v hvne (Or.inr hy_neg)) hden_p
  have hneg_T2 : ∫ x in tri C B C', Fsep x < 0 := by
    refine tri_ray_integral_neg hdet_CBC' hFsep_cont fun lam hlam => ?_
    set v := (1 - lam) • (B - C) + lam • (C' - C)
    have hvne : v ≠ 0 := by
      intro h0
      have := linear_combo_eq_zero_of_det2_ne_zero hdet_CBC' h0
      linarith [hlam.1]
    have hwg1 := hwg_edge_BCp lam ⟨le_of_lt hlam.1, le_of_lt hlam.2⟩
    have hray := hray_int v hvne hwg1
    simp only [Fsep, add_sub_cancel_left, ← mul_assoc]
    rw [hray]
    have hx_neg : xcoord v < 0 := by
      simp only [v, (hxy_add _ _).1, (hxy_smul _ _).1, hxy_BC.1, hxy_CpC.1]
      have : lam * (-α / δ) < 0 := mul_neg_of_pos_of_neg hlam.1 (div_neg_of_neg_of_pos (by linarith) hδ)
      linarith
    have hden_p : 0 < ∫ s in (0 : ℝ)..1, s ^ 2 * OMA.S_mo_499635.γ (C + s • v) :=
      intervalIntegral.integral_pos zero_lt_one (by have := continuous_gamma; fun_prop)
        (fun s _ => mul_nonneg (sq_nonneg s) (le_of_lt (gamma_pos _)))
        ⟨1 / 2, ⟨by norm_num, by norm_num⟩, mul_pos (by norm_num) (gamma_pos _)⟩
    exact mul_neg_of_neg_of_pos (hell_lt_of_neg_coord v hvne (Or.inl hx_neg)) hden_p
  -- Partition T' = tri C A B ∪ tri C A C' ∪ tri C B C' with measure-0 pairwise intersections!
  obtain ⟨hpart, hdisj_12, hdisj_0_12⟩ :=
    tri_partition_of_mem_triInt hdet_CAB hdet_CAC' hdet_CBC' hα hβ hδ hsum hC_eq hCp_eq
  -- Now assume center A B C' = center A B C = M and derive a contradiction!
  intro hM_eq
  set M := OMA.S_mo_499635.center A B C
  have hF_rew : ∀ x : E2, Fsep x = (ell x + (-ell C - 1)) * OMA.S_mo_499635.γ x := by
    intro x; simp only [Fsep, map_sub]; ring
  have hInt_T : ∫ x in tri A B C, Fsep x =
      (ell (M - C) - 1) * ∫ x in tri A B C, OMA.S_mo_499635.γ x := by
    simp_rw [hF_rew]
    rw [integral_affine_gamma_eq A B C hdet ell (-ell C - 1), map_sub]
    ring
  have hInt_T' : ∫ x in tri A B C', Fsep x =
      (ell (M - C) - 1) * ∫ x in tri A B C', OMA.S_mo_499635.γ x := by
    simp_rw [hF_rew]
    rw [integral_affine_gamma_eq A B C' hdet' ell (-ell C - 1), hM_eq, map_sub]
    ring
  have hT_eq : tri A B C = tri C A B := tri_perm_rot A B C
  have hInt_split_F : ∫ x in tri A B C', Fsep x =
      (∫ x in tri C A B, Fsep x) + ((∫ x in tri C A C', Fsep x) + ∫ x in tri C B C', Fsep x) := by
    rw [hpart,
      MeasureTheory.setIntegral_union₀ hdisj_0_12
        ((measurableSet_tri C A C').union (measurableSet_tri C B C')).nullMeasurableSet
        (hFsep_cont.continuousOn.integrableOn_compact (isCompact_tri C A B))
        ((hFsep_cont.continuousOn.integrableOn_compact (isCompact_tri C A C')).union
          (hFsep_cont.continuousOn.integrableOn_compact (isCompact_tri C B C'))),
      MeasureTheory.setIntegral_union₀ hdisj_12
        (measurableSet_tri C B C').nullMeasurableSet
        (hFsep_cont.continuousOn.integrableOn_compact (isCompact_tri C A C'))
        (hFsep_cont.continuousOn.integrableOn_compact (isCompact_tri C B C'))]
  have hInt_split_g : ∫ x in tri A B C', OMA.S_mo_499635.γ x =
      (∫ x in tri C A B, OMA.S_mo_499635.γ x) +
      ((∫ x in tri C A C', OMA.S_mo_499635.γ x) + ∫ x in tri C B C', OMA.S_mo_499635.γ x) := by
    rw [hpart,
      MeasureTheory.setIntegral_union₀ hdisj_0_12
        ((measurableSet_tri C A C').union (measurableSet_tri C B C')).nullMeasurableSet
        (continuous_gamma.continuousOn.integrableOn_compact (isCompact_tri C A B))
        ((continuous_gamma.continuousOn.integrableOn_compact (isCompact_tri C A C')).union
          (continuous_gamma.continuousOn.integrableOn_compact (isCompact_tri C B C'))),
      MeasureTheory.setIntegral_union₀ hdisj_12
        (measurableSet_tri C B C').nullMeasurableSet
        (continuous_gamma.continuousOn.integrableOn_compact (isCompact_tri C A C'))
        (continuous_gamma.continuousOn.integrableOn_compact (isCompact_tri C B C'))]
  have hg_T : 0 < ∫ x in tri C A B, OMA.S_mo_499635.γ x := integral_gamma_pos hdet_CAB
  have hg_1 : 0 < ∫ x in tri C A C', OMA.S_mo_499635.γ x := integral_gamma_pos hdet_CAC'
  have hg_2 : 0 < ∫ x in tri C B C', OMA.S_mo_499635.γ x := integral_gamma_pos hdet_CBC'
  -- From hInt_T and hpos_T: ell(M - C) - 1 > 0
  have hgt : 0 < ell (M - C) - 1 := by
    rw [hT_eq] at hInt_T
    nlinarith only [hInt_T, hpos_T, hg_T]
  -- From subtracting hInt_T from hInt_T': (ell(M - C) - 1) * (hg_1 + hg_2) = hneg_T1 + hneg_T2 < 0!
  rw [hT_eq] at hInt_T
  nlinarith only [hInt_T, hInt_T', hInt_split_F, hInt_split_g, hgt, hg_1, hg_2, hneg_T1, hneg_T2]

/-! #### Part 3: Boundary and Crossing Cases, and Main Theorem -/

/-- Boundary case: `C = α • A + δ • C'` with `α > 0, δ > 0, α + δ = 1` (so `C ∈ (A, C')`). -/
lemma boundary_case_ne {A B C C' : E2}
    (hdet : det2 (B - A) (C - A) ≠ 0) (hdet' : det2 (B - A) (C' - A) ≠ 0)
    {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hsum : α + δ = 1) (hC : C = α • A + δ • C') :
    OMA.S_mo_499635.center A B C' ≠ OMA.S_mo_499635.center A B C := by
  have hdet_BCC' : det2 (C - B) (C' - B) ≠ 0 := by
    have h1 : C - B = α • (A - B) + δ • (C' - B) := by
      rw [hC]; have : B = α • B + δ • B := by rw [← add_smul, hsum, one_smul]
      conv_lhs => rw [this]
      simp only [smul_sub]; abel
    rw [h1, det2_add_left, det2_smul_left, det2_smul_left, det2_self, mul_zero, add_zero]
    have h2 : det2 (A - B) (C' - B) = -det2 (B - A) (C' - A) := by unfold det2; simp; ring
    rw [h2]
    exact mul_ne_zero (ne_of_gt hα) (neg_ne_zero.mpr hdet')
  -- Partition tri A B C' = tri A B C ∪ tri B C C' (a.e.-disjoint!)
  have hpart : tri A B C' = tri A B C ∪ tri B C C' := by
    ext x
    constructor
    · intro hx
      rw [mem_tri_iff] at hx
      obtain ⟨p, q, r, hp, hq, hr, hpqr, rfl⟩ := hx
      rcases le_total (p / α) (r / δ) with h1 | h1
      · -- p / α ≤ r / δ => write using C and C'
        right; rw [mem_tri_iff]
        have hr' : 0 ≤ r - (p / α) * δ := by
          have := mul_le_mul_of_nonneg_right h1 (le_of_lt hδ)
          rw [div_mul_cancel₀ _ (ne_of_gt hδ)] at this
          linarith
        refine ⟨q, p / α, r - (p / α) * δ, hq, div_nonneg hp (le_of_lt hα), hr', by
          have : p / α + (r - p / α * δ) = p + r := by
            have hαne : α ≠ 0 := ne_of_gt hα
            field_simp; nlinarith
          linarith, ?_⟩
        rw [hC, smul_add, smul_smul, smul_smul, div_mul_cancel₀ _ (ne_of_gt hα), sub_smul]
        abel
      · -- r / δ ≤ p / α => x ∈ tri A B C!
        left; rw [mem_tri_iff]
        have hp' : 0 ≤ p - (r / δ) * α := by
          have := mul_le_mul_of_nonneg_right h1 (le_of_lt hα)
          rw [div_mul_cancel₀ _ (ne_of_gt hα)] at this
          linarith
        refine ⟨p - (r / δ) * α, q, r / δ, hp', hq, div_nonneg hr (le_of_lt hδ), by
          have : p - r / δ * α + r / δ = p + r := by
            have hδne : δ ≠ 0 := ne_of_gt hδ
            field_simp; nlinarith
          linarith, ?_⟩
        rw [hC, smul_add, smul_smul, smul_smul, div_mul_cancel₀ _ (ne_of_gt hδ), sub_smul]
        abel
    · intro hx
      have hC_mem : C ∈ tri A B C' := (mem_tri_iff A B C' C).mpr
        ⟨α, 0, δ, le_of_lt hα, le_rfl, le_of_lt hδ, by linarith, by rw [hC, zero_smul, add_zero]⟩
      have hA_mem : A ∈ tri A B C' := subset_convexHull ℝ _ (by simp)
      have hB_mem : B ∈ tri A B C' := subset_convexHull ℝ _ (by simp)
      have hCp_mem : C' ∈ tri A B C' := subset_convexHull ℝ _ (by simp)
      have hconv := convex_convexHull ℝ ({A, B, C'} : Set E2)
      rcases hx with hx | hx
      · exact convexHull_min (by intro y hy; rcases hy with rfl | rfl | rfl <;> assumption) hconv hx
      · exact convexHull_min (by intro y hy; rcases hy with rfl | rfl | rfl <;> assumption) hconv hx
  -- Separating linear functional along line BC: ψ(x) = det2 (C - B) (x - B) / det2 (C - B) (A - B)
  have hdet_CBA : det2 (C - B) (A - B) ≠ 0 := by
    have : det2 (C - B) (A - B) = det2 (B - A) (C - A) := by unfold det2; simp; ring
    rwa [this]
  set d := det2 (C - B) (A - B)
  let L : E2 →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun x => det2 (C - B) x / d
      map_add' := fun x y => by rw [det2_add_right, add_div]
      map_smul' := fun r x => by rw [det2_smul_right]; simp [mul_div_assoc] }
  have hL_val : ∀ x : E2, L x + (-L B) = det2 (C - B) (x - B) / d := by
    intro x; simp only [L, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    rw [det2_sub_right]; ring
  have hL_pos_T : ∀ x ∈ triInt A B C, 0 < L x + (-L B) := by
    intro x hx
    rw [hL_val x]
    obtain ⟨a, b, c, ha, hb, hc, hs, rfl⟩ := hx
    have hsub : a • A + b • B + c • C - B = a • (A - B) + c • (C - B) := by
      have : b = 1 - a - c := by linarith
      rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
    rw [hsub, det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, add_zero,
      mul_div_cancel_right₀ _ hdet_CBA]
    exact ha
  have hL_neg_T2 : ∀ x ∈ triInt B C C', L x + (-L B) < 0 := by
    intro x hx
    rw [hL_val x]
    obtain ⟨a, b, c, ha, hb, hc, hs, rfl⟩ := hx
    have hsub : a • B + b • C + c • C' - B = b • (C - B) + c • (C' - B) := by
      have : a = 1 - b - c := by linarith
      rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
    have hCp_rel : det2 (C - B) (C' - B) = -(α / δ) * d := by
      have h1 : C - B = α • (A - B) + δ • (C' - B) := by
        rw [hC]
        have hB : B = α • B + δ • B := by rw [← add_smul, hsum, one_smul]
        rw [smul_sub, smul_sub]
        conv_lhs => rw [hB]
        abel
      have h2 : δ • (C' - B) = (C - B) - α • (A - B) := by
        have := congrArg (· - α • (A - B)) h1; simpa using this.symm
      have h3 : det2 (C - B) (δ • (C' - B)) = -α * d := by
        rw [h2, det2_sub_right, det2_self, zero_sub, det2_smul_right]; ring
      rw [det2_smul_right] at h3
      have hδne : δ ≠ 0 := ne_of_gt hδ
      field_simp; linarith
    rw [hsub, det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, zero_add,
      hCp_rel, show c * (-(α / δ) * d) / d = -(c * (α / δ)) by field_simp]
    have : 0 < c * (α / δ) := mul_pos hc (div_pos hα hδ)
    linarith
  have hdisj : AEDisjoint volume (tri A B C) (tri B C C') := by
    change volume (tri A B C ∩ tri B C C') = 0
    have hsub : tri A B C ∩ tri B C C' ⊆
        (tri A B C \ triInt A B C) ∪ (tri B C C' \ triInt B C C') := by
      rintro x ⟨h1, h2⟩
      by_contra hnot
      simp only [Set.mem_union, Set.mem_sdiff, not_or, not_and, not_not] at hnot
      linarith [hL_pos_T x (hnot.1 h1), hL_neg_T2 x (hnot.2 h2)]
    exact measure_mono_null hsub (measure_union_null (tri_diff_triInt_measure_zero hdet)
      (tri_diff_triInt_measure_zero hdet_BCC'))
  intro hM_eq
  set M := OMA.S_mo_499635.center A B C
  have hpos_int : 0 < ∫ x in tri A B C, (L x + (-L B)) * OMA.S_mo_499635.γ x :=
    integral_tri_pos_of_pos_on_triInt hdet ((L.continuous.add continuous_const).mul continuous_gamma)
      fun x hx => mul_pos (hL_pos_T x hx) (gamma_pos x)
  have hneg_int : ∫ x in tri B C C', (L x + (-L B)) * OMA.S_mo_499635.γ x < 0 := by
    have hp : 0 < ∫ x in tri B C C', -((L x + (-L B)) * OMA.S_mo_499635.γ x) :=
      integral_tri_pos_of_pos_on_triInt hdet_BCC'
        (((L.continuous.add continuous_const).mul continuous_gamma).neg)
        fun x hx => neg_pos.mpr (mul_neg_of_neg_of_pos (hL_neg_T2 x hx) (gamma_pos x))
    rw [MeasureTheory.integral_neg] at hp; linarith
  have hT_eq := integral_affine_gamma_eq A B C hdet L (-L B)
  have hT'_eq := integral_affine_gamma_eq A B C' hdet' L (-L B)
  rw [hM_eq] at hT'_eq
  have hsplit_F : ∫ x in tri A B C', (L x + (-L B)) * OMA.S_mo_499635.γ x =
      (∫ x in tri A B C, (L x + (-L B)) * OMA.S_mo_499635.γ x) +
      ∫ x in tri B C C', (L x + (-L B)) * OMA.S_mo_499635.γ x := by
    rw [hpart]
    exact MeasureTheory.setIntegral_union₀ hdisj (measurableSet_tri B C C').nullMeasurableSet
      (((L.continuous.add continuous_const).mul continuous_gamma).continuousOn.integrableOn_compact
        (isCompact_tri A B C))
      (((L.continuous.add continuous_const).mul continuous_gamma).continuousOn.integrableOn_compact
        (isCompact_tri B C C'))
  have hsplit_g : ∫ x in tri A B C', OMA.S_mo_499635.γ x =
      (∫ x in tri A B C, OMA.S_mo_499635.γ x) + ∫ x in tri B C C', OMA.S_mo_499635.γ x := by
    rw [hpart]
    exact MeasureTheory.setIntegral_union₀ hdisj (measurableSet_tri B C C').nullMeasurableSet
      (continuous_gamma.continuousOn.integrableOn_compact (isCompact_tri A B C))
      (continuous_gamma.continuousOn.integrableOn_compact (isCompact_tri B C C'))
  have hg1 : 0 < ∫ x in tri A B C, OMA.S_mo_499635.γ x := integral_gamma_pos hdet
  have hg2 : 0 < ∫ x in tri B C C', OMA.S_mo_499635.γ x := integral_gamma_pos hdet_BCC'
  have hLM_pos : 0 < L M + (-L B) := by nlinarith
  nlinarith

/-- Edge-split partition: if `P = u • Q + v • R` (`u, v > 0`, `u + v = 1`), then
`tri O Q R = tri O Q P ∪ tri O P R`. -/
lemma tri_partition_edge {O Q R P : E2} {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (huv : u + v = 1) (hP : P = u • Q + v • R) :
    tri O Q R = tri O Q P ∪ tri O P R := by
  ext x
  constructor
  · intro hx
    rw [mem_tri_iff] at hx
    obtain ⟨p, q, r, hp, hq, hr, hpqr, rfl⟩ := hx
    rcases le_total (q / u) (r / v) with h1 | h1
    · right; rw [mem_tri_iff]
      have hr' : 0 ≤ r - (q / u) * v := by
        have := mul_le_mul_of_nonneg_right h1 (le_of_lt hv)
        rw [div_mul_cancel₀ _ (ne_of_gt hv)] at this; linarith
      refine ⟨p, q / u, r - (q / u) * v, hp, div_nonneg hq (le_of_lt hu), hr', by
        have : q / u + (r - q / u * v) = q + r := by
          have := ne_of_gt hu; field_simp; linear_combination -q * huv
        linarith, ?_⟩
      rw [hP, smul_add, smul_smul, smul_smul, div_mul_cancel₀ _ (ne_of_gt hu), sub_smul]
      abel
    · left; rw [mem_tri_iff]
      have hq' : 0 ≤ q - (r / v) * u := by
        have := mul_le_mul_of_nonneg_right h1 (le_of_lt hu)
        rw [div_mul_cancel₀ _ (ne_of_gt hu)] at this; linarith
      refine ⟨p, q - (r / v) * u, r / v, hp, hq', div_nonneg hr (le_of_lt hv), by
        have : q - r / v * u + r / v = q + r := by
          have := ne_of_gt hv; field_simp; linear_combination -r * huv
        linarith, ?_⟩
      rw [hP, smul_add, smul_smul, smul_smul, div_mul_cancel₀ _ (ne_of_gt hv), sub_smul]
      abel
  · intro hx
    have hP_mem : P ∈ tri O Q R := (mem_tri_iff O Q R P).mpr
      ⟨0, u, v, le_rfl, le_of_lt hu, le_of_lt hv, by linarith, by rw [hP, zero_smul, zero_add]⟩
    have hO_mem : O ∈ tri O Q R := subset_convexHull ℝ _ (by simp)
    have hQ_mem : Q ∈ tri O Q R := subset_convexHull ℝ _ (by simp)
    have hR_mem : R ∈ tri O Q R := subset_convexHull ℝ _ (by simp)
    have hconv := convex_convexHull ℝ ({O, Q, R} : Set E2)
    rcases hx with hx | hx
    · exact convexHull_min (by intro y hy; rcases hy with rfl | rfl | rfl <;> assumption) hconv hx
    · exact convexHull_min (by intro y hy; rcases hy with rfl | rfl | rfl <;> assumption) hconv hx

/-- Crossing case: `C = α • A + β • B + δ • C'` with `α > 0, β < 0, δ > 0, α + β + δ = 1`. -/
lemma crossing_case_ne {A B C C' : E2}
    (hdet : det2 (B - A) (C - A) ≠ 0) (hdet' : det2 (B - A) (C' - A) ≠ 0)
    {α β δ : ℝ} (hα : 0 < α) (hβ : β < 0) (hδ : 0 < δ) (hsum : α + β + δ = 1)
    (hC : C = α • A + β • B + δ • C') :
    OMA.S_mo_499635.center A B C' ≠ OMA.S_mo_499635.center A B C := by
  intro hM_eq
  set M := OMA.S_mo_499635.center A B C
  have h1mb : 0 < 1 - β := by linarith
  have had : 0 < α + δ := by linarith
  have h1mb_eq : 1 - β = α + δ := by linarith
  -- Intersection point P = (1/(1-β))•C + (-β/(1-β))•B = (α/(α+δ))•A + (δ/(α+δ))•C'
  set P := (α / (α + δ)) • A + (δ / (α + δ)) • C'
  have hP_BC : P = (1 / (1 - β)) • C + (-β / (1 - β)) • B := by
    rw [hC, h1mb_eq]
    simp only [smul_add, smul_smul]
    have had_ne : α + δ ≠ 0 := ne_of_gt had
    have h1 : (1 / (α + δ) * α) = α / (α + δ) := by ring
    have h2 : (1 / (α + δ) * δ) = δ / (α + δ) := by ring
    have h3 : (1 / (α + δ) * β + -β / (α + δ)) = 0 := by ring
    rw [show (1 / (α + δ) * α) • A + (1 / (α + δ) * β) • B + (1 / (α + δ) * δ) • C' +
        (-β / (α + δ)) • B =
        (1 / (α + δ) * α) • A + (1 / (α + δ) * β + -β / (α + δ)) • B +
        (1 / (α + δ) * δ) • C' by rw [add_smul]; abel]
    rw [h1, h2, h3, zero_smul, add_zero]
  have hC_P : C = (1 - β) • P + β • B := by
    have h1mb_ne : 1 - β ≠ 0 := ne_of_gt h1mb
    rw [hP_BC, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h1mb_ne,
      mul_div_cancel₀ _ h1mb_ne, one_smul, neg_smul]
    abel
  have hCP : C - P = β • (B - P) := by
    rw [hC_P, sub_smul, one_smul, smul_sub]; abel
  have hCpP : C' - P = -(α / δ) • (A - P) := by
    have had_ne : α + δ ≠ 0 := ne_of_gt had
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have h1 : (α + δ) • P = α • A + δ • C' := by
      simp only [P, smul_add, smul_smul, mul_div_cancel₀ _ had_ne]
    have h2 : δ • (C' - P) = (-α) • (A - P) := by
      rw [smul_sub, neg_smul, smul_sub]
      have h3 : α • P + δ • P = α • A + δ • C' := by rw [← add_smul, h1]
      have h4 : (δ • C' - δ • P) + (α • A - α • P) = 0 := by
        have h5 : (α • A + δ • C') - (α • P + δ • P) = 0 := by rw [h3, sub_self]
        calc (δ • C' - δ • P) + (α • A - α • P)
            = (α • A + δ • C') - (α • P + δ • P) := by abel
          _ = 0 := h5
      exact eq_neg_of_add_eq_zero_left h4
    have h3 := congrArg (δ⁻¹ • ·) h2
    rw [smul_smul, inv_mul_cancel₀ hδne, one_smul, smul_smul] at h3
    rw [h3, div_eq_inv_mul, mul_neg, neg_smul]
  -- Nonzero determinants of the 3 triangles ABP, APC, BPC'
  have hdet_ABP : det2 (B - A) (P - A) ≠ 0 := by
    have hPA : P - A = (δ / (α + δ)) • (C' - A) := by
      simp only [P, smul_sub]
      have h1 : α / (α + δ) - 1 = -(δ / (α + δ)) := by
        have had_ne : α + δ ≠ 0 := ne_of_gt had; field_simp; ring
      have h2 : (α / (α + δ)) • A + (δ / (α + δ)) • C' - A =
          (α / (α + δ) - 1) • A + (δ / (α + δ)) • C' := by rw [sub_smul, one_smul]; abel
      rw [h2, h1, neg_smul]; abel
    rw [hPA, det2_smul_right]
    exact mul_ne_zero (ne_of_gt (div_pos hδ had)) hdet'
  have hdet_APC : det2 (P - A) (C - A) ≠ 0 := by
    have h1 : C - A = (1 - β) • (P - A) + β • (B - A) := by
      rw [hC_P]; simp only [smul_sub, sub_smul, one_smul]; abel
    rw [h1, det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, zero_add,
      det2_antisymm (P - A) (B - A)]
    exact mul_ne_zero (ne_of_lt hβ) (neg_ne_zero.mpr hdet_ABP)
  have hdet_BPC' : det2 (P - B) (C' - B) ≠ 0 := by
    have h1 : P - B = (α / (α + δ)) • (A - B) + (δ / (α + δ)) • (C' - B) := by
      simp only [P, smul_sub]
      have hsum1 : α / (α + δ) + δ / (α + δ) = 1 := by
        have had_ne : α + δ ≠ 0 := ne_of_gt had; field_simp
      have hB : B = (α / (α + δ)) • B + (δ / (α + δ)) • B := by rw [← add_smul, hsum1, one_smul]
      conv_lhs => rw [hB]
      abel
    rw [h1, det2_add_left, det2_smul_left, det2_smul_left, det2_self, mul_zero, add_zero]
    have h2 : det2 (A - B) (C' - B) = -det2 (B - A) (C' - A) := by unfold det2; simp; ring
    rw [h2]
    exact mul_ne_zero (ne_of_gt (div_pos hα had)) (neg_ne_zero.mpr hdet')
  -- Partition T = tri A B P ∪ tri A P C (since P ∈ (B, C))
  -- Partition T' = tri A B P ∪ tri B P C' (since P ∈ (A, C'))
  have hpart_T : tri A B C = tri A B P ∪ tri A P C :=
    tri_partition_edge (u := -β / (1 - β)) (v := 1 / (1 - β))
      (div_pos (neg_pos.mpr hβ) h1mb) (div_pos one_pos h1mb)
      (by have := ne_of_gt h1mb; field_simp; ring) (by rw [hP_BC]; abel)
  have hpart_T' : tri A B C' = tri A B P ∪ tri B P C' := by
    have h := tri_partition_edge (O := B) (Q := A) (R := C') (P := P)
      (div_pos hα had) (div_pos hδ had) (by have := ne_of_gt had; field_simp) rfl
    rw [tri_perm_swap12 A B C', tri_perm_swap12 A B P]
    exact h
  -- M ∈ triInt A B C ∩ triInt A B C' implies M ∈ triInt A B P!
  have hM_in_T : M ∈ triInt A B C := center_mem_triInt hdet
  have hM_in_T' : M ∈ triInt A B C' := hM_eq ▸ center_mem_triInt hdet'
  have hM_in_ABP : M ∈ triInt A B P := by
    obtain ⟨a₁, b₁, c₁, ha₁, hb₁, hc₁, hs1, hM1⟩ := hM_in_T
    obtain ⟨a₂, b₂, c₂, ha₂, hb₂, hc₂, hs2, hM2⟩ := hM_in_T'
    -- Substitute C = α•A + β•B + δ•C' into hM1 and compare in affine basis (A, B, C'):
    have hM1' : M = (a₁ + c₁ * α) • A + (b₁ + c₁ * β) • B + (c₁ * δ) • C' := by
      rw [hM1, hC]; simp only [smul_add, smul_smul, add_smul]; abel
    have hrel : (a₁ + c₁ * α - a₂) • (A - C') + (b₁ + c₁ * β - b₂) • (B - C') = 0 := by
      have hdiff : ((a₁ + c₁ * α) • A + (b₁ + c₁ * β) • B + (c₁ * δ) • C') -
          (a₂ • A + b₂ • B + c₂ • C') = 0 := by rw [← hM1', ← hM2, sub_self]
      have hsum_eq : (a₁ + c₁ * α) + (b₁ + c₁ * β) + (c₁ * δ) = 1 := by
        linear_combination hs1 + c₁ * hsum
      have h1 : (a₁ + c₁ * α - a₂) + (b₁ + c₁ * β - b₂) + (c₁ * δ - c₂) = 0 := by
        linarith only [hsum_eq, hs2]
      have hc_eq : c₁ * δ - c₂ = -(a₁ + c₁ * α - a₂) - (b₁ + c₁ * β - b₂) := by linarith only [h1]
      simp only [smul_sub, sub_smul]
      rw [← hdiff]
      have hrew : (a₁ + c₁ * α) • A - a₂ • A - ((a₁ + c₁ * α) • C' - a₂ • C') +
          ((b₁ + c₁ * β) • B - b₂ • B - ((b₁ + c₁ * β) • C' - b₂ • C')) =
          (a₁ + c₁ * α) • A + (b₁ + c₁ * β) • B + (-(a₁ + c₁ * α - a₂) - (b₁ + c₁ * β - b₂) + c₂) • C' -
          (a₂ • A + b₂ • B + c₂ • C') := by
        simp only [add_smul, sub_smul, neg_smul]; abel
      rw [hrew, ← hc_eq]
      have : c₁ * δ - c₂ + c₂ = c₁ * δ := by ring
      rw [this]
    have hdet_AC'B : det2 (A - C') (B - C') ≠ 0 := by
      have : det2 (A - C') (B - C') = det2 (B - A) (C' - A) := by unfold det2; simp; ring
      rwa [this]
    obtain ⟨hEa, hEb⟩ := linear_combo_eq_zero_of_det2_ne_zero hdet_AC'B hrel
    have hEc : c₁ * δ = c₂ := by linear_combination -hEa - hEb + hs1 + c₁ * hsum - hs2
    -- Now express M in (A, B, P): M = a₁•A + b₂•B + (c₁*(1-β))•P!
    have hP_pos : 0 < c₁ * (1 - β) := mul_pos hc₁ h1mb
    refine ⟨a₁, b₂, c₁ * (1 - β), ha₁, hb₂, hP_pos, by linarith only [hEb, hs1], ?_⟩
    rw [hP_BC, smul_add, smul_smul, smul_smul,
      show c₁ * (1 - β) * (1 / (1 - β)) = c₁ by have := ne_of_gt h1mb; field_simp,
      show c₁ * (1 - β) * (-β / (1 - β)) = -c₁ * β by have := ne_of_gt h1mb; field_simp]
    rw [hM1]
    have hb_eq : b₂ = b₁ + c₁ * β := by linarith
    rw [hb_eq, add_smul, neg_mul, neg_smul]
    abel
  -- Separating linear functional ψ(x) = det2 (x - P) (M - P)
  let L : E2 →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun x => det2 x (M - P)
      map_add' := fun x y => det2_add_left x y (M - P)
      map_smul' := fun r x => by rw [det2_smul_left]; rfl }
  have hL_val : ∀ x : E2, L x + (-L P) = det2 (x - P) (M - P) := by
    intro x; simp only [L, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    rw [det2_sub_left]; ring
  have hL_M : L M + (-L P) = 0 := by rw [hL_val M, det2_self]
  -- Compute signs of det2 (A - P) (M - P), det2 (B - P) (M - P), det2 (C - P) (M - P), det2 (C' - P) (M - P)
  obtain ⟨ma, mb, mp, hma, hmb, hmp, hms, hM_eq_P⟩ := hM_in_ABP
  have hMP : M - P = ma • (A - P) + mb • (B - P) := by
    rw [hM_eq_P]; have : mp = 1 - ma - mb := by linarith
    rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
  set dAB := det2 (A - P) (B - P)
  have hdAB_ne : dAB ≠ 0 := by
    have : dAB = det2 (B - A) (P - A) := by unfold dAB det2; simp; ring
    rwa [this]
  have hψA : det2 (A - P) (M - P) = mb * dAB := by
    rw [hMP, det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, zero_add]
  have hψB : det2 (B - P) (M - P) = -ma * dAB := by
    rw [hMP, det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, add_zero,
      det2_antisymm (B - P) (A - P)]; ring
  have hψC : det2 (C - P) (M - P) = (-β) * (ma * dAB) := by
    rw [hCP, det2_smul_left, hψB]; ring
  have hψC' : det2 (C' - P) (M - P) = -(α / δ) * (mb * dAB) := by
    rw [hCpP, det2_smul_left, hψA]
  -- Measure-disjointness of T = ABP ∪ APC and T' = ABP ∪ BPC'
  have hdisj_T : AEDisjoint volume (tri A B P) (tri A P C) := by
    change volume (tri A B P ∩ tri A P C) = 0
    have hsub : tri A B P ∩ tri A P C ⊆
        (tri A B P \ triInt A B P) ∪ (tri A P C \ triInt A P C) := by
      rintro x ⟨h1, h2⟩
      by_contra hnot
      simp only [Set.mem_union, Set.mem_sdiff, not_or, not_and, not_not] at hnot
      obtain ⟨a₁, b₁, c₁, ha₁, hb₁, hc₁, hs1, hx1⟩ := hnot.1 h1
      obtain ⟨a₂, b₂, c₂, ha₂, hb₂, hc₂, hs2, hx2⟩ := hnot.2 h2
      have hd1 : det2 (x - P) (A - P) = -b₁ * dAB := by
        have : x - P = a₁ • (A - P) + b₁ • (B - P) := by
          rw [hx1]; have : c₁ = 1 - a₁ - b₁ := by linarith
          rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
        rw [this, det2_add_left, det2_smul_left, det2_smul_left, det2_self, mul_zero, zero_add,
          det2_antisymm (B - P) (A - P)]; ring
      have hd2 : det2 (x - P) (A - P) = c₂ * (-β) * dAB := by
        have : x - P = a₂ • (A - P) + c₂ • (C - P) := by
          rw [hx2]; have : b₂ = 1 - a₂ - c₂ := by linarith
          rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
        rw [this, hCP, det2_add_left, det2_smul_left, det2_smul_left, det2_self, mul_zero, zero_add,
          det2_smul_left, det2_antisymm (B - P) (A - P)]; ring
      have hEq : (-b₁ - c₂ * (-β)) * dAB = 0 := by linarith only [hd1, hd2]
      have h0 : -b₁ - c₂ * (-β) = 0 := (mul_eq_zero.mp hEq).resolve_right hdAB_ne
      nlinarith only [hb₁, hc₂, hβ, h0]
    exact measure_mono_null hsub (measure_union_null (tri_diff_triInt_measure_zero hdet_ABP)
      (tri_diff_triInt_measure_zero hdet_APC))
  have hdisj_T' : AEDisjoint volume (tri A B P) (tri B P C') := by
    change volume (tri A B P ∩ tri B P C') = 0
    have hsub : tri A B P ∩ tri B P C' ⊆
        (tri A B P \ triInt A B P) ∪ (tri B P C' \ triInt B P C') := by
      rintro x ⟨h1, h2⟩
      by_contra hnot
      simp only [Set.mem_union, Set.mem_sdiff, not_or, not_and, not_not] at hnot
      obtain ⟨a₁, b₁, c₁, ha₁, hb₁, hc₁, hs1, hx1⟩ := hnot.1 h1
      obtain ⟨a₂, b₂, c₂, ha₂, hb₂, hc₂, hs2, hx2⟩ := hnot.2 h2
      have hd1 : det2 (x - P) (B - P) = a₁ * dAB := by
        have : x - P = a₁ • (A - P) + b₁ • (B - P) := by
          rw [hx1]; have : c₁ = 1 - a₁ - b₁ := by linarith
          rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
        rw [this, det2_add_left, det2_smul_left, det2_smul_left, det2_self, mul_zero, add_zero]
      have hd2 : det2 (x - P) (B - P) = -(c₂ * (α / δ)) * dAB := by
        have : x - P = a₂ • (B - P) + c₂ • (C' - P) := by
          rw [hx2]; have : b₂ = 1 - a₂ - c₂ := by linarith
          rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
        rw [this, hCpP, det2_add_left, det2_smul_left, det2_smul_left, det2_self, mul_zero, zero_add,
          det2_smul_left]; ring
      have hEq : (a₁ + c₂ * (α / δ)) * dAB = 0 := by linarith only [hd1, hd2]
      have h0 : a₁ + c₂ * (α / δ) = 0 := (mul_eq_zero.mp hEq).resolve_right hdAB_ne
      have : 0 < c₂ * (α / δ) := mul_pos hc₂ (div_pos hα hδ)
      linarith only [ha₁, this, h0]
    exact measure_mono_null hsub (measure_union_null (tri_diff_triInt_measure_zero hdet_ABP)
      (tri_diff_triInt_measure_zero hdet_BPC'))
  -- Since L M + (-L P) = 0, both ∫_T and ∫_{T'} equal 0, so ∫_{APC} = ∫_{BPC'}!
  have hI_T : ∫ x in tri A B C, (L x + (-L P)) * OMA.S_mo_499635.γ x = 0 := by
    rw [integral_affine_gamma_eq A B C hdet L (-L P), hL_M, zero_mul]
  have hI_T' : ∫ x in tri A B C', (L x + (-L P)) * OMA.S_mo_499635.γ x = 0 := by
    rw [integral_affine_gamma_eq A B C' hdet' L (-L P), hM_eq, hL_M, zero_mul]
  have hcont_ψ : Continuous (fun x : E2 => (L x + (-L P)) * OMA.S_mo_499635.γ x) :=
    (L.continuous.add continuous_const).mul continuous_gamma
  have hs_T : ∫ x in tri A B C, (L x + (-L P)) * OMA.S_mo_499635.γ x =
      (∫ x in tri A B P, (L x + (-L P)) * OMA.S_mo_499635.γ x) +
      ∫ x in tri A P C, (L x + (-L P)) * OMA.S_mo_499635.γ x := by
    rw [hpart_T]
    exact MeasureTheory.setIntegral_union₀ hdisj_T (measurableSet_tri A P C).nullMeasurableSet
      (hcont_ψ.continuousOn.integrableOn_compact (isCompact_tri A B P))
      (hcont_ψ.continuousOn.integrableOn_compact (isCompact_tri A P C))
  have hs_T' : ∫ x in tri A B C', (L x + (-L P)) * OMA.S_mo_499635.γ x =
      (∫ x in tri A B P, (L x + (-L P)) * OMA.S_mo_499635.γ x) +
      ∫ x in tri B P C', (L x + (-L P)) * OMA.S_mo_499635.γ x := by
    rw [hpart_T']
    exact MeasureTheory.setIntegral_union₀ hdisj_T' (measurableSet_tri B P C').nullMeasurableSet
      (hcont_ψ.continuousOn.integrableOn_compact (isCompact_tri A B P))
      (hcont_ψ.continuousOn.integrableOn_compact (isCompact_tri B P C'))
  have hEq_int : ∫ x in tri A P C, (L x + (-L P)) * OMA.S_mo_499635.γ x =
      ∫ x in tri B P C', (L x + (-L P)) * OMA.S_mo_499635.γ x := by linarith
  -- Yet the two integrals have STRICTLY OPPOSITE signs (depending on the sign of dAB)!
  have hsign_APC : ∀ x ∈ triInt A P C,
      ∃ c > 0, L x + (-L P) = c * dAB := by
    rintro x ⟨a, b, c, ha, hb, hc, hs, rfl⟩
    have hsub : a • A + b • P + c • C - P = a • (A - P) + c • (C - P) := by
      have : b = 1 - a - c := by linarith
      rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
    refine ⟨a * mb + c * (-β) * ma,
      add_pos (mul_pos ha hmb) (mul_pos (mul_pos hc (neg_pos.mpr hβ)) hma), ?_⟩
    rw [hL_val, hsub, det2_add_left, det2_smul_left, det2_smul_left, hψA, hψC]; ring
  have hsign_BPC' : ∀ x ∈ triInt B P C',
      ∃ c > 0, L x + (-L P) = -(c * dAB) := by
    rintro x ⟨a, b, c, ha, hb, hc, hs, rfl⟩
    have hsub : a • B + b • P + c • C' - P = a • (B - P) + c • (C' - P) := by
      have : b = 1 - a - c := by linarith
      rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
    refine ⟨a * ma + c * (α / δ) * mb, add_pos (mul_pos ha hma) (mul_pos (mul_pos hc (div_pos hα hδ)) hmb), ?_⟩
    rw [hL_val, hsub, det2_add_left, det2_smul_left, det2_smul_left, hψB, hψC']; ring
  rcases lt_or_gt_of_ne hdAB_ne with hdAB_neg | hdAB_pos
  · have h1 : ∫ x in tri A P C, (L x + (-L P)) * OMA.S_mo_499635.γ x < 0 := by
      have hp : 0 < ∫ x in tri A P C, -((L x + (-L P)) * OMA.S_mo_499635.γ x) :=
        integral_tri_pos_of_pos_on_triInt hdet_APC hcont_ψ.neg fun x hx => by
          obtain ⟨c, hc, hval⟩ := hsign_APC x hx
          rw [hval]; exact neg_pos.mpr (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hc hdAB_neg) (gamma_pos x))
      rw [MeasureTheory.integral_neg] at hp; linarith
    have h2 : 0 < ∫ x in tri B P C', (L x + (-L P)) * OMA.S_mo_499635.γ x :=
      integral_tri_pos_of_pos_on_triInt hdet_BPC' hcont_ψ fun x hx => by
        obtain ⟨c, hc, hval⟩ := hsign_BPC' x hx
        rw [hval]; exact mul_pos (neg_pos.mpr (mul_neg_of_pos_of_neg hc hdAB_neg)) (gamma_pos x)
    linarith
  · have h1 : 0 < ∫ x in tri A P C, (L x + (-L P)) * OMA.S_mo_499635.γ x :=
      integral_tri_pos_of_pos_on_triInt hdet_APC hcont_ψ fun x hx => by
        obtain ⟨c, hc, hval⟩ := hsign_APC x hx
        rw [hval]; exact mul_pos (mul_pos hc hdAB_pos) (gamma_pos x)
    have h2 : ∫ x in tri B P C', (L x + (-L P)) * OMA.S_mo_499635.γ x < 0 := by
      have hp : 0 < ∫ x in tri B P C', -((L x + (-L P)) * OMA.S_mo_499635.γ x) :=
        integral_tri_pos_of_pos_on_triInt hdet_BPC' hcont_ψ.neg fun x hx => by
          obtain ⟨c, hc, hval⟩ := hsign_BPC' x hx
          rw [hval]; exact neg_pos.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hc hdAB_pos)) (gamma_pos x))
      rw [MeasureTheory.integral_neg] at hp; linarith
    linarith

lemma center_swap12 (A B C : E2) :
    OMA.S_mo_499635.center A B C = OMA.S_mo_499635.center B A C := by
  unfold OMA.S_mo_499635.center
  have h : convexHull ℝ ({A, B, C} : Set E2) = convexHull ℝ ({B, A, C} : Set E2) := tri_perm_swap12 A B C
  rw [h]

/-- **Main Theorem (MathOverflow 499635).** -/
theorem main_proof (A B C C' : E2)
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hABC' : AffineIndependent ℝ ![A, B, C'])
    (hCne : C' ≠ C) :
    OMA.S_mo_499635.center A B C' ≠ OMA.S_mo_499635.center A B C := by
  have hdet : det2 (B - A) (C - A) ≠ 0 := det2_ne_zero_of_affineIndependent hABC
  have hdet' : det2 (B - A) (C' - A) ≠ 0 := det2_ne_zero_of_affineIndependent hABC'
  intro hM_eq
  -- First, since M ∈ triInt A B C ∩ triInt A B C', det2 (B - A) (C - A) and det2 (B - A) (C' - A) have the same sign!
  set M := OMA.S_mo_499635.center A B C
  obtain ⟨a₁, b₁, c₁, ha₁, hb₁, hc₁, hs1, hM1⟩ := center_mem_triInt hdet
  obtain ⟨a₂, b₂, c₂, ha₂, hb₂, hc₂, hs2, hM2⟩ := hM_eq ▸ center_mem_triInt hdet'
  have hdM1 : det2 (B - A) (M - A) = c₁ * det2 (B - A) (C - A) := by
    have : M - A = b₁ • (B - A) + c₁ • (C - A) := by
      rw [show M = OMA.S_mo_499635.center A B C from rfl, hM1]; have : a₁ = 1 - b₁ - c₁ := by linarith
      rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
    rw [this, det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, zero_add]
  have hdM2 : det2 (B - A) (M - A) = c₂ * det2 (B - A) (C' - A) := by
    have : M - A = b₂ • (B - A) + c₂ • (C' - A) := by
      rw [hM2]; have : a₂ = 1 - b₂ - c₂ := by linarith
      rw [this]; simp only [sub_smul, one_smul, smul_sub]; abel
    rw [this, det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, zero_add]
  -- Express C in the affine basis (A, B, C'): C = α•A + β•B + δ•C'
  set β := det2 (C - A) (C' - A) / det2 (B - A) (C' - A)
  set δ := det2 (B - A) (C - A) / det2 (B - A) (C' - A)
  set α := 1 - β - δ
  have hδ : 0 < δ := by
    have hEq : δ = c₂ / c₁ := by
      simp only [δ]
      rw [div_eq_div_iff hdet' (ne_of_gt hc₁)]
      linarith
    rw [hEq]; exact div_pos hc₂ hc₁
  have hsum : α + β + δ = 1 := by simp only [α]; ring
  have hC_eq : C = α • A + β • B + δ • C' := by
    have hcr := cramer_e2 hdet' (C - A)
    have h1 : C = A + (C - A) := by abel
    rw [h1, hcr]
    simp only [α, β, δ, sub_smul, one_smul, smul_sub]
    abel
  -- 4-way case split on signs of α and β
  rcases lt_trichotomy α 0 with hα_neg | hα_zero | hα_pos
  · rcases lt_trichotomy β 0 with hβ_neg | hβ_zero | hβ_pos
    · -- α < 0, β < 0 => C' ∈ triInt A B C (reverse nested!)
      have hCp_in : C' ∈ triInt A B C := by
        have hδne : δ ≠ 0 := ne_of_gt hδ
        refine ⟨-α / δ, -β / δ, 1 / δ, div_pos (by linarith) hδ, div_pos (by linarith) hδ,
          div_pos one_pos hδ, by field_simp; linarith, ?_⟩
        have h1 : δ • C' = C - α • A - β • B := by rw [hC_eq]; abel
        have h2 := congrArg (δ⁻¹ • ·) h1
        rw [smul_smul, inv_mul_cancel₀ hδne, one_smul] at h2
        rw [h2]; simp only [smul_sub, smul_smul, div_eq_inv_mul, mul_neg, mul_one, neg_smul]; abel
      exact (nested_case_ne hdet' hdet hCp_in) hM_eq.symm
    · -- α < 0, β = 0 => C' ∈ (A, C) (reverse boundary!)
      have hCp_eq : C' = (-α / δ) • A + (1 / δ) • C := by
        have hδne : δ ≠ 0 := ne_of_gt hδ
        have h1 : δ • C' = C - α • A := by rw [hC_eq, hβ_zero, zero_smul, add_zero]; abel
        have h2 := congrArg (δ⁻¹ • ·) h1
        rw [smul_smul, inv_mul_cancel₀ hδne, one_smul] at h2
        rw [h2]; simp only [smul_sub, smul_smul, div_eq_inv_mul, mul_neg, mul_one, neg_smul]; abel
      exact (boundary_case_ne hdet' hdet (div_pos (by linarith) hδ) (div_pos one_pos hδ)
        (by have := ne_of_gt hδ; field_simp; linarith) hCp_eq) hM_eq.symm
    · -- α < 0, β > 0 => crossing case with A ↔ B swapped!
      have hdet_sw : det2 (A - B) (C - B) ≠ 0 := by
        have : det2 (A - B) (C - B) = -det2 (B - A) (C - A) := by unfold det2; simp; ring
        rw [this]; exact neg_ne_zero.mpr hdet
      have hdet'_sw : det2 (A - B) (C' - B) ≠ 0 := by
        have : det2 (A - B) (C' - B) = -det2 (B - A) (C' - A) := by unfold det2; simp; ring
        rw [this]; exact neg_ne_zero.mpr hdet'
      have hC_sw : C = β • B + α • A + δ • C' := by rw [hC_eq]; abel
      have hM_sw : OMA.S_mo_499635.center B A C' = OMA.S_mo_499635.center B A C := by
        rw [center_swap12 B A C', center_swap12 B A C]
        exact (show OMA.S_mo_499635.center A B C' = OMA.S_mo_499635.center A B C from hM_eq)
      exact (crossing_case_ne hdet_sw hdet'_sw hβ_pos hα_neg hδ (by linarith) hC_sw) hM_sw
  · rcases lt_trichotomy β 0 with hβ_neg | hβ_zero | hβ_pos
    · -- α = 0, β < 0 => C' ∈ (B, C) (reverse boundary with A ↔ B!)
      have hdet_sw : det2 (A - B) (C - B) ≠ 0 := by
        have : det2 (A - B) (C - B) = -det2 (B - A) (C - A) := by unfold det2; simp; ring
        rw [this]; exact neg_ne_zero.mpr hdet
      have hdet'_sw : det2 (A - B) (C' - B) ≠ 0 := by
        have : det2 (A - B) (C' - B) = -det2 (B - A) (C' - A) := by unfold det2; simp; ring
        rw [this]; exact neg_ne_zero.mpr hdet'
      have hCp_eq : C' = (-β / δ) • B + (1 / δ) • C := by
        have hδne : δ ≠ 0 := ne_of_gt hδ
        have h1 : δ • C' = C - β • B := by rw [hC_eq, hα_zero, zero_smul, zero_add]; abel
        have h2 := congrArg (δ⁻¹ • ·) h1
        rw [smul_smul, inv_mul_cancel₀ hδne, one_smul] at h2
        rw [h2]; simp only [smul_sub, smul_smul, div_eq_inv_mul, mul_neg, mul_one, neg_smul]; abel
      have hM_sw : OMA.S_mo_499635.center B A C = OMA.S_mo_499635.center B A C' := by
        rw [center_swap12 B A C, center_swap12 B A C']
        exact (show OMA.S_mo_499635.center A B C' = OMA.S_mo_499635.center A B C from hM_eq).symm
      exact (boundary_case_ne hdet'_sw hdet_sw (div_pos (by linarith) hδ) (div_pos one_pos hδ)
        (by have := ne_of_gt hδ; field_simp; linarith) hCp_eq) hM_sw
    · -- α = 0, β = 0 => δ = 1 => C = C', contradiction!
      have hδ1 : δ = 1 := by linarith
      apply hCne
      rw [hC_eq, hα_zero, hβ_zero, hδ1]; simp
    · -- α = 0, β > 0 => C ∈ (B, C') (boundary with A ↔ B!)
      have hdet_sw : det2 (A - B) (C - B) ≠ 0 := by
        have : det2 (A - B) (C - B) = -det2 (B - A) (C - A) := by unfold det2; simp; ring
        rw [this]; exact neg_ne_zero.mpr hdet
      have hdet'_sw : det2 (A - B) (C' - B) ≠ 0 := by
        have : det2 (A - B) (C' - B) = -det2 (B - A) (C' - A) := by unfold det2; simp; ring
        rw [this]; exact neg_ne_zero.mpr hdet'
      have hC_b : C = β • B + δ • C' := by rw [hC_eq, hα_zero, zero_smul, zero_add]
      have hM_sw : OMA.S_mo_499635.center B A C' = OMA.S_mo_499635.center B A C := by
        rw [center_swap12 B A C', center_swap12 B A C]
        exact (show OMA.S_mo_499635.center A B C' = OMA.S_mo_499635.center A B C from hM_eq)
      exact (boundary_case_ne hdet_sw hdet'_sw hβ_pos hδ (by linarith) hC_b) hM_sw
  · rcases lt_trichotomy β 0 with hβ_neg | hβ_zero | hβ_pos
    · -- α > 0, β < 0 => crossing case!
      exact (crossing_case_ne hdet hdet' hα_pos hβ_neg hδ hsum hC_eq) hM_eq
    · -- α > 0, β = 0 => C ∈ (A, C') (boundary case!)
      have hC_b : C = α • A + δ • C' := by rw [hC_eq, hβ_zero, zero_smul, add_zero]
      exact (boundary_case_ne hdet hdet' hα_pos hδ (by linarith) hC_b) hM_eq
    · -- α > 0, β > 0 => C ∈ triInt A B C' (nested case!)
      exact (nested_case_ne hdet hdet' ⟨α, β, δ, hα_pos, hβ_pos, hδ, hsum, hC_eq⟩) hM_eq

end

end OMA.Mo499635

theorem OMA.solution : type_of% @OMA.S_mo_499635.main :=
  OMA.Mo499635.main_proof

