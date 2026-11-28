import OMAStatements.S_mo_297709

/-!
# Disproof of MathOverflow 297709 as stated in the catalogue

The statement claims that every nonzero extreme point `M` of the set of positive semidefinite
complex matrices with diagonal at most `1` has diagonal entries `0` or `1`.

The matrix `M = !![1, 1/2; 1/2, 1/4] = u * uᴴ` with `u = (1, 1/2)` is a counterexample:
its second diagonal entry is `1/4`, yet it is an extreme point.

Extremality: if `X` and `Y` are positive semidefinite with diagonal at most `1` and
`(1 - θ) X + θ Y = M` with `0 < θ < 1`, then `X 0 0 = Y 0 0 = 1` (the diagonal bound is tight
at `M 0 0 = 1`), and for a positive semidefinite `2 × 2` matrix with `Z 0 0 = 1` the determinant
bound `0 ≤ det Z` reads `normSq (Z 0 1) ≤ (Z 1 1).re`.  Writing `p = X 0 1`, `q = Y 0 1`,
the entry equations give `(1 - θ) p + θ q = 1/2` and `normSq ((1 - θ) p + θ q) = 1/4`, while
`(1 - θ) normSq p + θ normSq q ≤ 1/4`; since
`normSq ((1-θ) p + θ q) = (1-θ) normSq p + θ normSq q - (1-θ)θ normSq (p - q)`, both are
equalities, forcing `p = q = 1/2`, and then `(X 1 1).re = normSq p = 1/4`.  So `X = M`.
-/

open Matrix
open scoped ComplexOrder

namespace MD1

/-- The counterexample matrix `u * uᴴ` with `u = (1, 1/2)`. -/
noncomputable def W : Matrix (Fin 2) (Fin 2) ℂ := !![1, (2 : ℂ)⁻¹; (2 : ℂ)⁻¹, (4 : ℂ)⁻¹]

/-- A matrix whose conjugate transpose times itself is `W`. -/
noncomputable def Blk : Matrix (Fin 2) (Fin 2) ℂ := !![1, (2 : ℂ)⁻¹; 0, 0]

lemma star_two : (starRingEnd ℂ) (2 : ℂ) = 2 := by
  rw [starRingEnd_apply]
  simp

lemma star_halves_form : (starRingEnd ℂ) ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
  rw [starRingEnd_apply, show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num]
  simp

lemma star_halves : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
  rw [show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num]
  simp

lemma W_block : W = Blkᴴ * Blk := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W, Blk, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, star_two,
      star_halves_form] <;>
    norm_num

lemma W_psd : W.PosSemidef := by
  rw [W_block]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma one_le_one : ((1 : ℂ)).re ≤ 1 := by norm_num

lemma W_mem : W ∈ OMA.S_mo_297709.BoundedDiagonalPSD 2 := by
  refine ⟨W_psd, ?_⟩
  intro i
  fin_cases i
  · show (W 0 0).re ≤ 1
    rw [show W 0 0 = (1 : ℂ) from rfl]
    norm_num
  · show (W 1 1).re ≤ 1
    rw [show W 1 1 = ((4 : ℂ)⁻¹) from rfl,
      show (4 : ℂ)⁻¹ = ((1 / 4 : ℝ) : ℂ) by norm_num]
    norm_num

lemma W_ne_zero : W ≠ 0 := by
  intro h
  have h' := congrFun (congrFun h 0) 0
  rw [show W 0 0 = (1 : ℂ) from rfl] at h'
  simp at h'

/-- The key identity: weighting a difference of complex numbers by `a + b = 1`. -/
lemma normSq_combo (a b : ℝ) (hab : a + b = 1) (p q : ℂ) :
    Complex.normSq ((a : ℂ) * p + (b : ℂ) * q) =
      a * Complex.normSq p + b * Complex.normSq q - a * b * Complex.normSq (p - q) := by
  have hb : b = 1 - a := by linarith
  subst hb
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

end MD1

open MD1

/-- The counterexample matrix is an extreme point. -/
lemma md1_W_ext : W ∈ (OMA.S_mo_297709.BoundedDiagonalPSD 2).extremePoints ℝ := by
  refine mem_extremePoints_iff_left.mpr ⟨W_mem, ?_⟩
  intro X hX Y hY hseg
  obtain ⟨hXpsd, hXdiag⟩ := hX
  obtain ⟨hYpsd, hYdiag⟩ := hY
  rw [openSegment_eq_image] at hseg
  obtain ⟨θ, ⟨hθ0, hθ1⟩, hW⟩ := hseg
  have ha : (0 : ℝ) < 1 - θ := by linarith
  have hb : (0 : ℝ) < θ := hθ0
  have hab : (1 - θ) + θ = 1 := by ring
  -- Hermitian: the off-diagonal relation and vanishing imaginary parts of the diagonal
  have hX10 : star (X 0 1) = X 1 0 := by
    have h := congrFun (congrFun hXpsd.isHermitian 1) 0
    simpa [Matrix.conjTranspose_apply] using h
  have hY10 : star (Y 0 1) = Y 1 0 := by
    have h := congrFun (congrFun hYpsd.isHermitian 1) 0
    simpa [Matrix.conjTranspose_apply] using h
  have hX00ss : X 0 0 = star (X 0 0) := by
    have h := congrFun (congrFun hXpsd.isHermitian 0) 0
    simpa [Matrix.conjTranspose_apply] using h.symm
  have hY00ss : Y 0 0 = star (Y 0 0) := by
    have h := congrFun (congrFun hYpsd.isHermitian 0) 0
    simpa [Matrix.conjTranspose_apply] using h.symm
  have hX11ss : X 1 1 = star (X 1 1) := by
    have h := congrFun (congrFun hXpsd.isHermitian 1) 1
    simpa [Matrix.conjTranspose_apply] using h.symm
  -- entry equations
  have e00 : ((1 - θ : ℝ) : ℂ) * X 0 0 + ((θ : ℝ) : ℂ) * Y 0 0 = 1 := by
    have h := congrFun (congrFun hW 0) 0
    simpa [W, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul] using h
  have e01 : ((1 - θ : ℝ) : ℂ) * X 0 1 + ((θ : ℝ) : ℂ) * Y 0 1 = (2 : ℂ)⁻¹ := by
    have h := congrFun (congrFun hW 0) 1
    simpa [W, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul] using h
  have e11 : ((1 - θ : ℝ) : ℂ) * X 1 1 + ((θ : ℝ) : ℂ) * Y 1 1 = (4 : ℂ)⁻¹ := by
    have h := congrFun (congrFun hW 1) 1
    simpa [W, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul] using h
  -- the first diagonal entries are both `1`
  have hX00im : (X 0 0).im = 0 := by
    have h := congrArg Complex.im hX00ss
    simp at h
    linarith
  have hY00im : (Y 0 0).im = 0 := by
    have h := congrArg Complex.im hY00ss
    simp at h
    linarith
  have e00re : (1 - θ) * (X 0 0).re + θ * (Y 0 0).re = 1 := by
    have h := congrArg Complex.re e00
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re]
      at h
    linarith
  have hX00re : (X 0 0).re = 1 := by
    have h2 := hYdiag 0
    have hb' : (0 : ℝ) ≤ θ := le_of_lt hb
    have hmul : θ * (Y 0 0).re ≤ θ * 1 := mul_le_mul_of_nonneg_left h2 hb'
    nlinarith [e00re, hmul, hXdiag 0, ha, hab]
  have hY00re : (Y 0 0).re = 1 := by
    have h1 := hXdiag 0
    have ha' : (0 : ℝ) ≤ 1 - θ := le_of_lt ha
    have hmul : (1 - θ) * (X 0 0).re ≤ (1 - θ) * 1 := mul_le_mul_of_nonneg_left h1 ha'
    nlinarith [e00re, hmul, hYdiag 0, hb, hab]
  have hX00 : X 0 0 = 1 := by
    have h : X 0 0 = ((X 0 0).re : ℂ) := by
      apply Complex.ext <;> simp [hX00im]
    rw [h, hX00re]
    norm_num
  -- the determinant bound
  have hXdet : Complex.normSq (X 0 1) ≤ (X 1 1).re := by
    have hd : (0 : ℂ) ≤ X.det := hXpsd.det_nonneg
    have hdre : 0 ≤ (X.det).re := hd.1
    have hform : X.det = X 1 1 - ((Complex.normSq (X 0 1) : ℝ) : ℂ) := by
      rw [Matrix.det_fin_two, hX00, ← hX10]
      simp [Complex.mul_conj]
    rw [hform] at hdre
    simpa using hdre
  have hYdet : Complex.normSq (Y 0 1) ≤ (Y 1 1).re := by
    have hd : (0 : ℂ) ≤ Y.det := hYpsd.det_nonneg
    have hdre : 0 ≤ (Y.det).re := hd.1
    have hY00 : Y 0 0 = 1 := by
      have h : Y 0 0 = ((Y 0 0).re : ℂ) := by
        apply Complex.ext <;> simp [hY00im]
      rw [h, hY00re]
      norm_num
    have hform : Y.det = Y 1 1 - ((Complex.normSq (Y 0 1) : ℝ) : ℂ) := by
      rw [Matrix.det_fin_two, hY00, ← hY10]
      simp [Complex.mul_conj]
    rw [hform] at hdre
    simpa using hdre
  -- weighted norm squares
  have hE11re : (1 - θ) * (X 1 1).re + θ * (Y 1 1).re = 1 / 4 := by
    have h := congrArg Complex.re e11
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re]
      at h
    norm_num at h
    exact h
  have hcombo : (1 - θ) * Complex.normSq (X 0 1) + θ * Complex.normSq (Y 0 1) ≤ 1 / 4 := by
    have a1 := mul_le_mul_of_nonneg_left hXdet (le_of_lt ha)
    have b1 := mul_le_mul_of_nonneg_left hYdet (le_of_lt hb)
    linarith
  -- the weighted sum of `p` and `q`
  have hpq : Complex.normSq (((1 - θ : ℝ) : ℂ) * X 0 1 + ((θ : ℝ) : ℂ) * Y 0 1) = 1 / 4 := by
    rw [e01]
    rw [show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num]
    simp [Complex.normSq_apply]
    norm_num
  have hid := normSq_combo (1 - θ) θ (by ring) (X 0 1) (Y 0 1)
  have hnn : 0 ≤ Complex.normSq (X 0 1 - Y 0 1) := Complex.normSq_nonneg _
  have heq : (1 - θ) * Complex.normSq (X 0 1) + θ * Complex.normSq (Y 0 1) = 1 / 4 := by
    rw [hid] at hpq
    have hprod : 0 ≤ (1 - θ) * θ * Complex.normSq (X 0 1 - Y 0 1) := by
      have : (0 : ℝ) ≤ (1 - θ) * θ := le_of_lt (mul_pos ha hb)
      exact mul_nonneg this hnn
    linarith
  have hdiff : Complex.normSq (X 0 1 - Y 0 1) = 0 := by
    rw [hid] at hpq
    have hprod : 0 ≤ (1 - θ) * θ * Complex.normSq (X 0 1 - Y 0 1) := by
      have : (0 : ℝ) ≤ (1 - θ) * θ := le_of_lt (mul_pos ha hb)
      exact mul_nonneg this hnn
    have hpos : 0 < (1 - θ) * θ := mul_pos ha hb
    nlinarith
  have hpq_eq : X 0 1 = Y 0 1 := by
    have h : X 0 1 - Y 0 1 = 0 := by
      by_contra hne
      have hpos : 0 < Complex.normSq (X 0 1 - Y 0 1) := by
        rcases lt_or_eq_of_le (Complex.normSq_nonneg (X 0 1 - Y 0 1)) with h | h
        · exact h
        · exact absurd (Complex.normSq_eq_zero.mp h.symm) hne
      rw [hdiff] at hpos
      exact lt_irrefl _ hpos
    exact sub_eq_zero.mp h
  have hX01 : X 0 1 = (2 : ℂ)⁻¹ := by
    have h : ((1 - θ : ℝ) : ℂ) * X 0 1 + ((θ : ℝ) : ℂ) * Y 0 1
        = (((1 - θ) + θ : ℝ) : ℂ) * X 0 1 := by
      rw [hpq_eq]
      push_cast
      ring
    rw [h, show ((1 - θ) + θ : ℝ) = 1 by ring] at e01
    simpa using e01
  have hX11re : (X 1 1).re = 1 / 4 := by
    have hp : Complex.normSq (X 0 1) = 1 / 4 := by
      rw [hX01, show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num]
      simp [Complex.normSq_apply]
      norm_num
    have hq : Complex.normSq (Y 0 1) = 1 / 4 := by
      rw [← hpq_eq, hp]
    rw [hp] at hXdet
    rw [hq] at hYdet
    nlinarith
  have hX11 : X 1 1 = (4 : ℂ)⁻¹ := by
    have him : (X 1 1).im = 0 := by
      have h := congrArg Complex.im hX11ss
      simp at h
      linarith
    have h : X 1 1 = ((X 1 1).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [h, hX11re, show (4 : ℂ)⁻¹ = ((1 / 4 : ℝ) : ℂ) by norm_num]
  ext i j
  have hi : i = 0 ∨ i = 1 := by revert i; decide
  have hj : j = 0 ∨ j = 1 := by revert j; decide
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact hX00
  · exact hX01
  · rw [← hX10, hX01, star_halves]
    rfl
  · exact hX11

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_297709.main) := by
  intro h
  have hconcl := h 2 W W_ne_zero md1_W_ext (1 : Fin 2)
  rcases hconcl with h0 | h1
  · rw [show W 1 1 = ((4 : ℂ)⁻¹) from rfl,
      show (4 : ℂ)⁻¹ = ((1 / 4 : ℝ) : ℂ) by norm_num] at h0
    norm_num at h0
  · rw [show W 1 1 = ((4 : ℂ)⁻¹) from rfl,
      show (4 : ℂ)⁻¹ = ((1 / 4 : ℝ) : ℂ) by norm_num] at h1
    norm_num at h1
