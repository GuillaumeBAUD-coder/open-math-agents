import FormalConjectures.Other.VCDimConvex

/-!
# Proof that every convex set in `ℝ²` has additive VC dimension at most `3`

Suppose for contradiction that a convex set `C ⊆ ℝ²` shatters four points `x : Fin 4 → ℝ²` via
translates `y : Set (Fin 4) → ℝ²` (`y s + x i ∈ C ↔ i ∈ s`).
1. Explicit 2D cross-product algebra produces a nontrivial affine dependence `∑ c_i = 0`,
   `∑ c_i • x_i = 0` (Radon's theorem in `ℝ²`), splitting `Fin 4` into nonempty `P = {c_i > 0}`
   and `N = {c_i < 0}`.
2. If `|P| = 1` or `|N| = 1`, one point lies in the convex hull of the others, contradicting
   convexity of `C` on the translate realizing the complementary subset.
3. If `|P| = |N| = 2`, the diagonals `[A, C']` and `[B, D]` cross at `q`. Translating to `K` with
   `A, C', B + w, D + w ∈ K` and `B, D, A + w, C' + w ∉ K`, projecting orthogonally to `w` via
   `φ(p) = -w₁ p₀ + w₀ p₁` and along `w` via `ψ(p) = w₀ p₀ + w₁ p₁` forces the height difference
   between `[A, C']` and `[B, D]` to be strictly positive at both endpoints of their overlapping
   `φ`-intervals while vanishing at `φ(q)`, a contradiction.
-/

-- Problem: VCₙ dimension of convex sets in ℝⁿ, ℝⁿ⁺¹, ℝⁿ⁺² — hasAddVCDimAtMost three of convex r2
-- Upstream: formal-conjectures FormalConjectures/Other/VCDimConvex.lean:42 (declaration VCDimConvex.hasAddVCDimAtMost_three_of_convex_r2)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)

namespace VCDimConvexR2Proof

open VCDimConvex
open scoped EuclideanGeometry Pointwise

private def det2 (p q : ℝ²) : ℝ := p 0 * q 1 - p 1 * q 0

private lemma exists_affine_dep_four (x : Fin 4 → ℝ²) :
    ∃ c : Fin 4 → ℝ, (∃ i, c i ≠ 0) ∧ (∑ i : Fin 4, c i = 0) ∧
      (∑ i : Fin 4, c i • x i = 0) := by
  let u : ℝ² := x 1 - x 0
  let v : ℝ² := x 2 - x 0
  let w : ℝ² := x 3 - x 0
  have hrel3 : ∃ a b d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ d ≠ 0) ∧ a • u + b • v + d • w = 0 := by
    by_cases h1 : det2 v w ≠ 0
    · refine ⟨det2 v w, det2 w u, det2 u v, Or.inl h1, ?_⟩
      ext k; fin_cases k <;> simp [det2] <;> ring
    by_cases h2 : det2 w u ≠ 0
    · refine ⟨det2 v w, det2 w u, det2 u v, Or.inr (Or.inl h2), ?_⟩
      ext k; fin_cases k <;> simp [det2] <;> ring
    by_cases h3 : det2 u v ≠ 0
    · refine ⟨det2 v w, det2 w u, det2 u v, Or.inr (Or.inr h3), ?_⟩
      ext k; fin_cases k <;> simp [det2] <;> ring
    push Not at h1 h2 h3
    by_cases hu0 : u 0 ≠ 0
    · refine ⟨v 0, -u 0, 0, Or.inr (Or.inl (neg_ne_zero.mpr hu0)), ?_⟩
      ext k; fin_cases k
      · simp; ring
      · simp only [Fin.mk_one, Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
          zero_mul, add_zero, PiLp.zero_apply]
        dsimp only [det2] at h3
        linarith
    by_cases hu1 : u 1 ≠ 0
    · refine ⟨v 1, -u 1, 0, Or.inr (Or.inl (neg_ne_zero.mpr hu1)), ?_⟩
      ext k; fin_cases k
      · simp only [Fin.zero_eta, Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
          zero_mul, add_zero, PiLp.zero_apply]
        dsimp only [det2] at h3
        linarith
      · simp; ring
    push Not at hu0 hu1
    refine ⟨1, 0, 0, Or.inl one_ne_zero, ?_⟩
    ext k; fin_cases k <;> simp [hu0, hu1]
  rcases hrel3 with ⟨a, b, d, hne, hsum⟩
  let c : Fin 4 → ℝ := ![-(a + b + d), a, b, d]
  refine ⟨c, ?_, ?_, ?_⟩
  · rcases hne with ha | hb | hd
    · exact ⟨1, ha⟩
    · exact ⟨2, hb⟩
    · exact ⟨3, hd⟩
  · simp [c, Fin.sum_univ_four]
    ring
  · have hlin : a • (x 1 - x 0) + b • (x 2 - x 0) + d • (x 3 - x 0) = 0 := hsum
    ext k
    have hk := congr_arg (fun p : ℝ² => p k) hlin
    simp only [Fin.sum_univ_four, c, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.zero_apply,
      smul_eq_mul] at hk ⊢
    linarith

private lemma line_mem_of_le {K : Set ℝ²} (hK : Convex ℝ K) {w p q : ℝ²}
    (hw : w ≠ 0)
    (hφ : -w 1 * p 0 + w 0 * p 1 = -w 1 * q 0 + w 0 * q 1)
    (hψ : w 0 * p 0 + w 1 * p 1 ≤ w 0 * q 0 + w 1 * q 1)
    (hp : p ∈ K) (hqw : q + w ∈ K) :
    q ∈ K ∧ p + w ∈ K := by
  have hw2 : 0 < w 0 ^ 2 + w 1 ^ 2 := by
    by_contra hle
    have h0 : w 0 ^ 2 + w 1 ^ 2 = 0 := le_antisymm (not_lt.mp hle) (by positivity)
    have hw0 : w 0 = 0 := by nlinarith
    have hw1 : w 1 = 0 := by nlinarith
    apply hw
    ext k; fin_cases k <;> simp [hw0, hw1]
  set s : ℝ := ((w 0 * p 0 + w 1 * p 1) - (w 0 * q 0 + w 1 * q 1)) / (w 0 ^ 2 + w 1 ^ 2)
  have hs_le : s ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw2.le
  have h1s_pos : 0 < 1 - s := by linarith
  have hp_eq : p = q + s • w := by
    ext k
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have hmul : (q 0 + s * w 0) * (w 0 ^ 2 + w 1 ^ 2) = p 0 * (w 0 ^ 2 + w 1 ^ 2) := by
        have hs_mul : s * (w 0 ^ 2 + w 1 ^ 2) = (w 0 * p 0 + w 1 * p 1) - (w 0 * q 0 + w 1 * q 1) :=
          div_mul_cancel₀ _ hw2.ne'
        linear_combination w 0 * hs_mul + w 1 * hφ
      exact (mul_right_cancel₀ hw2.ne' hmul).symm
    · simp only [Fin.mk_one, Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have hmul : (q 1 + s * w 1) * (w 0 ^ 2 + w 1 ^ 2) = p 1 * (w 0 ^ 2 + w 1 ^ 2) := by
        have hs_mul : s * (w 0 ^ 2 + w 1 ^ 2) = (w 0 * p 0 + w 1 * p 1) - (w 0 * q 0 + w 1 * q 1) :=
          div_mul_cancel₀ _ hw2.ne'
        linear_combination w 1 * hs_mul - w 0 * hφ
      exact (mul_right_cancel₀ hw2.ne' hmul).symm
  have ha1 : 0 ≤ 1 / (1 - s) := by positivity
  have hb1 : 0 ≤ (-s) / (1 - s) := div_nonneg (by linarith) h1s_pos.le
  have hab1 : 1 / (1 - s) + (-s) / (1 - s) = 1 := by field_simp; ring
  constructor
  · have hq_comb : (1 / (1 - s)) • p + ((-s) / (1 - s)) • (q + w) = q := by
      rw [hp_eq]
      ext k
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp
      ring
    rw [← hq_comb]
    exact hK hp hqw ha1 hb1 hab1
  · have hpw_comb : ((-s) / (1 - s)) • p + (1 / (1 - s)) • (q + w) = p + w := by
      rw [hp_eq]
      ext k
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp
      ring
    rw [← hpw_comb]
    exact hK hp hqw hb1 ha1 (by linarith)

private lemma contra_crossing_ordered {K : Set ℝ²} (hK : Convex ℝ K) {w A1 C1 B1 D1 : ℝ²}
    {l m : ℝ} (hw : w ≠ 0) (hl0 : 0 < l) (hl1 : l < 1) (hm0 : 0 < m) (hm1 : m < 1)
    (hcr : l • A1 + (1 - l) • C1 = m • B1 + (1 - m) • D1)
    (hAC : -w 1 * A1 0 + w 0 * A1 1 ≤ -w 1 * C1 0 + w 0 * C1 1)
    (hBD : -w 1 * B1 0 + w 0 * B1 1 ≤ -w 1 * D1 0 + w 0 * D1 1)
    (hA1 : A1 ∈ K) (hC1 : C1 ∈ K) (hB1 : B1 ∉ K) (hD1 : D1 ∉ K)
    (hB1w : B1 + w ∈ K) (hD1w : D1 + w ∈ K) (hA1w : A1 + w ∉ K) (hC1w : C1 + w ∉ K) :
    False := by
  let φ : ℝ² → ℝ := fun p => -w 1 * p 0 + w 0 * p 1
  let ψ : ℝ² → ℝ := fun p => w 0 * p 0 + w 1 * p 1
  have hφ_comb : ∀ (t : ℝ) (p q : ℝ²), φ (t • p + (1 - t) • q) = t * φ p + (1 - t) * φ q := by
    intro t p q; simp only [φ, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hψ_comb : ∀ (t : ℝ) (p q : ℝ²), ψ (t • p + (1 - t) • q) = t * ψ p + (1 - t) * ψ q := by
    intro t p q; simp only [ψ, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  set q : ℝ² := l • A1 + (1 - l) • C1
  have hq_mem : q ∈ K := hK hA1 hC1 hl0.le (by linarith) (by ring)
  have hqw_mem : q + w ∈ K := by
    have hqw_eq : q + w = m • (B1 + w) + (1 - m) • (D1 + w) := by
      rw [show q = m • B1 + (1 - m) • D1 from hcr]
      ext k; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hqw_eq]
    exact hK hB1w hD1w hm0.le (by linarith) (by ring)
  have hφq1 : φ q = l * φ A1 + (1 - l) * φ C1 := hφ_comb l A1 C1
  have hφq2 : φ q = m * φ B1 + (1 - m) * φ D1 := by
    rw [show q = m • B1 + (1 - m) • D1 from hcr]; exact hφ_comb m B1 D1
  have hψq1 : ψ q = l * ψ A1 + (1 - l) * ψ C1 := hψ_comb l A1 C1
  have hψq2 : ψ q = m * ψ B1 + (1 - m) * ψ D1 := by
    rw [show q = m • B1 + (1 - m) • D1 from hcr]; exact hψ_comb m B1 D1
  by_cases hAC_eq : φ A1 = φ C1
  · have hφA : φ A1 = φ q := by rw [hφq1, ← hAC_eq]; ring
    have hφC : φ C1 = φ q := by rw [hφq1, hAC_eq]; ring
    rcases le_or_gt (ψ A1) (ψ q) with hle | hgt
    · exact hA1w (line_mem_of_le hK hw hφA hle hA1 hqw_mem).2
    · have hmul_nonpos : (1 - l) * (ψ C1 - ψ q) ≤ 0 := by
        have hpos : 0 < l * (ψ A1 - ψ q) := mul_pos hl0 (by linarith)
        have heq : (1 - l) * (ψ C1 - ψ q) + l * (ψ A1 - ψ q) = 0 := by linarith
        linarith
      have hCle : ψ C1 ≤ ψ q := sub_nonpos.mp (nonpos_of_mul_nonpos_right hmul_nonpos (by linarith))
      exact hC1w (line_mem_of_le hK hw hφC hCle hC1 hqw_mem).2
  by_cases hBD_eq : φ B1 = φ D1
  · have hφB : φ q = φ B1 := by rw [hφq2, ← hBD_eq]; ring
    have hφD : φ q = φ D1 := by rw [hφq2, hBD_eq]; ring
    rcases le_or_gt (ψ q) (ψ B1) with hle | hgt
    · exact hB1 (line_mem_of_le hK hw hφB hle hq_mem hB1w).1
    · have hmul_nonneg : 0 ≤ (1 - m) * (ψ D1 - ψ q) := by
        have hneg : m * (ψ B1 - ψ q) < 0 := mul_neg_of_pos_of_neg hm0 (by linarith)
        have heq : (1 - m) * (ψ D1 - ψ q) + m * (ψ B1 - ψ q) = 0 := by linarith
        linarith
      have hDle : ψ q ≤ ψ D1 :=
        sub_nonneg.mp (nonneg_of_mul_nonneg_right hmul_nonneg (by linarith))
      exact hD1 (line_mem_of_le hK hw hφD hDle hq_mem hD1w).1
  have hAC_lt : φ A1 < φ C1 := lt_of_le_of_ne hAC hAC_eq
  have hBD_lt : φ B1 < φ D1 := lt_of_le_of_ne hBD hBD_eq
  let f1 : ℝ → ℝ := fun t => ((φ C1 - t) / (φ C1 - φ A1)) * ψ A1 +
    ((t - φ A1) / (φ C1 - φ A1)) * ψ C1
  let f2 : ℝ → ℝ := fun t => ((φ D1 - t) / (φ D1 - φ B1)) * ψ B1 +
    ((t - φ B1) / (φ D1 - φ B1)) * ψ D1
  have hf1_mem : ∀ t, φ A1 ≤ t → t ≤ φ C1 → ∃ P ∈ K, φ P = t ∧ ψ P = f1 t := by
    intro t ht1 ht2
    set a1 := (φ C1 - t) / (φ C1 - φ A1)
    have ha1_ge : 0 ≤ a1 := div_nonneg (by linarith) (by linarith)
    have ha1_le : a1 ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have h1a1 : 1 - a1 = (t - φ A1) / (φ C1 - φ A1) := by
      dsimp only [a1]; field_simp; ring
    refine ⟨a1 • A1 + (1 - a1) • C1, hK hA1 hC1 ha1_ge (by linarith) (by ring), ?_, ?_⟩
    · rw [hφ_comb, h1a1]; dsimp only [a1]; field_simp; ring
    · rw [hψ_comb, h1a1]
  have hf2_mem : ∀ t, φ B1 ≤ t → t ≤ φ D1 → ∃ Q : ℝ², Q + w ∈ K ∧ φ Q = t ∧ ψ Q = f2 t := by
    intro t ht1 ht2
    set a2 := (φ D1 - t) / (φ D1 - φ B1)
    have ha2_ge : 0 ≤ a2 := div_nonneg (by linarith) (by linarith)
    have ha2_le : a2 ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have h1a2 : 1 - a2 = (t - φ B1) / (φ D1 - φ B1) := by
      dsimp only [a2]; field_simp; ring
    refine ⟨a2 • B1 + (1 - a2) • D1, ?_, ?_, ?_⟩
    · have heq : (a2 • B1 + (1 - a2) • D1) + w = a2 • (B1 + w) + (1 - a2) • (D1 + w) := by
        ext k; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [heq]
      exact hK hB1w hD1w ha2_ge (by linarith) (by ring)
    · rw [hφ_comb, h1a2]; dsimp only [a2]; field_simp; ring
    · rw [hψ_comb, h1a2]
  have hf1_A : f1 (φ A1) = ψ A1 := by dsimp only [f1]; field_simp; ring
  have hf1_C : f1 (φ C1) = ψ C1 := by dsimp only [f1]; field_simp; ring
  have hf2_B : f2 (φ B1) = ψ B1 := by dsimp only [f2]; field_simp; ring
  have hf2_D : f2 (φ D1) = ψ D1 := by dsimp only [f2]; field_simp; ring
  have hf1_q : f1 (φ q) = ψ q := by
    dsimp only [f1]; rw [hφq1, hψq1]; field_simp; ring
  have hf2_q : f2 (φ q) = ψ q := by
    dsimp only [f2]; rw [hφq2, hψq2]; field_simp; ring
  have hφq_gt_A : φ A1 < φ q := by
    have : 0 < (1 - l) * (φ C1 - φ A1) := mul_pos (by linarith) (by linarith)
    linarith
  have hφq_lt_C : φ q < φ C1 := by
    have : 0 < l * (φ C1 - φ A1) := mul_pos hl0 (by linarith)
    linarith
  have hφq_gt_B : φ B1 < φ q := by
    have : 0 < (1 - m) * (φ D1 - φ B1) := mul_pos (by linarith) (by linarith)
    linarith
  have hφq_lt_D : φ q < φ D1 := by
    have : 0 < m * (φ D1 - φ B1) := mul_pos hm0 (by linarith)
    linarith
  set xL : ℝ := max (φ A1) (φ B1)
  set xR : ℝ := min (φ C1) (φ D1)
  have hxL_lt_q : xL < φ q := max_lt hφq_gt_A hφq_gt_B
  have hq_lt_xR : φ q < xR := lt_min hφq_lt_C hφq_lt_D
  have hΔL : f2 xL < f1 xL := by
    rcases le_or_gt (φ A1) (φ B1) with hAB | hBA
    · have hxL : xL = φ B1 := max_eq_right hAB
      rw [hxL, hf2_B]
      rcases hf1_mem (φ B1) hAB (by linarith) with ⟨P, hPK, hPφ, hPψ⟩
      by_contra hle
      push Not at hle
      exact hB1 (line_mem_of_le hK hw hPφ (by rw [← hPψ] at hle; exact hle) hPK hB1w).1
    · have hxL : xL = φ A1 := max_eq_left hBA.le
      rw [hxL, hf1_A]
      rcases hf2_mem (φ A1) hBA.le (by linarith) with ⟨Q, hQwK, hQφ, hQψ⟩
      by_contra hle
      push Not at hle
      exact hA1w (line_mem_of_le hK hw hQφ.symm (by rw [← hQψ] at hle; exact hle) hA1 hQwK).2
  have hΔR : f2 xR < f1 xR := by
    rcases le_or_gt (φ C1) (φ D1) with hCD | hDC
    · have hxR : xR = φ C1 := min_eq_left hCD
      rw [hxR, hf1_C]
      rcases hf2_mem (φ C1) (by linarith) hCD with ⟨Q, hQwK, hQφ, hQψ⟩
      by_contra hle
      push Not at hle
      exact hC1w (line_mem_of_le hK hw hQφ.symm (by rw [← hQψ] at hle; exact hle) hC1 hQwK).2
    · have hxR : xR = φ D1 := min_eq_right hDC.le
      rw [hxR, hf2_D]
      rcases hf1_mem (φ D1) (by linarith) hDC.le with ⟨P, hPK, hPφ, hPψ⟩
      by_contra hle
      push Not at hle
      exact hD1 (line_mem_of_le hK hw hPφ (by rw [← hPψ] at hle; exact hle) hPK hD1w).1
  have haff : (xR - xL) * (f1 (φ q) - f2 (φ q)) =
      (xR - φ q) * (f1 xL - f2 xL) + (φ q - xL) * (f1 xR - f2 xR) := by
    dsimp only [f1, f2]
    field_simp
    ring
  rw [hf1_q, hf2_q, sub_self, mul_zero] at haff
  have hpos1 : 0 < (xR - φ q) * (f1 xL - f2 xL) := mul_pos (by linarith) (by linarith)
  have hpos2 : 0 < (φ q - xL) * (f1 xR - f2 xR) := mul_pos (by linarith) (by linarith)
  linarith

private lemma contra_crossing {K : Set ℝ²} (hK : Convex ℝ K) {w A C' B D : ℝ²}
    {lam mu : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hmu0 : 0 < mu) (hmu1 : mu < 1)
    (hcross : lam • A + (1 - lam) • C' = mu • B + (1 - mu) • D)
    (hA : A ∈ K) (hC' : C' ∈ K) (hB : B ∉ K) (hD : D ∉ K)
    (hBw : B + w ∈ K) (hDw : D + w ∈ K) (hAw : A + w ∉ K) (hCw : C' + w ∉ K) :
    False := by
  have hw : w ≠ 0 := by
    intro h0
    subst h0
    simp at hBw
    exact hB hBw
  rcases le_total (-w 1 * A 0 + w 0 * A 1) (-w 1 * C' 0 + w 0 * C' 1) with hAC | hCA <;>
    rcases le_total (-w 1 * B 0 + w 0 * B 1) (-w 1 * D 0 + w 0 * D 1) with hBD | hDB
  · exact contra_crossing_ordered hK hw hlam0 hlam1 hmu0 hmu1 hcross hAC hBD
      hA hC' hB hD hBw hDw hAw hCw
  · exact contra_crossing_ordered (l := lam) (m := 1 - mu) hK hw hlam0 hlam1
      (by linarith) (by linarith)
      (by rw [sub_sub_cancel, add_comm ((1 - mu) • D), ← hcross]) hAC hDB
      hA hC' hD hB hDw hBw hAw hCw
  · exact contra_crossing_ordered (l := 1 - lam) (m := mu) hK hw
      (by linarith) (by linarith) hmu0 hmu1
      (by rw [sub_sub_cancel, add_comm ((1 - lam) • C'), hcross]) hCA hBD
      hC' hA hB hD hBw hDw hCw hAw
  · exact contra_crossing_ordered (l := 1 - lam) (m := 1 - mu) hK hw
      (by linarith) (by linarith) (by linarith) (by linarith)
      (by rw [sub_sub_cancel, sub_sub_cancel, add_comm ((1 - lam) • C'),
        add_comm ((1 - mu) • D), hcross]) hCA hDB
      hC' hA hD hB hDw hBw hCw hAw

private lemma contra_singleton {C : Set ℝ²} (hC : Convex ℝ C)
    {x : Fin 4 → ℝ²} {y : Set (Fin 4) → ℝ²}
    (hxy : ∀ i s, y s + x i ∈ C ↔ i ∈ s)
    {c : Fin 4 → ℝ} (hsum0 : ∑ i : Fin 4, c i = 0) (hvec0 : ∑ i : Fin 4, c i • x i = 0)
    {i0 : Fin 4} (hi0 : 0 < c i0) (hother : ∀ i : Fin 4, i ≠ i0 → c i ≤ 0) : False := by
  let s : Set (Fin 4) := {i | i ≠ i0}
  let N : Finset (Fin 4) := Finset.univ.erase i0
  have hsumN : ∑ i ∈ N, (-c i) = c i0 := by
    have hsplit : c i0 + ∑ i ∈ N, c i = 0 := by
      rw [← hsum0]
      exact Finset.add_sum_erase Finset.univ c (Finset.mem_univ i0)
    rw [Finset.sum_neg_distrib]
    linarith
  have hvecN : ∑ i ∈ N, (-c i) • x i = c i0 • x i0 := by
    have hsplit : c i0 • x i0 + ∑ i ∈ N, c i • x i = 0 := by
      rw [← hvec0]
      exact Finset.add_sum_erase Finset.univ (fun i => c i • x i) (Finset.mem_univ i0)
    simp_rw [neg_smul, Finset.sum_neg_distrib]
    exact neg_eq_iff_add_eq_zero.mpr (by rw [add_comm]; exact hsplit)
  let w : Fin 4 → ℝ := fun i => (-c i) / c i0
  have hw_nonneg : ∀ i ∈ N, 0 ≤ w i := by
    intro i hi
    have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
    exact div_nonneg (by linarith [hother i hne]) hi0.le
  have hw_sum : ∑ i ∈ N, w i = 1 := by
    simp only [w, ← Finset.sum_div, hsumN, div_self hi0.ne']
  have hmem : ∀ i ∈ N, y s + x i ∈ C := by
    intro i hi
    exact (hxy i s).mpr (Finset.mem_erase.mp hi).1
  have hcomb_mem : ∑ i ∈ N, w i • (y s + x i) ∈ C :=
    hC.sum_mem hw_nonneg hw_sum hmem
  have hcomb_eq : ∑ i ∈ N, w i • (y s + x i) = y s + x i0 := by
    simp_rw [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hw_sum, one_smul]
    congr 1
    have h1 : ∑ i ∈ N, w i • x i = (c i0)⁻¹ • ∑ i ∈ N, (-c i) • x i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [w, div_eq_inv_mul, mul_smul]
    rw [h1, hvecN, smul_smul, inv_mul_cancel₀ hi0.ne', one_smul]
  rw [hcomb_eq] at hcomb_mem
  exact ((hxy i0 s).mp hcomb_mem) rfl

end VCDimConvexR2Proof

open VCDimConvex VCDimConvexR2Proof
open scoped EuclideanGeometry Pointwise

theorem OMA.solution : type_of% @VCDimConvex.hasAddVCDimAtMost_three_of_convex_r2 := by
  intro C hC x y hxy
  rcases exists_affine_dep_four x with ⟨c, ⟨i_nz, hi_nz⟩, hsum0, hvec0⟩
  let P : Finset (Fin 4) := Finset.univ.filter (fun i => 0 < c i)
  let N : Finset (Fin 4) := Finset.univ.filter (fun i => c i < 0)
  have hP_ne : P.Nonempty := by
    by_contra hP
    rw [Finset.not_nonempty_iff_eq_empty] at hP
    have hle : ∀ i : Fin 4, c i ≤ 0 := by
      intro i
      by_contra hgt
      have hiP : i ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ i, not_le.mp hgt⟩
      rw [hP] at hiP
      exact Finset.notMem_empty i hiP
    have hlt : c i_nz < 0 := lt_of_le_of_ne (hle i_nz) hi_nz
    have hsum_neg : ∑ i : Fin 4, c i < 0 := by
      have hsplit : c i_nz + ∑ i ∈ Finset.univ.erase i_nz, c i = ∑ i : Fin 4, c i :=
        Finset.add_sum_erase Finset.univ c (Finset.mem_univ i_nz)
      have hrest : ∑ i ∈ Finset.univ.erase i_nz, c i ≤ 0 :=
        Finset.sum_nonpos fun i _ => hle i
      linarith
    linarith
  have hN_ne : N.Nonempty := by
    by_contra hN
    rw [Finset.not_nonempty_iff_eq_empty] at hN
    have hge : ∀ i : Fin 4, 0 ≤ c i := by
      intro i
      by_contra hlt
      have hiN : i ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ i, not_le.mp hlt⟩
      rw [hN] at hiN
      exact Finset.notMem_empty i hiN
    have hgt : 0 < c i_nz := lt_of_le_of_ne (hge i_nz) hi_nz.symm
    have hsum_pos : 0 < ∑ i : Fin 4, c i := by
      have hsplit : c i_nz + ∑ i ∈ Finset.univ.erase i_nz, c i = ∑ i : Fin 4, c i :=
        Finset.add_sum_erase Finset.univ c (Finset.mem_univ i_nz)
      have hrest : 0 ≤ ∑ i ∈ Finset.univ.erase i_nz, c i :=
        Finset.sum_nonneg fun i _ => hge i
      linarith
    linarith
  have hdisj : Disjoint P N := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by linarith
  have hcard_sum : P.card + N.card ≤ 4 := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact le_trans (Finset.card_le_univ _) (by simp)
  have hP1 : 1 ≤ P.card := Finset.card_pos.mpr hP_ne
  have hN1 : 1 ≤ N.card := Finset.card_pos.mpr hN_ne
  by_cases hP_eq1 : P.card = 1
  · rcases Finset.card_eq_one.mp hP_eq1 with ⟨i0, hi0_eq⟩
    have hi0_pos : 0 < c i0 := by
      have : i0 ∈ P := hi0_eq ▸ Finset.mem_singleton_self i0
      exact (Finset.mem_filter.mp this).2
    have hother : ∀ i : Fin 4, i ≠ i0 → c i ≤ 0 := by
      intro i hi
      by_contra hgt
      have hiP : i ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ i, not_le.mp hgt⟩
      rw [hi0_eq, Finset.mem_singleton] at hiP
      exact hi hiP
    exact contra_singleton hC hxy hsum0 hvec0 hi0_pos hother
  by_cases hN_eq1 : N.card = 1
  · rcases Finset.card_eq_one.mp hN_eq1 with ⟨i0, hi0_eq⟩
    have hi0_neg : c i0 < 0 := by
      have : i0 ∈ N := hi0_eq ▸ Finset.mem_singleton_self i0
      exact (Finset.mem_filter.mp this).2
    have hother : ∀ i : Fin 4, i ≠ i0 → -c i ≤ 0 := by
      intro i hi
      by_contra hgt
      have hiN : i ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ i, by linarith⟩
      rw [hi0_eq, Finset.mem_singleton] at hiN
      exact hi hiN
    have hsum0' : ∑ i : Fin 4, (-c i) = 0 := by rw [Finset.sum_neg_distrib, hsum0, neg_zero]
    have hvec0' : ∑ i : Fin 4, (-c i) • x i = 0 := by
      simp_rw [neg_smul, Finset.sum_neg_distrib, hvec0, neg_zero]
    exact contra_singleton hC hxy hsum0' hvec0' (by linarith) hother
  have hP2 : P.card = 2 := by omega
  have hN2 : N.card = 2 := by omega
  rcases Finset.card_eq_two.mp hP2 with ⟨a, b', hab', hP_eq⟩
  rcases Finset.card_eq_two.mp hN2 with ⟨d1, d2, hd12, hN_eq⟩
  have ha_P : a ∈ P := by rw [hP_eq]; exact Finset.mem_insert_self a {b'}
  have hb_P : b' ∈ P := by rw [hP_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b')
  have hd1_N : d1 ∈ N := by rw [hN_eq]; exact Finset.mem_insert_self d1 {d2}
  have hd2_N : d2 ∈ N := by rw [hN_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self d2)
  have hca : 0 < c a := (Finset.mem_filter.mp ha_P).2
  have hcb : 0 < c b' := (Finset.mem_filter.mp hb_P).2
  have hcd1 : c d1 < 0 := (Finset.mem_filter.mp hd1_N).2
  have hcd2 : c d2 < 0 := (Finset.mem_filter.mp hd2_N).2
  have huniv : P ∪ N = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj, hP2, hN2]
    rfl
  have hsum_split : c a + c b' + c d1 + c d2 = 0 := by
    have h1 := Finset.sum_union hdisj (f := c)
    rw [huniv, hsum0, hP_eq, hN_eq, Finset.sum_pair hab', Finset.sum_pair hd12] at h1
    linarith
  have hvec_split : c a • x a + c b' • x b' + c d1 • x d1 + c d2 • x d2 = 0 := by
    have h1 := Finset.sum_union hdisj (f := fun i => c i • x i)
    rw [huniv, hvec0, hP_eq, hN_eq, Finset.sum_pair hab', Finset.sum_pair hd12] at h1
    ext k
    have hk := congr_arg (fun p : ℝ² => p k) h1
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul] at hk ⊢
    linarith
  set S : ℝ := c a + c b'
  have hS_pos : 0 < S := by linarith
  have hS_eqN : (-c d1) + (-c d2) = S := by linarith
  set lam : ℝ := c a / S
  set mu : ℝ := (-c d1) / S
  have hlam0 : 0 < lam := div_pos hca hS_pos
  have hlam1 : lam < 1 := (div_lt_one hS_pos).mpr (by linarith)
  have hmu0 : 0 < mu := div_pos (by linarith) hS_pos
  have hmu1 : mu < 1 := (div_lt_one hS_pos).mpr (by linarith)
  have hcross : lam • x a + (1 - lam) • x b' = mu • x d1 + (1 - mu) • x d2 := by
    ext k
    have hk := congr_arg (fun p : ℝ² => p k) hvec_split
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul] at hk ⊢
    have h1l : 1 - lam = c b' / S := by dsimp only [lam, S]; field_simp; ring
    have h1m : 1 - mu = (-c d2) / S := by dsimp only [mu]; field_simp; linarith
    rw [h1l, h1m]
    dsimp only [lam, mu]
    field_simp
    linarith
  let s1 : Set (Fin 4) := (P : Set (Fin 4))
  let s2 : Set (Fin 4) := (N : Set (Fin 4))
  let t1 : ℝ² := y s1
  let t2 : ℝ² := y s2
  let K : Set ℝ² := {p : ℝ² | t1 + p ∈ C}
  have hK : Convex ℝ K := by
    intro p hp q hq r1 r2 hr1 hr2 hr12
    have hcomb : t1 + (r1 • p + r2 • q) = r1 • (t1 + p) + r2 • (t1 + q) := by
      ext k
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      linear_combination (t1 k) * hr12.symm
    change t1 + (r1 • p + r2 • q) ∈ C
    rw [hcomb]
    exact hC hp hq hr1 hr2 hr12
  let w : ℝ² := t2 - t1
  have hd1_notP : d1 ∉ P := Finset.disjoint_right.mp hdisj hd1_N
  have hd2_notP : d2 ∉ P := Finset.disjoint_right.mp hdisj hd2_N
  have ha_notN : a ∉ N := Finset.disjoint_left.mp hdisj ha_P
  have hb_notN : b' ∉ N := Finset.disjoint_left.mp hdisj hb_P
  have hshift : ∀ i : Fin 4, t1 + (x i + w) = t2 + x i := fun i => by
    dsimp only [w]
    abel
  exact contra_crossing hK hlam0 hlam1 hmu0 hmu1 hcross
    ((hxy a s1).mpr ha_P)
    ((hxy b' s1).mpr hb_P)
    (fun h => hd1_notP ((hxy d1 s1).mp h))
    (fun h => hd2_notP ((hxy d2 s1).mp h))
    (by change t1 + (x d1 + w) ∈ C; rw [hshift]; exact (hxy d1 s2).mpr hd1_N)
    (by change t1 + (x d2 + w) ∈ C; rw [hshift]; exact (hxy d2 s2).mpr hd2_N)
    (fun h => ha_notN ((hxy a s2).mp (by rwa [← hshift])))
    (fun h => hb_notN ((hxy b' s2).mp (by rwa [← hshift])))
