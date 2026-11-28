import OMAStatements.S_mo_279044
import Mathlib
section
open scoped BigOperators

theorem trace_layers_finset {ι : Type*} (s : Finset ι) (b w v : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmono : ∀ i ∈ s, ∀ j ∈ s, b i ≤ b j → w i ≤ w j)
    (hsums : ∀ i ∈ s, 0 ≤ ∑ j ∈ s.filter (fun j => b i ≤ b j), v j) :
    0 ≤ ∑ j ∈ s, w j * v j := by
  classical
  induction s using Finset.strongInduction generalizing w with
  | H s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨a, ha, hmin⟩ := s.exists_min_image b hs
      let t := s.filter (fun j => b a < b j)
      have hsub : t ⊆ s := Finset.filter_subset _ _
      have hproper : t ⊂ s := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hsub, ?_⟩
        intro he
        have h : a ∈ t := he.symm ▸ ha
        simpa [t] using h
      have hweight : ∀ i ∈ t, 0 ≤ w i - w a := by
        intro i hi
        exact sub_nonneg.mpr (hmono a ha i (hsub hi) (hmin i (hsub hi)))
      have horder : ∀ i ∈ t, ∀ j ∈ t, b i ≤ b j → w i - w a ≤ w j - w a :=
        fun i hi j hj h => sub_le_sub_right (hmono i (hsub hi) j (hsub hj) h) _
      have htail : ∀ i ∈ t, 0 ≤ ∑ j ∈ t.filter (fun j => b i ≤ b j), v j := by
        intro i hi
        have he : t.filter (fun j => b i ≤ b j) = s.filter (fun j => b i ≤ b j) := by
          ext j
          simp only [t, Finset.mem_filter]
          exact ⟨fun h => ⟨h.1.1,h.2⟩, fun h => ⟨⟨h.1,
            (Finset.mem_filter.mp hi).2.trans_le h.2⟩,h.2⟩⟩
        rw [he]
        exact hsums i (hsub hi)
      have hn := ih t hproper (fun i => w i - w a) hweight horder htail
      have hall : 0 ≤ ∑ j ∈ s, v j := by
        have he : s.filter (fun j => b a ≤ b j) = s := Finset.filter_true_of_mem hmin
        simpa [he] using hsums a ha
      have hzero : ∑ j ∈ t, (w j-w a)*v j = ∑ j ∈ s, (w j-w a)*v j := by
        apply Finset.sum_subset hsub
        intro j hj hnot
        have he : b j ≤ b a := by
          by_contra! hh
          exact hnot (Finset.mem_filter.mpr ⟨hj,hh⟩)
        have hwj := le_antisymm (hmono j hj a ha he) (hmono a ha j hj (hmin j hj))
        simp [hwj]
      rw [hzero] at hn
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at hn
      linarith [mul_nonneg (hw a ha) hall]
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

theorem trace_layers {ι : Type*} [Fintype ι] (b w v : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmono : ∀ i j, b i ≤ b j → w i ≤ w j)
    (hsums : ∀ i, 0 ≤ ∑ j ∈ Finset.univ.filter (fun j => b i ≤ b j), v j) :
    0 ≤ ∑ j, w j * v j :=
  trace_layers_finset Finset.univ b w v (fun i _ => hw i)
    (fun i _ j _ => hmono i j) (fun i _ => hsums i)
end

section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace Trace279044

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem trace_pair_mono {W U V : Matrix n n ℂ} (hW : 0 ≤ W) (hUV : U ≤ V) :
    (W*U).trace.re ≤ (W*V).trace.re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hW
  have hn := (Matrix.le_iff.mp hUV).mul_mul_conjTranspose_same C
  have hreal := (RCLike.nonneg_iff.mp hn.trace_nonneg).1
  rw [Matrix.trace_mul_cycle] at hreal
  simpa [Matrix.star_eq_conjTranspose, Matrix.mul_sub, Matrix.trace_sub, sub_nonneg] using hreal

theorem inverse_order {U V : Matrix n n ℂ} (hU : IsStrictlyPositive U) (hV : IsStrictlyPositive V)
    (hUV : U ≤ V) : V⁻¹ ≤ U⁻¹ := by
  rw [Matrix.nonsing_inv_eq_ringInverse, Matrix.nonsing_inv_eq_ringInverse]
  exact CStarAlgebra.antitoneOn_ringInverse hU hV hUV

noncomputable def phi (X Z : Matrix n n ℂ) : ℝ := (X * (X+Z)⁻¹).trace.re

theorem phi_add_complement (X Z : Matrix n n ℂ) (h : IsStrictlyPositive (X+Z)) :
    phi X Z + (Z * (X+Z)⁻¹).trace.re = (1: Matrix n n ℂ).trace.re := by
  unfold phi
  rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.add_mul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit)]

set_option maxHeartbeats 800000 in
theorem phi_mono {X Z U V : Matrix n n ℂ} (hX : 0 ≤ X) (hV : 0 ≤ V)
    (hXU : X ≤ U) (hVZ : V ≤ Z) (hmid : IsStrictlyPositive (X+V)) :
    phi X Z ≤ phi U V := by
  have hxu : X+V ≤ U+V := by
    simpa only [Matrix.le_iff, add_sub_add_right_eq_sub] using Matrix.le_iff.mp hXU
  have hvz : X+V ≤ X+Z := by
    simpa only [Matrix.le_iff, add_sub_add_left_eq_sub] using Matrix.le_iff.mp hVZ
  have hm1 := trace_pair_mono hX (inverse_order hmid (hmid.of_le hvz) hvz)
  have hm2 := trace_pair_mono hV (inverse_order hmid (hmid.of_le hxu) hxu)
  have hm3 := phi_add_complement X V hmid
  have hm4 := phi_add_complement U V (hmid.of_le hxu)
  change phi X Z ≤ phi X V at hm1
  linarith

theorem phi_scale (X Z : Matrix n n ℂ) (r : ℝ) (hr : r ≠ 0) (h : IsUnit (X+Z)) :
    phi (r • X) (r • Z) = phi X Z := by
  have hinv : (r • (X+Z))⁻¹ = r⁻¹ • (X+Z)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hr, one_smul,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp h)]
  unfold phi
  rw [← smul_add, hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ hr, one_smul]

end Trace279044
end

section
namespace OMA.S_mo_279044
open Matrix
open scoped ComplexOrder Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

noncomputable def traceProj (Y : Matrix κ ι ℂ) := Y * (Yᴴ * Y)⁻¹ * Yᴴ

def traceFrame (A : Matrix ι ι ℂ) := fromRows A (1 : Matrix ι ι ℂ)

theorem traceFrame_gram (A : Matrix ι ι ℂ) :
    (traceFrame A)ᴴ * traceFrame A = 1 + Aᴴ * A := by
  simp [traceFrame, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows, add_comm]

theorem traceGram_unit (A : Matrix ι ι ℂ) : IsUnit (1 + Aᴴ * A).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  exact (Matrix.PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self A)).isUnit

theorem trace_push (A : Matrix ι ι ℂ) : A * (1 + Aᴴ * A)⁻¹ * Aᴴ =
    1 - (1 + A * Aᴴ)⁻¹ := by
  let G := 1 + Aᴴ * A
  let H := 1 + A * Aᴴ
  have hg : IsUnit G.det := traceGram_unit A
  have hh : IsUnit H.det := by simpa [H] using traceGram_unit Aᴴ
  have hx : H*A = A*G := by dsimp [G,H]; noncomm_ring
  change A * G⁻¹ * Aᴴ = 1-H⁻¹
  have hx' : H*(A*G⁻¹*Aᴴ) = H*(1-H⁻¹) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hx, mul_nonsing_inv_cancel_right _ _ hg,
      mul_sub, mul_one, mul_nonsing_inv _ hh]
    dsimp [H]
    abel
  have hz := congrArg (H⁻¹ * ·) hx'
  simpa only [nonsing_inv_mul_cancel_left _ _ hh] using hz

theorem traceProj_blocks (A : Matrix ι ι ℂ) :
    traceProj (traceFrame A) = fromBlocks
      (1 - (1 + A * Aᴴ)⁻¹) (A * (1 + Aᴴ * A)⁻¹)
      ((1 + Aᴴ * A)⁻¹ * Aᴴ) ((1 + Aᴴ * A)⁻¹) := by
  rw [traceProj, traceFrame_gram,traceFrame,conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromRows_mul, fromRows_mul_fromCols]
  simp [trace_push]

theorem traceProj_top (A : Matrix ι ι ℂ) (i : ι) :
    traceProj (traceFrame A) (.inl i) (.inl i) = (1 - (1 + A * Aᴴ)⁻¹) i i := by
  rw [traceProj_blocks]; rfl

theorem traceProj_bottom (A : Matrix ι ι ℂ) (i : ι) :
    traceProj (traceFrame A) (.inr i) (.inr i) = ((1 + Aᴴ * A)⁻¹) i i := by
  rw [traceProj_blocks]; rfl

theorem traceProj_right (Y : Matrix κ ι ℂ) (B : Matrix ι ι ℂ) (hb : IsUnit B) :
    traceProj (Y * B) = traceProj Y := by
  have hb₁ := (Matrix.isUnit_iff_isUnit_det _).mp hb
  have hb₂ := (Matrix.isUnit_iff_isUnit_det _).mp (show IsUnit Bᴴ by simpa using hb)
  simp only [traceProj, conjTranspose_mul]
  rw [show Bᴴ * Yᴴ * (Y * B) = Bᴴ * (Yᴴ * Y) * B by simp only [Matrix.mul_assoc]]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hb₁,
    nonsing_inv_mul_cancel_left _ _ hb₂]

theorem traceProj_weight (A : Matrix ι ι ℂ) (w : ι → ℝ) :
    (∑ i, w i * (traceProj (traceFrame A) (.inl i) (.inl i)).re) +
    (∑ i, w i * (traceProj (traceFrame A) (.inr i) (.inr i)).re) =
    (∑ i, w i) - (diagonal (fun i => (w i : ℂ)) * (1 + A * Aᴴ)⁻¹).trace.re +
      (diagonal (fun i => (w i : ℂ)) * (1 + Aᴴ * A)⁻¹).trace.re := by
  simp [traceProj_top,traceProj_bottom,Matrix.trace,Matrix.diag,Complex.re_sum,
    mul_sub,Finset.sum_sub_distrib]

theorem traceProj_top_star (A : Matrix ι ι ℂ) (i : ι) :
    traceProj (traceFrame Aᴴ) (.inl i) (.inl i) = (1 - (1 + Aᴴ * A)⁻¹) i i := by
  simp only [traceProj_top, conjTranspose_conjTranspose]

theorem traceProj_bottom_star (A : Matrix ι ι ℂ) (i : ι) :
    traceProj (traceFrame Aᴴ) (.inr i) (.inr i) = ((1 + A * Aᴴ)⁻¹) i i := by
  simp only [traceProj_bottom, conjTranspose_conjTranspose]

end OMA.S_mo_279044
end

section
open Matrix
open scoped MatrixOrder ComplexOrder

namespace MO279044

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

noncomputable def weightedGram (Y : Matrix m n ℂ) (w : m → ℝ) :=
  Yᴴ * diagonal (fun i => (w i : ℂ)) * Y

noncomputable def rowScale (Y : Matrix m n ℂ) (b : m → ℝ) :=
  diagonal (fun i => (b i : ℂ)) * Y

noncomputable def hiWeight (b : m → ℝ) (τ : ℝ) (i : m) : ℝ :=
  if τ ≤ b i then 1 else 0

noncomputable def loWeight (b : m → ℝ) (τ : ℝ) (i : m) : ℝ :=
  if τ ≤ b i then 0 else 1

lemma weightedGram_mono (Y : Matrix m n ℂ) {v w : m → ℝ} (h : ∀ i, v i ≤ w i) :
    weightedGram Y v ≤ weightedGram Y w := by
  rw [Matrix.le_iff, weightedGram, weightedGram, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  apply PosSemidef.conjTranspose_mul_mul_same
  apply PosSemidef.diagonal
  intro i
  simpa using sub_nonneg.mpr (h i)

lemma weightedGram_nonneg (Y : Matrix m n ℂ) {v : m → ℝ} (h : ∀ i, 0 ≤ v i) :
    0 ≤ weightedGram Y v := by
  apply PosSemidef.nonneg
  apply PosSemidef.conjTranspose_mul_mul_same
  apply PosSemidef.diagonal
  intro i
  simpa using h i

lemma weightedGram_add (Y : Matrix m n ℂ) (v w : m → ℝ) :
    weightedGram Y v + weightedGram Y w = weightedGram Y (fun i => v i + w i) := by
  simp [weightedGram, ← Matrix.add_mul, ← Matrix.mul_add]

lemma weightedGram_smul (Y : Matrix m n ℂ) (a : ℝ) (w : m → ℝ) :
    a • weightedGram Y w = weightedGram Y (fun i => a * w i) := by
  unfold weightedGram
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
  simp only [Complex.ofReal_mul]
  rfl

lemma weightedGram_scale (Y : Matrix m n ℂ) (b w : m → ℝ) :
    weightedGram (rowScale Y b) w = weightedGram Y (fun i => (b i)^2 * w i) := by
  unfold weightedGram rowScale
  rw [conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc Yᴴ, diagonal_mul_diagonal,
    ← Matrix.mul_assoc _ (diagonal _) Y, Matrix.mul_assoc Yᴴ, diagonal_mul_diagonal]
  congr 2
  funext i
  simp [pow_two]
  ring

lemma threshold_hi (Y : Matrix m n ℂ) (b : m → ℝ) {τ : ℝ} (ht : 0 < τ) :
    (τ^2) • weightedGram Y (hiWeight b τ) ≤ weightedGram (rowScale Y b) (hiWeight b τ) := by
  rw [weightedGram_smul, weightedGram_scale]
  apply weightedGram_mono
  intro i
  by_cases h : τ ≤ b i
  · simpa [hiWeight, h] using pow_le_pow_left₀ ht.le h 2
  · simp [hiWeight, h]

lemma threshold_lo (Y : Matrix m n ℂ) (b : m → ℝ) (hb : ∀ i, 0 < b i) (τ : ℝ) :
    weightedGram (rowScale Y b) (loWeight b τ) ≤ (τ^2) • weightedGram Y (loWeight b τ) := by
  rw [weightedGram_scale, weightedGram_smul]
  apply weightedGram_mono
  intro i
  by_cases h : τ ≤ b i
  · simp [loWeight, h]
  · simpa [loWeight, h] using pow_le_pow_left₀ (hb i).le (le_of_not_ge h) 2

lemma weightedGram_posDef (Y : Matrix m n ℂ) (hY : IsUnit (Yᴴ * Y)) {w : m → ℝ}
    (hw : ∀ i, 0 < w i) : (weightedGram Y w).PosDef := by
  apply PosDef.conjTranspose_mul_mul_same
  · exact PosDef.diagonal fun i => by simpa using hw i
  · intro x y h
    apply Matrix.mulVec_injective_of_isUnit hY
    simpa only [← Matrix.mulVec_mulVec] using congrArg Yᴴ.mulVec h

lemma threshold_total_posDef (Y : Matrix m n ℂ) (hY : IsUnit (Yᴴ * Y))
    (b : m → ℝ) (hb : ∀ i, 0 < b i) (τ : ℝ) :
    (weightedGram (rowScale Y b) (hiWeight b τ) +
      weightedGram (rowScale Y b) (loWeight b τ)).PosDef := by
  rw [weightedGram_scale, weightedGram_scale, weightedGram_add]
  apply weightedGram_posDef Y hY
  intro i
  by_cases h : τ ≤ b i <;> simpa [hiWeight, loWeight, h] using sq_pos_of_pos (hb i)

lemma threshold_mixed_posDef (Y : Matrix m n ℂ) (hY : IsUnit (Yᴴ * Y))
    (b : m → ℝ) (hb : ∀ i, 0 < b i) {τ : ℝ} (ht : 0 < τ) :
    ((τ^2) • weightedGram Y (hiWeight b τ) +
      weightedGram (rowScale Y b) (loWeight b τ)).PosDef := by
  rw [weightedGram_smul, weightedGram_scale, weightedGram_add]
  apply weightedGram_posDef Y hY
  intro i
  by_cases h : τ ≤ b i
  · simpa [hiWeight, loWeight, h] using sq_pos_of_pos ht
  · simpa [hiWeight, loWeight, h] using sq_pos_of_pos (hb i)

end MO279044
end

section
open Matrix
open scoped Matrix ComplexOrder
namespace TraceGlue
open OMA.S_mo_279044 MO279044
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pairDiag (P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (i : ι) : ℝ :=
  (P (.inl i) (.inl i)).re + (P (.inr i) (.inr i)).re

theorem weight_trace (Y : Matrix (ι ⊕ ι) ι ℂ) (w : ι → ℝ) :
    ∑ i, w i * pairDiag (traceProj Y) i =
      (weightedGram Y (Sum.elim w w) * (Yᴴ * Y)⁻¹).trace.re := by
  let W := diagonal fun i : ι ⊕ ι => ((Sum.elim w w i : ℝ) : ℂ)
  have he : (W * traceProj Y).trace =
      (weightedGram Y (Sum.elim w w) * (Yᴴ * Y)⁻¹).trace := by
    unfold traceProj weightedGram
    rw [← Matrix.mul_assoc W, Matrix.trace_mul_comm]
    simp only [W, Matrix.mul_assoc]
  rw [← he]
  simp [Matrix.trace, Matrix.diag, W, Complex.re_sum, Fintype.sum_sum_type, pairDiag,
    mul_add, Finset.sum_add_distrib]

theorem cut_trace (Y : Matrix (ι ⊕ ι) ι ℂ) (b : ι → ℝ) (t : ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => t ≤ b i), pairDiag (traceProj Y) i =
      (weightedGram Y (hiWeight (Sum.elim b b) t) * (Yᴴ * Y)⁻¹).trace.re := by
  have he : Sum.elim (hiWeight b t) (hiWeight b t) = hiWeight (Sum.elim b b) t := by
    funext x
    cases x <;> rfl
  rw [← he, ← weight_trace]
  simp [Finset.sum_filter, hiWeight, ite_mul]

theorem scale_graph (b : ι → ℝ) (R : Matrix ι ι ℂ) (hr : R.IsHermitian) :
    let D := diagonal fun i => (b i : ℂ)
    let A := D * R
    rowScale (traceFrame Aᴴ) (Sum.elim b b) = traceFrame A * D := by
  dsimp only
  rw [traceFrame, traceFrame, fromRows_mul, one_mul, conjTranspose_mul, hr.eq,
    diagonal_conjTranspose]
  simp only [Pi.star_def, Complex.star_def, Complex.conj_ofReal]
  ext x j
  cases x with
  | inl i => simp [rowScale, diagonal_mul, mul_diagonal, mul_assoc]
  | inr i =>
    by_cases h : i = j <;> simp [rowScale, diagonal_mul, h]

theorem weighted_difference (A : Matrix ι ι ℂ) (w : ι → ℝ) :
    ∑ i, w i * (pairDiag (traceProj (traceFrame A)) i -
        pairDiag (traceProj (traceFrame Aᴴ)) i) =
    2 * ((diagonal (fun i => (w i : ℂ)) * (1 + Aᴴ * A)⁻¹).trace.re -
        (diagonal (fun i => (w i : ℂ)) * (1 + A * Aᴴ)⁻¹).trace.re) := by
  have h1 := traceProj_weight A w
  have h2 := traceProj_weight Aᴴ w
  simp only [conjTranspose_conjTranspose] at h2
  simp only [pairDiag, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith
end TraceGlue
end

section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Trace279044

open OMA.S_mo_279044 MO279044 TraceGlue

theorem full_gram {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (Y : Matrix m n ℂ) (b : m → ℝ) (t : ℝ) :
    weightedGram Y (hiWeight b t) + weightedGram Y (loWeight b t) = Yᴴ * Y := by
  rw [weightedGram_add]
  have hs : (fun i => hiWeight b t i + loWeight b t i) = fun _ => (1:ℝ) := by
    funext i
    by_cases h : t ≤ b i <;> simp [hiWeight, loWeight, h]
  rw [hs]
  simp [weightedGram]

theorem graph_cut_scale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : Matrix (ι ⊕ ι) ι ℂ) (hY : IsUnit (Yᴴ * Y))
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (t : ℝ) (ht : 0 < t) :
    ∑ i ∈ Finset.univ.filter (fun i => t ≤ b i), pairDiag (traceProj Y) i ≤
    ∑ i ∈ Finset.univ.filter (fun i => t ≤ b i),
      pairDiag (traceProj (rowScale Y (Sum.elim b b))) i := by
  let e := Sum.elim b b
  let Y' := rowScale Y e
  let X := weightedGram Y (hiWeight e t)
  let Z := weightedGram Y (loWeight e t)
  let U := weightedGram Y' (hiWeight e t)
  let V := weightedGram Y' (loWeight e t)
  have he (i) : 0 < e i := by cases i <;> apply hb
  have hx : 0 ≤ t^2 • X := by
    apply smul_nonneg (sq_nonneg t)
    exact weightedGram_nonneg Y (fun i => by dsimp [hiWeight]; split <;> norm_num)
  have hv : 0 ≤ V := weightedGram_nonneg Y' (fun i => by dsimp [loWeight]; split <;> norm_num)
  have hmid : IsStrictlyPositive (t^2 • X + V) :=
    (threshold_mixed_posDef Y hY e he ht).isStrictlyPositive
  have h := phi_mono hx hv (threshold_hi Y e ht) (threshold_lo Y e he t) hmid
  have hg : X + Z = Yᴴ * Y := full_gram Y e t
  have hg' : U + V = Y'ᴴ * Y' := full_gram Y' e t
  have hun : IsUnit (X+Z) := hg.symm ▸ hY
  change phi (t^2 • X) (t^2 • Z) ≤ phi U V at h
  rw [phi_scale X Z _ (ne_of_gt (sq_pos_of_pos ht)) hun] at h
  unfold phi at h
  rw [hg, hg'] at h
  simpa only [cut_trace] using h

theorem diagonal_weighted {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b w : ι → ℝ) (R : Matrix ι ι ℂ) (hb : ∀ i, 0 < b i) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ i j, b i ≤ b j → w i ≤ w j) (hr : R.IsHermitian) :
    let D := diagonal fun i => (b i : ℂ)
    let W := diagonal fun i => (w i : ℂ)
    (W * (1+D*R^2*D)⁻¹).trace.re ≤ (W * (1+R*D^2*R)⁻¹).trace.re := by
  let D := diagonal fun i => (b i : ℂ)
  let A := D*R
  let Y := traceFrame Aᴴ
  have hY : IsUnit (Yᴴ*Y) := by
    rw [show Yᴴ*Y = 1 + Aᴴᴴ*Aᴴ from traceFrame_gram Aᴴ]
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (traceGram_unit Aᴴ)
  have hd : IsUnit D := Matrix.isUnit_diagonal.mpr <| Pi.isUnit_iff.mpr fun i =>
    isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (hb i).ne')
  have hs := scale_graph b R hr
  change rowScale Y (Sum.elim b b) = traceFrame A * D at hs
  have hv (i : ι) : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j => b i ≤ b j),
      (pairDiag (traceProj (traceFrame A)) j - pairDiag (traceProj Y) j) := by
    rw [Finset.sum_sub_distrib, sub_nonneg]
    have h := graph_cut_scale Y hY b hb (b i) (hb i)
    rw [hs, traceProj_right _ _ hd] at h
    exact h
  have h := trace_layers b w _ hw hm hv
  change 0 ≤ ∑ j, w j * (pairDiag (traceProj (traceFrame A)) j -
      pairDiag (traceProj (traceFrame Aᴴ)) j) at h
  rw [weighted_difference] at h
  have hA : Aᴴ = R*D := by
    dsimp [A,D]
    simp only [conjTranspose_mul, hr.eq, diagonal_conjTranspose, Pi.star_def,
      Complex.star_def, Complex.conj_ofReal]
  rw [hA] at h
  dsimp only [A] at h
  dsimp only
  simp only [sq, Matrix.mul_assoc] at h ⊢
  linarith

end Trace279044
end

section
open scoped ComplexOrder Topology Matrix
open Matrix Filter

namespace MO279044Work

private abbrev D {n : ℕ} (b : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun i => (b i : ℂ)

private noncomputable def traceSide {n : ℕ} (W B R : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (trace (W * (1 + B * R^2 * B)⁻¹)).re

private lemma traceSideCont {n : ℕ} (W B R : Matrix (Fin n) (Fin n) ℂ)
    (hB : B.IsHermitian) (hR : R.IsHermitian) :
    ContinuousAt (fun p : (Matrix (Fin n) (Fin n) ℂ) × (Matrix (Fin n) (Fin n) ℂ) =>
      traceSide W p.1 p.2) (B,R) := by
  have gram : (B * R^2 * B).PosSemidef := by
    simpa only [conjTranspose_mul, hB.eq, hR.eq, sq, Matrix.mul_assoc]
      using posSemidef_conjTranspose_mul_self (R * B)
  have detunit : IsUnit ((1 + B * R ^ 2 * B).det) := (isUnit_iff_isUnit_det _).mp (PosDef.one.add_posSemidef gram).isUnit
  have invct := continuousAt_matrix_inv (1 + B * R^2 * B) (by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp detunit))
  have inner : Continuous (fun p : (Matrix (Fin n) (Fin n) ℂ) × (Matrix (Fin n) (Fin n) ℂ) =>
      1 + p.1 * p.2 ^ 2 * p.1) := by fun_prop
  have h : ContinuousAt (fun p : (Matrix (Fin n) (Fin n) ℂ) × (Matrix (Fin n) (Fin n) ℂ) =>
      W * (1 + p.1 * p.2^2 * p.1)⁻¹) (B,R) :=
    continuousAt_const.mul (invct.comp_of_eq inner.continuousAt rfl)
  exact Complex.continuous_re.continuousAt.comp_of_eq
    (continuous_id.matrix_trace.continuousAt.comp_of_eq h rfl) rfl

private lemma diagHerm {n : ℕ} (b : Fin n → ℝ) : (D b).IsHermitian :=
  isHermitian_diagonal_of_self_adjoint _ (funext fun _ => by simp)

private lemma diagLimit {n : ℕ} (b w : Fin n → ℝ) (R : Matrix (Fin n) (Fin n) ℂ)
    (hR : R.IsHermitian)
    (hpos : ∀ x : ℝ, 0 < x →
      traceSide (D w) (D (fun i => b i + x)) R ≤ traceSide (D w) R (D (fun i => b i + x))) :
    traceSide (D w) (D b) R ≤ traceSide (D w) R (D b) := by
  let d := fun x : ℝ => D (fun i => b i + x)
  have hd : Continuous d := Continuous.matrix_diagonal (continuous_pi fun i =>
    Complex.continuous_ofReal.comp (continuous_const.add continuous_id))
  have h0 : d 0 = D b := by simp [d]
  have hL := (traceSideCont (D w) (D b) R (diagHerm b) hR)
  have hR' := (traceSideCont (D w) R (D b) hR (diagHerm b))
  have left : ContinuousAt (fun x => traceSide (D w) (d x) R) 0 :=
    hL.comp_of_eq (f := fun x : ℝ => (d x, R)) (x := (0 : ℝ))
       (hd.prodMk continuous_const).continuousAt (by rw [h0])
  have right : ContinuousAt (fun x => traceSide (D w) R (d x)) 0 :=
    hR'.comp_of_eq (f := fun x : ℝ => (R, d x)) (x := (0 : ℝ))
       (continuous_const.prodMk hd).continuousAt (by rw [h0])
  rw [← h0]
  apply le_of_tendsto_of_tendsto (f := fun x : ℝ => traceSide (D w) (d x) R)
    (g := fun x : ℝ => traceSide (D w) R (d x)) (b := 𝓝[>] 0)
  · exact left.continuousWithinAt
  · exact right.continuousWithinAt
  · filter_upwards [self_mem_nhdsWithin] with x hx using hpos x hx

private lemma traceSideConj {n : ℕ} (u : unitary (Matrix (Fin n) (Fin n) ℂ))
    (W B R : Matrix (Fin n) (Fin n) ℂ) :
    let E := Unitary.conjStarAlgAut ℂ _ u
    traceSide (E W) (E B) (E R) = traceSide W B R := by
  let E := Unitary.conjStarAlgAut ℂ _ u
  have invu : (u : Matrix (Fin n) (Fin n) ℂ)⁻¹ = star (u : Matrix (Fin n) (Fin n) ℂ) :=
    inv_eq_left_inv (Unitary.coe_star_mul_self u)
  have invs : (star (u : Matrix (Fin n) (Fin n) ℂ))⁻¹ = (u : Matrix (Fin n) (Fin n) ℂ) :=
    inv_eq_left_inv (Unitary.coe_mul_star_self u)
  have hinv (X : Matrix (Fin n) (Fin n) ℂ) : (E X)⁻¹ = E X⁻¹ := by
    change ((u : Matrix (Fin n) (Fin n) ℂ) * X * star (u : Matrix (Fin n) (Fin n) ℂ))⁻¹ = (u : Matrix (Fin n) (Fin n) ℂ) * X⁻¹ * star (u : Matrix (Fin n) (Fin n) ℂ)
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, invu, invs, Matrix.mul_assoc]
  change (trace (E W * (1 + E B * E R ^ 2 * E B)⁻¹)).re = _
  rw [← map_pow, ← map_mul, ← map_mul, ← map_one E, ← map_add, hinv, ← map_mul]
  unfold E
  rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
  rfl

lemma traceReduction (n : ℕ)
    (hdiag : ∀ (b w : Fin n → ℝ) (R : Matrix (Fin n) (Fin n) ℂ),
      (∀ i, 0 < b i) → (∀ i, 0 ≤ w i) → (∀ i j, b i ≤ b j → w i ≤ w j) →
      R.IsHermitian → traceSide (D w) (D b) R ≤ traceSide (D w) R (D b))
    (B R : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef) (hR : R.IsHermitian)
    (s : ℝ) (hs : 0 ≤ s) :
    traceSide (hB.isHermitian.cfc (fun x => x^s)) B R ≤
      traceSide (hB.isHermitian.cfc (fun x => x^s)) R B := by
  let b := hB.isHermitian.eigenvalues
  let w := fun i => (b i)^s
  let u := hB.isHermitian.eigenvectorUnitary
  let E := Unitary.conjStarAlgAut ℂ _ u
  let T := E.symm R
  have hT : T.IsHermitian := by
    change star (E.symm R) = E.symm R
    rw [← map_star, (show star R = R from hR)]
  have hb : ∀ i, 0 ≤ b i := hB.eigenvalues_nonneg
  have hmono (i j : Fin n) (h : b i ≤ b j) : w i ≤ w j := Real.rpow_le_rpow (hb i) h hs
  have hl := diagLimit b w T hT (fun x hx => hdiag _ w T
    (fun i => add_pos_of_nonneg_of_pos (hb i) hx) (fun i => Real.rpow_nonneg (hb i) _)
    (fun i j hij => hmono i j (by simpa using hij)) hT)
  have hcf : hB.isHermitian.cfc (fun x => x^s) = E (D w) := rfl
  have hbm : B = E (D b) := hB.isHermitian.spectral_theorem
  have htm : R = E T := (E.apply_symm_apply R).symm
  rw [hcf, hbm, htm, traceSideConj, traceSideConj]
  exact hl
end MO279044Work
end

open scoped ComplexOrder
theorem OMA.solution : type_of% @OMA.S_mo_279044.main := by
  intro n B R hB hR s hs
  exact MO279044Work.traceReduction n Trace279044.diagonal_weighted B R hB hR s hs
