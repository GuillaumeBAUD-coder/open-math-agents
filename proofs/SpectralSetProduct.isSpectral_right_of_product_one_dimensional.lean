import FormalConjectures.Arxiv.«2209.04540».SpectralSetsAndWeakTiling
import Mathlib

-- Adapted from github.com/KitaKen1/klm-7-2-spectral-product-3d (commit 2874890904e117df17d8abf1dd27254eebfb2829), (c) Kenta Kitamura (KitaKen1) and contributors, Apache-2.0 licence. Only the one-dimensional interval part (ProductInterval.fc_one_dimensional, after Greenfeld-Lev 2016) and the modules it depends on are kept; comments stripped, set_option linter lines removed.
section
open MeasureTheory Complex Real
open scoped InnerProductSpace ComplexConjugate
namespace FCBridge
variable {d : ℕ}
noncomputable def ftInd (Ω : Set (Fin d → ℝ)) (ξ : Fin d → ℝ) : ℂ :=
  ∫ x in Ω, exponentialCharacter ξ x
theorem exponentialCharacter_add (ξ η x : Fin d → ℝ) :
    exponentialCharacter (ξ + η) x = exponentialCharacter ξ x * exponentialCharacter η x := by
  unfold exponentialCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  push_cast
  ring
theorem conj_exponentialCharacter (ξ x : Fin d → ℝ) :
    conj (exponentialCharacter ξ x) = exponentialCharacter (-ξ) x := by
  unfold exponentialCharacter
  rw [← Complex.exp_conj]
  congr 1
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, map_mul, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  push_cast
  ring
theorem exponentialCharacter_zero (x : Fin d → ℝ) : exponentialCharacter 0 x = 1 := by
  simp [exponentialCharacter]
theorem conj_mul_exponentialCharacter (ξ₁ ξ₂ x : Fin d → ℝ) :
    conj (exponentialCharacter ξ₁ x) * exponentialCharacter ξ₂ x =
      exponentialCharacter (ξ₂ - ξ₁) x := by
  rw [conj_exponentialCharacter, ← exponentialCharacter_add, neg_add_eq_sub]
theorem inner_toLp_exponentialCharacter {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤)
    (ξ₁ ξ₂ : Fin d → ℝ) :
    ⟪MemLp.toLp (exponentialCharacter ξ₁) (exponentialCharacter_memLp hΩ ξ₁),
      MemLp.toLp (exponentialCharacter ξ₂) (exponentialCharacter_memLp hΩ ξ₂)⟫_ℂ =
      ftInd Ω (ξ₂ - ξ₁) := by
  rw [MeasureTheory.L2.inner_def]
  unfold ftInd
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (exponentialCharacter_memLp hΩ ξ₁),
    MemLp.coeFn_toLp (exponentialCharacter_memLp hΩ ξ₂)] with x h1 h2
  rw [h1, h2, RCLike.inner_apply', conj_mul_exponentialCharacter]
theorem ftInd_neg (Ω : Set (Fin d → ℝ)) (ξ : Fin d → ℝ) :
    ftInd Ω (-ξ) = conj (ftInd Ω ξ) := by
  unfold ftInd
  rw [← integral_conj]
  simp_rw [conj_exponentialCharacter]
theorem ftInd_zero (Ω : Set (Fin d → ℝ)) : ftInd Ω 0 = (volume.real Ω : ℂ) := by
  simp [ftInd, exponentialCharacter_zero]
theorem topologicalClosure_span_eq_top_iff {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type*} (v : ι → H) :
    (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ ↔
      ∀ f : H, (∀ i, ⟪v i, f⟫_ℂ = 0) → f = 0 := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  refine forall_congr' fun f => ?_
  have : f ∈ (Submodule.span ℂ (Set.range v))ᗮ ↔ ∀ i, ⟪v i, f⟫_ℂ = 0 := by
    rw [Submodule.mem_orthogonal]
    constructor
    · intro h i
      exact h _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro h u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact h i
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
  rw [this]
theorem spectralPair_iff {Ω Λ : Set (Fin d → ℝ)} :
    spectralPair Ω Λ ↔ NullMeasurableSet Ω volume ∧ 0 < volume Ω ∧
      ∃ hΩ : volume Ω ≠ ⊤,
        (∀ ξ₁ ∈ Λ, ∀ ξ₂ ∈ Λ, ξ₁ ≠ ξ₂ → ftInd Ω (ξ₂ - ξ₁) = 0) ∧
        ∀ f : Lp ℂ 2 (volume.restrict Ω),
          (∀ ξ ∈ Λ, ⟪MemLp.toLp (exponentialCharacter ξ) (exponentialCharacter_memLp hΩ ξ),
            f⟫_ℂ = 0) → f = 0 := by
  unfold spectralPair
  refine and_congr Iff.rfl (and_congr Iff.rfl (exists_congr fun hΩ => ?_))
  simp only [inner_toLp_exponentialCharacter hΩ]
  refine and_congr Iff.rfl ?_
  rw [topologicalClosure_span_eq_top_iff]
  simp only [Subtype.forall]
def productSet {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) :
    Set (Fin (n + m) → ℝ) :=
  {x | (fun i ↦ x (Fin.castAdd m i)) ∈ A ∧ (fun j ↦ x (Fin.natAdd n j)) ∈ B}
noncomputable def splitEquiv (n m : ℕ) : (Fin (n + m) → ℝ) ≃ᵐ (Fin n → ℝ) × (Fin m → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))
theorem splitEquiv_apply {n m : ℕ} (x : Fin (n + m) → ℝ) :
    splitEquiv n m x = (fun i => x (Fin.castAdd m i), fun j => x (Fin.natAdd n j)) := by
  ext i <;> simp [splitEquiv, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply]
theorem measurePreserving_splitEquiv (n m : ℕ) :
    MeasurePreserving (splitEquiv n m) volume volume :=
  ((volume_measurePreserving_piCongrLeft (fun _ => ℝ) finSumFinEquiv).symm _).trans
    (volume_measurePreserving_sumPiEquivProdPi (fun _ => ℝ))
theorem productSet_eq_preimage {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) :
    productSet A B = splitEquiv n m ⁻¹' (A ×ˢ B) := by
  ext x
  simp [productSet, splitEquiv_apply]
theorem volume_productSet {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) :
    volume (productSet A B) = volume A * volume B := by
  rw [productSet_eq_preimage, (measurePreserving_splitEquiv n m).measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod]
theorem volume_pos_of_isSpectral_productSet {n m : ℕ} {A : Set (Fin n → ℝ)}
    {B : Set (Fin m → ℝ)} (h : isSpectral (productSet A B)) :
    0 < volume A ∧ 0 < volume B := by
  obtain ⟨Λ, -, hpos, -⟩ := h
  rw [volume_productSet] at hpos
  refine ⟨pos_iff_ne_zero.mpr fun h0 => ?_, pos_iff_ne_zero.mpr fun h0 => ?_⟩ <;>
    simp [h0] at hpos
theorem exponentialCharacter_append {n m : ℕ} (ξ : Fin n → ℝ) (η : Fin m → ℝ)
    (x : Fin (n + m) → ℝ) :
    exponentialCharacter (Fin.append ξ η) x =
      exponentialCharacter ξ (fun i => x (Fin.castAdd m i)) *
        exponentialCharacter η (fun j => x (Fin.natAdd n j)) := by
  unfold exponentialCharacter
  rw [← Complex.exp_add]
  congr 1
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  push_cast
  ring
theorem ftInd_productSet {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ))
    (ξ : Fin n → ℝ) (η : Fin m → ℝ) :
    ftInd (productSet A B) (Fin.append ξ η) = ftInd A ξ * ftInd B η := by
  unfold ftInd
  let g : (Fin n → ℝ) × (Fin m → ℝ) → ℂ := fun p =>
    exponentialCharacter ξ p.1 * exponentialCharacter η p.2
  have key := (measurePreserving_splitEquiv n m).setIntegral_preimage_emb
    (splitEquiv n m).measurableEmbedding g (A ×ˢ B)
  rw [← productSet_eq_preimage] at key
  have hint : ∫ x in productSet A B, exponentialCharacter (Fin.append ξ η) x =
      ∫ x in productSet A B, g (splitEquiv n m x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [g]
    rw [exponentialCharacter_append, splitEquiv_apply]
  rw [hint, key, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_mul (fun a => exponentialCharacter ξ a) (fun b => exponentialCharacter η b)
section Affine
open Matrix
theorem exponentialCharacter_add_right (ξ x b : Fin d → ℝ) :
    exponentialCharacter ξ (x + b) = exponentialCharacter ξ x * exponentialCharacter ξ b := by
  unfold exponentialCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  push_cast
  ring
theorem exponentialCharacter_transpose (T : Matrix (Fin d) (Fin d) ℝ) (ξ y : Fin d → ℝ) :
    exponentialCharacter (Tᵀ *ᵥ ξ) y = exponentialCharacter ξ (T *ᵥ y) := by
  have h : (Tᵀ *ᵥ ξ) ⬝ᵥ y = ξ ⬝ᵥ (T *ᵥ y) := by
    rw [mulVec_transpose, dotProduct_mulVec]
  unfold exponentialCharacter
  change Complex.exp (2 * π * Complex.I * ((Tᵀ *ᵥ ξ) ⬝ᵥ y : ℝ)) =
    Complex.exp (2 * π * Complex.I * (ξ ⬝ᵥ (T *ᵥ y) : ℝ))
  rw [h]
theorem exponentialCharacter_neg_mul_self (ξ x : Fin d → ℝ) :
    exponentialCharacter (-ξ) x * exponentialCharacter ξ x = 1 := by
  rw [← exponentialCharacter_add, neg_add_cancel, exponentialCharacter_zero]
noncomputable def matLinEquiv (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det) :
    (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin d)) T hT
theorem matLinEquiv_apply (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det)
    (y : Fin d → ℝ) : matLinEquiv T hT y = T *ᵥ y := by
  simp [matLinEquiv, Matrix.toLin_eq_toLin']
noncomputable def affEquiv (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det)
    (b : Fin d → ℝ) : (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) :=
  ((matLinEquiv T hT).toContinuousLinearEquiv.toHomeomorph.trans
    (Homeomorph.addRight b)).toMeasurableEquiv
theorem affEquiv_apply (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det)
    (b y : Fin d → ℝ) : affEquiv T hT b y = T *ᵥ y + b := by
  simp [affEquiv, matLinEquiv_apply]
theorem measurePreserving_affEquiv (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det)
    (b : Fin d → ℝ) :
    MeasurePreserving (affEquiv T hT b) volume (ENNReal.ofReal |T.det|⁻¹ • volume) := by
  refine ⟨(affEquiv T hT b).measurable, ?_⟩
  have hdet : LinearMap.det ((matLinEquiv T hT : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))) = T.det := by
    rw [show ((matLinEquiv T hT : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))) =
      Matrix.toLin (Pi.basisFun ℝ (Fin d)) (Pi.basisFun ℝ (Fin d)) T from rfl,
      LinearMap.det_toLin]
  have hlin : Measure.map (matLinEquiv T hT) volume =
      ENNReal.ofReal |T.det|⁻¹ • (volume : Measure (Fin d → ℝ)) := by
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin d → ℝ)))
      (f := (matLinEquiv T hT : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))) (by rw [hdet]; exact hT.ne_zero)
    rw [hdet, abs_inv] at h
    exact h
  have hcomp : (affEquiv T hT b : (Fin d → ℝ) → (Fin d → ℝ)) =
      (fun x => x + b) ∘ (matLinEquiv T hT) := by
    funext y
    simp [affEquiv_apply, matLinEquiv_apply]
  have hmeas : Measurable (matLinEquiv T hT) :=
    (matLinEquiv T hT).toLinearMap.continuous_of_finiteDimensional.measurable
  rw [hcomp, ← Measure.map_map (measurable_add_const b) hmeas, hlin, Measure.map_smul,
    map_add_right_eq_self]
theorem volume_affEquiv_preimage (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det)
    (b : Fin d → ℝ) (Ω : Set (Fin d → ℝ)) :
    volume (affEquiv T hT b ⁻¹' Ω) = ENNReal.ofReal |T.det|⁻¹ * volume Ω := by
  rw [(measurePreserving_affEquiv T hT b).measure_preimage_equiv, Measure.smul_apply,
    smul_eq_mul]
theorem ftInd_affEquiv_preimage (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det)
    (b : Fin d → ℝ) (Ω : Set (Fin d → ℝ)) (ξ : Fin d → ℝ) :
    ftInd (affEquiv T hT b ⁻¹' Ω) (Tᵀ *ᵥ ξ) =
      ((|T.det|⁻¹ : ℝ) : ℂ) * (exponentialCharacter (-ξ) b * ftInd Ω ξ) := by
  unfold ftInd
  have hpt : ∀ y, exponentialCharacter (Tᵀ *ᵥ ξ) y =
      exponentialCharacter (-ξ) b * exponentialCharacter ξ (affEquiv T hT b y) := by
    intro y
    rw [affEquiv_apply, exponentialCharacter_add_right, exponentialCharacter_transpose]
    rw [mul_comm (exponentialCharacter ξ (T *ᵥ y)), ← mul_assoc,
      exponentialCharacter_neg_mul_self, one_mul]
  simp_rw [hpt]
  rw [integral_const_mul, (measurePreserving_affEquiv T hT b).setIntegral_preimage_emb
    (affEquiv T hT b).measurableEmbedding (exponentialCharacter ξ) Ω,
    Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _))]
  rw [Complex.real_smul]
  ring
theorem ftInd_affEquiv_preimage_eq_zero_iff (T : Matrix (Fin d) (Fin d) ℝ)
    (hT : IsUnit T.det) (b : Fin d → ℝ) (Ω : Set (Fin d → ℝ)) (ξ : Fin d → ℝ) :
    ftInd (affEquiv T hT b ⁻¹' Ω) (Tᵀ *ᵥ ξ) = 0 ↔ ftInd Ω ξ = 0 := by
  rw [ftInd_affEquiv_preimage]
  have h1 : ((|T.det|⁻¹ : ℝ) : ℂ) ≠ 0 := by
    simpa using hT.ne_zero
  have h2 : exponentialCharacter (-ξ) b ≠ 0 := by
    intro h
    have := norm_exponentialCharacter (-ξ) b
    rw [h, norm_zero] at this
    exact zero_ne_one this
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h h1
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h h2
    · exact h
  · intro h
    rw [h, mul_zero, mul_zero]
end Affine
end FCBridge
end
section
open MeasureTheory Complex Real Filter Topology Matrix
open scoped InnerProductSpace ComplexConjugate
namespace FCBridge
variable {d : ℕ}
noncomputable def echar {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (ξ : Fin d → ℝ) :
    Lp ℂ 2 (volume.restrict Ω) :=
  MemLp.toLp (exponentialCharacter ξ) (exponentialCharacter_memLp hΩ ξ)
theorem coeFn_echar {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (ξ : Fin d → ℝ) :
    ⇑(echar hΩ ξ) =ᵐ[volume.restrict Ω] exponentialCharacter ξ :=
  MemLp.coeFn_toLp _
theorem inner_echar {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (ξ₁ ξ₂ : Fin d → ℝ) :
    ⟪echar hΩ ξ₁, echar hΩ ξ₂⟫_ℂ = ftInd Ω (ξ₂ - ξ₁) :=
  inner_toLp_exponentialCharacter hΩ ξ₁ ξ₂
theorem norm_echar_sq {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (ξ : Fin d → ℝ) :
    ‖echar hΩ ξ‖ ^ 2 = volume.real Ω := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_echar, sub_self, ftInd_zero]
  simp
theorem exponentialCharacter_comm (ξ x : Fin d → ℝ) :
    exponentialCharacter ξ x = exponentialCharacter x ξ := by
  unfold exponentialCharacter
  change Complex.exp (2 * π * Complex.I * ((ξ ⬝ᵥ x : ℝ) : ℂ)) =
    Complex.exp (2 * π * Complex.I * ((x ⬝ᵥ ξ : ℝ) : ℂ))
  rw [dotProduct_comm]
theorem continuous_ftInd {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) :
    Continuous (ftInd Ω) := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩ
  unfold ftInd
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ))
    (fun ξ => (continuous_exponentialCharacter ξ).aestronglyMeasurable)
    (fun ξ => Eventually.of_forall fun x => (norm_exponentialCharacter ξ x).le)
    (integrable_const 1) (Eventually.of_forall fun x => ?_)
  simp_rw [exponentialCharacter_comm _ x]
  exact continuous_exponentialCharacter x
theorem continuous_inner_echar {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤)
    (G : Lp ℂ 2 (volume.restrict Ω)) : Continuous fun ξ => ⟪G, echar hΩ ξ⟫_ℂ := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩ
  have hrepr : ∀ ξ, ⟪G, echar hΩ ξ⟫_ℂ =
      ∫ x in Ω, conj (G x) * exponentialCharacter ξ x := by
    intro ξ
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_echar hΩ ξ] with x hx
    rw [hx, RCLike.inner_apply']
  simp_rw [hrepr]
  have hGint : Integrable (fun x => ‖G x‖) (volume.restrict Ω) :=
    ((Lp.memLp G).integrable (by norm_num)).norm
  refine continuous_of_dominated (bound := fun x => ‖G x‖) (fun ξ => ?_) (fun ξ => ?_) hGint ?_
  · exact (continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable G)).mul
      (continuous_exponentialCharacter ξ).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [norm_mul, norm_exponentialCharacter, mul_one, RCLike.norm_conj]
  · refine Eventually.of_forall fun x => ?_
    simp_rw [exponentialCharacter_comm _ x]
    exact continuous_const.mul (continuous_exponentialCharacter x)
def OrthogonalOn (Ω Λ : Set (Fin d → ℝ)) : Prop :=
  ∀ ξ₁ ∈ Λ, ∀ ξ₂ ∈ Λ, ξ₁ ≠ ξ₂ → ftInd Ω (ξ₂ - ξ₁) = 0
theorem OrthogonalOn.countable {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤)
    (hpos : 0 < volume Ω) (horth : OrthogonalOn Ω Λ) : Λ.Countable := by
  have hr : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  set ρ := Real.sqrt (volume.real Ω) / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hdist : ∀ ξ₁ ∈ Λ, ∀ ξ₂ ∈ Λ, ξ₁ ≠ ξ₂ → ρ + ρ ≤ dist (echar hΩ ξ₁) (echar hΩ ξ₂) := by
    intro ξ₁ h₁ ξ₂ h₂ hne
    rw [dist_eq_norm]
    have hsq : ‖echar hΩ ξ₁ - echar hΩ ξ₂‖ ^ 2 = 2 * volume.real Ω := by
      rw [norm_sub_sq (𝕜 := ℂ), inner_echar, horth ξ₁ h₁ ξ₂ h₂ hne, norm_echar_sq,
        norm_echar_sq]
      simp only [map_zero, mul_zero, sub_zero]
      ring
    have : Real.sqrt (volume.real Ω) ≤ ‖echar hΩ ξ₁ - echar hΩ ξ₂‖ := by
      rw [← Real.sqrt_sq (norm_nonneg _), hsq]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  refine Set.PairwiseDisjoint.countable_of_isOpen
    (s := fun ξ => Metric.ball (echar hΩ ξ) ρ) ?_ (fun _ _ => Metric.isOpen_ball)
    (fun ξ _ => ⟨_, Metric.mem_ball_self hρpos⟩)
  intro ξ₁ h₁ ξ₂ h₂ hne
  exact Metric.ball_disjoint_ball (hdist ξ₁ h₁ ξ₂ h₂ hne)
noncomputable def nchar {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (Λ : Set (Fin d → ℝ)) :
    Λ → Lp ℂ 2 (volume.restrict Ω) :=
  fun ξ => ((Real.sqrt (volume.real Ω))⁻¹ : ℂ) • echar hΩ ξ
private theorem sqrt_inv_sq {a : ℝ} (ha : 0 < a) :
    ((Real.sqrt a)⁻¹ : ℂ) * ((Real.sqrt a)⁻¹ : ℂ) * (a : ℂ) = 1 := by
  have h2 : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have h3 : ((Real.sqrt a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h2
  have h4 : ((a : ℝ) : ℂ) = ((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ha.le]
  rw [h4]
  field_simp
theorem orthonormal_nchar {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω)
    (horth : OrthogonalOn Ω Λ) : Orthonormal ℂ (nchar hΩ Λ) := by
  classical
  have hr : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  rw [orthonormal_iff_ite]
  intro i j
  simp only [nchar, inner_smul_left, inner_smul_right, inner_echar, Complex.conj_ofReal,
    map_inv₀]
  split_ifs with hij
  · subst hij
    rw [sub_self, ftInd_zero, ← mul_assoc]
    exact sqrt_inv_sq hr
  · have : (i : Fin d → ℝ) ≠ j := fun h => hij (Subtype.ext h)
    rw [horth i i.2 j j.2 this]
    simp
theorem norm_inner_nchar_sq {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω)
    (i : Λ) (ξ : Fin d → ℝ) :
    ‖⟪nchar hΩ Λ i, echar hΩ ξ⟫_ℂ‖ ^ 2 = ‖ftInd Ω (ξ - i)‖ ^ 2 / volume.real Ω := by
  have hr : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  simp only [nchar, inner_smul_left, inner_echar, norm_mul, RCLike.norm_conj]
  rw [mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr hr), inv_pow, Real.sq_sqrt hr.le]
  ring
theorem OrthogonalOn.summable_tsum_le {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤)
    (hpos : 0 < volume Ω) (horth : OrthogonalOn Ω Λ) (ξ : Fin d → ℝ) :
    Summable (fun i : Λ => ‖ftInd Ω (ξ - i)‖ ^ 2) ∧
      ∑' i : Λ, ‖ftInd Ω (ξ - i)‖ ^ 2 ≤ volume.real Ω ^ 2 := by
  have hr : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  have hv := orthonormal_nchar hΩ hpos horth
  have hs := hv.inner_products_summable (x := echar hΩ ξ)
  have hb := hv.tsum_inner_products_le (x := echar hΩ ξ)
  simp_rw [norm_inner_nchar_sq hΩ hpos] at hs hb
  rw [norm_echar_sq] at hb
  have hs' : Summable (fun i : Λ => ‖ftInd Ω (ξ - i)‖ ^ 2) := by
    simpa [div_mul_cancel₀ _ hr.ne'] using hs.mul_right (volume.real Ω)
  refine ⟨hs', ?_⟩
  rw [tsum_div_const] at hb
  rw [div_le_iff₀ hr] at hb
  nlinarith
theorem span_range_nchar {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω) :
    Submodule.span ℂ (Set.range (nchar hΩ Λ)) =
      Submodule.span ℂ (Set.range fun ξ : Λ => echar hΩ ξ) := by
  have hr : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  have hc : ((Real.sqrt (volume.real Ω))⁻¹ : ℂ) ≠ 0 := by
    simp [(Real.sqrt_pos.mpr hr).ne']
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    dsimp only
    have : echar hΩ i = ((Real.sqrt (volume.real Ω))⁻¹ : ℂ)⁻¹ • nchar hΩ Λ i := by
      simp only [nchar, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
noncomputable def hilbertBasisOfSpectralPair {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤)
    (h : spectralPair Ω Λ) : HilbertBasis Λ ℂ (Lp ℂ 2 (volume.restrict Ω)) :=
  HilbertBasis.mk (orthonormal_nchar hΩ h.2.1 (by
      obtain ⟨-, -, hΩ', horth, -⟩ := spectralPair_iff.mp h
      exact horth))
    (by
      obtain ⟨-, hpos, hΩ', -, hcomp⟩ := h
      rw [span_range_nchar hΩ hpos]
      exact hcomp.ge)
theorem coe_hilbertBasisOfSpectralPair {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤)
    (h : spectralPair Ω Λ) : ⇑(hilbertBasisOfSpectralPair hΩ h) = nchar hΩ Λ :=
  HilbertBasis.coe_mk _ _
theorem hasSum_norm_inner_sq {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤)
    (h : spectralPair Ω Λ) (G : Lp ℂ 2 (volume.restrict Ω)) :
    HasSum (fun i : Λ => ‖⟪nchar hΩ Λ i, G⟫_ℂ‖ ^ 2) (‖G‖ ^ 2) := by
  set b := hilbertBasisOfSpectralPair hΩ h
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have := lp.hasSum_norm hp (b.repr G)
  simp only [HilbertBasis.repr_apply_apply, LinearIsometryEquiv.norm_map] at this
  rw [coe_hilbertBasisOfSpectralPair] at this
  simpa [Real.rpow_two] using this
theorem hasSum_normSq_ftInd_of_spectralPair {Ω Λ : Set (Fin d → ℝ)} (h : spectralPair Ω Λ)
    (ξ : Fin d → ℝ) :
    HasSum (fun i : Λ => ‖ftInd Ω (ξ - i)‖ ^ 2) (volume.real Ω ^ 2) := by
  have hh := h
  obtain ⟨-, hpos, hΩ, -⟩ := hh
  have hr : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  have hs := hasSum_norm_inner_sq hΩ h (echar hΩ ξ)
  simp_rw [norm_inner_nchar_sq hΩ hpos] at hs
  rw [norm_echar_sq] at hs
  have := hs.mul_right (volume.real Ω)
  simp only [div_mul_cancel₀ _ hr.ne'] at this
  rw [sq]
  exact this
theorem spectralPair_of_tiling {Ω Λ : Set (Fin d → ℝ)} (hmeas : NullMeasurableSet Ω volume)
    (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω) (horth : OrthogonalOn Ω Λ)
    (htot : ∀ G : Lp ℂ 2 (volume.restrict Ω), (∀ ξ, ⟪echar hΩ ξ, G⟫_ℂ = 0) → G = 0)
    (htile : ∀ᵐ ξ ∂volume, ∑' i : Λ, ‖ftInd Ω (ξ - i)‖ ^ 2 = volume.real Ω ^ 2) :
    spectralPair Ω Λ := by
  have hr : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  rw [spectralPair_iff]
  refine ⟨hmeas, hpos, hΩ, horth, fun G hG => ?_⟩
  have hG' : ∀ i : Λ, ⟪nchar hΩ Λ i, G⟫_ℂ = 0 := by
    intro i
    simp only [nchar, inner_smul_left]
    rw [show ⟪echar hΩ (i : Fin d → ℝ), G⟫_ℂ = 0 from hG i i.2, mul_zero]
  apply htot
  have hφae : ∀ᵐ ξ ∂volume, ⟪G, echar hΩ ξ⟫_ℂ = 0 := by
    filter_upwards [htile] with ξ hξ
    by_cases hG0 : G = 0
    · simp [hG0]
    have hGn : ‖G‖ ≠ 0 := norm_ne_zero_iff.mpr hG0
    let w : Unit ⊕ Λ → Lp ℂ 2 (volume.restrict Ω) :=
      Sum.elim (fun _ => ((‖G‖⁻¹ : ℝ) : ℂ) • G) (nchar hΩ Λ)
    have hv := orthonormal_nchar hΩ hpos horth
    have hw : Orthonormal ℂ w := by
      refine ⟨?_, ?_⟩
      · rintro (u | i)
        · simp only [w, Sum.elim_inl, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_inv, abs_norm]
          exact inv_mul_cancel₀ hGn
        · exact hv.1 i
      · rintro (u | i) (u' | j) hne
        · exact absurd (by cases u; cases u'; rfl) hne
        · simp only [w, Sum.elim_inl, Sum.elim_inr, inner_smul_left]
          rw [← inner_conj_symm, hG' j, map_zero, mul_zero]
        · simp only [w, Sum.elim_inl, Sum.elim_inr, inner_smul_right, hG' i, mul_zero]
        · exact hv.2 (fun h => hne (congrArg Sum.inr h))
    have hsum := hw.inner_products_summable (x := echar hΩ ξ)
    have hbes := hw.tsum_inner_products_le (x := echar hΩ ξ)
    rw [Summable.tsum_sum (hsum.comp_injective Sum.inl_injective)
      (hsum.comp_injective Sum.inr_injective)] at hbes
    simp only [w, Sum.elim_inl, Sum.elim_inr, tsum_const, Nat.card_unique, one_smul] at hbes
    simp_rw [norm_inner_nchar_sq hΩ hpos] at hbes
    rw [tsum_div_const, hξ, norm_echar_sq] at hbes
    have hle : ‖⟪((‖G‖⁻¹ : ℝ) : ℂ) • G, echar hΩ ξ⟫_ℂ‖ ^ 2 ≤ 0 := by
      have : volume.real Ω ^ 2 / volume.real Ω = volume.real Ω := by
        field_simp
      linarith
    have h0 : ⟪((‖G‖⁻¹ : ℝ) : ℂ) • G, echar hΩ ξ⟫_ℂ = 0 := by
      have := le_antisymm hle (sq_nonneg _)
      simpa using this
    rw [inner_smul_left] at h0
    simpa [hGn] using h0
  have hφ0 := (Continuous.ae_eq_iff_eq volume (continuous_inner_echar hΩ G)
    continuous_const).mp hφae
  intro ξ
  have := congrFun hφ0 ξ
  rw [← inner_conj_symm]
  simp [this]
theorem exists_freq_of_strongDual (L : StrongDual ℝ (Fin d → ℝ)) :
    ∃ ξ : Fin d → ℝ, ∀ x, Complex.exp (L x * Complex.I) = exponentialCharacter ξ x := by
  classical
  set c : Fin d → ℝ := fun i => L (fun j => if i = j then 1 else 0) with hc
  refine ⟨fun i => c i / (2 * π), fun x => ?_⟩
  have hL : L x = ∑ i, x i * c i := by
    conv_lhs => rw [pi_eq_sum_univ x]
    simp [map_sum, map_smul, hc, smul_eq_mul]
  unfold exponentialCharacter
  rw [hL]
  congr 1
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
private theorem integrable_mul_char {μ : Measure (Fin d → ℝ)} {g : (Fin d → ℝ) → ℂ}
    (hg : Integrable g μ) (ξ : Fin d → ℝ) :
    Integrable (fun x => g x * exponentialCharacter ξ x) μ :=
  hg.mul_bdd (continuous_exponentialCharacter ξ).aestronglyMeasurable
    (Eventually.of_forall fun x => (norm_exponentialCharacter ξ x).le)
theorem ae_eq_zero_of_integral_ofReal_mul_char {μ : Measure (Fin d → ℝ)} [IsFiniteMeasure μ]
    {w : (Fin d → ℝ) → ℝ} (hw : Integrable w μ)
    (h : ∀ ξ, ∫ x, (w x : ℂ) * exponentialCharacter ξ x ∂μ = 0) : w =ᵐ[μ] 0 := by
  set fp : (Fin d → ℝ) → ENNReal := fun x => ENNReal.ofReal (w x) with hfp_def
  set fm : (Fin d → ℝ) → ENNReal := fun x => ENNReal.ofReal (-w x) with hfm_def
  have hfp : AEMeasurable fp μ := hw.aemeasurable.ennreal_ofReal
  have hfm : AEMeasurable fm μ := hw.neg.aemeasurable.ennreal_ofReal
  have hfpi : ∫⁻ x, fp x ∂μ ≠ ⊤ := hw.lintegral_lt_top.ne
  have hfmi : ∫⁻ x, fm x ∂μ ≠ ⊤ := hw.neg.lintegral_lt_top.ne
  have : IsFiniteMeasure (μ.withDensity fp) := isFiniteMeasure_withDensity hfpi
  have : IsFiniteMeasure (μ.withDensity fm) := isFiniteMeasure_withDensity hfmi
  have hpart : ∀ (v : (Fin d → ℝ) → ℝ), Integrable v μ → ∀ ξ,
      ∫ x, exponentialCharacter ξ x ∂μ.withDensity (fun x => ENNReal.ofReal (v x)) =
        ∫ x, ((max (v x) 0 : ℝ) : ℂ) * exponentialCharacter ξ x ∂μ := by
    intro v hv ξ
    rw [integral_withDensity_eq_integral_toReal_smul₀ hv.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofReal', Complex.real_smul]
  have hchar : charFunDual (μ.withDensity fp) = charFunDual (μ.withDensity fm) := by
    funext L
    obtain ⟨ξ, hξ⟩ := exists_freq_of_strongDual L
    rw [charFunDual_apply, charFunDual_apply]
    simp_rw [hξ]
    have hwn : Integrable (fun x => -w x) μ := hw.neg
    rw [hpart w hw ξ, hpart (fun x => -w x) hwn ξ, ← sub_eq_zero]
    calc _ = ∫ x, (((max (w x) 0 : ℝ) : ℂ) * exponentialCharacter ξ x -
            ((max (-w x) 0 : ℝ) : ℂ) * exponentialCharacter ξ x) ∂μ :=
          (integral_sub (integrable_mul_char hw.pos_part.ofReal ξ)
            (integrable_mul_char hwn.pos_part.ofReal ξ)).symm
      _ = ∫ x, (w x : ℂ) * exponentialCharacter ξ x ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          have hm : max (w x) 0 - max (-w x) 0 = w x := by
            rcases le_total 0 (w x) with h0 | h0
            · rw [max_eq_left h0, max_eq_right (by linarith)]
              ring
            · rw [max_eq_right h0, max_eq_left (by linarith)]
              ring
          simp only
          rw [← sub_mul, ← Complex.ofReal_sub, hm]
      _ = 0 := h ξ
  have hae := (withDensity_eq_iff hfp hfm hfpi).mp (Measure.ext_of_charFunDual hchar)
  filter_upwards [hae] with x hx
  simp only [hfp_def, hfm_def] at hx
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : ENNReal.ofReal (w x) = 0 := ENNReal.ofReal_of_nonpos hlt.le
    have h2 : 0 < ENNReal.ofReal (-w x) := ENNReal.ofReal_pos.mpr (by simpa using hlt)
    rw [hx] at h1
    exact h2.ne' h1
  · have h1 : 0 < ENNReal.ofReal (w x) := ENNReal.ofReal_pos.mpr hgt
    have h2 : ENNReal.ofReal (-w x) = 0 := ENNReal.ofReal_of_nonpos (by simp at hgt ⊢; linarith)
    rw [hx] at h1
    exact h1.ne' h2
theorem ae_eq_zero_of_integral_mul_char {μ : Measure (Fin d → ℝ)} [IsFiniteMeasure μ]
    {g : (Fin d → ℝ) → ℂ} (hg : Integrable g μ)
    (h : ∀ ξ, ∫ x, g x * exponentialCharacter ξ x ∂μ = 0) : g =ᵐ[μ] 0 := by
  have hconj : ∀ ξ, conj (∫ x, g x * exponentialCharacter (-ξ) x ∂μ) =
      ∫ x, conj (g x) * exponentialCharacter ξ x ∂μ := by
    intro ξ
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [map_mul, conj_exponentialCharacter, neg_neg]
  have hgc : Integrable (fun x => conj (g x)) μ :=
    hg.mono (continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable)
      (Eventually.of_forall fun x => by rw [RCLike.norm_conj])
  have hre : (fun x => (g x).re) =ᵐ[μ] 0 := by
    refine ae_eq_zero_of_integral_ofReal_mul_char hg.re fun ξ => ?_
    have hsplit : ∫ x, ((g x).re : ℂ) * exponentialCharacter ξ x ∂μ =
        (∫ x, g x * exponentialCharacter ξ x ∂μ +
          ∫ x, conj (g x) * exponentialCharacter ξ x ∂μ) / 2 := by
      rw [← integral_add (integrable_mul_char hg ξ) (integrable_mul_char hgc ξ),
        ← integral_div]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [Complex.re_eq_add_conj]
      ring
    rw [hsplit, h ξ, ← hconj, h (-ξ), map_zero]
    simp
  have him : (fun x => (g x).im) =ᵐ[μ] 0 := by
    refine ae_eq_zero_of_integral_ofReal_mul_char hg.im fun ξ => ?_
    have hsplit : ∫ x, ((g x).im : ℂ) * exponentialCharacter ξ x ∂μ =
        (∫ x, g x * exponentialCharacter ξ x ∂μ -
          ∫ x, conj (g x) * exponentialCharacter ξ x ∂μ) / (2 * Complex.I) := by
      rw [← integral_sub (integrable_mul_char hg ξ) (integrable_mul_char hgc ξ),
        ← integral_div]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [Complex.im_eq_sub_conj]
      ring
    rw [hsplit, h ξ, ← hconj, h (-ξ), map_zero]
    simp
  filter_upwards [hre, him] with x h1 h2
  apply Complex.ext
  · simpa using h1
  · simpa using h2
theorem echar_total {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤)
    (G : Lp ℂ 2 (volume.restrict Ω)) (h : ∀ ξ, ⟪echar hΩ ξ, G⟫_ℂ = 0) : G = 0 := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩ
  have hGint : Integrable (⇑G) (volume.restrict Ω) := (Lp.memLp G).integrable (by norm_num)
  have hrepr : ∀ ξ, ⟪echar hΩ ξ, G⟫_ℂ =
      ∫ x, G x * exponentialCharacter (-ξ) x ∂(volume.restrict Ω) := by
    intro ξ
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_echar hΩ ξ] with x hx
    rw [hx, RCLike.inner_apply', conj_exponentialCharacter, mul_comm]
  have hae := ae_eq_zero_of_integral_mul_char hGint fun ξ => by
    rw [← neg_neg ξ, ← hrepr (-ξ), h]
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hae
theorem spectralPair_of_orthogonal_of_tiling {Ω Λ : Set (Fin d → ℝ)}
    (hmeas : NullMeasurableSet Ω volume) (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω)
    (horth : OrthogonalOn Ω Λ)
    (htile : ∀ᵐ ξ ∂volume, ∑' i : Λ, ‖ftInd Ω (ξ - i)‖ ^ 2 = volume.real Ω ^ 2) :
    spectralPair Ω Λ :=
  spectralPair_of_tiling hmeas hΩ hpos horth (echar_total hΩ) htile
end FCBridge
end
section
open MeasureTheory Complex Real Filter Topology Matrix
open scoped InnerProductSpace ComplexConjugate
namespace FCBridge
variable {d : ℕ}
def unitCube (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1
def intLattice (d : ℕ) : Set (Fin d → ℝ) := Set.range fun k : Fin d → ℤ => fun i => (k i : ℝ)
theorem exponentialCharacter_eq_prod (ξ x : Fin d → ℝ) :
    exponentialCharacter ξ x = ∏ i, Complex.exp (2 * π * Complex.I * ((ξ i : ℂ) * (x i : ℂ))) := by
  unfold exponentialCharacter
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
theorem integral_Ico_exp_int (k : ℤ) (hk : k ≠ 0) :
    ∫ t in Set.Ico (0 : ℝ) 1, Complex.exp (2 * π * Complex.I * (((k : ℝ) : ℂ) * (t : ℂ))) = 0 := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hc : (2 * π * Complex.I * (k : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero, hk, Complex.I_ne_zero]
  have hpt : ∀ t : ℝ, Complex.exp (2 * π * Complex.I * (((k : ℝ) : ℂ) * (t : ℂ))) =
      Complex.exp ((2 * π * Complex.I * (k : ℂ)) * t) := by
    intro t
    push_cast
    ring_nf
  simp_rw [hpt]
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp ((2 * π * Complex.I * (k : ℂ)) * ((1 : ℝ) : ℂ)) = 1 := by
    rw [Complex.ofReal_one, mul_one,
      show 2 * (π : ℂ) * Complex.I * k = k * (2 * π * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I k
  rw [h1]
  simp
theorem ftInd_unitCube_int {k : Fin d → ℤ} (hk : k ≠ 0) :
    ftInd (unitCube d) (fun i => (k i : ℝ)) = 0 := by
  unfold ftInd unitCube
  rw [volume_pi, Measure.restrict_pi_pi]
  simp_rw [exponentialCharacter_eq_prod]
  rw [integral_fintype_prod_eq_prod
    (fun i (t : ℝ) => Complex.exp (2 * π * Complex.I * (((k i : ℝ) : ℂ) * (t : ℂ))))]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
  exact Finset.prod_eq_zero (Finset.mem_univ i) (integral_Ico_exp_int (k i) hi)
theorem orthogonalOn_unitCube : OrthogonalOn (unitCube d) (intLattice d) := by
  rintro _ ⟨k₁, rfl⟩ _ ⟨k₂, rfl⟩ hne
  have hk : k₂ - k₁ ≠ 0 := by
    intro h
    apply hne
    funext i
    have := congrFun h i
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
    simp [this]
  have := ftInd_unitCube_int hk
  convert this using 2
  funext i
  simp
theorem volume_unitCube : volume (unitCube d) = 1 := by
  rw [unitCube, volume_pi_pi]
  simp [Real.volume_Ico]
theorem OrthogonalOn.affEquiv_preimage {Ω Λ : Set (Fin d → ℝ)} (h : OrthogonalOn Ω Λ)
    (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det) (b : Fin d → ℝ) :
    OrthogonalOn (affEquiv T hT b ⁻¹' Ω) ((fun ξ => Tᵀ *ᵥ ξ) '' Λ) := by
  rintro _ ⟨ξ₁, h₁, rfl⟩ _ ⟨ξ₂, h₂, rfl⟩ hne
  have hne' : ξ₁ ≠ ξ₂ := fun h => hne (by rw [h])
  rw [← mulVec_sub, ftInd_affEquiv_preimage_eq_zero_iff]
  exact h ξ₁ h₁ ξ₂ h₂ hne'
theorem OrthogonalOn.tsum_normSq_ftInd_le_of_subset {Ω Q Γ : Set (Fin d → ℝ)}
    (hΩm : MeasurableSet Ω) (hΩQ : Ω ⊆ Q) (hQ : volume Q ≠ ⊤) (hQpos : 0 < volume Q)
    (horth : OrthogonalOn Q Γ) (x : Fin d → ℝ) :
    Summable (fun γ : Γ => ‖ftInd Ω (x - γ)‖ ^ 2) ∧
      ∑' γ : Γ, ‖ftInd Ω (x - γ)‖ ^ 2 ≤ volume.real Q * volume.real Ω := by
  have hr : 0 < volume.real Q := ENNReal.toReal_pos hQpos.ne' hQ
  have : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.mpr hQ
  have hv := orthonormal_nchar hQ hQpos horth
  have hmem : MemLp (Ω.indicator (exponentialCharacter x)) 2 (volume.restrict Q) := by
    refine MemLp.of_bound
      ((continuous_exponentialCharacter x).aestronglyMeasurable.indicator hΩm) 1
      (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ Ω
    · simp [Set.indicator_of_mem hy, norm_exponentialCharacter]
    · simp [Set.indicator_of_notMem hy]
  set v := hmem.toLp (Ω.indicator (exponentialCharacter x)) with hvdef
  have hpt : ∀ γ : Fin d → ℝ, ∀ y, conj (exponentialCharacter γ y) *
      Ω.indicator (exponentialCharacter x) y = Ω.indicator (exponentialCharacter (x - γ)) y := by
    intro γ y
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, conj_mul_exponentialCharacter]
    · simp [Set.indicator_of_notMem hy]
  have hinner0 : ∀ γ : Fin d → ℝ, ⟪echar hQ γ, v⟫_ℂ = ftInd Ω (x - γ) := by
    intro γ
    rw [MeasureTheory.L2.inner_def]
    calc _ = ∫ y in Q, Ω.indicator (exponentialCharacter (x - γ)) y := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_echar hQ γ, MemLp.coeFn_toLp hmem] with y h1 h2
          rw [h1, h2, RCLike.inner_apply', hpt]
      _ = ∫ y in Q ∩ Ω, exponentialCharacter (x - γ) y := setIntegral_indicator hΩm
      _ = ftInd Ω (x - γ) := by rw [Set.inter_eq_right.mpr hΩQ]; rfl
  have hnorm : ‖v‖ ^ 2 = volume.real Ω := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def]
    have : ∫ y, ⟪v y, v y⟫_ℂ ∂(volume.restrict Q) = ∫ y in Q, Ω.indicator (fun _ => (1 : ℂ)) y := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hmem] with y h
      rw [h, RCLike.inner_apply']
      by_cases hy : y ∈ Ω
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, conj_mul_exponentialCharacter,
          sub_self, exponentialCharacter_zero]
      · simp [Set.indicator_of_notMem hy]
    rw [this, setIntegral_indicator hΩm, Set.inter_eq_right.mpr hΩQ]
    simp [measureReal_def]
  have hterm : ∀ γ : Γ, ‖⟪nchar hQ Γ γ, v⟫_ℂ‖ ^ 2 = ‖ftInd Ω (x - γ)‖ ^ 2 / volume.real Q := by
    intro γ
    simp only [nchar, inner_smul_left, hinner0, norm_mul, RCLike.norm_conj]
    rw [mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.mpr hr), inv_pow, Real.sq_sqrt hr.le]
    ring
  have hs := hv.inner_products_summable (x := v)
  have hb := hv.tsum_inner_products_le (x := v)
  simp_rw [hterm] at hs hb
  rw [hnorm, tsum_div_const, div_le_iff₀ hr] at hb
  refine ⟨?_, by linarith⟩
  simpa [div_mul_cancel₀ _ hr.ne'] using hs.mul_right (volume.real Q)
theorem lintegral_normSq_ftInd_le {Ω : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) :
    ∫⁻ ξ, ENNReal.ofReal (‖ftInd Ω ξ‖ ^ 2) ≤ volume Ω := by
  classical
  have hΩfin : volume Ω ≠ ⊤ := hΩb.measure_lt_top.ne
  obtain ⟨r, hr⟩ := hΩb.subset_closedBall 0
  set R : ℝ := |r| + 1 with hR
  have hRpos : 0 < R := by positivity
  set c : ℝ := (2 * R)⁻¹ with hc
  have hcpos : 0 < c := by positivity
  have hcR : c * R = 1 / 2 := by rw [hc]; field_simp
  set T : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal fun _ => c with hTdef
  have hTdet : T.det = c ^ d := by
    simp [hTdef, Matrix.det_diagonal, Finset.prod_const]
  have hT : IsUnit T.det := by rw [hTdet]; exact (pow_pos hcpos d).ne'.isUnit
  have hTt : Tᵀ = T := Matrix.diagonal_transpose _
  have hTmul : ∀ v, T *ᵥ v = c • v := by
    intro v; ext i; simp [hTdef, Matrix.mulVec_diagonal]
  set b : Fin d → ℝ := fun _ => 1 / 2 with hb
  set Q := affEquiv T hT b ⁻¹' unitCube d with hQdef
  have hΩQ : Ω ⊆ Q := by
    intro y hy
    have hyb : ‖y‖ ≤ r := mem_closedBall_zero_iff.mp (hr hy)
    simp only [hQdef, Set.mem_preimage, affEquiv_apply, unitCube, Set.mem_univ_pi,
      Set.mem_Ico, hTmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb]
    intro i
    have hyi : |y i| ≤ r := by
      have := norm_le_pi_norm y i
      rw [Real.norm_eq_abs] at this
      linarith
    have hlt : |y i| < R := by linarith [le_abs_self r]
    rw [abs_lt] at hlt
    constructor
    · nlinarith [mul_lt_mul_of_pos_left hlt.1 hcpos]
    · nlinarith [mul_lt_mul_of_pos_left hlt.2 hcpos]
  have hQvol : volume Q = ENNReal.ofReal (c ^ d)⁻¹ := by
    rw [hQdef, volume_affEquiv_preimage, volume_unitCube, mul_one, hTdet,
      abs_of_pos (pow_pos hcpos d)]
  have hQfin : volume Q ≠ ⊤ := by rw [hQvol]; exact ENNReal.ofReal_ne_top
  have hQpos : 0 < volume Q := by
    rw [hQvol]; exact ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hcpos d))
  have hQreal : volume.real Q = (c ^ d)⁻¹ := by
    rw [measureReal_def, hQvol, ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_pos hcpos d).le)]
  set bs := (Pi.basisFun ℝ (Fin d)).isUnitSMul (w := fun _ => c) (fun _ => hcpos.ne'.isUnit)
    with hbs
  have hbs_apply : ∀ i, bs i = c • Pi.single i (1 : ℝ) := by
    intro i; simp [hbs, Module.Basis.isUnitSMul_apply]
  set L := Submodule.span ℤ (Set.range bs) with hLdef
  have hL : ∀ v ∈ L, ∃ k : Fin d → ℤ, v = T *ᵥ (fun i => (k i : ℝ)) := by
    intro v hv
    obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
    refine ⟨k, ?_⟩
    rw [← hk, hTmul]
    ext j
    simp [hbs_apply, Finset.sum_apply, Pi.single_apply, mul_comm]
  have horthQ : OrthogonalOn Q (L : Set (Fin d → ℝ)) := by
    have ho := (orthogonalOn_unitCube (d := d)).affEquiv_preimage T hT b
    intro ξ₁ h₁ ξ₂ h₂ hne
    obtain ⟨k₁, rfl⟩ := hL ξ₁ h₁
    obtain ⟨k₂, rfl⟩ := hL ξ₂ h₂
    exact ho _ ⟨_, ⟨k₁, rfl⟩, by rw [hTt]⟩ _ ⟨_, ⟨k₂, rfl⟩, by rw [hTt]⟩ hne
  have hfd := ZSpan.isAddFundamentalDomain bs volume
  have : MeasurableVAdd L (Fin d → ℝ) :=
    (inferInstance : MeasurableVAdd L.toAddSubgroup (Fin d → ℝ))
  have : VAddInvariantMeasure L (Fin d → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (Fin d → ℝ) volume)
  set F : (Fin d → ℝ) → ENNReal := fun ξ => ENNReal.ofReal (‖ftInd Ω ξ‖ ^ 2) with hFdef
  have hFmeas : Measurable F :=
    (((continuous_ftInd hΩfin).norm.pow 2).measurable).ennreal_ofReal
  have hbound : ∀ x, ∑' g : L, F (g +ᵥ x) ≤
      ENNReal.ofReal (volume.real Q * volume.real Ω) := by
    intro x
    obtain ⟨hsum, hle⟩ := horthQ.tsum_normSq_ftInd_le_of_subset hΩm hΩQ hQfin hQpos (-x)
    have heq : ∀ g : L, F (g +ᵥ x) = ENNReal.ofReal (‖ftInd Ω (-x - g)‖ ^ 2) := by
      intro g
      simp only [hFdef, Submodule.vadd_def, vadd_eq_add]
      rw [show -x - (g : Fin d → ℝ) = -((g : Fin d → ℝ) + x) by abel, ftInd_neg,
        RCLike.norm_conj]
    calc ∑' g : L, F (g +ᵥ x) = ∑' g : L, ENNReal.ofReal (‖ftInd Ω (-x - g)‖ ^ 2) :=
          tsum_congr heq
      _ = ENNReal.ofReal (∑' γ : (L : Set (Fin d → ℝ)), ‖ftInd Ω (-x - γ)‖ ^ 2) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsum).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hle
  have hmeasg : ∀ g : L, AEMeasurable (fun x => F (g +ᵥ x))
      (volume.restrict (ZSpan.fundamentalDomain bs)) := by
    intro g
    exact (hFmeas.comp (measurable_const_add (g : Fin d → ℝ))).aemeasurable
  have hdetbs : (Matrix.of bs).det = c ^ d := by
    have : Matrix.of bs = Matrix.diagonal fun _ => c := by
      ext i j
      simp [hbs_apply, Matrix.diagonal_apply, Pi.single_apply, eq_comm]
    rw [this]
    simp [Matrix.det_diagonal, Finset.prod_const]
  calc ∫⁻ ξ, ENNReal.ofReal (‖ftInd Ω ξ‖ ^ 2)
      = ∑' g : L, ∫⁻ x in ZSpan.fundamentalDomain bs, F (g +ᵥ x) :=
        hfd.lintegral_eq_tsum'' F
    _ = ∫⁻ x in ZSpan.fundamentalDomain bs, ∑' g : L, F (g +ᵥ x) :=
        (lintegral_tsum hmeasg).symm
    _ ≤ ∫⁻ _ in ZSpan.fundamentalDomain bs, ENNReal.ofReal (volume.real Q * volume.real Ω) :=
        lintegral_mono hbound
    _ = volume (ZSpan.fundamentalDomain bs) *
          ENNReal.ofReal (volume.real Q * volume.real Ω) := by
        rw [setLIntegral_const, mul_comm]
    _ = volume Ω := by
        rw [ZSpan.volume_fundamentalDomain, hdetbs, abs_of_pos (pow_pos hcpos d), hQreal,
          ← ENNReal.ofReal_mul (pow_pos hcpos d).le, ← mul_assoc,
          mul_inv_cancel₀ (pow_pos hcpos d).ne', one_mul, measureReal_def,
          ENNReal.ofReal_toReal hΩfin]
end FCBridge
end
section
open MeasureTheory Filter Complex Real
open scoped ComplexConjugate
namespace FCBridge
variable {d : ℕ}
theorem lintegral_eq_lintegral_mul_tsum {Λ : Set (Fin d → ℝ)} (hΛ : Λ.Countable)
    {f g : (Fin d → ℝ) → ENNReal} (hf : Measurable f) (hg : Measurable g)
    (hF : ∀ᵐ x ∂volume, ∑' l : Λ, f (x - l) = 1) (x : Fin d → ℝ) :
    ∫⁻ y, g y = ∫⁻ w, f (x - w) * ∑' l : Λ, g (w - l) := by
  have : Countable Λ := hΛ.to_subtype
  calc ∫⁻ y, g y = ∫⁻ y, g (x - y) := (lintegral_sub_left_eq_self g x).symm
    _ = ∫⁻ y, g (x - y) * ∑' l : Λ, f (y - l) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hF] with y hy
        rw [hy, mul_one]
    _ = ∑' l : Λ, ∫⁻ y, g (x - y) * f (y - l) := by
        have hm : ∀ l : Λ, Measurable fun y => g (x - y) * f (y - l) := fun l =>
          (hg.comp (measurable_const_sub x)).mul (hf.comp (measurable_sub_const _))
        rw [← lintegral_tsum fun l => (hm l).aemeasurable]
        refine lintegral_congr fun y => ?_
        rw [ENNReal.tsum_mul_left]
    _ = ∑' l : Λ, ∫⁻ w, f (x - w) * g (w - l) := by
        refine tsum_congr fun l => ?_
        rw [← lintegral_sub_left_eq_self (fun y => g (x - y) * f (y - l)) (x + l)]
        refine lintegral_congr fun w => ?_
        rw [show x - (x + (l : Fin d → ℝ) - w) = w - l by abel,
          show x + (l : Fin d → ℝ) - w - l = x - w by abel, mul_comm]
    _ = ∫⁻ w, f (x - w) * ∑' l : Λ, g (w - l) := by
        have hm : ∀ l : Λ, Measurable fun w => f (x - w) * g (w - l) := fun l =>
          (hf.comp (measurable_const_sub x)).mul (hg.comp (measurable_sub_const _))
        rw [← lintegral_tsum fun l => (hm l).aemeasurable]
        refine lintegral_congr fun w => ?_
        rw [ENNReal.tsum_mul_left]
theorem lintegral_le_of_tiling_of_packing {Λ : Set (Fin d → ℝ)} (hΛ : Λ.Countable)
    {f g : (Fin d → ℝ) → ENNReal} (hf : Measurable f) (hg : Measurable g)
    (hF : ∀ᵐ x ∂volume, ∑' l : Λ, f (x - l) = 1)
    (hG : ∀ᵐ x ∂volume, ∑' l : Λ, g (x - l) ≤ 1) :
    ∫⁻ y, g y ≤ ∫⁻ y, f y := by
  rw [lintegral_eq_lintegral_mul_tsum hΛ hf hg hF 0]
  calc ∫⁻ w, f (0 - w) * ∑' l : Λ, g (w - l) ≤ ∫⁻ w, f (0 - w) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hG] with w hw
        calc f (0 - w) * ∑' l : Λ, g (w - l) ≤ f (0 - w) * 1 := by gcongr
          _ = f (0 - w) := mul_one _
    _ = ∫⁻ y, f y := lintegral_sub_left_eq_self f 0
theorem lintegral_ne_zero_of_tiling {Λ : Set (Fin d → ℝ)} (hΛ : Λ.Countable)
    {f : (Fin d → ℝ) → ENNReal} (hf : Measurable f)
    (hF : ∀ᵐ x ∂volume, ∑' l : Λ, f (x - l) = 1) : ∫⁻ y, f y ≠ 0 := by
  have : Countable Λ := hΛ.to_subtype
  intro h0
  have hf0 : f =ᵐ[volume] 0 := (lintegral_eq_zero_iff hf).mp h0
  have hshift : ∀ l : Λ, ∀ᵐ x ∂volume, f (x - l) = 0 := fun l =>
    (measurePreserving_sub_right volume (l : Fin d → ℝ)).quasiMeasurePreserving.ae hf0
  have hall : ∀ᵐ x ∂volume, ∀ l : Λ, f (x - l) = 0 := ae_all_iff.mpr hshift
  obtain ⟨x, hx1, hx0⟩ := (hF.and hall).exists
  rw [tsum_congr hx0, tsum_zero] at hx1
  exact zero_ne_one hx1
theorem tiling_of_packing_of_lintegral_le {Λ : Set (Fin d → ℝ)} (hΛ : Λ.Countable)
    {f g : (Fin d → ℝ) → ENNReal} (hf : Measurable f) (hg : Measurable g)
    (hftop : ∀ x, f x ≠ ⊤)
    (hF : ∀ᵐ x ∂volume, ∑' l : Λ, f (x - l) = 1)
    (hG : ∀ᵐ x ∂volume, ∑' l : Λ, g (x - l) ≤ 1)
    (hfin : ∫⁻ y, f y ≠ ⊤) (hle : ∫⁻ y, f y ≤ ∫⁻ y, g y) :
    ∀ᵐ x ∂volume, ∑' l : Λ, g (x - l) = 1 := by
  have : Countable Λ := hΛ.to_subtype
  set G : (Fin d → ℝ) → ENNReal := fun w => ∑' l : Λ, g (w - l) with hGdef
  have hGmeas : Measurable G :=
    Measurable.tsum fun l => hg.comp (measurable_sub_const _)
  have hgf : ∫⁻ y, g y = ∫⁻ y, f y :=
    le_antisymm (lintegral_le_of_tiling_of_packing hΛ hf hg hF hG) hle
  have hkey : ∀ x, ∀ᵐ w ∂volume, f (x - w) * G w = f (x - w) := by
    intro x
    have hle' : (fun w => f (x - w) * G w) ≤ᵐ[volume] fun w => f (x - w) := by
      filter_upwards [hG] with w hw
      calc f (x - w) * G w ≤ f (x - w) * 1 := by gcongr
        _ = f (x - w) := mul_one _
    have hint1 : ∫⁻ w, f (x - w) = ∫⁻ y, f y := lintegral_sub_left_eq_self f x
    have hint2 : ∫⁻ w, f (x - w) * G w = ∫⁻ y, g y :=
      (lintegral_eq_lintegral_mul_tsum hΛ hf hg hF x).symm
    exact ae_eq_of_ae_le_of_lintegral_le hle' (by rw [hint2, hgf]; exact hfin)
      (hf.comp (measurable_const_sub x)).aemeasurable (by rw [hint1, hint2, hgf])
  set E : Set (Fin d → ℝ) := {w | G w < 1} with hEdef
  have hEm : MeasurableSet E := measurableSet_lt hGmeas measurable_const
  have hzero : ∀ x, ∫⁻ w, f (x - w) * E.indicator 1 w = 0 := by
    intro x
    have hm : Measurable fun w => f (x - w) * E.indicator 1 w :=
      (hf.comp (measurable_const_sub x)).mul (measurable_one.indicator hEm)
    refine (lintegral_eq_zero_iff hm).mpr ?_
    filter_upwards [hkey x] with w hw
    show f (x - w) * E.indicator 1 w = 0
    by_cases hwE : w ∈ E
    · rw [Set.indicator_of_mem hwE, Pi.one_apply, mul_one]
      by_contra hne
      have hlt : G w * f (x - w) < 1 * f (x - w) := ENNReal.mul_lt_mul_left hne (hftop _) hwE
      rw [one_mul, mul_comm, hw] at hlt
      exact lt_irrefl _ hlt
    · simp [Set.indicator_of_notMem hwE]
  have hmeas2 : AEMeasurable (Function.uncurry fun x w => f (x - w) * E.indicator 1 w)
      (volume.prod volume) :=
    ((hf.comp measurable_sub).mul ((measurable_one.indicator hEm).comp measurable_snd)).aemeasurable
  have htotal : volume E * ∫⁻ y, f y = 0 := by
    have hswap := lintegral_lintegral_swap hmeas2
    simp only [hzero, lintegral_zero] at hswap
    rw [eq_comm] at hswap
    calc volume E * ∫⁻ y, f y = ∫⁻ w, E.indicator 1 w * ∫⁻ y, f y := by
          have hm : Measurable fun w => E.indicator (1 : (Fin d → ℝ) → ENNReal) w :=
            measurable_one.indicator hEm
          rw [lintegral_mul_const _ hm, lintegral_indicator_one hEm]
      _ = ∫⁻ w, ∫⁻ x, f (x - w) * E.indicator 1 w := by
          refine lintegral_congr fun w => ?_
          have hm : Measurable fun y => f (y - w) := hf.comp (measurable_sub_const w)
          rw [lintegral_mul_const _ hm, lintegral_sub_right_eq_self f w, mul_comm]
      _ = 0 := hswap
  have hfpos := lintegral_ne_zero_of_tiling hΛ hf hF
  have hE0 : volume E = 0 := (mul_eq_zero.mp htotal).resolve_right hfpos
  filter_upwards [hG, measure_eq_zero_iff_ae_notMem.mp hE0] with w hw hwE
  exact le_antisymm hw (not_lt.mp hwE)
section FNorm
variable {k : ℕ}
noncomputable def fNorm (S : Set (Fin k → ℝ)) (ξ : Fin k → ℝ) : ENNReal :=
  ENNReal.ofReal (‖ftInd S ξ‖ ^ 2 / volume.real S ^ 2)
theorem measurable_fNorm {S : Set (Fin k → ℝ)} (hS : volume S ≠ ⊤) : Measurable (fNorm S) :=
  ((((continuous_ftInd hS).norm.pow 2).div_const _).measurable).ennreal_ofReal
theorem fNorm_ne_top (S : Set (Fin k → ℝ)) (ξ : Fin k → ℝ) : fNorm S ξ ≠ ⊤ :=
  ENNReal.ofReal_ne_top
theorem tsum_fNorm_of_spectralPair {S Λ : Set (Fin k → ℝ)} (h : spectralPair S Λ)
    (z : Fin k → ℝ) : ∑' l : Λ, fNorm S (z - l) = 1 := by
  have hh := h
  obtain ⟨-, hpos, hS, -⟩ := hh
  have hr : 0 < volume.real S := ENNReal.toReal_pos hpos.ne' hS
  have hs := (hasSum_normSq_ftInd_of_spectralPair h z).div_const (volume.real S ^ 2)
  rw [div_self (pow_pos hr 2).ne'] at hs
  unfold fNorm
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs.summable, hs.tsum_eq,
    ENNReal.ofReal_one]
theorem tsum_fNorm_le_of_orthogonal {S Γ : Set (Fin k → ℝ)} (hS : volume S ≠ ⊤)
    (hpos : 0 < volume S) (horth : OrthogonalOn S Γ) (z : Fin k → ℝ) :
    ∑' v : Γ, fNorm S (z - v) ≤ 1 := by
  have hr : 0 < volume.real S := ENNReal.toReal_pos hpos.ne' hS
  obtain ⟨hsum, hle⟩ := horth.summable_tsum_le hS hpos z
  unfold fNorm
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (hsum.div_const _),
    tsum_div_const, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal ((div_le_one (pow_pos hr 2)).mpr hle)
theorem spectralPair_of_tsum_fNorm {S Γ : Set (Fin k → ℝ)} (hmeas : NullMeasurableSet S volume)
    (hS : volume S ≠ ⊤) (hpos : 0 < volume S) (horth : OrthogonalOn S Γ)
    (htile : ∀ᵐ z ∂volume, ∑' v : Γ, fNorm S (z - v) = 1) : spectralPair S Γ := by
  have hr : 0 < volume.real S := ENNReal.toReal_pos hpos.ne' hS
  have hc : volume.real S ^ 2 ≠ 0 := (pow_pos hr 2).ne'
  refine spectralPair_of_orthogonal_of_tiling hmeas hS hpos horth ?_
  filter_upwards [htile] with z hz
  obtain ⟨hsum, -⟩ := horth.summable_tsum_le hS hpos z
  unfold fNorm at hz
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (hsum.div_const _),
    tsum_div_const, ENNReal.ofReal_eq_one, div_eq_one_iff_eq hc] at hz
  exact hz
theorem lintegral_fNorm_le {S : Set (Fin k → ℝ)} (hSm : MeasurableSet S)
    (hSb : Bornology.IsBounded S) (hpos : 0 < volume S) :
    ∫⁻ ξ, fNorm S ξ ≤ (volume S)⁻¹ := by
  have hS : volume S ≠ ⊤ := hSb.measure_lt_top.ne
  have hr : 0 < volume.real S := ENNReal.toReal_pos hpos.ne' hS
  have hpt : ∀ ξ, fNorm S ξ = ENNReal.ofReal (‖ftInd S ξ‖ ^ 2) *
      ENNReal.ofReal ((volume.real S ^ 2)⁻¹) := by
    intro ξ
    unfold fNorm
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _)]
  simp_rw [hpt]
  have hm : Measurable fun ξ => ENNReal.ofReal (‖ftInd S ξ‖ ^ 2) :=
    ((continuous_ftInd hS).norm.pow 2).measurable.ennreal_ofReal
  rw [lintegral_mul_const _ hm]
  have hvol : volume S = ENNReal.ofReal (volume.real S) := (ENNReal.ofReal_toReal hS).symm
  calc (∫⁻ ξ, ENNReal.ofReal (‖ftInd S ξ‖ ^ 2)) * ENNReal.ofReal ((volume.real S ^ 2)⁻¹)
      ≤ volume S * ENNReal.ofReal ((volume.real S ^ 2)⁻¹) := by
        gcongr
        exact lintegral_normSq_ftInd_le hSm hSb
    _ = (volume S)⁻¹ := by
        have hr0 : volume.real S ≠ 0 := hr.ne'
        rw [hvol, ← ENNReal.ofReal_mul hr.le, ← ENNReal.ofReal_inv_of_pos hr]
        congr 1
        field_simp
end FNorm
section Product
variable {n m : ℕ}
def proj₁ (z : Fin (n + m) → ℝ) : Fin n → ℝ := fun i => z (Fin.castAdd m i)
def proj₂ (z : Fin (n + m) → ℝ) : Fin m → ℝ := fun j => z (Fin.natAdd n j)
theorem proj₁_sub (z w : Fin (n + m) → ℝ) : proj₁ (z - w) = proj₁ z - proj₁ w := rfl
theorem proj₂_sub (z w : Fin (n + m) → ℝ) : proj₂ (z - w) = proj₂ z - proj₂ w := rfl
theorem proj₁_append (x : Fin n → ℝ) (y : Fin m → ℝ) : proj₁ (Fin.append x y) = x := by
  funext i; simp [proj₁]
theorem proj₂_append (x : Fin n → ℝ) (y : Fin m → ℝ) : proj₂ (Fin.append x y) = y := by
  funext j; simp [proj₂]
theorem measurable_proj₁ : Measurable (proj₁ : (Fin (n + m) → ℝ) → Fin n → ℝ) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _
theorem measurable_proj₂ : Measurable (proj₂ : (Fin (n + m) → ℝ) → Fin m → ℝ) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _
theorem splitEquiv_apply' (z : Fin (n + m) → ℝ) : splitEquiv n m z = (proj₁ z, proj₂ z) :=
  splitEquiv_apply z
theorem splitEquiv_symm_apply (x : Fin n → ℝ) (y : Fin m → ℝ) :
    (splitEquiv n m).symm (x, y) = Fin.append x y := by
  apply (splitEquiv n m).injective
  rw [MeasurableEquiv.apply_symm_apply, splitEquiv_apply', proj₁_append, proj₂_append]
theorem fNorm_productSet (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) (z : Fin (n + m) → ℝ) :
    fNorm (productSet A B) z = fNorm A (proj₁ z) * fNorm B (proj₂ z) := by
  have hz : z = Fin.append (proj₁ z) (proj₂ z) := Fin.append_castAdd_natAdd.symm
  unfold fNorm
  rw [← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  congr 1
  have hvol : volume.real (productSet A B) = volume.real A * volume.real B := by
    rw [measureReal_def, volume_productSet, ENNReal.toReal_mul]
    rfl
  conv_lhs => rw [hz]
  rw [ftInd_productSet, hvol, norm_mul, mul_pow, mul_pow, mul_div_mul_comm]
theorem lintegral_proj_mul {F : (Fin n → ℝ) → ENNReal} {G : (Fin m → ℝ) → ENNReal}
    (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ z, F (proj₁ z) * G (proj₂ z) = (∫⁻ x, F x) * ∫⁻ y, G y := by
  have key := (measurePreserving_splitEquiv n m).lintegral_comp_emb
    (splitEquiv n m).measurableEmbedding (fun p => F p.1 * G p.2)
  simp only [splitEquiv_apply'] at key
  rw [key, Measure.volume_eq_prod]
  exact lintegral_prod_mul hF.aemeasurable hG.aemeasurable
theorem ae_proj₁_notMem {N : Set (Fin n → ℝ)} (hN : volume N = 0) :
    ∀ᵐ z ∂(volume : Measure (Fin (n + m) → ℝ)), proj₁ z ∉ N := by
  rw [ae_iff]
  simp only [not_not]
  refine measure_mono_null (t := splitEquiv n m ⁻¹' (N ×ˢ Set.univ)) ?_ ?_
  · intro z hz
    have hz' : proj₁ z ∈ N := hz
    simp [splitEquiv_apply', hz']
  · rw [(measurePreserving_splitEquiv n m).measure_preimage_equiv, Measure.volume_eq_prod,
      Measure.prod_prod, hN, zero_mul]
theorem ae_ae_of_ae_append {P : (Fin (n + m) → ℝ) → Prop} (h : ∀ᵐ z ∂volume, P z) :
    ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), ∀ᵐ y ∂(volume : Measure (Fin m → ℝ)),
      P (Fin.append x y) := by
  have h1 : ∀ᵐ p ∂(volume : Measure ((Fin n → ℝ) × (Fin m → ℝ))),
      P ((splitEquiv n m).symm p) :=
    ((measurePreserving_splitEquiv n m).symm _).quasiMeasurePreserving.ae h
  rw [Measure.volume_eq_prod] at h1
  filter_upwards [Measure.ae_ae_of_ae_prod h1] with x hx
  filter_upwards [hx] with y hy
  rwa [splitEquiv_symm_apply] at hy
end Product
theorem isSpectral_of_window {n m : ℕ} {A : Set (Fin n → ℝ)} {B : Set (Fin m → ℝ)}
    (hAm : MeasurableSet A) (hAb : Bornology.IsBounded A)
    (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B)
    {Λ : Set (Fin (n + m) → ℝ)} (hΛ : spectralPair (productSet A B) Λ)
    {W : Set (Fin n → ℝ)} (hWm : MeasurableSet W)
    (hWvol : (volume A)⁻¹ ≤ volume W)
    (hcompat : ∀ l ∈ Λ, ∀ l' ∈ Λ, l ≠ l' →
      volume {x | proj₁ l - x ∈ W ∧ proj₁ l' - x ∈ W} = 0 ∨
        ftInd B (proj₂ l' - proj₂ l) = 0) :
    isSpectral B := by
  classical
  have hΛ' := hΛ
  obtain ⟨-, hΩpos, hΩfin, -⟩ := hΛ'
  obtain ⟨hApos, hBpos⟩ := volume_pos_of_isSpectral_productSet ⟨Λ, hΛ⟩
  have hAfin : volume A ≠ ⊤ := hAb.measure_lt_top.ne
  have hBfin : volume B ≠ ⊤ := hBb.measure_lt_top.ne
  have hBr : 0 < volume.real B := ENNReal.toReal_pos hBpos.ne' hBfin
  have horthΩ : OrthogonalOn (productSet A B) Λ := by
    obtain ⟨-, -, -, horth, -⟩ := spectralPair_iff.mp hΛ
    exact horth
  have hΛc : Λ.Countable := horthΩ.countable hΩfin hΩpos
  have : Countable Λ := hΛc.to_subtype
  let bad : Λ → Λ → Set (Fin n → ℝ) := fun l l' =>
    if (l : Fin (n + m) → ℝ) ≠ l' ∧
        ftInd B (proj₂ (l' : Fin (n + m) → ℝ) - proj₂ (l : Fin (n + m) → ℝ)) ≠ 0 then
      {x | proj₁ (l : Fin (n + m) → ℝ) - x ∈ W ∧ proj₁ (l' : Fin (n + m) → ℝ) - x ∈ W}
    else ∅
  set N := ⋃ l : Λ, ⋃ l' : Λ, bad l l' with hNdef
  have hN : volume N = 0 := by
    refine measure_iUnion_null fun l => measure_iUnion_null fun l' => ?_
    simp only [bad]
    split_ifs with h
    · rcases hcompat l l.2 l' l'.2 h.1 with h0 | h0
      · exact h0
      · exact absurd h0 h.2
    · exact measure_empty
  have hgood : ∀ x ∉ N, ∀ l l' : Λ, (l : Fin (n + m) → ℝ) ≠ l' →
      proj₁ (l : Fin (n + m) → ℝ) - x ∈ W → proj₁ (l' : Fin (n + m) → ℝ) - x ∈ W →
      ftInd B (proj₂ (l' : Fin (n + m) → ℝ) - proj₂ (l : Fin (n + m) → ℝ)) = 0 := by
    intro x hx l l' hne h1 h2
    by_contra hne0
    apply hx
    refine Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨l', ?_⟩⟩
    simp only [bad]
    rw [if_pos ⟨hne, hne0⟩]
    exact ⟨h1, h2⟩
  let S : (Fin n → ℝ) → Set Λ := fun x => {l | proj₁ (l : Fin (n + m) → ℝ) - x ∈ W}
  let prj : (x : Fin n → ℝ) → S x → Fin m → ℝ := fun x s =>
    proj₂ ((s : Λ) : Fin (n + m) → ℝ)
  have hinj : ∀ x ∉ N, Function.Injective (prj x) := by
    intro x hx s₁ s₂ h
    by_contra hne
    have hne' : ((s₁ : Λ) : Fin (n + m) → ℝ) ≠ s₂ := fun e =>
      hne (Subtype.ext (Subtype.ext e))
    have h0 := hgood x hx s₁ s₂ hne' s₁.2 s₂.2
    have h' : proj₂ ((s₂ : Λ) : Fin (n + m) → ℝ) = proj₂ ((s₁ : Λ) : Fin (n + m) → ℝ) := h.symm
    rw [h', sub_self, ftInd_zero] at h0
    exact hBr.ne' (by exact_mod_cast h0)
  let Γ : (Fin n → ℝ) → Set (Fin m → ℝ) := fun x => Set.range (prj x)
  have hΓorth : ∀ x ∉ N, OrthogonalOn B (Γ x) := by
    rintro x hx _ ⟨s₁, rfl⟩ _ ⟨s₂, rfl⟩ hne
    have hne' : ((s₁ : Λ) : Fin (n + m) → ℝ) ≠ s₂ := fun e => hne (by simp [prj, e])
    exact hgood x hx s₁ s₂ hne' s₁.2 s₂.2
  set fB := fNorm B with hfB
  have hsum : ∀ x ∉ N, ∀ y : Fin m → ℝ,
      ∑' l : Λ, W.indicator (1 : (Fin n → ℝ) → ENNReal) (proj₁ (l : Fin (n + m) → ℝ) - x) *
        fB (y - proj₂ (l : Fin (n + m) → ℝ)) = ∑' v : Γ x, fB (y - v) := by
    intro x hx y
    have h1 : ∀ l : Λ, W.indicator (1 : (Fin n → ℝ) → ENNReal)
        (proj₁ (l : Fin (n + m) → ℝ) - x) * fB (y - proj₂ (l : Fin (n + m) → ℝ)) =
          (S x).indicator (fun l : Λ => fB (y - proj₂ (l : Fin (n + m) → ℝ))) l := by
      intro l
      by_cases hl : proj₁ (l : Fin (n + m) → ℝ) - x ∈ W
      · rw [Set.indicator_of_mem hl, Set.indicator_of_mem (show l ∈ S x from hl),
          Pi.one_apply, one_mul]
      · rw [Set.indicator_of_notMem hl, Set.indicator_of_notMem (show l ∉ S x from hl),
          zero_mul]
    simp_rw [h1]
    rw [← tsum_subtype (S x) (fun l : Λ => fB (y - proj₂ (l : Fin (n + m) → ℝ)))]
    exact (Equiv.ofInjective _ (hinj x hx)).tsum_eq
      (fun v : Set.range (prj x) => fB (y - (v : Fin m → ℝ)))
  set g : (Fin (n + m) → ℝ) → ENNReal := fun z =>
    W.indicator (1 : (Fin n → ℝ) → ENNReal) (-proj₁ z) * fB (proj₂ z) with hgdef
  have hgmeas : Measurable g :=
    ((measurable_one.indicator hWm).comp measurable_proj₁.neg).mul
      ((measurable_fNorm hBfin).comp measurable_proj₂)
  have hgsub : ∀ (z : Fin (n + m) → ℝ) (l : Λ), g (z - l) =
      W.indicator (1 : (Fin n → ℝ) → ENNReal) (proj₁ (l : Fin (n + m) → ℝ) - proj₁ z) *
        fB (proj₂ z - proj₂ (l : Fin (n + m) → ℝ)) := by
    intro z l
    simp only [hgdef, proj₁_sub, proj₂_sub, neg_sub]
  have hpack : ∀ᵐ z ∂volume, ∑' l : Λ, g (z - l) ≤ 1 := by
    filter_upwards [ae_proj₁_notMem (m := m) hN] with z hz
    simp_rw [hgsub]
    rw [hsum (proj₁ z) hz (proj₂ z)]
    exact tsum_fNorm_le_of_orthogonal hBfin hBpos (hΓorth _ hz) _
  have htile : ∀ᵐ z ∂volume, ∑' l : Λ, fNorm (productSet A B) (z - l) = 1 :=
    Eventually.of_forall (tsum_fNorm_of_spectralPair hΛ)
  have hIg : ∫⁻ z, g z = volume W * ∫⁻ y, fB y := by
    have hF : Measurable fun x : Fin n → ℝ => W.indicator (1 : (Fin n → ℝ) → ENNReal) (-x) :=
      (measurable_one.indicator hWm).comp measurable_neg
    have key := lintegral_proj_mul hF (measurable_fNorm hBfin)
    rw [lintegral_neg_eq_self (W.indicator (1 : (Fin n → ℝ) → ENNReal)),
      lintegral_indicator_one hWm] at key
    exact key
  have hIf : ∫⁻ z, fNorm (productSet A B) z = (∫⁻ x, fNorm A x) * ∫⁻ y, fB y := by
    simp_rw [fNorm_productSet]
    exact lintegral_proj_mul (measurable_fNorm hAfin) (measurable_fNorm hBfin)
  have hfA := lintegral_fNorm_le hAm hAb hApos
  have hfBle := lintegral_fNorm_le hBm hBb hBpos
  have hle : ∫⁻ z, fNorm (productSet A B) z ≤ ∫⁻ z, g z := by
    rw [hIf, hIg]
    gcongr
    exact hfA.trans hWvol
  have hfin : ∫⁻ z, fNorm (productSet A B) z ≠ ⊤ := by
    rw [hIf]
    exact ENNReal.mul_ne_top (ne_top_of_le_ne_top (ENNReal.inv_ne_top.mpr hApos.ne') hfA)
      (ne_top_of_le_ne_top (ENNReal.inv_ne_top.mpr hBpos.ne') hfBle)
  have htile_g : ∀ᵐ z ∂volume, ∑' l : Λ, g (z - l) = 1 :=
    tiling_of_packing_of_lintegral_le hΛc (measurable_fNorm hΩfin) hgmeas
      (fNorm_ne_top _) htile hpack hfin hle
  have hae := ae_ae_of_ae_append htile_g
  obtain ⟨x, hx, hxN⟩ := (hae.and (measure_eq_zero_iff_ae_notMem.mp hN)).exists
  refine ⟨Γ x, spectralPair_of_tsum_fNorm hBm.nullMeasurableSet hBfin hBpos
    (hΓorth x hxN) ?_⟩
  filter_upwards [hx] with y hy
  simp_rw [hgsub, proj₁_append, proj₂_append] at hy
  rw [hsum x hxN y] at hy
  exact hy
end FCBridge
end
section
open MeasureTheory Filter Topology Metric Real
namespace FCBridge
def unitI : Set (Fin 1 → ℝ) := {x | x 0 ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)}
theorem integral_Icc_exp {t a b : ℝ} (ht : t ≠ 0) (hab : a ≤ b) :
    ∫ s in Set.Icc a b, Complex.exp (2 * π * Complex.I * (t * s)) =
      (Complex.exp (2 * π * Complex.I * (t * b)) - Complex.exp (2 * π * Complex.I * (t * a))) /
        (2 * π * Complex.I * t) := by
  have hc : (2 * π * Complex.I * t : ℂ) ≠ 0 := by
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp_all
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have h := integral_exp_mul_complex (a := a) (b := b) hc
  simp only [mul_assoc] at h ⊢
  exact h
end FCBridge
end
section
open MeasureTheory Filter Topology Metric Real Matrix
open FCBridge
namespace ZonotopeFacets
theorem orth_product {n m : ℕ} {A : Set (Fin n → ℝ)} {B : Set (Fin m → ℝ)}
    {Λ : Set (Fin (n + m) → ℝ)} (hΛ : spectralPair (productSet A B) Λ) :
    ∀ l ∈ Λ, ∀ l' ∈ Λ, l ≠ l' →
      ftInd A (proj₁ (l' - l)) = 0 ∨ ftInd B (proj₂ (l' - l)) = 0 := by
  obtain ⟨-, -, -, horth, -⟩ := spectralPair_iff.1 hΛ
  intro l hl l' hl' hne
  have h := horth l hl l' hl' hne
  have hz : l' - l = Fin.append (proj₁ (l' - l)) (proj₂ (l' - l)) :=
    Fin.append_castAdd_natAdd.symm
  rw [hz, ftInd_productSet] at h
  exact mul_eq_zero.1 h
end ZonotopeFacets
end
section
open MeasureTheory Filter Topology Metric Real
open FCBridge
namespace ProductInterval
def ivl (a b : ℝ) : Set (Fin 1 → ℝ) := {x | x 0 ∈ Set.Icc a b}
theorem measurableSet_ivl (a b : ℝ) : MeasurableSet (ivl a b) :=
  measurableSet_Icc.preimage (measurable_pi_apply 0)
theorem volume_ivl (a b : ℝ) : volume (ivl a b) = ENNReal.ofReal (b - a) := by
  have hmp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ) volume volume :=
    volume_preserving_funUnique (Fin 1) ℝ
  have : ivl a b = (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Set.Icc a b := rfl
  rw [this, hmp.measure_preimage_equiv, Real.volume_Icc]
theorem norm_fin_one (x : Fin 1 → ℝ) : ‖x‖ = |x 0| := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => ?_) ?_
  · rw [Fin.fin_one_eq_zero i, Real.norm_eq_abs]
  · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x 0
theorem isBounded_ivl (a b : ℝ) : Bornology.IsBounded (ivl a b) := by
  refine (isBounded_closedBall (x := (0 : Fin 1 → ℝ)) (r := |a| + |b|)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff, norm_fin_one, abs_le]
  obtain ⟨h1, h2⟩ := hx
  constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith
theorem ftInd_ivl_eq {a b t : ℝ} (hab : a ≤ b) (ht : t ≠ 0) :
    ftInd (ivl a b) (fun _ => t) =
      (Complex.exp (2 * π * Complex.I * (t * b)) - Complex.exp (2 * π * Complex.I * (t * a))) /
        (2 * π * Complex.I * t) := by
  let e := MeasurableEquiv.funUnique (Fin 1) ℝ
  have hmp : MeasurePreserving e volume volume := volume_preserving_funUnique (Fin 1) ℝ
  have hset : ivl a b = e ⁻¹' Set.Icc a b := rfl
  let g : ℝ → ℂ := fun s => Complex.exp (2 * π * Complex.I * (t * s))
  have hchar : ∀ x : Fin 1 → ℝ, exponentialCharacter (fun _ => t) x = g (e x) := by
    intro x
    simp only [exponentialCharacter, Fin.sum_univ_one, g]
    push_cast
    rfl
  have hft : ftInd (ivl a b) (fun _ => t) = ∫ s in Set.Icc a b, g s := by
    unfold ftInd
    rw [← hmp.setIntegral_preimage_emb e.measurableEmbedding g, ← hset]
    exact setIntegral_congr_fun (measurableSet_ivl a b) fun x _ => hchar x
  rw [hft]
  exact integral_Icc_exp ht hab
theorem one_le_of_ftInd_ivl_eq_zero {a b t : ℝ} (hab : a < b)
    (h : ftInd (ivl a b) (fun _ => t) = 0) : 1 ≤ |t| * (b - a) := by
  have ht : t ≠ 0 := by
    rintro rfl
    rw [show (fun _ : Fin 1 => (0 : ℝ)) = 0 from rfl, ftInd_zero, measureReal_def,
      volume_ivl, ENNReal.toReal_ofReal (by linarith)] at h
    have : (b - a : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.2 hab).ne'
    exact this (by exact_mod_cast h)
  rw [ftInd_ivl_eq hab.le ht] at h
  have hden : (2 * π * Complex.I * t : ℂ) ≠ 0 := by
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp_all
  have hnum := (div_eq_zero_iff.1 h).resolve_right hden
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (sub_eq_zero.1 hnum)
  have h2 : (2 * π * Complex.I : ℂ) * ((t * (b - a) : ℝ) - n) = 0 := by
    push_cast
    linear_combination hn
  have h2π : (2 * π * Complex.I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp_all
  have h3 : t * (b - a) = n := by
    have := (mul_eq_zero.1 h2).resolve_left h2π
    exact_mod_cast sub_eq_zero.1 this
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : t * (b - a) = 0 := by exact_mod_cast h3
    exact (mul_ne_zero ht (sub_pos.2 hab).ne') this
  have h4 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
  rw [← h3, abs_mul, abs_of_pos (sub_pos.2 hab)] at h4
  exact h4
theorem isSpectral_right_of_ivl {m : ℕ} {a b : ℝ} (hab : a < b) {B : Set (Fin m → ℝ)}
    (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B)
    (hspec : isSpectral (productSet (ivl a b) B)) : isSpectral B := by
  obtain ⟨Λ, hΛ⟩ := hspec
  have hba : 0 < b - a := sub_pos.2 hab
  let W : Set (Fin 1 → ℝ) := {w | |w 0| < 1 / (2 * (b - a))}
  have hW : W = (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
      Set.Ioo (-(1 / (2 * (b - a)))) (1 / (2 * (b - a))) := by
    ext w
    simp only [W, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioo, abs_lt]
    rfl
  refine isSpectral_of_window (measurableSet_ivl a b) (isBounded_ivl a b) hBm hBb hΛ (W := W)
    ?_ ?_ ?_
  · rw [hW]
    exact measurableSet_Ioo.preimage (MeasurableEquiv.funUnique (Fin 1) ℝ).measurable
  · have hmp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ) volume volume :=
      volume_preserving_funUnique (Fin 1) ℝ
    rw [hW, hmp.measure_preimage_equiv, Real.volume_Ioo, volume_ivl,
      ← ENNReal.ofReal_inv_of_pos hba]
    apply le_of_eq
    congr 1
    field_simp
    ring
  · intro l hl l' hl' hne
    rcases ZonotopeFacets.orth_product hΛ l hl l' hl' hne with h0 | h0
    · left
      have hfun : proj₁ (l' - l) = fun _ => proj₁ (l' - l) 0 := by
        funext i; rw [Fin.fin_one_eq_zero i]
      rw [hfun] at h0
      have key := one_le_of_ftInd_ivl_eq_zero hab h0
      have hempty : {x : Fin 1 → ℝ | proj₁ l - x ∈ W ∧ proj₁ l' - x ∈ W} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun x hx => ?_
        obtain ⟨h1, h2⟩ := hx
        have h1' : |proj₁ l 0 - x 0| < 1 / (2 * (b - a)) := h1
        have h2' : |proj₁ l' 0 - x 0| < 1 / (2 * (b - a)) := h2
        have hsub : proj₁ (l' - l) 0 = (proj₁ l' 0 - x 0) - (proj₁ l 0 - x 0) := by
          rw [proj₁_sub]; simp
        have habs : |proj₁ (l' - l) 0| < 1 / (b - a) := by
          rw [hsub]
          calc |(proj₁ l' 0 - x 0) - (proj₁ l 0 - x 0)|
              ≤ |proj₁ l' 0 - x 0| + |proj₁ l 0 - x 0| := abs_sub _ _
            _ < 1 / (2 * (b - a)) + 1 / (2 * (b - a)) := add_lt_add h2' h1'
            _ = 1 / (b - a) := by field_simp; ring
        have : |proj₁ (l' - l) 0| * (b - a) < 1 := by
          rwa [lt_div_iff₀ hba] at habs
        linarith
      rw [hempty, measure_empty]
    · right
      rwa [← proj₂_sub]
def spectralProductImpliesRightSpectral (n m : ℕ) : Prop :=
  ∀ (A : ConvexBody (Fin n → ℝ)) (B : Set (Fin m → ℝ)),
    (interior (A : Set (Fin n → ℝ))).Nonempty →
    Bornology.IsBounded B → MeasurableSet B →
      isSpectral (productSet (A : Set (Fin n → ℝ)) B) → isSpectral B
theorem convexBody_one_eq_ivl (A : ConvexBody (Fin 1 → ℝ))
    (hA : (interior (A : Set (Fin 1 → ℝ))).Nonempty) :
    ∃ a b, a < b ∧ (A : Set (Fin 1 → ℝ)) = ivl a b := by
  set S : Set ℝ := (fun x : Fin 1 → ℝ => x 0) '' (A : Set (Fin 1 → ℝ)) with hS
  have hSc : IsCompact S := A.isCompact.image (continuous_apply 0)
  have hSne : S.Nonempty := A.nonempty.image _
  have hSconv : Convex ℝ S :=
    A.convex.linear_image (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
  have hAS : (A : Set (Fin 1 → ℝ)) = {x | x 0 ∈ S} := by
    ext x
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := by funext i; rw [Fin.fin_one_eq_zero i]; exact hyx
      rwa [← this]
  have ha := hSc.sInf_mem hSne
  have hb := hSc.sSup_mem hSne
  have hSeq : S = Set.Icc (sInf S) (sSup S) := by
    refine Set.Subset.antisymm (fun s hs => ⟨csInf_le hSc.bddBelow hs, le_csSup hSc.bddAbove hs⟩)
      ?_
    exact (convex_iff_ordConnected.1 hSconv).out ha hb
  refine ⟨sInf S, sSup S, ?_, ?_⟩
  · rcases (csInf_le_csSup hSne hSc.bddBelow hSc.bddAbove).lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := hA
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
      have hxA : x ∈ (A : Set (Fin 1 → ℝ)) := interior_subset hx
      let y : Fin 1 → ℝ := fun _ => x 0 + ε / 2
      have hy : y ∈ ball x ε := by
        rw [mem_ball, dist_eq_norm, norm_fin_one]
        simp only [y, Pi.sub_apply, add_sub_cancel_left]
        rw [abs_of_pos (by positivity)]
        linarith
      have hyA : y ∈ (A : Set (Fin 1 → ℝ)) := interior_subset (hball hy)
      rw [hAS, hSeq] at hxA hyA
      have h1 := hxA.1; have h2 := hxA.2; have h3 := hyA.1; have h4 := hyA.2
      simp only [y] at h3 h4
      rw [h] at h1 h3
      linarith
  · rw [hAS]
    ext x
    show x 0 ∈ S ↔ x 0 ∈ Set.Icc (sInf S) (sSup S)
    rw [← hSeq]
theorem fc_one_dimensional : True ↔ ∀ m : ℕ, 0 < m → spectralProductImpliesRightSpectral 1 m := by
  refine ⟨fun _ m _ A B hA hBb hBm hspec => ?_, fun _ => trivial⟩
  obtain ⟨a, b, hab, hAeq⟩ := convexBody_one_eq_ivl A hA
  rw [hAeq] at hspec
  exact isSpectral_right_of_ivl hab hBm hBb hspec
end ProductInterval
end

theorem OMA.solution : type_of% @SpectralSetProduct.isSpectral_right_of_product_one_dimensional :=
  fun m hm => ProductInterval.fc_one_dimensional.mp trivial m hm
