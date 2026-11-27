import FormalConjectures.Wikipedia.Fuglede
import Mathlib.Tactic
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Reduction R1 for `Fuglede.FugledeConjecture.variants.dim_1`

Dutkay-Lai (2014) reduction of 1D Fuglede's conjecture to two published structure theorems
(`H1`: Lagarias-Wang / Kolountzakis-Lagarias periodic rational tiling decomposition;
`H3`: Iosevich-Kolountzakis / Landau periodic spectrum) and two purely discrete conjectures
(`H2`: Universal Spectrum Conjecture on `ZMod L`; `H4`: Universal Tiling Conjecture on `ℤ`).
-/

namespace OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

/-- Lagarias-Wang (1996) and Kolountzakis-Lagarias (1996): every bounded measurable
unit-measure translational tile of R admits a periodic rational fiber decomposition
over [0, 1/k) with fibers tiling a cyclic group ZMod L against a common complement A. -/
def H1 : Prop :=
  ∀ Ω : Set (Fin 1 → ℝ),
    Bornology.IsBounded Ω → MeasurableSet Ω → volume Ω = 1 →
    tilesByTranslation Ω →
    ∃ (k L : ℕ) (A : Finset (ZMod L)) (ℬ : Finset (Finset ℤ)) (T : Finset ℤ → Set ℝ),
      0 < k ∧ 0 < L ∧
      (∀ B ∈ ℬ, B.card = k ∧ ∀ z : ZMod L,
        ∃! p : {a // a ∈ A} × {b // b ∈ B}, p.1.1 + (p.2.1 : ZMod L) = z) ∧
      (∀ B ∈ ℬ, MeasurableSet (T B) ∧ T B ⊆ Set.Ico 0 (1 / (k : ℝ))) ∧
      (∀ B₁ ∈ ℬ, ∀ B₂ ∈ ℬ, B₁ ≠ B₂ → Disjoint (T B₁) (T B₂)) ∧
      volume (Set.Ico (0 : ℝ) (1 / (k : ℝ)) \ ⋃ B ∈ ℬ, T B) = 0 ∧
      volume (symmDiff Ω (⋃ B ∈ ℬ, {x : Fin 1 → ℝ | ∃ t ∈ T B, ∃ b ∈ B,
        x 0 = t + (b : ℝ) / (k : ℝ)})) = 0

/-- Universal Spectrum Conjecture on finite cyclic groups USC(Z_L)
(Lagarias-Wang 1997; equivalent to T-S(Z_L) and T-S(R) by Dutkay-Lai 2014 Thm 1.1(i)):
any finite family of subsets of ZMod L sharing a common tiling complement A admits
a common discrete spectrum Γ in ZMod L. -/
def H2 : Prop :=
  ∀ (L : ℕ), 0 < L →
    ∀ (A : Finset (ZMod L)) (ℬ : Finset (Finset (ZMod L))),
      (∀ B ∈ ℬ, ∀ z : ZMod L,
        ∃! p : {a // a ∈ A} × {b // b ∈ B}, p.1.1 + p.2.1 = z) →
      ∃ Γ : Finset (ZMod L),
        (∀ B ∈ ℬ, Γ.card = B.card) ∧
        (∀ B ∈ ℬ, ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ →
          ∑ b ∈ B, Complex.exp (2 * Real.pi * Complex.I *
            (((γ₁.val : ℝ) - (γ₂.val : ℝ)) * (b.val : ℝ) / (L : ℝ))) = 0)

/-- Iosevich-Kolountzakis (2013) + Landau density: every bounded measurable
unit-measure spectral set in R admits a periodic spectrum Γ + pZ with p > 0
and |Γ| = p in [0, p). -/
def H3 : Prop :=
  ∀ Ω : Set (Fin 1 → ℝ),
    Bornology.IsBounded Ω → MeasurableSet Ω → volume Ω = 1 →
    isSpectral Ω →
    ∃ (p : ℕ) (Γ : Finset ℝ),
      0 < p ∧ Γ.card = p ∧
      (∀ γ ∈ Γ, 0 ≤ γ ∧ γ < (p : ℝ)) ∧
      spectralPair Ω {ξ : Fin 1 → ℝ | ∃ γ ∈ Γ, ∃ n : ℤ, ξ 0 = γ + (p : ℝ) * (n : ℝ)}

/-- Universal Tiling Conjecture on Z, UTC(Z)
(equivalent to S-T(R) by Dutkay-Lai 2014 Thm 1.1(iv)):
any finite family of finite subsets of Z sharing a common discrete spectrum Γ in R
admits a common translational tiling complement T in Z. -/
def H4 : Prop :=
  ∀ (p : ℕ), 0 < p →
    ∀ (Γ : Finset ℝ) (𝒜 : Finset (Finset ℤ)),
      Γ.card = p →
      (∀ S ∈ 𝒜, S.card = p ∧
        ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ →
          ∑ k ∈ S, Complex.exp (2 * Real.pi * Complex.I * (γ₁ - γ₂) * (k : ℝ)) = 0) →
      ∃ T : Set ℤ, ∀ S ∈ 𝒜, ∀ m : ℤ,
        ∃! q : {k // k ∈ S} × {t // t ∈ T}, q.1.1 + q.2.1 = m

/- Part 0: Basic 1D measure, exponential, and Fourier helpers -/

lemma mp_funUnique_symm :
    MeasurePreserving (fun t : ℝ => (fun _ : Fin 1 => t)) volume volume := by
  exact (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm

lemma mp_funUnique :
    MeasurePreserving (fun x : Fin 1 → ℝ => x 0) volume volume := by
  exact MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ

lemma volume_preimage_apply0 (S : Set ℝ) :
    volume {x : Fin 1 → ℝ | x 0 ∈ S} = volume S := by
  change volume ((fun x : Fin 1 → ℝ => x 0) ⁻¹' S) = volume S
  exact mp_funUnique.measure_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding S

lemma setIntegral_preimage_apply0 (S : Set ℝ) (f : (Fin 1 → ℝ) → ℂ) :
    ∫ x in {x : Fin 1 → ℝ | x 0 ∈ S}, f x = ∫ t in S, f (fun _ => t) := by
  have h := mp_funUnique_symm.setIntegral_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding f {x : Fin 1 → ℝ | x 0 ∈ S}
  have hpre : (fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' {x : Fin 1 → ℝ | x 0 ∈ S} = S := by
    ext t; simp
  rw [hpre] at h
  exact h.symm

lemma ec1_eq (ξ x : Fin 1 → ℝ) :
    exponentialCharacter ξ x = Complex.exp (2 * Real.pi * Complex.I * (ξ 0 * x 0)) := by
  unfold exponentialCharacter
  simp

lemma ec1_conj (ξ x : Fin 1 → ℝ) :
    conj (exponentialCharacter ξ x) = exponentialCharacter (-ξ) x := by
  rw [ec1_eq, ec1_eq, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]

lemma ec1_add_left (ξ η x : Fin 1 → ℝ) :
    exponentialCharacter (ξ + η) x = exponentialCharacter ξ x * exponentialCharacter η x := by
  rw [ec1_eq, ec1_eq, ec1_eq, ← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, Complex.ofReal_add]
  ring

lemma inner_toLp_eq {Ω : Set (Fin 1 → ℝ)} (u v : (Fin 1 → ℝ) → ℂ)
    (hu : MemLp u 2 (volume.restrict Ω)) (hv : MemLp v 2 (volume.restrict Ω)) :
    ⟪hu.toLp u, hv.toLp v⟫_ℂ = ∫ x in Ω, conj (u x) * v x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]

lemma exp_two_pi_I_int (m : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)) = 1 := by
  rw [Complex.exp_eq_one_iff]
  refine ⟨m, ?_⟩
  ring

lemma memLp_finsetSum {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (f : ι → α → ℂ) (hf : ∀ i ∈ s, MemLp (f i) 2 μ) :
    MemLp (fun x => ∑ i ∈ s, f i x) 2 μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact MemLp.zero
  | insert a s ha ih =>
    have ha' : MemLp (f a) 2 μ := hf a (Finset.mem_insert_self a s)
    have hs' : MemLp (fun x => ∑ i ∈ s, f i x) 2 μ :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hsum : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
      funext x; rw [Finset.sum_insert ha]
    rw [hsum]
    exact ha'.add hs'

lemma integral_Ico_div_exp (k : ℕ) (hk : 0 < k) (n : ℤ) (hn : n ≠ 0) :
    ∫ t in Set.Ico (0 : ℝ) (1 / (k : ℝ)),
      Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * t)) = 0 := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hc : (2 * Real.pi * Complex.I * (k : ℂ) * (n : ℂ)) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpiC) Complex.I_ne_zero) hkC) hnC
  have hrew : (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * t))) =
      fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I * (k : ℂ) * (n : ℂ)) * (t : ℂ)) := by
    funext t
    congr 1
    push_cast
    ring
  rw [hrew, MeasureTheory.integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 1 / (k : ℝ)),
    integral_exp_mul_complex hc]
  have h1 : (2 * Real.pi * Complex.I * (k : ℂ) * (n : ℂ)) * ((1 / (k : ℝ) : ℝ) : ℂ) =
      2 * Real.pi * Complex.I * (n : ℂ) := by
    push_cast
    field_simp [hkC]
  rw [h1, exp_two_pi_I_int n]
  simp

lemma fourier_complete_Ico_one (G : ℝ → ℂ)
    (hG : MemLp G 2 (volume.restrict (Set.Ico (0 : ℝ) 1)))
    (h : ∀ n : ℤ, ∫ t in Set.Ico (0 : ℝ) 1,
      Complex.exp (-(2 * Real.pi * Complex.I * ((n : ℝ) * t))) * G t = 0) :
    G =ᵐ[volume.restrict (Set.Ico (0 : ℝ) 1)] 0 := by
  let Sq : Set (Fin 1 → ℝ) := Set.univ.pi fun _ : Fin 1 => Set.Ico (0 : ℝ) 1
  let ψ : UnitAddTorus (Fin 1) → (Fin 1 → ℝ) :=
    Subtype.val ∘ ⇑(UnitAddTorus.measurableEquivPiIoc (0 : Fin 1 → ℝ))
  let μT : Measure (UnitAddTorus (Fin 1)) :=
    @volume (UnitAddTorus (Fin 1))
      (@MeasureSpace.pi (Fin 1) (Fin.fintype 1) (fun _ => UnitAddCircle)
        (fun _ => instMeasureSpaceUnitAddCircle))
  have hψ_mp : MeasurePreserving ψ μT (volume.restrict Sq) := by
    have h1 := UnitAddTorus.measurePreserving_equivPiIoc (0 : Fin 1 → ℝ)
    have hS : MeasurableSet {x : Fin 1 → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin 1 → ℝ) i) ((0 : Fin 1 → ℝ) i + 1)} := by
      convert (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc) :
        MeasurableSet (Set.univ.pi fun _ : Fin 1 => Set.Ioc (0 : ℝ) 1)) using 1
      ext x; simp
    have h2 : MeasurePreserving
        (Subtype.val : {x : Fin 1 → ℝ // ∀ i, x i ∈ Set.Ioc ((0 : Fin 1 → ℝ) i) ((0 : Fin 1 → ℝ) i + 1)} → _)
        (Measure.comap Subtype.val volume) (volume.restrict _) :=
      ⟨measurable_subtype_coe, map_comap_subtype_coe hS volume⟩
    have h3 := h2.comp h1
    have hset : volume.restrict {x : Fin 1 → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin 1 → ℝ) i) ((0 : Fin 1 → ℝ) i + 1)}
        = volume.restrict Sq := by
      apply Measure.restrict_congr_set
      have e1 : {x : Fin 1 → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin 1 → ℝ) i) ((0 : Fin 1 → ℝ) i + 1)} =
          Set.univ.pi (fun i => Set.Ioc ((fun _ : Fin 1 => (0 : ℝ)) i) ((fun _ : Fin 1 => (1 : ℝ)) i)) := by
        ext x; simp
      rw [e1]
      exact Measure.univ_pi_Ioc_ae_eq_Icc.trans
        (Measure.univ_pi_Ico_ae_eq_Icc (f := fun _ : Fin 1 => (0 : ℝ)) (g := fun _ => (1 : ℝ))).symm
    rw [hset] at h3
    exact h3
  have hSq_eq : Sq = {x : Fin 1 → ℝ | x 0 ∈ Set.Ico (0 : ℝ) 1} := by
    ext x
    simp [Sq]
  have hproj_mp : MeasurePreserving (fun x : Fin 1 → ℝ => x 0)
      (volume.restrict Sq) (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
    rw [hSq_eq]
    exact mp_funUnique.restrict_preimage_emb
      (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding (Set.Ico (0 : ℝ) 1)
  have hG1 : MemLp (fun x : Fin 1 → ℝ => G (x 0)) 2 (volume.restrict Sq) :=
    hG.comp_measurePreserving hproj_mp
  have hGψ : MemLp ((fun x : Fin 1 → ℝ => G (x 0)) ∘ ψ) 2 μT :=
    hG1.comp_measurePreserving hψ_mp
  set Gt : Lp ℂ 2 μT := hGψ.toLp ((fun x : Fin 1 → ℝ => G (x 0)) ∘ ψ) with hGt
  have hmFourier : ∀ (n : Fin 1 → ℤ) (θ : UnitAddTorus (Fin 1)),
      UnitAddTorus.mFourier n θ = Complex.exp (2 * Real.pi * Complex.I * ((n 0 : ℝ) * ψ θ 0)) := by
    intro n θ
    have hθ : θ = fun i => ((ψ θ i : ℝ) : UnitAddCircle) := by
      conv_lhs => rw [← (UnitAddTorus.measurableEquivPiIoc (0 : Fin 1 → ℝ)).symm_apply_apply θ]
      rfl
    generalize ψ θ = y at hθ ⊢
    subst hθ
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
      Fin.prod_univ_one]
    congr 1
    push_cast
    ring
  have hcoef : ∀ n : Fin 1 → ℤ, ⟪UnitAddTorus.mFourierLp 2 n, Gt⟫_ℂ = 0 := by
    intro n
    rw [L2.inner_def]
    have h1 : ∫ a, ⟪(UnitAddTorus.mFourierLp 2 n : UnitAddTorus (Fin 1) → ℂ) a,
        (Gt : UnitAddTorus (Fin 1) → ℂ) a⟫_ℂ ∂μT
        = ∫ θ, Complex.exp (-(2 * Real.pi * Complex.I * ((n 0 : ℝ) * ψ θ 0))) * G (ψ θ 0) ∂μT := by
      apply integral_congr_ae
      filter_upwards [UnitAddTorus.coeFn_mFourierLp 2 n, hGψ.coeFn_toLp] with θ h1 h2
      rw [h1, h2, RCLike.inner_apply, mul_comm, hmFourier]
      simp only [Function.comp_apply]
      rw [← Complex.exp_conj]
      congr 2
      simp [Complex.conj_ofReal, map_ofNat]
    refine h1.trans ?_
    have hint_eq : ∫ θ, Complex.exp (-(2 * Real.pi * Complex.I * ((n 0 : ℝ) * ψ θ 0))) * G (ψ θ 0) ∂μT
        = ∫ x in Sq, Complex.exp (-(2 * Real.pi * Complex.I * ((n 0 : ℝ) * x 0))) * G (x 0) := by
      have hmeas : AEStronglyMeasurable
          (fun x : Fin 1 → ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((n 0 : ℝ) * x 0))) * G (x 0))
          (volume.restrict Sq) := by
        have hc : Continuous (fun x : Fin 1 → ℝ =>
            Complex.exp (-(2 * Real.pi * Complex.I * ((n 0 : ℝ) * x 0)))) := by
          continuity
        exact hc.aestronglyMeasurable.mul hG1.1
      rw [← hψ_mp.map_eq] at hmeas ⊢
      exact (integral_map hψ_mp.measurable.aemeasurable hmeas).symm
    rw [hint_eq, hSq_eq, setIntegral_preimage_apply0]
    exact h (n 0)
  have hzero : Gt = 0 := by
    apply (UnitAddTorus.mFourierBasis (d := Fin 1)).repr.injective
    rw [map_zero]
    ext n
    rw [HilbertBasis.repr_apply_apply, UnitAddTorus.coe_mFourierBasis, hcoef n]
    rfl
  have hae : ((fun x : Fin 1 → ℝ => G (x 0)) ∘ ψ) =ᵐ[μT] 0 := by
    have := hGψ.coeFn_toLp
    rw [← hGt, hzero] at this
    exact this.symm.trans (Lp.coeFn_zero _ _ _)
  have h2 : eLpNorm (fun x : Fin 1 → ℝ => G (x 0)) 2 (volume.restrict Sq) = 0 := by
    rw [← eLpNorm_comp_measurePreserving hG1.1 hψ_mp, eLpNorm_congr_ae hae, eLpNorm_zero]
  have h3 : eLpNorm G 2 (volume.restrict (Set.Ico (0 : ℝ) 1)) = 0 := by
    rw [← eLpNorm_comp_measurePreserving hG.1 hproj_mp]
    exact h2
  exact (eLpNorm_eq_zero_iff hG.1 two_ne_zero).1 h3

lemma fourier_complete_Ico_div (k : ℕ) (hk : 0 < k) (G : ℝ → ℂ)
    (hG : MemLp G 2 (volume.restrict (Set.Ico (0 : ℝ) (1 / (k : ℝ)))))
    (h : ∀ n : ℤ, ∫ t in Set.Ico (0 : ℝ) (1 / (k : ℝ)),
      Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * t))) * G t = 0) :
    G =ᵐ[volume.restrict (Set.Ico (0 : ℝ) (1 / (k : ℝ)))] 0 := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hpre : (fun u : ℝ => u / (k : ℝ)) ⁻¹' Set.Ico (0 : ℝ) (1 / (k : ℝ)) = Set.Ico (0 : ℝ) 1 := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(div_nonneg_iff.1 h1).resolve_right (fun hc => by linarith) |>.1,
        (div_lt_div_iff_of_pos_right hkpos).1 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨div_nonneg h1 hkpos.le, (div_lt_div_iff_of_pos_right hkpos).2 h2⟩
  have hemb : MeasurableEmbedding (fun u : ℝ => u / (k : ℝ)) :=
    (Homeomorph.mulRight₀ (k : ℝ)⁻¹ (inv_ne_zero hkne)).measurableEmbedding
  have hmul : Measure.map (fun u : ℝ => u / (k : ℝ)) volume = ENNReal.ofReal (k : ℝ) • volume := by
    have := Real.map_volume_mul_right (inv_ne_zero hkne)
    simp only [abs_of_pos hkpos, inv_inv] at this
    simpa [div_eq_mul_inv] using this
  have hmap : Measure.map (fun u : ℝ => u / (k : ℝ)) (volume.restrict (Set.Ico (0 : ℝ) 1)) =
      ENNReal.ofReal (k : ℝ) • volume.restrict (Set.Ico (0 : ℝ) (1 / (k : ℝ))) := by
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, Measure.restrict_apply (hemb.measurable hs),
      Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul,
      ← hpre, ← Set.preimage_inter, ← hemb.map_apply volume, hmul, Measure.smul_apply, smul_eq_mul]
  have hG' : MemLp (fun u : ℝ => G (u / (k : ℝ))) 2 (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
    have hsm : MemLp G 2 (ENNReal.ofReal (k : ℝ) • volume.restrict (Set.Ico (0 : ℝ) (1 / (k : ℝ)))) :=
      hG.smul_measure ENNReal.ofReal_ne_top
    rw [← hmap] at hsm
    exact (memLp_map_measure_iff hsm.1 hemb.measurable.aemeasurable).1 hsm
  have hzero' : (fun u : ℝ => G (u / (k : ℝ))) =ᵐ[volume.restrict (Set.Ico (0 : ℝ) 1)] 0 := by
    apply fourier_complete_Ico_one _ hG'
    intro n
    have hmeas : AEStronglyMeasurable
        (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * t))) * G t)
        (Measure.map (fun u : ℝ => u / (k : ℝ)) (volume.restrict (Set.Ico (0 : ℝ) 1))) := by
      rw [hmap]
      have hc : Continuous (fun t : ℝ =>
          Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * t)))) := by
        continuity
      exact (hc.aestronglyMeasurable.mul hG.1).smul_measure _
    have hint := integral_map hemb.measurable.aemeasurable hmeas
    rw [hmap, integral_smul_measure, h n, smul_zero] at hint
    rw [hint]
    refine setIntegral_congr_fun measurableSet_Ico fun u _ => ?_
    congr 2
    have h1 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast
    field_simp [h1]
  have hnull : (volume.restrict (Set.Ico (0 : ℝ) 1)) ((fun u : ℝ => u / (k : ℝ)) ⁻¹' {t | G t ≠ 0}) = 0 := by
    have hz := ae_iff.1 hzero'
    simpa using hz
  have hnull2 : (Measure.map (fun u : ℝ => u / (k : ℝ)) (volume.restrict (Set.Ico (0 : ℝ) 1))) {t | G t ≠ 0} = 0 := by
    rw [hemb.map_apply]
    exact hnull
  rw [hmap, Measure.smul_apply, smul_eq_mul] at hnull2
  have hk_ne : ENNReal.ofReal (k : ℝ) ≠ 0 := (ENNReal.ofReal_pos.2 hkpos).ne'
  rw [Filter.EventuallyEq, ae_iff]
  exact (mul_eq_zero.1 hnull2).resolve_left hk_ne

/- Part 1: Null-set invariance and positive scaling invariance -/

lemma ae_eq_set_of_symmDiff_null {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (h : μ (symmDiff s t) = 0) : s =ᵐ[μ] t := by
  rw [MeasureTheory.ae_eq_set]
  exact ⟨measure_mono_null Set.subset_union_left h, measure_mono_null Set.subset_union_right h⟩

lemma isSpectral_of_ae_eq {Ω₁ Ω₂ : Set (Fin 1 → ℝ)}
    (hnull : volume (symmDiff Ω₁ Ω₂) = 0)
    (hmeas : NullMeasurableSet Ω₂ volume)
    (hspec : isSpectral Ω₁) : isSpectral Ω₂ := by
  have hae : (Ω₁ : Set (Fin 1 → ℝ)) =ᵐ[volume] Ω₂ := ae_eq_set_of_symmDiff_null hnull
  have hvol : volume Ω₁ = volume Ω₂ := measure_congr hae
  have hres : volume.restrict Ω₁ = volume.restrict Ω₂ := Measure.restrict_congr_set hae
  obtain ⟨Λ, _, hpos, hfin, horth, hspan⟩ := hspec
  refine ⟨Λ, hmeas, hvol ▸ hpos, hvol ▸ hfin, ?_, ?_⟩
  · intro ξ₁ hξ₁ ξ₂ hξ₂ hne
    have h1 := horth ξ₁ hξ₁ ξ₂ hξ₂ hne
    dsimp only at h1 ⊢
    rw [inner_toLp_eq] at h1 ⊢
    rw [setIntegral_congr_set hae.symm]
    exact h1
  · rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff] at hspan ⊢
    intro g hg
    rw [Submodule.mem_orthogonal] at hg
    set gf : (Fin 1 → ℝ) → ℂ := (g : (Fin 1 → ℝ) → ℂ)
    have hgm : MemLp gf 2 (volume.restrict Ω₂) := Lp.memLp g
    have hg1 : MemLp gf 2 (volume.restrict Ω₁) := by rwa [hres]
    set g₁ : Lp ℂ 2 (volume.restrict Ω₁) := hg1.toLp gf with hg₁
    have hmem : g₁ ∈ (Submodule.span ℂ (Set.range fun ξ : Λ =>
        (exponentialCharacter_memLp hfin ξ.1).toLp (exponentialCharacter ξ.1)))ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨ξ, rfl⟩
        rw [inner_toLp_eq, setIntegral_congr_set hae]
        have h2 := hg _ (Submodule.subset_span ⟨ξ, rfl⟩)
        dsimp only at h2
        rw [← Lp.toLp_coeFn g hgm, inner_toLp_eq] at h2
        exact h2
      · simp
      · intro u v _ _ hu hv; rw [inner_add_left, hu, hv, add_zero]
      · intro a u _ hu; rw [inner_smul_left, hu, mul_zero]
    have hg1_zero : g₁ = 0 := hspan g₁ hmem
    have hae1 : gf =ᵐ[volume.restrict Ω₁] 0 := by
      have := hg1.coeFn_toLp
      rw [← hg₁, hg1_zero] at this
      exact this.symm.trans (Lp.coeFn_zero _ _ _)
    rw [Lp.eq_zero_iff_ae_eq_zero]
    change gf =ᵐ[volume.restrict Ω₂] 0
    rwa [← hres]

lemma map_volume_smul_fin1 {c : ℝ} (hc : 0 < c) :
    Measure.map (fun x : Fin 1 → ℝ => c • x) volume = ENNReal.ofReal c⁻¹ • volume := by
  have h1 := mp_funUnique_symm.map_eq
  have hmul : Measure.map (fun t : ℝ => c * t) volume = ENNReal.ofReal c⁻¹ • volume := by
    have := Real.map_volume_mul_left hc.ne'
    simpa [abs_of_pos hc] using this
  have hcomp : (fun x : Fin 1 → ℝ => c • x) ∘ (fun t : ℝ => (fun _ : Fin 1 => t)) =
      (fun t : ℝ => (fun _ : Fin 1 => t)) ∘ (fun t : ℝ => c * t) := by
    funext t i; simp
  calc Measure.map (fun x : Fin 1 → ℝ => c • x) volume
      = Measure.map (fun x : Fin 1 → ℝ => c • x)
          (Measure.map (fun t : ℝ => (fun _ : Fin 1 => t)) volume) := by rw [h1]
    _ = Measure.map ((fun x : Fin 1 → ℝ => c • x) ∘ (fun t : ℝ => (fun _ : Fin 1 => t))) volume := by
        rw [Measure.map_map (continuous_const_smul c).measurable mp_funUnique_symm.measurable]
    _ = Measure.map ((fun t : ℝ => (fun _ : Fin 1 => t)) ∘ (fun t : ℝ => c * t)) volume := by
        rw [hcomp]
    _ = Measure.map (fun t : ℝ => (fun _ : Fin 1 => t)) (Measure.map (fun t : ℝ => c * t) volume) := by
        rw [← Measure.map_map mp_funUnique_symm.measurable (continuous_const_mul c).measurable]
    _ = Measure.map (fun t : ℝ => (fun _ : Fin 1 => t)) (ENNReal.ofReal c⁻¹ • volume) := by
        rw [hmul]
    _ = ENNReal.ofReal c⁻¹ • Measure.map (fun t : ℝ => (fun _ : Fin 1 => t)) volume := by
        rw [Measure.map_smul]
    _ = ENNReal.ofReal c⁻¹ • volume := by rw [h1]

lemma volume_preimage_smul_fin1 {c : ℝ} (hc : 0 < c) (S : Set (Fin 1 → ℝ)) :
    volume ((fun x : Fin 1 → ℝ => c • x) ⁻¹' S) = ENNReal.ofReal c⁻¹ * volume S := by
  have hemb : MeasurableEmbedding (fun x : Fin 1 → ℝ => c • x) :=
    (Homeomorph.smulOfNeZero c hc.ne').measurableEmbedding
  have h1 : Measure.map (fun x : Fin 1 → ℝ => c • x) volume S =
      volume ((fun x : Fin 1 → ℝ => c • x) ⁻¹' S) := hemb.map_apply volume S
  rw [← h1, map_volume_smul_fin1 hc, Measure.smul_apply, smul_eq_mul]

lemma isSpectral_preimage_smul {c : ℝ} (hc : 0 < c) {Ω : Set (Fin 1 → ℝ)}
    (hspec : isSpectral Ω) : isSpectral ((fun x : Fin 1 → ℝ => c • x) ⁻¹' Ω) := by
  have hcne : c ≠ 0 := hc.ne'
  set Ω' : Set (Fin 1 → ℝ) := (fun x : Fin 1 → ℝ => c • x) ⁻¹' Ω
  obtain ⟨Λ, hmeas, hpos, hfin, horth, hspan⟩ := hspec
  have hemb : MeasurableEmbedding (fun x : Fin 1 → ℝ => c • x) :=
    (Homeomorph.smulOfNeZero c hcne).measurableEmbedding
  have hemb_inv : MeasurableEmbedding (fun y : Fin 1 → ℝ => c⁻¹ • y) :=
    (Homeomorph.smulOfNeZero c⁻¹ (inv_ne_zero hcne)).measurableEmbedding
  have hmap_res : Measure.map (fun x : Fin 1 → ℝ => c • x) (volume.restrict Ω') =
      ENNReal.ofReal c⁻¹ • volume.restrict Ω := by
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, Measure.restrict_apply (hemb.measurable hs),
      Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul,
      ← Set.preimage_inter, volume_preimage_smul_fin1 hc]
  have hpre_inv : (fun y : Fin 1 → ℝ => c⁻¹ • y) ⁻¹' Ω' = Ω := by
    ext y
    simp [Ω', smul_inv_smul₀ hcne]
  have hmap_res_inv : Measure.map (fun y : Fin 1 → ℝ => c⁻¹ • y) (volume.restrict Ω) =
      ENNReal.ofReal c • volume.restrict Ω' := by
    ext s hs
    rw [Measure.map_apply hemb_inv.measurable hs, Measure.restrict_apply (hemb_inv.measurable hs),
      Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul,
      ← hpre_inv, ← Set.preimage_inter, volume_preimage_smul_fin1 (inv_pos.2 hc), inv_inv]
  have hmeas' : NullMeasurableSet Ω' volume := by
    have hmp : Measure.QuasiMeasurePreserving (fun x : Fin 1 → ℝ => c • x) volume volume := by
      refine ⟨hemb.measurable, ?_⟩
      rw [map_volume_smul_fin1 hc]
      exact Measure.AbsolutelyContinuous.rfl.smul_left _
    exact hmeas.preimage hmp
  have hvol' : volume Ω' = ENNReal.ofReal c⁻¹ * volume Ω := volume_preimage_smul_fin1 hc Ω
  have hpos' : 0 < volume Ω' := by
    rw [hvol']
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne' hpos.ne'
  have hfin' : volume Ω' ≠ ⊤ := by
    rw [hvol']
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  refine ⟨(fun ξ : Fin 1 → ℝ => c • ξ) '' Λ, hmeas', hpos', hfin', ?_, ?_⟩
  · rintro _ ⟨ξ₁, hξ₁, rfl⟩ _ ⟨ξ₂, hξ₂, rfl⟩ hne
    have hne' : ξ₁ ≠ ξ₂ := fun h => hne (by rw [h])
    dsimp only
    rw [inner_toLp_eq]
    have hpt : ∀ x : Fin 1 → ℝ,
        conj (exponentialCharacter (c • ξ₁) x) * exponentialCharacter (c • ξ₂) x =
          conj (exponentialCharacter ξ₁ (c • x)) * exponentialCharacter ξ₂ (c • x) := by
      intro x
      simp only [ec1_eq, Pi.smul_apply, smul_eq_mul]
      congr 3 <;> (push_cast; ring)
    simp_rw [hpt]
    have hmeas_f : AEStronglyMeasurable
        (fun y : Fin 1 → ℝ => conj (exponentialCharacter ξ₁ y) * exponentialCharacter ξ₂ y)
        (Measure.map (fun x : Fin 1 → ℝ => c • x) (volume.restrict Ω')) := by
      have hc1 : Continuous (fun y : Fin 1 → ℝ =>
          conj (exponentialCharacter ξ₁ y) * exponentialCharacter ξ₂ y) :=
        (Complex.continuous_conj.comp (continuous_exponentialCharacter ξ₁)).mul
          (continuous_exponentialCharacter ξ₂)
      exact hc1.aestronglyMeasurable
    have hint := integral_map hemb.measurable.aemeasurable hmeas_f
    rw [hmap_res, integral_smul_measure] at hint
    rw [← hint]
    have h0 := horth ξ₁ hξ₁ ξ₂ hξ₂ hne'
    dsimp only at h0
    rw [inner_toLp_eq] at h0
    rw [h0, smul_zero]
  · rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff] at hspan ⊢
    intro g hg
    rw [Submodule.mem_orthogonal] at hg
    have hg_mem : MemLp (g : (Fin 1 → ℝ) → ℂ) 2 (volume.restrict Ω') := Lp.memLp g
    have hqmp : Measure.QuasiMeasurePreserving (fun y : Fin 1 → ℝ => c⁻¹ • y)
        (volume.restrict Ω) (volume.restrict Ω') := by
      refine ⟨hemb_inv.measurable, ?_⟩
      rw [hmap_res_inv]
      exact Measure.AbsolutelyContinuous.rfl.smul_left _
    have hg_map : MemLp (fun y : Fin 1 → ℝ => g (c⁻¹ • y)) 2
        (Measure.map (fun x : Fin 1 → ℝ => c • x) (volume.restrict Ω')) := by
      rw [memLp_map_measure_iff]
      · convert hg_mem using 1
        funext x
        simp [inv_smul_smul₀ hcne]
      · rw [hmap_res]
        exact (hg_mem.1.comp_quasiMeasurePreserving hqmp).smul_measure _
      · exact hemb.measurable.aemeasurable
    rw [hmap_res] at hg_map
    have hg_Ω : MemLp (fun y : Fin 1 → ℝ => g (c⁻¹ • y)) 2 (volume.restrict Ω) := by
      have hne_c : ENNReal.ofReal c⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
      have hsm := hg_map.smul_measure (c := (ENNReal.ofReal c⁻¹)⁻¹) (ENNReal.inv_ne_top.2 hne_c)
      rwa [smul_smul, ENNReal.inv_mul_cancel hne_c ENNReal.ofReal_ne_top, one_smul] at hsm
    set g₀ : Lp ℂ 2 (volume.restrict Ω) := hg_Ω.toLp (fun y : Fin 1 → ℝ => g (c⁻¹ • y)) with hg₀
    have hmem : g₀ ∈ (Submodule.span ℂ (Set.range fun ξ : Λ =>
        (exponentialCharacter_memLp hfin ξ.1).toLp (exponentialCharacter ξ.1)))ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨ξ, rfl⟩
        rw [inner_toLp_eq]
        have h2 := hg _ (Submodule.subset_span ⟨⟨c • ξ.1, ξ.1, ξ.2, rfl⟩, rfl⟩)
        dsimp only at h2
        rw [← Lp.toLp_coeFn g hg_mem, inner_toLp_eq] at h2
        have hmeas_f : AEStronglyMeasurable
            (fun y : Fin 1 → ℝ => conj (exponentialCharacter ξ.1 y) * g (c⁻¹ • y))
            (Measure.map (fun x : Fin 1 → ℝ => c • x) (volume.restrict Ω')) := by
          rw [hmap_res]
          exact ((Complex.continuous_conj.comp
            (continuous_exponentialCharacter ξ.1)).aestronglyMeasurable.mul hg_Ω.1).smul_measure _
        have hint := integral_map hemb.measurable.aemeasurable hmeas_f
        rw [hmap_res, integral_smul_measure] at hint
        have hpt : (fun x : Fin 1 → ℝ => conj (exponentialCharacter ξ.1 (c • x)) * g (c⁻¹ • (c • x))) =
            fun x : Fin 1 → ℝ => conj (exponentialCharacter (c • ξ.1) x) * g x := by
          funext x
          rw [inv_smul_smul₀ hcne]
          congr 1
          simp only [ec1_eq, Pi.smul_apply, smul_eq_mul]
          congr 2
          push_cast
          ring
        rw [hpt, h2] at hint
        have hinv_ne : (ENNReal.ofReal c⁻¹).toReal ≠ 0 := by
          rw [ENNReal.toReal_ofReal (inv_pos.2 hc).le]
          exact (inv_pos.2 hc).ne'
        exact (smul_eq_zero.1 hint).resolve_left hinv_ne
      · simp
      · intro u v _ _ hu hv; rw [inner_add_left, hu, hv, add_zero]
      · intro a u _ hu; rw [inner_smul_left, hu, mul_zero]
    have hg0_zero : g₀ = 0 := hspan g₀ hmem
    have hae0 : (fun y : Fin 1 → ℝ => g (c⁻¹ • y)) =ᵐ[volume.restrict Ω] 0 := by
      have := hg_Ω.coeFn_toLp
      rw [← hg₀, hg0_zero] at this
      exact this.symm.trans (Lp.coeFn_zero _ _ _)
    rw [Lp.eq_zero_iff_ae_eq_zero, Filter.EventuallyEq, ae_iff]
    have hnull0 : (volume.restrict Ω) {y : Fin 1 → ℝ | g (c⁻¹ • y) ≠ 0} = 0 := by
      simpa [Filter.EventuallyEq, ae_iff] using hae0
    have hmap_null : (Measure.map (fun y : Fin 1 → ℝ => c⁻¹ • y) (volume.restrict Ω))
        {x : Fin 1 → ℝ | (g : (Fin 1 → ℝ) → ℂ) x ≠ 0} = 0 := by
      rw [hemb_inv.map_apply]
      exact hnull0
    rw [hmap_res_inv, Measure.smul_apply, smul_eq_mul] at hmap_null
    exact (mul_eq_zero.1 hmap_null).resolve_left (ENNReal.ofReal_pos.2 hc).ne'

lemma tilesByTranslation_preimage_smul {c : ℝ} (hc : 0 < c) {Ω : Set (Fin 1 → ℝ)}
    (htile : tilesByTranslation Ω) :
    tilesByTranslation ((fun x : Fin 1 → ℝ => c • x) ⁻¹' Ω) := by
  have hcne : c ≠ 0 := hc.ne'
  obtain ⟨T, hTc, hcov, hdisj⟩ := htile
  refine ⟨(fun t : Fin 1 → ℝ => c⁻¹ • t) '' T, hTc.image _, ?_, ?_⟩
  · have hset : Set.univ \ (⋃ t ∈ (fun t : Fin 1 → ℝ => c⁻¹ • t) '' T,
        translateSet ((fun x : Fin 1 → ℝ => c • x) ⁻¹' Ω) t) =
        (fun x : Fin 1 → ℝ => c • x) ⁻¹' (Set.univ \ (⋃ t ∈ T, translateSet Ω t)) := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_univ, true_and, Set.mem_iUnion, Set.mem_image,
        Set.mem_preimage, translateSet, Set.mem_ofPred_eq]
      refine not_congr ⟨?_, ?_⟩
      · rintro ⟨_, ⟨t, ht, rfl⟩, hx⟩
        refine ⟨t, ht, ?_⟩
        rwa [smul_sub, smul_inv_smul₀ hcne] at hx
      · rintro ⟨t, ht, hx⟩
        refine ⟨c⁻¹ • t, ⟨t, ht, rfl⟩, ?_⟩
        rwa [smul_sub, smul_inv_smul₀ hcne]
    rw [hset, volume_preimage_smul_fin1 hc, hcov, mul_zero]
  · intro t₁ t₂ ht₁ ht₂ hne
    obtain ⟨s₁, hs₁, rfl⟩ := ht₁
    obtain ⟨s₂, hs₂, rfl⟩ := ht₂
    have hne' : s₁ ≠ s₂ := fun h => hne (by rw [h])
    have hset : translateSet ((fun x : Fin 1 → ℝ => c • x) ⁻¹' Ω) (c⁻¹ • s₁) ∩
        translateSet ((fun x : Fin 1 → ℝ => c • x) ⁻¹' Ω) (c⁻¹ • s₂) =
        (fun x : Fin 1 → ℝ => c • x) ⁻¹' (translateSet Ω s₁ ∩ translateSet Ω s₂) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, translateSet, Set.mem_ofPred_eq,
        smul_sub, smul_inv_smul₀ hcne]
    rw [hset, volume_preimage_smul_fin1 hc, hdisj hs₁ hs₂ hne', mul_zero]

lemma unit_measure_reduction
    (hunit : ∀ Ω : Set (Fin 1 → ℝ),
      Bornology.IsBounded Ω → MeasurableSet Ω → volume Ω = 1 →
      (isSpectral Ω ↔ tilesByTranslation Ω)) :
    Fuglede.FugledeConjectureFor 1 := by
  intro Ω hbdd hmeas hpos
  have hlt_top : volume Ω < ⊤ := hbdd.measure_lt_top
  set c : ℝ := (volume Ω).toReal
  have hc : 0 < c := ENNReal.toReal_pos hpos.ne' hlt_top.ne
  set Ω₁ : Set (Fin 1 → ℝ) := (fun x : Fin 1 → ℝ => c • x) ⁻¹' Ω
  have hbdd₁ : Bornology.IsBounded Ω₁ := by
    have heq : Ω₁ = (fun y : Fin 1 → ℝ => c⁻¹ • y) '' Ω := by
      ext x
      simp only [Ω₁, Set.mem_preimage, Set.mem_image]
      exact ⟨fun hx => ⟨c • x, hx, inv_smul_smul₀ hc.ne' x⟩,
        by rintro ⟨y, hy, rfl⟩; rwa [smul_inv_smul₀ hc.ne']⟩
    rw [heq]
    exact (lipschitzWith_smul c⁻¹).isBounded_image hbdd
  have hmeas₁ : MeasurableSet Ω₁ := hmeas.preimage (continuous_const_smul c).measurable
  have hvol₁ : volume Ω₁ = 1 := by
    rw [volume_preimage_smul_fin1 hc, ← ENNReal.ofReal_toReal hlt_top.ne,
      ← ENNReal.ofReal_mul (inv_pos.2 hc).le, inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
  have hiff := hunit Ω₁ hbdd₁ hmeas₁ hvol₁
  have hΩ_eq : (fun x : Fin 1 → ℝ => c⁻¹ • x) ⁻¹' Ω₁ = Ω := by
    ext x
    simp [Ω₁, smul_inv_smul₀ hc.ne']
  constructor
  · intro hs
    have ht₁ := hiff.1 (isSpectral_preimage_smul hc hs)
    have ht := tilesByTranslation_preimage_smul (inv_pos.2 hc) ht₁
    rwa [hΩ_eq] at ht
  · intro ht
    have hs₁ := hiff.2 (tilesByTranslation_preimage_smul hc ht)
    have hs := isSpectral_preimage_smul (inv_pos.2 hc) hs₁
    rwa [hΩ_eq] at hs

/- Part 2: Dutkay-Jorgensen / Pedersen spectral synthesis (H1 + H2 -> Tiling => Spectral) -/

lemma linalg_fin {L : ℕ} (B : Finset ℤ) (Γ : Finset (ZMod L))
    (hcard : Γ.card = B.card)
    (horth : ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ →
      ∑ b ∈ B, Complex.exp (2 * Real.pi * Complex.I *
        (((γ₁.val : ℝ) - (γ₂.val : ℝ)) * (b : ℝ) / (L : ℝ))) = 0)
    (w : ℤ → ℂ)
    (hw : ∀ γ ∈ Γ, ∑ b ∈ B,
      Complex.exp (-(2 * Real.pi * Complex.I * ((γ.val : ℝ) * (b : ℝ) / (L : ℝ)))) * w b = 0) :
    ∀ b ∈ B, w b = 0 := by
  classical
  rcases B.eq_empty_or_nonempty with hB | hB
  · simp [hB]
  have hc : (B.card : ℂ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  let M : Matrix Γ B ℂ := fun γ b =>
    (B.card : ℂ)⁻¹ * Complex.exp (-(2 * Real.pi * Complex.I * ((γ.1.val : ℝ) * (b.1 : ℝ) / (L : ℝ))))
  let N : Matrix B Γ ℂ := fun b γ =>
    Complex.exp (2 * Real.pi * Complex.I * ((γ.1.val : ℝ) * (b.1 : ℝ) / (L : ℝ)))
  have hMN : M * N = 1 := by
    ext γ₁ γ₂
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [M, N]
    have hterm : ∀ b : B,
        (B.card : ℂ)⁻¹ *
          Complex.exp (-(2 * Real.pi * Complex.I * ((γ₁.1.val : ℝ) * (b.1 : ℝ) / (L : ℝ)))) *
          Complex.exp (2 * Real.pi * Complex.I * ((γ₂.1.val : ℝ) * (b.1 : ℝ) / (L : ℝ))) =
        (B.card : ℂ)⁻¹ *
          Complex.exp (2 * Real.pi * Complex.I *
            (((γ₂.1.val : ℝ) - (γ₁.1.val : ℝ)) * (b.1 : ℝ) / (L : ℝ))) := by
      intro b
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, Finset.sum_coe_sort B (fun b => Complex.exp (2 * Real.pi * Complex.I *
      (((γ₂.1.val : ℝ) - (γ₁.1.val : ℝ)) * (b : ℝ) / (L : ℝ))))]
    split_ifs with h
    · subst h
      simp [hc]
    · rw [horth γ₂.1 γ₂.2 γ₁.1 γ₁.2 (fun h' => h (Subtype.ext h'.symm)), mul_zero]
  have e : Γ ≃ B := Fintype.equivOfCardEq (by simp [hcard])
  have hNM : N * M = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hMN
  have hMw : Matrix.mulVec M (fun b : B => w b.1) = 0 := by
    funext γ
    rw [Matrix.mulVec, Pi.zero_apply]
    simp only [dotProduct, M]
    have hrew : (∑ i : B, (B.card : ℂ)⁻¹ *
          Complex.exp (-(2 * Real.pi * Complex.I * ((γ.1.val : ℝ) * (i.1 : ℝ) / (L : ℝ)))) * w i.1) =
        (B.card : ℂ)⁻¹ * ∑ b ∈ B,
          Complex.exp (-(2 * Real.pi * Complex.I * ((γ.1.val : ℝ) * (b : ℝ) / (L : ℝ)))) * w b := by
      rw [← Finset.sum_coe_sort B, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
    rw [hrew, hw γ.1 γ.2, mul_zero]
  have hw0 : (fun b : B => w b.1) = 0 := by
    have := congrArg (Matrix.mulVec N) hMw
    simp only [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this
  intro b hb
  exact congrFun hw0 ⟨b, hb⟩

lemma exp_zmod_val_eq {L : ℕ} (hL : 0 < L) (γ₁ γ₂ : ZMod L) (b : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I *
      (((γ₁.val : ℝ) - (γ₂.val : ℝ)) * (((b : ZMod L).val : ℝ)) / (L : ℝ))) =
    Complex.exp (2 * Real.pi * Complex.I *
      (((γ₁.val : ℝ) - (γ₂.val : ℝ)) * (b : ℝ) / (L : ℝ))) := by
  have : NeZero L := ⟨Nat.ne_of_gt hL⟩
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hdvd : (L : ℤ) ∣ (((b : ZMod L).val : ℤ) - b) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp
  obtain ⟨q, hq⟩ := hdvd
  have hvalZ : ((b : ZMod L).val : ℤ) = b + (L : ℤ) * q := by linarith
  have hvalC : (((b : ZMod L).val : ℕ) : ℂ) = (b : ℂ) + (L : ℂ) * (q : ℂ) := by
    exact_mod_cast hvalZ
  have hdiff : 2 * Real.pi * Complex.I *
      (((γ₁.val : ℝ) - (γ₂.val : ℝ)) * (((b : ZMod L).val : ℝ)) / (L : ℝ)) =
    2 * Real.pi * Complex.I *
      (((γ₁.val : ℝ) - (γ₂.val : ℝ)) * (b : ℝ) / (L : ℝ)) +
    2 * Real.pi * Complex.I * ((((γ₁.val : ℤ) - (γ₂.val : ℤ)) * q : ℤ) : ℂ) := by
    push_cast
    rw [hvalC]
    field_simp [hLC]
  rw [hdiff, Complex.exp_add, exp_two_pi_I_int, mul_one]

lemma continuous_exp_mul_ofReal (a b : ℂ) :
    Continuous (fun s : ℝ => Complex.exp (a * (s : ℂ) + b)) :=
  Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).add continuous_const)

set_option maxHeartbeats 800000 in
lemma tiling_to_spectral_unit (h1 : H1) (h2 : H2)
    (Ω : Set (Fin 1 → ℝ)) (hbdd : Bornology.IsBounded Ω) (hmeas : MeasurableSet Ω)
    (hvol : volume Ω = 1) (htile : tilesByTranslation Ω) :
    isSpectral Ω := by
  classical
  obtain ⟨k, L, A, ℬ, T, hk, hL, hBtile, hTmeas, hTdisj, hTcov, hΩdiff⟩ :=
    h1 Ω hbdd hmeas hvol htile
  have : NeZero L := ⟨Nat.ne_of_gt hL⟩
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLne : (L : ℝ) ≠ 0 := hLR.ne'
  have hℬne : ℬ.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.sdiff_empty] at hTcov
    rw [Real.volume_Ico, sub_zero] at hTcov
    have hpos : 0 < ENNReal.ofReal (1 / (k : ℝ)) := ENNReal.ofReal_pos.2 (by positivity)
    exact hpos.ne' hTcov
  obtain ⟨B₀, hB₀⟩ := hℬne
  have hAne : A.Nonempty := by
    obtain ⟨p, _, _⟩ := (hBtile B₀ hB₀).2 0
    exact ⟨p.1.1, p.1.2⟩
  obtain ⟨a₀, ha₀⟩ := hAne
  have hBinj : ∀ B ∈ ℬ, Set.InjOn (fun b : ℤ => (b : ZMod L)) (B : Set ℤ) := by
    intro B hB b₁ hb₁ b₂ hb₂ heq
    obtain ⟨_, _, huniq⟩ := (hBtile B hB).2 (a₀ + (b₁ : ZMod L))
    have e1 := huniq (⟨a₀, ha₀⟩, ⟨b₁, hb₁⟩) rfl
    have e2 := huniq (⟨a₀, ha₀⟩, ⟨b₂, hb₂⟩) (by simp [heq])
    have e12 := e1.trans e2.symm
    exact congrArg (fun p : {a // a ∈ A} × {b // b ∈ B} => p.2.1) e12
  let ℬ' : Finset (Finset (ZMod L)) := ℬ.image (fun B => B.image (fun b : ℤ => (b : ZMod L)))
  have hℬ'tile : ∀ B' ∈ ℬ', ∀ z : ZMod L,
      ∃! p : {a // a ∈ A} × {b // b ∈ B'}, p.1.1 + p.2.1 = z := by
    intro B' hB' z
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hB'
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hsum, huniq⟩ := (hBtile B hB).2 z
    refine ⟨(⟨a, ha⟩, ⟨(b : ZMod L), Finset.mem_image_of_mem _ hb⟩), hsum, ?_⟩
    rintro ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hsum'
    obtain ⟨b'', hb'', rfl⟩ := Finset.mem_image.1 hb'
    have eqp := huniq (⟨a', ha'⟩, ⟨b'', hb''⟩) hsum'
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at eqp
    rcases eqp with ⟨rfl, rfl⟩
    rfl
  obtain ⟨Γ, hΓcard, hΓorth⟩ := h2 L hL A ℬ' hℬ'tile
  have hΓcard_k : Γ.card = k := by
    have h1 := hΓcard (B₀.image (fun b : ℤ => (b : ZMod L))) (Finset.mem_image_of_mem _ hB₀)
    rw [Finset.card_image_of_injOn (hBinj B₀ hB₀), (hBtile B₀ hB₀).1] at h1
    exact h1
  have hΓorthZ : ∀ B ∈ ℬ, ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ →
      ∑ b ∈ B, Complex.exp (2 * Real.pi * Complex.I *
        (((γ₁.val : ℝ) - (γ₂.val : ℝ)) * (b : ℝ) / (L : ℝ))) = 0 := by
    intro B hB γ₁ hγ₁ γ₂ hγ₂ hne
    have h0 := hΓorth (B.image (fun b : ℤ => (b : ZMod L)))
      (Finset.mem_image_of_mem _ hB) γ₁ hγ₁ γ₂ hγ₂ hne
    rw [Finset.sum_image (hBinj B hB)] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun b _ => (exp_zmod_val_eq hL γ₁ γ₂ b).symm
  let piece : (Σ _ : Finset ℤ, ℤ) → Set (Fin 1 → ℝ) :=
    fun p => {x : Fin 1 → ℝ | x 0 - (p.2 : ℝ) / (k : ℝ) ∈ T p.1}
  let Ω' : Set (Fin 1 → ℝ) :=
    ⋃ B ∈ ℬ, {x : Fin 1 → ℝ | ∃ t ∈ T B, ∃ b ∈ B, x 0 = t + (b : ℝ) / (k : ℝ)}
  have hΩ'_eq : Ω' = ⋃ p ∈ ℬ.sigma id, piece p := by
    ext x
    simp only [Ω', piece, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_sigma, id_eq]
    constructor
    · rintro ⟨B, hB, t, ht, b, hb, hx⟩
      refine ⟨⟨B, b⟩, ⟨hB, hb⟩, ?_⟩
      simpa [hx] using ht
    · rintro ⟨⟨B, b⟩, ⟨hB, hb⟩, hx⟩
      exact ⟨B, hB, x 0 - (b : ℝ) / (k : ℝ), hx, b, hb, by ring⟩
  have hpiece_meas : ∀ p ∈ ℬ.sigma id, MeasurableSet (piece p) := by
    intro p hp
    have hB : p.1 ∈ ℬ := (Finset.mem_sigma.1 hp).1
    exact (hTmeas p.1 hB).1.preimage ((measurable_pi_apply 0).sub measurable_const)
  have hpiece_disj : (ℬ.sigma id : Set (Σ _ : Finset ℤ, ℤ)).PairwiseDisjoint piece := by
    intro p₁ hp₁ p₂ hp₂ hne
    show Disjoint (piece p₁) (piece p₂)
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    have hB₁ : p₁.1 ∈ ℬ := (Finset.mem_sigma.1 (Finset.mem_coe.1 hp₁)).1
    have hB₂ : p₂.1 ∈ ℬ := (Finset.mem_sigma.1 (Finset.mem_coe.1 hp₂)).1
    have ht₁ : x 0 - (p₁.2 : ℝ) / (k : ℝ) ∈ Set.Ico 0 (1 / (k : ℝ)) := (hTmeas p₁.1 hB₁).2 hx₁
    have ht₂ : x 0 - (p₂.2 : ℝ) / (k : ℝ) ∈ Set.Ico 0 (1 / (k : ℝ)) := (hTmeas p₂.1 hB₂).2 hx₂
    have hb1 : (p₁.2 : ℝ) < (p₂.2 : ℝ) + 1 := by
      have h1a : (0 : ℝ) ≤ (k : ℝ) * (x 0 - (p₁.2 : ℝ) / (k : ℝ)) := mul_nonneg hkpos.le ht₁.1
      have h2b : (k : ℝ) * (x 0 - (p₂.2 : ℝ) / (k : ℝ)) < 1 := by
        have := mul_lt_mul_of_pos_left ht₂.2 hkpos
        rwa [mul_one_div_cancel hkne] at this
      have ha : (k : ℝ) * (x 0 - (p₁.2 : ℝ) / (k : ℝ)) = (k : ℝ) * x 0 - (p₁.2 : ℝ) := by
        field_simp [hkne]
      have hb : (k : ℝ) * (x 0 - (p₂.2 : ℝ) / (k : ℝ)) = (k : ℝ) * x 0 - (p₂.2 : ℝ) := by
        field_simp [hkne]
      linarith
    have hb2 : (p₂.2 : ℝ) < (p₁.2 : ℝ) + 1 := by
      have h2a : (0 : ℝ) ≤ (k : ℝ) * (x 0 - (p₂.2 : ℝ) / (k : ℝ)) := mul_nonneg hkpos.le ht₂.1
      have h1b : (k : ℝ) * (x 0 - (p₁.2 : ℝ) / (k : ℝ)) < 1 := by
        have := mul_lt_mul_of_pos_left ht₁.2 hkpos
        rwa [mul_one_div_cancel hkne] at this
      have ha : (k : ℝ) * (x 0 - (p₁.2 : ℝ) / (k : ℝ)) = (k : ℝ) * x 0 - (p₁.2 : ℝ) := by
        field_simp [hkne]
      have hb : (k : ℝ) * (x 0 - (p₂.2 : ℝ) / (k : ℝ)) = (k : ℝ) * x 0 - (p₂.2 : ℝ) := by
        field_simp [hkne]
      linarith
    have hb1Z : p₁.2 < p₂.2 + 1 := by exact_mod_cast hb1
    have hb2Z : p₂.2 < p₁.2 + 1 := by exact_mod_cast hb2
    have hbeq : p₁.2 = p₂.2 := by omega
    have hBeq : p₁.1 = p₂.1 := by
      by_contra hBne
      have hd := Set.disjoint_left.1 (hTdisj p₁.1 hB₁ p₂.1 hB₂ hBne)
      exact hd hx₁ (hbeq ▸ hx₂)
    exact hne (Sigma.ext hBeq (heq_of_eq hbeq))
  have hshift_emb : ∀ b : ℤ, MeasurableEmbedding
      (fun t : ℝ => (fun _ : Fin 1 => t + (b : ℝ) / (k : ℝ))) := fun b =>
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding.comp
      (MeasurableEquiv.addRight ((b : ℝ) / (k : ℝ))).measurableEmbedding
  have hshift_mp_vol : ∀ b : ℤ, MeasurePreserving
      (fun t : ℝ => (fun _ : Fin 1 => t + (b : ℝ) / (k : ℝ))) volume volume := fun b =>
    mp_funUnique_symm.comp (measurePreserving_add_right volume ((b : ℝ) / (k : ℝ)))
  have hshift_pre : ∀ (B : Finset ℤ) (b : ℤ),
      (fun t : ℝ => (fun _ : Fin 1 => t + (b : ℝ) / (k : ℝ))) ⁻¹' piece ⟨B, b⟩ = T B := by
    intro B b; ext t; simp [piece]
  have hshift_mp : ∀ (B : Finset ℤ) (b : ℤ), MeasurePreserving
      (fun t : ℝ => (fun _ : Fin 1 => t + (b : ℝ) / (k : ℝ)))
      (volume.restrict (T B)) (volume.restrict (piece ⟨B, b⟩)) := by
    intro B b
    have h := (hshift_mp_vol b).restrict_preimage_emb (hshift_emb b) (piece ⟨B, b⟩)
    rwa [hshift_pre B b] at h
  have hint_Ω' : ∀ (h : (Fin 1 → ℝ) → ℂ), IntegrableOn h Ω' →
      ∫ x in Ω', h x = ∑ B ∈ ℬ, ∑ b ∈ B, ∫ t in T B, h (fun _ => t + (b : ℝ) / (k : ℝ)) := by
    intro h hint
    rw [hΩ'_eq] at hint ⊢
    rw [integral_biUnion_finset (ℬ.sigma id) hpiece_meas hpiece_disj
      (fun p hp => hint.mono_set (Set.subset_biUnion_of_mem (u := piece) hp))]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun b _ => ?_
    have hm := (hshift_mp_vol b).setIntegral_preimage_emb (hshift_emb b) h (piece ⟨B, b⟩)
    rw [hshift_pre B b] at hm
    exact hm.symm
  have hvol_Ω' : volume Ω' = 1 := by
    have hae := ae_eq_set_of_symmDiff_null hΩdiff
    rw [← measure_congr hae, hvol]
  have hΩ'_meas : MeasurableSet Ω' := by
    rw [hΩ'_eq]
    exact MeasurableSet.biUnion (ℬ.sigma id).countable_toSet hpiece_meas
  have hΩ'_fin : volume Ω' ≠ ⊤ := by rw [hvol_Ω']; exact ENNReal.one_ne_top
  have hΩ'_pos : 0 < volume Ω' := by rw [hvol_Ω']; exact zero_lt_one
  have hTunion_ae : (⋃ B ∈ ℬ, T B) =ᵐ[volume] Set.Ico (0 : ℝ) (1 / (k : ℝ)) := by
    apply ae_eq_set_of_symmDiff_null
    have hsub : (⋃ B ∈ ℬ, T B) ⊆ Set.Ico (0 : ℝ) (1 / (k : ℝ)) :=
      Set.iUnion₂_subset fun B hB => (hTmeas B hB).2
    have hsd : symmDiff (⋃ B ∈ ℬ, T B) (Set.Ico (0 : ℝ) (1 / (k : ℝ))) =
        Set.Ico (0 : ℝ) (1 / (k : ℝ)) \ ⋃ B ∈ ℬ, T B := by
      ext x
      simp only [Set.mem_symmDiff]
      exact ⟨fun h => h.elim (fun ⟨hx, hnx⟩ => absurd (hsub hx) hnx) id, Or.inr⟩
    rw [hsd]
    exact hTcov
  have hspec_Ω' : isSpectral Ω' := by
    have hfm : IsFiniteMeasure (volume.restrict Ω') := isFiniteMeasure_restrict.2 hΩ'_fin
    let Λ : Set (Fin 1 → ℝ) :=
      {ξ : Fin 1 → ℝ | ∃ γ ∈ Γ, ∃ n : ℤ, ξ 0 = (k : ℝ) * ((γ.val : ℝ) / (L : ℝ) + (n : ℝ))}
    refine ⟨Λ, hΩ'_meas.nullMeasurableSet, hΩ'_pos, hΩ'_fin, ?_, ?_⟩
    · rintro ξ₁ ⟨γ₁, hγ₁, n₁, hξ₁⟩ ξ₂ ⟨γ₂, hγ₂, n₂, hξ₂⟩ hne
      dsimp only
      rw [inner_toLp_eq]
      have hpt : ∀ x : Fin 1 → ℝ,
          conj (exponentialCharacter ξ₁ x) * exponentialCharacter ξ₂ x =
            exponentialCharacter (ξ₂ - ξ₁) x := by
        intro x
        rw [ec1_conj, ← ec1_add_left]
        congr 1; abel
      simp_rw [hpt]
      rw [hint_Ω' _ ((exponentialCharacter_memLp hΩ'_fin _).integrable one_le_two)]
      have hfactor : ∀ B ∈ ℬ,
          (∑ b ∈ B, ∫ t in T B, exponentialCharacter (ξ₂ - ξ₁) (fun _ => t + (b : ℝ) / (k : ℝ))) =
          (∫ t in T B, Complex.exp (2 * Real.pi * Complex.I * ((ξ₂ 0 - ξ₁ 0) * t))) *
          (∑ b ∈ B, Complex.exp (2 * Real.pi * Complex.I *
            (((γ₂.val : ℝ) - (γ₁.val : ℝ)) * (b : ℝ) / (L : ℝ)))) := by
        intro B _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        have hsplit : ∀ t : ℝ,
            exponentialCharacter (ξ₂ - ξ₁) (fun _ => t + (b : ℝ) / (k : ℝ)) =
            Complex.exp (2 * Real.pi * Complex.I * ((ξ₂ 0 - ξ₁ 0) * t)) *
            Complex.exp (2 * Real.pi * Complex.I *
              (((γ₂.val : ℝ) - (γ₁.val : ℝ)) * (b : ℝ) / (L : ℝ))) := by
          intro t
          rw [ec1_eq, ← Complex.exp_add]
          have h1 : (ξ₂ - ξ₁) 0 * (t + (b : ℝ) / (k : ℝ)) =
              (ξ₂ 0 - ξ₁ 0) * t +
              ((γ₂.val : ℝ) - (γ₁.val : ℝ)) * (b : ℝ) / (L : ℝ) +
              (((n₂ - n₁) * b : ℤ) : ℝ) := by
            simp only [Pi.sub_apply, hξ₁, hξ₂]
            push_cast
            field_simp [hkne, hLne]
            ring
          rw [← Complex.ofReal_mul, h1]
          have h2 : 2 * Real.pi * Complex.I *
              (((ξ₂ 0 - ξ₁ 0) * t +
                ((γ₂.val : ℝ) - (γ₁.val : ℝ)) * (b : ℝ) / (L : ℝ) +
                (((n₂ - n₁) * b : ℤ) : ℝ) : ℝ) : ℂ) =
              (2 * Real.pi * Complex.I * ((ξ₂ 0 - ξ₁ 0) * t) +
               2 * Real.pi * Complex.I * (((γ₂.val : ℝ) - (γ₁.val : ℝ)) * (b : ℝ) / (L : ℝ))) +
              2 * Real.pi * Complex.I * (((n₂ - n₁) * b : ℤ) : ℂ) := by
            push_cast; ring
          rw [h2, Complex.exp_add, exp_two_pi_I_int, mul_one]
        simp_rw [hsplit]
        exact integral_mul_const _ _
      rw [Finset.sum_congr rfl hfactor]
      by_cases hγ : γ₁ = γ₂
      · subst hγ
        have hn : n₁ ≠ n₂ := by
          intro h
          apply hne
          ext i
          fin_cases i
          change ξ₁ 0 = ξ₂ 0
          rw [hξ₁, hξ₂, h]
        have hξdiff : ξ₂ 0 - ξ₁ 0 = (k : ℝ) * ((n₂ - n₁ : ℤ) : ℝ) := by
          rw [hξ₁, hξ₂]; push_cast; ring
        have hsum_eq : ∀ B ∈ ℬ,
            (∫ t in T B, Complex.exp (2 * Real.pi * Complex.I * ((ξ₂ 0 - ξ₁ 0) * t))) *
            (∑ b ∈ B, Complex.exp (2 * Real.pi * Complex.I *
              (((γ₁.val : ℝ) - (γ₁.val : ℝ)) * (b : ℝ) / (L : ℝ)))) =
            (k : ℂ) * ∫ t in T B, Complex.exp (2 * Real.pi * Complex.I *
              ((k : ℝ) * ((n₂ - n₁ : ℤ) : ℝ) * t)) := by
          intro B hB
          have hξdiff' : ((ξ₂ 0 : ℂ) - (ξ₁ 0 : ℂ)) = ((k : ℝ) : ℂ) * (((n₂ - n₁ : ℤ) : ℝ) : ℂ) := by
            exact_mod_cast hξdiff
          simp only [sub_self, zero_mul, zero_div, mul_zero,
            Complex.exp_zero, Finset.sum_const, nsmul_eq_mul, mul_one, (hBtile B hB).1, hξdiff']
          ring
        rw [Finset.sum_congr rfl hsum_eq, ← Finset.mul_sum]
        have hint_Ico : IntegrableOn
            (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * ((n₂ - n₁ : ℤ) : ℝ) * t)))
            (Set.Ico (0 : ℝ) (1 / (k : ℝ))) := by
          have hc : Continuous (fun t : ℝ =>
              Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * ((n₂ - n₁ : ℤ) : ℝ) * t))) := by
            continuity
          exact hc.continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Set.Ico_subset_Icc_self
        have hsum_int : (∑ B ∈ ℬ, ∫ t in T B,
              Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * ((n₂ - n₁ : ℤ) : ℝ) * t))) =
            ∫ t in ⋃ B ∈ ℬ, T B,
              Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * ((n₂ - n₁ : ℤ) : ℝ) * t)) := by
          symm
          exact integral_biUnion_finset ℬ (fun B hB => (hTmeas B hB).1)
            (fun B₁ hB₁ B₂ hB₂ hBne => hTdisj B₁ hB₁ B₂ hB₂ hBne)
            (fun B hB => hint_Ico.mono_set (hTmeas B hB).2)
        rw [hsum_int, setIntegral_congr_set hTunion_ae,
          integral_Ico_div_exp k hk (n₂ - n₁) (sub_ne_zero.2 hn.symm), mul_zero]
      · have hzero : ∀ B ∈ ℬ,
            (∫ t in T B, Complex.exp (2 * Real.pi * Complex.I * ((ξ₂ 0 - ξ₁ 0) * t))) *
            (∑ b ∈ B, Complex.exp (2 * Real.pi * Complex.I *
              (((γ₂.val : ℝ) - (γ₁.val : ℝ)) * (b : ℝ) / (L : ℝ)))) = 0 := by
          intro B hB
          rw [hΓorthZ B hB γ₂ hγ₂ γ₁ hγ₁ (Ne.symm hγ), mul_zero]
        rw [Finset.sum_eq_zero hzero]
    · rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
      intro g hg
      rw [Submodule.mem_orthogonal] at hg
      have hgm : MemLp (g : (Fin 1 → ℝ) → ℂ) 2 (volume.restrict Ω') := Lp.memLp g
      have hg' : ∀ γ ∈ Γ, ∀ n : ℤ,
          ∫ x in Ω', conj (exponentialCharacter
            (fun _ : Fin 1 => (k : ℝ) * ((γ.val : ℝ) / (L : ℝ) + (n : ℝ))) x) * g x = 0 := by
        intro γ hγ n
        set ξ : Fin 1 → ℝ := fun _ => (k : ℝ) * ((γ.val : ℝ) / (L : ℝ) + (n : ℝ))
        have hξ : ξ ∈ Λ := ⟨γ, hγ, n, rfl⟩
        have h0 := hg _ (Submodule.subset_span ⟨⟨ξ, hξ⟩, rfl⟩)
        dsimp only at h0
        rw [← Lp.toLp_coeFn g hgm, inner_toLp_eq] at h0
        exact h0
      have hg_shift_memLp : ∀ B ∈ ℬ, ∀ b ∈ B,
          MemLp (fun t : ℝ => (g : (Fin 1 → ℝ) → ℂ) (fun _ => t + (b : ℝ) / (k : ℝ)))
            2 (volume.restrict (T B)) := by
        intro B hB b hb
        have hsub : piece ⟨B, b⟩ ⊆ Ω' := by
          rw [hΩ'_eq]
          exact Set.subset_biUnion_of_mem (u := piece) (Finset.mem_sigma.2 ⟨hB, hb⟩)
        exact (hgm.mono_measure (Measure.restrict_mono hsub le_rfl)).comp_measurePreserving
          (hshift_mp B b)
      have hkey : ∀ γ ∈ Γ,
          (fun t : ℝ => ∑ B ∈ ℬ, (T B).indicator
            (fun s => ∑ b ∈ B,
              Complex.exp (-(2 * Real.pi * Complex.I *
                ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ))))) *
              g (fun _ => s + (b : ℝ) / (k : ℝ))) t)
          =ᵐ[volume.restrict (Set.Ico (0 : ℝ) (1 / (k : ℝ)))] 0 := by
        intro γ hγ
        apply fourier_complete_Ico_div k hk
        · apply memLp_finsetSum ℬ
          intro B hB
          have hinner : MemLp
              (fun s : ℝ => ∑ b ∈ B,
                Complex.exp (-(2 * Real.pi * Complex.I *
                  ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ))))) *
                g (fun _ => s + (b : ℝ) / (k : ℝ)))
              2 (volume.restrict (T B)) := by
            apply memLp_finsetSum B
            intro b hb
            have hgb := hg_shift_memLp B hB b hb
            have hcont : Continuous (fun s : ℝ =>
                Complex.exp (-(2 * Real.pi * Complex.I *
                  ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ)))))) := by
              have hrew : (fun s : ℝ =>
                  Complex.exp (-(2 * Real.pi * Complex.I *
                    ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ)))))) =
                  fun s : ℝ => Complex.exp ((-(2 * Real.pi * Complex.I * ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ))))) * (s : ℂ) +
                    (-(2 * Real.pi * Complex.I * ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * ((b : ℝ) / (k : ℝ)))))) := by
                funext s; congr 1; push_cast; ring
              rw [hrew]
              exact continuous_exp_mul_ofReal _ _
            have hnorm : ∀ s : ℝ,
                ‖Complex.exp (-(2 * Real.pi * Complex.I *
                  ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ)))))‖ = 1 := by
              intro s
              have he : -(2 * Real.pi * Complex.I *
                  ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ)))) =
                ((-(2 * Real.pi * ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ)))) : ℝ) : ℂ) *
                Complex.I := by
                push_cast; ring
              rw [he, Complex.norm_exp_ofReal_mul_I]
            exact hgb.congr_norm (hcont.aestronglyMeasurable.mul hgb.1)
              (ae_of_all _ fun s => by simp only [norm_mul, hnorm s, one_mul])
          have hmem_ind : MemLp
              ((T B).indicator (fun s : ℝ => ∑ b ∈ B,
                Complex.exp (-(2 * Real.pi * Complex.I *
                  ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ))))) *
                g (fun _ => s + (b : ℝ) / (k : ℝ))))
              2 (volume.restrict (Set.Ico (0 : ℝ) (1 / (k : ℝ)))) := by
            rw [memLp_indicator_iff_restrict (hTmeas B hB).1,
              Measure.restrict_restrict_of_subset (hTmeas B hB).2]
            exact hinner
          exact hmem_ind
        · intro n
          have hterm_int : ∀ B ∈ ℬ,
              IntegrableOn
                (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * t))) *
                  (T B).indicator (fun s => ∑ b ∈ B,
                    Complex.exp (-(2 * Real.pi * Complex.I *
                      ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ))))) *
                    g (fun _ => s + (b : ℝ) / (k : ℝ))) t)
                (Set.Ico (0 : ℝ) (1 / (k : ℝ))) := by
            intro B hB
            have hTfin : IsFiniteMeasure (volume.restrict (T B)) :=
              isFiniteMeasure_restrict.2
                (ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
                  (measure_mono (hTmeas B hB).2))
            have hind_eq : (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * t))) *
                  (T B).indicator (fun s => ∑ b ∈ B,
                    Complex.exp (-(2 * Real.pi * Complex.I *
                      ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ))))) *
                    g (fun _ => s + (b : ℝ) / (k : ℝ))) t) =
                (T B).indicator (fun s => Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * s))) *
                  ∑ b ∈ B,
                    Complex.exp (-(2 * Real.pi * Complex.I *
                      ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ))))) *
                    g (fun _ => s + (b : ℝ) / (k : ℝ))) := by
              funext t; by_cases ht : t ∈ T B <;> simp [ht]
            rw [hind_eq, IntegrableOn, integrable_indicator_iff (hTmeas B hB).1, IntegrableOn,
              Measure.restrict_restrict_of_subset (hTmeas B hB).2]
            have hmem1 : MemLp (fun s : ℝ =>
                Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * s))) *
                ∑ b ∈ B,
                  Complex.exp (-(2 * Real.pi * Complex.I *
                    ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ))))) *
                  g (fun _ => s + (b : ℝ) / (k : ℝ))) 2 (volume.restrict (T B)) := by
              have hinner : MemLp (fun s : ℝ => ∑ b ∈ B,
                  Complex.exp (-(2 * Real.pi * Complex.I *
                    ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ))))) *
                  g (fun _ => s + (b : ℝ) / (k : ℝ))) 2 (volume.restrict (T B)) := by
                apply memLp_finsetSum B
                intro b hb
                have hgb := hg_shift_memLp B hB b hb
                have hcont : Continuous (fun s : ℝ =>
                    Complex.exp (-(2 * Real.pi * Complex.I *
                      ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ)))))) := by
                  have hrew : (fun s : ℝ =>
                      Complex.exp (-(2 * Real.pi * Complex.I *
                        ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ)))))) =
                      fun s : ℝ => Complex.exp ((-(2 * Real.pi * Complex.I * ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ))))) * (s : ℂ) +
                        (-(2 * Real.pi * Complex.I * ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * ((b : ℝ) / (k : ℝ)))))) := by
                    funext s; congr 1; push_cast; ring
                  rw [hrew]
                  exact continuous_exp_mul_ofReal _ _
                have hnorm : ∀ s : ℝ,
                    ‖Complex.exp (-(2 * Real.pi * Complex.I *
                      ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ)))))‖ = 1 := by
                  intro s
                  have he : -(2 * Real.pi * Complex.I *
                      ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ)))) =
                    ((-(2 * Real.pi * ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ)))) : ℝ) : ℂ) *
                    Complex.I := by push_cast; ring
                  rw [he, Complex.norm_exp_ofReal_mul_I]
                exact hgb.congr_norm (hcont.aestronglyMeasurable.mul hgb.1)
                  (ae_of_all _ fun s => by simp only [norm_mul, hnorm s, one_mul])
              have hcont2 : Continuous (fun s : ℝ =>
                  Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * s)))) := by
                have hrew : (fun s : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * s)))) =
                    fun s : ℝ => Complex.exp ((-(2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ)))) * (s : ℂ) + 0) := by
                  funext s; congr 1; push_cast; ring
                rw [hrew]
                exact continuous_exp_mul_ofReal _ _
              have hnorm2 : ∀ s : ℝ,
                  ‖Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * s)))‖ = 1 := by
                intro s
                have he : -(2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * s)) =
                  ((-(2 * Real.pi * ((k : ℝ) * (n : ℝ) * s)) : ℝ) : ℂ) * Complex.I := by
                  push_cast; ring
                rw [he, Complex.norm_exp_ofReal_mul_I]
              exact hinner.congr_norm (hcont2.aestronglyMeasurable.mul hinner.1)
                (ae_of_all _ fun s => by simp only [norm_mul, hnorm2 s, one_mul])
            exact hmem1.integrable one_le_two
          simp_rw [Finset.mul_sum]
          rw [integral_finsetSum ℬ hterm_int]
          have hsum_eq_Ω' : (∑ B ∈ ℬ, ∫ t in Set.Ico (0 : ℝ) (1 / (k : ℝ)),
              Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * t))) *
              (T B).indicator (fun s => ∑ b ∈ B,
                Complex.exp (-(2 * Real.pi * Complex.I *
                  ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ))))) *
                g (fun _ => s + (b : ℝ) / (k : ℝ))) t) =
            ∫ x in Ω', conj (exponentialCharacter
              (fun _ : Fin 1 => (k : ℝ) * ((γ.val : ℝ) / (L : ℝ) + (n : ℝ))) x) * g x := by
            have hint_Ωg : IntegrableOn
                (fun x : Fin 1 → ℝ => conj (exponentialCharacter
                  (fun _ : Fin 1 => (k : ℝ) * ((γ.val : ℝ) / (L : ℝ) + (n : ℝ))) x) * g x) Ω' := by
              have hcont := Complex.continuous_conj.comp
                (continuous_exponentialCharacter
                  (fun _ : Fin 1 => (k : ℝ) * ((γ.val : ℝ) / (L : ℝ) + (n : ℝ))))
              have hmem_prod : MemLp
                  (fun x : Fin 1 → ℝ => conj (exponentialCharacter
                    (fun _ : Fin 1 => (k : ℝ) * ((γ.val : ℝ) / (L : ℝ) + (n : ℝ))) x) * g x)
                  2 (volume.restrict Ω') :=
                hgm.congr_norm (hcont.aestronglyMeasurable.mul hgm.1)
                  (ae_of_all _ fun x => by simp [norm_exponentialCharacter])
              exact hmem_prod.integrable one_le_two
            rw [hint_Ω' _ hint_Ωg]
            refine Finset.sum_congr rfl fun B hB => ?_
            have hTfin : IsFiniteMeasure (volume.restrict (T B)) :=
              isFiniteMeasure_restrict.2
                (ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
                  (measure_mono (hTmeas B hB).2))
            have hind_eq : (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * t))) *
                  (T B).indicator (fun s => ∑ b ∈ B,
                    Complex.exp (-(2 * Real.pi * Complex.I *
                      ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ))))) *
                    g (fun _ => s + (b : ℝ) / (k : ℝ))) t) =
                (T B).indicator (fun s => ∑ b ∈ B,
                  conj (exponentialCharacter
                    (fun _ : Fin 1 => (k : ℝ) * ((γ.val : ℝ) / (L : ℝ) + (n : ℝ)))
                    (fun _ => s + (b : ℝ) / (k : ℝ))) *
                  g (fun _ => s + (b : ℝ) / (k : ℝ))) := by
              funext t
              by_cases ht : t ∈ T B
              · simp only [ht, Set.indicator_of_mem, Finset.mul_sum]
                refine Finset.sum_congr rfl fun b _ => ?_
                rw [← mul_assoc]
                congr 1
                rw [ec1_conj, ec1_eq, ← Complex.exp_add]
                simp only [Pi.neg_apply]
                have h1 : -(2 * Real.pi * Complex.I * ((k : ℝ) * (n : ℝ) * t)) +
                    -(2 * Real.pi * Complex.I *
                      ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (t + (b : ℝ) / (k : ℝ)))) =
                    2 * Real.pi * Complex.I *
                      (-((k : ℝ) * ((γ.val : ℝ) / (L : ℝ) + (n : ℝ))) * (t + (b : ℝ) / (k : ℝ))) +
                    2 * Real.pi * Complex.I * ((n * b : ℤ) : ℂ) := by
                  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
                  push_cast
                  field_simp [hkc]
                  ring
                rw [h1, Complex.exp_add, exp_two_pi_I_int, mul_one]
                congr 1
                push_cast
                ring
              · simp [ht]
            rw [hind_eq, setIntegral_indicator (hTmeas B hB).1,
              Set.inter_eq_right.2 (hTmeas B hB).2]
            rw [integral_finsetSum B]
            intro b hb
            have hgb := hg_shift_memLp B hB b hb
            have hcont : Continuous (fun s : ℝ => conj (exponentialCharacter
                (fun _ : Fin 1 => (k : ℝ) * ((γ.val : ℝ) / (L : ℝ) + (n : ℝ)))
                (fun _ => s + (b : ℝ) / (k : ℝ)))) :=
              Complex.continuous_conj.comp
                ((continuous_exponentialCharacter _).comp
                  (continuous_pi fun _ => continuous_id.add continuous_const))
            have hmem_b : MemLp (fun s : ℝ => conj (exponentialCharacter
                (fun _ : Fin 1 => (k : ℝ) * ((γ.val : ℝ) / (L : ℝ) + (n : ℝ)))
                (fun _ => s + (b : ℝ) / (k : ℝ))) * g (fun _ => s + (b : ℝ) / (k : ℝ)))
                2 (volume.restrict (T B)) :=
              hgb.congr_norm (hcont.aestronglyMeasurable.mul hgb.1)
                (ae_of_all _ fun s => by simp [norm_exponentialCharacter])
            exact hmem_b.integrable one_le_two
          rw [hsum_eq_Ω', hg' γ hγ n]
      have hkey_all : ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) (1 / (k : ℝ)))),
          ∀ γ ∈ Γ, ∑ B ∈ ℬ, (T B).indicator
            (fun s => ∑ b ∈ B,
              Complex.exp (-(2 * Real.pi * Complex.I *
                ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ))))) *
              g (fun _ => s + (b : ℝ) / (k : ℝ))) t = 0 :=
        (Filter.eventually_all_finset Γ).2 hkey
      rw [Lp.eq_zero_iff_ae_eq_zero]
      set gf : (Fin 1 → ℝ) → ℂ := (g : (Fin 1 → ℝ) → ℂ)
      show ∀ᵐ x ∂(volume.restrict Ω'), gf x = 0
      rw [hΩ'_eq, ae_restrict_biUnion_finset_iff]
      intro p hp
      obtain ⟨hB, hb⟩ := Finset.mem_sigma.1 hp
      rw [← (hshift_mp p.1 p.2).map_eq, (hshift_emb p.2).ae_map_iff]
      have hae_T : ∀ᵐ t ∂(volume.restrict (T p.1)),
          ∀ γ ∈ Γ, ∑ B ∈ ℬ, (T B).indicator
            (fun s => ∑ b ∈ B,
              Complex.exp (-(2 * Real.pi * Complex.I *
                ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (s + (b : ℝ) / (k : ℝ))))) *
              g (fun _ => s + (b : ℝ) / (k : ℝ))) t = 0 :=
        ae_restrict_of_ae_restrict_of_subset (hTmeas p.1 hB).2 hkey_all
      filter_upwards [hae_T, self_mem_ae_restrict (hTmeas p.1 hB).1] with t ht hmemT
      have hw : ∀ γ ∈ Γ, ∑ b ∈ p.1,
          Complex.exp (-(2 * Real.pi * Complex.I * ((γ.val : ℝ) * (b : ℝ) / (L : ℝ)))) *
          (g : (Fin 1 → ℝ) → ℂ) (fun _ => t + (b : ℝ) / (k : ℝ)) = 0 := by
        intro γ hγ
        have h0 := ht γ hγ
        rw [Finset.sum_eq_single p.1] at h0
        · rw [Set.indicator_of_mem hmemT] at h0
          have hfact : (∑ b ∈ p.1,
              Complex.exp (-(2 * Real.pi * Complex.I *
                ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * (t + (b : ℝ) / (k : ℝ))))) *
              g (fun _ => t + (b : ℝ) / (k : ℝ))) =
            Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * ((γ.val : ℝ) / (L : ℝ)) * t))) *
            ∑ b ∈ p.1,
              Complex.exp (-(2 * Real.pi * Complex.I * ((γ.val : ℝ) * (b : ℝ) / (L : ℝ)))) *
              g (fun _ => t + (b : ℝ) / (k : ℝ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => ?_
            symm
            rw [← mul_assoc, ← Complex.exp_add]
            congr 2
            have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
            have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
            push_cast
            field_simp [hkc, hLc]
            ring
          rw [hfact] at h0
          exact (mul_eq_zero.1 h0).resolve_left (Complex.exp_ne_zero _)
        · intro B' hB' hBne
          have hnot : t ∉ T B' := fun ht' => Set.disjoint_left.1 (hTdisj p.1 hB B' hB' hBne.symm) hmemT ht'
          exact Set.indicator_of_notMem hnot _
        · intro hnot; exact absurd hB hnot
      exact linalg_fin p.1 Γ (hΓcard_k.trans (hBtile p.1 hB).1.symm) (hΓorthZ p.1 hB)
        (fun b => (g : (Fin 1 → ℝ) → ℂ) (fun _ => t + (b : ℝ) / (k : ℝ))) hw p.2 hb
  exact isSpectral_of_ae_eq (by rw [symmDiff_comm]; exact hΩdiff) hmeas.nullMeasurableSet hspec_Ω'

/- Part 3: Fiber extraction and tiling lift (H3 + H4 -> Spectral => Tiling) -/

lemma spectral_to_tiling_unit (h3 : H3) (h4 : H4)
    (Ω : Set (Fin 1 → ℝ)) (hbdd : Bornology.IsBounded Ω) (hmeas : MeasurableSet Ω)
    (hvol : volume Ω = 1) (hspec : isSpectral Ω) :
    tilesByTranslation Ω := by
  classical
  obtain ⟨p, Γ, hp, hΓcard, hΓrange, hpair⟩ := h3 Ω hbdd hmeas hvol hspec
  obtain ⟨_, _, hΩfin, horth, _⟩ := hpair
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.2 hΩfin
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpne : (p : ℝ) ≠ 0 := hppos.ne'
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : Fin 1 → ℝ)
  set K : ℕ := Nat.ceil ((|R| + 1) * (p : ℝ)) + 1
  set I : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  have hmemI : ∀ (t : ℝ) (k : ℤ), t ∈ Set.Ico (0 : ℝ) (1 / (p : ℝ)) →
      (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) ∈ Ω → k ∈ I := by
    intro t k ht hx
    have hball : ‖(fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ))‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR hx
    have h0 : |t + (k : ℝ) / (p : ℝ)| ≤ |R| :=
      (norm_le_pi_norm (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) 0).trans (hball.trans (le_abs_self R))
    have ht1 : |t| ≤ 1 := by
      rw [abs_of_nonneg ht.1]
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      exact ht.2.le.trans (div_le_one_of_le₀ hp1 hppos.le)
    have hkdiv : |(k : ℝ) / (p : ℝ)| ≤ |R| + 1 := by
      have := abs_sub_le (t + (k : ℝ) / (p : ℝ)) 0 t
      have htri : |(k : ℝ) / (p : ℝ)| = |(t + (k : ℝ) / (p : ℝ)) - t| := by ring_nf
      rw [htri]
      exact (abs_sub _ _).trans (add_le_add h0 ht1)
    have hkabs : |(k : ℝ)| ≤ (|R| + 1) * (p : ℝ) := by
      rw [abs_div, abs_of_pos hppos] at hkdiv
      exact (div_le_iff₀ hppos).1 hkdiv
    have hKge : (|R| + 1) * (p : ℝ) ≤ (K : ℝ) := by
      have := Nat.le_ceil ((|R| + 1) * (p : ℝ))
      push_cast [K]
      linarith
    have hkR : -(K : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ (K : ℝ) := abs_le.1 (hkabs.trans hKge)
    rw [Finset.mem_Icc]
    exact ⟨by exact_mod_cast hkR.1, by exact_mod_cast hkR.2⟩
  let cell : ℤ → Set (Fin 1 → ℝ) :=
    fun k => Ω ∩ {x : Fin 1 → ℝ | x 0 ∈ Set.Ico ((k : ℝ) / (p : ℝ)) (((k : ℝ) + 1) / (p : ℝ))}
  have hΩ_union : Ω = ⋃ k ∈ I, cell k := by
    ext x
    simp only [cell, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ico]
    constructor
    · intro hx
      set k : ℤ := ⌊(p : ℝ) * x 0⌋
      set t : ℝ := x 0 - (k : ℝ) / (p : ℝ)
      have ht : t ∈ Set.Ico (0 : ℝ) (1 / (p : ℝ)) := by
        have hfl : (k : ℝ) ≤ (p : ℝ) * x 0 ∧ (p : ℝ) * x 0 < (k : ℝ) + 1 :=
          ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
        constructor
        · have : 0 ≤ (p : ℝ) * x 0 - (k : ℝ) := by linarith
          have h2 : t = ((p : ℝ) * x 0 - (k : ℝ)) / (p : ℝ) := by
            dsimp only [t]; field_simp [hpne]
          rw [h2]; exact div_nonneg this hppos.le
        · have : (p : ℝ) * x 0 - (k : ℝ) < 1 := by linarith
          have h2 : t = ((p : ℝ) * x 0 - (k : ℝ)) / (p : ℝ) := by
            dsimp only [t]; field_simp [hpne]
          rw [h2]; exact (div_lt_div_iff_of_pos_right hppos).2 this
      have hxeq : (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) = x := by
        ext i; fin_cases i; simp [t]
      refine ⟨k, hmemI t k ht (hxeq.symm ▸ hx), hx, ?_, ?_⟩
      · have : x 0 = t + (k : ℝ) / (p : ℝ) := by simp [t]
        linarith [ht.1]
      · have : x 0 = t + (k : ℝ) / (p : ℝ) := by simp [t]
        have hsum : 1 / (p : ℝ) + (k : ℝ) / (p : ℝ) = ((k : ℝ) + 1) / (p : ℝ) := by ring
        linarith [ht.2]
    · rintro ⟨_, _, hx, _⟩; exact hx
  have hcell_meas : ∀ k ∈ I, MeasurableSet (cell k) := fun k _ =>
    hmeas.inter (measurableSet_Ico.preimage (measurable_pi_apply 0))
  have hcell_disj : (I : Set ℤ).PairwiseDisjoint cell := by
    intro k₁ _ k₂ _ hne
    show Disjoint (cell k₁) (cell k₂)
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    have h1 : (k₁ : ℝ) / (p : ℝ) ≤ x 0 ∧ x 0 < ((k₁ : ℝ) + 1) / (p : ℝ) := hx₁.2
    have h2 : (k₂ : ℝ) / (p : ℝ) ≤ x 0 ∧ x 0 < ((k₂ : ℝ) + 1) / (p : ℝ) := hx₂.2
    have hlt1 : (k₁ : ℝ) < (k₂ : ℝ) + 1 := by
      have : (k₁ : ℝ) / (p : ℝ) < ((k₂ : ℝ) + 1) / (p : ℝ) := h1.1.trans_lt h2.2
      exact (div_lt_div_iff_of_pos_right hppos).1 this
    have hlt2 : (k₂ : ℝ) < (k₁ : ℝ) + 1 := by
      have : (k₂ : ℝ) / (p : ℝ) < ((k₁ : ℝ) + 1) / (p : ℝ) := h2.1.trans_lt h1.2
      exact (div_lt_div_iff_of_pos_right hppos).1 this
    have h1Z : k₁ < k₂ + 1 := by exact_mod_cast hlt1
    have h2Z : k₂ < k₁ + 1 := by exact_mod_cast hlt2
    exact hne (by omega)
  have hshift_emb : ∀ k : ℤ, MeasurableEmbedding
      (fun t : ℝ => (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ))) := fun k =>
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding.comp
      (MeasurableEquiv.addRight ((k : ℝ) / (p : ℝ))).measurableEmbedding
  have hshift_mp_vol : ∀ k : ℤ, MeasurePreserving
      (fun t : ℝ => (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ))) volume volume := fun k =>
    mp_funUnique_symm.comp (measurePreserving_add_right volume ((k : ℝ) / (p : ℝ)))
  have hshift_pre : ∀ k : ℤ,
      (fun t : ℝ => (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ))) ⁻¹' cell k =
      Set.Ico (0 : ℝ) (1 / (p : ℝ)) ∩ {t : ℝ | (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) ∈ Ω} := by
    intro k
    ext t
    simp only [cell, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨by linarith, ?_⟩, h1⟩
      have : ((k : ℝ) + 1) / (p : ℝ) = 1 / (p : ℝ) + (k : ℝ) / (p : ℝ) := by ring
      linarith
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h3, by linarith, ?_⟩
      have : ((k : ℝ) + 1) / (p : ℝ) = 1 / (p : ℝ) + (k : ℝ) / (p : ℝ) := by ring
      linarith
  let fiber : ℝ → Finset ℤ := fun t =>
    I.filter (fun k => (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) ∈ Ω)
  have hint_Ω : ∀ (h : (Fin 1 → ℝ) → ℂ), IntegrableOn h Ω →
      ∫ x in Ω, h x = ∫ t in Set.Ico (0 : ℝ) (1 / (p : ℝ)),
        ∑ k ∈ fiber t, h (fun _ => t + (k : ℝ) / (p : ℝ)) := by
    intro h hint
    have hsplit : ∫ x in Ω, h x = ∑ k ∈ I, ∫ x in cell k, h x := by
      conv_lhs => rw [hΩ_union]
      exact integral_biUnion_finset I hcell_meas hcell_disj
        (fun k hk => hint.mono_set (by rw [hΩ_union]; exact Set.subset_biUnion_of_mem (u := cell) hk))
    have hterm : ∀ k ∈ I,
        ∫ x in cell k, h x =
        ∫ t in Set.Ico (0 : ℝ) (1 / (p : ℝ)),
          {t : ℝ | (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) ∈ Ω}.indicator
            (fun t => h (fun _ => t + (k : ℝ) / (p : ℝ))) t := by
      intro k _
      have hm := (hshift_mp_vol k).setIntegral_preimage_emb (hshift_emb k) h (cell k)
      rw [hshift_pre k] at hm
      rw [← hm]
      have hmk : MeasurableSet {t : ℝ | (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) ∈ Ω} :=
        hmeas.preimage (hshift_emb k).measurable
      rw [setIntegral_indicator hmk]
    have hint_k : ∀ k ∈ I,
        IntegrableOn
          (fun t : ℝ => {t : ℝ | (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) ∈ Ω}.indicator
            (fun t => h (fun _ => t + (k : ℝ) / (p : ℝ))) t)
          (Set.Ico (0 : ℝ) (1 / (p : ℝ))) := by
      intro k hk
      have hmk : MeasurableSet {t : ℝ | (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) ∈ Ω} :=
        hmeas.preimage (hshift_emb k).measurable
      rw [IntegrableOn, integrable_indicator_iff hmk, IntegrableOn, Measure.restrict_restrict hmk,
        Set.inter_comm, ← hshift_pre k]
      have hint_cell : IntegrableOn h (cell k) :=
        hint.mono_set (by rw [hΩ_union]; exact Set.subset_biUnion_of_mem (u := cell) hk)
      exact (hshift_mp_vol k).integrableOn_comp_preimage (hshift_emb k) |>.2 hint_cell
    rw [hsplit, Finset.sum_congr rfl hterm, ← integral_finsetSum I hint_k]
    refine setIntegral_congr_fun measurableSet_Ico fun t _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) ∈ Ω <;> simp [hk]
  have hIco_fin : IsFiniteMeasure (volume.restrict (Set.Ico (0 : ℝ) (1 / (p : ℝ)))) :=
    isFiniteMeasure_restrict.2 (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  have hcard_ae : ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) (1 / (p : ℝ)))),
      (fiber t).card = p := by
    have hΓne : Γ.Nonempty := Finset.card_pos.1 (hΓcard.symm ▸ hp)
    obtain ⟨γ₀, hγ₀⟩ := hΓne
    let G₀ : ℝ → ℂ := fun t => ((fiber t).card : ℂ) - (p : ℂ)
    have hG₀_eq : G₀ = fun t =>
        (∑ k ∈ I, {t : ℝ | (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) ∈ Ω}.indicator
          (fun _ => (1 : ℂ)) t) - (p : ℂ) := by
      funext t
      simp only [G₀, fiber, Finset.card_filter, Nat.cast_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) ∈ Ω <;> simp [hk]
    have hG₀_memLp : MemLp G₀ 2 (volume.restrict (Set.Ico (0 : ℝ) (1 / (p : ℝ)))) := by
      rw [hG₀_eq]
      apply MemLp.sub _ (memLp_const _)
      apply memLp_finsetSum I
      intro k _
      have hmk : MeasurableSet {t : ℝ | (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) ∈ Ω} :=
        hmeas.preimage (hshift_emb k).measurable
      exact (memLp_const (1 : ℂ)).indicator hmk
    have hG₀_zero : G₀ =ᵐ[volume.restrict (Set.Ico (0 : ℝ) (1 / (p : ℝ)))] 0 := by
      apply fourier_complete_Ico_div p hp G₀ hG₀_memLp
      intro n
      have h1 : (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t))) * G₀ t) =
          fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t))) * ((fiber t).card : ℂ) -
            Complex.exp (-(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t))) * (p : ℂ) := by
        funext t; simp [G₀, mul_sub]
      rw [h1]
      have hcont : Continuous (fun t : ℝ =>
          Complex.exp (-(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t)))) := by
        have hrew : (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t)))) =
            fun t : ℝ => Complex.exp ((-(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ)))) * (t : ℂ) + 0) := by
          funext t; congr 1; push_cast; ring
        rw [hrew]
        exact continuous_exp_mul_ofReal _ _
      have hnorm : ∀ t : ℝ,
          ‖Complex.exp (-(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t)))‖ = 1 := by
        intro t
        have he : -(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t)) =
            ((-(2 * Real.pi * ((p : ℝ) * (n : ℝ) * t)) : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [he, Complex.norm_exp_ofReal_mul_I]
      have hcard_memLp : MemLp (fun t : ℝ => ((fiber t).card : ℂ)) 2
          (volume.restrict (Set.Ico (0 : ℝ) (1 / (p : ℝ)))) := by
        have : (fun t : ℝ => ((fiber t).card : ℂ)) = fun t => G₀ t + (p : ℂ) := by
          funext t; simp [G₀]
        rw [this]
        exact hG₀_memLp.add (memLp_const _)
      have hint_a : IntegrableOn
          (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t))) * ((fiber t).card : ℂ))
          (Set.Ico (0 : ℝ) (1 / (p : ℝ))) :=
        (hcard_memLp.congr_norm (hcont.aestronglyMeasurable.mul hcard_memLp.1)
          (ae_of_all _ fun t => by simp only [Pi.mul_apply, norm_mul, hnorm t, one_mul])).integrable one_le_two
      have hint_b : IntegrableOn
          (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t))) * (p : ℂ))
          (Set.Ico (0 : ℝ) (1 / (p : ℝ))) :=
        ((memLp_const (p : ℂ)).congr_norm (hcont.aestronglyMeasurable.mul aestronglyMeasurable_const)
          (ae_of_all _ fun t => by simp only [Pi.mul_apply, norm_mul, hnorm t, one_mul])).integrable one_le_two
      rw [integral_sub hint_a hint_b]
      by_cases hn : n = 0
      · subst hn
        simp only [Int.cast_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul,
          Complex.ofReal_zero]
        have hI1 : ∫ t in Set.Ico (0 : ℝ) (1 / (p : ℝ)), ((fiber t).card : ℂ) = 1 := by
          have hΩ1 := hint_Ω (fun _ => (1 : ℂ)) (integrableOn_const hΩfin)
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one, setIntegral_const,
            Measure.real_def, hvol, ENNReal.toReal_one, one_smul] at hΩ1
          exact hΩ1.symm
        have hI2 : ∫ t in Set.Ico (0 : ℝ) (1 / (p : ℝ)), (p : ℂ) = 1 := by
          rw [setIntegral_const, Measure.real_def, Real.volume_Ico, sub_zero,
            ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
          have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
          push_cast
          field_simp [hpC]
        rw [hI1, hI2, sub_self]
      · have hI1 : ∫ t in Set.Ico (0 : ℝ) (1 / (p : ℝ)),
            Complex.exp (-(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t))) *
            ((fiber t).card : ℂ) = 0 := by
          set ξ₁ : Fin 1 → ℝ := fun _ => γ₀ + (p : ℝ) * (n : ℝ)
          set ξ₂ : Fin 1 → ℝ := fun _ => γ₀
          have hξ₁ : ξ₁ ∈ {ξ : Fin 1 → ℝ | ∃ γ ∈ Γ, ∃ m : ℤ, ξ 0 = γ + (p : ℝ) * (m : ℝ)} :=
            ⟨γ₀, hγ₀, n, rfl⟩
          have hξ₂ : ξ₂ ∈ {ξ : Fin 1 → ℝ | ∃ γ ∈ Γ, ∃ m : ℤ, ξ 0 = γ + (p : ℝ) * (m : ℝ)} :=
            ⟨γ₀, hγ₀, 0, by simp [ξ₂]⟩
          have hne : ξ₁ ≠ ξ₂ := by
            intro h
            have h0 := congrFun h 0
            simp only [ξ₁, ξ₂] at h0
            have hpn : (p : ℝ) * (n : ℝ) = 0 := by linarith
            have hnR : (n : ℝ) = 0 := (mul_eq_zero.1 hpn).resolve_left hpne
            exact hn (by exact_mod_cast hnR)
          have h0 := horth ξ₁ hξ₁ ξ₂ hξ₂ hne
          dsimp only at h0
          rw [inner_toLp_eq] at h0
          have hpt : ∀ x : Fin 1 → ℝ,
              conj (exponentialCharacter ξ₁ x) * exponentialCharacter ξ₂ x =
                exponentialCharacter (ξ₂ - ξ₁) x := by
            intro x; rw [ec1_conj, ← ec1_add_left]; congr 1; abel
          simp_rw [hpt] at h0
          rw [hint_Ω _ ((exponentialCharacter_memLp hΩfin _).integrable one_le_two)] at h0
          rw [← h0]
          refine setIntegral_congr_fun measurableSet_Ico fun t _ => ?_
          have hsum : ∑ k ∈ fiber t, exponentialCharacter (ξ₂ - ξ₁) (fun _ => t + (k : ℝ) / (p : ℝ)) =
              Complex.exp (-(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t))) * ((fiber t).card : ℂ) := by
            have hterm' : ∀ k ∈ fiber t,
                exponentialCharacter (ξ₂ - ξ₁) (fun _ => t + (k : ℝ) / (p : ℝ)) =
                Complex.exp (-(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t))) := by
              intro k _
              rw [ec1_eq]
              have hdiff : (ξ₂ - ξ₁) 0 = -((p : ℝ) * (n : ℝ)) := by simp [ξ₁, ξ₂]
              rw [hdiff]
              have hexp : 2 * Real.pi * Complex.I * ((-((p : ℝ) * (n : ℝ)) * (t + (k : ℝ) / (p : ℝ)) : ℝ) : ℂ) =
                  -(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t)) +
                  2 * Real.pi * Complex.I * ((-(n * k) : ℤ) : ℂ) := by
                have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
                push_cast
                field_simp [hpC]
                ring
              rw [← Complex.ofReal_mul, hexp, Complex.exp_add, exp_two_pi_I_int, mul_one]
            rw [Finset.sum_congr rfl hterm', Finset.sum_const, nsmul_eq_mul, mul_comm]
          exact hsum.symm
        have hI2 : ∫ t in Set.Ico (0 : ℝ) (1 / (p : ℝ)),
            Complex.exp (-(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t))) * (p : ℂ) = 0 := by
          rw [integral_mul_const]
          have hrew : (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t)))) =
              fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((p : ℝ) * ((-n : ℤ) : ℝ) * t)) := by
            funext t; congr 1; push_cast; ring
          rw [hrew, integral_Ico_div_exp p hp (-n) (neg_ne_zero.2 hn), zero_mul]
        rw [hI1, hI2, sub_self]
    filter_upwards [hG₀_zero] with t ht
    have hsub : ((fiber t).card : ℂ) - (p : ℂ) = 0 := ht
    have heq : ((fiber t).card : ℂ) = (p : ℂ) := sub_eq_zero.1 hsub
    exact_mod_cast heq
  have horth_ae : ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ →
      ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) (1 / (p : ℝ)))),
        ∑ k ∈ fiber t, Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) / (p : ℝ)) * (k : ℝ)) = 0 := by
    intro γ₁ hγ₁ γ₂ hγ₂ hγne
    let G : ℝ → ℂ := fun t =>
      Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) * t)) *
      ∑ k ∈ fiber t, Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) / (p : ℝ)) * (k : ℝ))
    have hG_eq : G = fun t =>
        ∑ k ∈ I, {t : ℝ | (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) ∈ Ω}.indicator
          (fun s => Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) * s)) *
            Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) / (p : ℝ)) * (k : ℝ))) t := by
      funext t
      dsimp only [G]
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) ∈ Ω <;> simp [hk]
    have hG_memLp : MemLp G 2 (volume.restrict (Set.Ico (0 : ℝ) (1 / (p : ℝ)))) := by
      rw [hG_eq]
      apply memLp_finsetSum I
      intro k _
      have hmk : MeasurableSet {t : ℝ | (fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ)) ∈ Ω} :=
        hmeas.preimage (hshift_emb k).measurable
      have hcont : Continuous (fun s : ℝ =>
          Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) * s)) *
          Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) / (p : ℝ)) * (k : ℝ))) := by
        have hc1 : Continuous (fun s : ℝ =>
            Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) * s))) := by
          have hrew : (fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) * s))) =
              fun s : ℝ => Complex.exp ((2 * Real.pi * Complex.I * ((γ₁ - γ₂) : ℂ)) * (s : ℂ) + 0) := by
            funext s; congr 1; ring
          rw [hrew]
          exact continuous_exp_mul_ofReal _ _
        exact hc1.mul continuous_const
      have hnorm : ∀ s : ℝ,
          ‖Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) * s)) *
            Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) / (p : ℝ)) * (k : ℝ))‖ = 1 := by
        intro s
        rw [norm_mul]
        have he1 : 2 * Real.pi * Complex.I * ((γ₁ - γ₂) * s) =
            ((2 * Real.pi * ((γ₁ - γ₂) * s) : ℝ) : ℂ) * Complex.I := by push_cast; ring
        have he2 : 2 * Real.pi * Complex.I * ((γ₁ - γ₂) / (p : ℝ)) * (k : ℝ) =
            ((2 * Real.pi * ((γ₁ - γ₂) / (p : ℝ)) * (k : ℝ) : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [he1, he2, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, mul_one]
      have h1 : MemLp (fun s : ℝ =>
          Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) * s)) *
          Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) / (p : ℝ)) * (k : ℝ)))
          2 (volume.restrict (Set.Ico (0 : ℝ) (1 / (p : ℝ)))) :=
        (memLp_const (1 : ℂ)).congr_norm hcont.aestronglyMeasurable
          (ae_of_all _ fun s => by rw [hnorm s]; simp)
      exact h1.indicator hmk
    have hG_zero : G =ᵐ[volume.restrict (Set.Ico (0 : ℝ) (1 / (p : ℝ)))] 0 := by
      apply fourier_complete_Ico_div p hp G hG_memLp
      intro n
      set ξ₁ : Fin 1 → ℝ := fun _ => γ₂ + (p : ℝ) * (n : ℝ)
      set ξ₂ : Fin 1 → ℝ := fun _ => γ₁
      have hξ₁ : ξ₁ ∈ {ξ : Fin 1 → ℝ | ∃ γ ∈ Γ, ∃ m : ℤ, ξ 0 = γ + (p : ℝ) * (m : ℝ)} :=
        ⟨γ₂, hγ₂, n, rfl⟩
      have hξ₂ : ξ₂ ∈ {ξ : Fin 1 → ℝ | ∃ γ ∈ Γ, ∃ m : ℤ, ξ 0 = γ + (p : ℝ) * (m : ℝ)} :=
        ⟨γ₁, hγ₁, 0, by simp [ξ₂]⟩
      have hne : ξ₁ ≠ ξ₂ := by
        intro h
        have h0 := congrFun h 0
        simp only [ξ₁, ξ₂] at h0
        have hr1 := hΓrange γ₁ hγ₁
        have hr2 := hΓrange γ₂ hγ₂
        have hlt : (p : ℝ) * (n : ℝ) < (p : ℝ) * 1 := by linarith
        have hgt : (p : ℝ) * (-1 : ℝ) < (p : ℝ) * (n : ℝ) := by linarith
        have hn1 : (n : ℝ) < 1 := lt_of_mul_lt_mul_left hlt hppos.le
        have hn2 : (-1 : ℝ) < (n : ℝ) := lt_of_mul_lt_mul_left hgt hppos.le
        have hnZ : n = 0 := by
          have a1 : n < 1 := by exact_mod_cast hn1
          have a2 : -1 < n := by exact_mod_cast hn2
          omega
        subst hnZ
        simp only [Int.cast_zero, mul_zero, add_zero] at h0
        exact hγne h0.symm
      have h0 := horth ξ₁ hξ₁ ξ₂ hξ₂ hne
      dsimp only at h0
      rw [inner_toLp_eq] at h0
      have hpt : ∀ x : Fin 1 → ℝ,
          conj (exponentialCharacter ξ₁ x) * exponentialCharacter ξ₂ x =
            exponentialCharacter (ξ₂ - ξ₁) x := by
        intro x; rw [ec1_conj, ← ec1_add_left]; congr 1; abel
      simp_rw [hpt] at h0
      rw [hint_Ω _ ((exponentialCharacter_memLp hΩfin _).integrable one_le_two)] at h0
      rw [← h0]
      refine setIntegral_congr_fun measurableSet_Ico fun t _ => ?_
      simp only [G, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ec1_eq, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
      have hdiff : (ξ₂ - ξ₁) 0 = (γ₁ - γ₂) - (p : ℝ) * (n : ℝ) := by simp [ξ₁, ξ₂]; ring
      rw [hdiff]
      have hexp : (-(2 * Real.pi * Complex.I * ((p : ℝ) * (n : ℝ) * t)) +
          2 * Real.pi * Complex.I * ((γ₁ - γ₂) * t)) +
          2 * Real.pi * Complex.I * ((γ₁ - γ₂) / (p : ℝ)) * (k : ℝ) =
        2 * Real.pi * Complex.I *
          ((((γ₁ - γ₂) - (p : ℝ) * (n : ℝ)) * (t + (k : ℝ) / (p : ℝ)) : ℝ) : ℂ) +
        2 * Real.pi * Complex.I * ((n * k : ℤ) : ℂ) := by
        have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
        push_cast
        field_simp [hpC]
        ring
      rw [hexp, Complex.exp_add, exp_two_pi_I_int, mul_one, Complex.ofReal_mul]
    filter_upwards [hG_zero] with t ht
    exact (mul_eq_zero.1 ht).resolve_left (Complex.exp_ne_zero _)
  have hgood_ae : ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) (1 / (p : ℝ)))),
      (fiber t).card = p ∧
      ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ →
        ∑ k ∈ fiber t, Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) / (p : ℝ)) * (k : ℝ)) = 0 := by
    have hall : ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) (1 / (p : ℝ)))),
        ∀ q ∈ Γ ×ˢ Γ, q.1 ≠ q.2 →
          ∑ k ∈ fiber t, Complex.exp (2 * Real.pi * Complex.I * ((q.1 - q.2) / (p : ℝ)) * (k : ℝ)) = 0 := by
      rw [Filter.eventually_all_finset]
      intro q hq
      by_cases hne : q.1 = q.2
      · exact ae_of_all _ fun _ h => absurd hne h
      · filter_upwards [horth_ae q.1 (Finset.mem_product.1 hq).1 q.2 (Finset.mem_product.1 hq).2 hne]
          with t ht _ using ht
    filter_upwards [hcard_ae, hall] with t hc ho
    exact ⟨hc, fun γ₁ hγ₁ γ₂ hγ₂ hne => ho (γ₁, γ₂) (Finset.mem_product.2 ⟨hγ₁, hγ₂⟩) hne⟩
  let E : Finset ℤ → Set ℝ := fun S => {t ∈ Set.Ico (0 : ℝ) (1 / (p : ℝ)) | fiber t = S}
  let 𝒜 : Finset (Finset ℤ) := I.powerset.filter (fun S => volume (E S) ≠ 0)
  let Γ' : Finset ℝ := Γ.image (fun γ => γ / (p : ℝ))
  have hdiv_inj : Function.Injective (fun γ : ℝ => γ / (p : ℝ)) := fun a b h => by
    have := congrArg (· * (p : ℝ)) h
    simpa [div_mul_cancel₀ _ hpne] using this
  have hΓ'card : Γ'.card = p := by
    rw [Finset.card_image_of_injective _ hdiv_inj, hΓcard]
  have h𝒜good : ∀ S ∈ 𝒜, S.card = p ∧
      ∀ γ₁' ∈ Γ', ∀ γ₂' ∈ Γ', γ₁' ≠ γ₂' →
        ∑ k ∈ S, Complex.exp (2 * Real.pi * Complex.I * (γ₁' - γ₂') * (k : ℝ)) = 0 := by
    intro S hS
    have hvolS : volume (E S) ≠ 0 := (Finset.mem_filter.1 hS).2
    have hEsub : E S ⊆ Set.Ico (0 : ℝ) (1 / (p : ℝ)) := fun _ ht => ht.1
    have hne_good : ∃ t ∈ E S,
        (fiber t).card = p ∧
        ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ →
          ∑ k ∈ fiber t, Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) / (p : ℝ)) * (k : ℝ)) = 0 := by
      by_contra hno
      push Not at hno
      have hbad_sub : E S ⊆ {t | ¬ ((fiber t).card = p ∧
          ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ →
            ∑ k ∈ fiber t, Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) / (p : ℝ)) * (k : ℝ)) = 0)} := by
        intro t ht hgood
        obtain ⟨h1, h2⟩ := hgood
        obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hne, hnz⟩ := hno t ht h1
        exact hnz (h2 γ₁ hγ₁ γ₂ hγ₂ hne)
      have hnull_bad : (volume.restrict (Set.Ico (0 : ℝ) (1 / (p : ℝ))))
          {t | ¬ ((fiber t).card = p ∧
            ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ →
              ∑ k ∈ fiber t, Complex.exp (2 * Real.pi * Complex.I * ((γ₁ - γ₂) / (p : ℝ)) * (k : ℝ)) = 0)} = 0 :=
        ae_iff.1 hgood_ae
      have hnull_E : (volume.restrict (Set.Ico (0 : ℝ) (1 / (p : ℝ)))) (E S) = 0 :=
        measure_mono_null hbad_sub hnull_bad
      rw [Measure.restrict_apply' measurableSet_Ico, Set.inter_eq_left.2 hEsub] at hnull_E
      exact hvolS hnull_E
    obtain ⟨t, htE, htc, hto⟩ := hne_good
    have hft : fiber t = S := htE.2
    rw [hft] at htc hto
    refine ⟨htc, ?_⟩
    intro γ₁' hγ₁' γ₂' hγ₂' hne'
    obtain ⟨γ₁, hγ₁, rfl⟩ := Finset.mem_image.1 hγ₁'
    obtain ⟨γ₂, hγ₂, rfl⟩ := Finset.mem_image.1 hγ₂'
    have hne : γ₁ ≠ γ₂ := fun h => hne' (by rw [h])
    have h0 := hto γ₁ hγ₁ γ₂ hγ₂ hne
    rw [← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    push_cast
    ring
  obtain ⟨T, hT⟩ := h4 p hp Γ' 𝒜 hΓ'card h𝒜good
  let Bad : Set ℝ := ⋃ S ∈ I.powerset.filter (fun S => volume (E S) = 0), E S
  have hBad_null : volume Bad = 0 := by
    apply measure_iUnion_null
    intro S
    apply measure_iUnion_null
    intro hS
    exact (Finset.mem_filter.1 hS).2
  let BadLift : Set (Fin 1 → ℝ) :=
    ⋃ m : ℤ, {x : Fin 1 → ℝ | x 0 - (m : ℝ) / (p : ℝ) ∈ Bad}
  have hBadLift_null : volume BadLift = 0 := by
    apply measure_iUnion_null
    intro m
    have heq : {x : Fin 1 → ℝ | x 0 - (m : ℝ) / (p : ℝ) ∈ Bad} =
        {x : Fin 1 → ℝ | x 0 ∈ (fun u : ℝ => u - (m : ℝ) / (p : ℝ)) ⁻¹' Bad} := rfl
    rw [heq, volume_preimage_apply0]
    have hsub : (fun u : ℝ => u - (m : ℝ) / (p : ℝ)) ⁻¹' Bad =
        (fun u : ℝ => u + -((m : ℝ) / (p : ℝ))) ⁻¹' Bad := by
      ext u; simp [sub_eq_add_neg]
    rw [hsub, measure_preimage_add_right, hBad_null]
  let Tℝ : Set (Fin 1 → ℝ) := (fun n : ℤ => (fun _ : Fin 1 => (n : ℝ) / (p : ℝ))) '' T
  refine ⟨Tℝ, (Set.to_countable T).image _, ?_, ?_⟩
  · apply measure_mono_null _ hBadLift_null
    intro x hx
    simp only [Set.mem_sdiff, Set.mem_univ, true_and, Set.mem_iUnion] at hx
    set m : ℤ := ⌊(p : ℝ) * x 0⌋
    set t : ℝ := x 0 - (m : ℝ) / (p : ℝ)
    have ht : t ∈ Set.Ico (0 : ℝ) (1 / (p : ℝ)) := by
      have hfl : (m : ℝ) ≤ (p : ℝ) * x 0 ∧ (p : ℝ) * x 0 < (m : ℝ) + 1 :=
        ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
      constructor
      · have : 0 ≤ (p : ℝ) * x 0 - (m : ℝ) := by linarith
        have h2 : t = ((p : ℝ) * x 0 - (m : ℝ)) / (p : ℝ) := by
          dsimp only [t]; field_simp [hpne]
        rw [h2]; exact div_nonneg this hppos.le
      · have : (p : ℝ) * x 0 - (m : ℝ) < 1 := by linarith
        have h2 : t = ((p : ℝ) * x 0 - (m : ℝ)) / (p : ℝ) := by
          dsimp only [t]; field_simp [hpne]
        rw [h2]; exact (div_lt_div_iff_of_pos_right hppos).2 this
    refine Set.mem_iUnion.2 ⟨m, ?_⟩
    show t ∈ Bad
    by_contra htnot
    have hmemA : fiber t ∈ 𝒜 := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro hv0
      apply htnot
      exact Set.mem_biUnion (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.filter_subset _ _), hv0⟩)
        ⟨ht, rfl⟩
    obtain ⟨⟨⟨k, hk⟩, ⟨n, hn⟩⟩, hkn, _⟩ := hT (fiber t) hmemA m
    apply hx
    refine ⟨fun _ => (n : ℝ) / (p : ℝ), ⟨n, hn, rfl⟩, ?_⟩
    simp only [translateSet, Set.mem_ofPred_eq]
    have hxsub : (x - fun _ : Fin 1 => (n : ℝ) / (p : ℝ)) =
        fun _ : Fin 1 => t + (k : ℝ) / (p : ℝ) := by
      ext i; fin_cases i
      have hknR : (k : ℝ) + (n : ℝ) = (m : ℝ) := by exact_mod_cast hkn
      simp only [Pi.sub_apply, t]
      have : x 0 - (n : ℝ) / (p : ℝ) = x 0 - (m : ℝ) / (p : ℝ) + (k : ℝ) / (p : ℝ) := by
        field_simp [hpne]; linarith
      exact this
    rw [hxsub]
    exact (Finset.mem_filter.1 hk).2
  · intro τ₁ τ₂ hτ₁ hτ₂ hne
    obtain ⟨n₁, hn₁, rfl⟩ := hτ₁
    obtain ⟨n₂, hn₂, rfl⟩ := hτ₂
    have hn_ne : n₁ ≠ n₂ := fun h => hne (by rw [h])
    apply measure_mono_null _ hBadLift_null
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := hx
    simp only [translateSet, Set.mem_ofPred_eq] at hx₁ hx₂
    set m : ℤ := ⌊(p : ℝ) * x 0⌋
    set t : ℝ := x 0 - (m : ℝ) / (p : ℝ)
    have ht : t ∈ Set.Ico (0 : ℝ) (1 / (p : ℝ)) := by
      have hfl : (m : ℝ) ≤ (p : ℝ) * x 0 ∧ (p : ℝ) * x 0 < (m : ℝ) + 1 :=
        ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
      constructor
      · have : 0 ≤ (p : ℝ) * x 0 - (m : ℝ) := by linarith
        have h2 : t = ((p : ℝ) * x 0 - (m : ℝ)) / (p : ℝ) := by
          dsimp only [t]; field_simp [hpne]
        rw [h2]; exact div_nonneg this hppos.le
      · have : (p : ℝ) * x 0 - (m : ℝ) < 1 := by linarith
        have h2 : t = ((p : ℝ) * x 0 - (m : ℝ)) / (p : ℝ) := by
          dsimp only [t]; field_simp [hpne]
        rw [h2]; exact (div_lt_div_iff_of_pos_right hppos).2 this
    refine Set.mem_iUnion.2 ⟨m, ?_⟩
    show t ∈ Bad
    by_contra htnot
    have hmemA : fiber t ∈ 𝒜 := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro hv0
      apply htnot
      exact Set.mem_biUnion (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.filter_subset _ _), hv0⟩)
        ⟨ht, rfl⟩
    have hmem1 : m - n₁ ∈ fiber t := by
      have hx1' : (fun _ : Fin 1 => t + ((m - n₁ : ℤ) : ℝ) / (p : ℝ)) ∈ Ω := by
        convert hx₁ using 1
        ext i; fin_cases i
        simp only [Pi.sub_apply, t]; push_cast; ring
      exact Finset.mem_filter.2 ⟨hmemI t (m - n₁) ht hx1', hx1'⟩
    have hmem2 : m - n₂ ∈ fiber t := by
      have hx2' : (fun _ : Fin 1 => t + ((m - n₂ : ℤ) : ℝ) / (p : ℝ)) ∈ Ω := by
        convert hx₂ using 1
        ext i; fin_cases i
        simp only [Pi.sub_apply, t]; push_cast; ring
      exact Finset.mem_filter.2 ⟨hmemI t (m - n₂) ht hx2', hx2'⟩
    obtain ⟨_, _, huniq⟩ := hT (fiber t) hmemA m
    have e1 := huniq (⟨m - n₁, hmem1⟩, ⟨n₁, hn₁⟩) (by simp)
    have e2 := huniq (⟨m - n₂, hmem2⟩, ⟨n₂, hn₂⟩) (by simp)
    have e12 := e1.trans e2.symm
    have heqn : n₁ = n₂ := congrArg (fun q : {k // k ∈ fiber t} × {t // t ∈ T} => q.2.1) e12
    exact hn_ne heqn

/- Part 4: Main reduction theorem -/

theorem main : H1 → H2 → H3 → H4 → type_of% @Fuglede.FugledeConjecture.variants.dim_1 := by
  intro h1 h2 h3 h4
  refine unit_measure_reduction fun Ω hbdd hmeas hvol => ?_
  exact ⟨spectral_to_tiling_unit h3 h4 Ω hbdd hmeas hvol,
    tiling_to_spectral_unit h1 h2 Ω hbdd hmeas hvol⟩

end OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1
