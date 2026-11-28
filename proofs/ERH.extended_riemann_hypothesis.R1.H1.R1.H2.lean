import OMAReductions.R_ERH_extended_riemann_hypothesis_R1_H1_R1
import Mathlib

-- Credit: @deepqntm

/-!
# Mellin inversion and reciprocal scales for the Dedekind theta kernel

For any real `σ > 1`, pointwise Mellin inversion identifies the inverse transform of
the completed Dedekind series on the line `Re s = σ` with the centered ideal-class theta
sum. Its constant term is the class number times `2^(r₁+r₂) R_K / w_K`. The trace-dual
involution on ideal classes and Poisson summation then give the reciprocal-scale
identity for the line `σ = 2` specified in the problem.

The arithmetic and theta lemmas are ported from AxiomMath/DedekindZetaZeroFree,
revision 15f9d0d31f2336fbc38f8c111e8d3b46e337bfe4. They include attributed work
from the FLT Project and LeanPool/lean-pool, revision
68aa6ee63d20ad76bcc15f595adfc72949991f06. This file incorporates the local
port to the pinned Mathlib and retains its source notices and Apache-2.0 license.
The estimates for the gamma factors adapt the local Mellin-inversion proof,
which credits @STARDUSTLC666 for the gamma estimates in the quadratic cases.
-/

/- Source module: DedekindZetaZeroFree.Arithmetic.Units.FundamentalDomainIntegration -/

section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Mechanical port of `LeanPool/Odlyzko/CompletedZeta/UnitFundamentalDomain.lean`
from https://github.com/LeanPool/lean-pool at exact revision
`68aa6ee63d20ad76bcc15f595adfc72949991f06` (Lean 4.35.0-rc3, ported to rc2).
Original copyright and author attribution are retained above. Released under
Apache 2.0; the full license is in the repository root `LICENSE`.
The only source changes are imports, module visibility syntax, and namespace.
-/

noncomputable section

open Finset MeasureTheory Module NumberField NumberField.InfinitePlace
  NumberField.Units Set dirichletUnitTheorem

namespace DedekindZetaZeroFree.Theta

open mixedEmbedding mixedEmbedding.fundamentalCone

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in

abbrev unitFundamentalParamSet (K : Type*) [Field K] [NumberField K] :
    Set (realSpace K) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.univ else Set.Ico 0 1

theorem measurableSet_unitFundamentalParamSet :
    MeasurableSet (unitFundamentalParamSet K) := by
  classical
  refine MeasurableSet.univ_pi fun _ ↦ ?_
  split_ifs
  · simp
  · simp

theorem mem_unitFundamentalParamSet_iff
    (x : realSpace K) :
    x ∈ unitFundamentalParamSet K ↔
      ∀ w, w ≠ w₀ → x w ∈ Set.Ico 0 1 := by simp

open scoped Classical in
open scoped Classical in
open scoped Classical in

def unitFloor (x : realSpace K) : InfinitePlace K → ℤ :=
  fun w ↦ if w = w₀ then 0 else ⌊x w⌋

open scoped Classical in

def unitCoordinateShift
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) : realSpace K :=
  fun w ↦ if hw : w = w₀ then 0 else z ⟨w, hw⟩

open scoped Classical in

def fundamentalUnitForShift
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) : (𝓞 K)ˣ :=
  ∏ i, fundSystem K (equivFinRank.symm i) ^ z i

theorem expMapBasis_add_unitCoordinateShift
    (x : realSpace K) (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    expMapBasis (x + unitCoordinateShift z) =
      (fun w ↦ w (fundamentalUnitForShift z)) * expMapBasis x := by
  classical
  ext w
  rw [expMapBasis_apply', expMapBasis_apply']
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  have hradial :
      (x + unitCoordinateShift z) w₀ = x w₀ := by
    simp [unitCoordinateShift]
  have hcoord (i : {w : InfinitePlace K // w ≠ w₀}) :
      (x + unitCoordinateShift z) i = x i + (z i : ℝ) := by
    simp [unitCoordinateShift, i.prop]
  have hrpow (i : {w : InfinitePlace K // w ≠ w₀}) :
      w (fundSystem K (equivFinRank.symm i)) ^
          (x i + (z i : ℝ)) =
        w (fundSystem K (equivFinRank.symm i)) ^ x i *
          w (fundSystem K (equivFinRank.symm i)) ^ z i := by
    rw [Real.rpow_add_intCast]
    simp
  rw [hradial]
  simp_rw [hcoord, hrpow]
  rw [Finset.prod_mul_distrib]
  have hunit :
      w (fundamentalUnitForShift z) =
        ∏ i, w (fundSystem K (equivFinRank.symm i)) ^ z i := by
    rw [fundamentalUnitForShift, Units.coe_prod, map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro i _
    cases z i <;> simp [zpow_negSucc, map_inv₀]
  grind

open scoped Classical in
open scoped Classical in

def unitFundamentalTranslate
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) : Set (realSpace K) :=
  (fun x ↦ x - unitCoordinateShift z) ⁻¹' unitFundamentalParamSet K

theorem measurableSet_unitFundamentalTranslate
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    MeasurableSet (unitFundamentalTranslate z) :=
  (measurable_id.sub_const _)
    measurableSet_unitFundamentalParamSet

theorem mem_unitFundamentalTranslate_iff
    (x : realSpace K) (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    x ∈ unitFundamentalTranslate z ↔
      (fun i : {w : InfinitePlace K // w ≠ w₀} ↦ unitFloor x i) = z := by
  rw [unitFundamentalTranslate, Set.mem_preimage,
    mem_unitFundamentalParamSet_iff]
  constructor
  · intro hx
    funext i
    have hi := hx i i.prop
    have hi' : x i - (z i : ℝ) ∈ Set.Ico 0 1 := by
      simpa [unitCoordinateShift, i.prop] using hi
    have hfloor :
        ⌊x i - (z i : ℝ)⌋ = 0 :=
      Int.floor_eq_zero_iff.mpr hi'
    simp only [Int.floor_sub_intCast] at hfloor
    simpa [unitFloor, i.prop] using sub_eq_zero.mp hfloor
  · intro hz w hw
    have hfloor := congr_fun hz ⟨w, hw⟩
    have hfloor' : ⌊x w⌋ = z ⟨w, hw⟩ := by
      simpa [unitFloor, hw] using hfloor
    have hshift :
        unitCoordinateShift z w = (z ⟨w, hw⟩ : ℝ) := by
      simp [unitCoordinateShift, hw]
    simp only [Pi.sub_apply, hshift]
    rw [← hfloor']
    simpa only [Int.fract] using
      (show Int.fract (x w) ∈ Set.Ico (0 : ℝ) 1 from
        ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)

theorem pairwise_disjoint_unitFundamentalTranslate :
    Pairwise fun (z z' : {w : InfinitePlace K // w ≠ w₀} → ℤ) ↦
      Disjoint (unitFundamentalTranslate z) (unitFundamentalTranslate z') := by
  intro z z' hne
  rw [Set.disjoint_left]
  intro x hx hx'
  have hz := (mem_unitFundamentalTranslate_iff x z).mp hx
  have hz' := (mem_unitFundamentalTranslate_iff x z').mp hx'
  simp_all

theorem iUnion_unitFundamentalTranslate :
    ⋃ z : {w : InfinitePlace K // w ≠ w₀} → ℤ,
      unitFundamentalTranslate z = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨fun i ↦ unitFloor x i,
    (mem_unitFundamentalTranslate_iff _ _).mpr rfl⟩

theorem unitFundamentalTranslate_eq_image
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    unitFundamentalTranslate z =
      (fun x ↦ x + unitCoordinateShift z) '' unitFundamentalParamSet K := by
  ext x
  constructor
  · intro hx
    refine ⟨x - unitCoordinateShift z, hx, ?_⟩
    simp
  · rintro ⟨y, hy, rfl⟩
    simpa [unitFundamentalTranslate] using hy

theorem setIntegral_unitFundamentalTranslate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : realSpace K → E)
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    (∫ x in unitFundamentalTranslate z, f x) =
      ∫ x in unitFundamentalParamSet K,
        f (x + unitCoordinateShift z) := by
  rw [unitFundamentalTranslate_eq_image]
  let e : realSpace K ≃ᵐ realSpace K :=
    MeasurableEquiv.addRight (unitCoordinateShift z)
  have he : MeasurePreserving e volume volume :=
    ⟨e.measurable, by
      simpa [e] using
        (map_add_right_eq_self volume (unitCoordinateShift z))⟩
  exact he.setIntegral_image_emb e.measurableEmbedding f
    (unitFundamentalParamSet K)

theorem integral_eq_tsum_setIntegral_unitFundamentalTranslate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : realSpace K → E) (hf : Integrable f) :
    (∫ x, f x) =
      ∑' z : {w : InfinitePlace K // w ≠ w₀} → ℤ,
        ∫ x in unitFundamentalTranslate z, f x := by
  calc
    (∫ x, f x) =
        ∫ x in ⋃ z : {w : InfinitePlace K // w ≠ w₀} → ℤ,
          unitFundamentalTranslate z, f x := by
      rw [iUnion_unitFundamentalTranslate, setIntegral_univ]
    _ = _ := integral_iUnion measurableSet_unitFundamentalTranslate
      pairwise_disjoint_unitFundamentalTranslate (by
        rw [iUnion_unitFundamentalTranslate]
        simp_all)

theorem integral_eq_tsum_setIntegral_add_unitCoordinateShift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : realSpace K → E) (hf : Integrable f) :
    (∫ x, f x) =
      ∑' z : {w : InfinitePlace K // w ≠ w₀} → ℤ,
        ∫ x in unitFundamentalParamSet K,
          f (x + unitCoordinateShift z) := by
  rw [integral_eq_tsum_setIntegral_unitFundamentalTranslate f hf]
  congr 1
  funext z
  exact setIntegral_unitFundamentalTranslate f z

open scoped Classical in
theorem setIntegral_expMapBasis_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set (realSpace K)} (hs : MeasurableSet s)
    (f : realSpace K → E) :
    (∫ q in expMapBasis '' s, f q) =
      ∫ x in s,
        (Real.exp (x w₀ * Module.finrank ℚ K) *
          (∏ w : {w : InfinitePlace K // IsComplex w},
            expMapBasis x w.1)⁻¹ *
          2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K * regulator K) •
            f (expMapBasis x) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun x _ ↦ (hasFDerivAt_expMapBasis K x).hasFDerivWithinAt)
    (injective_expMapBasis K).injOn]
  apply setIntegral_congr_fun hs
  intro x _
  change |(fderiv_expMapBasis K x).det| • f (expMapBasis x) = _
  rw [abs_det_fderiv_expMapBasis]

open scoped Classical in
theorem integrableOn_expMapBasis_image_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set (realSpace K)} (hs : MeasurableSet s)
    (f : realSpace K → E) :
    IntegrableOn f (expMapBasis '' s) ↔
      IntegrableOn
        (fun x ↦
          (Real.exp (x w₀ * Module.finrank ℚ K) *
            (∏ w : {w : InfinitePlace K // IsComplex w},
              expMapBasis x w.1)⁻¹ *
            2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K * regulator K) •
              f (expMapBasis x))
        s := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (fun x _ ↦ (hasFDerivAt_expMapBasis K x).hasFDerivWithinAt)
    (injective_expMapBasis K).injOn]
  apply integrableOn_congr_fun _ hs
  intro x _
  dsimp only
  rw [abs_det_fderiv_expMapBasis]

end DedekindZetaZeroFree.Theta

end

end

/- Source module: DedekindZetaZeroFree.HarmonicAnalysis.Poisson.GaussianLattice -/

section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Vendored from https://github.com/LeanPool/lean-pool,
commit 68aa6ee63d20ad76bcc15f595adfc72949991f06.
Original source: LeanPool/Odlyzko/Theta/PoissonSummation.lean (1,335 lines).
Port to Lean 4.35.0-rc2: namespace and local imports renamed;
upstream module visibility syntax removed. Original proofs retained.
The full upstream Apache-2.0 license is included in the repository root LICENSE.
-/

noncomputable section

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {ι : Type*}

def torusQuotientMap (x : ι → ℝ) : UnitAddTorus ι :=
  fun i ↦ (x i : UnitAddCircle)

theorem isOpenQuotientMap_torusQuotientMap :
    IsOpenQuotientMap (torusQuotientMap : (ι → ℝ) → UnitAddTorus ι) := by
  change IsOpenQuotientMap
    (Pi.map fun _ : ι ↦ ((↑) : ℝ → UnitAddCircle))
  exact IsOpenQuotientMap.piMap fun _ ↦
    QuotientAddGroup.isOpenQuotientMap_mk

theorem surjective_torusQuotientMap :
    Function.Surjective
      (torusQuotientMap : (ι → ℝ) → UnitAddTorus ι) :=
  isOpenQuotientMap_torusQuotientMap.surjective

theorem exists_intPi_add_of_torusQuotientMap_eq
    {x y : ι → ℝ} (h : torusQuotientMap x = torusQuotientMap y) :
    ∃ n : ι → ℤ, y = x + fun i ↦ (n i : ℝ) := by
  classical
  have hi (i : ι) :
      ∃ n : ℤ, y i = x i + (n : ℝ) := by
    have hz : ((y i - x i : ℝ) : UnitAddCircle) = 0 := by
      change (y i : UnitAddCircle) - (x i : UnitAddCircle) = 0
      rw [sub_eq_zero]
      exact (congrFun h i).symm
    obtain ⟨n, hn⟩ :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    grind
  choose n hn using hi
  exact ⟨n, funext hn⟩

theorem torusQuotientMap_add_intPi
    (x : ι → ℝ) (n : ι → ℤ) :
    torusQuotientMap (x + fun i ↦ (n i : ℝ)) =
      torusQuotientMap x := by
  ext i
  simp [torusQuotientMap]

noncomputable def intPeriodization (f : (ι → ℝ) → ℂ) (x : ι → ℝ) : ℂ :=
  ∑' n : ι → ℤ, f (x + fun i ↦ (n i : ℝ))

theorem intPeriodization_add_intPi
    (f : (ι → ℝ) → ℂ) (x : ι → ℝ) (k : ι → ℤ) :
    intPeriodization f (x + fun i ↦ (k i : ℝ)) =
      intPeriodization f x := by
  unfold intPeriodization
  calc
    (∑' n : ι → ℤ,
        f ((x + fun i ↦ (k i : ℝ)) + fun i ↦ (n i : ℝ))) =
        ∑' n : ι → ℤ,
          f (x + fun i ↦ ((k + n) i : ℝ)) := by
      apply tsum_congr
      intro n
      congr 1
      funext i
      simp [add_assoc]
    _ = ∑' n : ι → ℤ, f (x + fun i ↦ (n i : ℝ)) :=
      Equiv.tsum_eq (Equiv.addLeft k)
        (fun n : ι → ℤ ↦ f (x + fun i ↦ (n i : ℝ)))

theorem intPeriodization_eq_of_torusQuotientMap_eq
    (f : (ι → ℝ) → ℂ) {x y : ι → ℝ}
    (h : torusQuotientMap x = torusQuotientMap y) :
    intPeriodization f x = intPeriodization f y := by
  obtain ⟨n, rfl⟩ := exists_intPi_add_of_torusQuotientMap_eq h
  exact (intPeriodization_add_intPi f x n).symm

noncomputable def torusLift {A : Type*} (f : (ι → ℝ) → A) :
    UnitAddTorus ι → A :=
  fun x ↦ f (Function.surjInv surjective_torusQuotientMap x)

theorem torusLift_comp_torusQuotientMap {A : Type*}
    (f : (ι → ℝ) → A)
    (hf : ∀ x y, torusQuotientMap x = torusQuotientMap y → f x = f y) :
    torusLift f ∘ torusQuotientMap = f := by
  funext x
  apply hf
  exact Function.rightInverse_surjInv
    surjective_torusQuotientMap (torusQuotientMap x)

theorem continuous_torusLift {A : Type*} [TopologicalSpace A]
    (f : (ι → ℝ) → A) (hfc : Continuous f)
    (hf : ∀ x y, torusQuotientMap x = torusQuotientMap y → f x = f y) :
    Continuous (torusLift f) := by
  apply isOpenQuotientMap_torusQuotientMap.continuous_comp_iff.mp
  simpa [torusLift_comp_torusQuotientMap f hf] using hfc

noncomputable def torusContinuousMap {A : Type*} [TopologicalSpace A]
    (f : (ι → ℝ) → A) (hfc : Continuous f)
    (hf : ∀ x y, torusQuotientMap x = torusQuotientMap y → f x = f y) :
    C(UnitAddTorus ι, A) :=
  ⟨torusLift f, continuous_torusLift f hfc hf⟩

@[simp]
theorem torusContinuousMap_comp_torusQuotientMap
    {A : Type*} [TopologicalSpace A]
    (f : (ι → ℝ) → A) (hfc : Continuous f)
    (hf : ∀ x y, torusQuotientMap x = torusQuotientMap y → f x = f y)
    (x : ι → ℝ) :
    torusContinuousMap f hfc hf (torusQuotientMap x) = f x :=
  congrFun (torusLift_comp_torusQuotientMap f hf) x

noncomputable def torusPeriodization
    (f : (ι → ℝ) → ℂ) (hf : Continuous (intPeriodization f)) :
    C(UnitAddTorus ι, ℂ) :=
  torusContinuousMap (intPeriodization f) hf
    (fun _x _y h ↦ intPeriodization_eq_of_torusQuotientMap_eq f h)

@[simp]
theorem torusPeriodization_apply_quotient
    (f : (ι → ℝ) → ℂ) (hf : Continuous (intPeriodization f))
    (x : ι → ℝ) :
    torusPeriodization f hf (torusQuotientMap x) =
      intPeriodization f x :=
  torusContinuousMap_comp_torusQuotientMap _ _ _ x

end DedekindZetaZeroFree.AbelianQuotient.Theta

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {ι : Type*} [Fintype ι]

theorem mFourier_torusQuotientMap
    (n : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier n (torusQuotientMap x) =
      Complex.exp (2 * Real.pi * Complex.I *
        ∑ i, (n i : ℂ) * (x i : ℂ)) := by
  simp only [UnitAddTorus.mFourier, torusQuotientMap,
    ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum]
  push_cast
  rw [Finset.mul_sum]
  ring_nf

theorem mFourier_neg_torusQuotientMap
    (n : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier (-n) (torusQuotientMap x) =
      Complex.exp (-2 * Real.pi * Complex.I *
        ∑ i, (n i : ℂ) * (x i : ℂ)) := by
  rw [mFourier_torusQuotientMap]
  simp

@[simp]
theorem norm_mFourier_torusQuotientMap
    (n : ι → ℤ) (x : ι → ℝ) :
    ‖UnitAddTorus.mFourier n (torusQuotientMap x)‖ = 1 := by
  simp only [UnitAddTorus.mFourier, torusQuotientMap,
    ContinuousMap.coe_mk, norm_prod, fourier_coe_apply]
  apply Finset.prod_eq_one
  intro i _
  rw [Complex.norm_exp]
  simp

end DedekindZetaZeroFree.AbelianQuotient.Theta

section

open Module Submodule
open scoped RealInnerProductSpace

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {E : Type*} [NormedAddCommGroup E]

theorem innerBilin_nondegenerate [InnerProductSpace ℝ E] :
    (innerₗ E).Nondegenerate := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)

noncomputable def dualRealBasis [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    Basis ι ℝ E :=
  LinearMap.BilinForm.dualBasis (innerₗ E) innerBilin_nondegenerate
    (b.ofZLatticeBasis ℝ L)

theorem inner_dualRealBasis_apply [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℤ L)
    (i : ι) (x : E) :
    inner ℝ (dualRealBasis L b i) x =
      (b.ofZLatticeBasis ℝ L).repr x i := by
  change (innerₗ E) (dualRealBasis L b i) x = _
  simp [dualRealBasis, LinearMap.BilinForm.dualBasis,
    Basis.coe_dualBasis]

noncomputable def dualLattice [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (innerₗ E) L

theorem mem_dualLattice_iff [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (y : E) :
    y ∈ dualLattice L ↔ ∀ x : L, ∃ n : ℤ, inner ℝ y (x : E) = n := by
  constructor
  · intro hy x
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp (hy x x.2)
    exact ⟨n, hn.symm⟩
  · intro hy x hx
    obtain ⟨n, hn⟩ := hy ⟨x, hx⟩
    simp_all

theorem span_range_dualRealBasis [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    span ℤ (Set.range (dualRealBasis L b)) = dualLattice L := by
  unfold dualLattice dualRealBasis
  calc
    span ℤ (Set.range (LinearMap.BilinForm.dualBasis (innerₗ E)
      innerBilin_nondegenerate (b.ofZLatticeBasis ℝ L))) =
        LinearMap.BilinForm.dualSubmodule (innerₗ E)
          (span ℤ (Set.range (b.ofZLatticeBasis ℝ L))) :=
      (LinearMap.BilinForm.dualSubmodule_span_of_basis
        (innerₗ E) innerBilin_nondegenerate (b.ofZLatticeBasis ℝ L)).symm
    _ = LinearMap.BilinForm.dualSubmodule (innerₗ E) L := by
      rw [b.ofZLatticeBasis_span ℝ]

instance dualLattice.instDiscreteTopology [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    DiscreteTopology (dualLattice L) := by
  classical
  rw [← span_range_dualRealBasis L (Free.chooseBasis ℤ L)]
  infer_instance

noncomputable def dualLatticeBasis [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    Basis ι ℤ (dualLattice L) :=
  ((dualRealBasis L b).restrictScalars ℤ).map
    (LinearEquiv.ofEq _ _ (span_range_dualRealBasis L b))

@[simp]
theorem dualLatticeBasis_apply_coe [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℤ L)
    (i : ι) :
    ((dualLatticeBasis L b i : dualLattice L) : E) =
      dualRealBasis L b i := by
  rw [dualLatticeBasis, Basis.map_apply]
  simp

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Filter Asymptotics
open scoped Topology

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def latticeGaussian (a : ℝ) (x : E) : ℂ :=
  Complex.exp (-(a : ℂ) * (‖x‖ : ℂ) ^ 2)

theorem norm_latticeGaussian (a : ℝ) (x : E) :
    ‖latticeGaussian a x‖ = Real.exp (-a * ‖x‖ ^ 2) := by
  have hvalue :
      latticeGaussian a x =
        ((Real.exp (-a * ‖x‖ ^ 2) : ℝ) : ℂ) := by
    unfold latticeGaussian
    simp
  rw [hvalue, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

theorem norm_latticeGaussian_add_le
    {a : ℝ} (ha : 0 ≤ a) (y z : E) :
    ‖latticeGaussian a (y + z)‖ ≤
      Real.exp (a * ‖y‖ ^ 2) * ‖latticeGaussian (a / 2) z‖ := by
  rw [norm_latticeGaussian, norm_latticeGaussian, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have htri : ‖z‖ ≤ ‖y + z‖ + ‖y‖ := by
    calc
      ‖z‖ = ‖(y + z) - y‖ := by simp
      _ ≤ ‖y + z‖ + ‖y‖ := norm_sub_le _ _
  have hsquare :
      ‖z‖ ^ 2 ≤ 2 * ‖y + z‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖y + z‖ - ‖y‖),
      norm_nonneg z, norm_nonneg (y + z), norm_nonneg y]
  nlinarith

theorem summable_latticeGaussian [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Summable (fun x : L ↦ latticeGaussian a (x : E)) := by
  let r : ℝ := -(Module.finrank ℤ L + 1)
  have hr : r < -(Module.finrank ℤ L : ℝ) := by grind
  have hclosed : IsClosed (L : Set E) :=
    by
      change IsClosed (L.toAddSubgroup : Set E)
      exact AddSubgroup.isClosed_of_discrete
  have htend :
      Tendsto (norm ∘ ((↑) : L → E)) cofinite atTop :=
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding
      hclosed.isClosedEmbedding_subtypeVal
  have hdecay :=
    (rexp_neg_quadratic_isLittleO_rpow_atTop
      (a := -a) (b := 0) (by grind) r).isBigO.comp_tendsto htend
  have hreal :
      Summable (fun x : L ↦ Real.exp (-a * ‖(x : E)‖ ^ 2)) := by
    obtain ⟨c, hc, hbound⟩ := hdecay.exists_pos
    apply ((ZLattice.summable_norm_rpow L r hr).mul_left c).of_norm_bounded_eventually
    filter_upwards [hbound.bound] with x hx
    simpa [Function.comp_apply, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hx
  apply hreal.of_norm_bounded
  intro x
  rw [norm_latticeGaussian]

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Module

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def latticeTheta
    (L : Submodule ℤ E) (a : ℝ) : ℂ :=
  ∑' x : L, latticeGaussian a (x : E)

theorem latticeTheta_map_linearIsometryEquiv [NormedSpace ℝ E]
    (L : Submodule ℤ E) (e : E ≃ₗᵢ[ℝ] E) (a : ℝ) :
    latticeTheta
        (L.map (e.toLinearEquiv.restrictScalars ℤ).toLinearMap) a =
      latticeTheta L a := by
  let eZ : E ≃ₗ[ℤ] E := e.toLinearEquiv.restrictScalars ℤ
  let eL :
      L ≃ₗ[ℤ] L.map eZ.toLinearMap :=
    Submodule.equivMapOfInjective eZ.toLinearMap eZ.injective L
  rw [latticeTheta, latticeTheta, ← eL.toEquiv.tsum_eq]
  apply tsum_congr
  intro x
  unfold latticeGaussian
  rw [show ((eL.toEquiv x : L.map eZ.toLinearMap) : E) = e x by rfl,
    e.norm_map]

theorem summable_latticeTheta [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Summable (fun x : L ↦ latticeGaussian a (x : E)) :=
  summable_latticeGaussian L ha

noncomputable def dualLatticeTheta [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (a : ℝ) : ℂ :=
  latticeTheta (dualLattice L) a

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Module
open scoped RealInnerProductSpace

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {E : Type*} [NormedAddCommGroup E] {ι : Type*} [Fintype ι]

noncomputable def latticePoint (L : Submodule ℤ E) (b : Basis ι ℤ L) (n : ι → ℤ) : E :=
  (b.equivFun.symm n : L)

noncomputable def dualLatticePoint [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [DecidableEq ι]
    (b : Basis ι ℤ L) (n : ι → ℤ) : E :=
  ((dualLatticeBasis L b).equivFun.symm n : dualLattice L)

theorem inner_dualLatticePoint_ofZLatticeBasis_equivFun_symm
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [DecidableEq ι]
    (b : Basis ι ℤ L) (n : ι → ℤ) (x : ι → ℝ) :
    inner ℝ (dualLatticePoint L b n)
        ((b.ofZLatticeBasis ℝ L).equivFun.symm x) =
      ∑ i, (n i : ℝ) * x i := by
  rw [dualLatticePoint, Basis.equivFun_symm_apply]
  have hn :
      ((↑(∑ i, n i • dualLatticeBasis L b i) :
          dualLattice L) : E) =
        ∑ i, (n i : ℝ) • dualRealBasis L b i := by
    change (dualLattice L).subtype
      (∑ i, n i • dualLatticeBasis L b i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul]
    have hd :
        (dualLattice L).subtype (dualLatticeBasis L b i) =
          dualRealBasis L b i :=
      dualLatticeBasis_apply_coe L b i
    rw [hd]
    exact (Int.cast_smul_eq_zsmul ℝ (n i)
      (dualRealBasis L b i)).symm
  rw [hn, sum_inner]
  have hrepr (i : ι) :
      (b.ofZLatticeBasis ℝ L).repr
          ((b.ofZLatticeBasis ℝ L).equivFun.symm x) i = x i := by
    change (b.ofZLatticeBasis ℝ L).equivFun
      ((b.ofZLatticeBasis ℝ L).equivFun.symm x) i = x i
    rw [LinearEquiv.apply_symm_apply]
  simp_rw [real_inner_smul_left,
    inner_dualRealBasis_apply, hrepr]

theorem latticeTheta_eq_tsum_coordinates
    (L : Submodule ℤ E) (b : Basis ι ℤ L) (a : ℝ) :
    latticeTheta L a =
      ∑' n : ι → ℤ, latticeGaussian a (latticePoint L b n) := by
  symm
  simpa [latticeTheta, latticePoint] using
    (Equiv.tsum_eq b.equivFun.toEquiv.symm
      (fun x : L ↦ latticeGaussian a (x : E)))

theorem dualLatticeTheta_eq_tsum_coordinates
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [DecidableEq ι]
    (b : Basis ι ℤ L) (a : ℝ) :
    dualLatticeTheta L a =
      ∑' n : ι → ℤ, latticeGaussian a (dualLatticePoint L b n) := by
  symm
  simpa [dualLatticeTheta, latticeTheta, dualLatticePoint] using
    (Equiv.tsum_eq (dualLatticeBasis L b).equivFun.toEquiv.symm
      (fun x : dualLattice L ↦ latticeGaussian a (x : E)))

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Module

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {E : Type*} [NormedAddCommGroup E] {ι : Type*} [Fintype ι]

noncomputable def coordinateGaussian [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (x : ι → ℝ) : ℂ :=
  latticeGaussian a ((b.ofZLatticeBasis ℝ L).equivFun.symm x)

noncomputable def coordinateBasisMap [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) :
    C(ι → ℝ, E) :=
  let e := LinearEquiv.toContinuousLinearEquiv
    (b.ofZLatticeBasis ℝ L).equivFun.symm
  ⟨e, e.continuous⟩

theorem continuous_coordinateGaussian [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) :
    Continuous (coordinateGaussian L b a) := by
  classical
  unfold coordinateGaussian latticeGaussian
  have hlin : Continuous fun x : ι → ℝ ↦
      (b.ofZLatticeBasis ℝ L).equivFun.symm x :=
    (LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm).continuous
  fun_prop

theorem ofZLatticeBasis_equivFun_symm_intCast
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (n : ι → ℤ) :
    (b.ofZLatticeBasis ℝ L).equivFun.symm (fun i ↦ (n i : ℝ)) =
      latticePoint L b n := by
  rw [Basis.equivFun_symm_apply, latticePoint,
    Basis.equivFun_symm_apply]
  have hcoe :
      ((↑(∑ i, n i • b i) : L) : E) =
        ∑ i, n i • (b i : E) := by simp
  rw [hcoe]
  apply Finset.sum_congr rfl
  intro i _
  rw [Basis.ofZLatticeBasis_apply]
  exact Int.cast_smul_eq_zsmul ℝ (n i) (b i : E)

noncomputable def coordinateGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (n : ι → ℤ) :
    C(ι → ℝ, ℂ) :=
  ⟨fun x ↦ coordinateGaussian L b a
      (x + fun i ↦ (n i : ℝ)),
    (continuous_coordinateGaussian L b a).comp
      (continuous_id.add (continuous_pi fun _ ↦ continuous_const))⟩

theorem summable_norm_latticeGaussian_latticePoint
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ι → ℤ ↦
      ‖latticeGaussian a (latticePoint L b n)‖) := by
  have hs := (Equiv.summable_iff
    (e := b.equivFun.toEquiv.symm)).mpr
      (summable_latticeGaussian L ha).norm
  simpa [Function.comp_def, latticePoint] using hs

theorem norm_coordinateGaussianTranslate_apply_le
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a)
    (x : ι → ℝ) (n : ι → ℤ) :
    ‖coordinateGaussianTranslate L b a n x‖ ≤
      Real.exp (a * ‖coordinateBasisMap L b x‖ ^ 2) *
        ‖latticeGaussian (a / 2) (latticePoint L b n)‖ := by
  classical
  change ‖coordinateGaussian L b a
      (x + fun i ↦ (n i : ℝ))‖ ≤ _
  have hsplit :
      (b.ofZLatticeBasis ℝ L).equivFun.symm
          (x + fun i ↦ (n i : ℝ)) =
        coordinateBasisMap L b x + latticePoint L b n := by
    rw [map_add, ofZLatticeBasis_equivFun_symm_intCast]
    rfl
  rw [coordinateGaussian, hsplit]
  exact norm_latticeGaussian_add_le ha.le _ _

theorem norm_restrict_coordinateGaussianTranslate_le
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a)
    (K : TopologicalSpace.Compacts (ι → ℝ)) (n : ι → ℤ) :
    ‖(coordinateGaussianTranslate L b a n).restrict K‖ ≤
      Real.exp (a * ‖(coordinateBasisMap L b).restrict K‖ ^ 2) *
        ‖latticeGaussian (a / 2) (latticePoint L b n)‖ := by
  classical
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.exp_pos _).le
    (norm_nonneg _))).2
  intro x
  refine (norm_coordinateGaussianTranslate_apply_le
    L b ha x n).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ ha.le
  have hx := ContinuousMap.norm_coe_le_norm
    ((coordinateBasisMap L b).restrict K) x
  change ‖coordinateBasisMap L b (x : ι → ℝ)‖ ≤
    ‖(coordinateBasisMap L b).restrict K‖ at hx
  nlinarith [norm_nonneg (coordinateBasisMap L b x),
    norm_nonneg ((coordinateBasisMap L b).restrict K)]

theorem summable_norm_restrict_coordinateGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a)
    (K : TopologicalSpace.Compacts (ι → ℝ)) :
    Summable (fun n : ι → ℤ ↦
      ‖(coordinateGaussianTranslate L b a n).restrict K‖) := by
  classical
  let C := Real.exp
    (a * ‖(coordinateBasisMap L b).restrict K‖ ^ 2)
  have hbase := summable_norm_latticeGaussian_latticePoint
    L b (half_pos ha)
  apply (hbase.mul_left C).of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_restrict_coordinateGaussianTranslate_le L b ha K n

private theorem summable_coordinateGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    Summable (coordinateGaussianTranslate L b a) := by
  classical
  apply ContinuousMap.summable_of_locally_summable_norm
  intro K
  exact summable_norm_restrict_coordinateGaussianTranslate L b ha K

theorem continuous_intPeriodization_coordinateGaussian
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    Continuous (intPeriodization (coordinateGaussian L b a)) := by
  classical
  let F := coordinateGaussianTranslate L b a
  have hF : Summable F :=
    summable_coordinateGaussianTranslate L b ha
  have hcontinuous : Continuous fun x : ι → ℝ ↦ (∑' n, F n) x :=
    (∑' n, F n).continuous
  have heval (x : ι → ℝ) :
      (∑' n, F n) x =
        intPeriodization (coordinateGaussian L b a) x := by
    calc
      (∑' n, F n) x = ∑' n, (F n) x :=
        (ContinuousMap.tsum_apply hF x).symm
      _ = intPeriodization (coordinateGaussian L b a) x := rfl
  simp_all

noncomputable def gaussianTorusPeriodization
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (ha : 0 < a) :
    C(UnitAddTorus ι, ℂ) :=
  torusPeriodization (coordinateGaussian L b a)
    (continuous_intPeriodization_coordinateGaussian L b ha)

theorem gaussianTorusPeriodization_zero
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    gaussianTorusPeriodization L b a ha 0 = latticeTheta L a := by
  classical
  rw [show (0 : UnitAddTorus ι) =
      torusQuotientMap (0 : ι → ℝ) by rfl]
  rw [gaussianTorusPeriodization,
    torusPeriodization_apply_quotient]
  unfold intPeriodization coordinateGaussian
  simp_rw [zero_add,
    ofZLatticeBasis_equivFun_symm_intCast]
  exact (latticeTheta_eq_tsum_coordinates L b a).symm

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Module Submodule MeasureTheory Set

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def coordinateIntLattice : Submodule ℤ (ι → ℝ) :=
  span ℤ (Set.range (Pi.basisFun ℝ ι))

noncomputable def coordinateIntBasis :
    Basis ι ℤ (coordinateIntLattice (ι := ι)) :=
  (Pi.basisFun ℝ ι).restrictScalars ℤ

noncomputable def coordinateIntPoint (n : ι → ℤ) :
    coordinateIntLattice (ι := ι) :=
  (coordinateIntBasis (ι := ι)).equivFun.symm n

omit [DecidableEq ι] in
@[simp]
theorem coordinateIntPoint_apply (n : ι → ℤ) (i : ι) :
    (coordinateIntPoint n : ι → ℝ) i = n i := by
  classical
  rw [coordinateIntPoint, Basis.equivFun_symm_apply]
  change (coordinateIntLattice (ι := ι)).subtype
    (∑ j, n j • coordinateIntBasis j) i = _
  rw [map_sum]
  simp_rw [map_zsmul]
  rw [Finset.sum_apply]
  have hb (j : ι) :
      (coordinateIntLattice (ι := ι)).subtype
        (coordinateIntBasis j) =
          Pi.basisFun ℝ ι j :=
    Basis.restrictScalars_apply ℤ (Pi.basisFun ℝ ι) j
  simp_rw [hb]
  simp only [Pi.basisFun_apply, Pi.smul_apply, zsmul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · simp_all
  · simp

omit [DecidableEq ι] in
theorem pi_Ioc_ae_eq_pi_Ico :
    ({x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} : Set (ι → ℝ)) =ᵐ[volume]
      {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1} := by
  have hioc :
      ({x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} : Set (ι → ℝ)) =
        Set.pi Set.univ fun _ : ι ↦ Ioc (0 : ℝ) 1 := by grind
  have hico :
      ({x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1} : Set (ι → ℝ)) =
        Set.pi Set.univ fun _ : ι ↦ Ico (0 : ℝ) 1 := by
    ext
    simp
  rw [hioc, hico, MeasureTheory.volume_pi]
  exact (Measure.pi_Ioc_ae_eq_pi_Icc.trans
    Measure.pi_Ico_ae_eq_pi_Icc.symm)

omit [DecidableEq ι] in
theorem integral_eq_tsum_integral_pi_Ico
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (f : (ι → ℝ) → A) (hf : Integrable f) :
    ∫ x, f x =
      ∑' n : ι → ℤ,
        ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ico 0 1},
          f ((fun i ↦ (n i : ℝ)) + x) := by
  classical
  let : VAddInvariantMeasure
      (span ℤ (Set.range (Pi.basisFun ℝ ι))) (ι → ℝ) volume :=
    ⟨fun c s _ ↦ measure_preimage_add volume (c : ι → ℝ) s⟩
  have hfund :=
    (ZSpan.isAddFundamentalDomain
      (Pi.basisFun ℝ ι) volume).integral_eq_tsum'' f hf
  rw [ZSpan.fundamentalDomain_pi_basisFun] at hfund
  have hset :
      (Set.pi Set.univ fun _ : ι ↦ Ico (0 : ℝ) 1) =
        {x : ι → ℝ | ∀ i, x i ∈ Ico 0 1} := by grind
  rw [hset] at hfund
  have hvadd
      (z : span ℤ (Set.range (Pi.basisFun ℝ ι)))
      (x : ι → ℝ) :
      z +ᵥ x = (z : ι → ℝ) + x := rfl
  simp_rw [hvadd] at hfund
  calc
    ∫ x, f x =
        ∑' z : coordinateIntLattice (ι := ι),
          ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ico 0 1},
            f ((z : ι → ℝ) + x) := by
      simpa [coordinateIntLattice] using hfund
    _ = ∑' n : ι → ℤ,
          ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ico 0 1},
            f ((coordinateIntPoint n : ι → ℝ) + x) := by
      exact (Equiv.tsum_eq
        (coordinateIntBasis (ι := ι)).equivFun.toEquiv.symm _).symm
    _ = _ := by
      apply tsum_congr
      intro n
      congr 1
      funext x
      congr 2
      funext i
      simp

omit [DecidableEq ι] in
theorem integral_eq_tsum_integral_pi_Ioc
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (f : (ι → ℝ) → A) (hf : Integrable f) :
    ∫ x, f x =
      ∑' n : ι → ℤ,
        ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
          f ((fun i ↦ (n i : ℝ)) + x) := by
  classical
  rw [integral_eq_tsum_integral_pi_Ico f hf]
  apply tsum_congr
  intro n
  exact setIntegral_congr_set pi_Ioc_ae_eq_pi_Ico.symm

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Module MeasureTheory Set

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {E : Type*} [NormedAddCommGroup E] {ι : Type*} [Fintype ι]

noncomputable def coordinateFourierCharacter
    (n : ι → ℤ) (x : ι → ℝ) : ℂ :=
  UnitAddTorus.mFourier (-n) (torusQuotientMap x)

private theorem continuous_coordinateFourierCharacter (n : ι → ℤ) :
    Continuous (coordinateFourierCharacter n) := by
  unfold coordinateFourierCharacter
  exact (UnitAddTorus.mFourier (-n)).continuous.comp
    (continuous_pi fun i ↦
      continuous_quotient_mk'.comp (continuous_apply i))

theorem measurableSet_pi_Ioc {κ : Type*} [Finite κ] :
    MeasurableSet {x : κ → ℝ | ∀ i, x i ∈ Ioc 0 1} := by
  let := Fintype.ofFinite κ
  rw [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have hi : Measurable (fun x : κ → ℝ ↦ x i) := measurable_pi_apply i
  exact measurableSet_Ioc.preimage hi

@[simp]
theorem norm_coordinateFourierCharacter
    (n : ι → ℤ) (x : ι → ℝ) :
    ‖coordinateFourierCharacter n x‖ = 1 :=
  norm_mFourier_torusQuotientMap (-n) x

noncomputable def coordinateFourierGaussian
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (n : ι → ℤ) (x : ι → ℝ) : ℂ :=
  coordinateFourierCharacter n x * coordinateGaussian L b a x

noncomputable def coordinateFourierGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (n k : ι → ℤ)
    (x : ι → ℝ) : ℂ :=
  coordinateFourierCharacter n x * coordinateGaussianTranslate L b a k x

theorem continuous_coordinateFourierGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (n k : ι → ℤ) :
    Continuous (coordinateFourierGaussianTranslate L b a n k) := by
  classical
  exact (continuous_coordinateFourierCharacter n).mul
    (coordinateGaussianTranslate L b a k).continuous

private theorem coordinateFourierCharacter_add_intPi
    (n k : ι → ℤ) (x : ι → ℝ) :
    coordinateFourierCharacter n ((fun i ↦ (k i : ℝ)) + x) =
      coordinateFourierCharacter n x := by
  unfold coordinateFourierCharacter
  congr 1
  rw [add_comm]
  exact torusQuotientMap_add_intPi x k

theorem coordinateFourierGaussian_add_intPi
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (n k : ι → ℤ) (x : ι → ℝ) :
    coordinateFourierGaussian L b a n
        ((fun i ↦ (k i : ℝ)) + x) =
      coordinateFourierGaussianTranslate L b a n k x := by
  classical
  rw [coordinateFourierGaussian,
    coordinateFourierGaussianTranslate,
    coordinateFourierCharacter_add_intPi]
  congr 1
  exact congrArg (coordinateGaussian L b a) (add_comm _ _)

theorem summable_integral_norm_coordinateFourierGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) (n : ι → ℤ) :
    Summable (fun k : ι → ℤ ↦
      ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
        ‖coordinateFourierGaussianTranslate L b a n k x‖) := by
  classical
  let S : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc 0 1}
  let K : TopologicalSpace.Compacts (ι → ℝ) :=
    ⟨Icc (0 : ι → ℝ) 1, isCompact_Icc⟩
  have hSK : S ⊆ K := by
    intro x hx
    exact ⟨fun i ↦ (hx i).1.le, fun i ↦ (hx i).2⟩
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_pi_Ioc
  have hKsum :=
    summable_norm_restrict_coordinateGaussianTranslate L b ha K
  have hmeasure : volume S < (⊤ : ENNReal) :=
    lt_of_le_of_lt (measure_mono hSK) K.2.measure_lt_top
  have hbound (k : ι → ℤ) :
      ∫ x in S,
          ‖coordinateFourierGaussianTranslate L b a n k x‖ ≤
        volume.real S *
          ‖(coordinateGaussianTranslate L b a k).restrict K‖ := by
    have hInt :
        IntegrableOn
          (fun x ↦ ‖coordinateFourierGaussianTranslate L b a n k x‖)
          S := by
      exact ((continuous_coordinateFourierGaussianTranslate
        L b a n k).norm.integrableOn_Icc).mono_set hSK
    have hConst :
        IntegrableOn (fun _ : ι → ℝ ↦
          ‖(coordinateGaussianTranslate L b a k).restrict K‖) S :=
      integrableOn_const (ne_of_lt hmeasure)
    calc
      ∫ x in S,
          ‖coordinateFourierGaussianTranslate L b a n k x‖ ≤
          ∫ _x in S,
            ‖(coordinateGaussianTranslate L b a k).restrict K‖ := by
        apply integral_mono_ae hInt hConst
        filter_upwards [ae_restrict_mem hS] with x hx
        rw [coordinateFourierGaussianTranslate, norm_mul,
          norm_coordinateFourierCharacter, one_mul]
        exact ContinuousMap.norm_coe_le_norm
          ((coordinateGaussianTranslate L b a k).restrict K) ⟨x, hSK hx⟩
      _ = volume.real S *
          ‖(coordinateGaussianTranslate L b a k).restrict K‖ := by simp
  apply Summable.of_nonneg_of_le
      (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) hbound
  exact hKsum.mul_left (volume.real S)

theorem integral_tsum_coordinateFourierGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) (n : ι → ℤ) :
    ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
        ∑' k : ι → ℤ,
          coordinateFourierGaussianTranslate L b a n k x =
      ∑' k : ι → ℤ,
        ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
          coordinateFourierGaussianTranslate L b a n k x := by
  classical
  symm
  apply integral_tsum_of_summable_integral_norm
  · intro k
    let S : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc 0 1}
    let K : Set (ι → ℝ) := Icc 0 1
    have hSK : S ⊆ K := fun x hx ↦
      ⟨fun i ↦ (hx i).1.le, fun i ↦ (hx i).2⟩
    exact ((continuous_coordinateFourierGaussianTranslate
      L b a n k).integrableOn_Icc).mono_set hSK
  · exact summable_integral_norm_coordinateFourierGaussianTranslate
      L b ha n

theorem mFourierCoeff_gaussianTorusPeriodization
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) (n : ι → ℤ)
    (hint : Integrable (coordinateFourierGaussian L b a n)) :
    UnitAddTorus.mFourierCoeff
        (gaussianTorusPeriodization L b a ha) n =
      ∫ x, coordinateFourierGaussian L b a n x := by
  classical
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ n 0]
  simp only [Pi.zero_apply, zero_add]
  have hpoint (x : ι → ℝ) :
      UnitAddTorus.mFourier (-n) (torusQuotientMap x) •
          gaussianTorusPeriodization L b a ha
            (torusQuotientMap x) =
        ∑' k : ι → ℤ,
          coordinateFourierGaussianTranslate L b a n k x := by
    rw [gaussianTorusPeriodization,
      torusPeriodization_apply_quotient]
    unfold intPeriodization coordinateFourierGaussianTranslate
      coordinateFourierCharacter
    rw [smul_eq_mul, tsum_mul_left]
    rfl
  change
    (∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
      UnitAddTorus.mFourier (-n) (torusQuotientMap x) •
        gaussianTorusPeriodization L b a ha (torusQuotientMap x)) =
      ∫ x, coordinateFourierGaussian L b a n x
  simp_rw [hpoint]
  rw [integral_tsum_coordinateFourierGaussianTranslate L b ha n]
  rw [integral_eq_tsum_integral_pi_Ioc
    (coordinateFourierGaussian L b a n) hint]
  apply tsum_congr
  intro k
  apply setIntegral_congr_fun measurableSet_pi_Ioc
  intro x hx
  exact (coordinateFourierGaussian_add_intPi L b a n k x).symm

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Module MeasureTheory

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem map_ofZLatticeBasis_equivFun_symm_volume
    (b : Basis ι ℤ L) :
    Measure.map (b.ofZLatticeBasis ℝ L).equivFun.symm volume =
      (b.ofZLatticeBasis ℝ L).addHaar := by
  classical
  let e : (ι → ℝ) ≃L[ℝ] E :=
    LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm
  have hcoord : (Pi.basisFun ℝ ι).addHaar =
      (volume : Measure (ι → ℝ)) := by
    rw [Basis.addHaar_def, Basis.parallelepiped_basisFun,
      addHaarMeasure_eq_volume_pi]
  rw [← hcoord]
  change Measure.map e (Pi.basisFun ℝ ι).addHaar =
    (b.ofZLatticeBasis ℝ L).addHaar
  rw [Basis.map_addHaar (Pi.basisFun ℝ ι) e]
  congr 1
  ext i
  simp [e]

omit [DecidableEq ι] in
theorem covolume_eq_volumeReal_parallelepiped
    (b : Basis ι ℤ L) :
    ZLattice.covolume L =
      volume.real
        ((b.ofZLatticeBasis ℝ L).parallelepiped : Set E) := by
  classical
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b
    (b.ofZLatticeBasis ℝ L)]
  have hfun :
      ((fun x : L ↦ (x : E)) ∘ b) =
        (b.ofZLatticeBasis ℝ L : ι → E) := by
    funext i
    simp
  rw [hfun, Basis.det_self, abs_one, one_mul]
  exact measureReal_congr
    (ZSpan.fundamentalDomain_ae_parallelepiped
      (b.ofZLatticeBasis ℝ L) volume)

omit [DecidableEq ι] in
theorem volume_parallelepiped_ofZLatticeBasis
    (b : Basis ι ℤ L) :
    volume ((b.ofZLatticeBasis ℝ L).parallelepiped : Set E) =
      ENNReal.ofReal (ZLattice.covolume L) := by
  classical
  have hfinite :
      volume ((b.ofZLatticeBasis ℝ L).parallelepiped : Set E) < ⊤ :=
    (b.ofZLatticeBasis ℝ L).parallelepiped.isCompact.measure_lt_top
  rw [covolume_eq_volumeReal_parallelepiped L b]
  exact (ENNReal.ofReal_toReal hfinite.ne).symm

omit [DecidableEq ι] in
theorem addHaar_ofZLatticeBasis_eq_inv_covolume_smul_volume
    (b : Basis ι ℤ L) :
    (b.ofZLatticeBasis ℝ L).addHaar =
      (Real.toNNReal (ZLattice.covolume L))⁻¹ • volume := by
  classical
  rw [Basis.addHaar_eq_iff]
  rw [Measure.smul_apply,
    volume_parallelepiped_ofZLatticeBasis L b]
  have hc : Real.toNNReal (ZLattice.covolume L) ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero]
    exact not_le_of_gt (ZLattice.covolume_pos L)
  change
    (↑((Real.toNNReal (ZLattice.covolume L))⁻¹) : ENNReal) *
        ENNReal.ofReal (ZLattice.covolume L) = 1
  rw [ENNReal.coe_inv hc, ENNReal.ofNNReal_toNNReal]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (ZLattice.covolume_pos L))
    ENNReal.ofReal_ne_top

omit [DecidableEq ι] in
theorem integral_comp_ofZLatticeBasis_equivFun_symm
    (b : Basis ι ℤ L) (f : E → ℂ) :
    (∫ x : ι → ℝ,
        f ((b.ofZLatticeBasis ℝ L).equivFun.symm x)) =
      (Real.toNNReal (ZLattice.covolume L))⁻¹ •
        ∫ y : E, f y := by
  classical
  let e : (ι → ℝ) ≃ᵐ E :=
    (LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm).toHomeomorph.toMeasurableEquiv
  change (∫ x : ι → ℝ, f (e x)) = _
  rw [← integral_map_equiv (μ := volume) e f]
  change (∫ y : E, f y ∂Measure.map
    (b.ofZLatticeBasis ℝ L).equivFun.symm volume) = _
  rw [map_ofZLatticeBasis_equivFun_symm_volume L b,
    addHaar_ofZLatticeBasis_eq_inv_covolume_smul_volume L b,
    integral_smul_nnreal_measure]

omit [DecidableEq ι] in
theorem integrable_comp_ofZLatticeBasis_equivFun_symm
    (b : Basis ι ℤ L) {f : E → ℂ} (hf : Integrable f) :
    Integrable
      (fun x : ι → ℝ ↦
        f ((b.ofZLatticeBasis ℝ L).equivFun.symm x)) := by
  classical
  let e : (ι → ℝ) ≃ᵐ E :=
    (LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm).toHomeomorph.toMeasurableEquiv
  change Integrable (f ∘ e)
  rw [← integrable_map_equiv e f]
  change Integrable f (Measure.map
    (b.ofZLatticeBasis ℝ L).equivFun.symm volume)
  rw [
    map_ofZLatticeBasis_equivFun_symm_volume L b,
    addHaar_ofZLatticeBasis_eq_inv_covolume_smul_volume L b]
  exact hf.smul_measure_nnreal

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Module MeasureTheory
open scoped RealInnerProductSpace

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {E : Type*} [NormedAddCommGroup E] {ι : Type*} [Fintype ι]

noncomputable def ambientFourierGaussian [InnerProductSpace ℝ E]
    (a : ℝ) (w y : E) : ℂ :=
  Complex.exp
    (-(a : ℂ) * (‖y‖ : ℂ) ^ 2 +
      (-2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ w y : ℂ))

theorem integrable_ambientFourierGaussian
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {a : ℝ} (ha : 0 < a) (w : E) :
    Integrable (ambientFourierGaussian a w) := by
  have h :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (b := (a : ℂ)) (by simp_all) (-2 * (Real.pi : ℂ) * Complex.I) w
  convert h using 1 with y
  unfold ambientFourierGaussian
  simp

theorem coordinateFourierGaussian_eq_ambient
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [DecidableEq ι]
    (b : Basis ι ℤ L) (a : ℝ) (n : ι → ℤ) (x : ι → ℝ) :
    coordinateFourierGaussian L b a n x =
      ambientFourierGaussian a (dualLatticePoint L b n)
        ((b.ofZLatticeBasis ℝ L).equivFun.symm x) := by
  rw [coordinateFourierGaussian, coordinateFourierCharacter,
    mFourier_neg_torusQuotientMap]
  unfold coordinateGaussian latticeGaussian ambientFourierGaussian
  rw [← Complex.exp_add]
  rw [inner_dualLatticePoint_ofZLatticeBasis_equivFun_symm L b n x]
  push_cast
  ring_nf

theorem integrable_coordinateFourierGaussian
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) (n : ι → ℤ) :
    Integrable (coordinateFourierGaussian L b a n) := by
  classical
  have h := integrable_comp_ofZLatticeBasis_equivFun_symm L b
    (integrable_ambientFourierGaussian
      (E := E) ha (dualLatticePoint L b n))
  apply h.congr
  filter_upwards with x
  exact (coordinateFourierGaussian_eq_ambient L b a n x).symm

theorem integral_ambientFourierGaussian
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {a : ℝ} (ha : 0 < a) (w : E) :
    (∫ y : E, ambientFourierGaussian a w y) =
      ((Real.pi : ℂ) / a) ^
          (Module.finrank ℝ E / 2 : ℂ) *
        Complex.exp
          (-(Real.pi : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / a) := by
  rw [← fourier_gaussian_innerProductSpace (b := (a : ℂ))
    (by simp_all) w]
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with y
  unfold ambientFourierGaussian
  rw [smul_eq_mul, ← Complex.exp_add]
  push_cast
  rw [real_inner_comm y w]
  ring_nf

theorem mFourierCoeff_gaussianTorusPeriodization_eq
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [DecidableEq ι]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff
        (gaussianTorusPeriodization L b a ha) n =
      (Real.toNNReal (ZLattice.covolume L))⁻¹ •
        (((Real.pi : ℂ) / a) ^
            (Module.finrank ℝ E / 2 : ℂ) *
          Complex.exp
            (-(Real.pi : ℂ) ^ 2 *
              (‖dualLatticePoint L b n‖ : ℂ) ^ 2 / a)) := by
  rw [mFourierCoeff_gaussianTorusPeriodization L b ha n
    (integrable_coordinateFourierGaussian L b ha n)]
  simp_rw [coordinateFourierGaussian_eq_ambient L b a n]
  rw [integral_comp_ofZLatticeBasis_equivFun_symm L b,
    integral_ambientFourierGaussian ha]

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Module MeasureTheory

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {E : Type*} [NormedAddCommGroup E] {ι : Type*}

theorem exp_fourierGaussian_eq_latticeGaussian
    {a : ℝ} (_ha : 0 < a) (w : E) :
    Complex.exp
        (-(Real.pi : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / a) =
      latticeGaussian (Real.pi ^ 2 / a) w := by
  unfold latticeGaussian
  push_cast
  grind

theorem summable_mFourierCoeff_gaussianTorusPeriodization
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [Fintype ι]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    Summable
      (UnitAddTorus.mFourierCoeff
        (gaussianTorusPeriodization L b a ha)) := by
  classical
  have hp : 0 < Real.pi ^ 2 / a := div_pos (sq_pos_of_pos Real.pi_pos) ha
  have hdual :
      Summable (fun n : ι → ℤ ↦
        latticeGaussian (Real.pi ^ 2 / a)
          (dualLatticePoint L b n)) := by
    have hs := (Equiv.summable_iff
      (e := (dualLatticeBasis L b).equivFun.toEquiv.symm)).mpr
        (summable_latticeGaussian (dualLattice L) hp)
    simpa [Function.comp_def, dualLatticePoint] using hs
  let C : ℂ :=
    (Real.toNNReal (ZLattice.covolume L))⁻¹ •
      (((Real.pi : ℂ) / a) ^
        (Module.finrank ℝ E / 2 : ℂ))
  have hscaled : Summable (fun n : ι → ℤ ↦
      C * latticeGaussian (Real.pi ^ 2 / a)
        (dualLatticePoint L b n)) :=
    hdual.mul_left C
  apply hscaled.congr
  intro n
  rw [mFourierCoeff_gaussianTorusPeriodization_eq L b ha n,
    exp_fourierGaussian_eq_latticeGaussian ha]
  dsimp [C]
  simp

theorem latticeGaussian_poissonSummation_of_basis
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [Finite ι]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    latticeTheta L a =
      (Real.toNNReal (ZLattice.covolume L))⁻¹ •
        (((Real.pi : ℂ) / a) ^
            (Module.finrank ℝ E / 2 : ℂ) *
          dualLatticeTheta L (Real.pi ^ 2 / a)) := by
  classical
  let := Fintype.ofFinite ι
  have hsummable :=
    summable_mFourierCoeff_gaussianTorusPeriodization L b ha
  have hseries :=
    UnitAddTorus.hasSum_mFourier_series_apply_of_summable
      hsummable (0 : UnitAddTorus ι)
  have hsum :
      (∑' n : ι → ℤ,
          UnitAddTorus.mFourierCoeff
            (gaussianTorusPeriodization L b a ha) n) =
        gaussianTorusPeriodization L b a ha 0 := by
    rw [← hseries.tsum_eq]
    apply tsum_congr
    intro n
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      Pi.zero_apply, fourier_eval_zero, Finset.prod_const_one,
      smul_eq_mul, mul_one]
  rw [← gaussianTorusPeriodization_zero L b ha, ← hsum]
  simp_rw [mFourierCoeff_gaussianTorusPeriodization_eq L b ha,
    exp_fourierGaussian_eq_latticeGaussian ha]
  have hp : 0 < Real.pi ^ 2 / a := div_pos (sq_pos_of_pos Real.pi_pos) ha
  have hdual :
      Summable (fun n : ι → ℤ ↦
        latticeGaussian (Real.pi ^ 2 / a)
          (dualLatticePoint L b n)) := by
    have hs := (Equiv.summable_iff
      (e := (dualLatticeBasis L b).equivFun.toEquiv.symm)).mpr
        (summable_latticeGaussian (dualLattice L) hp)
    simpa [Function.comp_def, dualLatticePoint] using hs
  have hinner := hdual.mul_left
    (((Real.pi : ℂ) / a) ^
      (Module.finrank ℝ E / 2 : ℂ))
  let c : NNReal :=
    (Real.toNNReal (ZLattice.covolume L volume))⁻¹
  change
    (∑' n : ι → ℤ,
      c • (((Real.pi : ℂ) / a) ^
        (Module.finrank ℝ E / 2 : ℂ) *
        latticeGaussian (Real.pi ^ 2 / a)
          (dualLatticePoint L b n))) =
      c • (((Real.pi : ℂ) / a) ^
        (Module.finrank ℝ E / 2 : ℂ) *
        dualLatticeTheta L (Real.pi ^ 2 / a))
  rw [hinner.tsum_const_smul c]
  rw [tsum_mul_left]
  rw [← dualLatticeTheta_eq_tsum_coordinates L b]

theorem latticeGaussian_poissonSummation
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {a : ℝ} (ha : 0 < a) :
    latticeTheta L a =
      (Real.toNNReal (ZLattice.covolume L))⁻¹ •
        (((Real.pi : ℂ) / a) ^
            (Module.finrank ℝ E / 2 : ℂ) *
          dualLatticeTheta L (Real.pi ^ 2 / a)) := by
  let b := Free.chooseBasis ℤ L
  exact latticeGaussian_poissonSummation_of_basis L b ha

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

end

/- Source module: DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.PolynomialGaussianAbsorption -/

section

namespace DedekindZetaZeroFree

theorem thetaPolynomialGaussianAbsorption (d : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ P : ℝ, 0 < P ∧ ∀ u : ℝ, 0 ≤ u →
      (1 + u) ^ d * Real.exp (-a * u ^ 2) ≤
        P * Real.exp (-(a / 2) * u ^ 2) := by
  have ha2 : 0 < a / 2 := by linarith

  have hlit : (fun x : ℝ => Real.exp (-(a / 2) * x ^ 2)) =o[Filter.atTop]
      (fun x : ℝ => x ^ (-(d : ℝ))) := by
    have h := rexp_neg_quadratic_isLittleO_rpow_atTop (a := -(a / 2)) (b := 0)
      (s := -(d : ℝ)) (by linarith)
    simpa using h
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp (-(a / 2) * x ^ 2) ≤ x ^ (-(d : ℝ)) := by
    filter_upwards [hlit.bound (c := 1) one_pos,
      Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul] at hx
    exact hx
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max ((1 + max N₀ 1) ^ d) (2 ^ d), ?_, ?_⟩
  · exact lt_of_lt_of_le (pow_pos (by norm_num) d) (le_max_right _ _)
  · intro u hu

    have hfu : (1 + u) ^ d * Real.exp (-(a / 2) * u ^ 2) ≤
        max ((1 + max N₀ 1) ^ d) (2 ^ d) := by
      rcases le_or_gt u (max N₀ 1) with hle | hlt
      · calc (1 + u) ^ d * Real.exp (-(a / 2) * u ^ 2)
            ≤ (1 + max N₀ 1) ^ d * 1 := by
              refine mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) d) ?_
                (Real.exp_pos _).le (by positivity)
              rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg u]
            _ = (1 + max N₀ 1) ^ d := by ring
            _ ≤ max ((1 + max N₀ 1) ^ d) (2 ^ d) := le_max_left _ _
      · have huN₀ : N₀ ≤ u := le_trans (le_max_left _ _) hlt.le
        have hu1 : 1 ≤ u := le_trans (le_max_right _ _) hlt.le
        have htail : Real.exp (-(a / 2) * u ^ 2) ≤ u ^ (-(d : ℝ)) := hN₀ u huN₀
        calc (1 + u) ^ d * Real.exp (-(a / 2) * u ^ 2)
            ≤ (2 * u) ^ d * u ^ (-(d : ℝ)) := by
              refine mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) d) htail
                (Real.exp_pos _).le (by positivity)
            _ = 2 ^ d * (u ^ d * u ^ (-(d : ℝ))) := by rw [mul_pow]; ring
            _ = 2 ^ d * 1 := by
              congr 1
              rw [← Real.rpow_natCast u d, ← Real.rpow_add (by linarith : (0 : ℝ) < u)]
              rw [show (d : ℝ) + -(d : ℝ) = 0 by ring, Real.rpow_zero]
            _ = 2 ^ d := by ring
            _ ≤ max ((1 + max N₀ 1) ^ d) (2 ^ d) := le_max_right _ _

    have hexp : Real.exp (-a * u ^ 2) =
        Real.exp (-(a / 2) * u ^ 2) * Real.exp (-(a / 2) * u ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (1 + u) ^ d * Real.exp (-a * u ^ 2)
        = (1 + u) ^ d * Real.exp (-(a / 2) * u ^ 2) *
            Real.exp (-(a / 2) * u ^ 2) := by rw [hexp]; ring
      _ ≤ max ((1 + max N₀ 1) ^ d) (2 ^ d) * Real.exp (-(a / 2) * u ^ 2) :=
          mul_le_mul_of_nonneg_right hfu (Real.exp_pos _).le

end DedekindZetaZeroFree

end

/- Source module: DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.GaussianExistence -/

section

noncomputable section

open scoped ContDiff

namespace DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

private theorem real_gaussian_decay
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a : ℝ) (ha : 0 < a) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : E ↦ Real.exp (-a * ‖x‖ ^ 2)) x‖ ≤ C := by
  have ht : Function.HasTemperateGrowth (fun x : E ↦ -a * ‖x‖ ^ 2) := by fun_prop
  obtain ⟨m, C, hC, hb⟩ := ht.norm_iteratedFDeriv_le_uniform n
  have hc1 : 1 ≤ max C 1 := le_max_right _ _
  obtain ⟨P, hP, hbound⟩ := DedekindZetaZeroFree.thetaPolynomialGaussianAbsorption
    (k + m * n) a ha
  refine ⟨(n.factorial : ℝ) * (max C 1) ^ n * P, ?_⟩
  intro x
  have hu : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hD1 : 1 ≤ max C 1 * (1 + ‖x‖) ^ m := one_le_mul_of_one_le_of_one_le hc1 (one_le_pow₀ hu)
  have hderiv : ‖iteratedFDeriv ℝ n (fun x : E ↦ Real.exp (-a * ‖x‖ ^ 2)) x‖ ≤
      (n.factorial : ℝ) * Real.exp (-a * ‖x‖ ^ 2) *
        (max C 1 * (1 + ‖x‖) ^ m) ^ n := by
    apply norm_iteratedFDeriv_comp_le (N := ∞) Real.contDiff_exp ht.1 (WithTop.coe_le_coe.mpr le_top) x
    · intro i hi
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
        Real.iter_deriv_exp, Real.norm_of_nonneg (Real.exp_pos _).le]
    · intro i hi hin
      calc ‖iteratedFDeriv ℝ i (fun x : E ↦ -a * ‖x‖ ^ 2) x‖
        ≤ C * (1 + ‖x‖) ^ m := hb i hin x
        _ ≤ max C 1 * (1 + ‖x‖) ^ m := by gcongr; exact le_max_left _ _
        _ ≤ (max C 1 * (1 + ‖x‖) ^ m) ^ i := by
          simpa using pow_le_pow_right₀ hD1 hi
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : E ↦ Real.exp (-a * ‖x‖ ^ 2)) x‖
    ≤ ‖x‖ ^ k * ((n.factorial : ℝ) * Real.exp (-a * ‖x‖ ^ 2) *
        (max C 1 * (1 + ‖x‖) ^ m) ^ n) := mul_le_mul_of_nonneg_left hderiv (by positivity)
    _ ≤ (1 + ‖x‖) ^ k * ((n.factorial : ℝ) * Real.exp (-a * ‖x‖ ^ 2) *
        (max C 1 * (1 + ‖x‖) ^ m) ^ n) := by gcongr; linarith
    _ = (n.factorial : ℝ) * (max C 1) ^ n *
        ((1 + ‖x‖) ^ (k + m * n) * Real.exp (-a * ‖x‖ ^ 2)) := by
      rw [mul_pow, ← pow_mul, pow_add]; ring
    _ ≤ (n.factorial : ℝ) * (max C 1) ^ n *
        (P * Real.exp (-(a / 2) * ‖x‖ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (hbound ‖x‖ (norm_nonneg _)) (by positivity)
    _ ≤ (n.factorial : ℝ) * (max C 1) ^ n * P := by
      have he : Real.exp (-(a / 2) * ‖x‖ ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
      calc _ ≤ (n.factorial : ℝ) * (max C 1) ^ n * (P * 1) := by gcongr
           _ = _ := by ring

theorem exists_gaussian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (a : ℝ) (ha : 0 < a) :
    ∃ f : SchwartzMap E ℂ, ∀ x, f x = latticeGaussian a x := by
  let g : SchwartzMap E ℝ := {
    toFun := fun x ↦ Real.exp (-a * ‖x‖ ^ 2)
    smooth' := Real.contDiff_exp.comp
      (show Function.HasTemperateGrowth (fun x : E ↦ -a * ‖x‖ ^ 2) from by fun_prop).1
    decay' := real_gaussian_decay a ha }
  refine ⟨SchwartzMap.postcompCLM Complex.ofRealCLM g, ?_⟩
  intro x
  change (Real.exp (-a * ‖x‖ ^ 2) : ℂ) = latticeGaussian a x
  simp [latticeGaussian]

end DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

end

end

/- Source module: DedekindZetaZeroFree.Arithmetic.Ideals.TraceDualIdeal -/

section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Mechanical port of `LeanPool/Odlyzko/Theta/TraceDualIdeal.lean` from
https://github.com/LeanPool/lean-pool at commit
`68aa6ee63d20ad76bcc15f595adfc72949991f06` (Lean 4.35.0-rc3), adapted to rc2.
The original copyright and Apache-2.0 license are retained above; the full
license is included in the repository root `LICENSE`.
Only the namespace, imports and module-visibility syntax have been changed.
-/

noncomputable section

open scoped nonZeroDivisors

open NumberField

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

noncomputable def traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0
    (FractionalIdeal.dual ℤ ℚ
      (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ (Units.ne_zero I))

@[simp]
theorem coe_traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdealUnit K I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ
        (I : FractionalIdeal (𝓞 K)⁰ K) :=
  rfl

@[simp]
theorem traceDualIdealUnit_traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    traceDualIdealUnit K (traceDualIdealUnit K I) = I := by
  ext
  simp

theorem coe_traceDualIdealUnit_eq_dual_one_mul_inv
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdealUnit K I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ
          (1 : FractionalIdeal (𝓞 K)⁰ K) *
        (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [coe_traceDualIdealUnit,
    FractionalIdeal.dual_eq_mul_inv]

theorem absNorm_traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    FractionalIdeal.absNorm
        (traceDualIdealUnit K I :
          FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.absNorm
          (FractionalIdeal.dual ℤ ℚ
            (1 : FractionalIdeal (𝓞 K)⁰ K)) *
        (FractionalIdeal.absNorm
          (I : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [coe_traceDualIdealUnit_eq_dual_one_mul_inv,
    map_mul, map_inv₀]

theorem absNorm_traceDual_one :
    FractionalIdeal.absNorm
        (FractionalIdeal.dual ℤ ℚ
          (1 : FractionalIdeal (𝓞 K)⁰ K)) =
      ((|(discr K : ℤ)| : ℚ))⁻¹ := by
  have hdifferent :=
    congrArg FractionalIdeal.absNorm
      (coeIdeal_differentIdeal ℤ ℚ K (𝓞 K))
  rw [map_inv₀, FractionalIdeal.coeIdeal_absNorm,
    NumberField.absNorm_differentIdeal K] at hdifferent
  simp_all

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

/- Source module: DedekindZetaZeroFree.Adeles.Lattices.TraceIdealDuality -/

section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Mechanical port of `LeanPool/Odlyzko/Theta/TraceDualLattice.lean` from
https://github.com/LeanPool/lean-pool at exact commit
`68aa6ee63d20ad76bcc15f595adfc72949991f06` (Lean 4.35.0-rc3), adapted to rc2.
The original copyright and Apache-2.0 license are retained above; the full
license is included in the repository root `LICENSE`.
Changes: local imports, namespace, removal of module-visibility syntax.
-/

noncomputable section

section

open Complex NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

open Classical in

noncomputable def euclideanIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (mixedEmbedding.idealLattice K I)
    (mixedEmbedding.euclidean.toMixed K).toLinearMap

open Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    DiscreteTopology (euclideanIdealLattice K I) := by
  unfold euclideanIdealLattice
  infer_instance

open Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsZLattice ℝ (euclideanIdealLattice K I) := by
  unfold euclideanIdealLattice
  infer_instance

open Classical in
theorem covolume_euclideanIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (euclideanIdealLattice K I) =
      FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) *
        (2⁻¹) ^ nrComplexPlaces K * √|discr K| := by
  rw [euclideanIdealLattice,
    ZLattice.covolume_comap (mixedEmbedding.idealLattice K I)
      MeasureTheory.volume MeasureTheory.volume
      (mixedEmbedding.euclidean.volumePreserving_toMixed K),
    mixedEmbedding.covolume_idealLattice]

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Complex NumberField NumberField.InfinitePlace
open scoped ComplexConjugate

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

open Classical in

noncomputable def mixedTracePairing
    (x y : mixedEmbedding.mixedSpace K) : ℝ :=
  (∑ w : {w : InfinitePlace K // IsReal w}, x.1 w * y.1 w) +
    ∑ w : {w : InfinitePlace K // IsComplex w},
      2 * (x.2 w * y.2 w).re

open Classical in
private theorem sum_embeddings_eq_sum_places (z : K) :
    (∑ φ : K →+* ℂ, φ z) =
      (∑ w : {w : InfinitePlace K // IsReal w},
          ((embedding_of_isReal w.2 z : ℝ) : ℂ)) +
        ∑ w : {w : InfinitePlace K // IsComplex w},
          (w.1.embedding z + conj (w.1.embedding z)) := by
  have hfiber (w : InfinitePlace K) :
      ∑ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ ↦
        InfinitePlace.mk φ = w), φ z =
        if hw : IsReal w then
          w.embedding z
        else
          w.embedding z + conj (w.embedding z) := by
    have hmk (φ : K →+* ℂ) :
        InfinitePlace.mk φ = w ↔
          φ = w.embedding ∨
            ComplexEmbedding.conjugate φ = w.embedding := by
      constructor
      · intro h
        apply mk_eq_iff.mp
        simp_all
      · intro h
        exact (mk_eq_iff.mpr h).trans (mk_embedding w)
    by_cases hw : IsReal w
    · have hconj :
          ComplexEmbedding.conjugate w.embedding = w.embedding :=
        ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hw)
      have hfilter :
          Finset.univ.filter (fun φ : K →+* ℂ ↦
            InfinitePlace.mk φ = w) =
            {w.embedding} := by
        ext φ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        rw [hmk]
        constructor
        · rintro (h | h)
          · simp_all
          · have hc := congrArg ComplexEmbedding.conjugate h
            simpa [hconj] using hc
        · simp_all
      simp_all
    · have hne :
          ComplexEmbedding.conjugate w.embedding ≠ w.embedding := by
        rwa [Ne, ← ComplexEmbedding.isReal_iff, ← isReal_iff]
      have hfilter :
          Finset.univ.filter (fun φ : K →+* ℂ ↦
            InfinitePlace.mk φ = w) =
            {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
        ext φ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        rw [hmk]
        constructor
        · rintro (rfl | h)
          · simp
          · right
            have hc := congrArg ComplexEmbedding.conjugate h
            simpa using hc
        · rintro (rfl | rfl) <;> simp
      simp [hfilter, hne.symm, hw,
        ComplexEmbedding.conjugate_coe_eq]
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk
    (fun φ : K →+* ℂ ↦ φ z)]
  simp_rw [hfiber]
  rw [← Fintype.sum_subtype_add_sum_subtype
    (p := fun w : InfinitePlace K ↦ IsReal w)]
  apply congrArg₂
  · apply Finset.sum_congr rfl
    simp_all
  · rw [Fintype.sum_equiv
      (Equiv.subtypeEquivRight
        (fun w : InfinitePlace K ↦ not_isReal_iff_isComplex))]
    simp_all

open Classical in
theorem mixedTracePairing_mixedEmbedding (x y : K) :
    mixedTracePairing K (mixedEmbedding K x) (mixedEmbedding K y) =
      Algebra.trace ℚ K (x * y) := by
  have hemb :
      (∑ σ : K →ₐ[ℚ] ℂ, σ (x * y)) =
        ∑ φ : K →+* ℂ, φ (x * y) := by
    rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ)]
    simp
  have htrace :
      ((Algebra.trace ℚ K (x * y) : ℚ) : ℂ) =
        (∑ w : {w : InfinitePlace K // IsReal w},
            ((embedding_of_isReal w.2 (x * y) : ℝ) : ℂ)) +
          ∑ w : {w : InfinitePlace K // IsComplex w},
            (w.1.embedding (x * y) +
              conj (w.1.embedding (x * y))) := by
    rw [← sum_embeddings_eq_sum_places K (x * y), ← hemb]
    exact trace_eq_sum_embeddings
      (K := ℚ) (L := K) (E := ℂ) (x := x * y)
  have hre :
      Algebra.trace ℚ K (x * y) =
        (∑ w : {w : InfinitePlace K // IsReal w},
            embedding_of_isReal w.2 (x * y)) +
          ∑ w : {w : InfinitePlace K // IsComplex w},
            (w.1.embedding (x * y) +
              conj (w.1.embedding (x * y))).re := by
    simpa only [Complex.add_re, Complex.re_sum, Complex.ofReal_re,
      Complex.ratCast_re] using congrArg Complex.re htrace
  have hreal (w : {w : InfinitePlace K // IsReal w}) :
      embedding_of_isReal w.2 (x * y) =
        embedding_of_isReal w.2 x * embedding_of_isReal w.2 y := by simp
  have hcomplex (w : {w : InfinitePlace K // IsComplex w}) :
      (w.1.embedding (x * y) + conj (w.1.embedding (x * y))).re =
        2 * (w.1.embedding x * w.1.embedding y).re := by
    rw [map_mul]
    simp only [Complex.add_re, Complex.conj_re]
    ring
  simp_rw [hreal, hcomplex] at hre
  simpa only [mixedTracePairing, mixedEmbedding.mixedEmbedding_apply_isReal,
    mixedEmbedding.mixedEmbedding_apply_isComplex] using hre.symm

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Complex NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

open Classical in

noncomputable def divideBySqrtTwo : ℂ ≃L[ℝ] ℂ :=
    ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ)
      (Units.mk0 (Real.sqrt 2)⁻¹
        (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))))

open Classical in
@[simp]
theorem divideBySqrtTwo_symm_apply (z : ℂ) :
    divideBySqrtTwo.symm z = Real.sqrt 2 • z := by
  apply divideBySqrtTwo.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change z = ((Real.sqrt 2)⁻¹ : ℝ) • (Real.sqrt 2 • z)
  simp

open Classical in

noncomputable def unscaleComplexCoordinates :
    ({w : InfinitePlace K // IsComplex w} → ℂ) ≃L[ℝ]
      ({w : InfinitePlace K // IsComplex w} → ℂ) :=
  ContinuousLinearEquiv.piCongrRight fun _ ↦ divideBySqrtTwo

open Classical in

noncomputable def traceToMixed :
    mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ]
      mixedEmbedding.mixedSpace K :=
  (mixedEmbedding.euclidean.toMixed K).trans
    ((ContinuousLinearEquiv.refl ℝ
      ({w : InfinitePlace K // IsReal w} → ℝ)).prodCongr
        (unscaleComplexCoordinates K))

open Classical in

noncomputable def traceEmbedding (x : K) :
    mixedEmbedding.euclidean.mixedSpace K :=
  (traceToMixed K).symm (mixedEmbedding K x)

open Classical in

noncomputable def traceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (mixedEmbedding.idealLattice K I)
    (traceToMixed K).toLinearMap

open Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    DiscreteTopology (traceIdealLattice K I) := by
  unfold traceIdealLattice
  infer_instance

open Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsZLattice ℝ (traceIdealLattice K I) := by
  unfold traceIdealLattice
  infer_instance

open Classical in
theorem traceEmbedding_mem_traceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} :
    traceEmbedding K x ∈ traceIdealLattice K I ↔
      x ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  change
    traceToMixed K (traceEmbedding K x) ∈
        mixedEmbedding.idealLattice K I ↔ _
  rw [traceEmbedding, ContinuousLinearEquiv.apply_symm_apply,
    mixedEmbedding.mem_idealLattice]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (mixedEmbedding_injective K hxy).symm ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

open Classical in
theorem exists_traceEmbedding_eq_of_mem_traceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {v : mixedEmbedding.euclidean.mixedSpace K}
    (hv : v ∈ traceIdealLattice K I) :
    ∃ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K),
      traceEmbedding K x = v := by
  change traceToMixed K v ∈ mixedEmbedding.idealLattice K I at hv
  rw [mixedEmbedding.mem_idealLattice] at hv
  obtain ⟨x, hx, hvx⟩ := hv
  refine ⟨x, hx, ?_⟩
  apply (traceToMixed K).injective
  rw [traceEmbedding, ContinuousLinearEquiv.apply_symm_apply]
  simp_all

open Classical in

noncomputable def traceConjugation :
    mixedEmbedding.euclidean.mixedSpace K ≃ₗᵢ[ℝ]
      mixedEmbedding.euclidean.mixedSpace K :=
  LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.refl ℝ
      (EuclideanSpace ℝ {w : InfinitePlace K // IsReal w}))
    (LinearIsometryEquiv.piLpCongrRight 2 fun _ ↦ Complex.conjLIE)

open Classical in
@[simp]
theorem traceConjugation_involutive
    (x : mixedEmbedding.euclidean.mixedSpace K) :
    traceConjugation K (traceConjugation K x) = x := by

  apply WithLp.ofLp_injective
  apply Prod.ext
  · rfl
  · apply WithLp.ofLp_injective
    funext w
    simp [traceConjugation]

open Classical in
theorem inner_traceEmbedding_traceConjugation (x y : K) :
    inner ℝ (traceEmbedding K x)
        (traceConjugation K (traceEmbedding K y)) =
      Algebra.trace ℚ K (x * y) := by
  rw [← mixedTracePairing_mixedEmbedding K x y]
  suffices
    (∑ w : {w : InfinitePlace K // IsReal w},
        embedding_of_isReal w.2 y * embedding_of_isReal w.2 x) +
      ((∑ w : {w : InfinitePlace K // IsComplex w},
          Real.sqrt 2 * (w.1.embedding y).re *
            (Real.sqrt 2 * (w.1.embedding x).re)) -
        ∑ w : {w : InfinitePlace K // IsComplex w},
          Real.sqrt 2 * (w.1.embedding y).im *
            (Real.sqrt 2 * (w.1.embedding x).im)) =
      (∑ w : {w : InfinitePlace K // IsReal w},
          embedding_of_isReal w.2 x * embedding_of_isReal w.2 y) +
        ∑ w : {w : InfinitePlace K // IsComplex w},
          2 * ((w.1.embedding x).re * (w.1.embedding y).re -
            (w.1.embedding x).im * (w.1.embedding y).im) by

    simpa [traceEmbedding, traceToMixed, unscaleComplexCoordinates,
      mixedEmbedding.euclidean.toMixed, traceConjugation, mixedTracePairing,
      WithLp.prod_inner_apply, PiLp.inner_apply,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.piCongrRight_symm_apply,
      mixedEmbedding.mixedEmbedding_apply_isReal,
      mixedEmbedding.mixedEmbedding_apply_isComplex]
  have hmul (a b : ℝ) :
      Real.sqrt 2 * a * (Real.sqrt 2 * b) = 2 * (a * b) := by grind
  simp_rw [hmul, mul_sub, Finset.sum_sub_distrib]
  grind

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Complex Module NumberField NumberField.InfinitePlace Submodule
open scoped nonZeroDivisors RealInnerProductSpace

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

open Classical in

noncomputable def traceIdealRealBasis
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Basis (Free.ChooseBasisIndex ℤ I) ℝ
      (mixedEmbedding.euclidean.mixedSpace K) :=
  (mixedEmbedding.fractionalIdealLatticeBasis K I).map
    (traceToMixed K).symm.toLinearEquiv

open Classical in
@[simp]
theorem traceIdealRealBasis_apply
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (i : Free.ChooseBasisIndex ℤ I) :
    traceIdealRealBasis K I i =
      traceEmbedding K (basisOfFractionalIdeal K I i) := by
  rw [traceIdealRealBasis, Basis.map_apply,
    mixedEmbedding.fractionalIdealLatticeBasis_apply]
  rfl

open Classical in
theorem span_traceIdealRealBasis
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    span ℤ (Set.range (traceIdealRealBasis K I)) =
      traceIdealLattice K I := by
  rw [traceIdealLattice]
  let eZ :
      mixedEmbedding.euclidean.mixedSpace K ≃ₗ[ℤ]
        mixedEmbedding.mixedSpace K :=
    (traceToMixed K).toLinearEquiv.restrictScalars ℤ
  have hrange :
      Set.range (traceIdealRealBasis K I) =
        eZ.symm '' Set.range
          (mixedEmbedding.fractionalIdealLatticeBasis K I) := by
    ext x
    simp [eZ, traceIdealRealBasis]
  calc
    span ℤ (Set.range (traceIdealRealBasis K I)) =
        (span ℤ
          (Set.range (mixedEmbedding.fractionalIdealLatticeBasis K I))).map
            eZ.symm.toLinearMap := by simp_all
    _ = (mixedEmbedding.idealLattice K I).map
          eZ.symm.toLinearMap := by
      rw [mixedEmbedding.span_idealLatticeBasis]
    _ = ZLattice.comap ℝ (mixedEmbedding.idealLattice K I)
          (traceToMixed K).toLinearMap := by
      change (mixedEmbedding.idealLattice K I).map eZ.symm.toLinearMap =
        (mixedEmbedding.idealLattice K I).comap eZ.toLinearMap
      exact Submodule.map_equiv_eq_comap_symm eZ.symm _

open Classical in
theorem innerDualBasis_traceIdealRealBasis_apply
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (i : Free.ChooseBasisIndex ℤ I) :
    LinearMap.BilinForm.dualBasis
        (innerₗ (mixedEmbedding.euclidean.mixedSpace K))
        innerBilin_nondegenerate (traceIdealRealBasis K I) i =
      traceConjugation K
        (traceEmbedding K
          ((basisOfFractionalIdeal K I).traceDual i)) := by
  have h :
      LinearMap.BilinForm.dualBasis
          (innerₗ (mixedEmbedding.euclidean.mixedSpace K))
          innerBilin_nondegenerate (traceIdealRealBasis K I) =
        fun i ↦ traceConjugation K
          (traceEmbedding K
            ((basisOfFractionalIdeal K I).traceDual i)) := by
    rw [LinearMap.BilinForm.dualBasis_eq_iff]
    intro a b
    rw [traceIdealRealBasis_apply]
    change inner ℝ
      (traceConjugation K
        (traceEmbedding K
          ((basisOfFractionalIdeal K I).traceDual a)))
      (traceEmbedding K (basisOfFractionalIdeal K I b)) = _
    rw [real_inner_comm,
      inner_traceEmbedding_traceConjugation K]
    rw [Module.Basis.trace_mul_traceDual]
    split_ifs <;> norm_num
  exact congrFun h i

open Classical in
theorem span_traceDual_basisOfFractionalIdeal
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    span ℤ (Set.range
        (basisOfFractionalIdeal K I).traceDual) =
      ((traceDualIdealUnit K I :
          FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K).restrictScalars ℤ := by
  rw [coe_traceDualIdealUnit,
    FractionalIdeal.coe_dual (A := ℤ) (K := ℚ)
      (Units.ne_zero I)]
  symm
  apply Submodule.traceDual_span_of_basis ℤ
  ext x
  exact (mem_span_basisOfFractionalIdeal K).symm

open Classical in

noncomputable def traceEmbeddingIntLinearMap :
    K →ₗ[ℤ] mixedEmbedding.euclidean.mixedSpace K :=
  ((traceToMixed K).symm.toLinearEquiv.toLinearMap.restrictScalars ℤ).comp
    (mixedEmbedding K).toIntAlgHom.toLinearMap

open Classical in
@[simp]
theorem traceEmbeddingIntLinearMap_apply (x : K) :
    traceEmbeddingIntLinearMap K x = traceEmbedding K x :=
  rfl

open Classical in

noncomputable def conjugateTraceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K) :=
  (traceIdealLattice K I).map
    ((traceConjugation K).toLinearEquiv.restrictScalars ℤ).toLinearMap

open Classical in
theorem map_traceEmbeddingIntLinearMap_fractionalIdeal
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((I : Submodule (𝓞 K) K).restrictScalars ℤ).map
        (traceEmbeddingIntLinearMap K) =
      traceIdealLattice K I := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (traceEmbedding_mem_traceIdealLattice K I).2 hx
  · intro hv
    obtain ⟨x, hx, hxv⟩ :=
      exists_traceEmbedding_eq_of_mem_traceIdealLattice K I hv
    exact ⟨x, hx, by simpa using hxv⟩

open Classical in
theorem span_conjugate_traceDual_basisOfFractionalIdeal
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    span ℤ (Set.range fun i : Free.ChooseBasisIndex ℤ I ↦
        traceConjugation K
          (traceEmbedding K
            ((basisOfFractionalIdeal K I).traceDual i))) =
      conjugateTraceIdealLattice K (traceDualIdealUnit K I) := by
  let cZ :
      mixedEmbedding.euclidean.mixedSpace K ≃ₗ[ℤ]
      mixedEmbedding.euclidean.mixedSpace K :=
    (traceConjugation K).toLinearEquiv.restrictScalars ℤ
  have hrange :
      Set.range (fun i : Free.ChooseBasisIndex ℤ I ↦
        traceConjugation K
          (traceEmbedding K
            ((basisOfFractionalIdeal K I).traceDual i))) =
        (cZ.toLinearMap.comp (traceEmbeddingIntLinearMap K)) ''
          Set.range (basisOfFractionalIdeal K I).traceDual := by
    ext x
    simp [cZ]
  calc
    span ℤ (Set.range fun i : Free.ChooseBasisIndex ℤ I ↦
        traceConjugation K
          (traceEmbedding K
            ((basisOfFractionalIdeal K I).traceDual i))) =
        (span ℤ (Set.range
          (basisOfFractionalIdeal K I).traceDual)).map
            (cZ.toLinearMap.comp (traceEmbeddingIntLinearMap K)) := by
      rw [hrange, Submodule.map_span]
    _ = (((traceDualIdealUnit K I :
          FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K).restrictScalars ℤ).map
            (cZ.toLinearMap.comp (traceEmbeddingIntLinearMap K)) := by
      rw [span_traceDual_basisOfFractionalIdeal]
    _ = conjugateTraceIdealLattice K (traceDualIdealUnit K I) := by
      rw [Submodule.map_comp, map_traceEmbeddingIntLinearMap_fractionalIdeal]
      rfl

open Classical in
theorem dualLattice_traceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualLattice (traceIdealLattice K I) =
      conjugateTraceIdealLattice K (traceDualIdealUnit K I) := by
  rw [dualLattice, ← span_traceIdealRealBasis K I]
  rw [LinearMap.BilinForm.dualSubmodule_span_of_basis
    (innerₗ (mixedEmbedding.euclidean.mixedSpace K))
    innerBilin_nondegenerate (traceIdealRealBasis K I)]
  rw [show Set.range
      (LinearMap.BilinForm.dualBasis
        (innerₗ (mixedEmbedding.euclidean.mixedSpace K))
        innerBilin_nondegenerate (traceIdealRealBasis K I)) =
      Set.range (fun i : Free.ChooseBasisIndex ℤ I ↦
        traceConjugation K
          (traceEmbedding K
            ((basisOfFractionalIdeal K I).traceDual i))) by
    congr 1
    funext i
    exact innerDualBasis_traceIdealRealBasis_apply K I i]
  exact span_conjugate_traceDual_basisOfFractionalIdeal K I

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

end

/- Source module: DedekindZetaZeroFree.Theta.Profiles.FractionalIdealShapeLattice -/

section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Extracted from `LeanPool/Odlyzko/CompletedZeta/FractionalShapeTheta.lean`,
https://github.com/LeanPool/lean-pool, pinned commit
`68aa6ee63d20ad76bcc15f595adfc72949991f06` (Lean 4.35.0-rc3), ported to rc2.
The original copyright and Apache-2.0 license are retained above, and the full
license is included in the repository root `LICENSE`.
-/

noncomputable section

section

open Complex Module NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

open Classical in

noncomputable def traceToEuclidean :
    mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ]
      mixedEmbedding.euclidean.mixedSpace K :=
  (traceToMixed K).trans (mixedEmbedding.euclidean.toMixed K).symm

open Classical in
theorem traceIdealLattice_eq_comap_euclideanIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    traceIdealLattice K I =
      ZLattice.comap ℝ (euclideanIdealLattice K I)
        (traceToEuclidean K).toLinearMap := by
  rfl

open Classical in
private theorem divideBySqrtTwo_toLinearMap :
    (divideBySqrtTwo : ℂ ≃L[ℝ] ℂ).toLinearMap =
      (Real.sqrt 2)⁻¹ • LinearMap.id := by
  rfl

open Classical in
private theorem det_divideBySqrtTwo :
    LinearMap.det (divideBySqrtTwo : ℂ ≃L[ℝ] ℂ).toLinearMap = 2⁻¹ := by
  rw [divideBySqrtTwo_toLinearMap, LinearMap.det_smul]
  simp

omit [NumberField K] in
open Classical in
private theorem unscaleComplexCoordinates_toLinearMap :
    (unscaleComplexCoordinates K).toLinearMap =
      LinearMap.pi (fun w ↦
        (divideBySqrtTwo : ℂ ≃L[ℝ] ℂ).toLinearMap.comp
          (LinearMap.proj w)) := by
  apply LinearMap.ext
  intro z
  funext w
  simp [unscaleComplexCoordinates]

open Classical in
private theorem det_unscaleComplexCoordinates :
    LinearMap.det (unscaleComplexCoordinates K).toLinearMap =
      (2⁻¹) ^ nrComplexPlaces K := by
  rw [unscaleComplexCoordinates_toLinearMap, LinearMap.det_pi]
  simp [det_divideBySqrtTwo]

open Classical in
private theorem det_traceToEuclidean :
    LinearMap.det (traceToEuclidean K).toLinearMap =
      (2⁻¹) ^ nrComplexPlaces K := by
  let u :=
    (ContinuousLinearEquiv.refl ℝ
      ({w : InfinitePlace K // IsReal w} → ℝ)).prodCongr
        (unscaleComplexCoordinates K)
  have hmap :
      (traceToEuclidean K).toLinearMap =
        (mixedEmbedding.euclidean.toMixed K).symm.toLinearMap.comp
          (u.toLinearMap.comp
            (mixedEmbedding.euclidean.toMixed K).toLinearMap) := by
    rfl
  rw [hmap]
  rw [show LinearMap.det
      ((mixedEmbedding.euclidean.toMixed K).symm.toLinearMap.comp
        (u.toLinearMap.comp
          (mixedEmbedding.euclidean.toMixed K).toLinearMap)) =
      LinearMap.det u.toLinearMap by
        exact LinearMap.det_conj u.toLinearMap
          (mixedEmbedding.euclidean.toMixed K).symm.toLinearEquiv]
  change LinearMap.det
      (LinearMap.prodMap
        (LinearMap.id (R := ℝ)
          (M := {w : InfinitePlace K // IsReal w} → ℝ))
        (unscaleComplexCoordinates K).toLinearMap) = _
  rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul,
    det_unscaleComplexCoordinates]

open Classical in
theorem covolume_comap_continuousLinearEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (e : E ≃L[ℝ] E) :
    ZLattice.covolume
        (ZLattice.comap ℝ L e.toLinearMap) μ =
      |LinearMap.det e.toLinearMap|⁻¹ *
        ZLattice.covolume L μ := by
  let b := Free.chooseBasis ℤ L
  have hfund :
      ZSpan.fundamentalDomain
          ((b.ofZLatticeComap ℝ L e.toLinearEquiv).ofZLatticeBasis
            ℝ (ZLattice.comap ℝ L e.toLinearMap)) =
        e ⁻¹'
          ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L) := by
    rw [← e.image_symm_eq_preimage, ← e.symm.coe_toLinearEquiv,
      ZSpan.map_fundamentalDomain]
    congr 1
    ext
    simp
  have hmeasure :
      μ (e ⁻¹' ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) =
        ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹| *
          μ (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) := by
    exact MeasureTheory.Measure.addHaar_preimage_linearMap
      μ (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero _
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _
      μ
      (ZLattice.isAddFundamentalDomain
        (b.ofZLatticeComap ℝ L e.toLinearEquiv)
        μ),
    ZLattice.covolume_eq_measure_fundamentalDomain L
      μ (ZLattice.isAddFundamentalDomain b μ),
    hfund, MeasureTheory.measureReal_def,
    MeasureTheory.measureReal_def,
    hmeasure,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  simp

open Classical in
theorem covolume_traceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (traceIdealLattice K I) =
      FractionalIdeal.absNorm
          (I : FractionalIdeal (𝓞 K)⁰ K) *
        √|discr K| := by
  rw [traceIdealLattice_eq_comap_euclideanIdealLattice K I,
    covolume_comap_continuousLinearEquiv
      (euclideanIdealLattice K I) MeasureTheory.volume
      (traceToEuclidean K),
    det_traceToEuclidean,
    covolume_euclideanIdealLattice]
  have hpos : 0 < (2⁻¹ : ℝ) ^ nrComplexPlaces K := by positivity
  grind

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Complex NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

open mixedEmbedding

variable (K : Type*) [Field K] [NumberField K]

open Classical in

noncomputable def radialMixedSpaceUnit
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    (mixedSpace K)ˣ where
  val := mixedSpaceOfRealSpace q
  inv := mixedSpaceOfRealSpace fun w ↦ (q w)⁻¹
  val_inv := by
    rw [mixedSpaceOfRealSpace_apply, mixedSpaceOfRealSpace_apply]
    apply Prod.ext
    · funext w
      simp [hq w.1]
    · funext w
      simp_all
  inv_val := by
    rw [mixedSpaceOfRealSpace_apply, mixedSpaceOfRealSpace_apply]
    apply Prod.ext
    · funext w
      simp [hq w.1]
    · funext w
      simp_all

omit [NumberField K] in
open Classical in
@[simp]
theorem radialMixedSpaceUnit_val
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    (radialMixedSpaceUnit K q hq : mixedSpace K) =
      mixedSpaceOfRealSpace q :=
  rfl

open Classical in

noncomputable def traceRadialScale
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ]
      mixedEmbedding.euclidean.mixedSpace K :=
  ((traceToMixed K).toLinearEquiv.trans
      ((radialMixedSpaceUnit K q hq).mulLeftLinearEquiv ℝ (mixedSpace K))).trans
    (traceToMixed K).symm.toLinearEquiv |>.toContinuousLinearEquiv

open Classical in
theorem traceToMixed_traceRadialScale
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    traceToMixed K (traceRadialScale K q hq v) =
      mixedSpaceOfRealSpace q * traceToMixed K v := by
  rw [traceRadialScale]
  simp

open Classical in
theorem inner_traceRadialScale
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v z : mixedEmbedding.euclidean.mixedSpace K) :
    inner ℝ (traceRadialScale K q hq v) z =
      inner ℝ v (traceRadialScale K q hq z) := by
  suffices
    (∑ w : {w : InfinitePlace K // IsReal w},
        (WithLp.fst z).ofLp w * (q w.1 * (WithLp.fst v).ofLp w)) +
      ∑ w : {w : InfinitePlace K // IsComplex w},
        (((WithLp.snd z).ofLp w).re *
            (Real.sqrt 2 *
              (q w.1 * divideBySqrtTwo ((WithLp.snd v).ofLp w)).re) +
          ((WithLp.snd z).ofLp w).im *
            (Real.sqrt 2 *
              (q w.1 * divideBySqrtTwo ((WithLp.snd v).ofLp w)).im)) =
      (∑ w : {w : InfinitePlace K // IsReal w},
          q w.1 * (WithLp.fst z).ofLp w * (WithLp.fst v).ofLp w) +
        ∑ w : {w : InfinitePlace K // IsComplex w},
          (Real.sqrt 2 *
              (q w.1 * divideBySqrtTwo ((WithLp.snd z).ofLp w)).re *
              ((WithLp.snd v).ofLp w).re +
            Real.sqrt 2 *
              (q w.1 * divideBySqrtTwo ((WithLp.snd z).ofLp w)).im *
              ((WithLp.snd v).ofLp w).im) by
    simpa [traceRadialScale, traceToMixed, unscaleComplexCoordinates,
      mixedEmbedding.euclidean.toMixed, mixedSpaceOfRealSpace_apply,
      radialMixedSpaceUnit, WithLp.prod_inner_apply, PiLp.inner_apply,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.piCongrRight_symm_apply]
  apply congrArg₂ (· + ·)
  · grind
  · apply Finset.sum_congr rfl
    intro w _
    simp [divideBySqrtTwo]
    ring

open Classical in
theorem traceRadialScale_symm_apply
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    (traceRadialScale K q hq).symm v =
      traceRadialScale K (fun w ↦ (q w)⁻¹)
        (fun w ↦ inv_ne_zero (hq w)) v := by
  apply (traceToMixed K).injective
  rw [traceToMixed_traceRadialScale]
  have h := traceToMixed_traceRadialScale K q hq
    ((traceRadialScale K q hq).symm v)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  rw [mixedSpaceOfRealSpace_apply]
  apply Prod.ext
  · funext w
    have hw := congrFun (congrArg Prod.fst h) w
    change (traceToMixed K ((traceRadialScale K q hq).symm v)).1 w =
      (q w.1)⁻¹ * (traceToMixed K v).1 w
    change (traceToMixed K v).1 w =
      q w.1 * (traceToMixed K ((traceRadialScale K q hq).symm v)).1 w at hw
    rw [hw]
    simp_all
  · funext w
    have hw := congrFun (congrArg Prod.snd h) w
    change (traceToMixed K ((traceRadialScale K q hq).symm v)).2 w =
      ((↑((q w.1)⁻¹) : ℂ) * (traceToMixed K v).2 w)
    change (traceToMixed K v).2 w =
      (q w.1 : ℂ) *
        (traceToMixed K ((traceRadialScale K q hq).symm v)).2 w at hw
    rw [hw]
    simp_all

open Classical in
theorem traceConjugation_traceRadialScale
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    traceConjugation K (traceRadialScale K q hq v) =
      traceRadialScale K q hq (traceConjugation K v) := by
  suffices
    (fun w ↦ (Real.sqrt 2 : ℂ) *
        ((q w.1 : ℂ) *
          starRingEnd ℂ (divideBySqrtTwo ((WithLp.snd v).ofLp w)))) =
      (ContinuousLinearEquiv.piCongrRight
        (fun _ ↦ divideBySqrtTwo)).symm
          ((fun w ↦ (q w.1 : ℂ)) *
            (ContinuousLinearEquiv.piCongrRight
              (fun _ ↦ divideBySqrtTwo))
                (fun w ↦ starRingEnd ℂ ((WithLp.snd v).ofLp w))) by
    simpa [traceConjugation, traceRadialScale, traceToMixed,
      unscaleComplexCoordinates, mixedEmbedding.euclidean.toMixed,
      mixedSpaceOfRealSpace_apply, radialMixedSpaceUnit,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.piCongrRight_symm_apply]
  funext w
  rw [ContinuousLinearEquiv.piCongrRight_symm_apply,
    divideBySqrtTwo_symm_apply]
  simp [divideBySqrtTwo]

open Classical in

noncomputable def shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (traceIdealLattice K I)
    (traceRadialScale K q hq).symm.toLinearMap

open Classical in
instance
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    DiscreteTopology (shapeIdealLattice K I q hq) := by
  unfold shapeIdealLattice
  infer_instance

open Classical in
instance
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    IsZLattice ℝ (shapeIdealLattice K I q hq) := by
  unfold shapeIdealLattice
  infer_instance

open Classical in

noncomputable def conjugateShapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K) :=
  (shapeIdealLattice K I q hq).map
    ((traceConjugation K).toLinearEquiv.restrictScalars ℤ).toLinearMap

open Classical in
theorem mem_conjugateShapeIdealLattice_iff
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    v ∈ conjugateShapeIdealLattice K I q hq ↔
      traceConjugation K v ∈ shapeIdealLattice K I q hq := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hv
    refine ⟨traceConjugation K v, hv, ?_⟩
    simp

open Classical in
theorem mem_conjugateTraceIdealLattice_iff
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    v ∈ conjugateTraceIdealLattice K I ↔
      traceConjugation K v ∈ traceIdealLattice K I := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hv
    refine ⟨traceConjugation K v, hv, ?_⟩
    simp

open Classical in
theorem mem_dualLattice_shapeIdealLattice_iff
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    v ∈ dualLattice (shapeIdealLattice K I q hq) ↔
      traceRadialScale K q hq v ∈ dualLattice (traceIdealLattice K I) := by
  rw [mem_dualLattice_iff, mem_dualLattice_iff]
  constructor
  · intro hv x
    have hx :
        traceRadialScale K q hq (x : mixedEmbedding.euclidean.mixedSpace K) ∈
          shapeIdealLattice K I q hq := by
      change
        (traceRadialScale K q hq).symm
            (traceRadialScale K q hq
              (x : mixedEmbedding.euclidean.mixedSpace K)) ∈
          traceIdealLattice K I
      simp
    obtain ⟨n, hn⟩ := hv
      ⟨traceRadialScale K q hq
        (x : mixedEmbedding.euclidean.mixedSpace K), hx⟩
    exact ⟨n, (inner_traceRadialScale K q hq v x).trans hn⟩
  · intro hv z
    have hz :
        (traceRadialScale K q hq).symm
            (z : mixedEmbedding.euclidean.mixedSpace K) ∈
          traceIdealLattice K I :=
      z.prop
    obtain ⟨n, hn⟩ := hv
      ⟨(traceRadialScale K q hq).symm
        (z : mixedEmbedding.euclidean.mixedSpace K), hz⟩
    refine ⟨n, ?_⟩
    rw [inner_traceRadialScale K q hq,
      ContinuousLinearEquiv.apply_symm_apply] at hn
    simp_all

open Classical in
theorem dualLattice_shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    dualLattice (shapeIdealLattice K I q hq) =
      conjugateShapeIdealLattice K (traceDualIdealUnit K I)
        (fun w ↦ (q w)⁻¹) (fun w ↦ inv_ne_zero (hq w)) := by
  ext v
  rw [mem_dualLattice_shapeIdealLattice_iff,
    dualLattice_traceIdealLattice,
    mem_conjugateTraceIdealLattice_iff,
    mem_conjugateShapeIdealLattice_iff]
  change
    traceConjugation K (traceRadialScale K q hq v) ∈
        traceIdealLattice K (traceDualIdealUnit K I) ↔
      (traceRadialScale K (fun w ↦ (q w)⁻¹)
        (fun w ↦ inv_ne_zero (hq w))).symm (traceConjugation K v) ∈
        traceIdealLattice K (traceDualIdealUnit K I)
  rw [traceRadialScale_symm_apply,
    traceConjugation_traceRadialScale]
  simp

open Classical in
theorem traceRadialScale_traceEmbedding_mem_shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) (x : K) :
    traceRadialScale K q hq (traceEmbedding K x) ∈
        shapeIdealLattice K I q hq ↔
      x ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  change
    (traceRadialScale K q hq).symm
        (traceRadialScale K q hq (traceEmbedding K x)) ∈
          traceIdealLattice K I ↔ _
  rw [ContinuousLinearEquiv.symm_apply_apply,
    traceEmbedding_mem_traceIdealLattice]

open Classical in
theorem dualLatticeTheta_shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    dualLatticeTheta (shapeIdealLattice K I q hq) Real.pi =
      latticeTheta
        (shapeIdealLattice K (traceDualIdealUnit K I)
          (fun w ↦ (q w)⁻¹) (fun w ↦ inv_ne_zero (hq w))) Real.pi := by
  rw [dualLatticeTheta, dualLattice_shapeIdealLattice,
    conjugateShapeIdealLattice]
  exact latticeTheta_map_linearIsometryEquiv
    (shapeIdealLattice K (traceDualIdealUnit K I)
      (fun w ↦ (q w)⁻¹) (fun w ↦ inv_ne_zero (hq w)))
    (traceConjugation K) Real.pi

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Complex Module NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

open mixedEmbedding

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
open Classical in
private theorem radialMixedSpaceUnit_toLinearMap
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ((radialMixedSpaceUnit K q hq).mulLeftLinearEquiv ℝ
        (mixedSpace K)).toLinearMap =
      LinearMap.prodMap
        (LinearMap.pi (fun w ↦
          (q w.1 • LinearMap.id).comp (LinearMap.proj w)))
        (LinearMap.pi (fun w ↦
          (q w.1 • LinearMap.id).comp (LinearMap.proj w))) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · funext w
    simp [radialMixedSpaceUnit, mixedSpaceOfRealSpace_apply]
  · funext w
    simp [radialMixedSpaceUnit, mixedSpaceOfRealSpace_apply]

open Classical in
theorem det_radialMixedSpaceUnit
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    LinearMap.det
        ((radialMixedSpaceUnit K q hq).mulLeftLinearEquiv ℝ
          (mixedSpace K)).toLinearMap =
      (∏ w : {w : InfinitePlace K // IsReal w}, q w.1) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, (q w.1) ^ 2 := by
  rw [radialMixedSpaceUnit_toLinearMap,
    LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  simp [LinearMap.det_smul]

open Classical in
theorem det_traceRadialScale
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    LinearMap.det (traceRadialScale K q hq).toLinearMap =
      (∏ w : {w : InfinitePlace K // IsReal w}, q w.1) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, (q w.1) ^ 2 := by
  let r :=
    ((radialMixedSpaceUnit K q hq).mulLeftLinearEquiv ℝ
      (mixedSpace K)).toLinearMap
  have hdet :
      LinearMap.det (traceRadialScale K q hq).toLinearMap =
        LinearMap.det r := by
    exact LinearMap.det_conj r (traceToMixed K).symm.toLinearEquiv
  rw [hdet]
  exact det_radialMixedSpaceUnit K q hq

open Classical in
theorem covolume_shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ZLattice.covolume (shapeIdealLattice K I q hq) =
      |(∏ w : {w : InfinitePlace K // IsReal w}, q w.1) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, (q w.1) ^ 2| *
        (FractionalIdeal.absNorm
          (I : FractionalIdeal (𝓞 K)⁰ K) * √|discr K|) := by
  have hsymm :
      LinearMap.det (traceRadialScale K q hq).symm.toLinearMap =
        (LinearMap.det (traceRadialScale K q hq).toLinearMap)⁻¹ :=
    LinearEquiv.det_coe_symm (traceRadialScale K q hq).toLinearEquiv
  rw [shapeIdealLattice,
    covolume_comap_continuousLinearEquiv
      (traceIdealLattice K I) MeasureTheory.volume
      (traceRadialScale K q hq).symm,
    hsymm,
    det_traceRadialScale, abs_inv, inv_inv,
    covolume_traceIdealLattice]

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Complex NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

open Classical in

noncomputable def fractionalIdealElementShapeMap
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)) :
    shapeIdealLattice K I q hq :=
  ⟨traceRadialScale K q hq (traceEmbedding K (x : K)),
    (traceRadialScale_traceEmbedding_mem_shapeIdealLattice
      K I q hq _).2 x.prop⟩

open Classical in
theorem fractionalIdealElementShapeMap_bijective
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    Function.Bijective (fractionalIdealElementShapeMap K I q hq) := by
  constructor
  · intro x y hxy
    have htrace :
        traceEmbedding K (x : K) = traceEmbedding K (y : K) :=
      (traceRadialScale K q hq).injective (congrArg Subtype.val hxy)
    apply Subtype.ext
    apply mixedEmbedding_injective K
    simpa [traceEmbedding] using congrArg (traceToMixed K) htrace
  · intro v
    have hv :
        (traceRadialScale K q hq).symm
            (v : mixedEmbedding.euclidean.mixedSpace K) ∈
          traceIdealLattice K I :=
      v.prop
    obtain ⟨x, hx, hxv⟩ :=
      exists_traceEmbedding_eq_of_mem_traceIdealLattice K I hv
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    change traceRadialScale K q hq (traceEmbedding K x) = v
    simp_all

open Classical in

noncomputable def fractionalIdealElementShapeEquiv
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K) ≃ shapeIdealLattice K I q hq :=
  Equiv.ofBijective (fractionalIdealElementShapeMap K I q hq)
    (fractionalIdealElementShapeMap_bijective K I q hq)

open Classical in
@[simp]
theorem fractionalIdealElementShapeEquiv_coe
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)) :
    ((fractionalIdealElementShapeEquiv K I q hq x :
        shapeIdealLattice K I q hq) :
      mixedEmbedding.euclidean.mixedSpace K) =
      traceRadialScale K q hq (traceEmbedding K (x : K)) :=
  rfl

open Classical in

noncomputable def fractionalShapeIdealTheta
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) : ℂ :=
  latticeTheta (shapeIdealLattice K I q hq) Real.pi

open Classical in
theorem fractionalShapeIdealTheta_poissonSummation
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    fractionalShapeIdealTheta K I q hq =
      (Real.toNNReal
        (ZLattice.covolume (shapeIdealLattice K I q hq)))⁻¹ •
        fractionalShapeIdealTheta K (traceDualIdealUnit K I)
          (fun w ↦ (q w)⁻¹) (fun w ↦ inv_ne_zero (hq w)) := by
  rw [fractionalShapeIdealTheta,
    latticeGaussian_poissonSummation
      (shapeIdealLattice K I q hq) Real.pi_pos]
  have hpi : ((Real.pi : ℂ) / Real.pi) = 1 := by simp
  have hparam : Real.pi ^ 2 / Real.pi = Real.pi := by grind
  rw [hpi, one_cpow, one_mul, hparam,
    dualLatticeTheta_shapeIdealLattice]
  rfl

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

end

/- Source module: DedekindZetaZeroFree.Theta.Profiles.MixedTraceNorm -/

section

noncomputable section

open Classical NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

theorem mixed_norm_sq
    (K : Type*) [Field K] [NumberField K]
    (q : InfinitePlace K → ℝ) (hq : ∀ v, q v ≠ 0) (x : K) :
    ‖traceRadialScale K q hq (traceEmbedding K x)‖ ^ 2 =
      ∑ v : InfinitePlace K, (v.mult : ℝ) * (q v) ^ 2 * (v x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp [traceRadialScale, traceEmbedding, traceToMixed, unscaleComplexCoordinates,
    mixedEmbedding.euclidean.toMixed, mixedSpaceOfRealSpace_apply,
    radialMixedSpaceUnit, WithLp.prod_inner_apply, PiLp.inner_apply,
    LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.piCongrRight_symm_apply,
    mixedEmbedding.mixedEmbedding_apply_isReal,
    mixedEmbedding.mixedEmbedding_apply_isComplex]
  simp only [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
    WithLp.fst, WithLp.snd, WithLp.ofLp_toLp, PiLp.toLp_apply,
    ContinuousLinearEquiv.piCongrRight_symm_apply, divideBySqrtTwo_symm_apply,
    Pi.mul_apply, mixedEmbedding.mixedEmbedding_apply_isReal,
    mixedEmbedding.mixedEmbedding_apply_isComplex, _root_.norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    norm_embedding_of_isReal, norm_embedding_eq]
  rw [sum_eq_sum_add_sum]
  simp
  have hreal (w : {w : InfinitePlace K // IsReal w}) :
      (embedding_of_isReal w.2 x) ^ 2 = (w.1 x) ^ 2 := by
    rw [← norm_embedding_of_isReal w.2 x, Real.norm_eq_abs, sq_abs]
  simp_rw [hreal, mul_pow, sq_abs, norm_embedding_eq, mul_assoc]

end DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

end

end

/- Source module: DedekindZetaZeroFree.Arithmetic.Ideals.UnitReindexing -/

section

noncomputable section

open Classical NumberField
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

theorem tsum_fractionalIdeal_mul_unit
    (K : Type*) [Field K] [NumberField K]
    (I : FractionalIdeal (𝓞 K)⁰ K) (u : (𝓞 K)ˣ) (f : K → ℂ) :
    (∑' x : ↥(I : Submodule (𝓞 K) K),
      f ((algebraMap (𝓞 K) K (u : 𝓞 K)) * (x : K))) =
      ∑' x : ↥(I : Submodule (𝓞 K) K), f (x : K) := by

  let e : ↥(I : Submodule (𝓞 K) K) ≃ ↥(I : Submodule (𝓞 K) K) :=
    { toFun := fun x =>
        ⟨algebraMap (𝓞 K) K (u : 𝓞 K) * (x : K), by
          rw [← Algebra.smul_def]
          exact Submodule.smul_mem _ _ x.2⟩
      invFun := fun x =>
        ⟨algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (x : K), by
          rw [← Algebra.smul_def]
          exact Submodule.smul_mem _ _ x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        show algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
            (algebraMap (𝓞 K) K (u : 𝓞 K) * (x : K)) = (x : K)
        rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      right_inv := fun x => by
        apply Subtype.ext
        show algebraMap (𝓞 K) K (u : 𝓞 K) *
            (algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (x : K)) = (x : K)
        rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul] }

  exact Equiv.tsum_eq e (fun x : ↥(I : Submodule (𝓞 K) K) => f (x : K))

end DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

end

end

/- Source module: DedekindZetaZeroFree.Theta.Profiles.MixedGaussian -/

section

noncomputable section

open Classical NumberField NumberField.InfinitePlace
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open DedekindZetaZeroFree.Theta
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

open Classical in

def mixedGaussian (x : K) (q : InfinitePlace K → ℝ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    ((∑ v : InfinitePlace K, (v.mult : ℝ) * (q v) ^ 2 * (v x) ^ 2 : ℝ) : ℂ))

theorem norm_sq_traceRadialScale_traceEmbedding
    (q : InfinitePlace K → ℝ) (hq : ∀ v, q v ≠ 0) (x : K) :
    ‖traceRadialScale K q hq (traceEmbedding K x)‖ ^ 2 =
      ∑ v : InfinitePlace K, (v.mult : ℝ) * (q v) ^ 2 * (v x) ^ 2 := by
  exact GaussianSchwartz.mixed_norm_sq K q hq x

theorem mixedGaussian_eq_latticeGaussian
    (x : K) (q : InfinitePlace K → ℝ) (hq : ∀ v, q v ≠ 0) :
    mixedGaussian K x q =
      latticeGaussian Real.pi (traceRadialScale K q hq (traceEmbedding K x)) := by
  simp only [mixedGaussian, latticeGaussian, ← Complex.ofReal_pow,
    norm_sq_traceRadialScale_traceEmbedding K q hq]

theorem fractionalShapeIdealTheta_eq_tsum_mixedGaussian
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ v, q v ≠ 0) :
    fractionalShapeIdealTheta K I q hq =
      ∑' x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
        mixedGaussian K (x : K) q := by
  unfold fractionalShapeIdealTheta latticeTheta
  rw [← (fractionalIdealElementShapeEquiv K I q hq).tsum_eq]
  apply tsum_congr
  intro x
  rw [fractionalIdealElementShapeEquiv_coe, mixedGaussian_eq_latticeGaussian]

theorem mixedGaussian_mul_unit
    (u : (𝓞 K)ˣ) (x : K) (q : InfinitePlace K → ℝ) :
    mixedGaussian K ((algebraMap (𝓞 K) K (u : 𝓞 K)) * x) q =
      mixedGaussian K x
        (fun v ↦ v (algebraMap (𝓞 K) K (u : 𝓞 K)) * q v) := by
  unfold mixedGaussian
  congr 3
  apply Finset.sum_congr rfl
  intro v _
  rw [map_mul]
  ring

theorem fractionalShapeIdealTheta_expMapBasis_add_unitCoordinateShift
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : realSpace K)
    (z : {w : InfinitePlace K // w ≠ Units.dirichletUnitTheorem.w₀} → ℤ) :
    fractionalShapeIdealTheta K I
        (expMapBasis (x + unitCoordinateShift z))
        (fun w ↦ ne_of_gt (expMapBasis_pos _ w)) =
      fractionalShapeIdealTheta K I (expMapBasis x)
        (fun w ↦ ne_of_gt (expMapBasis_pos _ w)) := by
  have heq : expMapBasis (x + unitCoordinateShift z) =
      (fun w ↦ w (algebraMap (𝓞 K) K
        (fundamentalUnitForShift z : 𝓞 K)) * expMapBasis x w) := by
    funext w
    exact congrFun (expMapBasis_add_unitCoordinateShift x z) w
  rw [fractionalShapeIdealTheta_eq_tsum_mixedGaussian,
    fractionalShapeIdealTheta_eq_tsum_mixedGaussian]
  simp_rw [heq, ← mixedGaussian_mul_unit]
  exact GaussianSchwartz.tsum_fractionalIdeal_mul_unit K
    (I : FractionalIdeal (𝓞 K)⁰ K) (fundamentalUnitForShift z)
    (fun y ↦ mixedGaussian K y (expMapBasis x))

def traceCoordinates :
    euclidean.mixedSpace K ≃ₗᵢ[ℝ] EuclideanSpace ℝ (mixedEmbedding.index K) :=
  (euclidean.stdOrthonormalBasis K).repr

def traceCoordinateCLM (i : mixedEmbedding.index K) :
    euclidean.mixedSpace K →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : mixedEmbedding.index K ↦ ℝ) i).comp
    (traceCoordinates K).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem traceCoordinateCLM_apply
    (i : mixedEmbedding.index K) (x : euclidean.mixedSpace K) :
    traceCoordinateCLM K i x = traceCoordinates K x i := rfl

def traceRealCoordinateCLM (w : {v : InfinitePlace K // IsReal v}) :
    euclidean.mixedSpace K →L[ℝ] ℝ :=
  traceCoordinateCLM K (Sum.inl w)

@[simp] theorem traceRealCoordinateCLM_apply
    (w : {v : InfinitePlace K // IsReal v}) (x : euclidean.mixedSpace K) :
    traceRealCoordinateCLM K w x = traceCoordinates K x (Sum.inl w) := rfl

theorem exists_latticeGaussianSchwartz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (a : ℝ) (ha : 0 < a) :
    ∃ f : SchwartzMap E ℂ, ∀ x, f x = latticeGaussian a x := by
  exact GaussianSchwartz.exists_gaussian a ha

theorem exists_traceGaussianSchwartz :
    ∃ f : SchwartzMap (euclidean.mixedSpace K) ℂ,
      ∀ x, f x = latticeGaussian Real.pi x :=
  exists_latticeGaussianSchwartz Real.pi Real.pi_pos

def traceGaussianSchwartz : SchwartzMap (euclidean.mixedSpace K) ℂ :=
  Classical.choose (exists_traceGaussianSchwartz K)

@[simp] theorem traceGaussianSchwartz_apply (x : euclidean.mixedSpace K) :
    traceGaussianSchwartz K x = latticeGaussian Real.pi x :=
  Classical.choose_spec (exists_traceGaussianSchwartz K) x

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

/- Source module: DedekindZetaZeroFree.Arithmetic.Units.TorsionFreeDecomposition -/

section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Mechanical port of `LeanPool/Odlyzko/CompletedZeta/UnitDecomposition.lean`
from https://github.com/LeanPool/lean-pool at exact revision
`68aa6ee63d20ad76bcc15f595adfc72949991f06` (Lean 4.35.0-rc3, ported to rc2).
Original copyright and author attribution are retained above. Released under
Apache 2.0; the full license is in the repository root `LICENSE`.
Source changes: imports, module visibility syntax, namespace, and additional
multiplication/inverse formulas below the original declarations.
-/

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.Units
  dirichletUnitTheorem

namespace DedekindZetaZeroFree.Theta

open mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in

def unitExponentReindex :
    (Fin (rank K) → ℤ) ≃
      ({w : InfinitePlace K // w ≠ w₀} → ℤ) where
  toFun f i := f (equivFinRank.symm i)
  invFun z i := z (equivFinRank i)
  left_inv f := by
    simp
  right_inv z := by
    simp

theorem fundamentalUnitForShift_unitExponentReindex
    (f : Fin (rank K) → ℤ) :
    fundamentalUnitForShift (unitExponentReindex K f) =
      ∏ i, fundSystem K i ^ f i := by
  classical
  exact (Fintype.prod_equiv
    (mixedEmbedding.fundamentalCone.equivFinRank (K := K))
    (fun i ↦ fundSystem K i ^ f i)
    (fun w ↦ fundSystem K (equivFinRank.symm w) ^
      unitExponentReindex K f w)
    (fun _ ↦ by simp [unitExponentReindex])).symm

noncomputable def unitDecompositionMap :
    torsion K × ({w : InfinitePlace K // w ≠ w₀} → ℤ) →
      (𝓞 K)ˣ :=
  fun p ↦ p.1 * fundamentalUnitForShift p.2

theorem bijective_unitDecompositionMap :
    Function.Bijective (unitDecompositionMap K) := by
  classical
  constructor
  · rintro ⟨ζ, z⟩ ⟨ζ', z'⟩ h
    let f := (unitExponentReindex K).symm z
    let f' := (unitExponentReindex K).symm z'
    have hfund : fundamentalUnitForShift z =
        ∏ i, fundSystem K i ^ f i := by
      rw [← fundamentalUnitForShift_unitExponentReindex K f]
      simp [f]
    have hfund' : fundamentalUnitForShift z' =
        ∏ i, fundSystem K i ^ f' i := by
      rw [← fundamentalUnitForShift_unitExponentReindex K f']
      simp [f']
    have hu := exist_unique_eq_mul_prod K (unitDecompositionMap K (ζ, z))
    have h₁ : unitDecompositionMap K (ζ, z) =
        ζ * ∏ i, fundSystem K i ^ f i := by
      rw [unitDecompositionMap, hfund]
    have h₂ : unitDecompositionMap K (ζ, z) =
        ζ' * ∏ i, fundSystem K i ^ f' i := by
      calc
        unitDecompositionMap K (ζ, z) =
            unitDecompositionMap K (ζ', z') := h
        _ = ζ' * ∏ i, fundSystem K i ^ f' i := by
          rw [unitDecompositionMap, hfund']
    have hp : (ζ, f) = (ζ', f') := hu.unique h₁ h₂
    apply Prod.ext
    · simp_all
    · apply (unitExponentReindex K).symm.injective
      grind
  · intro u
    obtain ⟨⟨ζ, f⟩, hu, _⟩ := exist_unique_eq_mul_prod K u
    refine ⟨(ζ, unitExponentReindex K f), ?_⟩
    rw [unitDecompositionMap,
      fundamentalUnitForShift_unitExponentReindex]
    simp_all

open scoped Classical in

def unitDecompositionEquiv :
    torsion K × ({w : InfinitePlace K // w ≠ w₀} → ℤ) ≃
      (𝓞 K)ˣ :=
  Equiv.ofBijective (unitDecompositionMap K)
    (bijective_unitDecompositionMap K)

@[simp]
theorem unitDecompositionEquiv_apply
    (p : torsion K × ({w : InfinitePlace K // w ≠ w₀} → ℤ)) :
    unitDecompositionEquiv K p =
      p.1 * fundamentalUnitForShift p.2 :=
  rfl

@[simp]
theorem fundamentalUnitForShift_zero :
    fundamentalUnitForShift (K := K) 0 = 1 := by
  classical
  simp [fundamentalUnitForShift]

theorem fundamentalUnitForShift_add
    (z z' : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    fundamentalUnitForShift (z + z') =
      fundamentalUnitForShift z * fundamentalUnitForShift z' := by
  classical
  simp [fundamentalUnitForShift, zpow_add, Finset.prod_mul_distrib]

@[simp]
theorem fundamentalUnitForShift_neg
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    fundamentalUnitForShift (-z) = (fundamentalUnitForShift z)⁻¹ := by
  classical
  simp [fundamentalUnitForShift, Finset.prod_inv_distrib]

@[simp]
theorem unitDecompositionEquiv_symm_apply_mul
    (ζ : torsion K) (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    (unitDecompositionEquiv K).symm (ζ * fundamentalUnitForShift z) =
      (ζ, z) := by
  exact (unitDecompositionEquiv K).symm_apply_apply (ζ, z)

@[simp]
theorem unitDecompositionEquiv_symm_apply_fundamentalUnitForShift
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    (unitDecompositionEquiv K).symm (fundamentalUnitForShift z) = (1, z) := by
  simpa using unitDecompositionEquiv_symm_apply_mul K 1 z

theorem unitDecompositionEquiv_mul
    (p q : torsion K × ({w : InfinitePlace K // w ≠ w₀} → ℤ)) :
    unitDecompositionEquiv K (p.1 * q.1, p.2 + q.2) =
      unitDecompositionEquiv K p * unitDecompositionEquiv K q := by
  simp only [unitDecompositionEquiv_apply, fundamentalUnitForShift_add,
    Subgroup.coe_mul]
  ac_rfl

@[simp]
theorem unitDecompositionEquiv_symm_mul (u v : (𝓞 K)ˣ) :
    (unitDecompositionEquiv K).symm (u * v) =
      (((unitDecompositionEquiv K).symm u).1 *
        ((unitDecompositionEquiv K).symm v).1,
       ((unitDecompositionEquiv K).symm u).2 +
        ((unitDecompositionEquiv K).symm v).2) := by
  apply (unitDecompositionEquiv K).injective
  simp only [Equiv.apply_symm_apply, unitDecompositionEquiv_mul]

end DedekindZetaZeroFree.Theta

end

end

/- Source module: DedekindZetaZeroFree.Arithmetic.Ideals.IdealElementDecomposition -/

section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Vendored from https://github.com/LeanPool/lean-pool,
commit 68aa6ee63d20ad76bcc15f595adfc72949991f06.
Original sources: LeanPool/Odlyzko/CompletedZeta/IdealElementDecomposition.lean;
the signature-general prefix of ConeGaussianIntegral.lean;
the idealSetElement_injective lemma of ConeGaussianInterchange.lean; and
the idealSetIntNorm definition of FundamentalConeSeries.lean.
Modifications: renamed namespace, replaced local imports, removed rc3 module
visibility syntax, and ported decomposition proofs.
Full upstream Apache-2.0 license: LICENSE.
-/

noncomputable section

open Ideal IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Theta

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K]

def idealSetIntNorm (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) : ℕ :=
  intNorm (idealSetEquiv K J a).val

noncomputable def idealSetElement
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) : K :=
  (preimageOfMemIntegerSet (idealSetEquiv K J a).val : 𝓞 K)

theorem idealSetElement_ne_zero
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    idealSetElement K J a ≠ 0 := by
  rw [idealSetElement]
  simp

theorem absNorm_idealSetElement
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    (((|Algebra.norm ℚ (idealSetElement K J a)| : ℚ) : ℝ)) =
      idealSetIntNorm K J a := by
  calc
    (((|Algebra.norm ℚ (idealSetElement K J a)| : ℚ) : ℝ)) =
        mixedEmbedding.norm (mixedEmbedding K (idealSetElement K J a)) := by simp
    _ = mixedEmbedding.norm (a : mixedSpace K) := by
      rw [idealSetElement, mixedEmbedding_preimageOfMemIntegerSet,
        idealSetEquiv_apply]
    _ = idealSetIntNorm K J a := by
      rw [idealSetIntNorm, intNorm_idealSetEquiv_apply]

theorem idealSetElement_injective (J : (Ideal (𝓞 K))⁰) :
    Function.Injective (idealSetElement K J) := by
  intro a b hab
  apply Subtype.ext
  calc
    (a : mixedSpace K) =
        mixedEmbedding K (idealSetElement K J a) := by
      rw [idealSetElement, mixedEmbedding_preimageOfMemIntegerSet,
        idealSetEquiv_apply]
    _ = mixedEmbedding K (idealSetElement K J b) := congrArg _ hab
    _ = (b : mixedSpace K) := by
      rw [idealSetElement, mixedEmbedding_preimageOfMemIntegerSet,
        idealSetEquiv_apply]

open Classical in

abbrev unitShiftIndex :=
  {w : InfinitePlace K // w ≠ w₀} → ℤ

open Classical in

abbrev nonzeroIdealElement (J : (Ideal (𝓞 K))⁰) :=
  {x : 𝓞 K // (x : 𝓞 K) ∈ (J : Ideal (𝓞 K)) ∧ x ≠ 0}

open Classical in

noncomputable def idealSetInteger
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) : 𝓞 K :=
  preimageOfMemIntegerSet (idealSetEquiv K J a).val

open Classical in
theorem idealSetInteger_mem
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    idealSetInteger K J a ∈ (J : Ideal (𝓞 K)) := by
  exact (idealSetEquiv K J a).prop

open Classical in
theorem idealSetInteger_ne_zero
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    idealSetInteger K J a ≠ 0 := by
  exact mem_nonZeroDivisors_iff_ne_zero.mp
    (preimageOfMemIntegerSet (idealSetEquiv K J a).val).2

open Classical in
theorem idealSetInteger_injective (J : (Ideal (𝓞 K))⁰) :
    Function.Injective (idealSetInteger K J) := by
  intro a b hab
  apply idealSetElement_injective K J
  exact congrArg (fun x : 𝓞 K ↦ (x : K)) hab

open Classical in

noncomputable def idealElementDecompositionMap
    (J : (Ideal (𝓞 K))⁰) :
    idealSet K J × unitShiftIndex K → nonzeroIdealElement K J :=
  fun p ↦
    ⟨((fundamentalUnitForShift p.2)⁻¹ : (𝓞 K)ˣ) *
        idealSetInteger K J p.1,
      (J : Ideal (𝓞 K)).mul_mem_left _
        (idealSetInteger_mem K J p.1),
      mul_ne_zero (Units.ne_zero _) (idealSetInteger_ne_zero K J p.1)⟩

open Classical in
@[simp]
theorem idealElementDecompositionMap_coe
    (J : (Ideal (𝓞 K))⁰) (p : idealSet K J × unitShiftIndex K) :
    ((idealElementDecompositionMap K J p : 𝓞 K) : K) =
      (((fundamentalUnitForShift p.2)⁻¹ : (𝓞 K)ˣ) : K) *
        idealSetElement K J p.1 := by
  rfl

open Classical in
theorem injective_idealElementDecompositionMap
    (J : (Ideal (𝓞 K))⁰) :
    Function.Injective (idealElementDecompositionMap K J) := by
  rintro ⟨a, z⟩ ⟨a', z'⟩ h
  have hval := congrArg
    (fun t : nonzeroIdealElement K J ↦ (t : 𝓞 K)) h
  change
    ((fundamentalUnitForShift z)⁻¹ : (𝓞 K)ˣ) *
        idealSetInteger K J a =
      ((fundamentalUnitForShift z')⁻¹ : (𝓞 K)ˣ) *
        idealSetInteger K J a' at hval
  let v : (𝓞 K)ˣ :=
    fundamentalUnitForShift z' * (fundamentalUnitForShift z)⁻¹
  have haeq :
      (v : 𝓞 K) * idealSetInteger K J a =
        idealSetInteger K J a' := by
    calc
      (v : 𝓞 K) * idealSetInteger K J a =
          (fundamentalUnitForShift z' : 𝓞 K) *
            (((fundamentalUnitForShift z)⁻¹ : (𝓞 K)ˣ) *
              idealSetInteger K J a) := by
        simp only [v, Units.val_mul]
        ring
      _ = (fundamentalUnitForShift z' : 𝓞 K) *
            (((fundamentalUnitForShift z')⁻¹ : (𝓞 K)ˣ) *
              idealSetInteger K J a') := congrArg _ hval
      _ = idealSetInteger K J a' := by simp
  have haembed :
      mixedEmbedding K ((idealSetInteger K J a : 𝓞 K) : K) =
        (a : mixedSpace K) := by
    rw [idealSetInteger,
      mixedEmbedding_preimageOfMemIntegerSet,
      idealSetEquiv_apply]
  have haembed' :
      mixedEmbedding K ((idealSetInteger K J a' : 𝓞 K) : K) =
        (a' : mixedSpace K) := by
    rw [idealSetInteger,
      mixedEmbedding_preimageOfMemIntegerSet,
      idealSetEquiv_apply]
  have hsmul : v • (a : mixedSpace K) = (a' : mixedSpace K) := by
    rw [unitSMul_smul]
    grind
  have hv : v ∈ torsion K :=
    (unit_smul_mem_iff_mem_torsion a.prop.1 v).mp
      (hsmul ▸ a'.prop.1)
  have hvshift :
      v = fundamentalUnitForShift (z' + -z) := by
    rw [fundamentalUnitForShift_add,
      fundamentalUnitForShift_neg]
  have hp :
      ((⟨v, hv⟩ : torsion K), (0 : unitShiftIndex K)) =
        (1, z' + -z) := by
    apply (unitDecompositionEquiv K).injective
    simp_all
  have : z' = z := by grind
  subst z'
  apply Prod.ext
  · apply idealSetInteger_injective K J
    exact mul_left_cancel₀ (Units.ne_zero _) hval
  · simp

open Classical in
theorem surjective_idealElementDecompositionMap
    (J : (Ideal (𝓞 K))⁰) :
    Function.Surjective (idealElementDecompositionMap K J) := by
  intro x
  have hxemb :
      mixedEmbedding K ((x : 𝓞 K) : K) ≠ 0 := by
    exact (map_ne_zero_iff (mixedEmbedding K)
      (mixedEmbedding_injective K)).mpr
        (RingOfIntegers.coe_ne_zero_iff.mpr x.prop.2)
  have hxnorm :
      mixedEmbedding.norm
          (mixedEmbedding K ((x : 𝓞 K) : K)) ≠ 0 :=
    (norm_eq_zero_iff'
      (Set.mem_range_self ((x : 𝓞 K) : K))).not.mpr hxemb
  obtain ⟨u, hu⟩ :=
    exists_unit_smul_mem hxnorm
  let a : idealSet K J :=
    ⟨u • mixedEmbedding K ((x : 𝓞 K) : K),
      mem_idealSet.mpr
        ⟨hu, ⟨(u : 𝓞 K) * x,
          (J : Ideal (𝓞 K)).mul_mem_left _ x.prop.1, by
            simp⟩⟩⟩
  have haInteger :
      idealSetInteger K J a = (u : 𝓞 K) * x := by
    apply RingOfIntegers.coe_injective
    apply mixedEmbedding_injective K
    rw [idealSetInteger,
      mixedEmbedding_preimageOfMemIntegerSet,
      idealSetEquiv_apply]
    change u • mixedEmbedding K ((x : 𝓞 K) : K) =
      mixedEmbedding K (((u : 𝓞 K) * x : 𝓞 K) : K)
    simp
  let p := (unitDecompositionEquiv K).symm u
  let ζ : torsion K := p.1
  let z : unitShiftIndex K := p.2
  have huDecomp :
      (ζ : (𝓞 K)ˣ) * fundamentalUnitForShift z = u := by
    have hp := (unitDecompositionEquiv K).apply_symm_apply u
    change unitDecompositionEquiv K (ζ, z) = u at hp
    simp_all
  have hζinv : ((ζ : (𝓞 K)ˣ)⁻¹) ∈ torsion K :=
    (torsion K).inv_mem ζ.prop
  let b : idealSet K J :=
    ⟨((ζ : (𝓞 K)ˣ)⁻¹) • (a : mixedSpace K),
      mem_idealSet.mpr
        ⟨torsion_smul_mem_of_mem a.prop.1 hζinv,
          ⟨(↑((ζ : (𝓞 K)ˣ)⁻¹) : 𝓞 K) *
              idealSetInteger K J a,
            (J : Ideal (𝓞 K)).mul_mem_left _
              (idealSetInteger_mem K J a), by
              rw [unitSMul_smul]
              push_cast
              rw [map_mul]
              rw [idealSetInteger,
                mixedEmbedding_preimageOfMemIntegerSet,
                idealSetEquiv_apply]⟩⟩⟩
  have hbInteger :
      idealSetInteger K J b =
        (↑((ζ : (𝓞 K)ˣ)⁻¹) : 𝓞 K) *
          idealSetInteger K J a := by
    apply RingOfIntegers.coe_injective
    apply mixedEmbedding_injective K
    rw [idealSetInteger,
      mixedEmbedding_preimageOfMemIntegerSet,
      idealSetEquiv_apply]
    change ((ζ : (𝓞 K)ˣ)⁻¹) • (a : mixedSpace K) =
      mixedEmbedding K
        ((((↑((ζ : (𝓞 K)ˣ)⁻¹) : 𝓞 K) *
          idealSetInteger K J a : 𝓞 K) : K))
    rw [unitSMul_smul]
    push_cast
    rw [map_mul]
    rw [idealSetInteger,
      mixedEmbedding_preimageOfMemIntegerSet,
      idealSetEquiv_apply]
  refine ⟨(b, z), ?_⟩
  apply Subtype.ext
  change
    ((fundamentalUnitForShift z)⁻¹ : (𝓞 K)ˣ) *
        idealSetInteger K J b = x
  rw [hbInteger, haInteger, ← huDecomp]
  calc
    (↑((fundamentalUnitForShift z)⁻¹) : 𝓞 K) *
        ((↑((ζ : (𝓞 K)ˣ)⁻¹) : 𝓞 K) *
          (((ζ : (𝓞 K)ˣ) : 𝓞 K) *
            (fundamentalUnitForShift z : 𝓞 K) * x)) =
      ((↑((fundamentalUnitForShift z)⁻¹) : 𝓞 K) *
          (↑((ζ : (𝓞 K)ˣ)⁻¹) : 𝓞 K) *
          ((ζ : (𝓞 K)ˣ) : 𝓞 K) *
          (fundamentalUnitForShift z : 𝓞 K)) * x := by ring
    _ = x := by simp

open Classical in

noncomputable def idealElementDecompositionEquiv
    (J : (Ideal (𝓞 K))⁰) :
    idealSet K J × unitShiftIndex K ≃ nonzeroIdealElement K J :=
  Equiv.ofBijective (idealElementDecompositionMap K J)
    ⟨injective_idealElementDecompositionMap K J,
      surjective_idealElementDecompositionMap K J⟩

open Classical in
@[simp]
theorem idealElementDecompositionEquiv_apply
    (J : (Ideal (𝓞 K))⁰)
    (p : idealSet K J × unitShiftIndex K) :
    idealElementDecompositionEquiv K J p =
      idealElementDecompositionMap K J p := by
  rfl

open Classical in

def unitShiftNegEquiv : unitShiftIndex K ≃ unitShiftIndex K where
  toFun z := -z
  invFun z := -z
  left_inv z := neg_neg z
  right_inv z := neg_neg z

open Classical in

noncomputable def idealElementMulDecompositionEquiv
    (J : (Ideal (𝓞 K))⁰) :
    idealSet K J × unitShiftIndex K ≃ nonzeroIdealElement K J :=
  (Equiv.prodCongr (Equiv.refl _) (unitShiftNegEquiv K)).trans
    (idealElementDecompositionEquiv K J)

open Classical in
@[simp]
theorem idealElementMulDecompositionEquiv_coe
    (J : (Ideal (𝓞 K))⁰)
    (p : idealSet K J × unitShiftIndex K) :
    (((idealElementMulDecompositionEquiv K J p :
        nonzeroIdealElement K J) : 𝓞 K) : K) =
      ((fundamentalUnitForShift p.2 : (𝓞 K)ˣ) : K) *
        idealSetElement K J p.1 := by
  change
    (((idealElementDecompositionEquiv K J (p.1, -p.2) :
        nonzeroIdealElement K J) : 𝓞 K) : K) = _
  simp

theorem countable_idealSet (J : (Ideal (𝓞 K))⁰) : Countable (idealSet K J) := by
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (𝓞 K) := RingOfIntegers.coe_injective.countable
  exact (idealSetInteger_injective K J).countable

theorem countable_nonzeroIdealElement (J : (Ideal (𝓞 K))⁰) :
    Countable (nonzeroIdealElement K J) := by
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (𝓞 K) := RingOfIntegers.coe_injective.countable
  infer_instance

end DedekindZetaZeroFree.Theta

end

end

/- Source module: DedekindZetaZeroFree.Theta.Unfolding.UnitSlabRadialAngularIntegration -/

section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Port of `LeanPool/Odlyzko/CompletedZeta/UnitSlabTranslation.lean`,
`UnitSlabRadial.lean`, and `UnitSlabRadialIntegral.lean` from
https://github.com/LeanPool/lean-pool at exact revision
`68aa6ee63d20ad76bcc15f595adfc72949991f06` (Lean 4.35.0-rc3, ported to rc2).
Original copyright and author attribution are retained above. Released under
Apache 2.0; full license: repository root `LICENSE`.
Source changes are imports, module visibility syntax, and namespace.
-/

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units Set
  dirichletUnitTheorem

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

open DedekindZetaZeroFree.Theta
open mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

open Classical in

noncomputable def unitCoordinateShiftHom :
    ({w : InfinitePlace K // w ≠ w₀} → ℤ) →+
      mixedEmbedding.realSpace K where
  toFun := unitCoordinateShift
  map_zero' := by
    ext w
    by_cases hw : w = w₀ <;> simp [unitCoordinateShift, hw]
  map_add' z z' := by
    ext w
    by_cases hw : w = w₀ <;> simp [unitCoordinateShift, hw]

open Classical in
@[simp]
theorem unitCoordinateShiftHom_apply
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    unitCoordinateShiftHom (K := K) z = unitCoordinateShift z :=
  rfl

open Classical in

def unitAngularParamSet (K : Type*) [Field K] [NumberField K] :
    Set ({w : InfinitePlace K // w ≠ w₀} → ℝ) :=
  Set.univ.pi fun _ ↦ Ico 0 1

open Classical in
theorem measurableSet_unitAngularParamSet :
    MeasurableSet (unitAngularParamSet K) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico

open Classical in

def unitRadialAngularEquiv :
    mixedEmbedding.realSpace K ≃ᵐ
      (ℝ × ({w : InfinitePlace K // w ≠ w₀} → ℝ)) where
  toFun y := (y w₀, fun w ↦ y w)
  invFun p w := if hw : w = w₀ then p.1 else p.2 ⟨w, hw⟩
  left_inv y := by
    ext w
    by_cases hw : w = w₀ <;> simp [hw]
  right_inv p := by
    rcases p with ⟨a, u⟩
    apply Prod.ext
    · simp
    · funext w
      simp [w.prop]
  measurable_toFun :=
    (measurable_pi_apply w₀).prodMk (measurable_pi_lambda _ fun w ↦ measurable_pi_apply w.val)
  measurable_invFun := by
    apply measurable_pi_lambda
    intro w
    change Measurable (fun p : ℝ × ({w : InfinitePlace K // w ≠ w₀} → ℝ) ↦
      if hw : w = w₀ then p.1 else p.2 ⟨w, hw⟩)
    by_cases hw : w = w₀
    · simpa [hw] using
        (measurable_fst : Measurable (fun p : ℝ × ({w : InfinitePlace K // w ≠ w₀} → ℝ) ↦ p.1))
    · simpa only [dif_neg hw, Function.comp_def] using
        ((measurable_pi_apply (⟨w, hw⟩ : {w : InfinitePlace K // w ≠ w₀})).comp
          (measurable_snd : Measurable (fun p : ℝ × ({w : InfinitePlace K // w ≠ w₀} → ℝ) ↦ p.2)))

open Classical in

def unitSlabCoordinates (a : ℝ) (u : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mixedEmbedding.realSpace K :=
  (unitRadialAngularEquiv (K := K)).symm (a, u)

open Classical in
@[simp] theorem unitSlabCoordinates_apply_w₀
    (a : ℝ) (u : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    unitSlabCoordinates a u w₀ = a := by
  simp [unitSlabCoordinates, unitRadialAngularEquiv]

open Classical in
@[simp] theorem unitSlabCoordinates_apply_ne
    (a : ℝ) (u : {w : InfinitePlace K // w ≠ w₀} → ℝ)
    (w : {w : InfinitePlace K // w ≠ w₀}) :
    unitSlabCoordinates a u w = u w := by
  simp [unitSlabCoordinates, unitRadialAngularEquiv, w.prop]

open Classical in
theorem measurePreserving_unitRadialAngularEquiv :
    MeasurePreserving (unitRadialAngularEquiv (K := K)) volume
      ((volume : Measure ℝ).prod
        (volume : Measure ({w : InfinitePlace K // w ≠ w₀} → ℝ))) := by
  letI : Fintype {w : InfinitePlace K // w = w₀} := Unique.fintype
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : InfinitePlace K ↦ ℝ)
    (fun w ↦ w = w₀)
  have he := volume_preserving_piEquivPiSubtypeProd (fun _ : InfinitePlace K ↦ ℝ)
    (fun w ↦ w = w₀)
  rw [Measure.volume_eq_prod] at he
  have hf := (volume_preserving_funUnique {w : InfinitePlace K // w = w₀} ℝ).prod
    (MeasurePreserving.id (volume : Measure ({w : InfinitePlace K // w ≠ w₀} → ℝ)))
  have he' : MeasurePreserving e volume
      ((volume : Measure ({w : InfinitePlace K // w = w₀} → ℝ)).prod
        (volume : Measure ({w : InfinitePlace K // w ≠ w₀} → ℝ))) := by
    convert he using 1 <;> congr 4 <;> exact Subsingleton.elim _ _
  have hdefault : (default : {w : InfinitePlace K // w = w₀}).val = w₀ :=
    (default : {w : InfinitePlace K // w = w₀}).prop
  simpa [unitRadialAngularEquiv, e, Function.comp_def,
    MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
    MeasurableEquiv.piUnique, Equiv.piEquivPiSubtypeProd, Prod.map, hdefault] using hf.comp he'

open Classical in
theorem unitRadialAngularEquiv_image_radialSlab (s : Set ℝ) :
    (unitRadialAngularEquiv (K := K)) ''
      (unitFundamentalParamSet K ∩ {y | y w₀ ∈ s}) =
        s ×ˢ unitAngularParamSet K := by
  rw [MeasurableEquiv.image_eq_preimage_symm]
  ext p
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_prod]
  change ((unitSlabCoordinates p.1 p.2 ∈ unitFundamentalParamSet K) ∧
    unitSlabCoordinates p.1 p.2 w₀ ∈ s) ↔ _
  rw [unitSlabCoordinates_apply_w₀, mem_unitFundamentalParamSet_iff]
  have hunit : (∀ w : InfinitePlace K, w ≠ w₀ →
      unitSlabCoordinates p.1 p.2 w ∈ Ico (0 : ℝ) 1) ↔ p.2 ∈ unitAngularParamSet K := by
    constructor
    · intro h
      change ∀ w ∈ Set.univ, p.2 w ∈ Ico (0 : ℝ) 1
      intro w _
      simpa using h w w.prop
    · intro h w hw
      have h' : ∀ i : {w : InfinitePlace K // w ≠ w₀}, p.2 i ∈ Ico (0 : ℝ) 1 := by
        simpa [unitAngularParamSet] using h
      simpa [unitSlabCoordinates, unitRadialAngularEquiv, hw] using h' ⟨w, hw⟩
  rw [hunit, and_comm]

open Classical in

theorem integrableOn_radialSlab_iff
    {E : Type*} [NormedAddCommGroup E]
    (f : mixedEmbedding.realSpace K → E) (s : Set ℝ) :
    IntegrableOn f (unitFundamentalParamSet K ∩ {y | y w₀ ∈ s}) ↔
      IntegrableOn (fun p ↦ unitSlabCoordinates (K := K) p.1 p.2 |> f)
        (s ×ˢ unitAngularParamSet K)
        ((volume : Measure ℝ).prod
          (volume : Measure ({w : InfinitePlace K // w ≠ w₀} → ℝ))) := by
  let e := unitRadialAngularEquiv (K := K)
  have he := measurePreserving_unitRadialAngularEquiv (K := K)
  have hpre : e.symm ⁻¹' (unitFundamentalParamSet K ∩ {y | y w₀ ∈ s}) =
      s ×ˢ unitAngularParamSet K := by
    rw [← MeasurableEquiv.image_eq_preimage_symm]
    exact unitRadialAngularEquiv_image_radialSlab s
  have h := (he.symm e).integrableOn_comp_preimage e.symm.measurableEmbedding
    (f := f) (s := unitFundamentalParamSet K ∩ {y | y w₀ ∈ s})
  rw [hpre] at h
  exact h.symm

open Classical in

theorem setIntegral_radialSlab_eq_radialAngular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E) (s : Set ℝ)
    (hf : IntegrableOn f (unitFundamentalParamSet K ∩ {y | y w₀ ∈ s})) :
    (∫ y in unitFundamentalParamSet K ∩ {y | y w₀ ∈ s}, f y) =
      ∫ a in s, ∫ u in unitAngularParamSet K, f (unitSlabCoordinates a u) := by
  let e := unitRadialAngularEquiv (K := K)
  have he := measurePreserving_unitRadialAngularEquiv (K := K)
  have hchange := he.setIntegral_image_emb e.measurableEmbedding
    (fun p ↦ f (e.symm p)) (unitFundamentalParamSet K ∩ {y | y w₀ ∈ s})
  rw [unitRadialAngularEquiv_image_radialSlab] at hchange
  change (∫ p in s ×ˢ unitAngularParamSet K, f (e.symm p)
    ∂(volume : Measure ℝ).prod (volume : Measure ({w : InfinitePlace K // w ≠ w₀} → ℝ))) =
    (∫ y in unitFundamentalParamSet K ∩ {y | y w₀ ∈ s}, f (e.symm (e y))) at hchange
  simp only [MeasurableEquiv.symm_apply_apply] at hchange
  rw [← hchange]
  exact setIntegral_prod (fun p ↦ f (e.symm p)) ((integrableOn_radialSlab_iff f s).mp hf)

open Classical in

theorem setIntegral_unitFundamentalParamSet_eq_radialAngular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E)
    (hf : IntegrableOn f (unitFundamentalParamSet K)) :
    (∫ y in unitFundamentalParamSet K, f y) =
      ∫ a : ℝ, ∫ u in unitAngularParamSet K, f (unitSlabCoordinates a u) := by
  simpa using setIntegral_radialSlab_eq_radialAngular f Set.univ (by simpa using hf)

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

/- Source module: DedekindZetaZeroFree.Theta.Profiles.MixedThetaDefinitions -/

section

noncomputable section

open Classical MeasureTheory NumberField NumberField.InfinitePlace
  NumberField.Units NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding.fundamentalCone
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

abbrev Angular := {v : InfinitePlace K // v ≠ w₀} → ℝ

def angularLift (u : Angular K) : mixedEmbedding.realSpace K :=
  fun v ↦ if h : v = w₀ then 0 else u ⟨v, h⟩

def radialLift (a : ℝ) : mixedEmbedding.realSpace K :=
  fun v ↦ if v = w₀ then a else 0

def angularCube : Set (Angular K) :=
  Set.univ.pi (fun _ ↦ Set.Ico (0 : ℝ) 1)

def mixedThetaCovolume (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
    Real.sqrt |(discr K : ℝ)|

def mixedThetaShape (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (u : Angular K) : InfinitePlace K → ℝ :=
  expMapBasis (angularLift K u +
    radialLift K ((Real.log t - Real.log (mixedThetaCovolume K I)) /
      (Module.finrank ℚ K : ℝ)))

def mixedRadialTheta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (u : Angular K) : ℂ :=
  fractionalShapeIdealTheta K I (mixedThetaShape K I t u)
    (fun v ↦ ne_of_gt (expMapBasis_pos _ v))

def mixedAngularAverage (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℂ :=
  ∫ u in angularCube K, mixedRadialTheta K I t u

def mixedNegAngularAverage (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℂ :=
  ∫ u in angularCube K, mixedRadialTheta K I t (-u)

def alpha : ℝ :=
  (2 : ℝ) ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K /
    (torsionOrder K : ℝ)

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

/- Source module: DedekindZetaZeroFree.Geometry.TranslatedLatticeGap -/

section

namespace DedekindZetaZeroFree

theorem thetaTranslateGap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] (z : E) :
    ∃ η : ℝ, 0 < η ∧ ∀ ℓ : L, z + (ℓ : E) ≠ 0 → η ≤ ‖z + (ℓ : E)‖ := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hdisc : IsDiscrete ((L : Set E)) := DiscreteTopology.isDiscrete
  have hclosed : IsClosed ((L : Set E)) :=
    AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)

  have hbdd : Bornology.IsBounded (Metric.closedBall (0 : E) (1 + ‖z‖)) :=
    Metric.isBounded_closedBall
  have hSfin : Set.Finite ({x : E | x ∈ (L : Set E) ∧ ‖z + x‖ ≤ 1}) := by
    refine (Metric.finite_isBounded_inter_isClosed hdisc hbdd hclosed).subset ?_
    intro x hx
    refine ⟨?_, hx.1⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖x‖ ≤ ‖z + x‖ + ‖z‖ := by
      have := norm_sub_le (z + x) z
      simpa using this
    linarith [hx.2]
  have hfin : Set.Finite ({ℓ : L | ‖z + (ℓ : E)‖ ≤ 1} : Set L) :=
    (hSfin.preimage_embedding (Function.Embedding.subtype (· ∈ (L : Set E)))).subset
      (by intro ℓ hℓ; exact ⟨ℓ.2, hℓ⟩)
  rcases Set.eq_empty_or_nonempty
      ({ℓ : L | z + (ℓ : E) ≠ 0 ∧ ‖z + (ℓ : E)‖ ≤ 1} : Set L) with hempty | hne
  ·
    refine ⟨1, one_pos, fun ℓ hℓ => ?_⟩
    by_contra hcon
    have h2 : ‖z + (ℓ : E)‖ ≤ 1 := le_of_lt (not_le.mp hcon)
    have hmem : ℓ ∈ ({ℓ : L | z + (ℓ : E) ≠ 0 ∧ ‖z + (ℓ : E)‖ ≤ 1} : Set L) := ⟨hℓ, h2⟩
    rw [hempty] at hmem
    exact hmem
  · have hfin' : ({ℓ : L | z + (ℓ : E) ≠ 0 ∧ ‖z + (ℓ : E)‖ ≤ 1} : Set L).Finite :=
      hfin.subset (by intro ℓ hℓ; exact hℓ.2)
    obtain ⟨b, hb, hmin⟩ :=
      Set.exists_min_image _ (fun ℓ : L => ‖z + (ℓ : E)‖) hfin' hne
    refine ⟨min 1 ‖z + (b : E)‖, lt_min one_pos (norm_pos_iff.mpr hb.1), fun ℓ hℓ => ?_⟩
    by_cases h2 : ‖z + (ℓ : E)‖ ≤ 1
    · have hmem : ℓ ∈ ({ℓ : L | z + (ℓ : E) ≠ 0 ∧ ‖z + (ℓ : E)‖ ≤ 1} : Set L) :=
        ⟨hℓ, h2⟩
      exact (min_le_right _ _).trans (hmin ℓ hmem)
    · exact (min_le_left _ _).trans (le_of_lt (not_le.mp h2))

end DedekindZetaZeroFree

end

/- Source module: DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.UniformGaussianTail -/

section

namespace DedekindZetaZeroFree

theorem thetaUniformGaussianTail
    {ι : Type*} [Countable ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} (x : ι → E) (S : Set H) (F : ℝ → H → ι → ℂ)
    (P c p η : ℝ) (hP : 0 < P) (hc : 0 < c) (hp : 0 < p) (hη : 0 < η)
    (hgap : ∀ i, η ≤ ‖x i‖)
    (hsum : Summable (fun i => Real.exp (-(c / 2) * ‖x i‖ ^ 2)))
    (hbound : ∀ t : ℝ, 1 ≤ t → ∀ h ∈ S, ∀ i,
      ‖F t h i‖ ≤ P * Real.exp (-c * t ^ p * ‖x i‖ ^ 2)) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, 1 ≤ t → ∀ h ∈ S,
      Summable (F t h) ∧
        ‖∑' i, F t h i‖ ≤ A * Real.exp (-(c * η ^ 2 / 2) * t ^ p) := by
  set G : ι → ℝ := fun i => Real.exp (-(c / 2) * ‖x i‖ ^ 2) with hG
  have hGsum : Summable G := by simpa only [hG] using hsum
  have hGnonneg : ∀ i, 0 ≤ G i := fun i => by rw [hG]; exact Real.exp_nonneg _
  have hGtsum : 0 ≤ ∑' i, G i := tsum_nonneg hGnonneg
  have hc2 : 0 ≤ c / 2 := by positivity
  refine ⟨P * (1 + ∑' i, G i), mul_pos hP (by linarith), ?_⟩
  intro t ht h hh
  have htp : 1 ≤ t ^ p := Real.one_le_rpow ht hp.le
  set E' : ℝ := Real.exp (-(c * η ^ 2 / 2) * t ^ p) with hE'
  have hE'pos : 0 < E' := Real.exp_pos _
  have hpoint : ∀ i, ‖F t h i‖ ≤ (P * E') * G i := by
    intro i
    have hxnonneg : 0 ≤ ‖x i‖ := norm_nonneg _
    have hη2 : η ^ 2 ≤ ‖x i‖ ^ 2 := by nlinarith [hη.le, hgap i, hxnonneg]
    have hexp_eq : Real.exp (-c * t ^ p * ‖x i‖ ^ 2)
        = Real.exp (-(c / 2) * t ^ p * ‖x i‖ ^ 2)
          * Real.exp (-(c / 2) * t ^ p * ‖x i‖ ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hle1 : Real.exp (-(c / 2) * t ^ p * ‖x i‖ ^ 2) ≤ E' := by
      rw [hE', Real.exp_le_exp]
      have hmul : (c / 2) * t ^ p * η ^ 2 ≤ (c / 2) * t ^ p * ‖x i‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hη2 (by positivity)
      have heq : (c * η ^ 2 / 2) * t ^ p = (c / 2) * t ^ p * η ^ 2 := by ring
      linarith [hmul, heq]
    have hle2 : Real.exp (-(c / 2) * t ^ p * ‖x i‖ ^ 2) ≤ G i := by
      rw [hG, Real.exp_le_exp]
      have hA : 0 ≤ (c / 2) * ‖x i‖ ^ 2 := mul_nonneg hc2 (sq_nonneg _)
      have h1 : (c / 2) * ‖x i‖ ^ 2 * (t ^ p - 1) ≥ 0 :=
        mul_nonneg hA (by linarith)
      nlinarith [h1]
    have hprod : Real.exp (-c * t ^ p * ‖x i‖ ^ 2) ≤ E' * G i := by
      rw [hexp_eq]
      exact mul_le_mul hle1 hle2 (Real.exp_nonneg _) hE'pos.le
    calc ‖F t h i‖ ≤ P * Real.exp (-c * t ^ p * ‖x i‖ ^ 2) := hbound t ht h hh i
      _ ≤ P * (E' * G i) := mul_le_mul_of_nonneg_left hprod hP.le
      _ = (P * E') * G i := by ring
  have hsumPE : Summable (fun i => (P * E') * G i) := hGsum.mul_left (P * E')
  have hnormsum : Summable (fun i => ‖F t h i‖) :=
    Summable.of_norm_bounded hsumPE fun i => by simpa using hpoint i
  have hFsum : Summable (F t h) := hnormsum.of_norm
  refine ⟨hFsum, ?_⟩
  have step1 : ‖∑' i, F t h i‖ ≤ ∑' i, ‖F t h i‖ := norm_tsum_le_tsum_norm hnormsum
  have step2 : ∑' i, ‖F t h i‖ ≤ ∑' i, (P * E') * G i :=
    hnormsum.tsum_le_tsum hpoint hsumPE
  have step3 : ∑' i, (P * E') * G i = (P * E') * ∑' i, G i := tsum_mul_left
  have step4 : (P * E') * ∑' i, G i ≤ (P * (1 + ∑' i, G i)) * E' := by
    have hPE : 0 ≤ P * E' := mul_nonneg hP.le hE'pos.le
    nlinarith [hPE]
  calc ‖∑' i, F t h i‖ ≤ ∑' i, ‖F t h i‖ := step1
    _ ≤ ∑' i, (P * E') * G i := step2
    _ = (P * E') * ∑' i, G i := step3
    _ ≤ (P * (1 + ∑' i, G i)) * E' := step4
    _ = (P * (1 + ∑' i, G i)) * Real.exp (-(c * η ^ 2 / 2) * t ^ p) := by rw [hE']

end DedekindZetaZeroFree

end

/- Source module: DedekindZetaZeroFree.Theta.Profiles.UniformMixedThetaTail -/

section

noncomputable section

open Classical NumberField NumberField.InfinitePlace
open NumberField.mixedEmbedding.fundamentalCone
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

private theorem continuous_angularLift : Continuous (angularLift K) := by
  apply continuous_pi
  intro v
  by_cases h : v = NumberField.Units.dirichletUnitTheorem.w₀
  · simpa [angularLift, h] using (continuous_const : Continuous (fun _ : Angular K => (0 : ℝ)))
  · simpa [angularLift, h] using (continuous_apply (⟨v,h⟩ : {v : InfinitePlace K // v ≠ NumberField.Units.dirichletUnitTheorem.w₀}))
private theorem continuous_radialLift : Continuous (radialLift K) := by
  apply continuous_pi
  intro v
  by_cases h : v = NumberField.Units.dirichletUnitTheorem.w₀
  · change Continuous (fun x : ℝ => if v = NumberField.Units.dirichletUnitTheorem.w₀ then x else 0)
    simp only [if_pos h]
    fun_prop
  · simpa [radialLift, h] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
private theorem continuousOn_shape (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
  ContinuousOn (fun p : ℝ × Angular K => mixedThetaShape K I p.1 p.2)
    (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  apply (continuous_expMapBasis K).comp_continuousOn
  apply ((continuous_angularLift K).comp continuous_snd).continuousOn.add
  apply (continuous_radialLift K).comp_continuousOn
  apply ContinuousOn.div_const
  apply ContinuousOn.sub _ continuousOn_const
  apply Real.continuousOn_log.comp continuous_fst.continuousOn
  intro p hp
  exact ne_of_gt hp.1
private theorem continuous_scale_family :
  Continuous (fun p : (InfinitePlace K → ℝ) × NumberField.mixedEmbedding.euclidean.mixedSpace K =>
    (traceToMixed K).symm (NumberField.mixedEmbedding.mixedSpaceOfRealSpace p.1 * traceToMixed K p.2)) := by
  apply (traceToMixed K).symm.continuous.comp
  apply Continuous.mul _ ((traceToMixed K).continuous.comp continuous_snd)
  exact (NumberField.mixedEmbedding.mixedSpaceOfRealSpace (K := K)).continuous.comp continuous_fst
private theorem uniform_lower_scale
    (T : Set (InfinitePlace K → ℝ)) (hT : IsCompact T)
    (hpos : ∀ q ∈ T, ∀ v, q v ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ q, ∀ hq : q ∈ T, ∀ x : NumberField.mixedEmbedding.euclidean.mixedSpace K,
      d * ‖x‖ ≤ ‖traceRadialScale K q (hpos q hq) x‖ := by
  let E := NumberField.mixedEmbedding.euclidean.mixedSpace K
  let F : (InfinitePlace K → ℝ) × E → E := fun p =>
    (traceToMixed K).symm (NumberField.mixedEmbedding.mixedSpaceOfRealSpace p.1 * traceToMixed K p.2)
  have hc : IsCompact (T ×ˢ Metric.sphere (0 : E) 1) := hT.prod (isCompact_sphere _ _)
  obtain ⟨d, hd, hbound⟩ := hc.exists_forall_le' (continuous_scale_family K).norm.continuousOn (a := 0) (by
    intro p hp
    have heq : F p = traceRadialScale K p.1 (hpos _ hp.1) p.2 := by
      apply (traceToMixed K).injective
      simp [F, traceToMixed_traceRadialScale]
    change 0 < ‖F p‖
    rw [heq, norm_pos_iff]
    intro hz
    have : p.2 = 0 := (traceRadialScale K p.1 (hpos _ hp.1)).injective (by simpa using hz)
    have hs : dist p.2 0 = 1 := hp.2
    rw [this, dist_self] at hs
    norm_num at hs)
  refine ⟨d, hd, ?_⟩
  intro q hq x
  by_cases hx : x = 0
  · simp [hx]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hnorm.ne']
  have hb := hbound (q, (‖x‖⁻¹ : ℝ) • x) ⟨hq, by simpa [Metric.mem_sphere, dist_eq_norm] using hy⟩
  have heq : F (q, (‖x‖⁻¹ : ℝ) • x) = traceRadialScale K q (hpos q hq) ((‖x‖⁻¹ : ℝ) • x) := by
    apply (traceToMixed K).injective
    simp [F, traceToMixed_traceRadialScale]
  change d ≤ ‖F (q, (‖x‖⁻¹ : ℝ) • x)‖ at hb
  rw [heq, map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at hb
  calc
    d * ‖x‖ ≤ (‖x‖⁻¹ * ‖traceRadialScale K q (hpos q hq) x‖) * ‖x‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = _ := by field_simp
private theorem theta_tsum_fixed (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ v, q v ≠ 0) :
    fractionalShapeIdealTheta K I q hq =
      ∑' x : traceIdealLattice K I, latticeGaussian Real.pi (traceRadialScale K q hq x) := by
  let e : traceIdealLattice K I ≃ shapeIdealLattice K I q hq := {
    toFun := fun x => ⟨traceRadialScale K q hq x, by
      change (traceRadialScale K q hq).symm (traceRadialScale K q hq x) ∈ traceIdealLattice K I
      simpa using x.prop⟩
    invFun := fun x => ⟨(traceRadialScale K q hq).symm x, x.prop⟩
    left_inv := fun x => by ext; simp
    right_inv := fun x => by ext; simp }
  exact (e.tsum_eq (fun x => latticeGaussian Real.pi (x : NumberField.mixedEmbedding.euclidean.mixedSpace K))).symm

private theorem shape_radial (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (ht : 0 < t) (u : Angular K) :
    mixedThetaShape K I t u = t ^ (1 / (Module.finrank ℚ K : ℝ)) • mixedThetaShape K I 1 u := by
  let n : ℝ := Module.finrank ℚ K
  have hshape (s : ℝ) : mixedThetaShape K I s u =
      Real.exp ((Real.log s - Real.log (mixedThetaCovolume K I)) / n) • expMapBasis (angularLift K u) := by
    rw [mixedThetaShape, expMapBasis_apply'']
    congr 1
    · simp [angularLift, radialLift, n]
    · congr 1
      funext v
      by_cases hv : v = NumberField.Units.dirichletUnitTheorem.w₀
      · simp [angularLift, radialLift, hv]
      · simp [angularLift, radialLift, hv]
  rw [hshape t, hshape 1, smul_smul, Real.rpow_def_of_pos ht, ← Real.exp_add]
  congr 2
  simp only [Real.log_one]
  ring
set_option maxHeartbeats 800000 in
private theorem scale_shape_radial (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (ht : 0 < t) (u : Angular K)
    (x : NumberField.mixedEmbedding.euclidean.mixedSpace K) :
    traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) x =
    t ^ (1 / (Module.finrank ℚ K : ℝ)) •
      traceRadialScale K (mixedThetaShape K I 1 u) (fun v => ne_of_gt (expMapBasis_pos _ v)) x := by
  apply (traceToMixed K).injective
  simp only [traceToMixed_traceRadialScale, map_smul]
  rw [shape_radial K I t ht u, map_smul, smul_mul_assoc]

set_option maxHeartbeats 3000000 in

theorem mixedRadialTheta_uniform_exponential_tail
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (S : Set (Angular K)) (hS : IsCompact S) :
    ∃ B b : ℝ, 0 < B ∧ 0 < b ∧
      ∀ t : ℝ, 1 ≤ t → ∀ u ∈ S,
        ‖mixedRadialTheta K I t u - 1‖ ≤
          B * Real.exp (-b * t ^ (2 / (Module.finrank ℚ K : ℝ))) := by
  let L := traceIdealLattice K I
  let E := NumberField.mixedEmbedding.euclidean.mixedSpace K
  let X := {x : L // x ≠ 0}
  let T := (mixedThetaShape K I 1) '' S
  have hT : IsCompact T := by
    apply hS.image_of_continuousOn
    change ContinuousOn (fun u => expMapBasis (angularLift K u + radialLift K ((Real.log 1 - Real.log (mixedThetaCovolume K I)) / (Module.finrank ℚ K : ℝ)))) S
    exact ((continuous_expMapBasis K).comp ((continuous_angularLift K).add continuous_const)).continuousOn
  have hn : ∀ q ∈ T, ∀ v, q v ≠ 0 := by
    intro q hq v
    obtain ⟨u, hu, rfl⟩ := hq
    exact ne_of_gt (expMapBasis_pos _ _)
  obtain ⟨d, hd, hb⟩ := uniform_lower_scale K T hT hn
  obtain ⟨η, hη, hgap⟩ := DedekindZetaZeroFree.thetaTranslateGap L (0 : E)
  let c := Real.pi * d ^ 2
  let p := 2 / (Module.finrank ℚ K : ℝ)
  have hc : 0 < c := mul_pos Real.pi_pos (sq_pos_of_pos hd)
  have hp : 0 < p := div_pos (by norm_num) (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K)))
  let F : ℝ → Angular K → X → ℂ := fun t u x => latticeGaussian Real.pi
    (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (x.val : E))
  have hs : Summable (fun x : X => Real.exp (-(c / 2) * ‖(x.val : E)‖ ^ 2)) := by
    have hh := ((summable_latticeGaussian L (half_pos hc)).norm).subtype (fun x => x ≠ 0)
    change Summable (fun x : {x : L // x ≠ 0} => Real.exp (-(c / 2) * ‖(x.val : E)‖ ^ 2))
    simpa only [Function.comp_def, norm_latticeGaussian] using hh
  have hg : ∀ x : X, η ≤ ‖(x.val : E)‖ := by
    intro x
    have hxx : (x.val : E) ≠ 0 := fun hz => x.prop (Subtype.ext hz)
    have hgg := hgap x.val (by simpa only [zero_add] using hxx)
    simpa only [zero_add] using hgg
  have hbound : ∀ t : ℝ, 1 ≤ t → ∀ u ∈ S, ∀ x : X,
      ‖F t u x‖ ≤ 1 * Real.exp (-c * t ^ p * ‖(x.val : E)‖ ^ 2) := by
    intro t ht u hu x
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    change ‖latticeGaussian Real.pi _‖ ≤ _
    rw [norm_latticeGaussian, scale_shape_radial K I t ht0 u, norm_smul,
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), mul_pow, one_mul]
    have hpow : (t ^ (1 / (Module.finrank ℚ K : ℝ))) ^ 2 = t ^ p := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul ht0.le]
      congr 1
      dsimp [p]
      ring
    rw [hpow]
    apply Real.exp_le_exp.mpr
    have hh := hb _ ⟨u, hu, rfl⟩ (x.val : E)
    have hh2 : d ^ 2 * ‖(x.val : E)‖ ^ 2 ≤
        ‖traceRadialScale K (mixedThetaShape K I 1 u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (x.val : E)‖ ^ 2 := by
      simpa only [mul_pow] using (sq_le_sq₀ (mul_nonneg hd.le (norm_nonneg _)) (norm_nonneg _)).mpr hh
    have hmm := mul_le_mul_of_nonneg_left hh2 (mul_nonneg Real.pi_pos.le (Real.rpow_nonneg ht0.le p))
    dsimp [c]
    nlinarith [hmm]
  obtain ⟨B, hB, hres⟩ := DedekindZetaZeroFree.thetaUniformGaussianTail
    (fun x : X => (x.val : E)) S F 1 c p η one_pos hc hp hη hg hs hbound
  refine ⟨B, c * η ^ 2 / 2, hB, div_pos (mul_pos hc (sq_pos_of_pos hη)) (by norm_num), ?_⟩
  intro t ht u hu
  have hres' := hres t ht u hu
  have hfull : Summable (fun x : L => latticeGaussian Real.pi
      (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (x : E))) := by
    let e : L ≃ shapeIdealLattice K I (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) := {
      toFun := fun x => ⟨traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) x, by
        change (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v))).symm (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) x) ∈ traceIdealLattice K I
        rw [ContinuousLinearEquiv.symm_apply_apply]
        exact x.prop⟩
      invFun := fun x => ⟨(traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v))).symm x, x.prop⟩
      left_inv := fun x => by ext; simp
      right_inv := fun x => by ext; simp }
    exact e.summable_iff.mpr (summable_latticeGaussian _ Real.pi_pos)
  have heq : mixedRadialTheta K I t u - 1 = ∑' x : X, F t u x := by
    rw [mixedRadialTheta, theta_tsum_fixed]
    have hh := hfull.tsum_subtype_add_tsum_subtype_compl ({0} : Set L)
    have hsingle : (∑' x : ↥({0} : Set L), latticeGaussian Real.pi (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (x.val : E))) = latticeGaussian Real.pi (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (0 : L)) :=
      tsum_singleton (0 : L) (fun x : L => latticeGaussian Real.pi (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (x : E)))
    rw [hsingle] at hh
    have hz : latticeGaussian Real.pi (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (0 : L)) = 1 := by
      simp [latticeGaussian]
    rw [hz] at hh
    have he : (∑' x : ↥({0} : Set L)ᶜ, latticeGaussian Real.pi (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (x.val : E))) = ∑' x : X, F t u x := by
      rfl
    rw [he] at hh
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hh.symm)
  rw [heq]
  exact hres'.2

theorem mixedRadialTheta_hasSumUniformlyOn
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a b' : ℝ) (ha : 0 < a) (hab : a ≤ b')
    (S : Set (Angular K)) (hS : IsCompact S) :
    HasSumUniformlyOn
      (fun (x : ↥(traceIdealLattice K I)) (p : ℝ × Angular K) ↦
        latticeGaussian Real.pi
          (traceRadialScale K (mixedThetaShape K I p.1 p.2)
            (fun v ↦ ne_of_gt (expMapBasis_pos _ v))
            (x : NumberField.mixedEmbedding.euclidean.mixedSpace K)))
      (fun p : ℝ × Angular K ↦ mixedRadialTheta K I p.1 p.2)
      (Set.Icc a b' ×ˢ S) := by
  let C := Set.Icc a b' ×ˢ S
  have hC : IsCompact C := isCompact_Icc.prod hS
  have hsub : C ⊆ Set.Ioi (0 : ℝ) ×ˢ Set.univ := fun p hp => ⟨lt_of_lt_of_le ha hp.1.1, Set.mem_univ _⟩
  have hc := (continuousOn_shape K I).mono hsub
  let T := (fun p : ℝ × Angular K => mixedThetaShape K I p.1 p.2) '' C
  have hT : IsCompact T := hC.image_of_continuousOn hc
  have hn : ∀ q ∈ T, ∀ v, q v ≠ 0 := by
    intro q hq v
    obtain ⟨p, hp, rfl⟩ := hq
    exact ne_of_gt (expMapBasis_pos _ _)
  obtain ⟨d, hd, hb⟩ := uniform_lower_scale K T hT hn
  have hs := (summable_latticeGaussian (traceIdealLattice K I) (mul_pos Real.pi_pos (sq_pos_of_pos hd))).norm
  have heq : (fun p : ℝ × Angular K => mixedRadialTheta K I p.1 p.2) =
    (fun p => ∑' x : traceIdealLattice K I, latticeGaussian Real.pi
      (traceRadialScale K (mixedThetaShape K I p.1 p.2) (fun v => ne_of_gt (expMapBasis_pos _ v)) x)) := by
    funext p
    exact theta_tsum_fixed K I _ _
  rw [heq]
  apply HasSumUniformlyOn.of_norm_le_summable hs
  intro x p hp
  rw [norm_latticeGaussian, norm_latticeGaussian]
  apply Real.exp_le_exp.mpr
  have hb' := hb _ ⟨p, hp, rfl⟩ x
  have hsquare : d ^ 2 * ‖(x : NumberField.mixedEmbedding.euclidean.mixedSpace K)‖ ^ 2 ≤
    ‖traceRadialScale K (mixedThetaShape K I p.1 p.2) (fun v => ne_of_gt (expMapBasis_pos _ v)) x‖ ^ 2 := by
    have hh := sq_le_sq₀ (mul_nonneg hd.le (norm_nonneg (x : NumberField.mixedEmbedding.euclidean.mixedSpace K))) (norm_nonneg (traceRadialScale K (mixedThetaShape K I p.1 p.2) (fun v => ne_of_gt (expMapBasis_pos _ v)) x))
    simpa only [mul_pow] using hh.mpr hb'
  nlinarith [Real.pi_pos]

private theorem continuousOn_summand (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : traceIdealLattice K I) : ContinuousOn
      (fun p : ℝ × Angular K => latticeGaussian Real.pi
        (traceRadialScale K (mixedThetaShape K I p.1 p.2) (fun v => ne_of_gt (expMapBasis_pos _ v)) x))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have heq : (fun p : ℝ × Angular K => traceRadialScale K (mixedThetaShape K I p.1 p.2) (fun v => ne_of_gt (expMapBasis_pos _ v)) x) =
    (fun p => (traceToMixed K).symm (NumberField.mixedEmbedding.mixedSpaceOfRealSpace (mixedThetaShape K I p.1 p.2) * traceToMixed K x)) := by
    funext p
    apply (traceToMixed K).injective
    simp [traceToMixed_traceRadialScale]
  have hgauss : Continuous (latticeGaussian Real.pi (E := NumberField.mixedEmbedding.euclidean.mixedSpace K)) := by
    unfold latticeGaussian
    fun_prop
  apply hgauss.comp_continuousOn
  rw [heq]
  apply (traceToMixed K).symm.continuous.comp_continuousOn
  apply ContinuousOn.mul _ continuousOn_const
  exact NumberField.mixedEmbedding.mixedSpaceOfRealSpace.continuous.comp_continuousOn (continuousOn_shape K I)

theorem continuousOn_mixedRadialTheta
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (fun p : ℝ × Angular K ↦ mixedRadialTheta K I p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Angular K))) := by
  intro p hp
  have hpp : 0 < p.1 := hp.1
  let a := p.1 / 2
  let b := p.1 + 1
  let S := Metric.closedBall p.2 1
  have ha : 0 < a := half_pos hp.1
  have hab : a ≤ b := by dsimp [a, b]; linarith [hpp]
  have hc : ContinuousOn (fun p : ℝ × Angular K => mixedRadialTheta K I p.1 p.2) (Set.Icc a b ×ˢ S) := by
    apply (mixedRadialTheta_hasSumUniformlyOn K I a b ha hab S (isCompact_closedBall _ _)).tendstoUniformlyOn.continuousOn
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro n
    apply continuousOn_finsetSum
    intro x hx
    apply (continuousOn_summand K I x).mono
    intro q hq
    exact ⟨lt_of_lt_of_le ha hq.1.1, Set.mem_univ _⟩
  apply (hc.continuousAt ?_).continuousWithinAt
  rw [show p = (p.1, p.2) from rfl, nhds_prod_eq]
  exact Filter.Eventually.prod_mk (Icc_mem_nhds (by dsimp [a]; linarith [hpp]) (by dsimp [b]; linarith)) (Metric.closedBall_mem_nhds _ (by norm_num : (0 : ℝ) < 1))

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

/- Source module: DedekindZetaZeroFree.Theta.Profiles.AngularAverageRegularityAndDecay -/

section

noncomputable section

open Classical MeasureTheory NumberField
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

def angularBox : Set (Angular K) :=
  Set.univ.pi (fun _ ↦ Set.Icc (0 : ℝ) 1)

private theorem compact_angularBox : IsCompact (angularBox K) :=
  isCompact_univ_pi (fun _ ↦ isCompact_Icc)

private theorem cube_subset_box : angularCube K ⊆ angularBox K := by
  intro u hu i hi
  exact ⟨(hu i hi).1, (hu i hi).2.le⟩

private theorem measurable_cube : MeasurableSet (angularCube K) :=
  MeasurableSet.univ_pi (fun _ ↦ measurableSet_Ico)

private theorem volume_cube : volume (angularCube K) = 1 := by
  simp [angularCube, Real.volume_pi_Ico]

private theorem continuous_slice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (ht : 0 < t) : Continuous (mixedRadialTheta K I t) := by
  change Continuous ((fun p : ℝ × Angular K ↦ mixedRadialTheta K I p.1 p.2) ∘
    (fun u : Angular K ↦ (t, u)))
  exact (continuousOn_mixedRadialTheta K I).comp_continuous
    (show Continuous (fun u : Angular K ↦ (t, u)) from
      continuous_const.prodMk continuous_id) (fun _ ↦ ⟨ht, Set.mem_univ _⟩)

theorem integrableOn_mixedRadialTheta
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun u ↦ mixedRadialTheta K I t u) (angularCube K) := by
  exact ((continuous_slice K I t ht).continuousOn.integrableOn_compact
    (compact_angularBox K)).mono_set (cube_subset_box K)

theorem integrableOn_mixedRadialTheta_neg
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun u ↦ mixedRadialTheta K I t (-u)) (angularCube K) := by
  exact (((continuous_slice K I t ht).comp continuous_neg).continuousOn.integrableOn_compact
    (compact_angularBox K)).mono_set (cube_subset_box K)

theorem integral_one_angularCube :
    (∫ _u in angularCube K, (1 : ℂ)) = 1 := by
  simp [setIntegral_const, volume_cube K, Measure.real]

theorem mixedAngularAverage_sub_one
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (ht : 0 < t) :
    mixedAngularAverage K I t - 1 =
      ∫ u in angularCube K, (mixedRadialTheta K I t u - 1) := by
  rw [integral_sub (integrableOn_mixedRadialTheta K I t ht)
    (integrableOn_const (by simp [volume_cube K])), integral_one_angularCube]
  rfl

theorem mixedNegAngularAverage_sub_one
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (ht : 0 < t) :
    mixedNegAngularAverage K I t - 1 =
      ∫ u in angularCube K, (mixedRadialTheta K I t (-u) - 1) := by
  rw [integral_sub (integrableOn_mixedRadialTheta_neg K I t ht)
    (integrableOn_const (by simp [volume_cube K])), integral_one_angularCube]
  rfl

theorem continuousOn_average
    (f : ℝ × Angular K → ℂ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun t ↦ ∫ u in angularCube K, f (t, u)) (Set.Ioi (0 : ℝ)) := by
  intro t ht
  change 0 < t at ht
  have hslice : ∀ x : ℝ, 0 < x → Continuous (fun u : Angular K ↦ f (x, u)) := by
    intro x hx
    change Continuous (f ∘ (fun u : Angular K ↦ (x, u)))
    exact hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ ↦ ⟨hx, Set.mem_univ _⟩)
  have hcp := (isCompact_Icc : IsCompact (Set.Icc (t / 2) (t + 1))).prod
    (compact_angularBox K)
  have hsub : Set.Icc (t / 2) (t + 1) ×ˢ angularBox K ⊆ Set.Ioi (0 : ℝ) ×ˢ Set.univ := by
    intro p hp
    exact ⟨lt_of_lt_of_le (by linarith) hp.1.1, Set.mem_univ _⟩
  obtain ⟨M, hM⟩ := hcp.bddAbove_image (hf.mono hsub).norm
  have hnb : Set.Ioo (t / 2) (t + 1) ∈ nhds t := Ioo_mem_nhds (by linarith) (by linarith)
  have hc : ContinuousAt (fun x ↦ ∫ u in angularCube K, f (x, u)) t := by
    apply continuousAt_of_dominated (bound := fun _ ↦ M)
    · filter_upwards [hnb] with x hx
      exact (hslice x (by have := hx.1; linarith)).aestronglyMeasurable
    · filter_upwards [hnb] with x hx
      filter_upwards [ae_restrict_mem (measurable_cube K)] with u hu
      exact hM (Set.mem_image_of_mem _ ⟨⟨hx.1.le, hx.2.le⟩, cube_subset_box K hu⟩)
    · exact integrableOn_const (by simp [volume_cube K])
    · filter_upwards with u
      have hrad : ContinuousOn (fun x ↦ f (x, u)) (Set.Ioi (0 : ℝ)) := by
        change ContinuousOn (f ∘ (fun x : ℝ ↦ (x, u))) _
        exact hf.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun x hx ↦ ⟨hx, Set.mem_univ _⟩)
      exact hrad.continuousAt (isOpen_Ioi.mem_nhds ht)
  exact hc.continuousWithinAt

theorem locallyIntegrableOn_mixedAngularAverage
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    LocallyIntegrableOn (mixedAngularAverage K I) (Set.Ioi (0 : ℝ)) := by
  exact (continuousOn_average K _ (continuousOn_mixedRadialTheta K I)).locallyIntegrableOn
    measurableSet_Ioi

theorem locallyIntegrableOn_mixedNegAngularAverage
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    LocallyIntegrableOn (mixedNegAngularAverage K I) (Set.Ioi (0 : ℝ)) := by
  have hf : ContinuousOn (fun p : ℝ × Angular K ↦ mixedRadialTheta K I p.1 (-p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
    change ContinuousOn ((fun p : ℝ × Angular K ↦ mixedRadialTheta K I p.1 p.2) ∘
      (fun p : ℝ × Angular K ↦ (p.1, -p.2))) _
    exact (continuousOn_mixedRadialTheta K I).comp
      (continuous_fst.prodMk continuous_snd.neg).continuousOn (fun p hp ↦ ⟨hp.1, trivial⟩)
  exact (continuousOn_average K _ hf).locallyIntegrableOn measurableSet_Ioi

private theorem exp_rpow_isBigO (b p r : ℝ) (hb : 0 < b) (hp : 0 < p) :
    Asymptotics.IsBigO Filter.atTop (fun t : ℝ ↦ Real.exp (-b * t ^ p))
      (fun t : ℝ ↦ t ^ r) := by
  have h := ((isLittleO_exp_neg_mul_rpow_atTop hb (r / p)).comp_tendsto
    (tendsto_rpow_atTop hp)).isBigO
  apply h.congr' (Filter.Eventually.of_forall (fun _ ↦ rfl))
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  change (t ^ p) ^ (r / p) = t ^ r
  rw [← Real.rpow_mul ht, mul_div_cancel₀ r hp.ne']

private theorem integral_centered_isBigO
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (q : Angular K → Angular K)
    (hq : Continuous q) (r : ℝ) :
    Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ ↦ ∫ u in angularCube K, (mixedRadialTheta K I t (q u) - 1))
      (fun t : ℝ ↦ t ^ r) := by
  obtain ⟨B, b, hB, hb, htail⟩ := mixedRadialTheta_uniform_exponential_tail K I
    (q '' angularBox K) ((compact_angularBox K).image hq)
  have hbound : Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ ↦ ∫ u in angularCube K, (mixedRadialTheta K I t (q u) - 1))
      (fun t : ℝ ↦ Real.exp (-b * t ^ (2 / (Module.finrank ℚ K : ℝ)))) := by
    apply Asymptotics.IsBigO.of_bound B
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (by simp [volume_cube K])
      (fun u hu ↦ htail t ht (q u) (Set.mem_image_of_mem q (cube_subset_box K hu)))
    simpa [Measure.real, volume_cube K, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using h
  exact hbound.trans (exp_rpow_isBigO b _ r hb
    (div_pos (by norm_num) (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K)))))

theorem mixedAngularAverage_isBigO_rpow
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ ↦ mixedAngularAverage K I t - 1)
      (fun t : ℝ ↦ t ^ r) := by
  apply (integral_centered_isBigO K I id continuous_id r).congr'
    _ (Filter.Eventually.of_forall (fun _ ↦ rfl))
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (mixedAngularAverage_sub_one K I t ht).symm

theorem mixedNegAngularAverage_isBigO_rpow
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ ↦ mixedNegAngularAverage K I t - 1)
      (fun t : ℝ ↦ t ^ r) := by
  apply (integral_centered_isBigO K I (fun u ↦ -u) continuous_neg r).congr'
    _ (Filter.Eventually.of_forall (fun _ ↦ rfl))
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (mixedNegAngularAverage_sub_one K I t ht).symm

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

/- Source module: DedekindZetaZeroFree.LFunctions.Dedekind.GammaFactors -/

section

namespace DedekindZetaZeroFree.AbelianQuotient

noncomputable section

def zetaGammaFactor (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) *
    Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K *
    Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K

end

end DedekindZetaZeroFree.AbelianQuotient

end

/- Source module: DedekindZetaZeroFree.Analysis.FiniteFiberDirichletSeries -/

section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Vendored from https://github.com/LeanPool/lean-pool,
commit 68aa6ee63d20ad76bcc15f595adfc72949991f06.
Original source: LeanPool/Odlyzko/DedekindZeta/FiniteFiberSeries.lean.
Port to Lean 4.35.0-rc2: local imports and namespace renamed; module visibility syntax removed.
The full upstream Apache-2.0 license is included in LICENSE.
-/

open NumberField

namespace DedekindZetaZeroFree.Odlyzko

theorem tsum_sigma_of_summable {β E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    [ContinuousAdd E] [T3Space E]
    {γ : β → Type*} (w : (Σ b, γ b) → E)
    (hfiber : ∀ b, Summable (fun x : γ b ↦ w ⟨b, x⟩))
    (hw : Summable w) :
    (∑' x, w x) = ∑' b, ∑' x, w ⟨b, x⟩ :=
  Summable.tsum_sigma' hfiber hw

theorem hasSum_inversePower_eq_lSeries_fiberCard
    {α : Type*} (ν : α → ℕ) [∀ n, Finite {a : α // ν a = n}]
    (hν : ∀ a, ν a ≠ 0) {s : ℂ}
    (hsum : Summable (fun a ↦ ((ν a : ℂ) ^ (-s)))) :
    HasSum (fun a ↦ ((ν a : ℂ) ^ (-s)))
      (LSeries (fun n ↦ (Nat.card {a : α // ν a = n} : ℂ)) s) := by
  let e := Equiv.sigmaFiberEquiv ν
  apply e.hasSum_iff.mp
  have hsigma :
      Summable (fun x : Σ n, {a : α // ν a = n} ↦
        ((ν x.2.1 : ℂ) ^ (-s))) :=
    hsum.comp_injective e.injective
  have hfiber (n : ℕ) :
      Summable (fun a : {a : α // ν a = n} ↦
        ((ν a.1 : ℂ) ^ (-s))) :=
    Summable.of_finite
  have hfiberSum (n : ℕ) :
      (∑' a : {a : α // ν a = n}, ((ν a.1 : ℂ) ^ (-s))) =
        LSeries.term
          (fun n ↦ (Nat.card {a : α // ν a = n} : ℂ)) s n := by
    by_cases hn : n = 0
    · subst n
      have : IsEmpty {a : α // ν a = 0} :=
        ⟨fun a ↦ (hν a.1) a.2⟩
      simp
    · let : Fintype {a : α // ν a = n} := Fintype.ofFinite _
      rw [tsum_fintype, LSeries.term_of_ne_zero hn]
      simp_rw [show ∀ a : {a : α // ν a = n}, ν a.1 = n from fun a ↦ a.2]
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card,
        Finset.card_univ, Complex.cpow_neg, div_eq_mul_inv]
  have heq :
      (∑' x : Σ n, {a : α // ν a = n},
        ((ν x.2.1 : ℂ) ^ (-s))) =
        LSeries (fun n ↦ (Nat.card {a : α // ν a = n} : ℂ)) s := by
    calc
      _ = ∑' n, ∑' a : {a : α // ν a = n},
          ((ν a.1 : ℂ) ^ (-s)) :=
        tsum_sigma_of_summable
          (fun x : Σ n, {a : α // ν a = n} ↦
            ((ν x.2.1 : ℂ) ^ (-s))) hfiber hsigma
      _ = ∑' n, LSeries.term
          (fun n ↦ (Nat.card {a : α // ν a = n} : ℂ)) s n := by simp_all
      _ = LSeries (fun n ↦
          (Nat.card {a : α // ν a = n} : ℂ)) s := rfl
  exact heq ▸ hsigma.hasSum

theorem summable_inversePower_of_lSeriesSummable_fiberCard
    {α : Type*} (ν : α → ℕ) [∀ n, Finite {a : α // ν a = n}]
    (hν : ∀ a, ν a ≠ 0) {s : ℂ}
    (hsum :
      LSeriesSummable
        (fun n ↦ (Nat.card {a : α // ν a = n} : ℂ)) s) :
    Summable (fun a ↦ ((ν a : ℂ) ^ (-s))) := by
  rw [← summable_norm_iff]
  let e := Equiv.sigmaFiberEquiv ν
  apply e.summable_iff.mp
  change Summable (fun x : Σ n, {a : α // ν a = n} ↦
    ‖((ν x.2.1 : ℂ) ^ (-s))‖)
  apply (summable_sigma_of_nonneg fun _ ↦ norm_nonneg _).mpr
  constructor
  · intro n
    exact Summable.of_finite
  · have houter :
        (fun n ↦
          ∑' a : {a : α // ν a = n},
            ‖((ν a.1 : ℂ) ^ (-s))‖) =
        (fun n ↦
          ‖LSeries.term
            (fun n ↦ (Nat.card {a : α // ν a = n} : ℂ)) s n‖) := by
      funext n
      by_cases hn : n = 0
      · subst n
        have : IsEmpty {a : α // ν a = 0} :=
          ⟨fun a ↦ (hν a.1) a.2⟩
        simp
      · let : Fintype {a : α // ν a = n} := Fintype.ofFinite _
        rw [tsum_fintype, LSeries.term_of_ne_zero hn]
        simp_rw [show ∀ a : {a : α // ν a = n}, ν a.1 = n from
          fun a ↦ a.2]
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card,
          Finset.card_univ, norm_div, Complex.norm_natCast,
          Complex.cpow_neg, norm_inv, div_eq_mul_inv]
    rw [houter]
    exact hsum.norm

end DedekindZetaZeroFree.Odlyzko

end

/- Source module: DedekindZetaZeroFree.LFunctions.Dedekind.IdealNormCoefficients -/

section

/-
Copyright (c) 2026 Imperial College London. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Vendored from https://github.com/LeanPool/lean-pool,
commit 68aa6ee63d20ad76bcc15f595adfc72949991f06.
Original source: LeanPool/Odlyzko/DedekindZeta/Coefficients.lean.
Port to Lean 4.35.0-rc2: local imports and namespace renamed; module visibility syntax removed.
The full upstream Apache-2.0 license is included in LICENSE.
-/

open Ideal

open NumberField

namespace DedekindZetaZeroFree.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

noncomputable def idealNormCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // absNorm I = n}

lemma dedekindZeta_eq_LSeries_idealNormCount (s : ℂ) :
    NumberField.dedekindZeta K s = LSeries (fun n ↦ (idealNormCount K n : ℂ)) s :=
  rfl

end DedekindZetaZeroFree.Odlyzko

end

/- Source module: DedekindZetaZeroFree.LFunctions.Dedekind.DirichletSeriesConvergence -/

section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Vendored from https://github.com/LeanPool/lean-pool,
commit 68aa6ee63d20ad76bcc15f595adfc72949991f06.
Original source: LeanPool/Odlyzko/DedekindZeta/Convergence.lean.
Port to Lean 4.35.0-rc2: local imports and namespace renamed; module visibility syntax removed.
The full upstream Apache-2.0 license is included in LICENSE.
-/

noncomputable section

open Filter Ideal Set Topology

open NumberField

namespace DedekindZetaZeroFree.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem tendsto_sum_idealNormCount_div :
    Tendsto
      (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n, (idealNormCount K k : ℝ)) / n)
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
  rw [NumberField.dedekindZeta_residue_def]
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp
    tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr 1
  norm_cast
  simp only [idealNormCount]
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc n.zero_le,
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem lSeriesSummable_idealNormCount {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (idealNormCount K n : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_
    (fun n ↦ by positivity) zero_le_one hs
  exact Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (by simpa using tendsto_sum_idealNormCount_div K)

end DedekindZetaZeroFree.Odlyzko

end

end

/- Source module: DedekindZetaZeroFree.LFunctions.Dedekind.LocalFactor -/

section

/-
Copyright (c) 2026 Imperial College London. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Vendored from https://github.com/LeanPool/lean-pool,
commit 68aa6ee63d20ad76bcc15f595adfc72949991f06.
Original source: LeanPool/Odlyzko/DedekindZeta/LocalFactor.lean.
Port to Lean 4.35.0-rc2: local imports and namespace renamed; module visibility syntax removed.
The full upstream Apache-2.0 license is included in LICENSE.
-/

open NumberField

namespace DedekindZetaZeroFree.Odlyzko

noncomputable def inverseNormPower (q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-s)

lemma norm_inverseNormPower (q : ℕ) (hq : 0 < q) (s : ℂ) :
    ‖inverseNormPower q s‖ = (q : ℝ) ^ (-s.re) := by
  simp [inverseNormPower, Complex.norm_natCast_cpow_of_pos hq]

end DedekindZetaZeroFree.Odlyzko

end

/- Source module: DedekindZetaZeroFree.LFunctions.Dedekind.PrimeIdealSummability -/

section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Vendored from https://github.com/LeanPool/lean-pool,
commit 68aa6ee63d20ad76bcc15f595adfc72949991f06.
Original source: LeanPool/Odlyzko/DedekindZeta/PrimeIdealSummability.lean.
Port to Lean 4.35.0-rc2: local imports and namespace renamed; module visibility syntax removed.
The full upstream Apache-2.0 license is included in LICENSE.
-/

noncomputable section

open Ideal IsDedekindDomain

open NumberField

namespace DedekindZetaZeroFree.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem summable_ideal_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 K) ↦ (absNorm I : ℝ) ^ (-σ)) := by
  let e := Equiv.sigmaFiberEquiv (absNorm : Ideal (𝓞 K) → ℕ)
  rw [← e.summable_iff]
  apply (summable_sigma_of_nonneg (fun x ↦
    Real.rpow_nonneg (Nat.cast_nonneg (absNorm (e x))) _)).2
  constructor
  · intro n
    let : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).fintype
    exact Summable.of_finite
  · have hseries :=
      (lSeriesSummable_idealNormCount K (s := (σ : ℂ)) (by simpa using hσ)).norm
    convert hseries using 1
    ext n
    simp only [e, Equiv.sigmaFiberEquiv_apply, LSeries.norm_term_eq]
    split_ifs with hn
    · subst n
      have hzero :
          (fun y : {I : Ideal (𝓞 K) // absNorm I = 0} ↦
            (absNorm (y : Ideal (𝓞 K)) : ℝ) ^ (-σ)) = 0 := by
        funext y
        rw [y.2]
        simp [ne_of_gt (zero_lt_one.trans hσ)]
      rw [hzero]
      change (∑' _ : {I : Ideal (𝓞 K) // absNorm I = 0}, (0 : ℝ)) = 0
      simp
    · have hconst :
          (fun y : {I : Ideal (𝓞 K) // absNorm I = n} ↦
            (absNorm (y : Ideal (𝓞 K)) : ℝ) ^ (-σ)) =
            fun _ ↦ (n : ℝ) ^ (-σ) := by grind
      rw [hconst, tsum_const]
      simp only [idealNormCount, nsmul_eq_mul, norm_natCast]
      rw [Real.rpow_neg (Nat.cast_nonneg n)]
      simp [div_eq_mul_inv]

end DedekindZetaZeroFree.Odlyzko

end

end

/- Source module: DedekindZetaZeroFree.LFunctions.Dedekind.IdealNormSeries -/

section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Vendored from https://github.com/LeanPool/lean-pool,
commit 68aa6ee63d20ad76bcc15f595adfc72949991f06.
Original source: LeanPool/Odlyzko/DedekindZeta/IdealSeries.lean.
Port to Lean 4.35.0-rc2: local imports and namespace renamed; module visibility syntax removed.
The full upstream Apache-2.0 license is included in LICENSE.
-/

noncomputable section

section

open Complex Nat

open NumberField

namespace DedekindZetaZeroFree.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

noncomputable def dedekindZetaSummand (s : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (fun m ↦ (idealNormCount K m : ℂ)) s n

@[simp] lemma dedekindZetaSummand_zero (s : ℂ) :
    dedekindZetaSummand K s 0 = 0 := by
  simp [dedekindZetaSummand]

end DedekindZetaZeroFree.Odlyzko

end

section

open Ideal IsDedekindDomain

open NumberField

namespace DedekindZetaZeroFree.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

noncomputable def idealInverseNormPower (s : ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  if I = 0 then 0 else ((absNorm I : ℂ) ^ (-s))

lemma idealInverseNormPower_of_ne_zero (s : ℂ) {I : Ideal (𝓞 K)}
    (hI : I ≠ 0) :
    idealInverseNormPower K s I = ((absNorm I : ℂ) ^ (-s)) := by
  unfold idealInverseNormPower
  simp_all

theorem summable_norm_idealInverseNormPower {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 K) ↦ ‖idealInverseNormPower K s I‖) := by
  apply (summable_ideal_absNorm_rpow K hs).congr
  intro I
  by_cases hI : I = 0
  · subst I
    simp [idealInverseNormPower, ne_of_gt (zero_lt_one.trans hs)]
  · rw [idealInverseNormPower_of_ne_zero K s hI,
      show ((absNorm I : ℂ) ^ (-s)) =
        inverseNormPower (absNorm I) s by rfl,
      norm_inverseNormPower]
    exact Nat.pos_of_ne_zero (by
      simpa [Ideal.absNorm_eq_zero_iff] using hI)

theorem summable_idealInverseNormPower {s : ℂ} (hs : 1 < s.re) :
    Summable (idealInverseNormPower K s) :=
  (summable_norm_idealInverseNormPower K hs).of_norm

end DedekindZetaZeroFree.Odlyzko

end

end

end

/- Source module: DedekindZetaZeroFree.LFunctions.Dedekind.IdealClassConeSeries -/

section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Vendored from https://github.com/LeanPool/lean-pool,
commit 68aa6ee63d20ad76bcc15f595adfc72949991f06.
Original sources: LeanPool/Odlyzko/CompletedZeta/FundamentalConeSeries.lean and
LeanPool/Odlyzko/CompletedZeta/ClassRepresentatives.lean.
Modifications: local imports and namespace, removal of module visibility syntax,
restriction to ordinary ideal/cone counting and series, and porting of the upstream
proofs. The already landed ideal series/convergence are imported, not copied.
The upstream idealSetIntNorm definition is reused from VendorIdealElementDecomposition.
Full upstream Apache-2.0 license: LICENSE.
-/

noncomputable section

open Ideal IsDedekindDomain NumberField NumberField.Units Submodule
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

open mixedEmbedding fundamentalCone
open DedekindZetaZeroFree.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

abbrev idealSetIntNorm (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) : ℕ :=
  DedekindZetaZeroFree.Theta.idealSetIntNorm K J a

def principalIdealNormCount (J : (Ideal (𝓞 K))⁰) (n : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ //
    (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
      absNorm (I : Ideal (𝓞 K)) = n}

def fundamentalConeNormCount (J : (Ideal (𝓞 K))⁰) (n : ℕ) : ℕ :=
  Nat.card {a : idealSet K J //
    mixedEmbedding.norm (a : mixedSpace K) = n}

theorem idealSetIntNorm_eq_norm
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    ((idealSetIntNorm K J a : ℝ)) = mixedEmbedding.norm (a : mixedSpace K) :=
  intNorm_idealSetEquiv_apply a

noncomputable def idealSetIntNormFiberEquiv
    (J : (Ideal (𝓞 K))⁰) (n : ℕ) :
    {a : idealSet K J // idealSetIntNorm K J a = n} ≃
      {a : idealSet K J //
        mixedEmbedding.norm (a : mixedSpace K) = n} :=
  Equiv.subtypeEquivRight fun a ↦ by
    rw [← idealSetIntNorm_eq_norm K J a]
    exact_mod_cast Iff.rfl

private theorem finite_idealSetIntNorm_fiber
    (J : (Ideal (𝓞 K))⁰) (n : ℕ) :
    Finite {a : idealSet K J // idealSetIntNorm K J a = n} := by
  let : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).fintype
  let f :
      {I : (Ideal (𝓞 K))⁰ //
        (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} →
        {I : Ideal (𝓞 K) // absNorm I = n} :=
    fun I ↦ ⟨I.1.1, I.2.2.2⟩
  have hf : Function.Injective f := fun I I' h ↦ by
    grind
  let : Finite
      {I : (Ideal (𝓞 K))⁰ //
        (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} :=
    Finite.of_injective f hf
  exact Finite.of_equiv _
    ((idealSetEquivNorm K J n).symm.trans
      (idealSetIntNormFiberEquiv K J n).symm)

theorem fundamentalConeNormCount_eq_natCard_idealSetIntNorm
    (J : (Ideal (𝓞 K))⁰) (n : ℕ) :
    fundamentalConeNormCount K J n =
      Nat.card {a : idealSet K J // idealSetIntNorm K J a = n} := by
  rw [fundamentalConeNormCount]
  exact (Nat.card_congr (idealSetIntNormFiberEquiv K J n)).symm

theorem idealSetIntNorm_ne_zero
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    idealSetIntNorm K J a ≠ 0 := by
  have hpos := fundamentalCone.norm_pos_of_mem a.prop.1
  rw [← idealSetIntNorm_eq_norm K J a] at hpos
  intro h
  rw [h] at hpos
  exact absurd hpos (by norm_num)

theorem fundamentalConeNormCount_eq_torsion_mul
    (J : (Ideal (𝓞 K))⁰) (n : ℕ) :
    fundamentalConeNormCount K J n =
      principalIdealNormCount K J n * torsionOrder K := by
  rw [fundamentalConeNormCount, principalIdealNormCount, torsionOrder,
    ← Nat.card_prod]
  exact Nat.card_congr (idealSetEquivNorm K J n)

theorem principalIdealNormCount_le_idealNormCount
    (J : (Ideal (𝓞 K))⁰) (n : ℕ) :
    principalIdealNormCount K J n ≤ idealNormCount K n := by
  let : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).fintype
  rw [principalIdealNormCount, idealNormCount]
  let f :
      {I : (Ideal (𝓞 K))⁰ //
        (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} →
        {I : Ideal (𝓞 K) // absNorm I = n} :=
    fun I ↦ ⟨I.1.1, I.2.2.2⟩
  exact Nat.card_le_card_of_injective f fun I I' h ↦ by
    grind

def principalIdealZeta (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  LSeries (fun n ↦ (principalIdealNormCount K J n : ℂ)) s

def fundamentalConeZeta (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  LSeries (fun n ↦ (fundamentalConeNormCount K J n : ℂ)) s

theorem lSeriesSummable_principalIdealNormCount
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (principalIdealNormCount K J n : ℂ)) s := by
  rw [LSeriesSummable]
  refine Summable.of_norm_bounded (lSeriesSummable_idealNormCount K hs).norm ?_
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  simp only [LSeries.term_of_ne_zero hn.ne', norm_div,
    Complex.norm_natCast]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast principalIdealNormCount_le_idealNormCount K J n)
    (norm_nonneg _)

theorem lSeriesSummable_fundamentalConeNormCount
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (fundamentalConeNormCount K J n : ℂ)) s := by
  have hcoeff :
      (fun n ↦ (fundamentalConeNormCount K J n : ℂ)) =
        (torsionOrder K : ℂ) •
          (fun n ↦ (principalIdealNormCount K J n : ℂ)) := by
    funext n
    rw [fundamentalConeNormCount_eq_torsion_mul]
    simp [Pi.smul_apply, Nat.cast_mul, mul_comm]
  rw [hcoeff]
  exact (lSeriesSummable_principalIdealNormCount K J hs).smul _

theorem summable_idealSet_inverseNormPower
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun a : idealSet K J ↦
      ((idealSetIntNorm K J a : ℂ) ^ (-s))) := by
  let (n : ℕ) :
      Finite {a : idealSet K J // idealSetIntNorm K J a = n} :=
    finite_idealSetIntNorm_fiber K J n
  apply summable_inversePower_of_lSeriesSummable_fiberCard
    (idealSetIntNorm K J) (idealSetIntNorm_ne_zero K J)
  convert lSeriesSummable_fundamentalConeNormCount K J hs using 1
  funext n
  rw [fundamentalConeNormCount_eq_natCard_idealSetIntNorm]

theorem hasSum_idealSet_inverseNormPower
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun a : idealSet K J ↦
      ((idealSetIntNorm K J a : ℂ) ^ (-s)))
      (fundamentalConeZeta K J s) := by
  let (n : ℕ) :
      Finite {a : idealSet K J // idealSetIntNorm K J a = n} :=
    finite_idealSetIntNorm_fiber K J n
  have h := hasSum_inversePower_eq_lSeries_fiberCard
    (idealSetIntNorm K J) (idealSetIntNorm_ne_zero K J)
    (summable_idealSet_inverseNormPower K J hs)
  simpa only [fundamentalConeZeta,
    ← fundamentalConeNormCount_eq_natCard_idealSetIntNorm] using h

theorem fundamentalConeZeta_eq_torsion_mul_principalIdealZeta
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    fundamentalConeZeta K J s =
      (torsionOrder K : ℂ) * principalIdealZeta K J s := by
  have hcoeff :
      (fun n ↦ (fundamentalConeNormCount K J n : ℂ)) =
        (torsionOrder K : ℂ) •
          (fun n ↦ (principalIdealNormCount K J n : ℂ)) := by
    funext n
    rw [fundamentalConeNormCount_eq_torsion_mul]
    simp [Pi.smul_apply, Nat.cast_mul, mul_comm]
  rw [fundamentalConeZeta, hcoeff, LSeries_smul, principalIdealZeta]

open Classical in

def classIdealNormCount (C : ClassGroup (𝓞 K)) (n : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ //
    ClassGroup.mk0 I = C ∧ absNorm (I : Ideal (𝓞 K)) = n}

open Classical in

def partialDedekindZeta (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  LSeries (fun n ↦ (classIdealNormCount K C n : ℂ)) s

open Classical in
noncomputable def idealNormFiberEquivNonzero
    {n : ℕ} (hn : n ≠ 0) :
    {I : Ideal (𝓞 K) // absNorm I = n} ≃
      {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n} where
  toFun I :=
    ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr fun hI ↦
      hn <| I.2.symm.trans (Ideal.absNorm_eq_zero_iff.mpr hI)⟩, I.2⟩
  invFun I := ⟨I.1.1, I.2⟩
  left_inv I := by simp
  right_inv I := by
    simp

open Classical in

theorem sum_classIdealNormCount {n : ℕ} (hn : n ≠ 0) :
    ∑ C : ClassGroup (𝓞 K), classIdealNormCount K C n =
      idealNormCount K n := by
  let : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).fintype
  let : Fintype {I : (Ideal (𝓞 K))⁰ //
      absNorm (I : Ideal (𝓞 K)) = n} :=
    Fintype.ofEquiv _ (idealNormFiberEquivNonzero K hn)
  let e := fun C : ClassGroup (𝓞 K) ↦
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun I : (Ideal (𝓞 K))⁰ ↦ absNorm (I : Ideal (𝓞 K)) = n)
      (fun I ↦ ClassGroup.mk0 I = C)).trans
      (Equiv.subtypeEquivRight fun _ ↦ and_comm)
  calc
    _ = ∑ C : ClassGroup (𝓞 K),
        Nat.card {I : {I : (Ideal (𝓞 K))⁰ //
          absNorm (I : Ideal (𝓞 K)) = n} //
            ClassGroup.mk0 I.1 = C} := by
      apply Finset.sum_congr rfl
      intro C _
      exact (Nat.card_congr (e C)).symm
    _ = Nat.card
        (Σ C : ClassGroup (𝓞 K),
          {I : {I : (Ideal (𝓞 K))⁰ //
            absNorm (I : Ideal (𝓞 K)) = n} //
              ClassGroup.mk0 I.1 = C}) := Nat.card_sigma.symm
    _ = Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) = n} :=
      Nat.card_congr
        (Equiv.sigmaFiberEquiv
          (fun I : {I : (Ideal (𝓞 K))⁰ //
            absNorm (I : Ideal (𝓞 K)) = n} ↦ ClassGroup.mk0 I.1))
    _ = idealNormCount K n := by
      rw [idealNormCount]
      exact Nat.card_congr (idealNormFiberEquivNonzero K hn).symm

open Classical in

theorem classIdealNormCount_le_idealNormCount
    (C : ClassGroup (𝓞 K)) (n : ℕ) :
    classIdealNormCount K C n ≤ idealNormCount K n := by
  let : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).fintype
  rw [classIdealNormCount, idealNormCount]
  let f :
      {I : (Ideal (𝓞 K))⁰ //
        ClassGroup.mk0 I = C ∧ absNorm (I : Ideal (𝓞 K)) = n} →
        {I : Ideal (𝓞 K) // absNorm I = n} :=
    fun I ↦ ⟨I.1.1, I.2.2⟩
  exact Nat.card_le_card_of_injective f fun I I' h ↦ by
    grind

open Classical in

theorem lSeriesSummable_classIdealNormCount
    (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (classIdealNormCount K C n : ℂ)) s := by
  rw [LSeriesSummable]
  refine Summable.of_norm_bounded (lSeriesSummable_idealNormCount K hs).norm ?_
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  simp only [LSeries.term_of_ne_zero hn.ne', norm_div,
    Complex.norm_natCast]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast classIdealNormCount_le_idealNormCount K C n)
    (norm_nonneg _)

open Classical in
def classIdealNormFiberEquiv
    (C : ClassGroup (𝓞 K)) (n : ℕ) :
    {I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} //
      absNorm (I.1 : Ideal (𝓞 K)) = n} ≃
      {I : (Ideal (𝓞 K))⁰ //
        ClassGroup.mk0 I = C ∧ absNorm (I : Ideal (𝓞 K)) = n} :=
  Equiv.subtypeSubtypeEquivSubtypeInter
    (fun I : (Ideal (𝓞 K))⁰ ↦ ClassGroup.mk0 I = C)
    (fun I ↦ absNorm (I : Ideal (𝓞 K)) = n)

noncomputable instance finite_classIdealNormFiber
    (C : ClassGroup (𝓞 K)) (n : ℕ) :
    Finite
      {I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} //
        absNorm (I.1 : Ideal (𝓞 K)) = n} := by
  let : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).fintype
  let f :
      {I : (Ideal (𝓞 K))⁰ //
        ClassGroup.mk0 I = C ∧ absNorm (I : Ideal (𝓞 K)) = n} →
        {I : Ideal (𝓞 K) // absNorm I = n} :=
    fun I ↦ ⟨I.1.1, I.2.2⟩
  have hf : Function.Injective f := fun I I' h ↦ by
    grind
  let : Finite
      {I : (Ideal (𝓞 K))⁰ //
        ClassGroup.mk0 I = C ∧ absNorm (I : Ideal (𝓞 K)) = n} :=
    Finite.of_injective f hf
  exact Finite.of_equiv _
    (classIdealNormFiberEquiv K C n).symm

open Classical in
private theorem summable_inverseNormPower_inverseIdealClass
    (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} ↦
        ((absNorm (I.1 : Ideal (𝓞 K)) : ℂ) ^ (-s))) :=
  by
    let f :
        {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} →
          Ideal (𝓞 K) :=
      fun I ↦ I.1.1
    have hf : Function.Injective f := fun I I' h ↦ by
      grind
    have hsum :=
      (summable_idealInverseNormPower K hs).comp_injective hf
    apply hsum.congr
    intro I
    change idealInverseNormPower K s (f I) =
      ((absNorm (I.1 : Ideal (𝓞 K)) : ℂ) ^ (-s))
    rw [idealInverseNormPower_of_ne_zero K s]
    change (I.1 : Ideal (𝓞 K)) ≠ 0
    exact mem_nonZeroDivisors_iff_ne_zero.mp I.1.2

open Classical in

theorem hasSum_inverseIdealClass_inverseNormPower
    (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    HasSum
      (fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} ↦
        ((absNorm (I.1 : Ideal (𝓞 K)) : ℂ) ^ (-s)))
      (partialDedekindZeta K C s) := by
  let ν :
      {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} → ℕ :=
    fun I ↦ absNorm (I.1 : Ideal (𝓞 K))
  have hν (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C}) :
      ν I ≠ 0 :=
    absNorm_ne_zero_of_nonZeroDivisors I.1
  have h := hasSum_inversePower_eq_lSeries_fiberCard ν hν
    (summable_inverseNormPower_inverseIdealClass K C hs)
  have hcoeff :
      (fun n ↦
        (Nat.card
          {I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} //
            ν I = n} : ℂ)) =
        (fun n ↦ (classIdealNormCount K C n : ℂ)) := by
    funext n
    norm_cast
    exact Nat.card_congr (classIdealNormFiberEquiv K C n)
  rw [hcoeff] at h
  exact h

open Classical in

theorem sum_partialDedekindZeta {s : ℂ} (hs : 1 < s.re) :
    ∑ C : ClassGroup (𝓞 K), partialDedekindZeta K C s =
      NumberField.dedekindZeta K s := by
  simp_rw [partialDedekindZeta]
  rw [dedekindZeta_eq_LSeries_idealNormCount]
  rw [← LSeries_sum (fun C _ ↦ lSeriesSummable_classIdealNormCount K C hs)]
  apply LSeries_congr
  intro n hn
  simp only [Finset.sum_apply]
  exact_mod_cast sum_classIdealNormCount K hn

open Classical in

abbrev PrincipalIdealAbove (J : (Ideal (𝓞 K))⁰) :=
  {I : (Ideal (𝓞 K))⁰ //
    (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K))}

open Classical in

abbrev InverseIdealClass (J : (Ideal (𝓞 K))⁰) :=
  {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹}

open Classical in
noncomputable def inverseIdealClassEquivPrincipalIdealAbove
    (J : (Ideal (𝓞 K))⁰) :
    InverseIdealClass K J ≃ PrincipalIdealAbove K J := by
  let e₁ :
      InverseIdealClass K J ≃
        {I : {I : (Ideal (𝓞 K))⁰ // J ∣ I} //
          IsPrincipal (I.1 : Ideal (𝓞 K))} :=
    (Equiv.dvd J).subtypeEquiv fun I ↦ by
      rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
      simp only [Equiv.dvd_apply]
      change ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ ↔
        ClassGroup.mk0 (J * I) = 1
      rw [_root_.map_mul]
      constructor
      · simp_all
      · exact mul_eq_one_iff_eq_inv'.mp
  let e₂ :
      {I : {I : (Ideal (𝓞 K))⁰ // J ∣ I} //
          IsPrincipal (I.1 : Ideal (𝓞 K))} ≃
        {I : (Ideal (𝓞 K))⁰ // J ∣ I ∧
          IsPrincipal (I : Ideal (𝓞 K))} :=
    Equiv.subtypeSubtypeEquivSubtypeInter
      (fun I : (Ideal (𝓞 K))⁰ ↦ J ∣ I)
      (fun I ↦ IsPrincipal (I : Ideal (𝓞 K)))
  let e₃ :
      {I : (Ideal (𝓞 K))⁰ // J ∣ I ∧
          IsPrincipal (I : Ideal (𝓞 K))} ≃
        PrincipalIdealAbove K J :=
    Equiv.subtypeEquivRight fun I ↦ by
      rw [nonZeroDivisors_dvd_iff_dvd_coe]
  exact e₁.trans (e₂.trans e₃)

open Classical in
private theorem absNorm_inverseIdealClassEquivPrincipalIdealAbove
    (J : (Ideal (𝓞 K))⁰) (I : InverseIdealClass K J) :
    absNorm (inverseIdealClassEquivPrincipalIdealAbove K J I).1.1 =
      absNorm (J : Ideal (𝓞 K)) *
        absNorm I.1.1 := by
  simp [inverseIdealClassEquivPrincipalIdealAbove, Equiv.dvd_apply,
    map_mul]

open Classical in
def principalIdealAboveNormFiberEquiv
    (J : (Ideal (𝓞 K))⁰) (n : ℕ) :
    {I : PrincipalIdealAbove K J //
      absNorm I.1.1 = n} ≃
      {I : (Ideal (𝓞 K))⁰ //
        (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} := by
  refine (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun I : (Ideal (𝓞 K))⁰ ↦
      (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)))
    (fun I ↦ absNorm (I : Ideal (𝓞 K)) = n)).trans ?_
  exact Equiv.subtypeEquivRight fun _ ↦ by
    grind

noncomputable instance finite_principalIdealAboveNormFiber
    (J : (Ideal (𝓞 K))⁰) (n : ℕ) :
    Finite {I : PrincipalIdealAbove K J //
      absNorm I.1.1 = n} := by
  let : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).fintype
  let f :
      {I : (Ideal (𝓞 K))⁰ //
        (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} →
        {I : Ideal (𝓞 K) // absNorm I = n} :=
    fun I ↦ ⟨I.1.1, I.2.2.2⟩
  have hf : Function.Injective f := fun I I' h ↦ by
    grind
  let : Finite
      {I : (Ideal (𝓞 K))⁰ //
        (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} :=
    Finite.of_injective f hf
  exact Finite.of_equiv _
    (principalIdealAboveNormFiberEquiv K J n).symm

open Classical in
private theorem summable_inverseNormPower_principalIdealAbove
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun I : PrincipalIdealAbove K J ↦
        ((absNorm I.1.1 : ℂ) ^ (-s))) := by
  let f : PrincipalIdealAbove K J → Ideal (𝓞 K) := fun I ↦ I.1.1
  have hf : Function.Injective f := fun I I' h ↦ by
    grind
  have hsum := (summable_idealInverseNormPower K hs).comp_injective hf
  apply hsum.congr
  intro I
  change idealInverseNormPower K s (f I) =
    ((absNorm I.1.1 : ℂ) ^ (-s))
  rw [idealInverseNormPower_of_ne_zero K s]
  change I.1.1 ≠ 0
  exact mem_nonZeroDivisors_iff_ne_zero.mp I.1.2

open Classical in
private theorem hasSum_principalIdealAbove_inverseNormPower
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasSum
      (fun I : PrincipalIdealAbove K J ↦
        ((absNorm I.1.1 : ℂ) ^ (-s)))
      (principalIdealZeta K J s) := by
  let ν : PrincipalIdealAbove K J → ℕ :=
    fun I ↦ absNorm I.1.1
  have hν (I : PrincipalIdealAbove K J) : ν I ≠ 0 :=
    absNorm_ne_zero_of_nonZeroDivisors I.1
  have h := hasSum_inversePower_eq_lSeries_fiberCard ν hν
    (summable_inverseNormPower_principalIdealAbove K J hs)
  have hcoeff :
      (fun n ↦
        (Nat.card {I : PrincipalIdealAbove K J // ν I = n} : ℂ)) =
        (fun n ↦ (principalIdealNormCount K J n : ℂ)) := by
    funext n
    norm_cast
    exact Nat.card_congr (principalIdealAboveNormFiberEquiv K J n)
  rw [hcoeff] at h
  exact h

open Classical in

theorem principalIdealZeta_eq_inverseNormPower_mul_partialDedekindZeta
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    principalIdealZeta K J s =
      ((absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s)) *
        partialDedekindZeta K (ClassGroup.mk0 J)⁻¹ s := by
  let e := inverseIdealClassEquivPrincipalIdealAbove K J
  have hclass := hasSum_inverseIdealClass_inverseNormPower K
    (ClassGroup.mk0 J)⁻¹ hs
  have hscaled :
      HasSum
        (fun I : InverseIdealClass K J ↦
          ((absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s)) *
            ((absNorm I.1.1 : ℂ) ^ (-s)))
        (((absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s)) *
          partialDedekindZeta K (ClassGroup.mk0 J)⁻¹ s) :=
    hclass.mul_left ((absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s))
  have habove :
      HasSum
        (fun I : PrincipalIdealAbove K J ↦
          ((absNorm I.1.1 : ℂ) ^ (-s)))
        (((absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s)) *
          partialDedekindZeta K (ClassGroup.mk0 J)⁻¹ s) := by
    apply e.hasSum_iff.mp
    change HasSum
      (fun I : InverseIdealClass K J ↦
        ((absNorm (e I).1.1 : ℂ) ^ (-s)))
      (((absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s)) *
        partialDedekindZeta K (ClassGroup.mk0 J)⁻¹ s)
    have hfun :
        (fun I : InverseIdealClass K J ↦
          ((absNorm (e I).1.1 : ℂ) ^ (-s))) =
        (fun I : InverseIdealClass K J ↦
          ((absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s)) *
            ((absNorm I.1.1 : ℂ) ^ (-s))) := by
      funext I
      rw [show e I = inverseIdealClassEquivPrincipalIdealAbove K J I from rfl,
        absNorm_inverseIdealClassEquivPrincipalIdealAbove]
      rw [Nat.cast_mul]
      exact Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg _) (Nat.cast_nonneg _) (-s)
    simp_all
  exact (hasSum_principalIdealAbove_inverseNormPower K J hs).unique habove

open Classical in

def inverseClassIdealRepresentative
    (C : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  Classical.choose
    (ClassGroup.mk0_surjective (R := 𝓞 K) C⁻¹)

open Classical in

@[simp] theorem mk0_inverseClassIdealRepresentative
    (C : ClassGroup (𝓞 K)) :
    ClassGroup.mk0 (inverseClassIdealRepresentative K C) = C⁻¹ :=
  Classical.choose_spec
    (ClassGroup.mk0_surjective (R := 𝓞 K) C⁻¹)

open Classical in

theorem partialDedekindZeta_eq_normalized_fundamentalConeZeta_of_mk0
    (C : ClassGroup (𝓞 K)) (J : (Ideal (𝓞 K))⁰)
    (hJ : ClassGroup.mk0 J = C⁻¹) {s : ℂ} (hs : 1 < s.re) :
    partialDedekindZeta K C s =
      (torsionOrder K : ℂ)⁻¹ *
        (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ s *
        fundamentalConeZeta K J s := by
  have hcone :=
    fundamentalConeZeta_eq_torsion_mul_principalIdealZeta K J s
  have hprincipal :=
    principalIdealZeta_eq_inverseNormPower_mul_partialDedekindZeta K J hs
  have hclass : (ClassGroup.mk0 J)⁻¹ = C := by simp_all
  rw [hprincipal, hclass] at hcone
  have ht : (torsionOrder K : ℂ) ≠ 0 := by
    exact_mod_cast torsionOrder_ne_zero K
  have hnNat :
      absNorm (J : Ideal (𝓞 K)) ≠ 0 :=
    absNorm_ne_zero_of_nonZeroDivisors J
  have hn : (absNorm (J : Ideal (𝓞 K)) : ℂ) ≠ 0 := by simp_all
  have hpow :
      (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ s *
          (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add s (-s) hn]
    simp
  grind

open Classical in

theorem partialDedekindZeta_eq_normalized_fundamentalConeZeta
    (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    partialDedekindZeta K C s =
      (torsionOrder K : ℂ)⁻¹ *
        (absNorm
          (inverseClassIdealRepresentative K C : Ideal (𝓞 K)) : ℂ) ^ s *
        fundamentalConeZeta K (inverseClassIdealRepresentative K C) s :=
  partialDedekindZeta_eq_normalized_fundamentalConeZeta_of_mk0 K C
    (inverseClassIdealRepresentative K C)
    (mk0_inverseClassIdealRepresentative K C) hs

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

/- Source module: DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.ArchimedeanGaussianMellin -/

section

/-
The two generic square-Gaussian computations below are adapted from LeanPool's
`Odlyzko/CompletedZeta/UnitAveragedGaussian.lean`, commit
`68aa6ee63d20ad76bcc15f595adfc72949991f06`, copyright (c) 2026 The FLT Project,
released under the Apache 2.0 license. See the project's vendored license.
-/

namespace DedekindZetaZeroFree.AbelianQuotient

open MeasureTheory

private theorem integrable_square_gaussian {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (2 * s - 1) * Complex.exp (-((r * x ^ 2 : ℝ) : ℂ)))
      (Set.Ioi 0) := by
  have hbase : MellinConvergent (fun t : ℝ => Complex.exp (-(t : ℂ))) s := by
    rw [MellinConvergent]
    convert Complex.GammaIntegral_convergent hs using 1
    ext t
    simp [mul_comm]
  have hscaled : MellinConvergent
      (fun t : ℝ => Complex.exp (-((r * t : ℝ) : ℂ))) s := by
    simpa only [Complex.ofReal_mul] using
      (MellinConvergent.comp_mul_left (f :=
        fun t : ℝ => Complex.exp (-(t : ℂ))) (s := s) hr).2 hbase
  have hsquare : MellinConvergent
      (fun t : ℝ => Complex.exp (-((r * t ^ 2 : ℝ) : ℂ))) (2 * s) := by
    have h := (MellinConvergent.comp_rpow
      (f := fun t : ℝ => Complex.exp (-((r * t : ℝ) : ℂ)))
      (s := 2 * s) (a := 2) (by norm_num)).2
    simp_all
  simpa only [MellinConvergent, smul_eq_mul] using hsquare

private theorem integral_square_gaussian {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Set.Ioi 0,
      (x : ℂ) ^ (2 * s - 1) * Complex.exp (-((r * x ^ 2 : ℝ) : ℂ))) =
      (2 : ℂ)⁻¹ * (1 / r : ℂ) ^ s * Complex.Gamma s := by
  have hsq := mellin_comp_rpow
    (f := fun t : ℝ => Complex.exp (-(r * t))) (2 * s) 2
  rw [show (2 * s) / (2 : ℝ) = s by norm_num] at hsq
  have hgamma := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
  rw [mellin] at hsq
  rw [mellin] at hsq
  simp only [smul_eq_mul, Complex.real_smul] at hsq
  rw [hgamma] at hsq
  have htwo : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  simpa only [htwo, Complex.ofReal_inv, Complex.ofReal_ofNat,
    Complex.ofReal_pow, Complex.ofReal_mul, one_div, Real.rpow_two, mul_assoc] using hsq

private theorem inverse_cpow {r : ℝ} (hr : 0 < r) (s : ℂ) :
    (1 / r : ℂ) ^ s = (r : ℂ) ^ (-s) := by
  rw [one_div, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact Real.pi_ne_zero.symm), Complex.cpow_neg]

theorem integrableOn_gaussian_real_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    IntegrableOn (fun q : ℝ =>
      (q : ℂ) ^ (s - 1) * Complex.exp (-((Real.pi * a * q ^ 2 : ℝ) : ℂ)))
      (Set.Ioi 0) := by
  have hs' : 0 < (s / 2).re := by simpa using half_pos hs
  have htwo : (2 : ℂ) * (s / 2) = s := by ring
  simpa only [htwo] using integrable_square_gaussian hs' (mul_pos Real.pi_pos ha)

theorem gaussian_real_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    (∫ q : ℝ in Set.Ioi 0,
      (q : ℂ) ^ (s - 1) * Complex.exp (-((Real.pi * a * q ^ 2 : ℝ) : ℂ))) =
      (2 : ℂ)⁻¹ * (a : ℂ) ^ (-s / 2) * Complex.Gammaℝ s := by
  have hs' : 0 < (s / 2).re := by simpa using half_pos hs
  have h := integral_square_gaussian hs' (mul_pos Real.pi_pos ha)
  simp only [mul_div_cancel₀ _ (by norm_num : (2 : ℂ) ≠ 0)] at h
  rw [h, inverse_cpow (mul_pos Real.pi_pos ha), Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le ha.le, Complex.Gammaℝ]
  rw [neg_div]
  ring

theorem integrableOn_gaussian_complex_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    IntegrableOn (fun q : ℝ =>
      (q : ℂ) ^ (2 * s - 1) * Complex.exp (-((2 * Real.pi * a * q ^ 2 : ℝ) : ℂ)))
      (Set.Ioi 0) := by
  exact integrable_square_gaussian hs (mul_pos (mul_pos (by norm_num) Real.pi_pos) ha)

theorem gaussian_complex_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    (∫ q : ℝ in Set.Ioi 0,
      (q : ℂ) ^ (2 * s - 1) * Complex.exp (-((2 * Real.pi * a * q ^ 2 : ℝ) : ℂ))) =
      (4 : ℂ)⁻¹ * (a : ℂ) ^ (-s) * Complex.Gammaℂ s := by
  rw [integral_square_gaussian hs (mul_pos (mul_pos (by norm_num) Real.pi_pos) ha),
    inverse_cpow (mul_pos (mul_pos (by norm_num) Real.pi_pos) ha),
    Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) ha.le,
    Complex.Gammaℂ, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

end DedekindZetaZeroFree.AbelianQuotient

end

/- Source module: DedekindZetaZeroFree.Nonvanishing.Mellin.ArchimedeanGaussianFactors -/

section

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

open MeasureTheory

private theorem square_cpow (a : ℝ) (ha : 0 < a) (z : ℂ) :
    ((a ^ 2 : ℝ) : ℂ) ^ z = (a : ℂ) ^ (2 * z) := by
  rw [pow_two, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le ha.le,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne')]
  congr 1
  ring

theorem integrableOn_gaussian_real_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    IntegrableOn (fun q : ℝ ↦
      (q : ℂ) ^ (s - 1) *
        Complex.exp (-((Real.pi * a ^ 2 : ℝ) : ℂ) * (q : ℂ) ^ 2))
      (Set.Ioi 0) := by
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, neg_mul] using
    AbelianQuotient.integrableOn_gaussian_real_place_mellin s (a ^ 2) hs
      (sq_pos_of_pos ha)

theorem gaussian_real_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    (∫ q : ℝ in Set.Ioi 0,
      (q : ℂ) ^ (s - 1) *
        Complex.exp (-((Real.pi * a ^ 2 : ℝ) : ℂ) * (q : ℂ) ^ 2)) =
      (1 / 2 : ℂ) * (a : ℂ) ^ (-s) * Complex.Gammaℝ s := by
  have h := AbelianQuotient.gaussian_real_place_mellin s (a ^ 2) hs
    (sq_pos_of_pos ha)
  rw [square_cpow a ha, show (2 : ℂ) * (-s / 2) = -s by ring] at h
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, neg_mul, one_div] using h

theorem integrableOn_gaussian_complex_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    IntegrableOn (fun q : ℝ ↦
      (q : ℂ) ^ (2 * s - 1) *
        Complex.exp (-((2 * Real.pi * a ^ 2 : ℝ) : ℂ) * (q : ℂ) ^ 2))
      (Set.Ioi 0) := by
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, neg_mul] using
    AbelianQuotient.integrableOn_gaussian_complex_place_mellin s (a ^ 2) hs
      (sq_pos_of_pos ha)

theorem gaussian_complex_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    (∫ q : ℝ in Set.Ioi 0,
      (q : ℂ) ^ (2 * s - 1) *
        Complex.exp (-((2 * Real.pi * a ^ 2 : ℝ) : ℂ) * (q : ℂ) ^ 2)) =
      (1 / 4 : ℂ) * (a : ℂ) ^ (-2 * s) * Complex.Gammaℂ s := by
  have h := AbelianQuotient.gaussian_complex_place_mellin s (a ^ 2) hs
    (sq_pos_of_pos ha)
  rw [square_cpow a ha, show (2 : ℂ) * (-s) = -2 * s by ring] at h
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, neg_mul, one_div] using h

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

/- Source module: DedekindZetaZeroFree.Theta.Unfolding.MixedRadialJacobian -/

section

noncomputable section

open Classical NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

def mixedMellinGaussian (x : K) (s : ℂ) (q : InfinitePlace K → ℝ) : ℂ :=
  ∏ v : InfinitePlace K,
    (q v : ℂ) ^ ((v.mult : ℂ) * s - 1) *
      Complex.exp (-(Real.pi : ℂ) * (v.mult : ℂ) *
        (q v : ℂ) ^ 2 * (v x : ℂ) ^ 2)

def mixedRadialJacobian (y : realSpace K) : ℝ :=
  Real.exp ((Module.finrank ℚ K : ℝ) * y Units.dirichletUnitTheorem.w₀) *
    (∏ v : {v : InfinitePlace K // IsComplex v}, expMapBasis y v.1)⁻¹ *
      (2 : ℝ)⁻¹ ^ nrComplexPlaces K * (Module.finrank ℚ K : ℝ) * regulator K

private theorem radialJacobian_eq_prod (y : realSpace K) :
    mixedRadialJacobian K y = (∏ v, expMapBasis y v) *
      ((2 : ℝ)⁻¹ ^ nrComplexPlaces K * (Module.finrank ℚ K : ℝ) * regulator K) := by
  have hp : Real.exp ((Module.finrank ℚ K : ℝ) * y dirichletUnitTheorem.w₀) =
      (∏ v, expMapBasis y v) *
        (∏ v : {v : InfinitePlace K // IsComplex v}, expMapBasis y v.1) := by
    rw [Real.exp_nat_mul, ← prod_expMapBasis_pow,
      prod_eq_prod_mul_prod, prod_eq_prod_mul_prod (fun v ↦ expMapBasis y v)]
    simp only [mult_isReal, mult_isComplex, pow_one, Finset.prod_pow]
    ring
  unfold mixedRadialJacobian
  rw [hp]
  have hn : (∏ v : {v : InfinitePlace K // IsComplex v}, expMapBasis y v.1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ ↦ (expMapBasis_pos y v.1).ne'
  field_simp
  <;> ring

private theorem weighted_log_sum (y : realSpace K) :
    ∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (expMapBasis y v) =
      (Module.finrank ℚ K : ℝ) * y dirichletUnitTheorem.w₀ := by
  have h := congrArg Real.log (prod_expMapBasis_pow y)
  rw [Real.log_prod (fun v _ ↦ pow_ne_zero _ (expMapBasis_pos y v).ne'),
    Real.log_pow, Real.log_exp] at h
  simpa only [Real.log_pow] using h

theorem mixedRadialJacobian_mul_mixedMellinGaussian
    (y : realSpace K) (x : K) (s : ℂ) :
    (mixedRadialJacobian K y : ℂ) *
        mixedMellinGaussian K x s (expMapBasis y) =
      (((2 : ℝ)⁻¹ ^ nrComplexPlaces K *
          (Module.finrank ℚ K : ℝ) * regulator K : ℝ) : ℂ) *
        Complex.exp ((Module.finrank ℚ K : ℂ) * s *
          (y Units.dirichletUnitTheorem.w₀ : ℂ)) *
        mixedGaussian K x (expMapBasis y) := by
  have hp : (∏ v : InfinitePlace K, (expMapBasis y v : ℂ)) *
      (∏ v : InfinitePlace K, (expMapBasis y v : ℂ) ^ ((v.mult : ℂ) * s - 1)) =
      Complex.exp ((Module.finrank ℚ K : ℂ) * s *
        (y dirichletUnitTheorem.w₀ : ℂ)) := by
    rw [← Finset.prod_mul_distrib]
    have he : ∀ v : InfinitePlace K,
        (expMapBasis y v : ℂ) * (expMapBasis y v : ℂ) ^ ((v.mult : ℂ) * s - 1) =
        Complex.exp (((v.mult : ℂ) * (Real.log (expMapBasis y v) : ℂ)) * s) := by
      intro v
      have hn : (expMapBasis y v : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (expMapBasis_pos y v).ne'
      rw [Complex.cpow_sub _ _ hn, Complex.cpow_one, mul_div_cancel₀ _ hn,
        Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log (expMapBasis_pos y v).le]
      congr 1
      ring
    simp_rw [he]
    rw [← Complex.exp_sum]
    rw [← Finset.sum_mul]
    have hs : (∑ v : InfinitePlace K,
        (v.mult : ℂ) * (Real.log (expMapBasis y v) : ℂ)) =
        (Module.finrank ℚ K : ℂ) * (y dirichletUnitTheorem.w₀ : ℂ) := by
      exact_mod_cast weighted_log_sum K y
    rw [hs]
    congr 1
    ring
  have hg : (∏ v : InfinitePlace K,
      Complex.exp (-(Real.pi : ℂ) * (v.mult : ℂ) *
        (expMapBasis y v : ℂ) ^ 2 * (v x : ℂ) ^ 2)) =
      mixedGaussian K x (expMapBasis y) := by
    rw [← Complex.exp_sum]
    unfold mixedGaussian
    congr 1
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_natCast]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [radialJacobian_eq_prod, mixedMellinGaussian, Finset.prod_mul_distrib]
  push_cast
  rw [← mul_assoc, mul_right_comm (∏ v : InfinitePlace K, (expMapBasis y v : ℂ)),
    mul_assoc, hp, hg]
  ring

theorem norm_mixedMellinGaussian
    (x : K) (s : ℂ) (q : InfinitePlace K → ℝ) (hq : ∀ v, 0 < q v) :
    ‖mixedMellinGaussian K x s q‖ =
      ∏ v : InfinitePlace K,
        (q v) ^ ((v.mult : ℝ) * s.re - 1) *
          Real.exp (-Real.pi * (v.mult : ℝ) * (q v) ^ 2 * (v x) ^ 2) := by
  unfold mixedMellinGaussian
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro v hv
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hq v), Complex.norm_exp]
  congr 2 <;> simp [Complex.mul_re, ← Complex.ofReal_pow]

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

/- Source module: DedekindZetaZeroFree.Nonvanishing.Mellin.MixedGaussianProduct -/

section

noncomputable section

open Classical NumberField NumberField.InfinitePlace MeasureTheory

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

private theorem positive_prod_cpow {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ t, 0 ≤ a i) (s : ℂ) :
    (∏ i ∈ t, (a i : ℂ) ^ s) = ((∏ i ∈ t, a i : ℝ) : ℂ) ^ s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (ha i (Finset.mem_insert_self _ _))
        (Finset.prod_nonneg (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))]

private theorem place_integral (x : K) (hx : x ≠ 0) (s : ℂ) (hs : 0 < s.re)
    (v : InfinitePlace K) :
    (∫ q : ℝ in Set.Ioi 0,
      (q : ℂ) ^ ((v.mult : ℂ) * s - 1) *
        Complex.exp (-(Real.pi : ℂ) * (v.mult : ℂ) * (q : ℂ) ^ 2 * (v x : ℂ) ^ 2)) =
      (if IsReal v then (1 / 2 : ℂ) * Complex.Gammaℝ s
        else (1 / 4 : ℂ) * Complex.Gammaℂ s) *
      ((v x ^ v.mult : ℝ) : ℂ) ^ (-s) := by
  classical
  have ha : 0 < v x := pos_iff.mpr hx
  have hp : ((v x ^ v.mult : ℝ) : ℂ) ^ (-s) =
      (v x : ℂ) ^ ((v.mult : ℂ) * (-s)) := by
    rw [← Real.rpow_natCast, ← Complex.cpow_mul_ofReal_nonneg ha.le]
    simp
  rw [hp]
  rcases isReal_or_isComplex v with hv | hv
  · rw [if_pos hv, hv.mult_eq_one]
    simp only [Nat.cast_one, one_mul]
    convert gaussian_real_place_mellin s (v x) hs ha using 1
    · push_cast
      congr! 2
      ring_nf
    · ring
  · rw [if_neg (not_isReal_iff_isComplex.mpr hv), hv.mult_eq_two]
    simp only [Nat.cast_ofNat]
    convert gaussian_complex_place_mellin s (v x) hs ha using 1
    · push_cast
      congr! 2
      ring_nf
    · ring

theorem integrable_mixedMellinGaussian (x : K) (hx : x ≠ 0)
    (s : ℂ) (hs : 0 < s.re) :
    Integrable (mixedMellinGaussian K x s)
      (Measure.pi (fun _v : InfinitePlace K ↦
        (volume : Measure ℝ).restrict (Set.Ioi 0))) := by
  classical
  unfold mixedMellinGaussian
  apply Integrable.fintype_prod (f := fun (v : InfinitePlace K) (q : ℝ) ↦
    (q : ℂ) ^ ((v.mult : ℂ) * s - 1) *
      Complex.exp (-(Real.pi : ℂ) * (v.mult : ℂ) * (q : ℂ) ^ 2 * (v x : ℂ) ^ 2))
  intro v
  have ha : 0 < v x := pos_iff.mpr hx
  rcases isReal_or_isComplex v with hv | hv
  · convert integrableOn_gaussian_real_place_mellin s (v x) hs ha using 1
    simp only [hv.mult_eq_one, Nat.cast_one, one_mul, Complex.ofReal_mul,
      Complex.ofReal_pow, IntegrableOn]
    congr! 2
    push_cast
    ring_nf
  · convert integrableOn_gaussian_complex_place_mellin s (v x) hs ha using 1
    simp only [hv.mult_eq_two, Nat.cast_ofNat, Complex.ofReal_mul,
      Complex.ofReal_pow, IntegrableOn]
    congr! 2
    push_cast
    ring_nf

theorem integral_mixedMellinGaussian (x : K) (hx : x ≠ 0)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ q : InfinitePlace K → ℝ, mixedMellinGaussian K x s q
      ∂Measure.pi (fun _v : InfinitePlace K ↦
        (volume : Measure ℝ).restrict (Set.Ioi 0))) =
      (1 / 2 : ℂ) ^ nrRealPlaces K *
        (1 / 4 : ℂ) ^ nrComplexPlaces K *
        Complex.Gammaℝ s ^ nrRealPlaces K *
        Complex.Gammaℂ s ^ nrComplexPlaces K *
        ((|Algebra.norm ℚ x| : ℚ) : ℂ) ^ (-s) := by
  classical
  unfold mixedMellinGaussian
  rw [integral_fintype_prod_eq_prod (fun (v : InfinitePlace K) (q : ℝ) ↦
    (q : ℂ) ^ ((v.mult : ℂ) * s - 1) *
      Complex.exp (-(Real.pi : ℂ) * (v.mult : ℂ) * (q : ℂ) ^ 2 * (v x : ℂ) ^ 2))]
  simp_rw [place_integral K x hx s hs]
  rw [Finset.prod_mul_distrib, positive_prod_cpow]
  · rw [prod_eq_abs_norm]
    have hc : (∏ v : InfinitePlace K,
        if IsReal v then (1 / 2 : ℂ) * Complex.Gammaℝ s
          else (1 / 4 : ℂ) * Complex.Gammaℂ s) =
        ((1 / 2 : ℂ) * Complex.Gammaℝ s) ^ nrRealPlaces K *
          ((1 / 4 : ℂ) * Complex.Gammaℂ s) ^ nrComplexPlaces K := by
      rw [prod_eq_prod_mul_prod]
      have hr (v : {v : InfinitePlace K // IsReal v}) : IsReal v.val := v.property
      have hi (v : {v : InfinitePlace K // IsComplex v}) : ¬IsReal v.val :=
        not_isReal_iff_isComplex.mpr v.property
      simp only [hr, hi, if_true, if_false, Finset.prod_const, Finset.card_univ,
        nrRealPlaces, nrComplexPlaces]
    rw [hc, Rat.cast_abs]
    norm_cast
    ring
  · intro v hv
    exact pow_nonneg (AbsoluteValue.nonneg _ _) _

theorem norm_mixedMellinGaussian_eq_realPart (x : K) (s : ℂ)
    (q : InfinitePlace K → ℝ) (hq : ∀ v, 0 < q v) :
    ‖mixedMellinGaussian K x s q‖ =
      ‖mixedMellinGaussian K x (s.re : ℂ) q‖ := by
  rw [norm_mixedMellinGaussian K x s q hq,
    norm_mixedMellinGaussian K x (s.re : ℂ) q hq]
  simp

private theorem kernel_real_norm (x : K) (σ : ℝ) (q : InfinitePlace K → ℝ)
    (hq : ∀ v, 0 < q v) :
    mixedMellinGaussian K x (σ : ℂ) q =
      (‖mixedMellinGaussian K x (σ : ℂ) q‖ : ℂ) := by
  rw [norm_mixedMellinGaussian K x (σ : ℂ) q hq]
  unfold mixedMellinGaussian
  simp only [Complex.ofReal_re, Complex.ofReal_prod, Complex.ofReal_mul,
    Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow,
    Complex.ofReal_natCast, Complex.ofReal_sub, Complex.ofReal_one]
  apply Finset.prod_congr rfl
  intro v hv
  rw [Complex.ofReal_cpow (hq v).le]
  push_cast
  ring_nf

private theorem positive_coordinates_ae :
    ∀ᵐ q : InfinitePlace K → ℝ ∂Measure.pi (fun _v : InfinitePlace K ↦
      (volume : Measure ℝ).restrict (Set.Ioi 0)), ∀ v, 0 < q v := by
  apply Filter.eventually_all.mpr
  intro v
  exact (MeasureTheory.Measure.tendsto_eval_ae_ae (i := v)).eventually
    (ae_restrict_mem measurableSet_Ioi)

theorem integral_norm_mixedMellinGaussian (x : K) (hx : x ≠ 0)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ q : InfinitePlace K → ℝ, ‖mixedMellinGaussian K x s q‖
      ∂Measure.pi (fun _v : InfinitePlace K ↦
        (volume : Measure ℝ).restrict (Set.Ioi 0))) =
      (1 / 2 : ℝ) ^ nrRealPlaces K *
        (1 / 4 : ℝ) ^ nrComplexPlaces K *
        ‖Complex.Gammaℝ (s.re : ℂ)‖ ^ nrRealPlaces K *
        ‖Complex.Gammaℂ (s.re : ℂ)‖ ^ nrComplexPlaces K *
        ((|Algebra.norm ℚ x| : ℚ) : ℝ) ^ (-s.re) := by
  let μ := Measure.pi (fun _v : InfinitePlace K ↦
    (volume : Measure ℝ).restrict (Set.Ioi 0))
  have heq : (∫ q, ‖mixedMellinGaussian K x s q‖ ∂μ) =
      ∫ q, ‖mixedMellinGaussian K x (s.re : ℂ) q‖ ∂μ := by
    apply integral_congr_ae
    exact (positive_coordinates_ae K).mono fun q hq ↦
      norm_mixedMellinGaussian_eq_realPart K x s q hq
  have hi : (∫ q, mixedMellinGaussian K x (s.re : ℂ) q ∂μ) =
      (((∫ q, ‖mixedMellinGaussian K x (s.re : ℂ) q‖ ∂μ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact (positive_coordinates_ae K).mono fun q hq ↦ kernel_real_norm K x s.re q hq
  have hn : ‖∫ q, mixedMellinGaussian K x (s.re : ℂ) q ∂μ‖ =
      ∫ q, ‖mixedMellinGaussian K x (s.re : ℂ) q‖ ∂μ := by
    rw [hi, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun q ↦ norm_nonneg _)]
  change (∫ q, ‖mixedMellinGaussian K x s q‖ ∂μ) = _
  rw [heq, ← hn]
  change ‖∫ q, mixedMellinGaussian K x (s.re : ℂ) q
    ∂Measure.pi (fun _v : InfinitePlace K ↦
      (volume : Measure ℝ).restrict (Set.Ioi 0))‖ = _
  rw [integral_mixedMellinGaussian K x hx (s.re : ℂ) (by simpa using hs)]
  simp only [norm_mul, norm_pow]
  have hnorm : 0 < ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
    have hprod : 0 < ∏ v : InfinitePlace K, v x ^ v.mult :=
      Finset.prod_pos fun v hv ↦ pow_pos (pos_iff.mpr hx) _
    rwa [prod_eq_abs_norm] at hprod
  rw [show (-(s.re : ℂ)) = ((-s.re : ℝ) : ℂ) by simp,
    ← Complex.ofReal_ratCast, Complex.norm_cpow_eq_rpow_re_of_pos hnorm]
  norm_num

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

/- Source module: DedekindZetaZeroFree.Theta.Unfolding.MixedConeMellinSummability -/

section

noncomputable section

open NumberField NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open DedekindZetaZeroFree.Theta
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

theorem summable_integral_norm_mixedMellinGaussian_idealSet
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun a : idealSet K J ↦
      ∫ q : InfinitePlace K → ℝ,
        ‖mixedMellinGaussian K (idealSetElement K J a) s q‖
        ∂Measure.pi (fun _v : InfinitePlace K ↦
          (volume : Measure ℝ).restrict (Set.Ioi 0))) := by
  have hbase := (summable_idealSet_inverseNormPower K J (s := (s.re : ℂ)) hs).norm
  refine (hbase.mul_left ((1 / 2 : ℝ) ^ nrRealPlaces K *
    (1 / 4 : ℝ) ^ nrComplexPlaces K *
    ‖Complex.Gammaℝ (s.re : ℂ)‖ ^ nrRealPlaces K *
    ‖Complex.Gammaℂ (s.re : ℂ)‖ ^ nrComplexPlaces K)).congr fun a ↦ ?_
  rw [integral_norm_mixedMellinGaussian K (idealSetElement K J a) (idealSetElement_ne_zero K J a) s
    (lt_trans zero_lt_one hs)]
  rw [absNorm_idealSetElement K J a]
  rw [← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (idealSetIntNorm_ne_zero K J a)))]
  simp

theorem hasSum_integral_mixedMellinGaussian_idealSet
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun a : idealSet K J ↦
      ∫ q : InfinitePlace K → ℝ,
        mixedMellinGaussian K (idealSetElement K J a) s q
        ∂Measure.pi (fun _v : InfinitePlace K ↦
          (volume : Measure ℝ).restrict (Set.Ioi 0)))
      (((1 / 2 : ℂ) ^ nrRealPlaces K *
          (1 / 4 : ℂ) ^ nrComplexPlaces K *
          Complex.Gammaℝ s ^ nrRealPlaces K *
          Complex.Gammaℂ s ^ nrComplexPlaces K) *
        fundamentalConeZeta K J s) := by
  have h := (hasSum_idealSet_inverseNormPower K J hs).mul_left
    ((1 / 2 : ℂ) ^ nrRealPlaces K *
      (1 / 4 : ℂ) ^ nrComplexPlaces K *
      Complex.Gammaℝ s ^ nrRealPlaces K *
      Complex.Gammaℂ s ^ nrComplexPlaces K)
  refine h.congr_fun fun a ↦ ?_
  rw [integral_mixedMellinGaussian K (idealSetElement K J a) (idealSetElement_ne_zero K J a) s
    (lt_trans zero_lt_one hs)]
  congr 2
  exact_mod_cast absNorm_idealSetElement K J a

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

/- Source module: DedekindZetaZeroFree.Theta.Unfolding.MixedConeMellin -/

section

noncomputable section

open NumberField NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open DedekindZetaZeroFree.Theta
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

/-
The change-of-variables and unit-slab helpers below adapt proof code from
LeanPool/lean-pool, commit 68aa6ee63d20ad76bcc15f595adfc72949991f06,
`CompletedZeta/ConeGaussianRadial.lean` and `IdealThetaUnfolding.lean`.
Copyright (c) 2026 The FLT Project. Released under Apache 2.0;
see `DedekindZetaZeroFree/LICENSE`.
-/

def mixedConeRadialKernel (x : K) (s : ℂ) (y : realSpace K) : ℂ :=
  (mixedRadialJacobian K y : ℂ) * mixedMellinGaussian K x s (expMapBasis y)

private theorem mixedCone_expMapBasis_image_univ :
    expMapBasis '' (Set.univ : Set (realSpace K)) =
      Set.univ.pi (fun _ : InfinitePlace K ↦ Set.Ioi (0 : ℝ)) := by
  ext q
  constructor
  · rintro ⟨x, -, rfl⟩
    exact Set.mem_univ_pi.mpr fun w ↦ expMapBasis_pos x w
  · intro hq
    have htarget : q ∈ expMapBasis.target := hq
    exact ⟨expMapBasis.symm q, Set.mem_univ _, expMapBasis.right_inv htarget⟩

private theorem mixedCone_pi_restrict :
    Measure.pi (fun _ : InfinitePlace K ↦ (volume : Measure ℝ).restrict (Set.Ioi 0)) =
      (volume : Measure (realSpace K)).restrict
        (Set.univ.pi (fun _ : InfinitePlace K ↦ Set.Ioi (0 : ℝ))) := by
  rw [← Measure.restrict_pi_pi, ← MeasureTheory.volume_pi]

theorem integral_mixedConeRadialKernel (x : K) (s : ℂ) :
    (∫ y : realSpace K, mixedConeRadialKernel K x s y) =
      ∫ q : realSpace K, mixedMellinGaussian K x s q
        ∂Measure.pi (fun _ : InfinitePlace K ↦
          (volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  rw [mixedCone_pi_restrict, ← mixedCone_expMapBasis_image_univ]
  symm
  convert setIntegral_expMapBasis_image (K := K) MeasurableSet.univ
    (mixedMellinGaussian K x s) using 1
  simp only [MeasureTheory.setIntegral_univ, mixedConeRadialKernel,
    mixedRadialJacobian, smul_eq_mul, Complex.real_smul,
    mul_comm (b := (Module.finrank ℚ K : ℝ))]

theorem integrable_mixedConeRadialKernel {x : K} (hx : x ≠ 0)
    {s : ℂ} (hs : 0 < s.re) : Integrable (mixedConeRadialKernel K x s) := by
  have h := integrable_mixedMellinGaussian K x hx s hs
  rw [mixedCone_pi_restrict, ← mixedCone_expMapBasis_image_univ] at h
  have h' := (integrableOn_expMapBasis_image_iff (K := K) MeasurableSet.univ
    (mixedMellinGaussian K x s)).mp h
  change Integrable (fun y ↦ (mixedRadialJacobian K y : ℂ) *
    mixedMellinGaussian K x s (expMapBasis y))
  simpa only [integrableOn_univ, mixedConeRadialKernel, mixedRadialJacobian,
    smul_eq_mul, Complex.real_smul, mul_comm (b := (Module.finrank ℚ K : ℝ))] using h'

theorem integral_norm_mixedConeRadialKernel (x : K) (s : ℂ) :
    (∫ y : realSpace K, ‖mixedConeRadialKernel K x s y‖) =
      ∫ q : realSpace K, ‖mixedMellinGaussian K x s q‖
        ∂Measure.pi (fun _ : InfinitePlace K ↦
          (volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  classical
  rw [mixedCone_pi_restrict, ← mixedCone_expMapBasis_image_univ]
  symm
  convert setIntegral_expMapBasis_image (K := K) MeasurableSet.univ
    (fun q ↦ ‖mixedMellinGaussian K x s q‖) using 1
  simp only [setIntegral_univ]
  apply integral_congr_ae
  filter_upwards with y
  have hprod : 0 < ∏ v : {v : InfinitePlace K // IsComplex v}, expMapBasis y v.1 :=
    Finset.prod_pos fun _ _ ↦ expMapBasis_pos _ _
  have hreg := Units.regulator_pos K
  have hpos : 0 ≤ mixedRadialJacobian K y := by
    unfold mixedRadialJacobian
    positivity
  rw [mixedConeRadialKernel, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hpos]
  simp only [smul_eq_mul, mixedRadialJacobian,
    mul_comm (b := (Module.finrank ℚ K : ℝ))]

theorem mixedConeRadialKernel_add_unitCoordinateShift
    (x : K) (s : ℂ) (y : realSpace K) (z : unitShiftIndex K) :
    mixedConeRadialKernel K x s (y + unitCoordinateShift z) =
      mixedConeRadialKernel K
        (((fundamentalUnitForShift z : (𝓞 K)ˣ) : K) * x) s y := by
  simp only [mixedConeRadialKernel, mixedRadialJacobian_mul_mixedMellinGaussian]
  have hrad : (y + unitCoordinateShift z) Units.dirichletUnitTheorem.w₀ =
      y Units.dirichletUnitTheorem.w₀ := by
    simp [unitCoordinateShift]
  rw [hrad, expMapBasis_add_unitCoordinateShift, mixedGaussian_mul_unit]
  rfl

theorem hasSum_integral_norm_mixedConeRadialKernel_unitSlab
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J)
    {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun z : unitShiftIndex K ↦
      ∫ y in unitFundamentalParamSet K,
        ‖mixedConeRadialKernel K
          (((fundamentalUnitForShift z : (𝓞 K)ˣ) : K) * idealSetElement K J a) s y‖)
      (∫ y : realSpace K, ‖mixedConeRadialKernel K (idealSetElement K J a) s y‖) := by
  classical
  let f : realSpace K → ℝ := fun y ↦
    ‖mixedConeRadialKernel K (idealSetElement K J a) s y‖
  have hf : Integrable f :=
    (integrable_mixedConeRadialKernel K (idealSetElement_ne_zero K J a) hs).norm
  have hp := hasSum_integral_iUnion (f := f)
    (fun z : unitShiftIndex K ↦ measurableSet_unitFundamentalTranslate z)
    pairwise_disjoint_unitFundamentalTranslate (by
      rw [iUnion_unitFundamentalTranslate]
      simpa only [integrableOn_univ] using hf)
  have hp' : HasSum (fun z : unitShiftIndex K ↦
      ∫ y in unitFundamentalTranslate z, f y) (∫ y, f y) := by
    simpa only [iUnion_unitFundamentalTranslate, setIntegral_univ] using hp
  refine hp'.congr_fun fun z ↦ ?_
  rw [setIntegral_unitFundamentalTranslate f z]
  apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
  intro y _
  exact congrArg norm (mixedConeRadialKernel_add_unitCoordinateShift K
    (idealSetElement K J a) s y z).symm

theorem summable_prod_integral_norm_mixedConeRadialKernel_unitSlab
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : idealSet K J × unitShiftIndex K ↦
      ∫ y in unitFundamentalParamSet K,
        ‖mixedConeRadialKernel K
          (((fundamentalUnitForShift p.2 : (𝓞 K)ˣ) : K) * idealSetElement K J p.1) s y‖) := by
  classical
  apply (summable_prod_of_nonneg fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _).mpr
  constructor
  · intro a
    exact (hasSum_integral_norm_mixedConeRadialKernel_unitSlab K J a
      (lt_trans zero_lt_one hs)).summable
  · refine (summable_integral_norm_mixedMellinGaussian_idealSet K J hs).congr fun a ↦ ?_
    rw [(hasSum_integral_norm_mixedConeRadialKernel_unitSlab K J a
      (lt_trans zero_lt_one hs)).tsum_eq, integral_norm_mixedConeRadialKernel]

theorem integral_mixedConeRadialKernel_eq_tsum_unitSlab
    {x : K} (hx : x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    (∫ y : realSpace K, mixedConeRadialKernel K x s y) =
      ∑' z : unitShiftIndex K, ∫ y in unitFundamentalParamSet K,
        mixedConeRadialKernel K (((fundamentalUnitForShift z : (𝓞 K)ˣ) : K) * x) s y := by
  rw [integral_eq_tsum_setIntegral_add_unitCoordinateShift _
    (integrable_mixedConeRadialKernel K hx hs)]
  apply tsum_congr
  intro z
  apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
  intro y _
  exact mixedConeRadialKernel_add_unitCoordinateShift K x s y z

open Classical in
noncomputable def coneIdealElementShapeMap
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥(J : Ideal (𝓞 K))) :
    shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq :=
  ⟨traceRadialScale K q hq
      (traceEmbedding K (((x : 𝓞 K) : K))),
      (traceRadialScale_traceEmbedding_mem_shapeIdealLattice
        K (FractionalIdeal.mk0 K J) q hq _).2 (by
          rw [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal]
          exact ⟨x, x.prop, rfl⟩)⟩

theorem coneIdealElementShapeMap_bijective
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    Function.Bijective (coneIdealElementShapeMap K J q hq) := by
  constructor
  · intro x y hxy
    have htrace :
        traceEmbedding K (((x : 𝓞 K) : K)) =
          traceEmbedding K (((y : 𝓞 K) : K)) :=
      (traceRadialScale K q hq).injective (congrArg Subtype.val hxy)
    apply Subtype.ext
    apply RingOfIntegers.coe_injective
    apply mixedEmbedding_injective K
    simpa [traceEmbedding] using congrArg (traceToMixed K) htrace
  · intro v
    have hv :
        (traceRadialScale K q hq).symm (v : mixedEmbedding.euclidean.mixedSpace K) ∈
          traceIdealLattice K (FractionalIdeal.mk0 K J) :=
      v.prop
    obtain ⟨x, hx, hxv⟩ :=
      exists_traceEmbedding_eq_of_mem_traceIdealLattice
        K (FractionalIdeal.mk0 K J) hv
    rw [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change traceRadialScale K q hq (traceEmbedding K ((y : 𝓞 K) : K)) = v
    simp_all

noncomputable def coneIdealElementShapeEquiv
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ↥(J : Ideal (𝓞 K)) ≃
      shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq :=
  Equiv.ofBijective (coneIdealElementShapeMap K J q hq)
    (coneIdealElementShapeMap_bijective K J q hq)

@[simp]
theorem coneIdealElementShapeEquiv_coe
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥(J : Ideal (𝓞 K))) :
    ((coneIdealElementShapeEquiv K J q hq x :
        shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq) :
      mixedEmbedding.euclidean.mixedSpace K) =
      traceRadialScale K q hq
        (traceEmbedding K (((x : 𝓞 K) : K))) :=
  by rfl

open Classical in
def coneNonzeroEquivSingletonCompl
    (J : (Ideal (𝓞 K))⁰) :
    nonzeroIdealElement K J ≃
      {x : ↥(J : Ideal (𝓞 K)) // x ∉ ({0} : Finset ↥(J : Ideal (𝓞 K)))} where
  toFun x :=
    ⟨⟨x.1, x.2.1⟩, by
      simp only [Finset.mem_singleton]
      intro hx
      exact x.2.2 (congrArg Subtype.val hx)⟩
  invFun x :=
    ⟨x.1.1, x.1.2, by
      intro hx
      apply x.2
      simp_all⟩
  left_inv x := by
    simp
  right_inv x := by
    apply Subtype.ext
    simp

private theorem coneTheta_eq_one_add_nonzero
    (J : (Ideal (𝓞 K))⁰) (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    fractionalShapeIdealTheta K (FractionalIdeal.mk0 K J) q hq =
      1 + ∑' x : nonzeroIdealElement K J, mixedGaussian K (((x : 𝓞 K) : K)) q := by
  classical
  let f : ↥(J : Ideal (𝓞 K)) → ℂ := fun x ↦ mixedGaussian K (((x : 𝓞 K) : K)) q
  have hsL := summable_latticeTheta
    (shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq) Real.pi_pos
  have hs : Summable f := by
    have h := (Equiv.summable_iff (coneIdealElementShapeEquiv K J q hq)).mpr hsL
    exact h.congr fun x ↦ by
      dsimp only [Function.comp_apply, f]
      rw [coneIdealElementShapeEquiv_coe, ← mixedGaussian_eq_latticeGaussian]
  have heq : fractionalShapeIdealTheta K (FractionalIdeal.mk0 K J) q hq = ∑' x, f x := by
    rw [fractionalShapeIdealTheta, latticeTheta,
      ← (coneIdealElementShapeEquiv K J q hq).tsum_eq]
    apply tsum_congr
    intro x
    rw [coneIdealElementShapeEquiv_coe, ← mixedGaussian_eq_latticeGaussian]
  rw [heq, ← hs.sum_add_tsum_subtype_compl ({0} : Finset ↥(J : Ideal (𝓞 K)))]
  simp only [Finset.sum_singleton]
  have hz : f 0 = 1 := by simp [f, mixedGaussian]
  rw [hz, ← (coneNonzeroEquivSingletonCompl K J).tsum_eq]
  rfl

private theorem coneRadialConstant_ne_zero :
    ((((2 : ℝ)⁻¹ ^ nrComplexPlaces K * (Module.finrank ℚ K : ℝ) *
      Units.regulator K) : ℝ) : ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  have hn : 0 < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  exact (mul_pos (mul_pos (by positivity) hn) (Units.regulator_pos K)).ne'

private theorem cone_tsum_radialKernel
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) (y : realSpace K) :
    (∑' x : nonzeroIdealElement K J, mixedConeRadialKernel K (((x : 𝓞 K) : K)) s y) =
      (((2 : ℝ)⁻¹ ^ nrComplexPlaces K * (Module.finrank ℚ K : ℝ) *
        Units.regulator K : ℝ) : ℂ) *
      (Complex.exp ((Module.finrank ℚ K : ℂ) * s *
        (y Units.dirichletUnitTheorem.w₀ : ℂ)) *
      (fractionalShapeIdealTheta K (FractionalIdeal.mk0 K J) (expMapBasis y)
        (fun w ↦ ne_of_gt (expMapBasis_pos _ w)) - 1)) := by
  rw [coneTheta_eq_one_add_nonzero]
  simp only [add_sub_cancel_left]
  rw [← mul_assoc, ← tsum_mul_left]
  apply tsum_congr
  intro x
  exact mixedRadialJacobian_mul_mixedMellinGaussian K y (((x : 𝓞 K) : K)) s

private theorem cone_summable_integral_norm
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun x : nonzeroIdealElement K J ↦ ∫ y in unitFundamentalParamSet K,
      ‖mixedConeRadialKernel K (((x : 𝓞 K) : K)) s y‖) := by
  rw [← (idealElementMulDecompositionEquiv K J).summable_iff]
  convert summable_prod_integral_norm_mixedConeRadialKernel_unitSlab K J hs using 1
  funext p
  apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
  intro y _
  rw [idealElementMulDecompositionEquiv_coe]

private theorem cone_integrable_tsum {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} [Countable ι] {F : ι → α → ℂ}
    (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    Integrable (fun a ↦ ∑' i, F i a) μ := by
  let G : ι → α →₁[μ] ℂ := fun i ↦ (hF_int i).toL1 (F i)
  have hnorm (i : ι) : ‖G i‖ = ∫ a, ‖F i a‖ ∂μ := by
    rw [show G i = (hF_int i).toL1 (F i) by rfl,
      Integrable.norm_toL1, integral_norm_eq_lintegral_enorm
        (hF_int i).aestronglyMeasurable]
    simp only [edist_zero_right]
  have hG_norm : Summable fun i ↦ ‖G i‖ := hF_sum.congr fun i ↦ (hnorm i).symm
  have hG_enorm : ∑' i, ‖G i‖ₑ ≠ ⊤ := tsum_enorm_ne_top_iff_summable_norm.mpr hG_norm
  have hcoe : (⇑(∑' i, G i) : α → ℂ) =ᵐ[μ] fun a ↦ ∑' i, F i a := by
    filter_upwards [Lp.coeFn_tsum hG_enorm,
      ae_all_iff.mpr (fun i ↦ (hF_int i).coeFn_toL1)] with a hsum hterm
    exact hsum.trans (tsum_congr fun i ↦ hterm i)
  exact (L1.integrable_coeFn (∑' i, G i)).congr hcoe

theorem integrableOn_fractionalShapeIdealTheta_logMellin
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
      (fun y : realSpace K ↦
        Complex.exp ((Module.finrank ℚ K : ℂ) * s *
          (y Units.dirichletUnitTheorem.w₀ : ℂ)) *
          (fractionalShapeIdealTheta K (FractionalIdeal.mk0 K J)
            (expMapBasis y) (fun w ↦ ne_of_gt (expMapBasis_pos _ w)) - 1))
      (unitFundamentalParamSet K) := by
  classical
  letI := countable_nonzeroIdealElement K J
  have hi (x : nonzeroIdealElement K J) : IntegrableOn
      (mixedConeRadialKernel K (((x : 𝓞 K) : K)) s) (unitFundamentalParamSet K) :=
    (integrable_mixedConeRadialKernel K (RingOfIntegers.coe_ne_zero_iff.mpr x.prop.2)
      (lt_trans zero_lt_one hs)).integrableOn
  have ht := cone_integrable_tsum hi (cone_summable_integral_norm K J hs)
  have hscaled := ht.const_mul (
    ((((2 : ℝ)⁻¹ ^ nrComplexPlaces K * (Module.finrank ℚ K : ℝ) *
      Units.regulator K) : ℝ) : ℂ)⁻¹)
  apply IntegrableOn.congr_fun hscaled _ measurableSet_unitFundamentalParamSet
  intro y _
  dsimp only
  rw [cone_tsum_radialKernel, ← mul_assoc, inv_mul_cancel₀ (coneRadialConstant_ne_zero K), one_mul]

private theorem cone_integral_tsum_radialKernel
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    (∫ y in unitFundamentalParamSet K,
      ∑' x : nonzeroIdealElement K J, mixedConeRadialKernel K (((x : 𝓞 K) : K)) s y) =
      ((1 / 2 : ℂ) ^ nrRealPlaces K * (1 / 4 : ℂ) ^ nrComplexPlaces K *
        Complex.Gammaℝ s ^ nrRealPlaces K * Complex.Gammaℂ s ^ nrComplexPlaces K) *
          fundamentalConeZeta K J s := by
  classical
  letI := countable_nonzeroIdealElement K J
  letI := countable_idealSet K J
  have hi (x : nonzeroIdealElement K J) : IntegrableOn
      (mixedConeRadialKernel K (((x : 𝓞 K) : K)) s) (unitFundamentalParamSet K) :=
    (integrable_mixedConeRadialKernel K (RingOfIntegers.coe_ne_zero_iff.mpr x.prop.2)
      (lt_trans zero_lt_one hs)).integrableOn
  rw [← integral_tsum_of_summable_integral_norm hi (cone_summable_integral_norm K J hs),
    ← (idealElementMulDecompositionEquiv K J).tsum_eq]
  have hp : Summable (fun p : idealSet K J × unitShiftIndex K ↦
      ∫ y in unitFundamentalParamSet K,
        mixedConeRadialKernel K
          (((fundamentalUnitForShift p.2 : (𝓞 K)ˣ) : K) * idealSetElement K J p.1) s y) := by
    apply Summable.of_norm_bounded
      (summable_prod_integral_norm_mixedConeRadialKernel_unitSlab K J hs)
    intro p
    exact norm_integral_le_integral_norm _
  have hrewrite : (fun p : idealSet K J × unitShiftIndex K ↦
    ∫ y in unitFundamentalParamSet K,
      mixedConeRadialKernel K (((idealElementMulDecompositionEquiv K J p : 𝓞 K) : K)) s y) =
    (fun p : idealSet K J × unitShiftIndex K ↦
    ∫ y in unitFundamentalParamSet K,
      mixedConeRadialKernel K
        (((fundamentalUnitForShift p.2 : (𝓞 K)ˣ) : K) * idealSetElement K J p.1) s y) := by
    funext p
    apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
    intro y _
    rw [idealElementMulDecompositionEquiv_coe]
  rw [hrewrite, hp.tsum_prod]
  have hin : (fun a : idealSet K J ↦ ∑' z : unitShiftIndex K,
      ∫ y in unitFundamentalParamSet K,
        mixedConeRadialKernel K
          (((fundamentalUnitForShift z : (𝓞 K)ˣ) : K) * idealSetElement K J a) s y) =
      (fun a : idealSet K J ↦ ∫ q : realSpace K,
        mixedMellinGaussian K (idealSetElement K J a) s q
        ∂Measure.pi (fun _ : InfinitePlace K ↦
          (volume : Measure ℝ).restrict (Set.Ioi 0))) := by
    funext a
    rw [← integral_mixedConeRadialKernel_eq_tsum_unitSlab K
      (idealSetElement_ne_zero K J a) (lt_trans zero_lt_one hs),
      integral_mixedConeRadialKernel]
  rw [hin]
  exact (hasSum_integral_mixedMellinGaussian_idealSet K J hs).tsum_eq

private theorem cone_normalizingCoefficient :
    ((((2 : ℝ)⁻¹ ^ nrComplexPlaces K * (Module.finrank ℚ K : ℝ) *
      Units.regulator K) : ℝ) : ℂ)⁻¹ *
      ((1 / 2 : ℂ) ^ nrRealPlaces K * (1 / 4 : ℂ) ^ nrComplexPlaces K) =
    (2 : ℂ) ^ (-(↑(nrRealPlaces K + nrComplexPlaces K) : ℤ)) /
      ((Module.finrank ℚ K : ℂ) * (Units.regulator K : ℂ)) := by
  push_cast
  rw [zpow_neg, zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]
  simp only [zpow_natCast]
  have hfour : (1 / 4 : ℂ) = (2 : ℂ)⁻¹ ^ 2 := by norm_num
  rw [hfour, one_div, inv_pow, ← pow_mul, Nat.mul_comm 2, pow_mul]
  simp only [mul_inv_rev, inv_inv, inv_pow]
  field_simp
  <;> ring

theorem setIntegral_fractionalShapeIdealTheta_logMellin
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    (∫ y : realSpace K in unitFundamentalParamSet K,
      Complex.exp ((Module.finrank ℚ K : ℂ) * s *
        (y Units.dirichletUnitTheorem.w₀ : ℂ)) *
        (fractionalShapeIdealTheta K (FractionalIdeal.mk0 K J)
          (expMapBasis y) (fun w ↦ ne_of_gt (expMapBasis_pos _ w)) - 1)) =
      (2 : ℂ) ^ (-(↑(nrRealPlaces K + nrComplexPlaces K) : ℤ)) /
        ((Module.finrank ℚ K : ℂ) * (Units.regulator K : ℂ)) *
        Complex.Gammaℝ s ^ nrRealPlaces K *
        Complex.Gammaℂ s ^ nrComplexPlaces K *
        fundamentalConeZeta K J s := by
  have hi := cone_integral_tsum_radialKernel K J hs
  simp_rw [cone_tsum_radialKernel] at hi
  rw [integral_const_mul] at hi
  have hi' := congrArg
    (fun z : ℂ ↦
      ((((2 : ℝ)⁻¹ ^ nrComplexPlaces K * (Module.finrank ℚ K : ℝ) *
        Units.regulator K) : ℝ) : ℂ)⁻¹ * z) hi
  rw [← mul_assoc, inv_mul_cancel₀ (coneRadialConstant_ne_zero K), one_mul] at hi'
  calc
    _ = _ := hi'
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc,
        cone_normalizingCoefficient]

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

/- Source module: DedekindZetaZeroFree.LFunctions.Dedekind.IdealClassThetaMellin -/

section

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace
open NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

private theorem exp_weight (s : ℂ) (x : ℝ) :
    (Real.exp x : ℂ) * (Real.exp x : ℂ) ^ (s - 1) = Complex.exp (s * x) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  ring
private theorem log_mellin (f : ℝ → ℂ) (s : ℂ) {c n : ℝ} (hc : 0 < c) (hn : 0 < n)
    (hi : Integrable (fun a : ℝ ↦ Complex.exp ((n : ℂ) * s * a) * f (c * Real.exp (n * a)))) :
    HasMellin f s ((n : ℂ) * (c : ℂ) ^ s *
      ∫ a : ℝ, Complex.exp ((n : ℂ) * s * a) * f (c * Real.exp (n * a))) := by
  let h := fun a : ℝ ↦ Complex.exp ((n : ℂ) * s * a) * f (c * Real.exp (n * a))
  let g := fun t : ℝ ↦ (t : ℂ) ^ (s - 1) * f t
  have heq (x : ℝ) : Real.exp x • g (Real.exp x) =
      (c : ℂ) ^ s * h ((x - Real.log c) / n) := by
    have ha : n * ((x - Real.log c) / n) = x - Real.log c := by field_simp
    have ht : c * Real.exp (n * ((x - Real.log c) / n)) = Real.exp x := by
      rw [ha, Real.exp_sub, Real.exp_log hc]
      field_simp
    dsimp [g, h]
    rw [ht, ← mul_assoc, exp_weight,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne'),
      ← Complex.ofReal_log hc.le, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hn.ne']
    <;> ring
  have hj : Integrable (fun x : ℝ ↦ h ((x - Real.log c) / n)) :=
    (hi.comp_div hn.ne').comp_sub_right (Real.log c)
  -- Change variables on all of the positive line, as in the independent Mellin proof.
  have hr : Real.exp '' Set.univ = Set.Ioi 0 := by rw [Set.image_univ, Real.range_exp]
  have habs (x : ℝ) : |Real.exp x| = Real.exp x := abs_of_pos (Real.exp_pos x)
  constructor
  · change IntegrableOn g (Set.Ioi 0)
    rw [← hr, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
      integrableOn_univ]
    simpa only [habs, heq] using hj.const_mul ((c : ℂ) ^ s)
  change (∫ t in Set.Ioi 0, g t) = _
  rw [← hr, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn, setIntegral_univ]
  simp_rw [habs, heq]
  rw [integral_const_mul, integral_sub_right_eq_self (fun x : ℝ ↦ h (x / n))]
  rw [Measure.integral_comp_div]
  simp only [abs_of_pos hn, Complex.real_smul]
  dsimp [h]
  ring
private theorem slab_coords (K : Type*) [Field K] [NumberField K]
    (a : ℝ) (u : Angular K) :
    unitSlabCoordinates (K := K) a u = angularLift K u + radialLift K a := by
  classical
  ext w
  by_cases hw : w = w₀ <;> simp [unitSlabCoordinates, unitRadialAngularEquiv,
    angularLift, radialLift, hw]

private theorem cov_pos (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) : 0 < mixedThetaCovolume K (FractionalIdeal.mk0 K J) := by
  unfold mixedThetaCovolume
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm]
  have hJ := Ideal.absNorm_ne_zero_of_nonZeroDivisors J
  have hd : (discr K : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero K
  positivity

private theorem class_centered_mellin (K : Type) [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun t : ℝ ↦ mixedAngularAverage K (FractionalIdeal.mk0 K J) t - 1) s
      ((Module.finrank ℚ K : ℂ) *
        (mixedThetaCovolume K (FractionalIdeal.mk0 K J) : ℂ) ^ s *
        ((2 : ℂ) ^ (-(↑(nrRealPlaces K + nrComplexPlaces K) : ℤ)) /
          ((Module.finrank ℚ K : ℂ) * (Units.regulator K : ℂ)) *
          Complex.Gammaℝ s ^ nrRealPlaces K * Complex.Gammaℂ s ^ nrComplexPlaces K *
          fundamentalConeZeta K J s)) := by
  classical
  let I := FractionalIdeal.mk0 K J
  let n : ℝ := Module.finrank ℚ K
  let c := mixedThetaCovolume K I
  let F := fun y : realSpace K ↦ Complex.exp ((n : ℂ) * s * (y w₀ : ℂ)) *
    (fractionalShapeIdealTheta K I (NumberField.mixedEmbedding.fundamentalCone.expMapBasis y)
      (fun w ↦ ne_of_gt (NumberField.mixedEmbedding.fundamentalCone.expMapBasis_pos _ w)) - 1)
  have hn : 0 < n := by dsimp [n]; exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  have hc : 0 < c := cov_pos K J
  have hi : IntegrableOn F (DedekindZetaZeroFree.Theta.unitFundamentalParamSet K) :=
    integrableOn_fractionalShapeIdealTheta_logMellin K J hs
  have hip : Integrable (fun p : ℝ × Angular K ↦ F (unitSlabCoordinates p.1 p.2))
      ((volume : Measure ℝ).prod ((volume : Measure (Angular K)).restrict (angularCube K))) := by
    have h := (integrableOn_radialSlab_iff F Set.univ).mp (by simpa using hi)
    unfold IntegrableOn at h
    rw [← Measure.prod_restrict, Measure.restrict_univ] at h
    exact h
  have hcoord (a : ℝ) (u : Angular K) :
      fractionalShapeIdealTheta K I
        (NumberField.mixedEmbedding.fundamentalCone.expMapBasis (unitSlabCoordinates a u))
        (fun w ↦ ne_of_gt (NumberField.mixedEmbedding.fundamentalCone.expMapBasis_pos _ w)) =
        mixedRadialTheta K I (c * Real.exp (n * a)) u := by
    have ht : (Real.log (c * Real.exp (n * a)) - Real.log c) / n = a := by
      rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp]
      field_simp
      ring
    unfold mixedRadialTheta
    congr 1
    unfold mixedThetaShape
    change _ = NumberField.mixedEmbedding.fundamentalCone.expMapBasis
      (angularLift K u + radialLift K ((Real.log (c * Real.exp (n * a)) - Real.log c) / n))
    rw [ht, slab_coords]
  have hinner (a : ℝ) : (∫ u in angularCube K, F (unitSlabCoordinates a u)) =
      Complex.exp ((n : ℂ) * s * a) * (mixedAngularAverage K I (c * Real.exp (n * a)) - 1) := by
    have ht : 0 < c * Real.exp (n * a) := mul_pos hc (Real.exp_pos _)
    rw [mixedAngularAverage_sub_one K I _ ht, ← integral_const_mul]
    apply setIntegral_congr_fun (measurableSet_unitAngularParamSet (K := K))
    intro u hu
    dsimp [F]
    rw [unitSlabCoordinates_apply_w₀, hcoord]
  have havg := hip.integral_prod_left
  have hi' : Integrable (fun a : ℝ ↦ Complex.exp ((n : ℂ) * s * a) *
      (mixedAngularAverage K I (c * Real.exp (n * a)) - 1)) := by
    simpa only [hinner] using havg
  have hm := log_mellin (fun t ↦ mixedAngularAverage K I t - 1) s hc hn hi'
  have hint := setIntegral_unitFundamentalParamSet_eq_radialAngular F hi
  change (∫ y in DedekindZetaZeroFree.Theta.unitFundamentalParamSet K, F y) =
    ∫ a : ℝ, ∫ u in angularCube K, F (unitSlabCoordinates a u) at hint
  simp only [hinner] at hint
  rw [← hint] at hm
  have hcone := setIntegral_fractionalShapeIdealTheta_logMellin K J hs
  change (∫ y in DedekindZetaZeroFree.Theta.unitFundamentalParamSet K, F y) = _ at hcone
  rw [hcone] at hm
  exact hm
private theorem cov_cpow (K : Type) [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    (mixedThetaCovolume K (FractionalIdeal.mk0 K J) : ℂ) ^ s =
      (Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ) ^ s *
        (((|discr K| : ℤ) : ℂ) ^ (s / 2)) := by
  have hN : 0 < (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors J)
  have hD : 0 < |(discr K : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero K)
  unfold mixedThetaCovolume
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm]
  rw [Complex.ofReal_mul, Rat.cast_natCast]
  change (((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) *
    (Real.sqrt |(discr K : ℝ)| : ℂ)) ^ s = _
  rw [Complex.mul_cpow_ofReal_nonneg hN.le (Real.sqrt_nonneg _)]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hD).ne'),
    ← Complex.ofReal_log (Real.sqrt_nonneg _), Real.log_sqrt hD.le]
  have hd : ((|discr K| : ℤ) : ℂ) = Complex.ofReal |(discr K : ℝ)| := by norm_cast
  rw [hd, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    ← Complex.ofReal_log hD.le]
  congr 1
  push_cast
  ring

private theorem normalized_calibration (K : Type) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    (alpha K : ℂ) *
      ((Module.finrank ℚ K : ℂ) *
        (mixedThetaCovolume K (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) : ℂ) ^ s *
        ((2 : ℂ) ^ (-(↑(nrRealPlaces K + nrComplexPlaces K) : ℤ)) /
          ((Module.finrank ℚ K : ℂ) * (Units.regulator K : ℂ)) *
          Complex.Gammaℝ s ^ nrRealPlaces K * Complex.Gammaℂ s ^ nrComplexPlaces K *
          fundamentalConeZeta K (inverseClassIdealRepresentative K C) s)) =
        zetaGammaFactor K s * partialDedekindZeta K C s := by
  have hn : (Module.finrank ℚ K : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hr : (Units.regulator K : ℂ) ≠ 0 := by
    exact_mod_cast (Units.regulator_pos K).ne'
  have hw : (Units.torsionOrder K : ℂ) ≠ 0 := by
    exact_mod_cast Units.torsionOrder_ne_zero K
  rw [partialDedekindZeta_eq_normalized_fundamentalConeZeta K C hs,
    cov_cpow K _ s]
  unfold alpha zetaGammaFactor
  push_cast
  rw [← Nat.cast_add (R := ℤ), zpow_neg, zpow_natCast]
  field_simp [hn, hr, hw]
  <;> ring

theorem hasMellin_classTheta (K : Type) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    HasMellin
      (fun t : ℝ ↦ (alpha K : ℂ) *
        (mixedAngularAverage K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) t - 1))
      s (zetaGammaFactor K s * partialDedekindZeta K C s) := by
  have hm := class_centered_mellin K (inverseClassIdealRepresentative K C) hs
  have hscalar := hasMellin_const_smul hm.1 (alpha K : ℂ)
  change HasMellin _ s ((alpha K : ℂ) * _) at hscalar
  rw [hm.2, normalized_calibration K C hs] at hscalar
  exact hscalar

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

/- Source module: DedekindZetaZeroFree.Theta.Profiles.CenteredPoissonSummation -/

section

noncomputable section

open Classical MeasureTheory NumberField
open NumberField.mixedEmbedding.fundamentalCone
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

open NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem

private theorem centeredCovolume_pos (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < mixedThetaCovolume K I := by
  have hI : 0 < FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) :=
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm
      (FractionalIdeal.absNorm_eq_zero_iff.not.mpr (Units.ne_zero I)))
  have hd : 0 < |(discr K : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero K)
  exact mul_pos (by exact_mod_cast hI) (Real.sqrt_pos.mpr hd)

private theorem centeredShape_prod (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (ht : 0 < t) (u : Angular K) :
    (∏ w : {w : InfinitePlace K // IsReal w}, mixedThetaShape K I t u w.1) *
      ∏ w : {w : InfinitePlace K // IsComplex w}, (mixedThetaShape K I t u w.1)^2 =
        t / mixedThetaCovolume K I := by
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hp := prod_expMapBasis_pow (angularLift K u +
    radialLift K ((Real.log t - Real.log (mixedThetaCovolume K I)) /
      (Module.finrank ℚ K : ℝ)))
  rw [prod_eq_prod_mul_prod] at hp
  simp only [mult_isReal, mult_isComplex, pow_one] at hp
  change _ = _ at hp
  rw [show (angularLift K u + radialLift K
      ((Real.log t - Real.log (mixedThetaCovolume K I)) /
        (Module.finrank ℚ K : ℝ))) w₀ =
      (Real.log t - Real.log (mixedThetaCovolume K I)) /
        (Module.finrank ℚ K : ℝ) by simp [angularLift, radialLift]] at hp
  rw [← Real.exp_nat_mul, mul_div_cancel₀ _ hn, Real.exp_sub,
    Real.exp_log ht, Real.exp_log (centeredCovolume_pos K I)] at hp
  exact hp

theorem covolume_shapeIdealLattice_mixedThetaShape
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (ht : 0 < t) (u : Angular K) :
    ZLattice.covolume
      (shapeIdealLattice K I (mixedThetaShape K I t u)
        (fun v ↦ ne_of_gt (expMapBasis_pos _ v))) volume = t := by
  rw [covolume_shapeIdealLattice, centeredShape_prod K I t ht u,
    abs_of_pos (div_pos ht (centeredCovolume_pos K I))]
  exact div_mul_cancel₀ t (ne_of_gt (centeredCovolume_pos K I))

private theorem centeredCovolume_dual (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    mixedThetaCovolume K (traceDualIdealUnit K I) = (mixedThetaCovolume K I)⁻¹ := by
  have hI : (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.mpr (Units.ne_zero I))
  have hd : |(discr K : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast discr_ne_zero K)
  have hs := Real.sq_sqrt (abs_nonneg (discr K : ℝ))
  have hs0 : Real.sqrt |(discr K : ℝ)| ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd)))
  unfold mixedThetaCovolume
  rw [absNorm_traceDualIdealUnit, absNorm_traceDual_one]
  push_cast
  rw [mul_inv_rev]
  field_simp
  nlinarith [hs]

private theorem centeredShape_inverse (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (u : Angular K) :
    (fun w ↦ (mixedThetaShape K I (1 / t) u w)⁻¹) =
      mixedThetaShape K (traceDualIdealUnit K I) t (-u) := by
  have hx : angularLift K (-u) + radialLift K
      ((Real.log t - Real.log (mixedThetaCovolume K (traceDualIdealUnit K I))) /
        (Module.finrank ℚ K : ℝ)) =
      -(angularLift K u + radialLift K
        ((Real.log (1 / t) - Real.log (mixedThetaCovolume K I)) /
          (Module.finrank ℚ K : ℝ))) := by
    rw [centeredCovolume_dual, one_div, Real.log_inv, Real.log_inv]
    ext w
    simp only [Pi.add_apply, Pi.neg_apply, angularLift, radialLift]
    split_ifs <;> simp <;> ring
  unfold mixedThetaShape
  rw [hx, expMapBasis_apply, expMapBasis_apply, map_neg]
  ext w
  simp [expMap_apply, Real.exp_neg]

theorem mixedRadialTheta_poisson
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (ht : 0 < t) (u : Angular K) :
    mixedRadialTheta K I (1 / t) u =
      (t : ℂ) * mixedRadialTheta K (traceDualIdealUnit K I) t (-u) := by
  unfold mixedRadialTheta
  rw [fractionalShapeIdealTheta_poissonSummation,
    covolume_shapeIdealLattice_mixedThetaShape K I (1 / t) (one_div_pos.mpr ht) u]
  have hq := centeredShape_inverse K I t u
  simp_rw [hq]
  simp [NNReal.smul_def, Real.toNNReal_of_nonneg (le_of_lt (one_div_pos.mpr ht)),
    max_eq_left (le_of_lt (inv_pos.mpr ht)), ht.ne']

theorem mixedAngularAverage_poisson
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (ht : 0 < t) :
    mixedAngularAverage K I (1 / t) =
      (t : ℂ) * mixedNegAngularAverage K (traceDualIdealUnit K I) t := by
  unfold mixedAngularAverage mixedNegAngularAverage
  simp_rw [mixedRadialTheta_poisson K I t ht]
  exact integral_const_mul _ _

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

/- Source module: DedekindZetaZeroFree.Theta.Profiles.MixedThetaFunctionalEquationPair -/

section

noncomputable section

open Classical NumberField
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

theorem mixedThetaPair_primal_integrable (K : Type) [Field K] [NumberField K] :
    MeasureTheory.LocallyIntegrableOn (fun t ↦ (alpha K : ℂ) *
      ∑ C : ClassGroup (𝓞 K), mixedAngularAverage K
        (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) t) (Set.Ioi 0) := by
  apply (MeasureTheory.locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).mpr
  intro s hs hsc
  apply MeasureTheory.Integrable.const_mul
  apply MeasureTheory.integrable_finsetSum
  intro C _
  exact (locallyIntegrableOn_mixedAngularAverage K
    (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))).integrableOn_compact_subset
      hs hsc

theorem mixedThetaPair_dual_integrable (K : Type) [Field K] [NumberField K] :
    MeasureTheory.LocallyIntegrableOn (fun t ↦ (alpha K : ℂ) *
      ∑ C : ClassGroup (𝓞 K), mixedNegAngularAverage K
        (traceDualIdealUnit K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))) t) (Set.Ioi 0) := by
  apply (MeasureTheory.locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).mpr
  intro s hs hsc
  apply MeasureTheory.Integrable.const_mul
  apply MeasureTheory.integrable_finsetSum
  intro C _
  exact (locallyIntegrableOn_mixedNegAngularAverage K
    (traceDualIdealUnit K
      (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)))).integrableOn_compact_subset
        hs hsc

def mixedThetaPair (K : Type) [Field K] [NumberField K] : WeakFEPair ℂ where
  f := fun t ↦ (alpha K : ℂ) *
    ∑ C : ClassGroup (𝓞 K),
      mixedAngularAverage K
        (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) t
  g := fun t ↦ (alpha K : ℂ) *
    ∑ C : ClassGroup (𝓞 K),
      mixedNegAngularAverage K
        (traceDualIdealUnit K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))) t
  k := 1
  ε := 1
  f₀ := (alpha K : ℂ) * (Fintype.card (ClassGroup (𝓞 K)) : ℂ)
  g₀ := (alpha K : ℂ) * (Fintype.card (ClassGroup (𝓞 K)) : ℂ)
  hk := by norm_num
  hε := by norm_num
  hf_int := mixedThetaPair_primal_integrable K
  hg_int := mixedThetaPair_dual_integrable K
  h_feq := by
    intro x hx
    simp only [Real.rpow_one, one_mul, smul_eq_mul]
    simp_rw [mixedAngularAverage_poisson K _ x hx]
    rw [← Finset.mul_sum]
    ring
  hf_top := by
    intro r
    have h := (Asymptotics.IsBigO.sum (s := Finset.univ)
      (fun C _ ↦ mixedAngularAverage_isBigO_rpow K
        (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) r)).const_mul_left
          (alpha K : ℂ)
    simpa only [Finset.sum_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, mul_sub] using h
  hg_top := by
    intro r
    have h := (Asymptotics.IsBigO.sum (s := Finset.univ)
      (fun C _ ↦ mixedNegAngularAverage_isBigO_rpow K
        (traceDualIdealUnit K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))) r)).const_mul_left
            (alpha K : ℂ)
    simpa only [Finset.sum_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, mul_sub] using h

@[simp] theorem mixedThetaPair_k (K : Type) [Field K] [NumberField K] :
    (mixedThetaPair K).k = 1 := rfl

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

/- Source module: DedekindZetaZeroFree.LFunctions.Dedekind.MixedThetaPairMellin -/

section

noncomputable section

open Classical NumberField
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

private lemma mixedThetaPair_f (K : Type) [Field K] [NumberField K] :
    (mixedThetaPair K).f = fun t => (alpha K : ℂ) *
      ∑ C : ClassGroup (𝓞 K),
        mixedAngularAverage K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) t := rfl

private lemma mixedThetaPair_f0 (K : Type) [Field K] [NumberField K] :
    (mixedThetaPair K).f₀ = (alpha K : ℂ) * (Fintype.card (ClassGroup (𝓞 K)) : ℂ) := rfl

private lemma hasMellin_finset_sum {s : ℂ} {ι : Type*} (t : Finset ι)
    (f : ι → ℝ → ℂ) (m : ι → ℂ)
    (h : ∀ i ∈ t, HasMellin (f i) s (m i)) :
    HasMellin (fun x => ∑ i ∈ t, f i x) s (∑ i ∈ t, m i) := by
  classical
  induction t using Finset.induction with
  | empty =>
      constructor
      · show MeasureTheory.IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (0 : ℂ)) (Set.Ioi 0)
        simpa using (MeasureTheory.integrableOn_zero
          (f := fun _ : ℝ => (0 : ℂ)) (s := Set.Ioi 0) (μ := volume))
      · simp [mellin]
  | insert a t ha ih =>
      have hfa := h a (Finset.mem_insert_self a t)
      have hft : ∀ i ∈ t, HasMellin (f i) s (m i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have ih' := ih hft
      have hadd := hasMellin_add hfa.1 ih'.1
      rw [hfa.2, ih'.2] at hadd
      convert hadd using 2
      · exact Finset.sum_insert ha
      · exact Finset.sum_insert ha

theorem hasMellin_mixedThetaPair (K : Type) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun t : ℝ ↦ (mixedThetaPair K).f t - (mixedThetaPair K).f₀)
      s (zetaGammaFactor K s * NumberField.dedekindZeta K s) := by

  have hfun : (fun t : ℝ ↦ (mixedThetaPair K).f t - (mixedThetaPair K).f₀) =
      (fun t => ∑ C : ClassGroup (𝓞 K), (alpha K : ℂ) *
        (mixedAngularAverage K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) t - 1)) := by
    rw [mixedThetaPair_f, mixedThetaPair_f0]
    funext t
    conv_rhs => rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    ring
  rw [hfun]

  have h := hasMellin_finset_sum (Finset.univ : Finset (ClassGroup (𝓞 K)))
    (fun C t => (alpha K : ℂ) *
      (mixedAngularAverage K
        (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) t - 1))
    (fun C => zetaGammaFactor K s * partialDedekindZeta K C s)
    (fun C _ => hasMellin_classTheta K C hs)

  rw [show (∑ C : ClassGroup (𝓞 K), zetaGammaFactor K s * partialDedekindZeta K C s)
      = zetaGammaFactor K s * NumberField.dedekindZeta K s by
    rw [← Finset.mul_sum, sum_partialDedekindZeta K hs]] at h
  exact h

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end

/- Source module: DedekindZetaZeroFree.HarmonicAnalysis.Haar.PeriodicCubeIntegration -/

section

/-
The translation change-of-variables and fundamental-domain comparison pattern is adapted
from LeanPool/lean-pool, commit `68aa6ee63d20ad76bcc15f595adfc72949991f06`,
`LeanPool/Odlyzko/CompletedZeta/UnitSlabTranslation.lean`.
Copyright (c) 2026 The FLT Project; released under the Apache 2.0 license.
-/

open MeasureTheory

namespace DedekindZetaZeroFree.Hecke

theorem periodicCubeIntegral_translation {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℂ) (hf : Continuous f)
    (hperiodic : ∀ (z : ι → ℤ) (u : ι → ℝ),
      f (u + fun i => (z i : ℝ)) = f u) :
    ∀ d : ι → ℝ,
      (∫ u in Set.univ.pi (fun _ : ι => Set.Ico (0 : ℝ) 1), f (u + d)) =
        ∫ u in Set.univ.pi (fun _ : ι => Set.Ico (0 : ℝ) 1), f u := by
  intro d
  classical
  let L := Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))
  let Q := Set.univ.pi (fun _ : ι => Set.Ico (0 : ℝ) 1)
  have hQ : IsAddFundamentalDomain L Q volume := by
    simpa [L, Q, ZSpan.fundamentalDomain_pi_basisFun] using
      ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) (volume : Measure (ι → ℝ))
  letI : VAddInvariantMeasure L (ι → ℝ) volume := ⟨fun g s hs =>
    (measurePreserving_add_left volume (g : ι → ℝ)).measure_preimage hs.nullMeasurableSet⟩
  have hf : ∀ (g : L) u, f (g +ᵥ u) = f u := by
    intro g u
    have hg := ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ g).mp g.prop
    choose z hz using hg
    have heq : (g : ι → ℝ) = fun i => (z i : ℝ) := by
      ext i
      simpa using (hz i).symm
    change f ((g : ι → ℝ) + u) = f u
    rw [heq, add_comm]
    exact hperiodic z u
  let e : (ι → ℝ) ≃ᵐ (ι → ℝ) := MeasurableEquiv.addRight d
  have he : MeasurePreserving e volume volume :=
    ⟨e.measurable, by simpa [e] using map_add_right_eq_self volume d⟩
  have hT : IsAddFundamentalDomain L (e '' Q) volume := by
    apply hQ.image_of_equiv e.toEquiv ?_ (Equiv.refl L) ?_
    · exact (measurePreserving_add_right volume (-d)).quasiMeasurePreserving
    · intro g x
      change ((g : ι → ℝ) + x) + d = (g : ι → ℝ) + (x + d)
      exact add_assoc _ _ _
  calc
    _ = ∫ u in e '' Q, f u := (he.setIntegral_image_emb e.measurableEmbedding f Q).symm
    _ = ∫ u in Q, f u := hT.setIntegral_eq hQ hf

theorem periodicCubeIntegral_negation {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℂ) (hf : Continuous f)
    (hperiodic : ∀ (z : ι → ℤ) (u : ι → ℝ),
      f (u + fun i => (z i : ℝ)) = f u) :
    (∫ u in Set.univ.pi (fun _ : ι => Set.Ico (0 : ℝ) 1), f (-u)) =
      ∫ u in Set.univ.pi (fun _ : ι => Set.Ico (0 : ℝ) 1), f u := by
  classical
  let L := Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))
  let Q := Set.univ.pi (fun _ : ι => Set.Ico (0 : ℝ) 1)
  have hQ : IsAddFundamentalDomain L Q volume := by
    simpa [L, Q, ZSpan.fundamentalDomain_pi_basisFun] using
      ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) (volume : Measure (ι → ℝ))
  letI : VAddInvariantMeasure L (ι → ℝ) volume := ⟨fun g s hs =>
    (measurePreserving_add_left volume (g : ι → ℝ)).measure_preimage hs.nullMeasurableSet⟩
  have hf : ∀ (g : L) u, f (g +ᵥ u) = f u := by
    intro g u
    have hg := ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ g).mp g.prop
    choose z hz using hg
    have heq : (g : ι → ℝ) = fun i => (z i : ℝ) := by
      ext i
      simpa using (hz i).symm
    change f ((g : ι → ℝ) + u) = f u
    rw [heq, add_comm]
    exact hperiodic z u
  let e : (ι → ℝ) ≃ᵐ (ι → ℝ) := MeasurableEquiv.neg (ι → ℝ)
  have he : MeasurePreserving e volume volume := Measure.measurePreserving_neg volume
  have hT : IsAddFundamentalDomain L (e '' Q) volume := by
    apply hQ.image_of_equiv e.toEquiv ?_ (Equiv.neg L) ?_
    · exact (Measure.measurePreserving_neg volume).quasiMeasurePreserving
    · intro g x
      change -(-(g : ι → ℝ) + x) = (g : ι → ℝ) + -x
      simp [add_comm]
  calc
    _ = ∫ u in e '' Q, f u := (he.setIntegral_image_emb e.measurableEmbedding f Q).symm
    _ = ∫ u in Q, f u := hT.setIntegral_eq hQ hf

end DedekindZetaZeroFree.Hecke

end

/- Source module: DedekindZetaZeroFree.Theta.Profiles.PrincipalIdealCenteredShapeCovariance -/

section

open NumberField
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

open Classical NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding.fundamentalCone
open DedekindZetaZeroFree.AbelianQuotient.Theta

private theorem covariance_exp_add {F : Type} [Field F] [NumberField F]
    (x y : mixedEmbedding.realSpace F) :
    expMapBasis (x + y) = expMapBasis x * expMapBasis y := by
  simp only [expMapBasis_apply, map_add, expMap_add]

private theorem covariance_covolume_pos {F : Type} [Field F] [NumberField F]
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : 0 < mixedThetaCovolume F I := by
  apply mul_pos
  · exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _)
      (Ne.symm (fun h => Units.ne_zero I (FractionalIdeal.absNorm_eq_zero_iff.mp h)))
  · apply Real.sqrt_pos.mpr
    exact abs_pos.mpr (by exact_mod_cast discr_ne_zero F)

private theorem covariance_reindex {F : Type} [Field F] [NumberField F]
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (a : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) * (I : FractionalIdeal (𝓞 F)⁰ F))
    (f : F → ℂ) :
    (∑' x : ↥((J : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F), f (x : F)) =
    ∑' x : ↥((I : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F), f ((a : F) * x) := by
  have h := FractionalIdeal.eq_spanSingleton_mul.mp hJ
  let m : ↥((I : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) →
      ↥((J : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) :=
    fun x => ⟨(a : F) * x, h.2 x x.2⟩
  have hm : Function.Bijective m := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact mul_left_cancel₀ (Units.ne_zero a) (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx, he⟩ := h.1 y y.2
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  exact ((Equiv.ofBijective m hm).tsum_eq (fun x => f (x : F))).symm

theorem principalCenteredShapeCovariance (F : Type) [Field F] [NumberField F]
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (a : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ d : DedekindZetaZeroFree.AbelianQuotient.Theta.Angular F,
      ∀ t : ℝ, 0 < t →
        ∀ u : DedekindZetaZeroFree.AbelianQuotient.Theta.Angular F,
          DedekindZetaZeroFree.AbelianQuotient.Theta.mixedRadialTheta F J t u =
            DedekindZetaZeroFree.AbelianQuotient.Theta.mixedRadialTheta F I t (u + d) := by
  classical
  let A : mixedEmbedding.realSpace F := fun v => v (a : F)
  let L : mixedEmbedding.realSpace F := expMapBasis.symm A
  have hA : ∀ v, 0 < A v := by
    intro v
    exact InfinitePlace.pos_iff.mpr (Units.ne_zero a)
  have hL : expMapBasis L = A := by
    apply expMapBasis.right_inv
    change A ∈ expMap.target
    rw [expMap_target]
    exact Set.mem_univ_pi.mpr hA
  let N : ℝ := (|(Algebra.norm ℚ) (a : F)| : ℚ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (abs_pos.mpr
      (show (Algebra.norm ℚ) (a : F) ≠ 0 from Algebra.norm_ne_zero_iff.mpr (Units.ne_zero a)))
  have hrad : L w₀ = Real.log N / (Module.finrank ℚ F : ℝ) := by
    have hp := prod_expMapBasis_pow L
    rw [hL, prod_eq_abs_norm] at hp
    have hl := congrArg Real.log hp
    rw [Real.log_pow, Real.log_exp] at hl
    dsimp [N]
    exact (eq_div_iff (by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne')).mpr
      (by linarith)
  have hc : mixedThetaCovolume F J = N * mixedThetaCovolume F I := by
    unfold mixedThetaCovolume
    rw [hJ, map_mul, FractionalIdeal.absNorm_span_singleton]
    dsimp [N]
    push_cast
    ring
  let d : Angular F := fun v => L v
  refine ⟨d, ?_⟩
  intro t ht u
  have hcoords :
      angularLift F (u + d) + radialLift F
          ((Real.log t - Real.log (mixedThetaCovolume F I)) / (Module.finrank ℚ F : ℝ)) =
      (angularLift F u + radialLift F
          ((Real.log t - Real.log (mixedThetaCovolume F J)) / (Module.finrank ℚ F : ℝ))) + L := by
    have hlog : Real.log (mixedThetaCovolume F J) =
        Real.log N + Real.log (mixedThetaCovolume F I) := by
      rw [hc, Real.log_mul hN.ne' (covariance_covolume_pos I).ne']
    funext v
    by_cases hv : v = w₀
    · subst v
      simp only [Pi.add_apply, angularLift, radialLift, dite_true, ite_true]
      rw [hlog, hrad]
      ring
    · simp only [Pi.add_apply, angularLift, radialLift, dif_neg hv, if_neg hv,
        add_zero, d]
  have hs : mixedThetaShape F I t (u + d) =
      (fun v => mixedThetaShape F J t u v * v (a : F)) := by
    unfold mixedThetaShape
    rw [hcoords, covariance_exp_add, hL]
    rfl
  unfold mixedRadialTheta
  rw [fractionalShapeIdealTheta_eq_tsum_mixedGaussian,
    fractionalShapeIdealTheta_eq_tsum_mixedGaussian]
  rw [covariance_reindex I J a hJ (fun x => mixedGaussian F x (mixedThetaShape F J t u))]
  apply tsum_congr
  intro x
  unfold mixedGaussian
  congr 3
  apply Finset.sum_congr rfl
  intro v _
  rw [map_mul, hs]
  ring

end DedekindZetaZeroFree.Hecke

end

/- Source module: DedekindZetaZeroFree.Theta.Periods.AngularAverageClassInvariance -/

section

open NumberField
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

open DedekindZetaZeroFree.AbelianQuotient.Theta

private theorem continuous_class_slice (F : Type) [Field F] [NumberField F]
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t) :
    Continuous (mixedRadialTheta F I t) := by
  change Continuous ((fun p : ℝ × Angular F ↦ mixedRadialTheta F I p.1 p.2) ∘
    (fun u : Angular F ↦ (t, u)))
  exact (continuousOn_mixedRadialTheta F I).comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ ↦ ⟨ht, Set.mem_univ _⟩)

private theorem periodic_slice (F : Type) [Field F] [NumberField F]
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ)
    (z : {v : InfinitePlace F // v ≠ Units.dirichletUnitTheorem.w₀} → ℤ)
    (u : Angular F) :
    mixedRadialTheta F I t (u + fun i => (z i : ℝ)) = mixedRadialTheta F I t u := by
  classical
  have h : angularLift F (u + fun i => (z i : ℝ)) =
      angularLift F u + DedekindZetaZeroFree.Theta.unitCoordinateShift z := by
    ext v
    by_cases hv : v = Units.dirichletUnitTheorem.w₀ <;>
      simp [angularLift, DedekindZetaZeroFree.Theta.unitCoordinateShift, hv]
  simpa only [mixedRadialTheta, mixedThetaShape, h, add_right_comm] using
    fractionalShapeIdealTheta_expMapBasis_add_unitCoordinateShift F I
      (angularLift F u + radialLift F ((Real.log t - Real.log (mixedThetaCovolume F I)) /
        (Module.finrank ℚ F : ℝ))) z

private theorem principal_of_class (F : Type) [Field F] [NumberField F]
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hclass : ClassGroup.mk F I = ClassGroup.mk F J) :
    ∃ a : Fˣ, (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) * (I : FractionalIdeal (𝓞 F)⁰ F) := by
  have hq := congrArg (ClassGroup.equiv F) hclass
  simp only [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
    RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_monoidHom_refl] at hq
  have hq' : QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range I =
      QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range J := hq
  rw [QuotientGroup.mk'_eq_mk'] at hq'
  rcases hq' with ⟨a, ⟨b, rfl⟩, ha⟩
  refine ⟨b, ?_⟩
  simpa only [Units.val_mul, coe_toPrincipalIdeal, mul_comm] using
    (congrArg (fun U : (FractionalIdeal (𝓞 F)⁰ F)ˣ => (U : FractionalIdeal (𝓞 F)⁰ F)) ha).symm

theorem mixedAngularAverage_class_invariant (F : Type) [Field F] [NumberField F]
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hclass : ClassGroup.mk F I = ClassGroup.mk F J)
    (t : ℝ) (ht : 0 < t) :
    DedekindZetaZeroFree.AbelianQuotient.Theta.mixedAngularAverage F I t =
      DedekindZetaZeroFree.AbelianQuotient.Theta.mixedAngularAverage F J t := by
  classical
  obtain ⟨a, ha⟩ := principal_of_class F I J hclass
  obtain ⟨d, hd⟩ := principalCenteredShapeCovariance F I J a ha
  unfold mixedAngularAverage
  simp_rw [hd t ht]
  exact (periodicCubeIntegral_translation (mixedRadialTheta F I t)
    (continuous_class_slice F I t ht) (periodic_slice F I t) d).symm

theorem mixedNegAngularAverage_eq_mixedAngularAverage
    (F : Type) [Field F] [NumberField F]
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t) :
    DedekindZetaZeroFree.AbelianQuotient.Theta.mixedNegAngularAverage F I t =
      DedekindZetaZeroFree.AbelianQuotient.Theta.mixedAngularAverage F I t := by
  classical
  exact periodicCubeIntegral_negation (mixedRadialTheta F I t)
    (continuous_class_slice F I t ht) (periodic_slice F I t)

end DedekindZetaZeroFree.Hecke

end

/- Source module: DedekindZetaZeroFree.Arithmetic.Ideals.TraceDualClassInvolution -/

section

/-
https://github.com/LeanPool/lean-pool
Revision: 68aa6ee63d20ad76bcc15f595adfc72949991f06.
Source: LeanPool/Odlyzko/CompletedZeta/TraceDualClass.lean.
-/

noncomputable section

open scoped NumberField nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

def principalTraceDualClass (F : Type) [Field F] [NumberField F] : ClassGroup (𝓞 F) :=
  ClassGroup.mk F (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F 1)

theorem mk_traceDualIdealUnit (F : Type) [Field F] [NumberField F]
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    ClassGroup.mk F (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F I) =
      principalTraceDualClass F * (ClassGroup.mk F I)⁻¹ := by
  have h : DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F I =
      DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F 1 * I⁻¹ := by
    apply Units.ext
    simpa using
      DedekindZetaZeroFree.AbelianQuotient.Theta.coe_traceDualIdealUnit_eq_dual_one_mul_inv F I
  rw [h, map_mul, map_inv]
  rfl

def principalTraceDualClassEquiv (F : Type) [Field F] [NumberField F] :
    ClassGroup (𝓞 F) ≃ ClassGroup (𝓞 F) where
  toFun C := (principalTraceDualClass F)⁻¹ * C⁻¹
  invFun C := (principalTraceDualClass F)⁻¹ * C⁻¹
  left_inv := by
    intro C
    simp [mul_inv_rev, mul_comm, mul_left_comm]
  right_inv := by
    intro C
    simp [mul_inv_rev, mul_comm, mul_left_comm]

@[simp] theorem principalTraceDualClassEquiv_apply (F : Type) [Field F] [NumberField F]
    (C : ClassGroup (𝓞 F)) :
    principalTraceDualClassEquiv F C = (principalTraceDualClass F)⁻¹ * C⁻¹ := rfl

@[simp] theorem principalTraceDualClassEquiv_symm_apply (F : Type)
    [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) :
    (principalTraceDualClassEquiv F).symm C = (principalTraceDualClass F)⁻¹ * C⁻¹ := rfl

theorem mk_traceDual_inverseClassIdealRepresentative (F : Type) [Field F] [NumberField F]
    (C : ClassGroup (𝓞 F)) :
    ClassGroup.mk F
      (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F
        (FractionalIdeal.mk0 F
          (DedekindZetaZeroFree.AbelianQuotient.Theta.inverseClassIdealRepresentative F C))) =
    ClassGroup.mk F
      (FractionalIdeal.mk0 F
        (DedekindZetaZeroFree.AbelianQuotient.Theta.inverseClassIdealRepresentative F
          (principalTraceDualClassEquiv F C))) := by
  rw [mk_traceDualIdealUnit, ClassGroup.mk_mk0, ClassGroup.mk_mk0]
  simp [DedekindZetaZeroFree.AbelianQuotient.Theta.mk0_inverseClassIdealRepresentative,
    mul_inv_rev, mul_comm]

end DedekindZetaZeroFree.Hecke

end

end

/- Source module: DedekindZetaZeroFree.Theta.Inversion.MixedPairConstantTermSelfDuality -/

section

namespace DedekindZetaZeroFree.Hecke

theorem mixedThetaPair_selfdual (F : Type) [Field F] [NumberField F] :
    ∀ t : ℝ, 0 < t →
      (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).f t =
        (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).g t := by
  intro t ht
  change (_ : ℂ) * ∑ C : ClassGroup (NumberField.RingOfIntegers F),
      DedekindZetaZeroFree.AbelianQuotient.Theta.mixedAngularAverage F
        (FractionalIdeal.mk0 F
          (DedekindZetaZeroFree.AbelianQuotient.Theta.inverseClassIdealRepresentative F C)) t =
    (_ : ℂ) * ∑ C : ClassGroup (NumberField.RingOfIntegers F),
      DedekindZetaZeroFree.AbelianQuotient.Theta.mixedNegAngularAverage F
        (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F
          (FractionalIdeal.mk0 F
            (DedekindZetaZeroFree.AbelianQuotient.Theta.inverseClassIdealRepresentative F C))) t
  congr 1
  symm
  calc
    _ = ∑ C : ClassGroup (NumberField.RingOfIntegers F),
        DedekindZetaZeroFree.AbelianQuotient.Theta.mixedAngularAverage F
          (FractionalIdeal.mk0 F
            (DedekindZetaZeroFree.AbelianQuotient.Theta.inverseClassIdealRepresentative F
              (principalTraceDualClassEquiv F C))) t := by
      apply Finset.sum_congr rfl
      intro C _
      rw [mixedNegAngularAverage_eq_mixedAngularAverage F _ t ht]
      exact mixedAngularAverage_class_invariant F _ _
        (mk_traceDual_inverseClassIdealRepresentative F C) t ht
    _ = _ := (principalTraceDualClassEquiv F).sum_comp
      (fun C ↦ DedekindZetaZeroFree.AbelianQuotient.Theta.mixedAngularAverage F
        (FractionalIdeal.mk0 F
          (DedekindZetaZeroFree.AbelianQuotient.Theta.inverseClassIdealRepresentative F C)) t)

@[simp] theorem mixedThetaPair_k (F : Type) [Field F] [NumberField F] :
    (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).k = 1 := rfl

@[simp] theorem mixedThetaPair_ε (F : Type) [Field F] [NumberField F] :
    (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).ε = 1 := rfl

@[simp] theorem mixedThetaPair_f₀_eq_g₀ (F : Type) [Field F] [NumberField F] :
    (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).f₀ =
      (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).g₀ := rfl

end DedekindZetaZeroFree.Hecke

end

namespace OMA.DedekindKernel

open Complex Filter Set NumberField NumberField.InfinitePlace MeasureTheory Asymptotics
open DedekindZetaZeroFree.Odlyzko
open scoped NumberField Topology

theorem norm_Gamma_le_real {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le, norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem gamma_shift_bound {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    |s.im| ^ n * ‖Gamma s‖ ≤ Real.Gamma (s.re + n) := by
  induction n generalizing s with
  | zero => simpa using norm_Gamma_le_real hs
  | succ n ih =>
    have hpos : 0 < (s + 1).re := by rw [add_re, one_re]; linarith
    have hstep : |s.im| * ‖Gamma s‖ ≤ ‖Gamma (s + 1)‖ := by
      rw [Gamma_add_one s (ne_zero_of_re_pos hs), norm_mul]
      exact mul_le_mul_of_nonneg_right (abs_im_le_norm s) (norm_nonneg _)
    calc |s.im| ^ (n + 1) * ‖Gamma s‖ = |s.im| ^ n * (|s.im| * ‖Gamma s‖) := by ring
         _ ≤ |s.im| ^ n * ‖Gamma (s + 1)‖ := by gcongr
         _ ≤ Real.Gamma ((s + 1).re + n) := by simpa using ih (s := s + 1) hpos
         _ = Real.Gamma (s.re + (n + 1 : ℕ)) := by push_cast; congr 1; simp; ring

def StripBound (a b : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc a b → ‖F s‖ ≤ C

def StripDecay (a b : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc a b → (1 + s.im ^ 2) * ‖F s‖ ≤ C

theorem StripDecay.bound {a b : ℝ} {F : ℂ → ℂ} (h : StripDecay a b F) : StripBound a b F := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun s hs => le_trans ?_ (h s hs)⟩
  nlinarith [mul_nonneg (sq_nonneg s.im) (norm_nonneg (F s))]

theorem StripBound.pow {a b : ℝ} {F : ℂ → ℂ} (h : StripBound a b F) (n : ℕ) :
    StripBound a b (fun s => F s ^ n) := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C ^ n, pow_nonneg hC _, fun s hs => (norm_pow _ _).le.trans (pow_le_pow_left₀ (norm_nonneg _) (h s hs) n)⟩

theorem StripDecay.mul_bound {a b : ℝ} {F G : ℂ → ℂ} (hF : StripDecay a b F) (hG : StripBound a b G) :
    StripDecay a b (fun s => F s * G s) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  refine ⟨C * D, mul_nonneg hC hD, fun s hs => ?_⟩
  dsimp only
  rw [norm_mul, ← mul_assoc]
  exact mul_le_mul (hF s hs) (hG s hs) (norm_nonneg _) hC

theorem StripDecay.pow_succ {a b : ℝ} {F : ℂ → ℂ} (hF : StripDecay a b F) (n : ℕ) :
    StripDecay a b (fun s => F s ^ (n + 1)) := by
  simpa only [pow_succ'] using hF.mul_bound (hF.bound.pow n)

theorem gamma_strip {a b : ℝ} (ha : 0 < a) : StripDecay a b Gamma := by
  let g (x : ℝ) := Real.Gamma x + Real.Gamma (x + 2)
  have hcont {x : ℝ} (hx : 0 < x) : ContinuousAt Real.Gamma x :=
    (Real.differentiableAt_Gamma (fun n => ne_of_gt (by have := Nat.cast_nonneg (α := ℝ) n; linarith : -(n : ℝ) < x))).continuousAt
  have hg : ContinuousOn g (Icc a b) := by
    intro x hx
    have hadd : ContinuousAt (fun y : ℝ => y + 2) x := by fun_prop
    have hshift : ContinuousAt (fun y : ℝ => Real.Gamma (y + 2)) x :=
      (hcont (x := x + 2) (by linarith [hx.1])).comp (f := fun y : ℝ => y + 2) hadd
    exact ((hcont (ha.trans_le hx.1)).fun_add hshift).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hg
  refine ⟨max C 0, le_max_right _ _, fun s hs => ?_⟩
  have h0 : 0 < s.re := ha.trans_le hs.1
  have h2 := gamma_shift_bound h0 2
  simp only [Nat.cast_ofNat, sq_abs] at h2
  calc (1 + s.im ^ 2) * ‖Gamma s‖ ≤ g s.re := by dsimp [g]; linarith [norm_Gamma_le_real h0]
       _ ≤ C := hC (mem_image_of_mem _ hs)
       _ ≤ _ := le_max_left _ _

theorem gammaR_strip {a b : ℝ} (ha : 0 < a) : StripDecay a b Gammaℝ := by
  obtain ⟨C, hC, h⟩ := gamma_strip (b := b / 2) (half_pos ha)
  refine ⟨4 * C, by positivity, fun s hs => ?_⟩
  have hhalf : (s / 2).re ∈ Icc (a / 2) (b / 2) := by
    simp only [Set.mem_Icc, div_ofNat_re]; constructor <;> linarith [hs.1, hs.2]
  have hx := h (s / 2) hhalf
  have hπ : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp; linarith [hs.1]
  have hG : ‖Gammaℝ s‖ ≤ ‖Gamma (s / 2)‖ := by
    rw [Gammaℝ_def, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hπ
  refine (mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ 1 + s.im ^ 2)).trans ?_
  simp only [div_ofNat_im] at hx
  nlinarith [norm_nonneg (Gamma (s / 2))]

theorem StripDecay.vertical {F : ℂ → ℂ} {a b σ : ℝ} (h : StripDecay a b F) (hσ : σ ∈ Icc a b)
    (hcont : Continuous (fun y : ℝ => F (σ + y * I))) : VerticalIntegrable F σ := by
  obtain ⟨C, hC, h⟩ := h
  apply (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
  filter_upwards with y
  change ‖F (σ + y * I)‖ ≤ C * (1 + y ^ 2)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa [mul_comm] using h ((σ : ℂ) + y * I) (by simpa using hσ)

noncomputable def completion (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) * Gammaℝ s ^ nrRealPlaces K *
    Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s


theorem gammaC_strip {a b : ℝ} (ha : 0 < a) : StripDecay a b Gammaℂ := by
  obtain ⟨C, hC, h⟩ := (gammaR_strip (b := b + 1) (a := a + 1) (by linarith)).bound
  have hshift : StripBound a b (fun s => Gammaℝ (s + 1)) := by
    refine ⟨C, hC, fun s hs => h _ ?_⟩
    simp only [mem_Icc, add_re, one_re]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  simpa only [Gammaℝ_mul_Gammaℝ_add_one] using (gammaR_strip ha).mul_bound hshift

variable (K : Type*) [Field K] [NumberField K]

theorem zeta_strip {a b : ℝ} (ha : 1 < a) : StripBound a b (dedekindZeta K) := by
  let c (n : ℕ) : ℂ := idealNormCount K n
  have hsum : LSeriesSummable c (a : ℂ) := lSeriesSummable_idealNormCount K (by simpa using ha)
  refine ⟨∑' n, ‖LSeries.term c (a : ℂ) n‖, tsum_nonneg (fun _ => norm_nonneg _), fun s hs => ?_⟩
  have hle : (a : ℂ).re ≤ s.re := hs.1
  exact (norm_tsum_le_tsum_norm (hsum.of_re_le_re hle).norm).trans
    (Summable.tsum_le_tsum (LSeries.norm_term_le_of_re_le_re c hle) (hsum.of_re_le_re hle).norm hsum.norm)

theorem exp_strip (d a b : ℝ) : StripBound a b (fun s => exp (s * d)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (show ContinuousOn (fun t : ℝ => Real.exp (t * d)) (Icc a b) by fun_prop)
  refine ⟨max C 0, le_max_right _ _, fun s hs => ?_⟩
  rw [Complex.norm_exp, mul_re]
  simpa using (hC (mem_image_of_mem _ hs)).trans (le_max_left C 0)

theorem completion_strip {a b : ℝ} (ha : 1 < a) :
    StripDecay a b (completion K) := by
  have hR := gammaR_strip (b := b) (zero_lt_one.trans ha)
  have hC := gammaC_strip (b := b) (zero_lt_one.trans ha)
  have hp : StripDecay a b (fun s => Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K) := by
    cases hr : nrRealPlaces K with
    | succ r => exact (hR.pow_succ r).mul_bound (hC.bound.pow _)
    | zero =>
      cases hc : nrComplexPlaces K with
      | succ n => simpa using hC.pow_succ n
      | zero =>
        have := card_add_two_mul_card_eq_rank K
        have := Module.finrank_pos (R := ℚ) (M := K)
        omega
  have h := (hp.mul_bound (exp_strip (Real.log (discr K).natAbs / 2) a b)).mul_bound (zeta_strip K ha)
  simpa only [StripDecay, completion, mul_assoc, mul_left_comm, mul_comm] using h

theorem completion_diff {s : ℂ} (hs : 1 < s.re) : DifferentiableAt ℂ (completion K) s := by
  have habs := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    (f := fun n => (idealNormCount K n : ℂ)) (x := 1) (fun y hy => lSeriesSummable_idealNormCount K (by simpa using hy))
  have hZ : DifferentiableAt ℂ (dedekindZeta K) s :=
    (LSeries_hasDerivAt (lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hs))).differentiableAt
  have hR (z : ℂ) (hz : 0 < z.re) : DifferentiableAt ℂ Gammaℝ z := by
    simpa only [Pi.inv_def, inv_inv] using
      (differentiable_Gammaℝ_inv z).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hz))
  have hs' : 0 < s.re := zero_lt_one.trans hs
  have hC : DifferentiableAt ℂ Gammaℂ s := by
    have hC0 : Gammaℂ s ≠ 0 := by
      rw [← Gammaℝ_mul_Gammaℝ_add_one]
      exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos hs')
        (Gammaℝ_ne_zero_of_re_pos (by simp; linarith))
    simpa only [Pi.inv_def, inv_inv] using (differentiable_Gammaℂ_inv s).inv (inv_ne_zero hC0)
  exact (((show DifferentiableAt ℂ (fun z : ℂ => exp (z * (Real.log (discr K).natAbs / 2 : ℝ))) s
      by fun_prop).mul ((hR s hs').pow _)).mul (hC.pow _)).mul hZ

end OMA.DedekindKernel

namespace OMA.DedekindKernel

open Complex MeasureTheory NumberField NumberField.InfinitePlace Set
open scoped Topology NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient DedekindZetaZeroFree.AbelianQuotient.Theta

/-- Pointwise inversion needs the values of the Mellin transform only on the chosen line. -/
theorem mellinInv_eq_of_hasMellin_on_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {g : ℝ → E} {F : ℂ → E} {σ x : ℝ} (hx : 0 < x)
    (hm : ∀ y : ℝ, HasMellin g (σ + y * I) (F (σ + y * I)))
    (hv : VerticalIntegrable F σ) (hc : ContinuousAt g x) :
    mellinInv σ F x = g x := by
  have hline (y : ℝ) : mellin g (σ + y * I) = F (σ + y * I) := (hm y).2
  have hvm : VerticalIntegrable (mellin g) σ := by
    simpa only [VerticalIntegrable, hline] using hv
  calc
    mellinInv σ F x = mellinInv σ (mellin g) x := by simp only [mellinInv, hline]
    _ = g x := mellinInv_mellin_eq σ g hx (by simpa using (hm 0).1) hvm hc

variable (K : Type) [Field K] [NumberField K]

private theorem gammaFactor_normalization (s : ℂ) :
    zetaGammaFactor K s =
      exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K := by
  have hD : 0 < ((discr K).natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)
  have hd : ((|discr K| : ℤ) : ℂ) = (((discr K).natAbs : ℝ) : ℂ) := by
    calc
      ((|discr K| : ℤ) : ℂ) = (((discr K).natAbs : ℤ) : ℂ) :=
        congrArg (fun n : ℤ => (n : ℂ)) (Int.natCast_natAbs _).symm
      _ = _ := by simp only [Int.cast_natCast, Complex.ofReal_natCast]
  rw [zetaGammaFactor, hd, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    ← Complex.ofReal_log hD.le]
  push_cast
  ring_nf

/-- The zero-lattice-vector term summed over the ideal classes. -/
noncomputable def thetaConstant : ℂ :=
  (((2 : ℝ) ^ (nrRealPlaces K + nrComplexPlaces K) * Units.regulator K /
    (Units.torsionOrder K : ℝ) : ℝ) : ℂ) * (Fintype.card (ClassGroup (𝓞 K)) : ℂ)

/-- The inverse Mellin kernel of the completed series is the class theta sum with its
zero mode removed, pointwise at every positive scale and on every line to the right of one. -/
theorem mellinInv_eq_centeredTheta {σ x : ℝ} (hσ : 1 < σ) (hx : 0 < x) :
    mellinInv σ (completion K) x = (mixedThetaPair K).f x - thetaConstant K := by
  let P := mixedThetaPair K
  let g (t : ℝ) := P.f t - P.f₀
  change mellinInv σ (completion K) x = g x
  apply mellinInv_eq_of_hasMellin_on_line hx
  · intro y
    simpa only [gammaFactor_normalization, completion] using
      hasMellin_mixedThetaPair K (s := (σ : ℂ) + y * I) (by simpa using hσ)
  · apply (completion_strip (b := σ) K hσ).vertical ⟨le_rfl, le_rfl⟩
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (completion_diff K (s := (σ : ℂ) + y * I) (by simpa using hσ)).continuousAt.comp
      (f := fun u : ℝ => (σ : ℂ) + u * I) (by fun_prop)
  · have hc : ContinuousAt P.f x := by
      change ContinuousAt (fun t : ℝ => (alpha K : ℂ) *
        ∑ C : ClassGroup (𝓞 K), mixedAngularAverage K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) t) x
      refine continuousAt_const.mul ((continuousOn_finsetSum _ fun C _ => ?_).continuousAt
        (isOpen_Ioi.mem_nhds hx))
      exact continuousOn_average K _ (continuousOn_mixedRadialTheta K _)
    exact hc.sub continuousAt_const

/-- The trace-dual involution carries the full theta sum to itself under reciprocal scales. -/
theorem mellinInv_reciprocity {σ x : ℝ} (hσ : 1 < σ) (hx : 0 < x) :
    mellinInv σ (completion K) (1 / x) + thetaConstant K =
      (x : ℂ) * (mellinInv σ (completion K) x + thetaConstant K) := by
  rw [mellinInv_eq_centeredTheta K hσ (one_div_pos.mpr hx),
    mellinInv_eq_centeredTheta K hσ hx, sub_add_cancel, sub_add_cancel]
  simpa only [mixedThetaPair_k, show (mixedThetaPair K).ε = 1 from rfl, Real.rpow_one,
    one_mul, smul_eq_mul, ← DedekindZetaZeroFree.Hecke.mixedThetaPair_selfdual K x hx]
    using (mixedThetaPair K).h_feq x hx

end OMA.DedekindKernel

theorem OMA.solution : OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1.H2 := by
  intro K _ _ _
  exact ⟨OMA.DedekindKernel.thetaConstant K, fun x hx =>
    OMA.DedekindKernel.mellinInv_reciprocity K (by norm_num : (1 : ℝ) < 2) hx⟩

/-
License for the ported AxiomMath and FLT Project sources.

Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
