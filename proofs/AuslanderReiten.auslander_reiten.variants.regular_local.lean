import FormalConjectures.Paper.AuslanderReiten

-- Copyright (c) 2025 Nailin Guan. All rights reserved for the adapted portions.
-- The marked adaptations are distributed under Apache-2.0.

universe u

open CategoryTheory CategoryTheory.Abelian


namespace OMA.RegularLocal

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

private theorem extends_to_free_kernel (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) [Module.Finite R S.X₁] [Module.Free R S.X₁]
    (h : Subsingleton (Ext S.X₃ (ModuleCat.of R R) 1)) :
    ∃ r : S.X₂ ⟶ S.X₁, CategoryStruct.comp S.f r = 𝟙 S.X₁ := by
  classical
  letI := h
  let Z := ModuleCat.of R R
  have extend (a : S.X₁ ⟶ Z) : ∃ b : S.X₂ ⟶ Z, CategoryStruct.comp S.f b = a := by
    obtain ⟨v, hv⟩ := Ext.contravariant_sequence_exact₁ hS Z (Ext.mk₀ a)
      (show 1 + 0 = 1 by rfl) (Subsingleton.eq_zero _)
    obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective S.X₂ Z).surjective v
    rw [Ext.mk₀_comp_mk₀, (Ext.mk₀_bijective _ _).injective.eq_iff] at hv
    exact ⟨b, hv⟩
  let I := Module.Free.ChooseBasisIndex R S.X₁
  letI : Fintype I := Module.Free.ChooseBasisIndex.fintype R S.X₁
  let e : S.X₁ ≃ₗ[R] (I → R) := (Module.Free.chooseBasis R S.X₁).equivFun
  have point (i : I) : ∃ b : S.X₂ ⟶ Z,
      CategoryStruct.comp S.f b = ModuleCat.ofHom ((LinearMap.proj i).comp e.toLinearMap) :=
    extend _
  choose b hb using point
  let r : S.X₂ ⟶ S.X₁ := ModuleCat.ofHom
    (e.symm.toLinearMap.comp (LinearMap.pi fun i => (b i).hom))
  refine ⟨r, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply e.injective
  funext i
  change e (e.symm (fun j => b j (S.f x))) i = e x i
  rw [e.apply_symm_apply]
  exact congrArg (fun f : S.X₁ ⟶ Z => f x) (hb i)

theorem projective_of_ext_vanishing (n : ℕ) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hPd : HasProjectiveDimensionLT M (n + 1))
    (hMR : ∀ i > 0, Subsingleton (Ext M (ModuleCat.of R R) i)) : Projective M := by
  induction n generalizing M with
  | zero =>
    exact projective_iff_hasProjectiveDimensionLT_one.mpr hPd
  | succ n ih =>
    obtain ⟨_, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R M
    let S : ShortComplex (ModuleCat.{u} R) := f.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
    let Z := ModuleCat.of R R
    have hK (i : ℕ) (hi : 0 < i) : Subsingleton (Ext S.X₁ Z i) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
      haveI : Subsingleton (Ext M Z (1 + (k + 1))) := hMR _ (by omega)
      haveI : Subsingleton (Ext S.X₂ Z (k + 1)) := Ext.subsingleton_of_projective _ _ _
      have zero (a : Ext S.X₁ Z (k + 1)) : a = 0 := by
        obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₁ hS Z a rfl (Subsingleton.eq_zero _)
        simpa [Subsingleton.eq_zero b] using hb.symm
      exact ⟨fun a b => (zero a).trans (zero b).symm⟩
    have hPdK : HasProjectiveDimensionLT S.X₁ (n + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hPd
    haveI : Projective S.X₁ := ih S.X₁ hPdK hK
    haveI : Module.Projective R S.X₁ := ModuleCat.projective_of_module_projective S.X₁
    haveI : Module.Free R S.X₁ := Module.free_of_flat_of_isLocalRing
    obtain ⟨r, hr⟩ := extends_to_free_kernel S hS (hMR 1 (by decide))
    let split := ShortComplex.Splitting.ofExactOfRetraction S hS.exact r hr hS.epi_g
    exact (Retract.mk split.s S.g split.s_g).projective

theorem free_of_ext_vanishing (M : ModuleCat.{u} R) [Module.Finite R M]
    (hPd : ∃ n, HasProjectiveDimensionLT M (n + 1))
    (hMR : ∀ i > 0, Subsingleton (Ext M (ModuleCat.of R R) i)) : Module.Free R M := by
  obtain ⟨n, hn⟩ := hPd
  haveI : Projective M := projective_of_ext_vanishing n M hn hMR
  haveI : Module.Projective R M := inferInstance
  exact Module.free_of_flat_of_isLocalRing

end OMA.RegularLocal

open CategoryTheory Abelian IsLocalRing
open scoped Pointwise


namespace OMA.RegularLocal

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Adapted from Nailin Guan, Mathlib/RingTheory/Regular/ProjectiveDimension.lean,
-- commit 2fcfef815a43b0b3da78b7493d8e286107a50a3f, Apache 2.0.
theorem lift_projective_dimension {x : R} [IsLocalRing (R ⧸ Ideal.span {x})]
    (regR : IsSMulRegular R x) (mem : x ∈ maximalIdeal R) (n : ℕ)
    (M : ModuleCat.{u} R) [Module.Finite R M] (regM : IsSMulRegular M x)
    (hQ : HasProjectiveDimensionLT
      (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) (n + 1)) :
    HasProjectiveDimensionLT M (n + 1) := by
  induction n generalizing M with
  | zero =>
    haveI : Projective (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :=
      projective_iff_hasProjectiveDimensionLT_one.mpr hQ
    haveI : Module.Projective (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
      ModuleCat.projective_of_module_projective (ModuleCat.of _ (QuotSMulTop x M))
    haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
    haveI : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
      Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
    have hfree : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
      Module.free_of_flat_of_isLocalRing
    have hmem : x ∈ (⊥ : Ideal R).jacobson :=
      maximalIdeal_le_jacobson _ mem
    haveI : Module.Free R M := (Module.free_quotSMulTop_iff_free R M hmem regM).mp hfree
    exact projective_iff_hasProjectiveDimensionLT_one.mp inferInstance
  | succ n ih =>
    obtain ⟨P, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R M
    let S := f.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
    have regP : IsSMulRegular S.X₂ x := (isLeftRegular_iff_isRegular.mp regR).isSMulRegular
    have regK : IsSMulRegular S.X₁ x := regP.submodule _ _
    have surj := Ideal.Quotient.mk_surjective (I := Ideal.span {x})
    let g := (QuotSMulTop.map x (LinearMap.ker f).subtype).extendScalarsOfSurjective surj
    let h := (QuotSMulTop.map x f).extendScalarsOfSurjective surj
    have hExact : Function.Exact g h :=
      QuotSMulTop.map_exact x f.exact_subtype_ker_map surjf
    let SQ := ModuleCat.shortComplexOfCompEqZero g h hExact.linearMap_comp_eq_zero
    have inj : Function.Injective (QuotSMulTop.map x (LinearMap.ker f).subtype) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro y hy
      obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ y
      simp only [LinearMap.mem_ker, QuotSMulTop.map_apply_mk, Submodule.subtype_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists,
        Submodule.mem_top, true_and] at hy
      obtain ⟨z, hz⟩ := hy
      have hzker := y'.2
      rw [← hz, LinearMap.mem_ker, map_smul] at hzker
      simp only [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists,
        Submodule.mem_top, true_and, Subtype.exists, SetLike.mk_smul_mk, LinearMap.mem_ker]
      exact ⟨z, regM.right_eq_zero_of_smul hzker, Subtype.val_inj.mp hz⟩
    have hSQ := ModuleCat.shortComplex_shortExact SQ hExact inj
      (QuotSMulTop.map_surjective x surjf)
    haveI : Module.FinitePresentation R P := Module.finitePresentation_of_finite R P
    have hQK : HasProjectiveDimensionLT SQ.X₁ (n + 1) :=
      (hSQ.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hQ
    exact (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mpr (ih S.X₁ regK hQK)

end OMA.RegularLocal

open IsLocalRing IsRegularLocalRing
open scoped Pointwise


namespace OMA.RegularLocal

variable {R : Type u} [CommRing R]

-- Adapted from Nailin Guan, Mathlib/Algebra/Module/SpanRankOperations.lean and
-- Mathlib/RingTheory/RegularLocalRing/Basic.lean, commit
-- 31de1910408b03287bf4e81c13fe16872d771ec2, Apache 2.0.
private instance residueRingHomSurjective (R : Type u) [CommRing R] [IsLocalRing R] :
    RingHomSurjective (residue R) := ⟨residue_surjective⟩

private def toCotangentSpace (R : Type u) [CommRing R] [IsLocalRing R] :
    maximalIdeal R →ₛₗ[residue R] CotangentSpace R where
  __ := (maximalIdeal R).toCotangent
  map_smul' r x := by simp [← ResidueField.algebraMap_eq]

private theorem toCotangentSpace_eq_toCotangent (R : Type u) [CommRing R] [IsLocalRing R] :
    ⇑(toCotangentSpace R) = (maximalIdeal R).toCotangent := rfl

private theorem spanFinrank_add_kernel_cotangent [IsLocalRing R] [IsNoetherianRing R]
    {S : Type u} [CommRing S] [IsLocalRing S] [Algebra R S]
    (surj : Function.Surjective (algebraMap R S)) [IsLocalHom (algebraMap R S)] :
    (maximalIdeal S).spanFinrank + Module.finrank (ResidueField R)
      ((Submodule.comap (maximalIdeal R).subtype (RingHom.ker (algebraMap R S))).map
        (toCotangentSpace R)) = (maximalIdeal R).spanFinrank := by
  have : IsNoetherianRing S := isNoetherianRing_of_surjective R S (algebraMap R S) surj
  let f := (maximalIdeal R).mapCotangent (maximalIdeal S) (Algebra.ofId R S) (fun x hx => by simpa)
  have hker : RingHom.ker (algebraMap R S) ≤ maximalIdeal R :=
    le_maximalIdeal (RingHom.ker_ne_top _)
  have eqsup : (maximalIdeal S).comap (algebraMap R S) =
      RingHom.ker (algebraMap R S) ⊔ maximalIdeal R := by
    rw [maximalIdeal_comap, sup_eq_right.mpr hker]
  let toCot := (Submodule.comap (maximalIdeal R).subtype (RingHom.ker (algebraMap R S))).map
    (toCotangentSpace R)
  let Q := CotangentSpace R ⧸ toCot
  have ker : (LinearMap.ker f : Set (maximalIdeal R).Cotangent) = toCot := by
    rw [Ideal.mapCotangent_ker_of_surjective surj eqsup, inf_eq_left.mpr hker]
    simp [toCot, toCotangentSpace]
  let f' : Q →+ CotangentSpace S :=
    QuotientAddGroup.lift _ f (fun x hx => (Set.ext_iff.mp ker x).mpr hx)
  have bij : Function.Bijective f' := by
    constructor
    · rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
      exact (QuotientAddGroup.eq_zero_iff _).mpr ((Set.ext_iff.mp ker x).mp hx)
    · apply QuotientAddGroup.lift_surjective_of_surjective
      exact Ideal.mapCotangent_surjective_of_comap_eq surj eqsup
  let e : Q ≃+ CotangentSpace S := AddEquiv.ofBijective f' bij
  have compat (r : ResidueField R) (m : Q) :
      e (r • m) = (ResidueField.map (algebraMap R S)) r • e m := by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨r, rfl⟩ := residue_surjective r
    exact (map_smul f r m).trans (algebraMap_smul S r _).symm
  have bij' : Function.Bijective (ResidueField.map (algebraMap R S)) :=
    ⟨RingHom.injective _, Ideal.Quotient.lift_surjective_of_surjective _ _
      (Ideal.Quotient.mk_surjective.comp surj)⟩
  have rk := lift_rank_eq_of_equiv_equiv (ResidueField.map (algebraMap R S)) e bij' compat
  have frk : Module.finrank (ResidueField R) Q =
      Module.finrank (ResidueField S) (CotangentSpace S) := by
    simpa [Module.finrank] using congrArg Cardinal.toNat rk
  simp only [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  rw [← frk, Submodule.finrank_quotient_add_finrank]

private theorem quotient_of_independent_parameters [IsRegularLocalRing R] (S : Finset R)
    (sub : (S : Set R) ⊆ maximalIdeal R)
    (li : LinearIndependent (ResidueField R) ((maximalIdeal R).toCotangent ∘ Set.inclusion sub)) :
    IsRegularLocalRing (R ⧸ Ideal.span (S : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span (S : Set R)) + S.card = ringKrullDim R := by
  have : Nontrivial (R ⧸ Ideal.span (S : Set R)) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (Ideal.span_le.mpr sub))
  have : IsLocalHom (Ideal.Quotient.mk (Ideal.span (S : Set R))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalRing (R ⧸ Ideal.span (S : Set R)) :=
    IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsNoetherianRing (R ⧸ Ideal.span (S : Set R)) :=
    isNoetherianRing_of_surjective _ _ _ Ideal.Quotient.mk_surjective
  have hspan : (maximalIdeal (R ⧸ Ideal.span (S : Set R))).spanFinrank + S.card =
      (maximalIdeal R).spanFinrank := by
    have h := spanFinrank_add_kernel_cotangent
      (R := R) (S := R ⧸ Ideal.span (S : Set R)) Ideal.Quotient.mk_surjective
    convert h using 2
    have range_val : (S : Set R) = Set.range (Subtype.val ∘ Set.inclusion sub) := by
      rw [Set.val_comp_inclusion, Subtype.range_val]
    have eqmap : Ideal.span S =
        (Submodule.span R (Set.range (Set.inclusion sub))).map (maximalIdeal R).subtype := by
      rw [Submodule.map_span, Ideal.submodule_span_eq, ← Set.range_comp]
      congr
    have eqcomap : Submodule.comap (maximalIdeal R).subtype (Ideal.span S) =
        Submodule.span R (Set.range (Set.inclusion sub)) := by
      rw [eqmap, Submodule.comap_map_eq_of_injective (maximalIdeal R).subtype_injective]
    have hmk : RingHom.ker (algebraMap R (R ⧸ Ideal.span (S : Set R))) =
        Ideal.span (S : Set R) := by
      change RingHom.ker (Ideal.Quotient.mk (Ideal.span (S : Set R))) = _
      exact Ideal.mk_ker
    rw [hmk, eqcomap, Submodule.map_span, ← Set.range_comp]
    simp only [SetLike.coe_sort_coe, toCotangentSpace_eq_toCotangent, (Fintype.card_coe S).symm]
    exact (finrank_span_eq_card li).symm
  rw [isRegularLocalRing_iff]
  have lo := ringKrullDim_le_ringKrullDim_quotient_add_card S
    (by simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using sub)
  have eq : (↑(maximalIdeal (R ⧸ Ideal.span (S : Set R))).spanFinrank : WithBot ℕ∞) +
      S.card = ringKrullDim R := by
    rw [← Nat.cast_add, hspan, IsRegularLocalRing.spanFinrank_maximalIdeal]
  have hi : ringKrullDim (R ⧸ Ideal.span (S : Set R)) + S.card ≤
      (↑(maximalIdeal (R ⧸ Ideal.span (S : Set R))).spanFinrank : WithBot ℕ∞) + S.card :=
    add_le_add_left (ringKrullDim_le_spanFinrank_maximalIdeal _) _
  exact ⟨ENat.WithBot.add_natCast_cancel.mp (le_antisymm (eq.le.trans lo) hi),
    le_antisymm (hi.trans eq.le) lo⟩

theorem quotient_parameter [IsRegularLocalRing R] {x : R} (mem : x ∈ maximalIdeal R)
    (nmem : x ∉ (maximalIdeal R) ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
  rw [← Nat.cast_one, ← Finset.card_singleton x, ← Finset.coe_singleton x]
  apply quotient_of_independent_parameters {x} (by simpa)
  simpa [← LinearMap.mem_ker, Ideal.mem_toCotangent_ker] using nmem

theorem field_of_dimension_zero [IsRegularLocalRing R] (dim : ringKrullDim R = 0) : IsField R := by
  simpa [← (isRegularLocalRing_iff R).mp ‹_›, Submodule.spanFinrank_eq_zero_iff_eq_bot,
    IsNoetherian.noetherian, ← isField_iff_maximalIdeal_eq] using dim

theorem exists_parameter [IsRegularLocalRing R] (dim : ringKrullDim R ≠ 0) :
    ∃ x ∈ maximalIdeal R, x ∉ (maximalIdeal R) ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  have hlt := (maximalIdeal_sq_lt_maximalIdeal R).mpr (mt ringKrullDim_eq_zero_of_isField dim)
  have fin := (minimalPrimes.finite_of_isNoetherianRing R).insert ((maximalIdeal R) ^ 2)
  suffices h : ∃ x ∈ maximalIdeal R,
      x ∉ ⋃ I ∈ (insert ((maximalIdeal R) ^ 2) (minimalPrimes R)), I by
    simpa using h
  by_contra! h
  absurd (Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite fin _ _
    (fun I hI ne _ => (Set.mem_of_mem_insert_of_ne hI ne).1.1) hlt.ne_top hlt.ne_top).mp h
  simp only [Set.mem_insert_iff, hlt.ne.symm, ← Ideal.height_eq_zero_iff, false_or]
  rwa [← WithBot.coe_inj, maximalIdeal_height_eq_ringKrullDim]

theorem domain_of_dimension (d : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (dim : ringKrullDim R = d) : IsDomain R := by
  induction d generalizing R with
  | zero =>
    exact (field_of_dimension_zero (by simpa using dim)).isDomain
  | succ d ih =>
    have nzero : ringKrullDim R ≠ 0 := dim.trans_ne (by exact_mod_cast Nat.succ_ne_zero d)
    obtain ⟨x, mem, nmem, avoid⟩ := exists_parameter nzero
    obtain ⟨reg, dimQ⟩ := quotient_parameter mem nmem
    rw [dim, Nat.cast_succ] at dimQ
    haveI : IsRegularLocalRing (R ⧸ Ideal.span {x}) := reg
    have dom := ih (R ⧸ Ideal.span {x}) (ENat.WithBot.add_one_cancel.mp dimQ)
    have : (Ideal.span {x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp dom
    obtain ⟨p, pmin, hp⟩ := Ideal.exists_minimalPrimes_le (bot_le (a := Ideal.span {x}))
    have self : Ideal.span {x} * p = p := by
      haveI : p.IsPrime := pmin.1.1
      refine Ideal.mul_le_right.antisymm ?_
      intro y hy
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp (hp hy)
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
        ((Ideal.IsPrime.mul_mem_left_iff (avoid p pmin)).mp hy)
    suffices hpbot : p = ⊥ from @IsDomain.of_bot_isPrime R _ (hpbot ▸ pmin.1.1)
    exact Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator (IsNoetherian.noetherian _)
      self.symm (((Ideal.span_singleton_le_iff_mem _).mpr mem).trans (maximalIdeal_le_jacobson _))

end OMA.RegularLocal

namespace OMA.RegularLocal

theorem finite_projective_dimension (d : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (dim : ringKrullDim R = d) (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ n, HasProjectiveDimensionLT M (n + 1) := by
  induction d generalizing R with
  | zero =>
    letI : Field R := (field_of_dimension_zero (by simpa using dim)).toField
    exact ⟨0, inferInstance⟩
  | succ d ih =>
    have nzero : ringKrullDim R ≠ 0 :=
      dim.trans_ne (by exact_mod_cast Nat.succ_ne_zero d)
    obtain ⟨x, mem, nmem, _⟩ := exists_parameter nzero
    obtain ⟨reg, dimQ⟩ := quotient_parameter mem nmem
    rw [dim, Nat.cast_succ] at dimQ
    let Q := R ⧸ Ideal.span {x}
    haveI : IsRegularLocalRing Q := reg
    haveI : IsDomain R := domain_of_dimension (d + 1) R dim
    have hx : x ≠ 0 := by
      intro h
      apply nmem
      simp [h]
    have regR : IsSMulRegular R x := fun _ _ h => mul_left_cancel₀ hx h
    obtain ⟨_, _, _, _, _, f, surj⟩ := Module.exists_finite_presentation R M
    let S := f.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer surj
    have regP : IsSMulRegular S.X₂ x := (isLeftRegular_iff_isRegular.mp regR).isSMulRegular
    have regK : IsSMulRegular S.X₁ x := regP.submodule _ _
    haveI : Module.Finite Q (QuotSMulTop x S.X₁) :=
      Module.Finite.of_restrictScalars_finite R Q (QuotSMulTop x S.X₁)
    obtain ⟨k, hk⟩ := ih Q (ENat.WithBot.add_one_cancel.mp dimQ)
      (ModuleCat.of Q (QuotSMulTop x S.X₁))
    have hK := lift_projective_dimension regR mem k S.X₁ regK hk
    exact ⟨k + 1, (hS.hasProjectiveDimensionLT_X₃_iff k inferInstance).mpr hK⟩

end OMA.RegularLocal

theorem OMA.solution : type_of% @AuslanderReiten.auslander_reiten.variants.regular_local := by
  intro R _ M _ _ _ _ hMR
  have hdim : ringKrullDim R = (IsLocalRing.maximalIdeal R).spanFinrank :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  exact OMA.RegularLocal.free_of_ext_vanishing (ModuleCat.of R M)
    (OMA.RegularLocal.finite_projective_dimension _ R hdim (ModuleCat.of R M)) hMR
