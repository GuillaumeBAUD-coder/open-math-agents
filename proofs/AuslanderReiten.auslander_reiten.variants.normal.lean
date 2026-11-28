import FormalConjectures.Paper.AuslanderReiten

/-!
# The Auslander–Reiten conjecture for normal domains

`OMA.solution` proves Kimura's theorem: a finitely generated module `M` over a commutative
Noetherian normal domain `R` with `Ext^i(M, R) = 0` and `Ext^i(M, M) = 0` for all `i > 0` is
projective.

## Reduction

The reduction clears denominators in Ext, handles the local rings of dimension at most
one, and uses induction on prime height. At a nonfree stalk of minimal height the module is
locally free on the punctured spectrum, the depth is at least two and iterated syzygies preserve
self-Ext vanishing. After two steps the syzygy is reflexive, and further steps give vanishing
against the ring for its dual through any prescribed finite degree. This leaves `PuncturedCase`.

## The punctured case

Kimura proves the local criterion (Theorem 2.4 and Corollary 2.5) with the tail of a dualizing
complex over the completion. The proof here uses neither completions nor Cohen's structure
theorem. Take a regular sequence `x₁, …, x_t` in the maximal ideal, where `t` is the depth, and
put `W₀ = R` and `W_{r+1} = W_r[1/x_{r+1}] / W_r`, a model of the top local cohomology of
`(x₁, …, x_r)`. Each step is a short exact sequence whose middle term is divisible by an
element of the maximal ideal, and a power of that element kills every positive Ext out of a
module that is locally free on the punctured spectrum. So Ext groups shift along the chain
(`exists_chain`):

* `Hom(k, W_t)` vanishes exactly when `Ext^t(k, R)` does, so `W_t` has a nonzero socle element;
* for a counterexample `X` with second syzygy `K`, the group `Ext^1(X, Hom(K^*, W_t))` embeds
  in `Ext^{t+1}(X, K^{**})`, which is `Ext^{t-1}(X, X) = 0`.

A trace computation (`trace_vanishing`, `dual_ker_criterion`) turns these two facts into the
statement that every functional on `K` with values in the maximal ideal lies in `𝔪 K^*`. Then
`K^*` embeds in a free module compatibly with reduction modulo `𝔪`, so `K^*` is free
(`free_dual_of_criterion`), and so is the reflexive module `K`. This contradicts infinite
projective dimension.

Kaito Kimura, *Auslander–Reiten conjecture for normal rings*, Israel J. Math. 274 (2026),
no. 1, 441–453, https://doi.org/10.1007/s11856-025-2877-0.
Numbering here follows the 2023 preprint, arXiv:2304.03956v1, Theorem 2.4, Corollary 2.5,
Lemma 2.6, Propositions 2.8 and 2.10, and Corollary 2.16(3), https://arxiv.org/abs/2304.03956v1.
-/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u

namespace OMA.AuslanderReitenReduction

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A denominator clears any Ext class between localized modules when the source is finite. -/
theorem exists_smul_ext_eq_map (S : Submonoid R) (X Y : ModuleCat.{u} R)
    [Module.Finite R X] (n : ℕ)
    (e : Ext (X.localizedModule S) (Y.localizedModule S) n) :
    ∃ (s : S) (a : Ext X Y n), algebraMap R (Localization S) s.val • e =
      a.mapExactFunctor (ModuleCat.localizedModuleFunctor S) := by
  let F := ModuleCat.localizedModuleFunctor.{u} S
  induction n generalizing X with
  | zero =>
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective e
    let := Module.finitePresentation_of_finite R X
    obtain ⟨⟨h, s⟩, hs⟩ := IsLocalizedModule.surj S
      (IsLocalizedModule.mapExtendScalars S (X.localizedModuleMkLinearMap S)
        (Y.localizedModuleMkLinearMap S) (Localization S)) g.hom
    refine ⟨s, Ext.mk₀ (ModuleCat.ofHom h), ?_⟩
    rw [Ext.mapExactFunctor_mk₀, ← Ext.mk₀_smul]
    apply congrArg Ext.mk₀
    apply ModuleCat.hom_ext
    ext x
    change algebraMap R (Localization S) s.val • g.hom x =
      IsLocalizedModule.mapExtendScalars S _ _ _ h x
    rw [algebraMap_smul]
    exact LinearMap.congr_fun hs x
  | succ n ih =>
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R X
    let T := f.shortComplexKer
    have hT : T.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have hF := hT.map_of_exact F
    have : Projective (T.map F).X₂ := F.projective_obj_of_projective (inferInstance : Projective T.X₂)
    obtain ⟨b, hb⟩ := precomp_extClass_surjective_of_projective_X₂ (F.obj Y) hF n e
    obtain ⟨s, a, ha⟩ := ih T.X₁ b
    refine ⟨s, hT.extClass.comp a (add_comm 1 n), ?_⟩
    change hF.extClass.comp b (add_comm 1 n) = e at hb
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
    change algebraMap R (Localization S) s.val • e = hF.extClass.comp (a.mapExactFunctor F) _
    exact (congrArg (algebraMap R (Localization S) s.val • ·) hb.symm).trans
      ((Ext.comp_smul hF.extClass b _ _).symm.trans
        (congrArg (fun z => hF.extClass.comp z (add_comm 1 n)) ha))

/-- Vanishing of an individual Ext group persists under localization. -/
theorem subsingleton_ext_localized (S : Submonoid R) (X Y : ModuleCat.{u} R)
    [Module.Finite R X] (n : ℕ) (h : Subsingleton (Ext X Y n)) :
    Subsingleton (Ext (X.localizedModule S) (Y.localizedModule S) n) := by
  apply subsingleton_of_forall_eq 0
  intro e
  obtain ⟨s, a, hs⟩ := exists_smul_ext_eq_map S X Y n e
  rw [Subsingleton.eq_zero a, Ext.mapExactFunctor_zero] at hs
  exact (IsLocalization.map_units (Localization S) s).smul_eq_zero.mp hs

private theorem subsingleton_ext_iso {A : Type u} [CommRing A] (X : ModuleCat.{u} A)
    {Y Z : ModuleCat.{u} A} (e : Y ≅ Z) (n : ℕ) (h : Subsingleton (Ext X Y n)) :
    Subsingleton (Ext X Z n) :=
  ((extFunctorObj X n).mapIso e).addCommGroupIsoToAddEquiv.subsingleton_congr.mp h

/-- In the second variable the localization of the rank-one module identifies with the ring. -/
theorem subsingleton_ext_localized_ring (S : Submonoid R) (X : ModuleCat.{u} R)
    [Module.Finite R X] (n : ℕ) (h : Subsingleton (Ext X (ModuleCat.of R R) n)) :
    Subsingleton (Ext (X.localizedModule S) (ModuleCat.of (Localization S) (Localization S)) n) := by
  have : IsLocalizedModule S ((ModuleCat.of R R).localizedModuleMkLinearMap S) :=
    ModuleCat.localizedModule_isLocalizedModule _ _
  let e := (IsLocalizedModule.linearEquiv S ((ModuleCat.of R R).localizedModuleMkLinearMap S)
    (Algebra.linearMap R (Localization S))).extendScalarsOfIsLocalization S (Localization S)
  exact subsingleton_ext_iso _ e.toModuleIso n (subsingleton_ext_localized S _ _ n h)

omit [IsNoetherianRing R] in
/-- Vanishing against the ring implies vanishing against each finite free module. -/
theorem subsingleton_ext_finite_free [Nontrivial R] (X Y : ModuleCat.{u} R) [Module.Finite R Y]
    [Module.Free R Y] (n : ℕ) (h : Subsingleton (Ext X (ModuleCat.of R R) n)) :
    Subsingleton (Ext X Y n) := by
  let f := fun _ : Fin (Module.finrank R Y) => ModuleCat.of R R
  let e := (ModuleCat.biproductIsoPi f) ≪≫ (Module.finBasis R Y).equivFun.symm.toModuleIso
  apply subsingleton_ext_iso X e n
  exact (Ext.addEquivBiproduct X (biproduct.isBilimit f) n).subsingleton_congr.mpr
    (inferInstanceAs (Subsingleton (∀ _ : Fin (Module.finrank R Y), Ext X (ModuleCat.of R R) n)))

omit [IsNoetherianRing R] in
/-- A projective presentation splits if Ext in degree one vanishes against its kernel. -/
theorem projective_of_ext_kernel (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    [Projective T.X₂] (h : Subsingleton (Ext T.X₃ T.X₁ 1)) : Module.Projective R T.X₃ := by
  rcases Ext.covariant_sequence_exact₃ T.X₃ hT (Ext.mk₀ (𝟙 T.X₃)) (zero_add 1)
    (Subsingleton.eq_zero _) with ⟨a, ha⟩
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective a
  rw [Ext.mk₀_comp_mk₀, (Ext.mk₀_bijective _ _).injective.eq_iff] at ha
  exact (IsProjective.iff_projective _).mpr (Retract.mk g T.g ha).projective

/-- Over a PID the kernel of a finite free presentation is finite free. -/
theorem projective_of_ext_one_pid [IsDomain R] [IsPrincipalIdealRing R] (X : ModuleCat.{u} R)
    [Module.Finite R X] (h : Subsingleton (Ext X (ModuleCat.of R R) 1)) :
    Module.Projective R X := by
  obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R X
  let T := f.shortComplexKer
  have : Module.Free R T.X₁ := inferInstanceAs (Module.Free R (LinearMap.ker f))
  exact projective_of_ext_kernel T (LinearMap.shortExact_shortComplexKer hf)
    (subsingleton_ext_finite_free X T.X₁ 1 h)

omit [IsNoetherianRing R] in
/-- Ext vanishing shifts from a module to its first syzygy. -/
theorem ext_syzygy (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    [Projective T.X₂] (Y : ModuleCat.{u} R) (i : ℕ) (hi : 0 < i)
    (h : Subsingleton (Ext T.X₃ Y (i + 1))) : Subsingleton (Ext T.X₁ Y i) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hT Y x (add_comm 1 (j + 1))
    (Subsingleton.eq_zero _)
  rw [← hy, Ext.eq_zero_of_projective y, Ext.comp_zero]

/-- The finite-projective-dimension case of the conjecture over a local ring. -/
theorem projective_of_finite_projective_dimension [IsLocalRing R] (X : ModuleCat.{u} R)
    [Module.Finite R X] (n : ℕ) (hd : HasProjectiveDimensionLE X n)
    (h : ∀ i > 0, Subsingleton (Ext X (ModuleCat.of R R) i)) : Module.Projective R X := by
  induction n generalizing X with
  | zero => exact (IsProjective.iff_projective _).mpr (projective_iff_hasProjectiveDimensionLT_one.mpr hd)
  | succ n ih =>
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R X
    let T := f.shortComplexKer
    have hT : T.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have hdK : HasProjectiveDimensionLE T.X₁ n := (hT.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hd
    have := ih T.X₁ hdK (fun i hi => ext_syzygy T hT _ i hi (h _ (Nat.succ_pos _)))
    have : Module.Free R T.X₁ := Module.free_of_flat_of_isLocalRing
    exact projective_of_ext_kernel T hT (subsingleton_ext_finite_free X T.X₁ 1 (h 1 Nat.one_pos))

/-- Applying the ring dual reverses a short complex. -/
private abbrev dualComplex (T : ShortComplex (ModuleCat.{u} R)) :=
  ModuleCat.shortComplexOfCompEqZero T.g.hom.dualMap T.f.hom.dualMap (by
    ext φ x
    change φ (T.g (T.f x)) = 0
    simp)

omit [IsNoetherianRing R] in
private theorem dual_surj (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    (h : Subsingleton (Ext T.X₃ (ModuleCat.of R R) 1)) :
    Function.Surjective T.f.hom.dualMap := by
  intro φ
  obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₁ hT (ModuleCat.of R R)
    (Ext.mk₀ (ModuleCat.ofHom φ)) (add_zero 1) (Subsingleton.eq_zero _)
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective a
  rw [Ext.mk₀_comp_mk₀, (Ext.mk₀_bijective _ _).injective.eq_iff] at ha
  exact ⟨g.hom, ModuleCat.hom_ext_iff.mp ha⟩

omit [IsNoetherianRing R] in
private theorem dual_shortExact (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    (h : Subsingleton (Ext T.X₃ (ModuleCat.of R R) 1)) : (dualComplex T).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro φ
    constructor
    · intro hφ
      have hz : (Ext.mk₀ T.f).comp (Ext.mk₀ (ModuleCat.ofHom φ : T.X₂ ⟶ ModuleCat.of R R))
          (zero_add 0) = 0 := by
        rw [Ext.mk₀_comp_mk₀, ← Ext.mk₀_zero]
        exact congrArg Ext.mk₀ (ModuleCat.hom_ext hφ)
      obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₂ hT _ _ hz
      obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective b
      rw [Ext.mk₀_comp_mk₀, (Ext.mk₀_bijective _ _).injective.eq_iff] at hb
      exact ⟨g.hom, ModuleCat.hom_ext_iff.mp hb⟩
    · rintro ⟨ψ, rfl⟩
      exact (dualComplex T).moduleCat_zero_apply ψ
  · exact LinearMap.dualMap_injective_of_surjective hT.moduleCat_surjective_g
  · exact dual_surj T hT h

omit [IsNoetherianRing R] in
private theorem syzygy_eval_injective (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    [Module.IsReflexive R T.X₂] : Function.Injective (Module.Dual.eval R T.X₁) := by
  intro x y hxy
  apply hT.moduleCat_injective_f
  apply (Module.bijective_dual_eval R T.X₂).injective
  ext φ
  exact LinearMap.congr_fun hxy (T.f.hom.dualMap φ)

omit [IsNoetherianRing R] in
private theorem syzygy_reflexive (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    [Module.IsReflexive R T.X₂] (hX : Function.Injective (Module.Dual.eval R T.X₃))
    (h : Subsingleton (Ext T.X₃ (ModuleCat.of R R) 1)) : Module.IsReflexive R T.X₁ := by
  refine ⟨syzygy_eval_injective T hT, ?_⟩
  intro Φ
  obtain ⟨p, hp⟩ := (Module.bijective_dual_eval R T.X₂).surjective (T.f.hom.dualMap.dualMap Φ)
  have hp0 : T.g p = 0 := by
    apply hX
    ext φ
    have hz : T.f.hom.dualMap (T.g.hom.dualMap φ) = 0 := by
      ext x
      change φ (T.g (T.f x)) = 0
      simp
    have he := LinearMap.congr_fun hp (T.g.hom.dualMap φ)
    change φ (T.g p) = Φ (T.f.hom.dualMap (T.g.hom.dualMap φ)) at he
    simpa [hz] using he
  obtain ⟨k, hk⟩ := T.moduleCat_exact_iff.mp hT.exact p hp0
  refine ⟨k, ?_⟩
  ext φ
  obtain ⟨ψ, rfl⟩ := dual_surj T hT h φ
  change ψ (T.f k) = Φ (T.f.hom.dualMap ψ)
  rw [hk]
  exact LinearMap.congr_fun hp ψ

omit [IsNoetherianRing R] in
private theorem ext_one_of_dual_surj (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    [Projective T.X₂] (h : Function.Surjective T.f.hom.dualMap) :
    Subsingleton (Ext T.X₃ (ModuleCat.of R R) 1) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨b, hb⟩ := precomp_extClass_surjective_of_projective_X₂ (ModuleCat.of R R) hT 0 x
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).surjective b
  obtain ⟨ψ, hψ⟩ := h φ.hom
  have eqφ : (T.f ≫ (ModuleCat.ofHom ψ : T.X₂ ⟶ ModuleCat.of R R)) = φ := ModuleCat.hom_ext hψ
  rw [← eqφ, ← Ext.mk₀_comp_mk₀] at hb
  change hT.extClass.comp _ (add_zero 1) = x at hb
  rw [← hb, hT.extClass_comp_assoc]

omit [IsNoetherianRing R] in
/-- The vanishing implication for one syzygy in Kimura's Lemma 2.6. -/
theorem self_ext_syzygy [Nontrivial R] (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    [Module.Finite R T.X₂] [Module.Free R T.X₂] (i : ℕ) (hi : 0 < i)
    (hR : Subsingleton (Ext T.X₃ (ModuleCat.of R R) (i + 1)))
    (hX : Subsingleton (Ext T.X₃ T.X₃ i)) : Subsingleton (Ext T.X₁ T.X₁ i) := by
  have := subsingleton_ext_finite_free T.X₃ T.X₂ (i + 1) hR
  apply ext_syzygy T hT T.X₁ i hi
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ T.X₃ hT x (Subsingleton.eq_zero _) rfl
  rw [← hy, Subsingleton.eq_zero y, Ext.zero_comp]

private abbrev ringDual (X : ModuleCat.{u} R) := ModuleCat.of R (Module.Dual R X)

omit [IsNoetherianRing R] in
private theorem dual_ext_bound (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    [Nontrivial R] [Module.Finite R T.X₂] [Module.Free R T.X₂] [Module.IsReflexive R T.X₃]
    (h : Subsingleton (Ext T.X₃ (ModuleCat.of R R) 1)) (n : ℕ)
    (hd : ∀ i > 0, i ≤ n → Subsingleton (Ext (ringDual T.X₃) (ModuleCat.of R R) i)) :
    ∀ i > 0, i ≤ n + 1 → Subsingleton (Ext (ringDual T.X₁) (ModuleCat.of R R) i) := by
  let D := dualComplex T
  have hD : D.ShortExact := dual_shortExact T hT h
  have : Projective D.X₂ := inferInstanceAs (Projective (ModuleCat.of R (Module.Dual R T.X₂)))
  intro i hi hin
  cases i with
  | zero => cases hi
  | succ j =>
    cases j with
    | zero =>
      apply ext_one_of_dual_surj D hD
      intro Φ
      obtain ⟨x, rfl⟩ := (Module.bijective_dual_eval R T.X₃).surjective Φ
      obtain ⟨p, rfl⟩ := hT.moduleCat_surjective_g x
      exact ⟨Module.Dual.eval R T.X₂ p, rfl⟩
    | succ j =>
      have := hd (j + 1) (Nat.succ_pos _) (Nat.le_of_succ_le_succ hin)
      apply subsingleton_of_forall_eq 0
      intro x
      obtain ⟨b, hb⟩ := precomp_extClass_surjective_of_projective_X₂ (ModuleCat.of R R) hD (j + 1) x
      change hD.extClass.comp b (add_comm 1 (j + 1)) = x at hb
      rw [← hb, Subsingleton.eq_zero b, Ext.comp_zero]

omit [IsNoetherianRing R] in
/-- Freeness on the punctured spectrum is inherited by kernels of finite free presentations. -/
private theorem localized_syzygy_free (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    [Module.Finite R T.X₁] [Projective T.X₂] (p : PrimeSpectrum R)
    (h : Module.Free (Localization.AtPrime p.asIdeal) (T.X₃.localizedModule p.asIdeal.primeCompl)) :
    Module.Free (Localization.AtPrime p.asIdeal) (T.X₁.localizedModule p.asIdeal.primeCompl) := by
  let F := ModuleCat.localizedModuleFunctor.{u} p.asIdeal.primeCompl
  let U := T.map F
  have hU : U.ShortExact := hT.map_of_exact F
  have : Projective U.X₃ := inferInstanceAs (Projective (T.X₃.localizedModule p.asIdeal.primeCompl))
  have : Projective U.X₂ := F.projective_obj_of_projective (inferInstance : Projective T.X₂)
  let sp := hU.splittingOfProjective
  have : Module.Projective (Localization.AtPrime p.asIdeal) (T.X₁.localizedModule p.asIdeal.primeCompl) :=
    (IsProjective.iff_projective _).mpr (Retract.mk U.f sp.r sp.f_r).projective
  have : Module.Finite (Localization.AtPrime p.asIdeal) (T.X₁.localizedModule p.asIdeal.primeCompl) :=
    Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
      (T.X₁.localizedModuleMkLinearMap p.asIdeal.primeCompl)
  exact Module.free_of_flat_of_isLocalRing


/-- Normal local domains of dimension at most one are PIDs (including the field case). -/
theorem projective_of_low_dimension [IsLocalRing R] [IsDomain R] [IsIntegrallyClosed R]
    (X : ModuleCat.{u} R) [Module.Finite R X] (hd : ringKrullDim R ≤ 1)
    (h : Subsingleton (Ext X (ModuleCat.of R R) 1)) : Module.Projective R X := by
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simpa using hd)
  have : Ring.DimensionLEOne R := ⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩
  have : IsDedekindDomain R := { }
  exact projective_of_ext_one_pid X h

/-- A finite module over a Noetherian ring is projective if its maximal stalks are projective. -/
private theorem projective_of_stalks (X : ModuleCat.{u} R) [Module.Finite R X]
    (h : ∀ p : MaximalSpectrum R, Module.Projective (Localization.AtPrime p.asIdeal)
      (X.localizedModule p.asIdeal.primeCompl)) : Module.Projective R X := by
  apply (IsProjective.iff_projective _).mpr
  apply projective_iff_hasProjectiveDimensionLT_one.mpr
  apply (X.hasProjectiveDimensionLE_iff_forall_maximalSpectrum 0).mpr
  intro p
  exact projective_iff_hasProjectiveDimensionLT_one.mp ((IsProjective.iff_projective _).mp (h p))

/-- The unconditional normal-domain case in dimension at most one. Only first Ext against
the ring is needed, including when the global ring has nonprincipal ideals. -/
theorem projective_of_dimension_le_one [IsDomain R] [IsIntegrallyClosed R]
    (X : ModuleCat.{u} R) [Module.Finite R X] (hd : ringKrullDim R ≤ 1)
    (h : Subsingleton (Ext X (ModuleCat.of R R) 1)) : Module.Projective R X := by
  apply projective_of_stalks X
  intro p
  let B := Localization.AtPrime p.asIdeal
  have : IsIntegrallyClosed B := isIntegrallyClosed_of_isLocalization B _
    p.asIdeal.primeCompl_le_nonZeroDivisors
  have : Module.Finite B (X.localizedModule p.asIdeal.primeCompl) :=
    Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl (X.localizedModuleMkLinearMap _)
  apply projective_of_low_dimension (R := B)
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal B]
    exact (Ideal.height_le_ringKrullDim_of_ne_top p.isMaximal.ne_top).trans hd
  · exact subsingleton_ext_localized_ring _ X 1 h


/-- The local case left by the reduction: an infinite-projective-dimension module locally free on
the punctured spectrum, over a normal local domain of dimension greater than one. -/
def PuncturedCase : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] (X : ModuleCat.{u} A) [Module.Finite A X],
    1 < ringKrullDim A →
    (∀ n : ℕ, ¬ HasProjectiveDimensionLE X n) →
    (∀ p : PrimeSpectrum A, p.asIdeal ≠ IsLocalRing.maximalIdeal A →
      Module.Free (Localization.AtPrime p.asIdeal) (X.localizedModule p.asIdeal.primeCompl)) →
    (∀ i > 0, Subsingleton (Ext X (ModuleCat.of A A) i)) →
    (∀ i > 0, Subsingleton (Ext X X i)) → False

/-- Locally free at every prime other than the maximal ideal. -/
abbrev PuncturedFree {A : Type u} [CommRing A] [IsLocalRing A] (X : ModuleCat.{u} A) :=
  ∀ p : PrimeSpectrum A, p.asIdeal ≠ IsLocalRing.maximalIdeal A →
    Module.Free (Localization.AtPrime p.asIdeal) (X.localizedModule p.asIdeal.primeCompl)

omit [IsNoetherianRing R] in
open IsLocalRing in
private theorem maximal_height_gt_one [IsLocalRing R] (hd : 1 < ringKrullDim R) :
    1 < (maximalIdeal R).height := by
  apply WithBot.coe_lt_coe.mp
  simpa only [maximalIdeal_height_eq_ringKrullDim, WithBot.coe_one] using hd

omit [IsNoetherianRing R] in
open IsLocalRing in
private theorem exists_nonzero_maximal [IsLocalRing R] [IsDomain R] (hd : 1 < ringKrullDim R) :
    ∃ a : maximalIdeal R, a.val ≠ 0 := by
  have hh := maximal_height_gt_one hd
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).mp
    (show maximalIdeal R ≠ ⊥ by
      intro he
      have := Ideal.height_eq_zero_iff_eq_bot.mpr he
      rw [this] at hh
      exact (not_lt_of_ge zero_le_one) hh)
  exact ⟨⟨a, ha⟩, ha0⟩

omit [IsNoetherianRing R] in
private theorem dual_ideal_relation (I : Ideal R) (φ : Module.Dual R I) (a b : I) :
    φ a * (b : R) = φ b * (a : R) := by
  have h : (b : R) • a = (a : R) • b := Subtype.ext (mul_comm _ _)
  simpa [smul_eq_mul, mul_comm] using congrArg φ h

open IsLocalRing in
/-- In a normal local domain of dimension at least two, every functional on the maximal
ideal is multiplication by a scalar. -/
theorem maximalIdeal_dual_extends [IsLocalRing R] [IsDomain R] [IsIntegrallyClosed R]
    (hd : 1 < ringKrullDim R) (φ : Module.Dual R (maximalIdeal R)) :
    ∃ c : R, ∀ y : maximalIdeal R, φ y = c * y.val := by
  let m := maximalIdeal R
  have hφ : ∀ y : m, φ y ∈ m := by
    intro y
    by_contra hy
    have hyu : IsUnit (φ y) := not_not.mp hy
    have hey : m = Ideal.span {y.val} := by
      apply le_antisymm _ (m.span_singleton_le_iff_mem.mpr y.property)
      intro a ha
      apply (Ideal.unit_mul_mem_iff_mem _ hyu).mp
      rw [dual_ideal_relation m φ y ⟨a, ha⟩]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    have hle : m.height ≤ 1 := by
      rw [hey]
      exact Ideal.height_span_singleton_le_one y.property
    exact (not_lt_of_ge hle) (maximal_height_gt_one hd)
  obtain ⟨a, ha⟩ := exists_nonzero_maximal hd
  let F := FractionRing R
  let j := algebraMap R F
  let z := j (φ a) / j a.val
  have ha' : j a.val ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha
  have hz (y : m) : z * j y.val = j (φ y) := by
    change j (φ a) / j a.val * j y.val = j (φ y)
    rw [div_mul_eq_mul_div, div_eq_iff ha', ← map_mul, ← map_mul, dual_ideal_relation]
  let L := Submodule.map (Algebra.linearMap R F) m
  have hi : IsIntegral R z := by
    apply isIntegral_of_smul_mem_submodule L
    · exact (Submodule.ne_bot_iff _).mpr ⟨j a.val, ⟨a.val, a.property, rfl⟩, ha'⟩
    · exact (IsNoetherian.noetherian m).map _
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨φ ⟨y, hy⟩, hφ ⟨y, hy⟩, (hz ⟨y, hy⟩).symm⟩
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
  refine ⟨c, fun y => (IsFractionRing.injective R F) ?_⟩
  rw [map_mul, hc]
  exact (hz y).symm

open IsLocalRing in
private theorem residue_ext_small [IsLocalRing R] [IsDomain R] [IsIntegrallyClosed R]
    (hd : 1 < ringKrullDim R) (i : ℕ) (hi : i < 2) :
    Subsingleton (Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) i) := by
  let m := maximalIdeal R
  interval_cases i
  · apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
    rw [← Ext.mk₀_zero]
    apply congrArg Ext.mk₀
    obtain ⟨a, ha⟩ := exists_nonzero_maximal hd
    ext y
    have h : a.val • y = 0 := by
      rw [Algebra.smul_def, ResidueField.algebraMap_eq, (residue_eq_zero_iff _).mpr a.property, zero_mul]
    have he := congrArg f.hom h
    simpa [smul_eq_mul, ha] using he
  · let T := ModuleCat.shortComplexOfCompEqZero m.subtype m.mkQ (LinearMap.exact_subtype_mkQ m).linearMap_comp_eq_zero
    have hT := ModuleCat.shortComplex_shortExact T (LinearMap.exact_subtype_mkQ m) m.injective_subtype m.mkQ_surjective
    apply ext_one_of_dual_surj T hT
    intro φ
    obtain ⟨c, hc⟩ := maximalIdeal_dual_extends hd φ
    exact ⟨c • LinearMap.id, LinearMap.ext fun y => (hc y).symm⟩


/-- The Ext characterization of the depth of a nonzero Noetherian local ring. -/
def HasDepth (A : Type u) [CommRing A] [IsLocalRing A] (t : ℕ) : Prop :=
  let k := ModuleCat.of A (IsLocalRing.ResidueField A)
  let A' := ModuleCat.of A A
  (∀ i < t, Subsingleton (Ext k A' i)) ∧ ¬ Subsingleton (Ext k A' t)

open IsLocalRing in
private theorem exists_depth [IsLocalRing R] : ∃ t, HasDepth R t := by
  classical
  let m := maximalIdeal R
  let k := ModuleCat.of R (ResidueField R)
  let A := ModuleCat.of R R
  have h : ∃ t : ℕ, ¬ Subsingleton (Ext k A t) := by
    by_contra! hz
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top_of_isPrime (I := m))
    have hdim : ringKrullDim R = d := by
      rw [← maximalIdeal_height_eq_ringKrullDim]
      exact congrArg (fun a : ℕ∞ => (a : WithBot ℕ∞)) hd.symm
    have hlt : m • (⊤ : Ideal R) < ⊤ := by simpa using (maximalIdeal.isMaximal R).lt_top
    have H := ModuleCat.exists_isRegular_tfae m (d + 1) A hlt
    have hsh (i : ℕ) : Subsingleton (Ext (ModuleCat.of R (Shrink.{u} (R ⧸ m))) A i) := by
      let e := (Shrink.linearEquiv.{u} R (R ⧸ m)).toModuleIso
      let E := ((extFunctor (C := ModuleCat.{u} R) i).mapIso e.op).app A
      exact E.addCommGroupIsoToAddEquiv.subsingleton_congr.mp (hz i)
    obtain ⟨rs, hlen, hmem, hreg⟩ := (H.out 1 3).mp (fun i _ => hsh i)
    have hr : RingTheory.Sequence.IsRegular R rs := hreg
    have : Nontrivial (R ⧸ Ideal.ofList rs) := Ideal.Quotient.nontrivial_iff.mpr (by
      intro htop
      apply hr.top_ne_smul
      simp [htop])
    have hle : (rs.length : WithBot ℕ∞) ≤ ringKrullDim R := by
      rw [← ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hr]
      simpa only [zero_add] using add_le_add_left
        (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ Ideal.ofList rs)) (rs.length : WithBot ℕ∞)
    rw [hlen, hdim] at hle
    exact (Nat.not_succ_le_self d) (by exact_mod_cast hle)
  exact ⟨Nat.find h, fun i hi => not_not.mp (Nat.find_min h hi), Nat.find_spec h⟩

/-- A normal Noetherian local domain of dimension greater than one has depth at least two. -/
theorem exists_depth_ge_two [IsLocalRing R] [IsDomain R] [IsIntegrallyClosed R]
    (hd : 1 < ringKrullDim R) : ∃ t : ℕ, 2 ≤ t ∧ HasDepth R t := by
  obtain ⟨t, ht⟩ := exists_depth (R := R)
  exact ⟨t, le_of_not_gt (fun h => ht.2 (residue_ext_small hd t h)), ht⟩

private structure Counterexample [IsLocalRing R] (X : ModuleCat.{u} R) : Prop where
  infiniteDimension : ∀ n : ℕ, ¬ HasProjectiveDimensionLE X n
  puncturedFree : PuncturedFree X
  ringExt : ∀ i > 0, Subsingleton (Ext X (ModuleCat.of R R) i)
  selfExt : ∀ i > 0, Subsingleton (Ext X X i)

omit [IsNoetherianRing R] in
private theorem counterexample_syzygy [IsLocalRing R] (T : ShortComplex (ModuleCat.{u} R))
    (hT : T.ShortExact) [Module.Finite R T.X₁] [Module.Finite R T.X₂] [Module.Free R T.X₂]
    (hX : Counterexample T.X₃) : Counterexample T.X₁ where
  infiniteDimension n hk := hX.infiniteDimension (n + 1)
    ((hT.hasProjectiveDimensionLT_X₃_iff n inferInstance).mpr hk)
  puncturedFree p hp := localized_syzygy_free T hT p (hX.puncturedFree p hp)
  ringExt i hi := ext_syzygy T hT _ i hi (hX.ringExt _ (Nat.succ_pos _))
  selfExt i hi := self_ext_syzygy T hT i hi (hX.ringExt _ (Nat.succ_pos _)) (hX.selfExt i hi)

private theorem exists_reflexive_syzygy [IsLocalRing R] (X : ModuleCat.{u} R) [Module.Finite R X]
    (hX : Counterexample X) (n : ℕ) :
    ∃ (K : ModuleCat.{u} R) (_ : Module.Finite R K) (_ : Module.IsReflexive R K),
      Counterexample K ∧
      ∀ i > 0, i ≤ n → Subsingleton (Ext (ringDual K) (ModuleCat.of R R) i) := by
  induction n with
  | zero =>
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R X
    let T := f.shortComplexKer
    have hT : T.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have hK := counterexample_syzygy T hT hX
    obtain ⟨Q, _, _, _, _, g, hg⟩ := Module.exists_finite_presentation R T.X₁
    let U := g.shortComplexKer
    have hU : U.ShortExact := LinearMap.shortExact_shortComplexKer hg
    exact ⟨U.X₁, inferInstance, syzygy_reflexive U hU (syzygy_eval_injective T hT)
      (hK.ringExt 1 Nat.one_pos), counterexample_syzygy U hU hK, fun i hi hi0 => by omega⟩
  | succ n ih =>
    obtain ⟨K, _, _, hK, hd⟩ := ih
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R K
    let T := f.shortComplexKer
    have hT : T.ShortExact := LinearMap.shortExact_shortComplexKer hf
    exact ⟨T.X₁, inferInstance, syzygy_reflexive T hT (Module.bijective_dual_eval R K).injective
      (hK.ringExt 1 Nat.one_pos), counterexample_syzygy T hT hK,
      dual_ext_bound T hT (hK.ringExt 1 Nat.one_pos) n hd⟩

private theorem dual_punctured_free [IsLocalRing R] (X : ModuleCat.{u} R) [Module.Finite R X]
    (hX : PuncturedFree X) : PuncturedFree (ringDual X) := by
  intro p hp
  let S := p.asIdeal.primeCompl
  let B := Localization S
  let Xp := X.localizedModule S
  have : Module.FinitePresentation R X := Module.finitePresentation_of_finite R X
  have : Module.Finite B Xp := Module.Finite.of_isLocalizedModule S (X.localizedModuleMkLinearMap S)
  have : Module.Free B Xp := hX p hp
  let l := IsLocalizedModule.mapExtendScalars S (X.localizedModuleMkLinearMap S)
    (Algebra.linearMap R B) B
  let K := ringDual X
  have : IsLocalizedModule S (K.localizedModuleMkLinearMap S) := ModuleCat.localizedModule_isLocalizedModule _ _
  let e := (IsLocalizedModule.linearEquiv S l (K.localizedModuleMkLinearMap S)).extendScalarsOfIsLocalization S B
  exact Module.Free.of_equiv e

private def LocalCaseAtHeight (n : ℕ) : Prop :=
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
      [IsIntegrallyClosed A] (X : ModuleCat.{u} A) [Module.Finite A X],
      (IsLocalRing.maximalIdeal A).height = n →
      (∀ i > 0, Subsingleton (Ext X (ModuleCat.of A A) i)) →
      (∀ i > 0, Subsingleton (Ext X X i)) → Module.Projective A X

private theorem local_aux (core : PuncturedCase.{u}) (n : ℕ) : LocalCaseAtHeight.{u} n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A _ _ _ _ _ X _ hn hR hX
    by_cases hlow : ringKrullDim A ≤ 1
    · exact projective_of_low_dimension X hlow (hR 1 Nat.one_pos)
    by_cases hfin : ∃ k, HasProjectiveDimensionLE X k
    · obtain ⟨k, hk⟩ := hfin
      exact projective_of_finite_projective_dimension X k hk hR
    apply False.elim
    apply core A X (lt_of_not_ge hlow) (fun k hk => hfin ⟨k, hk⟩) _ hR hX
    intro p hp
    let B := Localization.AtPrime p.asIdeal
    have : IsIntegrallyClosed B := isIntegrallyClosed_of_isLocalization B _ p.asIdeal.primeCompl_le_nonZeroDivisors
    let Y := X.localizedModule p.asIdeal.primeCompl
    have : Module.Finite B Y := Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
      (X.localizedModuleMkLinearMap p.asIdeal.primeCompl)
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top_of_isPrime (I := p.asIdeal))
    have hklt : k < n := by
      have hlt := Ideal.height_strict_mono_of_isPrime
        ((IsLocalRing.le_maximalIdeal_of_isPrime p.asIdeal).lt_of_ne hp)
      exact_mod_cast (show (k : ℕ∞) < n by simpa only [← hk, hn] using hlt)
    have hdim : (IsLocalRing.maximalIdeal B).height = k := by
      apply WithBot.coe_injective
      rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
        IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal B, hk]
    have : Module.Projective B Y := ih k hklt B Y hdim
      (fun i hi => subsingleton_ext_localized_ring _ X i (hR i hi))
      (fun i hi => subsingleton_ext_localized _ X X i (hX i hi))
    exact Module.free_of_flat_of_isLocalRing

end OMA.AuslanderReitenReduction

namespace OMA.AuslanderReitenReduction

section Divisible

variable {R : Type u} [CommRing R]

/-- Multiplication by `x` on `C` has a linear right inverse. -/
def SMulSection (x : R) (C : Type u) [AddCommGroup C] [Module R C] : Prop :=
  ∃ ψ : C →ₗ[R] C, ∀ z, x • ψ z = z

/-- A class killed by a power of `x` vanishes when `x` is invertible on the target. -/
theorem ext_eq_zero_of_smulSection {Y L : ModuleCat.{u} R} {j : ℕ} (x : R)
    (hd : SMulSection x L) (n : ℕ) (ξ : Ext Y L j) (hx : x ^ n • ξ = 0) : ξ = 0 := by
  obtain ⟨ψ, hψ⟩ := hd
  have key : ∀ ζ : Ext Y L j, (x • ζ).comp (Ext.mk₀ (ModuleCat.ofHom ψ)) (add_zero j) = ζ := by
    intro ζ
    have h1 : x • ModuleCat.ofHom ψ = 𝟙 L := by
      ext z
      exact hψ z
    rw [Ext.smul_comp, ← Ext.comp_smul, ← Ext.mk₀_smul, h1, Ext.comp_mk₀_id]
  induction n generalizing ξ with
  | zero => simpa using hx
  | succ n ih =>
    have := ih (x • ξ) (by rw [smul_smul, ← pow_succ]; exact hx)
    rw [← key ξ, this, Ext.zero_comp]

/-- Ext vanishes when `x` kills the source and is invertible on the target. -/
theorem subsingleton_ext_of_smul_eq_zero (Q L : ModuleCat.{u} R) (x : R)
    (hQ : ∀ q : Q, x • q = 0) (hd : SMulSection x L) (j : ℕ) : Subsingleton (Ext Q L j) := by
  apply subsingleton_of_forall_eq 0
  intro ξ
  apply ext_eq_zero_of_smulSection x hd 1
  have h0 : x • 𝟙 Q = 0 := by
    ext q
    exact hQ q
  rw [pow_one, ← Ext.mk₀_id_comp ξ, ← Ext.smul_comp, ← Ext.mk₀_smul, h0, Ext.mk₀_zero,
    Ext.zero_comp]

/-- A scalar whose multiplication on `T.X₃` lifts to `T.X₂` kills the extension class. -/
theorem smul_extClass_eq_zero (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact) (r : R)
    (a : T.X₃ ⟶ T.X₂) (ha : (a ≫ T.g) = r • 𝟙 T.X₃) : r • hT.extClass = 0 := by
  rw [← Ext.mk₀_id_comp hT.extClass, ← Ext.smul_comp, ← Ext.mk₀_smul, ← ha,
    ← Ext.mk₀_comp_mk₀_assoc, hT.comp_extClass, Ext.comp_zero]

/-- Positive Ext out of `T.X₃` vanishes against modules on which `x` is invertible. -/
theorem subsingleton_ext_succ_of_torsion (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    [Projective T.X₂] (x : R) (n : ℕ) (h : x ^ n • hT.extClass = 0) (L : ModuleCat.{u} R)
    (hd : SMulSection x L) (j : ℕ) : Subsingleton (Ext T.X₃ L (j + 1)) := by
  apply subsingleton_of_forall_eq 0
  intro ξ
  obtain ⟨b, hb⟩ := precomp_extClass_surjective_of_projective_X₂ L hT j ξ
  change hT.extClass.comp b (add_comm 1 j) = ξ at hb
  apply ext_eq_zero_of_smulSection x hd n
  rw [← hb, ← Ext.smul_comp, h, Ext.zero_comp]

/-- Dimension shifting in the second variable, towards the cokernel. -/
theorem subsingleton_ext_X₃ (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (Y : ModuleCat.{u} R) (j : ℕ) (h₂ : Subsingleton (Ext Y S.X₂ j))
    (h₁ : Subsingleton (Ext Y S.X₁ (j + 1))) : Subsingleton (Ext Y S.X₃ j) := by
  apply subsingleton_of_forall_eq 0
  intro ξ
  obtain ⟨ζ, hζ⟩ := Ext.covariant_sequence_exact₃ Y hS ξ rfl (Subsingleton.eq_zero _)
  rw [← hζ, Subsingleton.eq_zero ζ, Ext.zero_comp]

/-- Dimension shifting in the second variable, towards the kernel. -/
theorem subsingleton_ext_X₁ (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (Y : ModuleCat.{u} R) (j : ℕ) (h₂ : Subsingleton (Ext Y S.X₂ (j + 1)))
    (h₃ : Subsingleton (Ext Y S.X₃ j)) : Subsingleton (Ext Y S.X₁ (j + 1)) := by
  apply subsingleton_of_forall_eq 0
  intro ξ
  obtain ⟨ζ, hζ⟩ := Ext.covariant_sequence_exact₁ Y hS ξ (Subsingleton.eq_zero _) rfl
  rw [← hζ, Subsingleton.eq_zero ζ, Ext.zero_comp]

end Divisible

section Localization

variable {R : Type u} [CommRing R]

/-- The complex `Z → Z[1/x] → Z[1/x]/Z`. -/
noncomputable def locComplex (Z : ModuleCat.{u} R) (x : R) : ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero (LocalizedModule.mkLinearMap (Submonoid.powers x) Z)
    (LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers x) Z)).mkQ
    (LinearMap.exact_map_mkQ_range _).linearMap_comp_eq_zero

/-- The localization complex is short exact when `x` is regular on `Z`. -/
theorem locComplex_shortExact (Z : ModuleCat.{u} R) (x : R) (hx : IsSMulRegular Z x) :
    (locComplex Z x).ShortExact := by
  have hinj : Function.Injective (LocalizedModule.mkLinearMap (Submonoid.powers x) Z) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers x) _).mp hz
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    apply hx.pow n
    change x ^ n • z = x ^ n • 0
    rw [smul_zero, hn]
    exact hs
  exact ModuleCat.shortComplex_shortExact _ (LinearMap.exact_map_mkQ_range _) hinj
    (Submodule.mkQ_surjective _)

/-- Multiplication by `x` is invertible on the localization at the powers of `x`. -/
theorem smulSection_localizedModule (Z : Type u) [AddCommGroup Z] [Module R Z] (x : R) :
    SMulSection x (LocalizedModule (Submonoid.powers x) Z) := by
  have hu := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers x) Z)
    ⟨x, Submonoid.mem_powers x⟩
  refine ⟨((hu.unit⁻¹ : (Module.End R (LocalizedModule (Submonoid.powers x) Z))ˣ) :
    Module.End R (LocalizedModule (Submonoid.powers x) Z)), fun z => ?_⟩
  exact LinearMap.congr_fun hu.mul_val_inv z

/-- The middle term of the localization complex is `x`-divisible. -/
theorem smulSection_locComplex (Z : ModuleCat.{u} R) (x : R) : SMulSection x (locComplex Z x).X₂ :=
  smulSection_localizedModule Z x

/-- Every element of `Z[1/x]/Z` is killed by a power of `x`. -/
theorem locComplex_torsion_self (Z : ModuleCat.{u} R) (x : R) (w : (locComplex Z x).X₃) :
    ∃ n : ℕ, x ^ n • w = 0 := by
  let f := LocalizedModule.mkLinearMap (Submonoid.powers x) Z
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range f) w
  obtain ⟨⟨z, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers x) f c
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  refine ⟨n, ?_⟩
  have h1 : (LinearMap.range f).mkQ (x ^ n • c) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨z, ?_⟩
    rw [hn]
    exact hs.symm
  exact (map_smul (LinearMap.range f).mkQ (x ^ n) c).symm.trans h1

/-- Power torsion with respect to another element passes from `Z` to `Z[1/x]/Z`. -/
theorem locComplex_torsion (Z : ModuleCat.{u} R) (x y : R)
    (hy : ∀ z : Z, ∃ n : ℕ, y ^ n • z = 0) (w : (locComplex Z x).X₃) :
    ∃ n : ℕ, y ^ n • w = 0 := by
  let f := LocalizedModule.mkLinearMap (Submonoid.powers x) Z
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range f) w
  obtain ⟨⟨z, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers x) f c
  obtain ⟨n, hn⟩ := hy z
  refine ⟨n, ?_⟩
  have hc : y ^ n • c = 0 := by
    apply IsLocalizedModule.smul_injective f s
    change s • y ^ n • c = s • (0 : LocalizedModule (Submonoid.powers x) Z)
    rw [smul_zero, smul_comm, hs, ← map_smul, hn, map_zero]
  have h1 : (LinearMap.range f).mkQ (y ^ n • c) = 0 := by rw [hc, map_zero]
  exact (map_smul (LinearMap.range f).mkQ (y ^ n) c).symm.trans h1

end Localization

section HomComplex

variable {R : Type u} [CommRing R]

/-- Apply `Hom(P, -)` to a short complex. -/
noncomputable def homComplex (P : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero
    (LinearMap.compRight R S.f.hom : (P →ₗ[R] S.X₁) →ₗ[R] (P →ₗ[R] S.X₂))
    (LinearMap.compRight R S.g.hom : (P →ₗ[R] S.X₂) →ₗ[R] (P →ₗ[R] S.X₃)) (by
      ext φ p
      change S.g (S.f (φ p)) = 0
      simp)

/-- `Hom(P, -)` keeps a short exact sequence exact when `Ext¹(P, -)` vanishes on the kernel. -/
theorem homComplex_shortExact (P : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (h : Subsingleton (Ext P S.X₁ 1)) : (homComplex P S).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro φ
    constructor
    · intro hφ
      have hz : (Ext.mk₀ (ModuleCat.ofHom φ : P ⟶ S.X₂)).comp (Ext.mk₀ S.g) (add_zero 0) = 0 := by
        rw [Ext.mk₀_comp_mk₀, ← Ext.mk₀_zero]
        exact congrArg Ext.mk₀ (ModuleCat.hom_ext hφ)
      obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₂ P hS _ hz
      obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective b
      rw [Ext.mk₀_comp_mk₀, (Ext.mk₀_bijective _ _).injective.eq_iff] at hb
      exact ⟨g.hom, ModuleCat.hom_ext_iff.mp hb⟩
    · rintro ⟨ψ, rfl⟩
      exact (homComplex P S).moduleCat_zero_apply ψ
  · intro φ ψ hφψ
    apply LinearMap.ext
    intro p
    exact hS.moduleCat_injective_f (LinearMap.congr_fun hφψ p)
  · intro φ
    obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃ P hS (Ext.mk₀ (ModuleCat.ofHom φ))
      (zero_add 1) (Subsingleton.eq_zero _)
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective a
    rw [Ext.mk₀_comp_mk₀, (Ext.mk₀_bijective _ _).injective.eq_iff] at ha
    exact ⟨g.hom, ModuleCat.hom_ext_iff.mp ha⟩

/-- Divisibility of the target passes to the module of homomorphisms. -/
theorem smulSection_hom (P : Type u) [AddCommGroup P] [Module R P] (x : R) (C : Type u)
    [AddCommGroup C] [Module R C] (hd : SMulSection x C) : SMulSection x (P →ₗ[R] C) := by
  obtain ⟨ψ, hψ⟩ := hd
  exact ⟨LinearMap.compRight R ψ, fun φ => LinearMap.ext fun p => hψ (φ p)⟩

end HomComplex

section Lift

variable {R : Type u} [CommRing R]

/-- Scalars whose multiplication on `T.X₃` lifts through `T.g`. -/
def liftIdeal (T : ShortComplex (ModuleCat.{u} R)) : Ideal R where
  carrier := {r | ∃ a : T.X₃ →ₗ[R] T.X₂, T.g.hom ∘ₗ a = r • LinearMap.id}
  add_mem' := by
    rintro r s ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [LinearMap.comp_add, ha, hb, add_smul]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c r ⟨a, ha⟩
    exact ⟨c • a, by rw [LinearMap.comp_smul, ha, smul_smul, smul_eq_mul]⟩

variable [IsNoetherianRing R]

open IsLocalRing in
/-- Away from the maximal ideal the localized surjection splits, so some scalar outside the
prime lifts. -/
theorem liftIdeal_not_le [IsLocalRing R] (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    [Module.Finite R T.X₃] (hX : PuncturedFree T.X₃) (p : PrimeSpectrum R)
    (hp : p.asIdeal ≠ maximalIdeal R) : ¬ liftIdeal T ≤ p.asIdeal := by
  intro hle
  let S := p.asIdeal.primeCompl
  let B := Localization S
  have : Module.FinitePresentation R T.X₃ := Module.finitePresentation_of_finite R T.X₃
  have hfree : Module.Free B (T.X₃.localizedModule S) := hX p hp
  let f₂ := T.X₂.localizedModuleMkLinearMap S
  let f₃ := T.X₃.localizedModuleMkLinearMap S
  let gS : T.X₂.localizedModule S →ₗ[B] T.X₃.localizedModule S :=
    IsLocalizedModule.mapExtendScalars S f₂ f₃ B T.g.hom
  have hgS : Function.Surjective gS :=
    IsLocalizedModule.map_surjective S f₂ f₃ T.g.hom hT.moduleCat_surjective_g
  have hproj : Module.Projective B (T.X₃.localizedModule S) :=
    @Module.Projective.of_free B _ (T.X₃.localizedModule S) _ _ hfree
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property gS LinearMap.id hgS
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalizedModule.surj S (IsLocalizedModule.mapExtendScalars S f₃ f₂ B) σ
  have h1 : IsLocalizedModule.mapExtendScalars S f₃ f₃ B (T.g.hom ∘ₗ a) =
      IsLocalizedModule.mapExtendScalars S f₃ f₃ B ((s : R) • LinearMap.id) := by
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.linearMap_ext S f₃ f₃
    ext x
    have e2 : gS (σ (f₃ x)) = f₃ x := LinearMap.congr_fun hσ (f₃ x)
    have e3 : (s : R) • σ (f₃ x) = f₂ (a x) := by
      have := LinearMap.congr_fun hs (f₃ x)
      simp only [LinearMap.smul_apply, IsLocalizedModule.mapExtendScalars_apply_apply,
        IsLocalizedModule.map_apply] at this
      exact this
    have e4 : gS (f₂ (a x)) = f₃ (T.g.hom (a x)) := by simp [gS]
    have e5 : gS ((s : R) • σ (f₃ x)) = (s : R) • gS (σ (f₃ x)) :=
      LinearMap.map_smul_of_tower gS (s : R) (σ (f₃ x))
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq, map_smul]
    rw [← e4, ← e3, e5, e2]
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists S
    (IsLocalizedModule.mapExtendScalars S f₃ f₃ B)).mp h1
  have hmem : (c : R) * s ∈ liftIdeal T := by
    refine ⟨(c : R) • a, ?_⟩
    rw [LinearMap.comp_smul, mul_smul]
    exact hc
  exact (c * s).2 (hle hmem)

open IsLocalRing in
/-- On the punctured spectrum a power of each element of the maximal ideal kills the class. -/
theorem exists_pow_smul_extClass [IsLocalRing R] (T : ShortComplex (ModuleCat.{u} R))
    (hT : T.ShortExact) [Module.Finite R T.X₃] (hX : PuncturedFree T.X₃) (x : R)
    (hx : x ∈ maximalIdeal R) : ∃ n : ℕ, x ^ n • hT.extClass = 0 := by
  have hrad : x ∈ (liftIdeal T).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro p ⟨hle, hprime⟩
    by_cases hp : p = maximalIdeal R
    · rw [hp]
      exact hx
    · exact absurd hle (liftIdeal_not_le T hT hX ⟨p, hprime⟩ hp)
  obtain ⟨n, a, ha⟩ := hrad
  refine ⟨n, smul_extClass_eq_zero T hT (x ^ n) (ModuleCat.ofHom a) ?_⟩
  ext z
  exact LinearMap.congr_fun ha z

open IsLocalRing in
/-- Positive Ext out of a punctured-free module vanishes against `x`-divisible modules. -/
theorem subsingleton_ext_of_puncturedFree [IsLocalRing R] (X : ModuleCat.{u} R) [Module.Finite R X]
    (hX : PuncturedFree X) (x : R) (hx : x ∈ maximalIdeal R) (L : ModuleCat.{u} R)
    (hd : SMulSection x L) (j : ℕ) : Subsingleton (Ext X L (j + 1)) := by
  obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R X
  let T := f.shortComplexKer
  have hT : T.ShortExact := LinearMap.shortExact_shortComplexKer hf
  obtain ⟨n, hn⟩ := exists_pow_smul_extClass T hT hX x hx
  exact subsingleton_ext_succ_of_torsion T hT x n hn L hd j

end Lift

section Regular

variable {R : Type u} [CommRing R]

/-- In a power-torsion module every nonzero element has a nonzero multiple killed by the whole
list. -/
theorem exists_smul_ne_zero_of_torsion {W : Type u} [AddCommGroup W] [Module R W] (l : List R)
    (hl : ∀ y ∈ l, ∀ z : W, ∃ n : ℕ, y ^ n • z = 0) (z : W) (hz : z ≠ 0) :
    ∃ c : R, c • z ≠ 0 ∧ ∀ y ∈ l, y • c • z = 0 := by
  induction l with
  | nil => exact ⟨1, by simpa using hz, by simp⟩
  | cons y l ih =>
    obtain ⟨c, hc, hcl⟩ := ih (fun y' hy' => hl y' (List.mem_cons_of_mem _ hy'))
    classical
    have hex := hl y List.mem_cons_self (c • z)
    have hn : y ^ Nat.find hex • c • z = 0 := Nat.find_spec hex
    have hn0 : Nat.find hex ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_smul] at hn
      exact hc hn
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    refine ⟨y ^ m * c, ?_, ?_⟩
    · rw [mul_smul]
      exact Nat.find_min hex (by omega : m < Nat.find hex)
    · intro y' hy'
      rcases List.mem_cons.mp hy' with h | h
      · rw [h, mul_smul, smul_smul, ← pow_succ', ← Nat.succ_eq_add_one, ← hm]
        exact hn
      · rw [mul_smul, smul_comm, hcl y' h, smul_zero]

/-- A torsion module without elements killed by the whole sequence has a regular last term. -/
theorem isSMulRegular_of_torsion (W : ModuleCat.{u} R) (l : List R) (x : R)
    (hl : ∀ y ∈ l, ∀ z : W, ∃ n : ℕ, y ^ n • z = 0)
    (hQ : Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList (l ++ [x]))) W 0)) :
    IsSMulRegular W x := by
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro z hxz
  by_contra hz
  obtain ⟨c, hc, hcl⟩ := exists_smul_ne_zero_of_torsion l hl z hz
  have hker : Ideal.ofList (l ++ [x]) ≤
      LinearMap.ker (LinearMap.toSpanSingleton R W (c • z)) := by
    apply Ideal.span_le.mpr
    intro y hy
    rcases List.mem_append.mp hy with h | h
    · exact hcl y h
    · rw [List.mem_singleton.mp h]
      change x • c • z = 0
      rw [smul_comm, hxz, smul_zero]
  let φ : R ⧸ Ideal.ofList (l ++ [x]) →ₗ[R] W :=
    Submodule.liftQ _ (LinearMap.toSpanSingleton R W (c • z)) hker
  have h0 : Ext.mk₀ (ModuleCat.ofHom φ) = 0 := Subsingleton.elim _ _
  rw [← Ext.mk₀_zero, (Ext.mk₀_bijective _ _).injective.eq_iff] at h0
  have h1 : φ (Submodule.Quotient.mk 1) = 0 := by
    have := congrArg (fun f => f.hom (Submodule.Quotient.mk 1)) h0
    simpa using this
  have h2 : φ (Submodule.Quotient.mk 1) = c • z := by
    change (LinearMap.toSpanSingleton R W (c • z)) 1 = c • z
    rw [LinearMap.toSpanSingleton_apply, one_smul]
  exact hc (h2.symm.trans h1)

end Regular

section ChainInduction

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

open IsLocalRing RingTheory.Sequence in
/-- Rees vanishing for the quotient by an initial segment of a regular sequence. -/
theorem subsingleton_ext_quotient_take [IsLocalRing R] (rs : List R)
    (hmem : ∀ x ∈ rs, x ∈ maximalIdeal R) (hreg : IsWeaklyRegular R rs) (r : ℕ)
    (hr : r < rs.length) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList (rs.take (r + 1))))
      (ModuleCat.of R R) r) := by
  let I := Ideal.ofList (rs.take (r + 1))
  have hIm : I ≤ maximalIdeal R :=
    Ideal.span_le.mpr fun y hy => hmem y (List.mem_of_mem_take hy)
  have hlt : I • (⊤ : Submodule R R) < ⊤ := by
    refine lt_of_le_of_lt (Submodule.smul_mono_left hIm) ?_
    simpa using (maximalIdeal.isMaximal R).lt_top
  have hw : IsWeaklyRegular R (rs.take (r + 1)) := by
    have h := hreg
    rw [← List.take_append_drop (r + 1) rs, isWeaklyRegular_append_iff] at h
    exact h.1
  have hreg' : IsRegular (ModuleCat.of R R) (rs.take (r + 1)) :=
    IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R
      (fun y hy => hmem y (List.mem_of_mem_take hy)) hw
  have hsupp : Module.support R (ModuleCat.of R (R ⧸ I)) ⊆ PrimeSpectrum.zeroLocus I := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  exact ModuleCat.subsingleton_ext_of_exists_isRegular I (ModuleCat.of R (R ⧸ I)) hsupp
    (ModuleCat.of R R) hlt (rs.take (r + 1)) (fun y hy => Ideal.subset_span hy) hreg' r
    (by rw [List.length_take]; omega)

open IsLocalRing RingTheory.Sequence in
/-- Iterated localization along a regular sequence. Stage `r` is a model of the top local
cohomology of the first `r` terms, and all the Ext vanishing shifts along the chain. -/
theorem exists_chain [IsLocalRing R] (rs : List R) (hmem : ∀ x ∈ rs, x ∈ maximalIdeal R)
    (hreg : IsWeaklyRegular R rs) (X P : ModuleCat.{u} R)
    (hXd : ∀ x ∈ maximalIdeal R, ∀ L : ModuleCat.{u} R, SMulSection x L →
      ∀ j, Subsingleton (Ext X L (j + 1)))
    (hPd : ∀ x ∈ maximalIdeal R, ∀ L : ModuleCat.{u} R, SMulSection x L →
      ∀ j, Subsingleton (Ext P L (j + 1)))
    (hP : ∀ j, 1 ≤ j → j ≤ rs.length → Subsingleton (Ext P (ModuleCat.of R R) j))
    (hX : Subsingleton (Ext X (ModuleCat.of R (P →ₗ[R] R)) (rs.length + 1)))
    (r : ℕ) (hr : r ≤ rs.length) :
    ∃ W : ModuleCat.{u} R,
      (∀ y ∈ rs.take r, ∀ z : W, ∃ n : ℕ, y ^ n • z = 0) ∧
      (∀ Q : ModuleCat.{u} R, (∀ y ∈ rs.take r, ∀ q : Q, y • q = 0) → ∀ j,
        (Subsingleton (Ext Q W j) ↔ Subsingleton (Ext Q (ModuleCat.of R R) (j + r)))) ∧
      (∀ j, 1 ≤ j → j + r ≤ rs.length → Subsingleton (Ext P W j)) ∧
      Subsingleton (Ext X (ModuleCat.of R (P →ₗ[R] W)) (rs.length + 1 - r)) := by
  induction r with
  | zero =>
    exact ⟨ModuleCat.of R R, by simp, fun Q _ j => Iff.rfl,
      fun j h1 h2 => hP j h1 (by simpa using h2), hX⟩
  | succ r ih =>
    obtain ⟨W, hT, hQ, hPW, hXW⟩ := ih (Nat.le_of_succ_le hr)
    have hlt : r < rs.length := hr
    have htake : rs.take (r + 1) = rs.take r ++ [rs[r]] := List.take_succ_eq_append_getElem hlt
    have hxm : rs[r] ∈ maximalIdeal R := hmem _ (List.getElem_mem hlt)
    have hxreg : IsSMulRegular W rs[r] := by
      apply isSMulRegular_of_torsion W (rs.take r) rs[r] hT
      rw [← htake]
      apply (hQ (ModuleCat.of R (R ⧸ Ideal.ofList (rs.take (r + 1)))) ?_ 0).mpr
      · rw [zero_add]
        exact subsingleton_ext_quotient_take rs hmem hreg r hlt
      · intro y hy q
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        rw [← Submodule.Quotient.mk_smul]
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        rw [smul_eq_mul]
        apply Ideal.mul_mem_right
        apply Ideal.subset_span
        rw [htake]
        exact List.mem_append_left _ hy
    let S := locComplex W rs[r]
    have hS : S.ShortExact := locComplex_shortExact W rs[r] hxreg
    have hdiv : SMulSection rs[r] S.X₂ := smulSection_locComplex W rs[r]
    refine ⟨S.X₃, ?_, ?_, ?_, ?_⟩
    · intro y hy z
      rw [htake] at hy
      rcases List.mem_append.mp hy with hy | hy
      · exact locComplex_torsion W rs[r] y (hT y hy) z
      · rw [List.mem_singleton.mp hy]
        exact locComplex_torsion_self W rs[r] z
    · intro Q hQann j
      have hQx : ∀ q : Q, rs[r] • q = 0 := hQann rs[r] (by
        rw [htake]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl))
      have hQr : ∀ y ∈ rs.take r, ∀ q : Q, y • q = 0 := fun y hy =>
        hQann y (by rw [htake]; exact List.mem_append_left _ hy)
      have hmid : ∀ i, Subsingleton (Ext Q S.X₂ i) :=
        subsingleton_ext_of_smul_eq_zero Q S.X₂ rs[r] hQx hdiv
      have h := hQ Q hQr (j + 1)
      rw [show j + (r + 1) = j + 1 + r by omega, ← h]
      exact ⟨fun h3 => subsingleton_ext_X₁ S hS Q j (hmid _) h3,
        fun h1 => subsingleton_ext_X₃ S hS Q j (hmid _) h1⟩
    · intro j hj1 hjr
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      exact subsingleton_ext_X₃ S hS P (i + 1) (hPd rs[r] hxm S.X₂ hdiv i)
        (hPW (i + 1 + 1) (by omega) (by omega))
    · have hH : (homComplex P S).ShortExact :=
        homComplex_shortExact P S hS (hPW 1 le_rfl (by omega))
      have hdivH : SMulSection rs[r] (homComplex P S).X₂ := smulSection_hom P rs[r] S.X₂ hdiv
      obtain ⟨i, hi⟩ : ∃ i, rs.length + 1 - (r + 1) = i + 1 := ⟨rs.length - r - 1, by omega⟩
      rw [hi]
      have h1 : Subsingleton (Ext X (homComplex P S).X₁ (i + 1 + 1)) := by
        have he : rs.length + 1 - r = i + 1 + 1 := by omega
        rw [← he]
        exact hXW
      exact subsingleton_ext_X₃ (homComplex P S) hH X (i + 1) (hXd rs[r] hxm _ hdivH i) h1

end ChainInduction

section Trace

variable {R : Type u} [CommRing R]

/-- The trace identity behind the socle argument: a map on `F₁` of the form `v ↦ ỹ(v) • γ` which
extends through `d : F₁ → F₀` pairs to zero with the restriction of `ỹ` to a submodule killed
by `d`. -/
theorem trace_vanishing [Nontrivial R] {K F₁ F₀ W : Type u} [AddCommGroup K] [Module R K]
    [AddCommGroup F₁] [Module R F₁] [AddCommGroup F₀] [Module R F₀] [AddCommGroup W] [Module R W]
    [Module.Free R F₁] [Module.Finite R F₁] [Module.Free R F₀] [Module.Finite R F₀]
    (ι : K →ₗ[R] F₁) (d : F₁ →ₗ[R] F₀) (hd : d ∘ₗ ι = 0)
    (ht : F₀ →ₗ[R] (Module.Dual R K →ₗ[R] W)) (yt : Module.Dual R F₁)
    (γ : Module.Dual R K →ₗ[R] W) (hh : ∀ v : F₁, ht (d v) = yt v • γ) : γ (yt ∘ₗ ι) = 0 := by
  classical
  let b₁ := Module.finBasis R F₁
  let b₀ := Module.finBasis R F₀
  have e1 : ∀ φ : Module.Dual R F₁, φ ∘ₗ ι = ∑ i, φ (b₁ i) • (b₁.coord i ∘ₗ ι) := by
    intro φ
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun (b₁.sum_dual_apply_smul_coord φ) (ι x)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply] at h ⊢
    exact h.symm
  have e2 : ∀ i, yt (b₁ i) • γ (b₁.coord i ∘ₗ ι) =
      ∑ k, (b₀.coord k (d (b₁ i))) • ht (b₀ k) (b₁.coord i ∘ₗ ι) := by
    intro i
    have h1 : ht (d (b₁ i)) = ∑ k, (b₀.coord k (d (b₁ i))) • ht (b₀ k) := by
      conv_lhs => rw [← b₀.sum_repr (d (b₁ i))]
      simp only [map_sum, map_smul, Module.Basis.coord_apply]
    rw [← LinearMap.smul_apply, ← hh, h1, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
  have e3 : ∀ k, ∑ i, (b₀.coord k (d (b₁ i))) • (b₁.coord i ∘ₗ ι) = 0 := by
    intro k
    have h2 := e1 (b₀.coord k ∘ₗ d)
    simp only [LinearMap.comp_apply] at h2
    rw [← h2, LinearMap.comp_assoc, hd, LinearMap.comp_zero]
  rw [e1 yt, map_sum]
  simp only [map_smul]
  simp_rw [e2]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k _
  have h3 := congrArg (ht (b₀ k)) (e3 k)
  simpa only [map_sum, map_smul, map_zero] using h3

end Trace

section Criterion

variable {R : Type u} [CommRing R] [IsLocalRing R]

open IsLocalRing in
/-- The socle argument: if first Ext against `Hom(K^*, W)` vanishes, functionals on the second
syzygy `K` with values in the maximal ideal are killed by every map to `W` vanishing on
`𝔪 K^*`. -/
theorem dual_ker_criterion (T₀ : ShortComplex (ModuleCat.{u} R)) (hT₀ : T₀.ShortExact)
    [Module.Finite R T₀.X₂] [Module.Free R T₀.X₂]
    {Q : Type u} [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Free R Q]
    (g : Q →ₗ[R] T₀.X₁) (hg : Function.Surjective g)
    (hdual : Function.Surjective (LinearMap.ker g).subtype.dualMap)
    (W : ModuleCat.{u} R)
    (hE : Subsingleton (Ext T₀.X₃
      (ModuleCat.of R (Module.Dual R (LinearMap.ker g) →ₗ[R] W)) 1))
    (y : Module.Dual R (LinearMap.ker g)) (hy : ∀ κ, y κ ∈ maximalIdeal R)
    (γ : Module.Dual R (LinearMap.ker g) →ₗ[R] W)
    (hγ : ∀ a ∈ maximalIdeal R, ∀ p, γ (a • p) = 0) : γ y = 0 := by
  obtain ⟨yt, hyt⟩ := hdual y
  let L := Module.Dual R (LinearMap.ker g) →ₗ[R] W
  let h : Q →ₗ[R] L := (LinearMap.toSpanSingleton R L γ) ∘ₗ yt
  have hker : LinearMap.ker g ≤ LinearMap.ker h := by
    intro κ hκ
    rw [LinearMap.mem_ker]
    change yt κ • γ = 0
    have h1 : yt κ = y ⟨κ, hκ⟩ := by
      rw [← hyt]
      rfl
    apply LinearMap.ext
    intro p
    rw [LinearMap.smul_apply, ← map_smul, LinearMap.zero_apply]
    exact hγ _ (h1 ▸ hy ⟨κ, hκ⟩) p
  let hbar : T₀.X₁ →ₗ[R] L := (Submodule.liftQ (LinearMap.ker g) h hker) ∘ₗ
    (g.quotKerEquivOfSurjective hg).symm.toLinearMap
  have hbar_g : ∀ v, hbar (g v) = h v := by
    intro v
    have h2 : (g.quotKerEquivOfSurjective hg).symm (g v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    change Submodule.liftQ _ h hker ((g.quotKerEquivOfSurjective hg).symm (g v)) = h v
    rw [h2]
    rfl
  obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₁ hT₀ (ModuleCat.of R L)
    (Ext.mk₀ (ModuleCat.ofHom hbar)) (add_zero 1) (Subsingleton.eq_zero _)
  obtain ⟨e, rfl⟩ := (Ext.mk₀_bijective _ _).surjective a
  rw [Ext.mk₀_comp_mk₀, (Ext.mk₀_bijective _ _).injective.eq_iff] at ha
  have he : ∀ k₁ : T₀.X₁, e.hom (T₀.f k₁) = hbar k₁ := fun k₁ =>
    congrArg (fun φ => φ.hom k₁) ha
  have key := trace_vanishing (LinearMap.ker g).subtype (T₀.f.hom ∘ₗ g) (by
    apply LinearMap.ext
    intro κ
    change T₀.f (g κ.1) = 0
    rw [LinearMap.mem_ker.mp κ.2, map_zero]) e.hom yt γ (fun v => by
    change e.hom (T₀.f (g v)) = yt v • γ
    rw [he, hbar_g]
    rfl)
  rw [← hyt]
  exact key

open IsLocalRing in
/-- A nonzero map from the residue field detects membership in `𝔪 P`. -/
theorem mem_smul_top_of_forall {P : Type u} [AddCommGroup P] [Module R P] (W : Type u)
    [AddCommGroup W] [Module R W] (σ : ResidueField R →ₗ[R] W) (hσ : σ ≠ 0) (y : P)
    (H : ∀ γ : P →ₗ[R] W, (∀ a ∈ maximalIdeal R, ∀ p, γ (a • p) = 0) → γ y = 0) :
    y ∈ maximalIdeal R • (⊤ : Submodule R P) := by
  by_contra hy
  let : Module (ResidueField R) (P ⧸ (maximalIdeal R • ⊤ : Submodule R P)) :=
    inferInstanceAs (Module (R ⧸ maximalIdeal R) (P ⧸ maximalIdeal R • (⊤ : Submodule R P)))
  have : IsScalarTower R (ResidueField R) (P ⧸ (maximalIdeal R • ⊤ : Submodule R P)) :=
    inferInstanceAs (IsScalarTower R (R ⧸ maximalIdeal R)
      (P ⧸ maximalIdeal R • (⊤ : Submodule R P)))
  have hne : (maximalIdeal R • ⊤ : Submodule R P).mkQ y ≠ 0 := fun h0 =>
    hy ((Submodule.Quotient.mk_eq_zero _).mp h0)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual (ResidueField R) (P ⧸ (maximalIdeal R • ⊤ : Submodule R P)),
      f ((maximalIdeal R • ⊤ : Submodule R P).mkQ y) ≠ 0 := by
    by_contra hall
    exact hne ((Module.forall_dual_apply_eq_zero_iff (ResidueField R) _).mp
      (fun φ => not_not.mp (fun hφ => hall ⟨φ, hφ⟩)))
  let γ : P →ₗ[R] W := σ ∘ₗ (f.restrictScalars R) ∘ₗ (maximalIdeal R • ⊤ : Submodule R P).mkQ
  have h0 : σ (f ((maximalIdeal R • ⊤ : Submodule R P).mkQ y)) = 0 := H γ (fun a ha p => by
    change σ (f ((maximalIdeal R • ⊤ : Submodule R P).mkQ (a • p))) = 0
    have hz : (maximalIdeal R • ⊤ : Submodule R P).mkQ (a • p) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul ha Submodule.mem_top)
    rw [hz, map_zero, map_zero])
  apply hσ
  apply LinearMap.ext
  intro c
  obtain ⟨a, ha⟩ := residue_surjective
    (c * (f ((maximalIdeal R • ⊤ : Submodule R P).mkQ y))⁻¹)
  have hc : c = a • f ((maximalIdeal R • ⊤ : Submodule R P).mkQ y) := by
    rw [Algebra.smul_def, ResidueField.algebraMap_eq, ha, inv_mul_cancel_right₀ hf]
  rw [hc, map_smul, h0, smul_zero, LinearMap.zero_apply]

open IsLocalRing TensorProduct in
/-- The dual of a finite module is free once functionals with values in the maximal ideal lie
in `𝔪` times the dual. -/
theorem free_dual_of_criterion [IsNoetherianRing R] {K : Type u} [AddCommGroup K] [Module R K]
    [Module.Finite R K]
    (H : ∀ y : Module.Dual R K, (∀ κ, y κ ∈ maximalIdeal R) →
      y ∈ maximalIdeal R • (⊤ : Submodule R (Module.Dual R K))) :
    Module.Free R (Module.Dual R K) := by
  obtain ⟨F, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R K
  have hfin : Module.Finite R (Module.Dual R K) :=
    Module.Finite.of_injective f.dualMap (LinearMap.dualMap_injective_of_surjective hf)
  have hinj : Function.Injective (f.dualMap.lTensor (ResidueField R)) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    obtain ⟨y, rfl⟩ := TensorProduct.mk_surjective R (Module.Dual R K) (ResidueField R)
      Ideal.Quotient.mk_surjective z
    have hy : ∀ κ, y κ ∈ maximalIdeal R := by
      intro κ
      obtain ⟨v, rfl⟩ := hf κ
      have h1 := congrArg ((LinearMap.applyₗ v : Module.Dual R F →ₗ[R] R).lTensor
        (ResidueField R)) hz
      have h2 := congrArg (TensorProduct.rid R (ResidueField R)) h1
      simp only [TensorProduct.mk_apply, LinearMap.lTensor_tmul, LinearMap.applyₗ_apply_apply,
        LinearMap.dualMap_apply, TensorProduct.rid_tmul, map_zero] at h2
      rw [Algebra.smul_def, ResidueField.algebraMap_eq, mul_one] at h2
      exact (residue_eq_zero_iff _).mp h2
    have hmem := H y hy
    change (1 : ResidueField R) ⊗ₜ[R] y = 0
    refine Submodule.smul_induction_on hmem ?_ ?_
    · intro a ha p _
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
        ResidueField.algebraMap_eq, (residue_eq_zero_iff a).mpr ha, zero_mul,
        TensorProduct.zero_tmul]
    · intro u v hu hv
      rw [TensorProduct.tmul_add, hu, hv, add_zero]
  obtain ⟨l', hl'⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective f.dualMap).mpr hinj
  have : Module.Projective R (Module.Dual R K) := Module.Projective.of_split f.dualMap l' hl'
  exact Module.free_of_flat_of_isLocalRing

end Criterion

section Assembly

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

open IsLocalRing in
/-- A regular sequence in the maximal ideal whose length is the depth. -/
theorem exists_regular_of_hasDepth [IsLocalRing R] {t : ℕ} (h : HasDepth R t) :
    ∃ rs : List R, rs.length = t ∧ (∀ x ∈ rs, x ∈ maximalIdeal R) ∧
      RingTheory.Sequence.IsWeaklyRegular R rs := by
  let m := maximalIdeal R
  let A := ModuleCat.of R R
  have hlt : m • (⊤ : Ideal R) < ⊤ := by simpa using (maximalIdeal.isMaximal R).lt_top
  have H := ModuleCat.exists_isRegular_tfae m t A hlt
  have hsh (i : ℕ) (hi : i < t) :
      Subsingleton (Ext (ModuleCat.of R (Shrink.{u} (R ⧸ m))) A i) := by
    let e := (Shrink.linearEquiv.{u} R (R ⧸ m)).toModuleIso
    let E := ((extFunctor (C := ModuleCat.{u} R) i).mapIso e.op).app A
    exact E.addCommGroupIsoToAddEquiv.subsingleton_congr.mp (h.1 i hi)
  obtain ⟨rs, hlen, hmem, hreg⟩ := (H.out 1 3).mp hsh
  exact ⟨rs, hlen, hmem, hreg.toIsWeaklyRegular⟩

/-- Kimura's local criterion, in the form needed by the reduction: there is no counterexample
that is locally free on the punctured spectrum of a normal local domain of dimension at least
two. -/
theorem puncturedCase : PuncturedCase.{u} := by
  intro A _ _ _ _ _ X _ hdim hinf hp hR hX
  obtain ⟨t, ht, hdepth⟩ := exists_depth_ge_two hdim
  obtain ⟨rs, hlen, hmem, hreg⟩ := exists_regular_of_hasDepth hdepth
  obtain ⟨K₀, _, _, hK₀, hd₀⟩ := exists_reflexive_syzygy X ⟨hinf, hp, hR, hX⟩ t
  obtain ⟨F₀, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation A K₀
  let T₀ := f.shortComplexKer
  have hT₀ : T₀.ShortExact := LinearMap.shortExact_shortComplexKer hf
  have hK₁ : Counterexample T₀.X₁ := counterexample_syzygy T₀ hT₀ hK₀
  have hrefl₁ : Module.IsReflexive A T₀.X₁ := syzygy_reflexive T₀ hT₀
    (Module.bijective_dual_eval A K₀).injective (hK₀.ringExt 1 Nat.one_pos)
  have hd₁ := dual_ext_bound T₀ hT₀ (hK₀.ringExt 1 Nat.one_pos) t hd₀
  obtain ⟨F₁, _, _, _, _, g, hg⟩ := Module.exists_finite_presentation A T₀.X₁
  let T₁ := g.shortComplexKer
  have hT₁ : T₁.ShortExact := LinearMap.shortExact_shortComplexKer hg
  have hK : Counterexample T₁.X₁ := counterexample_syzygy T₁ hT₁ hK₁
  have hrefl : Module.IsReflexive A T₁.X₁ := syzygy_reflexive T₁ hT₁
    (Module.bijective_dual_eval A T₀.X₁).injective (hK₁.ringExt 1 Nat.one_pos)
  have hd := dual_ext_bound T₁ hT₁ (hK₁.ringExt 1 Nat.one_pos) (t + 1) hd₁
  let K := T₁.X₁
  let P := ringDual K
  have hPfin : Module.Finite A P := by
    obtain ⟨G, _, _, _, _, φ, hφ⟩ := Module.exists_finite_presentation A K
    exact Module.Finite.of_injective φ.dualMap (LinearMap.dualMap_injective_of_surjective hφ)
  have hPpf : PuncturedFree P := dual_punctured_free K hK.puncturedFree
  have hXd : ∀ x ∈ IsLocalRing.maximalIdeal A, ∀ L : ModuleCat.{u} A, SMulSection x L →
      ∀ j, Subsingleton (Ext K₀ L (j + 1)) :=
    fun x hx L hL j => subsingleton_ext_of_puncturedFree K₀ hK₀.puncturedFree x hx L hL j
  have hPd : ∀ x ∈ IsLocalRing.maximalIdeal A, ∀ L : ModuleCat.{u} A, SMulSection x L →
      ∀ j, Subsingleton (Ext P L (j + 1)) :=
    fun x hx L hL j => subsingleton_ext_of_puncturedFree P hPpf x hx L hL j
  have hPA : ∀ j, 1 ≤ j → j ≤ rs.length → Subsingleton (Ext P (ModuleCat.of A A) j) :=
    fun j h1 h2 => hd j h1 (by omega)
  have hXA : Subsingleton (Ext K₀ (ModuleCat.of A (P →ₗ[A] A)) (rs.length + 1)) := by
    rw [hlen]
    have h3 : Subsingleton (Ext K₀ T₀.X₁ t) := by
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      exact subsingleton_ext_X₁ T₀ hT₀ K₀ s
        (subsingleton_ext_finite_free K₀ T₀.X₂ (s + 1) (hK₀.ringExt (s + 1) (Nat.succ_pos _)))
        (hK₀.selfExt s (by omega))
    have h4 : Subsingleton (Ext K₀ K (t + 1)) :=
      subsingleton_ext_X₁ T₁ hT₁ K₀ t
        (subsingleton_ext_finite_free K₀ T₁.X₂ (t + 1) (hK₀.ringExt (t + 1) (Nat.succ_pos _)))
        h3
    exact subsingleton_ext_iso K₀ (Module.evalEquiv A K).toModuleIso (t + 1) h4
  obtain ⟨W, -, hQ, -, hXW⟩ := exists_chain rs hmem hreg K₀ P hXd hPd hPA hXA rs.length le_rfl
  have hsoc : ¬ Subsingleton (Ext (ModuleCat.of A (IsLocalRing.ResidueField A)) W 0) := by
    rw [hQ (ModuleCat.of A (IsLocalRing.ResidueField A)) (fun y hy q => ?_) 0, zero_add, hlen]
    · exact hdepth.2
    · have hym := hmem y (List.mem_of_mem_take hy)
      rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
        (IsLocalRing.residue_eq_zero_iff _).mpr hym, zero_mul]
  obtain ⟨σ, hσ⟩ : ∃ σ : IsLocalRing.ResidueField A →ₗ[A] W, σ ≠ 0 := by
    by_contra hall
    apply hsoc
    apply subsingleton_of_forall_eq 0
    intro ξ
    obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).surjective ξ
    have h0 : φ.hom = 0 := not_not.mp (fun hne => hall ⟨φ.hom, hne⟩)
    rw [← Ext.mk₀_zero]
    exact congrArg Ext.mk₀ (ModuleCat.hom_ext h0)
  have hE : Subsingleton (Ext K₀ (ModuleCat.of A (P →ₗ[A] W)) 1) := by
    have h1 : rs.length + 1 - rs.length = 1 := by omega
    rw [h1] at hXW
    exact hXW
  have hdual : Function.Surjective (LinearMap.ker g).subtype.dualMap :=
    dual_surj T₁ hT₁ (hK₁.ringExt 1 Nat.one_pos)
  have Hcrit : ∀ y : Module.Dual A (LinearMap.ker g),
      (∀ κ, y κ ∈ IsLocalRing.maximalIdeal A) →
      y ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A (Module.Dual A (LinearMap.ker g))) :=
    fun y hy => mem_smul_top_of_forall W σ hσ y
      (fun γ hγ => dual_ker_criterion T₀ hT₀ g hg hdual W hE y hy γ hγ)
  have hfree : Module.Free A (Module.Dual A (LinearMap.ker g)) := free_dual_of_criterion Hcrit
  have : Module.Free A (Module.Dual A K) := hfree
  have : Module.Free A K := Module.Free.of_equiv (Module.evalEquiv A K).symm
  exact hK.infiniteDimension 0 (projective_iff_hasProjectiveDimensionLT_one.mp inferInstance)

end Assembly

end OMA.AuslanderReitenReduction

open OMA.AuslanderReitenReduction in
/-- The Auslander–Reiten conjecture for commutative Noetherian normal domains. -/
theorem OMA.solution : type_of% @AuslanderReiten.auslander_reiten.variants.normal := by
  intro R _ _ M _ _ _ _ _ hR hM
  let X := ModuleCat.of R M
  apply projective_of_stalks X
  intro p
  let B := Localization.AtPrime p.asIdeal
  let Y := X.localizedModule p.asIdeal.primeCompl
  have : IsLocalizedModule p.asIdeal.primeCompl
      (X.localizedModuleMkLinearMap p.asIdeal.primeCompl) :=
    ModuleCat.localizedModule_isLocalizedModule _ _
  have : IsIntegrallyClosed B := isIntegrallyClosed_of_isLocalization B _
    p.asIdeal.primeCompl_le_nonZeroDivisors
  have : Module.Finite B Y := Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
    (X.localizedModuleMkLinearMap p.asIdeal.primeCompl)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ideal.height_ne_top_of_isPrime (I := IsLocalRing.maximalIdeal B))
  exact local_aux puncturedCase n B Y hn.symm
    (fun i hi => subsingleton_ext_localized_ring _ X i (hR i hi))
    (fun i hi => subsingleton_ext_localized _ X X i (hM i hi))
