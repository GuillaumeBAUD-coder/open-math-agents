import FormalConjectures.Paper.AuslanderReiten
import Mathlib

/-!
Auslander-Reiten Conjecture for Normal Rings (Kimura 2023): Reduction

This file reduces the Auslander-Reiten conjecture for finitely generated modules `M` over a
Noetherian integrally closed integral domain `R` in an arbitrary universe `u` to two canonical
`Type 0` commutative-algebra theorems:

1. `H1`: Serre's condition (S₂) for local normal Noetherian domains of Krull dimension at least 2
   (Matsumura, Commutative Ring Theory, Theorem 23.8): every such ring has a regular sequence
   of length 2 in its maximal ideal.
2. `H2`: Kimura's (S₂) punctured-spectrum projectivity criterion (Kimura 2023, Theorem 1.1(3)):
   over a local Noetherian ring `A` of Krull dimension at least 2 satisfying Serre's condition
   (S₂), every finitely generated `A`-module `M` that is locally projective on the punctured
   spectrum and satisfies `Ext^i_A(M, A) = 0` and `Ext^i_A(M, M) = 0` for all `i > 0` is
   projective.

In `main`, we prove directly in Lean:
- Flat base change (forward) and faithfully flat descent (backward) of `Abelian.Ext` vanishing
  across arbitrary universes for all degrees `i > 0`, via degree-0 Hom flat base change on a
  finite presentation and homological dimension shifting.
- Global-to-local reduction from `R` to `Localization.AtPrime P` at every maximal ideal `P`, using
  `Module.projective_of_localization_maximal` and `Module.finitePresentation_of_finite`.
- Countable syzygy-closed faithfully flat local descent from `(R_P, M_P)` in `Type u` to
  `(A, M₀)` in `Type 0`, including a direct proof that `IsIntegrallyClosed` descends along any
  faithfully flat map into an integrally closed domain.
- The Krull dimension `≤ 1` base case (fields and DVRs) directly via `IsDedekindDomain`,
  `IsPrincipalIdealRing.of_finite_maximals`, `Submodule.basisOfPid`, and `Ext¹(M, K) = 0`.
- Strong induction on `ringKrullDim A` reducing every dimension `≥ 2` local normal domain to the
  punctured spectrum before invoking `H1` and `H2`.
-/

namespace OMA.R_AuslanderReiten_auslander_reiten_variants_normal_R1

open CategoryTheory Limits TensorProduct IsLocalRing

universe u u₁ u₂

/-- Serre's condition (S₂) for local normal Noetherian domains: every local Noetherian integrally
closed domain of Krull dimension at least 2 has a regular sequence of length 2 in its maximal
ideal (Matsumura, Commutative Ring Theory, Theorem 23.8). -/
def H1 : Prop :=
  ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A],
    (2 : WithBot ℕ∞) ≤ ringKrullDim A →
    ∃ x ∈ maximalIdeal A, IsSMulRegular A x ∧
      ∃ y ∈ maximalIdeal A, IsSMulRegular (A ⧸ Ideal.span {x}) y

/-- Kimura's (S₂) punctured-spectrum Auslander-Reiten criterion (Kimura 2023, Theorem 1.1(3)):
over a local Noetherian ring of Krull dimension at least 2 satisfying Serre's condition (S₂),
any finitely generated module that is locally projective on the punctured spectrum and has
vanishing positive Ext against itself and the base ring is projective. -/
def H2 : Prop :=
  ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
    (2 : WithBot ℕ∞) ≤ ringKrullDim A →
    (∀ (Q : Ideal A) [Q.IsPrime],
      (1 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime Q) →
      ∃ x ∈ maximalIdeal (Localization.AtPrime Q),
        IsSMulRegular (Localization.AtPrime Q) x) →
    (∀ (Q : Ideal A) [Q.IsPrime],
      (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime Q) →
      ∃ x ∈ maximalIdeal (Localization.AtPrime Q),
        IsSMulRegular (Localization.AtPrime Q) x ∧
        ∃ y ∈ maximalIdeal (Localization.AtPrime Q),
          IsSMulRegular ((Localization.AtPrime Q) ⧸ Ideal.span {x}) y) →
    ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M],
      (∀ (Q : Ideal A) [Q.IsPrime], Q ≠ maximalIdeal A →
        Module.Projective (Localization.AtPrime Q) (LocalizedModule Q.primeCompl M)) →
      (∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of A M) (ModuleCat.of A A) i)) →
      (∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of A M) (ModuleCat.of A M) i)) →
      Module.Projective A M

section

/- Section 1: Ext congruence, dimension shifting, and flat / faithfully flat base change -/

private lemma ext_subsingleton_congr
    {R : Type u} [CommRing R]
    {M₁ M₂ N₁ N₂ : Type u} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    (eM : M₁ ≃ₗ[R] M₂) (eN : N₁ ≃ₗ[R] N₂) (n : ℕ) :
    Subsingleton (Abelian.Ext (ModuleCat.of R M₁) (ModuleCat.of R N₁) n) ↔
      Subsingleton (Abelian.Ext (ModuleCat.of R M₂) (ModuleCat.of R N₂) n) := by
  have fwd : ∀ {A₁ A₂ B₁ B₂ : Type u}
      [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂]
      [AddCommGroup B₁] [Module R B₁] [AddCommGroup B₂] [Module R B₂]
      (fM : A₁ ≃ₗ[R] A₂) (fN : B₁ ≃ₗ[R] B₂),
      Subsingleton (Abelian.Ext (ModuleCat.of R A₁) (ModuleCat.of R B₁) n) →
      Subsingleton (Abelian.Ext (ModuleCat.of R A₂) (ModuleCat.of R B₂) n) := by
    intro A₁ A₂ B₁ B₂ _ _ _ _ _ _ _ _ fM fN hsub
    refine subsingleton_of_forall_eq 0 fun α => ?_
    let iM : ModuleCat.of R A₁ ≅ ModuleCat.of R A₂ := fM.toModuleIso
    let iN : ModuleCat.of R B₁ ≅ ModuleCat.of R B₂ := fN.toModuleIso
    let β : Abelian.Ext (ModuleCat.of R A₁) (ModuleCat.of R B₁) n :=
      (Abelian.Ext.mk₀ iM.hom).comp (α.comp (Abelian.Ext.mk₀ iN.inv) (add_zero n)) (zero_add n)
    have hβ : β = 0 := Subsingleton.elim β 0
    have h1 : (Abelian.Ext.mk₀ iM.inv).comp
        (β.comp (Abelian.Ext.mk₀ iN.hom) (add_zero n)) (zero_add n) = 0 := by
      rw [hβ, Abelian.Ext.zero_comp, Abelian.Ext.comp_zero]
    have h2 : (Abelian.Ext.mk₀ iM.inv).comp
        (β.comp (Abelian.Ext.mk₀ iN.hom) (add_zero n)) (zero_add n) = α := by
      dsimp only [β]
      rw [Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ iM.hom)
            (α.comp (Abelian.Ext.mk₀ iN.inv) (add_zero n)) (Abelian.Ext.mk₀ iN.hom)
            (zero_add n) (add_zero n) (by omega),
          Abelian.Ext.comp_assoc α (Abelian.Ext.mk₀ iN.inv) (Abelian.Ext.mk₀ iN.hom)
            (add_zero n) (zero_add 0) (by omega),
          Abelian.Ext.mk₀_comp_mk₀, iN.inv_hom_id, Abelian.Ext.comp_mk₀_id,
          ← Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ iM.inv) (Abelian.Ext.mk₀ iM.hom) α
            (zero_add 0) (zero_add n) (by omega),
          Abelian.Ext.mk₀_comp_mk₀, iM.inv_hom_id, Abelian.Ext.mk₀_id_comp]
    rw [← h2, h1]
  exact ⟨fwd eM eN, fwd eM.symm eN.symm⟩

private lemma ext_subsingleton_fin_pi
    {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M]
    (b n : ℕ)
    (hR : Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R R) n)) :
    Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R (Fin b → R)) n) := by
  classical
  refine subsingleton_of_forall_eq 0 fun α => ?_
  let f : Fin b → (ModuleCat.of R (Fin b → R) ⟶ ModuleCat.of R (Fin b → R)) := fun k =>
    ModuleCat.ofHom (LinearMap.proj (R := R) (φ := fun _ : Fin b => R) k) ≫
      ModuleCat.ofHom (LinearMap.single R (fun _ : Fin b => R) k)
  have hid : (𝟙 (ModuleCat.of R (Fin b → R))) = ∑ k : Fin b, f k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    ext j
    change v j = (∑ k : Fin b, f k) v j
    have hsum : ∀ (s : Finset (Fin b)),
        ((∑ k ∈ s, f k) : ModuleCat.of R (Fin b → R) ⟶ ModuleCat.of R (Fin b → R)) v =
          ∑ k ∈ s, (f k) v := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        change (f a) v + (∑ k ∈ s, f k) v = (f a) v + ∑ k ∈ s, (f k) v
        rw [ih]
    rw [hsum, Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp [f]
    · intro k _ hkj
      simp [f, hkj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  calc α = α.comp (Abelian.Ext.mk₀ (𝟙 (ModuleCat.of R (Fin b → R)))) (add_zero n) :=
        (Abelian.Ext.comp_mk₀_id α).symm
    _ = α.comp (Abelian.Ext.mk₀ (∑ k : Fin b, f k)) (add_zero n) := by rw [hid]
    _ = α.comp (∑ k : Fin b, Abelian.Ext.mk₀ (f k)) (add_zero n) := by rw [Abelian.Ext.mk₀_sum]
    _ = ∑ k : Fin b, α.comp (Abelian.Ext.mk₀ (f k)) (add_zero n) := Abelian.Ext.comp_sum _ _ _
    _ = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      dsimp only [f]
      rw [← Abelian.Ext.mk₀_comp_mk₀,
        ← Abelian.Ext.comp_assoc α
          (Abelian.Ext.mk₀ (ModuleCat.ofHom (LinearMap.proj (R := R) (φ := fun _ : Fin b => R) k)))
          (Abelian.Ext.mk₀ (ModuleCat.ofHom (LinearMap.single R (fun _ : Fin b => R) k)))
          (add_zero n) (zero_add 0) (by omega)]
      have h0 : α.comp
          (Abelian.Ext.mk₀ (ModuleCat.ofHom (LinearMap.proj (R := R) (φ := fun _ : Fin b => R) k)))
          (add_zero n) = 0 := Subsingleton.elim _ 0
      rw [h0, Abelian.Ext.zero_comp]

private lemma subsingleton_ext_one_iff_surjective
    {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {a : ℕ} (π : (Fin a → R) →ₗ[R] M) (hπ : Function.Surjective π) :
    Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R N) 1) ↔
      Function.Surjective (fun f : (Fin a → R) →ₗ[R] N => f.comp (LinearMap.ker π).subtype) := by
  let K := LinearMap.ker π
  let S : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk (ModuleCat.ofHom K.subtype) (ModuleCat.ofHom π) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro k
      exact k.2)
  have hS : S.ShortExact := {
    exact := by
      rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      intro v
      simp [S, K]
    mono_f := (ModuleCat.mono_iff_injective S.f).mpr K.injective_subtype
    epi_g := (ModuleCat.epi_iff_surjective S.g).mpr hπ
  }
  have hFproj : Projective (ModuleCat.of R (Fin a → R)) :=
    (IsProjective.iff_projective (R := R) (ModuleCat.of R (Fin a → R))).mp inferInstance
  have hExtF : Subsingleton (Abelian.Ext S.X₂ (ModuleCat.of R N) 1) :=
    Abelian.Ext.subsingleton_of_projective (ModuleCat.of R (Fin a → R)) (ModuleCat.of R N) 0
  constructor
  · intro hsub g
    have hx1 : hS.extClass.comp (Abelian.Ext.mk₀ (ModuleCat.ofHom g)) (add_zero 1) = 0 :=
      Subsingleton.elim _ 0
    obtain ⟨x2, hx2⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS (ModuleCat.of R N)
      (Abelian.Ext.mk₀ (ModuleCat.ofHom g)) (add_zero 1) hx1
    let fHom : S.X₂ ⟶ ModuleCat.of R N := Abelian.Ext.addEquiv₀ x2
    refine ⟨fHom.hom, ?_⟩
    have hx2' : Abelian.Ext.mk₀ (CategoryStruct.comp S.f fHom) = Abelian.Ext.mk₀ (ModuleCat.ofHom g) := by
      rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_addEquiv₀_apply]
      exact hx2
    have hcomp : CategoryStruct.comp S.f fHom = ModuleCat.ofHom g :=
      Abelian.Ext.addEquiv₀.symm.injective hx2'
    exact congrArg ModuleCat.Hom.hom hcomp
  · intro hsurj
    refine subsingleton_of_forall_eq 0 fun e => ?_
    have hge : (Abelian.Ext.mk₀ S.g).comp e (zero_add 1) = 0 := Subsingleton.elim _ 0
    obtain ⟨x1, hx1⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS (ModuleCat.of R N) e hge (add_zero 1)
    let gHom : S.X₁ ⟶ ModuleCat.of R N := Abelian.Ext.addEquiv₀ x1
    obtain ⟨f, hf⟩ := hsurj gHom.hom
    have hx1_eq : x1 = (Abelian.Ext.mk₀ S.f).comp
        (Abelian.Ext.mk₀ (ModuleCat.ofHom f)) (zero_add 0) := by
      rw [Abelian.Ext.mk₀_comp_mk₀]
      have hgf : CategoryStruct.comp S.f (ModuleCat.ofHom f) = gHom := by
        apply ModuleCat.hom_ext
        exact hf
      rw [hgf, Abelian.Ext.mk₀_addEquiv₀_apply]
    rw [← hx1, hx1_eq]
    simp only [ShortComplex.ShortExact.extClass_comp_assoc]

private lemma subsingleton_ext_succ_succ_iff
    {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {a : ℕ} (π : (Fin a → R) →ₗ[R] M) (hπ : Function.Surjective π) (n : ℕ) :
    Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R N) (n + 2)) ↔
      Subsingleton (Abelian.Ext (ModuleCat.of R (LinearMap.ker π)) (ModuleCat.of R N) (n + 1)) := by
  let K := LinearMap.ker π
  let S : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk (ModuleCat.ofHom K.subtype) (ModuleCat.ofHom π) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro k
      exact k.2)
  have hS : S.ShortExact := {
    exact := by
      rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      intro v
      simp [S, K]
    mono_f := (ModuleCat.mono_iff_injective S.f).mpr K.injective_subtype
    epi_g := (ModuleCat.epi_iff_surjective S.g).mpr hπ
  }
  have hFproj : Projective (ModuleCat.of R (Fin a → R)) :=
    (IsProjective.iff_projective (R := R) (ModuleCat.of R (Fin a → R))).mp inferInstance
  have hExtF1 : Subsingleton (Abelian.Ext S.X₂ (ModuleCat.of R N) (n + 1)) :=
    Abelian.Ext.subsingleton_of_projective (ModuleCat.of R (Fin a → R)) (ModuleCat.of R N) n
  have hExtF2 : Subsingleton (Abelian.Ext S.X₂ (ModuleCat.of R N) (n + 2)) :=
    Abelian.Ext.subsingleton_of_projective (ModuleCat.of R (Fin a → R)) (ModuleCat.of R N) (n + 1)
  have hn : 1 + (n + 1) = n + 2 := by omega
  constructor
  · intro hsub
    refine subsingleton_of_forall_eq 0 fun x1 => ?_
    have hx1 : hS.extClass.comp x1 hn = 0 := Subsingleton.elim _ 0
    obtain ⟨x2, hx2⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS (ModuleCat.of R N) x1 hn hx1
    have hx20 : x2 = 0 := Subsingleton.elim x2 0
    rw [← hx2, hx20, Abelian.Ext.comp_zero]
  · intro hsub
    refine subsingleton_of_forall_eq 0 fun x3 => ?_
    have hx3 : (Abelian.Ext.mk₀ S.g).comp x3 (zero_add (n + 2)) = 0 := Subsingleton.elim _ 0
    obtain ⟨x1, hx1⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS (ModuleCat.of R N) x3 hx3 hn
    have hx10 : x1 = 0 := Subsingleton.elim x1 0
    rw [← hx1, hx10, Abelian.Ext.comp_zero]

private lemma exists_hom_baseChange_equiv_fin
    {A : Type u₁} [CommRing A]
    {B : Type u₂} [CommRing B] [Algebra A B]
    (a : ℕ) (N₀ : Type u₁) [AddCommGroup N₀] [Module A N₀] :
    ∃ e : (B ⊗[A] ((Fin a → A) →ₗ[A] N₀)) ≃ₗ[B] ((B ⊗[A] (Fin a → A)) →ₗ[B] (B ⊗[A] N₀)),
      ∀ (b : B) (f : (Fin a → A) →ₗ[A] N₀) (r : B) (v : Fin a → A),
        e (b ⊗ₜ[A] f) (r ⊗ₜ[A] v) = (b * r) ⊗ₜ[A] f v := by
  classical
  let φBilin : B →ₗ[B] ((Fin a → A) →ₗ[A] N₀) →ₗ[A] ((B ⊗[A] (Fin a → A)) →ₗ[B] (B ⊗[A] N₀)) := {
    toFun := fun b =>
      { toFun := fun f => b • LinearMap.baseChange B f
        map_add' := fun f₁ f₂ => by
          apply LinearMap.ext; intro x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | add x₁ x₂ h₁ h₂ =>
            change (b • LinearMap.baseChange B (f₁ + f₂)) (x₁ + x₂) =
              (b • LinearMap.baseChange B f₁ + b • LinearMap.baseChange B f₂) (x₁ + x₂)
            rw [map_add, map_add, h₁, h₂]
          | tmul r v => simp [smul_add]
        map_smul' := fun c f => by
          apply LinearMap.ext; intro x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | add x₁ x₂ h₁ h₂ =>
            change (b • LinearMap.baseChange B (c • f)) (x₁ + x₂) =
              (c • (b • LinearMap.baseChange B f)) (x₁ + x₂)
            rw [map_add, map_add, h₁, h₂]
            rfl
          | tmul r v =>
            simp only [LinearMap.smul_apply, LinearMap.baseChange_tmul, RingHom.id_apply,
              TensorProduct.smul_tmul', TensorProduct.tmul_smul, Algebra.smul_def]
            congr 1; ring }
    map_add' := fun b₁ b₂ => by
      apply LinearMap.ext; intro f; apply LinearMap.ext; intro x
      simp [add_smul]
    map_smul' := fun b₁ b₂ => by
      apply LinearMap.ext; intro f; apply LinearMap.ext; intro x
      simp [mul_smul]
  }
  let φ : (B ⊗[A] ((Fin a → A) →ₗ[A] N₀)) →ₗ[B] ((B ⊗[A] (Fin a → A)) →ₗ[B] (B ⊗[A] N₀)) :=
    AlgebraTensorModule.lift φBilin
  have hφ_tmul : ∀ (b : B) (f : (Fin a → A) →ₗ[A] N₀) (r : B) (v : Fin a → A),
      φ (b ⊗ₜ[A] f) (r ⊗ₜ[A] v) = (b * r) ⊗ₜ[A] f v := by
    intro b f r v
    change (b • LinearMap.baseChange B f) (r ⊗ₜ[A] v) = (b * r) ⊗ₜ[A] f v
    simp [TensorProduct.smul_tmul']
  let e1 : ((Fin a → A) →ₗ[A] N₀) ≃ₗ[A] (Fin a → N₀) := {
    toFun := fun f k => f (Pi.single k 1)
    invFun := fun g =>
      { toFun := fun v => ∑ k : Fin a, v k • g k
        map_add' := fun v w => by simp [add_smul, Finset.sum_add_distrib]
        map_smul' := fun c v => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum]
          refine Finset.sum_congr rfl fun k _ => by rw [mul_smul] }
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun f => by
      apply LinearMap.ext; intro v
      have hv : v = ∑ k : Fin a, v k • Pi.single k (1 : A) := by
        ext j; simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hv]
      simp [map_sum, map_smul]
    right_inv := fun g => by
      ext k
      simp [Pi.single_apply]
  }
  let e2Bilin : B →ₗ[B] (Fin a → N₀) →ₗ[A] (Fin a → B ⊗[A] N₀) := {
    toFun := fun b =>
      { toFun := fun g k => b ⊗ₜ[A] g k
        map_add' := fun g₁ g₂ => by ext k; exact TensorProduct.tmul_add b (g₁ k) (g₂ k)
        map_smul' := fun c g => by ext k; simp [TensorProduct.tmul_smul] }
    map_add' := fun b₁ b₂ => by
      apply LinearMap.ext; intro g; ext k; exact TensorProduct.add_tmul b₁ b₂ (g k)
    map_smul' := fun b₁ b₂ => by
      apply LinearMap.ext; intro g; ext k
      change (b₁ * b₂) ⊗ₜ[A] g k = b₁ • (b₂ ⊗ₜ[A] g k)
      rw [TensorProduct.smul_tmul', smul_eq_mul]
  }
  let e2Fwd : (B ⊗[A] (Fin a → N₀)) →ₗ[B] (Fin a → B ⊗[A] N₀) :=
    AlgebraTensorModule.lift e2Bilin
  let e2Bwd : (Fin a → B ⊗[A] N₀) →ₗ[B] (B ⊗[A] (Fin a → N₀)) := {
    toFun := fun h =>
      ∑ k : Fin a, LinearMap.baseChange B (LinearMap.single A (fun _ : Fin a => N₀) k) (h k)
    map_add' := fun h₁ h₂ => by simp [Finset.sum_add_distrib]
    map_smul' := fun c h => by simp [Finset.smul_sum]
  }
  have he2_left : ∀ x : B ⊗[A] (Fin a → N₀), e2Bwd (e2Fwd x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x₁ x₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
    | tmul b g =>
      have hg : g = ∑ k : Fin a, LinearMap.single A (fun _ : Fin a => N₀) k (g k) := by
        ext j; simp [Finset.sum_apply, LinearMap.single_apply]
      change ∑ k : Fin a, LinearMap.baseChange B
        (LinearMap.single A (fun _ : Fin a => N₀) k) (b ⊗ₜ[A] g k) = b ⊗ₜ[A] g
      conv_rhs => rw [hg, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rfl
  have he2_right : ∀ h : Fin a → B ⊗[A] N₀, e2Fwd (e2Bwd h) = h := by
    intro h
    ext j
    change e2Fwd (∑ k : Fin a, LinearMap.baseChange B
      (LinearMap.single A (fun _ : Fin a => N₀) k) (h k)) j = h j
    rw [map_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · generalize h j = z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, Pi.add_apply, h₁, h₂]
      | tmul b n =>
        change b ⊗ₜ[A] (LinearMap.single A (fun _ : Fin a => N₀) j n j) = b ⊗ₜ[A] n
        simp
    · intro k _ hkj
      generalize h k = z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, Pi.add_apply, h₁, h₂, add_zero]
      | tmul b n =>
        change b ⊗ₜ[A] (LinearMap.single A (fun _ : Fin a => N₀) k n j) = 0
        simp [LinearMap.single_apply, hkj]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  let e2 : (B ⊗[A] (Fin a → N₀)) ≃ₗ[B] (Fin a → B ⊗[A] N₀) :=
    LinearEquiv.ofLinearMap e2Fwd e2Bwd (LinearMap.ext he2_right) (LinearMap.ext he2_left)
  let eLHS : (B ⊗[A] ((Fin a → A) →ₗ[A] N₀)) ≃ₗ[B] (Fin a → B ⊗[A] N₀) :=
    (AlgebraTensorModule.congr (LinearEquiv.refl B B) e1).trans e2
  let eRHS : ((B ⊗[A] (Fin a → A)) →ₗ[B] (B ⊗[A] N₀)) ≃ₗ[B] (Fin a → B ⊗[A] N₀) := {
    toFun := fun ψ k => ψ (1 ⊗ₜ[A] Pi.single k 1)
    invFun := fun h =>
      { toFun := fun x =>
          ∑ k : Fin a, (TensorProduct.piScalarRight A B B (Fin a) x k) • h k
        map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
        map_smul' := fun c x => by
          simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum]
          refine Finset.sum_congr rfl fun k _ => by rw [mul_smul] }
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun ψ => by
      apply LinearMap.ext; intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x₁ x₂ h₁ h₂ =>
        change ∑ k : Fin a, (TensorProduct.piScalarRight A B B (Fin a) (x₁ + x₂) k) •
            ψ (1 ⊗ₜ[A] Pi.single k 1) = ψ (x₁ + x₂)
        simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
        exact congrArg₂ (· + ·) h₁ h₂
      | tmul r v =>
        have hv : v = ∑ k : Fin a, v k • Pi.single k (1 : A) := by
          ext j; simp [Finset.sum_apply, Pi.single_apply]
        have hx : r ⊗ₜ[A] v = ∑ k : Fin a, (r * algebraMap A B (v k)) • (1 ⊗ₜ[A] Pi.single k (1 : A)) := by
          conv_lhs => rw [hv]
          rw [TensorProduct.tmul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
            Algebra.smul_def, mul_comm]
        have hpi : ∀ k : Fin a,
            TensorProduct.piScalarRight A B B (Fin a) (r ⊗ₜ[A] v) k = r * algebraMap A B (v k) := by
          intro k
          simp [Algebra.smul_def, mul_comm]
        change ∑ k : Fin a, (TensorProduct.piScalarRight A B B (Fin a) (r ⊗ₜ[A] v) k) •
            ψ (1 ⊗ₜ[A] Pi.single k 1) = ψ (r ⊗ₜ[A] v)
        conv_rhs => rw [hx, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hpi k, map_smul]
    right_inv := fun h => by
      ext k
      change ∑ j : Fin a, (TensorProduct.piScalarRight A B B (Fin a)
        (1 ⊗ₜ[A] Pi.single k (1 : A)) j) • h j = h k
      rw [Finset.sum_eq_single k]
      · have hk : TensorProduct.piScalarRight A B B (Fin a) (1 ⊗ₜ[A] Pi.single k (1 : A)) k = 1 := by
          simp
        rw [hk, one_smul]
      · intro j _ hjk
        have hj : TensorProduct.piScalarRight A B B (Fin a) (1 ⊗ₜ[A] Pi.single k (1 : A)) j = 0 := by
          simp [hjk]
        rw [hj, zero_smul]
      · intro hk; exact absurd (Finset.mem_univ k) hk
  }
  have hcomp : ∀ x : B ⊗[A] ((Fin a → A) →ₗ[A] N₀), eRHS (φ x) = eLHS x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x₁ x₂ h₁ h₂ => simp [h₁, h₂]
    | tmul b f =>
      ext k
      change φ (b ⊗ₜ[A] f) (1 ⊗ₜ[A] Pi.single k 1) = b ⊗ₜ[A] f (Pi.single k 1)
      rw [hφ_tmul, mul_one]
  have hbij : Function.Bijective φ := by
    have heq : (φ : _ → _) = eRHS.symm ∘ eLHS := by
      funext x
      exact eRHS.injective (by simp [hcomp x])
    rw [heq]
    exact eRHS.symm.bijective.comp eLHS.bijective
  exact ⟨LinearEquiv.ofBijective φ hbij, hφ_tmul⟩

private lemma exists_hom_baseChange_equiv
    {A : Type u₁} [CommRing A] [IsNoetherianRing A]
    {B : Type u₂} [CommRing B] [Algebra A B] [Module.Flat A B]
    (M₀ : Type u₁) [AddCommGroup M₀] [Module A M₀] [Module.Finite A M₀]
    (N₀ : Type u₁) [AddCommGroup N₀] [Module A N₀] :
    ∃ e : (B ⊗[A] (M₀ →ₗ[A] N₀)) ≃ₗ[B] ((B ⊗[A] M₀) →ₗ[B] (B ⊗[A] N₀)),
      ∀ (b : B) (f : M₀ →ₗ[A] N₀) (r : B) (m : M₀),
        e (b ⊗ₜ[A] f) (r ⊗ₜ[A] m) = (b * r) ⊗ₜ[A] f m := by
  classical
  let φBilin : B →ₗ[B] (M₀ →ₗ[A] N₀) →ₗ[A] ((B ⊗[A] M₀) →ₗ[B] (B ⊗[A] N₀)) := {
    toFun := fun b =>
      { toFun := fun f => b • LinearMap.baseChange B f
        map_add' := fun f₁ f₂ => by
          apply LinearMap.ext; intro x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | add x₁ x₂ h₁ h₂ =>
            change (b • LinearMap.baseChange B (f₁ + f₂)) (x₁ + x₂) =
              (b • LinearMap.baseChange B f₁ + b • LinearMap.baseChange B f₂) (x₁ + x₂)
            rw [map_add, map_add, h₁, h₂]
          | tmul r m => simp [smul_add]
        map_smul' := fun c f => by
          apply LinearMap.ext; intro x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | add x₁ x₂ h₁ h₂ =>
            change (b • LinearMap.baseChange B (c • f)) (x₁ + x₂) =
              (c • (b • LinearMap.baseChange B f)) (x₁ + x₂)
            rw [map_add, map_add, h₁, h₂]
            rfl
          | tmul r m =>
            simp only [LinearMap.smul_apply, LinearMap.baseChange_tmul, RingHom.id_apply,
              TensorProduct.smul_tmul', TensorProduct.tmul_smul, Algebra.smul_def]
            congr 1; ring }
    map_add' := fun b₁ b₂ => by
      apply LinearMap.ext; intro f; apply LinearMap.ext; intro x; simp [add_smul]
    map_smul' := fun b₁ b₂ => by
      apply LinearMap.ext; intro f; apply LinearMap.ext; intro x; simp [mul_smul]
  }
  let φ : (B ⊗[A] (M₀ →ₗ[A] N₀)) →ₗ[B] ((B ⊗[A] M₀) →ₗ[B] (B ⊗[A] N₀)) :=
    AlgebraTensorModule.lift φBilin
  have hφ_tmul : ∀ (b : B) (f : M₀ →ₗ[A] N₀) (r : B) (m : M₀),
      φ (b ⊗ₜ[A] f) (r ⊗ₜ[A] m) = (b * r) ⊗ₜ[A] f m := by
    intro b f r m
    change (b • LinearMap.baseChange B f) (r ⊗ₜ[A] m) = (b * r) ⊗ₜ[A] f m
    simp [TensorProduct.smul_tmul']
  obtain ⟨a, π, hπ⟩ := Module.Finite.exists_fin' A M₀
  have _ : Module.Finite A (LinearMap.ker π) := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  obtain ⟨c, σ, hσ⟩ := Module.Finite.exists_fin' A (LinearMap.ker π)
  let d : (Fin c → A) →ₗ[A] (Fin a → A) := (LinearMap.ker π).subtype.comp σ
  have hd_exact : Function.Exact d π := by
    intro v
    constructor
    · intro hv
      obtain ⟨w, hw⟩ := hσ ⟨v, hv⟩
      exact ⟨w, congrArg Subtype.val hw⟩
    · rintro ⟨w, rfl⟩
      exact (σ w).2
  obtain ⟨eF0, heF0⟩ := exists_hom_baseChange_equiv_fin (A := A) (B := B) a N₀
  obtain ⟨eF1, heF1⟩ := exists_hom_baseChange_equiv_fin (A := A) (B := B) c N₀
  let preπ : (M₀ →ₗ[A] N₀) →ₗ[A] ((Fin a → A) →ₗ[A] N₀) := {
    toFun := fun f => f.comp π
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
  }
  let pred : ((Fin a → A) →ₗ[A] N₀) →ₗ[A] ((Fin c → A) →ₗ[A] N₀) := {
    toFun := fun f => f.comp d
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
  }
  have hpreπ_inj : Function.Injective preπ := by
    intro f₁ f₂ h
    apply LinearMap.ext; intro m
    obtain ⟨v, rfl⟩ := hπ m
    exact LinearMap.congr_fun h v
  have hpre_exact : Function.Exact preπ pred := by
    intro f
    constructor
    · intro hf
      have hker : LinearMap.ker π ≤ LinearMap.ker f := by
        intro v hv
        obtain ⟨w, hw⟩ := (hd_exact v).mp hv
        rw [← hw]
        exact LinearMap.congr_fun hf w
      let g : M₀ →ₗ[A] N₀ :=
        ((LinearMap.ker π).liftQ f hker).comp (LinearMap.quotKerEquivOfSurjective π hπ).symm.toLinearMap
      refine ⟨g, ?_⟩
      apply LinearMap.ext; intro v
      change ((LinearMap.ker π).liftQ f hker)
        ((LinearMap.quotKerEquivOfSurjective π hπ).symm (π v)) = f v
      have hq : (LinearMap.quotKerEquivOfSurjective π hπ).symm (π v) = Submodule.Quotient.mk v :=
        (LinearMap.quotKerEquivOfSurjective π hπ).injective (by simp)
      rw [hq]
      rfl
    · rintro ⟨g, rfl⟩
      apply LinearMap.ext; intro w
      change g (π (d w)) = 0
      rw [(hd_exact (d w)).mpr ⟨w, rfl⟩, map_zero]
  have hlT_inj : Function.Injective (LinearMap.lTensor B preπ) :=
    Module.Flat.lTensor_preserves_injective_linearMap preπ hpreπ_inj
  have hlT_exact : Function.Exact (LinearMap.lTensor B preπ) (LinearMap.lTensor B pred) :=
    Module.Flat.lTensor_exact (R := A) (M := B) hpre_exact
  have hπB_surj : Function.Surjective (LinearMap.baseChange B π) :=
    LinearMap.lTensor_surjective B hπ
  have hdB_exact : Function.Exact (LinearMap.baseChange B d) (LinearMap.baseChange B π) :=
    Module.Flat.lTensor_exact (R := A) (M := B) hd_exact
  have hnatπ : ∀ x : B ⊗[A] (M₀ →ₗ[A] N₀),
      (φ x).comp (LinearMap.baseChange B π) = eF0 (LinearMap.lTensor B preπ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x₁ x₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, LinearMap.add_comp, h₁, h₂]
    | tmul b f =>
      apply LinearMap.ext; intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z₁ z₂ h₁ h₂ =>
        rw [map_add, map_add, h₁, h₂]
      | tmul r v =>
        change φ (b ⊗ₜ[A] f) (r ⊗ₜ[A] π v) = eF0 (b ⊗ₜ[A] (f.comp π)) (r ⊗ₜ[A] v)
        rw [hφ_tmul, heF0]
        rfl
  have hnatd : ∀ y : B ⊗[A] ((Fin a → A) →ₗ[A] N₀),
      (eF0 y).comp (LinearMap.baseChange B d) = eF1 (LinearMap.lTensor B pred y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, LinearMap.add_comp, h₁, h₂]
    | tmul b f =>
      apply LinearMap.ext; intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z₁ z₂ h₁ h₂ =>
        rw [map_add, map_add, h₁, h₂]
      | tmul r w =>
        change eF0 (b ⊗ₜ[A] f) (r ⊗ₜ[A] d w) = eF1 (b ⊗ₜ[A] (f.comp d)) (r ⊗ₜ[A] w)
        rw [heF0, heF1]
        rfl
  have hbij : Function.Bijective φ := by
    constructor
    · intro x₁ x₂ hx
      apply hlT_inj
      apply eF0.injective
      rw [← hnatπ x₁, ← hnatπ x₂, hx]
    · intro ψ
      let y := eF0.symm (ψ.comp (LinearMap.baseChange B π))
      have hy0 : LinearMap.lTensor B pred y = 0 := by
        apply eF1.injective
        rw [map_zero, ← hnatd y]
        change (eF0 (eF0.symm (ψ.comp (LinearMap.baseChange B π)))).comp (LinearMap.baseChange B d) = 0
        rw [eF0.apply_symm_apply]
        apply LinearMap.ext; intro z
        change ψ (LinearMap.baseChange B π (LinearMap.baseChange B d z)) = 0
        rw [(hdB_exact _).mpr ⟨z, rfl⟩, map_zero]
      obtain ⟨x, hx⟩ := (hlT_exact y).mp hy0
      refine ⟨x, ?_⟩
      apply LinearMap.ext; intro z
      obtain ⟨w, rfl⟩ := hπB_surj z
      have h1 : (φ x).comp (LinearMap.baseChange B π) = ψ.comp (LinearMap.baseChange B π) := by
        rw [hnatπ x, hx]
        exact eF0.apply_symm_apply _
      exact LinearMap.congr_fun h1 w
  exact ⟨LinearEquiv.ofBijective φ hbij, hφ_tmul⟩

private lemma surjective_of_lTensor_surjective
    {A : Type u₁} [CommRing A]
    {B : Type u₂} [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    {P Q : Type u₁} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (α : P →ₗ[A] Q) (h : Function.Surjective (LinearMap.lTensor B α)) :
    Function.Surjective α := by
  let C := Q ⧸ LinearMap.range α
  have hq : Function.Surjective (LinearMap.lTensor B (LinearMap.range α).mkQ) :=
    LinearMap.lTensor_surjective B (Submodule.mkQ_surjective _)
  have hcomp0 : (LinearMap.lTensor B (LinearMap.range α).mkQ).comp (LinearMap.lTensor B α) = 0 := by
    rw [← LinearMap.lTensor_comp]
    have h0 : (LinearMap.range α).mkQ.comp α = 0 := by
      apply LinearMap.ext; intro p
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨p, rfl⟩
    rw [h0, LinearMap.lTensor_zero]
  have hsubB : Subsingleton (B ⊗[A] C) := by
    refine subsingleton_of_forall_eq 0 fun y => ?_
    obtain ⟨z, rfl⟩ := hq y
    obtain ⟨w, rfl⟩ := h z
    exact LinearMap.congr_fun hcomp0 w
  have hsubC : Subsingleton C := Module.FaithfullyFlat.lTensor_reflects_triviality A B C
  intro q
  have h0 : (LinearMap.range α).mkQ q = 0 := Subsingleton.elim _ 0
  exact (Submodule.Quotient.mk_eq_zero _).mp h0

private lemma flat_baseChange_ext_subsingleton
    {A : Type u₁} [CommRing A] [IsNoetherianRing A]
    {B : Type (max u₁ u₂)} [CommRing B] [Algebra A B] [Module.Flat A B]
    (n : ℕ) :
    ∀ (M₀ : Type u₁) [AddCommGroup M₀] [Module A M₀] [Module.Finite A M₀]
      (N₀ : Type u₁) [AddCommGroup N₀] [Module A N₀],
      Subsingleton (Abelian.Ext (ModuleCat.of A M₀) (ModuleCat.of A N₀) (n + 1)) →
      Subsingleton (Abelian.Ext (ModuleCat.of B (B ⊗[A] M₀)) (ModuleCat.of B (B ⊗[A] N₀)) (n + 1)) := by
  induction n with
  | zero =>
    intro M₀ _ _ _ N₀ _ _ hsub
    obtain ⟨a, π, hπ⟩ := Module.Finite.exists_fin' A M₀
    let K₀ := LinearMap.ker π
    have _ : Module.Finite A K₀ := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    let eF : B ⊗[A] (Fin a → A) ≃ₗ[B] (Fin a → B) := TensorProduct.piScalarRight A B B (Fin a)
    let πB : (Fin a → B) →ₗ[B] (B ⊗[A] M₀) := (LinearMap.baseChange B π).comp eF.symm.toLinearMap
    have hπB : Function.Surjective πB :=
      (LinearMap.lTensor_surjective B hπ).comp eF.symm.surjective
    let KB := LinearMap.ker πB
    have hker_exact : Function.Exact K₀.subtype π := fun v => by simp [K₀]
    have hkerB_exact : Function.Exact (LinearMap.baseChange B K₀.subtype) (LinearMap.baseChange B π) :=
      Module.Flat.lTensor_exact (R := A) (M := B) hker_exact
    have hkerB_inj : Function.Injective (LinearMap.baseChange B K₀.subtype) :=
      Module.Flat.lTensor_preserves_injective_linearMap K₀.subtype K₀.injective_subtype
    let ιKB : (B ⊗[A] K₀) →ₗ[B] KB := {
      toFun := fun z => ⟨eF (LinearMap.baseChange B K₀.subtype z), by
        change LinearMap.baseChange B π (eF.symm (eF (LinearMap.baseChange B K₀.subtype z))) = 0
        rw [eF.symm_apply_apply]
        exact (hkerB_exact _).mpr ⟨z, rfl⟩⟩
      map_add' := fun _ _ => Subtype.ext (by simp)
      map_smul' := fun _ _ => Subtype.ext (by simp)
    }
    have hιKB_bij : Function.Bijective ιKB := by
      constructor
      · intro z₁ z₂ h
        exact hkerB_inj (eF.injective (congrArg Subtype.val h))
      · rintro ⟨w, hw⟩
        have hw' : LinearMap.baseChange B π (eF.symm w) = 0 := hw
        obtain ⟨z, hz⟩ := (hkerB_exact (eF.symm w)).mp hw'
        refine ⟨z, Subtype.ext ?_⟩
        change eF (LinearMap.baseChange B K₀.subtype z) = w
        rw [hz, eF.apply_symm_apply]
    let eK : (B ⊗[A] K₀) ≃ₗ[B] KB := LinearEquiv.ofBijective ιKB hιKB_bij
    change Subsingleton (Abelian.Ext (ModuleCat.of B (B ⊗[A] M₀)) (ModuleCat.of B (B ⊗[A] N₀)) 1)
    rw [subsingleton_ext_one_iff_surjective πB hπB]
    have hsurjA : Function.Surjective
        (fun f : (Fin a → A) →ₗ[A] N₀ => f.comp K₀.subtype) :=
      (subsingleton_ext_one_iff_surjective π hπ).mp hsub
    let preA : ((Fin a → A) →ₗ[A] N₀) →ₗ[A] (K₀ →ₗ[A] N₀) := {
      toFun := fun f => f.comp K₀.subtype
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
    }
    have hsurjTensor : Function.Surjective (LinearMap.lTensor B preA) :=
      LinearMap.lTensor_surjective B hsurjA
    obtain ⟨eHomF, heHomF⟩ := exists_hom_baseChange_equiv (A := A) (B := B) (Fin a → A) N₀
    obtain ⟨eHomK, heHomK⟩ := exists_hom_baseChange_equiv (A := A) (B := B) K₀ N₀
    intro gB
    let gB' : (B ⊗[A] K₀) →ₗ[B] (B ⊗[A] N₀) := gB.comp eK.toLinearMap
    obtain ⟨u, hu⟩ := hsurjTensor (eHomK.symm gB')
    let fB : (Fin a → B) →ₗ[B] (B ⊗[A] N₀) := (eHomF u).comp eF.symm.toLinearMap
    refine ⟨fB, ?_⟩
    apply LinearMap.ext; intro w
    obtain ⟨z, rfl⟩ := eK.surjective w
    have hnat : (eHomF u).comp (LinearMap.baseChange B K₀.subtype) =
        eHomK (LinearMap.lTensor B preA u) := by
      clear hu gB' gB fB z
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add u₁ u₂ h₁ h₂ =>
        rw [map_add, map_add, map_add, LinearMap.add_comp, h₁, h₂]
      | tmul b f =>
        apply LinearMap.ext; intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
        | tmul r k =>
          change eHomF (b ⊗ₜ[A] f) (r ⊗ₜ[A] K₀.subtype k) =
            eHomK (b ⊗ₜ[A] (f.comp K₀.subtype)) (r ⊗ₜ[A] k)
          rw [heHomF, heHomK]
          rfl
    change eHomF u (eF.symm (eF (LinearMap.baseChange B K₀.subtype z))) = gB (eK z)
    rw [eF.symm_apply_apply]
    have h1 := LinearMap.congr_fun hnat z
    rw [hu, eHomK.apply_symm_apply] at h1
    exact h1
  | succ n ih =>
    intro M₀ _ _ _ N₀ _ _ hsub
    obtain ⟨a, π, hπ⟩ := Module.Finite.exists_fin' A M₀
    let K₀ := LinearMap.ker π
    have _ : Module.Finite A K₀ := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    let eF : B ⊗[A] (Fin a → A) ≃ₗ[B] (Fin a → B) := TensorProduct.piScalarRight A B B (Fin a)
    let πB : (Fin a → B) →ₗ[B] (B ⊗[A] M₀) := (LinearMap.baseChange B π).comp eF.symm.toLinearMap
    have hπB : Function.Surjective πB :=
      (LinearMap.lTensor_surjective B hπ).comp eF.symm.surjective
    let KB := LinearMap.ker πB
    have hker_exact : Function.Exact K₀.subtype π := fun v => by simp [K₀]
    have hkerB_exact : Function.Exact (LinearMap.baseChange B K₀.subtype) (LinearMap.baseChange B π) :=
      Module.Flat.lTensor_exact (R := A) (M := B) hker_exact
    have hkerB_inj : Function.Injective (LinearMap.baseChange B K₀.subtype) :=
      Module.Flat.lTensor_preserves_injective_linearMap K₀.subtype K₀.injective_subtype
    let ιKB : (B ⊗[A] K₀) →ₗ[B] KB := {
      toFun := fun z => ⟨eF (LinearMap.baseChange B K₀.subtype z), by
        change LinearMap.baseChange B π (eF.symm (eF (LinearMap.baseChange B K₀.subtype z))) = 0
        rw [eF.symm_apply_apply]
        exact (hkerB_exact _).mpr ⟨z, rfl⟩⟩
      map_add' := fun _ _ => Subtype.ext (by simp)
      map_smul' := fun _ _ => Subtype.ext (by simp)
    }
    have hιKB_bij : Function.Bijective ιKB := by
      constructor
      · intro z₁ z₂ h
        exact hkerB_inj (eF.injective (congrArg Subtype.val h))
      · rintro ⟨w, hw⟩
        obtain ⟨z, hz⟩ := (hkerB_exact (eF.symm w)).mp hw
        refine ⟨z, Subtype.ext ?_⟩
        change eF (LinearMap.baseChange B K₀.subtype z) = w
        rw [hz, eF.apply_symm_apply]
    let eK : (B ⊗[A] K₀) ≃ₗ[B] KB := LinearEquiv.ofBijective ιKB hιKB_bij
    have hK₀ : Subsingleton (Abelian.Ext (ModuleCat.of A K₀) (ModuleCat.of A N₀) (n + 1)) :=
      (subsingleton_ext_succ_succ_iff π hπ n).mp hsub
    have hKB₀ := ih K₀ N₀ hK₀
    have hKB : Subsingleton (Abelian.Ext (ModuleCat.of B KB) (ModuleCat.of B (B ⊗[A] N₀)) (n + 1)) :=
      (ext_subsingleton_congr eK (LinearEquiv.refl B _) (n + 1)).mp hKB₀
    exact (subsingleton_ext_succ_succ_iff πB hπB n).mpr hKB

private lemma faithfullyFlat_descend_ext_subsingleton
    {A : Type u₁} [CommRing A] [IsNoetherianRing A]
    {B : Type (max u₁ u₂)} [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (n : ℕ) :
    ∀ (M₀ : Type u₁) [AddCommGroup M₀] [Module A M₀] [Module.Finite A M₀]
      (N₀ : Type u₁) [AddCommGroup N₀] [Module A N₀],
      Subsingleton (Abelian.Ext (ModuleCat.of B (B ⊗[A] M₀)) (ModuleCat.of B (B ⊗[A] N₀)) (n + 1)) →
      Subsingleton (Abelian.Ext (ModuleCat.of A M₀) (ModuleCat.of A N₀) (n + 1)) := by
  induction n with
  | zero =>
    intro M₀ _ _ _ N₀ _ _ hsub
    obtain ⟨a, π, hπ⟩ := Module.Finite.exists_fin' A M₀
    let K₀ := LinearMap.ker π
    have _ : Module.Finite A K₀ := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    let eF : B ⊗[A] (Fin a → A) ≃ₗ[B] (Fin a → B) := TensorProduct.piScalarRight A B B (Fin a)
    let πB : (Fin a → B) →ₗ[B] (B ⊗[A] M₀) := (LinearMap.baseChange B π).comp eF.symm.toLinearMap
    have hπB : Function.Surjective πB :=
      (LinearMap.lTensor_surjective B hπ).comp eF.symm.surjective
    let KB := LinearMap.ker πB
    have hker_exact : Function.Exact K₀.subtype π := fun v => by simp [K₀]
    have hkerB_exact : Function.Exact (LinearMap.baseChange B K₀.subtype) (LinearMap.baseChange B π) :=
      Module.Flat.lTensor_exact (R := A) (M := B) hker_exact
    have hkerB_inj : Function.Injective (LinearMap.baseChange B K₀.subtype) :=
      Module.Flat.lTensor_preserves_injective_linearMap K₀.subtype K₀.injective_subtype
    let ιKB : (B ⊗[A] K₀) →ₗ[B] KB := {
      toFun := fun z => ⟨eF (LinearMap.baseChange B K₀.subtype z), by
        change LinearMap.baseChange B π (eF.symm (eF (LinearMap.baseChange B K₀.subtype z))) = 0
        rw [eF.symm_apply_apply]
        exact (hkerB_exact _).mpr ⟨z, rfl⟩⟩
      map_add' := fun _ _ => Subtype.ext (by simp)
      map_smul' := fun _ _ => Subtype.ext (by simp)
    }
    have hιKB_bij : Function.Bijective ιKB := by
      constructor
      · intro z₁ z₂ h
        exact hkerB_inj (eF.injective (congrArg Subtype.val h))
      · rintro ⟨w, hw⟩
        obtain ⟨z, hz⟩ := (hkerB_exact (eF.symm w)).mp hw
        refine ⟨z, Subtype.ext ?_⟩
        change eF (LinearMap.baseChange B K₀.subtype z) = w
        rw [hz, eF.apply_symm_apply]
    let eK : (B ⊗[A] K₀) ≃ₗ[B] KB := LinearEquiv.ofBijective ιKB hιKB_bij
    have hsurjB : Function.Surjective (fun f : (Fin a → B) →ₗ[B] (B ⊗[A] N₀) => f.comp KB.subtype) :=
      (subsingleton_ext_one_iff_surjective πB hπB).mp hsub
    let preA : ((Fin a → A) →ₗ[A] N₀) →ₗ[A] (K₀ →ₗ[A] N₀) := {
      toFun := fun f => f.comp K₀.subtype
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
    }
    obtain ⟨eHomF, heHomF⟩ := exists_hom_baseChange_equiv (A := A) (B := B) (Fin a → A) N₀
    obtain ⟨eHomK, heHomK⟩ := exists_hom_baseChange_equiv (A := A) (B := B) K₀ N₀
    have hsurjTensor : Function.Surjective (LinearMap.lTensor B preA) := by
      intro y
      let gB : KB →ₗ[B] (B ⊗[A] N₀) := (eHomK y).comp eK.symm.toLinearMap
      obtain ⟨fB, hfB⟩ := hsurjB gB
      let u : B ⊗[A] ((Fin a → A) →ₗ[A] N₀) := eHomF.symm (fB.comp eF.toLinearMap)
      refine ⟨u, ?_⟩
      apply eHomK.injective
      have hnat : ∀ v : B ⊗[A] ((Fin a → A) →ₗ[A] N₀),
          (eHomF v).comp (LinearMap.baseChange B K₀.subtype) =
            eHomK (LinearMap.lTensor B preA v) := by
        intro v
        induction v using TensorProduct.induction_on with
        | zero => simp
        | add v₁ v₂ h₁ h₂ =>
          rw [map_add, map_add, map_add, LinearMap.add_comp, h₁, h₂]
        | tmul b f =>
          apply LinearMap.ext; intro t
          induction t using TensorProduct.induction_on with
          | zero => simp
          | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
          | tmul r k =>
            change eHomF (b ⊗ₜ[A] f) (r ⊗ₜ[A] K₀.subtype k) =
              eHomK (b ⊗ₜ[A] (f.comp K₀.subtype)) (r ⊗ₜ[A] k)
            rw [heHomF, heHomK]
            rfl
      rw [← hnat u]
      apply LinearMap.ext; intro z
      change eHomF (eHomF.symm (fB.comp eF.toLinearMap)) (LinearMap.baseChange B K₀.subtype z) =
        eHomK y z
      rw [eHomF.apply_symm_apply]
      have h1 : fB (eF (LinearMap.baseChange B K₀.subtype z)) = gB (eK z) :=
        LinearMap.congr_fun hfB (eK z)
      simpa [gB] using h1
    change Subsingleton (Abelian.Ext (ModuleCat.of A M₀) (ModuleCat.of A N₀) 1)
    rw [subsingleton_ext_one_iff_surjective π hπ]
    exact surjective_of_lTensor_surjective preA hsurjTensor
  | succ n ih =>
    intro M₀ _ _ _ N₀ _ _ hsub
    obtain ⟨a, π, hπ⟩ := Module.Finite.exists_fin' A M₀
    let K₀ := LinearMap.ker π
    have _ : Module.Finite A K₀ := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    let eF : B ⊗[A] (Fin a → A) ≃ₗ[B] (Fin a → B) := TensorProduct.piScalarRight A B B (Fin a)
    let πB : (Fin a → B) →ₗ[B] (B ⊗[A] M₀) := (LinearMap.baseChange B π).comp eF.symm.toLinearMap
    have hπB : Function.Surjective πB :=
      (LinearMap.lTensor_surjective B hπ).comp eF.symm.surjective
    let KB := LinearMap.ker πB
    have hker_exact : Function.Exact K₀.subtype π := fun v => by simp [K₀]
    have hkerB_exact : Function.Exact (LinearMap.baseChange B K₀.subtype) (LinearMap.baseChange B π) :=
      Module.Flat.lTensor_exact (R := A) (M := B) hker_exact
    have hkerB_inj : Function.Injective (LinearMap.baseChange B K₀.subtype) :=
      Module.Flat.lTensor_preserves_injective_linearMap K₀.subtype K₀.injective_subtype
    let ιKB : (B ⊗[A] K₀) →ₗ[B] KB := {
      toFun := fun z => ⟨eF (LinearMap.baseChange B K₀.subtype z), by
        change LinearMap.baseChange B π (eF.symm (eF (LinearMap.baseChange B K₀.subtype z))) = 0
        rw [eF.symm_apply_apply]
        exact (hkerB_exact _).mpr ⟨z, rfl⟩⟩
      map_add' := fun _ _ => Subtype.ext (by simp)
      map_smul' := fun _ _ => Subtype.ext (by simp)
    }
    have hιKB_bij : Function.Bijective ιKB := by
      constructor
      · intro z₁ z₂ h
        exact hkerB_inj (eF.injective (congrArg Subtype.val h))
      · rintro ⟨w, hw⟩
        obtain ⟨z, hz⟩ := (hkerB_exact (eF.symm w)).mp hw
        refine ⟨z, Subtype.ext ?_⟩
        change eF (LinearMap.baseChange B K₀.subtype z) = w
        rw [hz, eF.apply_symm_apply]
    let eK : (B ⊗[A] K₀) ≃ₗ[B] KB := LinearEquiv.ofBijective ιKB hιKB_bij
    have hKB : Subsingleton (Abelian.Ext (ModuleCat.of B KB) (ModuleCat.of B (B ⊗[A] N₀)) (n + 1)) :=
      (subsingleton_ext_succ_succ_iff πB hπB n).mp hsub
    have hKB₀ : Subsingleton (Abelian.Ext (ModuleCat.of B (B ⊗[A] K₀)) (ModuleCat.of B (B ⊗[A] N₀)) (n + 1)) :=
      (ext_subsingleton_congr eK (LinearEquiv.refl B _) (n + 1)).mpr hKB
    have hK₀ := ih K₀ N₀ hKB₀
    exact (subsingleton_ext_succ_succ_iff π hπ n).mpr hK₀

private lemma localizedModule_ext_subsingleton
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N]
    (Q : Ideal R) [Q.IsPrime]
    (h : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R N) i)) :
    ∀ i > 0, Subsingleton
      (Abelian.Ext
        (ModuleCat.of (Localization.AtPrime Q) (LocalizedModule Q.primeCompl M))
        (ModuleCat.of (Localization.AtPrime Q) (LocalizedModule Q.primeCompl N)) i) := by
  intro i hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have h1 := flat_baseChange_ext_subsingleton (A := R) (B := Localization.AtPrime Q) n M N (h (n + 1) hi)
  let eM : (Localization.AtPrime Q ⊗[R] M) ≃ₗ[Localization.AtPrime Q] LocalizedModule Q.primeCompl M :=
    (IsLocalizedModule.isBaseChange Q.primeCompl (Localization.AtPrime Q)
      (LocalizedModule.mkLinearMap Q.primeCompl M)).equiv
  let eN : (Localization.AtPrime Q ⊗[R] N) ≃ₗ[Localization.AtPrime Q] LocalizedModule Q.primeCompl N :=
    (IsLocalizedModule.isBaseChange Q.primeCompl (Localization.AtPrime Q)
      (LocalizedModule.mkLinearMap Q.primeCompl N)).equiv
  exact (ext_subsingleton_congr eM eN (n + 1)).mp h1

private lemma localizedModule_ext_ring_subsingleton
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (Q : Ideal R) [Q.IsPrime]
    (h : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R R) i)) :
    ∀ i > 0, Subsingleton
      (Abelian.Ext
        (ModuleCat.of (Localization.AtPrime Q) (LocalizedModule Q.primeCompl M))
        (ModuleCat.of (Localization.AtPrime Q) (Localization.AtPrime Q)) i) := by
  intro i hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have h1 := flat_baseChange_ext_subsingleton (A := R) (B := Localization.AtPrime Q) n M R (h (n + 1) hi)
  let eM : (Localization.AtPrime Q ⊗[R] M) ≃ₗ[Localization.AtPrime Q] LocalizedModule Q.primeCompl M :=
    (IsLocalizedModule.isBaseChange Q.primeCompl (Localization.AtPrime Q)
      (LocalizedModule.mkLinearMap Q.primeCompl M)).equiv
  let eR : (Localization.AtPrime Q ⊗[R] R) ≃ₗ[Localization.AtPrime Q] Localization.AtPrime Q :=
    Algebra.TensorProduct.rid R (Localization.AtPrime Q) (Localization.AtPrime Q)
  exact (ext_subsingleton_congr eM eR (n + 1)).mp h1

/- Section 2: Countable faithfully flat normal local descent (`Type u` -> `Type 0`) -/

private lemma countable_subring_closure {R : Type u} [CommRing R] {s : Set R} (hs : s.Countable) :
    (Subring.closure s : Set R).Countable := by
  let step : Set R → Set R := fun t =>
    t ∪ ((fun p : R × R => p.1 + p.2) '' (t ×ˢ t)) ∪
      ((fun p : R × R => p.1 * p.2) '' (t ×ˢ t)) ∪
      ((fun x : R => -x) '' t)
  let L : ℕ → Set R := Nat.rec (s ∪ {0, 1}) (fun _ t => step t)
  have hL_count : ∀ n, (L n).Countable := by
    intro n
    induction n with
    | zero => exact hs.union ((Set.countable_singleton 0).union (Set.countable_singleton 1))
    | succ n ih =>
      exact ((ih.union ((ih.prod ih).image _)).union ((ih.prod ih).image _)).union (ih.image _)
  have hL_step : ∀ n, L n ⊆ L (n + 1) := fun n x hx => Or.inl (Or.inl (Or.inl hx))
  have hL_mono : Monotone L := monotone_nat_of_le_succ hL_step
  let U : Set R := ⋃ n : ℕ, L n
  let B : Subring R := {
    carrier := U
    zero_mem' := Set.mem_iUnion.mpr ⟨0, Or.inr (Or.inl rfl)⟩
    one_mem' := Set.mem_iUnion.mpr ⟨0, Or.inr (Or.inr rfl)⟩
    add_mem' := fun {a b} ha hb => by
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ha
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hb
      refine Set.mem_iUnion.mpr ⟨max m n + 1, Or.inl (Or.inl (Or.inr ?_))⟩
      exact ⟨(a, b), ⟨hL_mono (le_max_left m n) hm, hL_mono (le_max_right m n) hn⟩, rfl⟩
    mul_mem' := fun {a b} ha hb => by
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ha
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hb
      refine Set.mem_iUnion.mpr ⟨max m n + 1, Or.inl (Or.inr ?_)⟩
      exact ⟨(a, b), ⟨hL_mono (le_max_left m n) hm, hL_mono (le_max_right m n) hn⟩, rfl⟩
    neg_mem' := fun {a} ha => by
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
      exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr ⟨a, hn, rfl⟩⟩
  }
  have hsub : (Subring.closure s : Set R) ⊆ U := by
    change Subring.closure s ≤ B
    rw [Subring.closure_le]
    intro x hx
    exact Set.mem_iUnion.mpr ⟨0, Or.inl hx⟩
  exact (Set.countable_iUnion hL_count).mono hsub

private lemma baseChange_quotient_span_equiv
    (A : Type) [CommRing A] (R : Type u) [CommRing R] [Algebra A R]
    (a b : ℕ) (rows₀ : Fin b → (Fin a → A)) :
    Nonempty
      ((R ⊗[A] ((Fin a → A) ⧸ Submodule.span A (Set.range rows₀))) ≃ₗ[R]
        ((Fin a → R) ⧸ Submodule.span R
          (Set.range (fun i : Fin b => fun j : Fin a => algebraMap A R (rows₀ i j))))) := by
  let K₀ : Submodule A (Fin a → A) := Submodule.span A (Set.range rows₀)
  let rowsR : Fin b → (Fin a → R) := fun i j => algebraMap A R (rows₀ i j)
  let KR : Submodule R (Fin a → R) := Submodule.span R (Set.range rowsR)
  let eFin : R ⊗[A] (Fin a → A) ≃ₗ[R] (Fin a → R) :=
    TensorProduct.piScalarRight A R R (Fin a)
  have heFin_tmul : ∀ (r : R) (v : Fin a → A) (j : Fin a),
      eFin (r ⊗ₜ[A] v) j = r * algebraMap A R (v j) := by
    intro r v j
    simp [eFin, Algebra.smul_def, mul_comm]
  let fwdBilin : R →ₗ[R] ((Fin a → A) ⧸ K₀) →ₗ[A] ((Fin a → R) ⧸ KR) := {
    toFun := fun r =>
      K₀.liftQ
        { toFun := fun v => Submodule.Quotient.mk (fun j => r * algebraMap A R (v j))
          map_add' := fun v w => by
            rw [← Submodule.Quotient.mk_add]
            congr 1; ext j; simp [mul_add]
          map_smul' := fun c v => by
            simp only [RingHom.id_apply]
            conv_rhs => rw [← algebraMap_smul R c, ← Submodule.Quotient.mk_smul]
            congr 1; ext j
            simp only [Pi.smul_apply, smul_eq_mul, map_mul]
            ring }
        (by
          intro v hv
          rw [LinearMap.mem_ker]
          change Submodule.Quotient.mk (fun j => r * algebraMap A R (v j)) = 0
          rw [Submodule.Quotient.mk_eq_zero]
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
          · rintro _ ⟨i, rfl⟩
            have h1 : (fun j => r * algebraMap A R (rows₀ i j)) = r • rowsR i := by
              ext j; rfl
            rw [h1]
            exact Submodule.smul_mem KR r (Submodule.subset_span ⟨i, rfl⟩)
          · have h0 : (fun j : Fin a => r * algebraMap A R ((0 : Fin a → A) j)) = 0 := by
              ext j; simp
            rw [h0]; exact KR.zero_mem
          · intro x y _ _ hx hy
            have hadd : (fun j => r * algebraMap A R ((x + y) j)) =
                (fun j => r * algebraMap A R (x j)) + (fun j => r * algebraMap A R (y j)) := by
              ext j; simp [mul_add]
            rw [hadd]; exact KR.add_mem hx hy
          · intro c x _ hx
            have hsm : (fun j => r * algebraMap A R ((c • x) j)) =
                (algebraMap A R c) • (fun j => r * algebraMap A R (x j)) := by
              ext j; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
            rw [hsm]; exact KR.smul_mem _ hx)
    map_add' := fun r₁ r₂ => by
      apply LinearMap.ext
      intro v
      induction v using Submodule.Quotient.induction_on with
      | _ v =>
        change Submodule.Quotient.mk (p := KR) (fun j => (r₁ + r₂) * algebraMap A R (v j)) =
          Submodule.Quotient.mk (p := KR) (fun j => r₁ * algebraMap A R (v j)) +
            Submodule.Quotient.mk (p := KR) (fun j => r₂ * algebraMap A R (v j))
        rw [← Submodule.Quotient.mk_add]
        congr 1; ext j; simp only [Pi.add_apply]; ring
    map_smul' := fun r₁ r₂ => by
      apply LinearMap.ext
      intro v
      induction v using Submodule.Quotient.induction_on with
      | _ v =>
        simp only [RingHom.id_apply, smul_eq_mul]
        change Submodule.Quotient.mk (p := KR) (fun j => (r₁ * r₂) * algebraMap A R (v j)) =
          r₁ • Submodule.Quotient.mk (p := KR) (fun j => r₂ * algebraMap A R (v j))
        rw [← Submodule.Quotient.mk_smul]
        congr 1; ext j; simp [mul_assoc]
  }
  let fwd : R ⊗[A] ((Fin a → A) ⧸ K₀) →ₗ[R] ((Fin a → R) ⧸ KR) :=
    AlgebraTensorModule.lift fwdBilin
  let bwd0 : (Fin a → R) →ₗ[R] R ⊗[A] ((Fin a → A) ⧸ K₀) :=
    (LinearMap.baseChange R K₀.mkQ).comp eFin.symm.toLinearMap
  have hbwd_ker : KR ≤ LinearMap.ker bwd0 := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hpre : eFin (1 ⊗ₜ[A] rows₀ i) = rowsR i := by
      ext j; rw [heFin_tmul, one_mul]
    rw [← hpre]
    change (LinearMap.baseChange R K₀.mkQ) (eFin.symm (eFin (1 ⊗ₜ[A] rows₀ i))) = 0
    rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
    have hzero : K₀.mkQ (rows₀ i) = 0 :=
      (Submodule.Quotient.mk_eq_zero K₀).mpr (Submodule.subset_span ⟨i, rfl⟩)
    rw [hzero, TensorProduct.tmul_zero]
  let bwd : ((Fin a → R) ⧸ KR) →ₗ[R] R ⊗[A] ((Fin a → A) ⧸ K₀) := KR.liftQ bwd0 hbwd_ker
  have hleft : ∀ x, bwd (fwd x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x₁ x₂ hx₁ hx₂ => rw [map_add, map_add, hx₁, hx₂]
    | tmul r u =>
      induction u using Submodule.Quotient.induction_on with
      | _ v =>
        change bwd0 (fun j => r * algebraMap A R (v j)) = r ⊗ₜ[A] Submodule.Quotient.mk v
        have hpre : eFin (r ⊗ₜ[A] v) = fun j => r * algebraMap A R (v j) := by
          ext j; exact heFin_tmul r v j
        rw [← hpre]
        change (LinearMap.baseChange R K₀.mkQ) (eFin.symm (eFin (r ⊗ₜ[A] v))) = _
        rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
        rfl
  have hright : ∀ y, fwd (bwd y) = y := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ w =>
      have hw : w = eFin (eFin.symm w) := (eFin.apply_symm_apply w).symm
      rw [hw]
      generalize eFin.symm w = z
      induction z using TensorProduct.induction_on with
      | zero => simp [bwd, bwd0]
      | add z₁ z₂ hz₁ hz₂ =>
        rw [map_add, Submodule.Quotient.mk_add, map_add, map_add, hz₁, hz₂]
      | tmul r v =>
        change fwd (bwd0 (eFin (r ⊗ₜ[A] v))) = Submodule.Quotient.mk (eFin (r ⊗ₜ[A] v))
        change fwd ((LinearMap.baseChange R K₀.mkQ) (eFin.symm (eFin (r ⊗ₜ[A] v)))) = _
        rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
        have h1 : fwd (r ⊗ₜ[A] K₀.mkQ v) =
            Submodule.Quotient.mk (fun j => r * algebraMap A R (v j)) := rfl
        rw [h1]
        congr 1; ext j; exact (heFin_tmul r v j).symm
  exact ⟨LinearEquiv.ofLinearMap fwd bwd (LinearMap.ext hright) (LinearMap.ext hleft)⟩

private lemma exists_countable_flat_subring
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (S₀ : Set R) (hS₀_count : S₀.Countable) :
    ∃ (R₀ : Subring R), Countable R₀ ∧ S₀ ⊆ (R₀ : Set R) ∧
      IsLocalHom (algebraMap R₀ R) ∧ IsLocalRing R₀ ∧
      Module.Flat R₀ R ∧ IsNoetherianRing R₀ := by
  classical
  let syzGen : ∀ (n : ℕ) (f : Fin n → R), Finset (Fin n → R) := fun n f =>
    let φ : (Fin n → R) →ₗ[R] R := {
      toFun := fun v => ∑ i : Fin n, f i * v i
      map_add' := fun v w => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
    }
    (IsNoetherian.noetherian (LinearMap.ker φ)).choose
  have hsyzGen : ∀ (n : ℕ) (f : Fin n → R),
      Submodule.span R (syzGen n f : Set (Fin n → R)) =
      LinearMap.ker ({
        toFun := fun v : Fin n → R => ∑ i : Fin n, f i * v i
        map_add' := fun v w => by simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun r v => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
      } : (Fin n → R) →ₗ[R] R) := fun n f =>
    (IsNoetherian.noetherian _).choose_spec
  let stepSet : Subring R → Set R := fun B =>
    (B : Set R) ∪
    Set.range (fun u : { b : B // IsUnit (b : R) } => ((u.2.unit⁻¹ : Rˣ) : R)) ∪
    ⋃ (q : Σ n : ℕ, Fin n → B), ⋃ (v : syzGen q.1 (fun i => (q.2 i : R))),
      Set.range (v.1 : Fin q.1 → R)
  have hstep_count : ∀ B : Subring R, (B : Set R).Countable → (stepSet B).Countable := by
    intro B hB
    have _ : Countable B := hB.to_subtype
    have h1 : (Set.range (fun u : { b : B // IsUnit (b : R) } => ((u.2.unit⁻¹ : Rˣ) : R))).Countable :=
      Set.countable_range _
    have h2 : (⋃ (q : Σ n : ℕ, Fin n → B), ⋃ (v : syzGen q.1 (fun i => (q.2 i : R))),
        Set.range (v.1 : Fin q.1 → R)).Countable := by
      refine Set.countable_iUnion fun q => ?_
      refine Set.countable_iUnion fun v => ?_
      exact Set.countable_range _
    exact (hB.union h1).union h2
  let T : ℕ → Subring R := Nat.rec (Subring.closure S₀) (fun _ B => Subring.closure (stepSet B))
  have hT_count : ∀ k, (SetLike.coe (T k)).Countable := by
    intro k
    induction k with
    | zero => exact countable_subring_closure hS₀_count
    | succ k ih => exact countable_subring_closure (hstep_count (T k) ih)
  have hT_step : ∀ k, T k ≤ T (k + 1) := by
    intro k x hx
    exact Subring.subset_closure (Or.inl (Or.inl (show x ∈ SetLike.coe (T k) from hx)))
  have hT_mono : Monotone T := monotone_nat_of_le_succ hT_step
  let R₀ : Subring R := ⨆ k : ℕ, T k
  have hR₀_mem : ∀ x : R, x ∈ R₀ ↔ ∃ k : ℕ, x ∈ T k := fun x =>
    Subring.mem_iSup_of_directed hT_mono.directed_le
  have hR₀_count : (R₀ : Set R).Countable := by
    have heq : (R₀ : Set R) = ⋃ k : ℕ, SetLike.coe (T k) := by
      ext x; simp only [SetLike.mem_coe, Set.mem_iUnion, hR₀_mem]
    rw [heq]
    exact Set.countable_iUnion hT_count
  have hcnt : Countable R₀ := hR₀_count.to_subtype
  have hS₀_sub : S₀ ⊆ (R₀ : Set R) := fun x hx =>
    (hR₀_mem x).mpr ⟨0, Subring.subset_closure hx⟩
  have hlocalHom₀ : IsLocalHom (algebraMap R₀ R) := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (hR₀_mem b.1).mp b.2
    have hinv_mem : ((hb.unit⁻¹ : Rˣ) : R) ∈ T (k + 1) :=
      Subring.subset_closure (Or.inl (Or.inr ⟨⟨⟨b.1, hk⟩, hb⟩, rfl⟩))
    have hinvR₀ : ((hb.unit⁻¹ : Rˣ) : R) ∈ R₀ := (hR₀_mem _).mpr ⟨k + 1, hinv_mem⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨((hb.unit⁻¹ : Rˣ) : R), hinvR₀⟩, ?_⟩
    ext
    exact hb.unit.mul_inv
  have hloc₀ : IsLocalRing R₀ := (algebraMap R₀ R).domain_isLocalRing
  have hflat₀ : Module.Flat R₀ R := by
    apply Module.Flat.of_forall_isTrivialRelation
    intro l f x hrel
    have hex_k : ∃ k : ℕ, ∀ i : Fin l, (f i : R) ∈ T k := by
      have : ∀ i : Fin l, ∃ k : ℕ, (f i : R) ∈ T k := fun i => (hR₀_mem _).mp (f i).2
      choose fk hfk using this
      refine ⟨Finset.univ.sup fk, fun i => hT_mono (Finset.le_sup (Finset.mem_univ i)) (hfk i)⟩
    obtain ⟨k, hk⟩ := hex_k
    let f_k : Fin l → T k := fun i => ⟨(f i : R), hk i⟩
    let G := syzGen l (fun i => (f_k i : R))
    have hx_mem : x ∈ Submodule.span R (G : Set (Fin l → R)) := by
      rw [hsyzGen l (fun i => (f_k i : R)), LinearMap.mem_ker]
      exact hrel
    rw [Finsupp.mem_span_iff_linearCombination] at hx_mem
    obtain ⟨c, hc⟩ := hx_mem
    let m : ℕ := G.card
    let eG : Fin m ≃ G := (Fintype.equivFinOfCardEq (Fintype.card_coe G)).symm
    have hmem_coord : ∀ (j : Fin m) (i : Fin l), (eG j).1 i ∈ R₀ := fun j i => by
      have h1 : (eG j).1 i ∈ T (k + 1) := by
        apply Subring.subset_closure
        right
        refine Set.mem_iUnion.mpr ⟨⟨l, f_k⟩, ?_⟩
        refine Set.mem_iUnion.mpr ⟨eG j, ?_⟩
        exact ⟨i, rfl⟩
      exact (hR₀_mem _).mpr ⟨k + 1, h1⟩
    refine ⟨m, fun i j => ⟨(eG j).1 i, hmem_coord j i⟩, fun j => c (eG j), ?_, ?_⟩
    · intro i
      have hci := congrFun hc.symm i
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype] at hci
      · rw [hci]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        calc ∑ g : G, c g * g.1 i
            = ∑ j : Fin m, c (eG j) * (eG j).1 i := (Equiv.sum_comp eG (fun g : G => c g * g.1 i)).symm
          _ = ∑ j : Fin m, (⟨(eG j).1 i, hmem_coord j i⟩ : R₀) • c (eG j) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              change c (eG j) * (eG j).1 i = (eG j).1 i * c (eG j)
              ring
      · intro _; exact zero_smul R _
    · intro j
      apply Subtype.ext
      have hkerj : (eG j).1 ∈ Submodule.span R (G : Set (Fin l → R)) :=
        Submodule.subset_span (eG j).2
      rw [hsyzGen l (fun i => (f_k i : R)), LinearMap.mem_ker] at hkerj
      simpa [f_k] using hkerj
  have hff₀ : Module.FaithfullyFlat R₀ R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hnoeth₀ : IsNoetherianRing R₀ := by
    rw [IsNoetherianRing, ← monotone_stabilizes_iff_noetherian]
    intro f
    let g : ℕ →o Submodule R R := {
      toFun := fun n => Ideal.map (algebraMap R₀ R) (f n)
      monotone' := fun _ _ h => Ideal.map_mono (f.monotone h)
    }
    obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R R) g
    refine ⟨N, fun n hn => ?_⟩
    exact Ideal.map_injective_of_faithfullyFlat (A := R₀) (B := R) (hN n hn)
  exact ⟨R₀, hcnt, hS₀_sub, hlocalHom₀, hloc₀, hflat₀, hnoeth₀⟩

private lemma isDomain_and_isIntegrallyClosed_of_faithfullyFlat
    (A : Type u₁) [CommRing A]
    (R : Type u₂) [CommRing R] [Algebra A R] [Module.FaithfullyFlat A R]
    [IsDomain R] [IsIntegrallyClosed R] :
    IsDomain A ∧ IsIntegrallyClosed A := by
  have hinj : Function.Injective (algebraMap A R) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ ((⊥ : Ideal A).map (algebraMap A R)).comap (algebraMap A R) := by
      rw [Ideal.mem_comap, ha]
      exact Ideal.zero_mem _
    rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hmem
    exact hmem
  have hdom : IsDomain A := Function.Injective.isDomain (algebraMap A R) hinj
  refine ⟨hdom, ?_⟩
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  obtain ⟨a, ⟨b, hb⟩, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors A) x
  have hR_map_mem : ∀ y ∈ nonZeroDivisors A, algebraMap A R y ∈ nonZeroDivisors R := by
    intro y hy
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    exact nonZeroDivisors.ne_zero hy (hinj (by rw [h0, map_zero]))
  let f : FractionRing A →+* FractionRing R :=
    IsLocalization.map (FractionRing R) (algebraMap A R)
      (show nonZeroDivisors A ≤ (nonZeroDivisors R).comap (algebraMap A R) from
        fun y hy => hR_map_mem y hy)
  have hf_comp : ∀ c : A,
      f (algebraMap A (FractionRing A) c) = algebraMap R (FractionRing R) (algebraMap A R c) :=
    fun c => IsLocalization.map_eq (T := nonZeroDivisors R) _ c
  have hfx_int : IsIntegral R (f (IsLocalization.mk' (FractionRing A) a ⟨b, hb⟩)) := by
    obtain ⟨p, hp_monic, hp_eval⟩ := hx
    refine ⟨p.map (algebraMap A R), hp_monic.map (algebraMap A R), ?_⟩
    rw [Polynomial.eval₂_map]
    have heq : (algebraMap R (FractionRing R)).comp (algebraMap A R) =
        f.comp (algebraMap A (FractionRing A)) := by
      ext c
      exact (hf_comp c).symm
    rw [heq, ← Polynomial.hom_eval₂, hp_eval, map_zero]
  obtain ⟨r, hr⟩ := (isIntegrallyClosed_iff (FractionRing R)).mp inferInstance hfx_int
  have hmul : algebraMap R (FractionRing R) (algebraMap A R b * r) =
      algebraMap R (FractionRing R) (algebraMap A R a) := by
    rw [map_mul, hr, ← hf_comp b, ← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul]
    have hcancel : IsLocalization.mk' (FractionRing A) (b * a) ⟨b, hb⟩ =
        algebraMap A (FractionRing A) a :=
      (IsLocalization.mk'_eq_iff_eq_mul (M := nonZeroDivisors A)).mpr (by rw [map_mul, mul_comm])
    rw [hcancel, hf_comp a]
  have hdiv : algebraMap A R a = algebraMap A R b * r :=
    (IsFractionRing.injective R (FractionRing R) hmul).symm
  have ha_mem : a ∈ ((Ideal.span {b}).map (algebraMap A R)).comap (algebraMap A R) := by
    rw [Ideal.mem_comap, hdiv]
    exact Ideal.mul_mem_right r _ (Ideal.mem_map_of_mem (algebraMap A R) (Ideal.subset_span rfl))
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat, Ideal.mem_span_singleton] at ha_mem
  obtain ⟨c, hc⟩ := ha_mem
  refine ⟨c, ?_⟩
  symm
  apply (IsLocalization.mk'_eq_iff_eq_mul (M := nonZeroDivisors A)).mpr
  rw [hc, map_mul, mul_comm]

private lemma descent_via_opaque_ring
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A]
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra A R] [IsLocalHom (algebraMap A R)] [Module.Flat A R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hMR : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R R) i))
    (hMM : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R M) i))
    (a b : ℕ) (rows₀ : Fin b → (Fin a → A))
    (eM_pres : ((Fin a → R) ⧸ Submodule.span R
      (Set.range (fun i : Fin b => fun j : Fin a => algebraMap A R (rows₀ i j)))) ≃ₗ[R] M)
    (hType0 : ∀ (M₀ : Type) [AddCommGroup M₀] [Module A M₀] [Module.Finite A M₀],
      (∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of A M₀) (ModuleCat.of A A) i)) →
      (∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of A M₀) (ModuleCat.of A M₀) i)) →
      Module.Projective A M₀) :
    Module.Projective R M := by
  let M₀ : Type := (Fin a → A) ⧸ Submodule.span A (Set.range rows₀)
  obtain ⟨eM₀⟩ := baseChange_quotient_span_equiv A R a b rows₀
  let eM : R ⊗[A] M₀ ≃ₗ[R] M := eM₀.trans eM_pres
  let eR : R ⊗[A] A ≃ₗ[R] R := Algebra.TensorProduct.rid A R R
  have _ : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hMR₀ : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of A M₀) (ModuleCat.of A A) i) := by
    intro i hi
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    have h1 : Subsingleton (Abelian.Ext (ModuleCat.of R (R ⊗[A] M₀)) (ModuleCat.of R (R ⊗[A] A)) (n + 1)) :=
      (ext_subsingleton_congr eM eR (n + 1)).mpr (hMR (n + 1) hi)
    exact faithfullyFlat_descend_ext_subsingleton (A := A) (B := R) n M₀ A h1
  have hMM₀ : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of A M₀) (ModuleCat.of A M₀) i) := by
    intro i hi
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    have h1 : Subsingleton (Abelian.Ext (ModuleCat.of R (R ⊗[A] M₀)) (ModuleCat.of R (R ⊗[A] M₀)) (n + 1)) :=
      (ext_subsingleton_congr eM eM (n + 1)).mpr (hMM (n + 1) hi)
    exact faithfullyFlat_descend_ext_subsingleton (A := A) (B := R) n M₀ M₀ h1
  have _ : Module.Projective A M₀ := hType0 M₀ hMR₀ hMM₀
  have _ : Module.Projective R (R ⊗[A] M₀) := Module.Projective.tensorProduct
  exact Module.Projective.of_equiv eM

private lemma local_normal_projective_of_type0
    (hType0 : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [IsDomain A] [IsIntegrallyClosed A]
      (M₀ : Type) [AddCommGroup M₀] [Module A M₀] [Module.Finite A M₀],
      (∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of A M₀) (ModuleCat.of A A) i)) →
      (∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of A M₀) (ModuleCat.of A M₀) i)) →
      Module.Projective A M₀)
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] [IsIntegrallyClosed R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hMR : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R R) i))
    (hMM : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R M) i)) :
    Module.Projective R M := by
  classical
  obtain ⟨a, π, hπ⟩ := Module.Finite.exists_fin' R M
  obtain ⟨sK, hsK⟩ := IsNoetherian.noetherian (LinearMap.ker π)
  let b : ℕ := sK.card
  let eK : Fin b ≃ sK := (Fintype.equivFinOfCardEq (Fintype.card_coe sK)).symm
  let rows : Fin b → (Fin a → R) := fun i => (eK i).1
  have hrows_span : Submodule.span R (Set.range rows) = LinearMap.ker π := by
    rw [← hsK]
    congr 1
    ext x
    simp only [Set.mem_range, Finset.mem_coe, rows]
    constructor
    · rintro ⟨i, rfl⟩; exact (eK i).2
    · intro hx; exact ⟨eK.symm ⟨x, hx⟩, by simp⟩
  let eM_pres : ((Fin a → R) ⧸ Submodule.span R (Set.range rows)) ≃ₗ[R] M :=
    (Submodule.quotEquivOfEq _ _ hrows_span).trans (LinearMap.quotKerEquivOfSurjective π hπ)
  let S₀ : Set R := Set.range (fun p : Fin b × Fin a => rows p.1 p.2)
  have hS₀_count : S₀.Countable := Set.countable_range _
  obtain ⟨R₀, hcnt, hS₀_sub, hlocalHom₀, hloc₀, hflat₀, hnoeth₀⟩ :=
    exists_countable_flat_subring R S₀ hS₀_count
  have _ : Module.FaithfullyFlat R₀ R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have ⟨hdom₀, hic₀⟩ := isDomain_and_isIntegrallyClosed_of_faithfullyFlat R₀ R
  let A : Type := Shrink.{0} R₀
  let eA : A ≃+* R₀ := Shrink.ringEquiv.{0} R₀
  let _ : Algebra A R := (R₀.subtype.comp eA.toRingHom).toAlgebra
  have hlocal_eA : IsLocalHom eA.toRingHom := ⟨fun a ha => by
    have h1 : IsUnit (eA.symm (eA a)) := ha.map eA.symm.toRingHom
    rwa [eA.symm_apply_apply] at h1⟩
  have _ : IsLocalRing A := eA.toRingHom.domain_isLocalRing
  have _ : IsNoetherianRing A := isNoetherianRing_of_ringEquiv R₀ eA.symm
  have _ : IsDomain A := Function.Injective.isDomain eA.toRingHom eA.injective
  have _ : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv eA.symm
  have hlocalHomA : IsLocalHom (algebraMap A R) := by
    constructor
    intro a ha
    have h1 : IsUnit (eA a) := hlocalHom₀.map_nonunit (eA a) ha
    have h2 : IsUnit (eA.symm (eA a)) := h1.map eA.symm.toRingHom
    rwa [eA.symm_apply_apply] at h2
  have hflatA : Module.Flat A R := by
    apply Module.Flat.of_forall_isTrivialRelation
    intro l f x hrel
    have hrel₀ : ∑ i : Fin l, (eA (f i)) • x i = 0 := hrel
    obtain ⟨m, aMat, y, hxy, hfa⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel₀
    refine ⟨m, fun i j => eA.symm (aMat i j), y, fun i => ?_, fun j => ?_⟩
    · have h1 : ∀ j, algebraMap A R (eA.symm (aMat i j)) = algebraMap R₀ R (aMat i j) := fun j => by
        change (eA (eA.symm (aMat i j)) : R) = (aMat i j : R); simp
      simpa [Algebra.smul_def, h1] using hxy i
    · apply eA.injective
      simpa [map_sum, map_mul] using hfa j
  let rows₀ : Fin b → (Fin a → A) := fun i j =>
    eA.symm ⟨rows i j, hS₀_sub ⟨(i, j), rfl⟩⟩
  have hrows_eq : (fun i : Fin b => fun j : Fin a => algebraMap A R (rows₀ i j)) = rows := by
    ext i j
    change (eA (eA.symm ⟨rows i j, hS₀_sub ⟨(i, j), rfl⟩⟩) : R) = rows i j
    simp
  exact descent_via_opaque_ring A R M hMR hMM a b rows₀
    ((Submodule.quotEquivOfEq _ _ (by rw [hrows_eq])).trans eM_pres) (hType0 A)

/- Section 3: Dimension <= 1 direct proof and strong induction on Krull dimension in Type 0 -/

private lemma projective_of_dim_le_one
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A]
    (hdim : ringKrullDim A ≤ 1)
    (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hMR : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of A M) (ModuleCat.of A A) i)) :
    Module.Projective A M := by
  classical
  have hdim1 : Ring.DimensionLEOne A := by
    constructor
    intro P hPne hP
    by_contra hnotmax
    have hP_lt : P < maximalIdeal A :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hP.ne_top) fun heq =>
        hnotmax (heq ▸ IsLocalRing.maximalIdeal.isMaximal A)
    have hbot_lt : (⊥ : Ideal A) < P := bot_lt_iff_ne_bot.mpr hPne
    let l : LTSeries (PrimeSpectrum A) := {
      length := 2
      toFun := fun i =>
        match i with
        | ⟨0, _⟩ => ⟨⊥, Ideal.isPrime_bot⟩
        | ⟨1, _⟩ => ⟨P, hP⟩
        | ⟨2, _⟩ => ⟨maximalIdeal A, inferInstance⟩
      step := fun i => by
        fin_cases i
        · exact hbot_lt
        · exact hP_lt
    }
    have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim A := by
      rw [ringKrullDim, Order.krullDim_eq_iSup_length]
      exact WithBot.coe_le_coe.mpr (le_iSup (fun p : LTSeries (PrimeSpectrum A) => (p.length : ℕ∞)) l)
    have hbad : ((2 : ℕ) : WithBot ℕ∞) ≤ 1 := h2.trans hdim
    have hbad' : ((2 : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp hbad
    exact absurd (ENat.natCast_le_natCast.mp hbad') (by omega)
  have hded : IsDedekindDomain A :=
    (isDedekindDomain_iff A (FractionRing A)).mpr
      ⟨inferInstance, inferInstance, hdim1,
        fun {_} => (isIntegrallyClosed_iff (FractionRing A)).mp inferInstance⟩
  have hfinmax : {I : Ideal A | I.IsMaximal}.Finite := by
    refine (Set.finite_singleton (maximalIdeal A)).subset fun I hI => ?_
    exact IsLocalRing.eq_maximalIdeal hI
  have hpid : IsPrincipalIdealRing A := IsPrincipalIdealRing.of_finite_maximals hfinmax
  obtain ⟨a, π, hπ⟩ := Module.Finite.exists_fin' A M
  let K : Submodule A (Fin a → A) := LinearMap.ker π
  obtain ⟨b, bK⟩ := Submodule.basisOfPid (Pi.basisFun A (Fin a)) K
  have hExtFin : Subsingleton (Abelian.Ext (ModuleCat.of A M) (ModuleCat.of A (Fin b → A)) 1) :=
    ext_subsingleton_fin_pi b 1 (hMR 1 (by omega))
  have hExtK : Subsingleton (Abelian.Ext (ModuleCat.of A M) (ModuleCat.of A K) 1) :=
    (ext_subsingleton_congr (LinearEquiv.refl A M) bK.equivFun.symm 1).mp hExtFin
  obtain ⟨s, hs⟩ := (subsingleton_ext_one_iff_surjective π hπ).mp hExtK LinearMap.id
  let u : (Fin a → A) →ₗ[A] (Fin a → A) := LinearMap.id - K.subtype.comp s
  have hker_u : LinearMap.ker π ≤ LinearMap.ker u := by
    intro v hv
    rw [LinearMap.mem_ker]
    have hsv : s v = ⟨v, hv⟩ := LinearMap.congr_fun hs ⟨v, hv⟩
    change v - (s v).1 = 0
    rw [hsv, sub_self]
  let t : M →ₗ[A] (Fin a → A) :=
    (K.liftQ u hker_u).comp (LinearMap.quotKerEquivOfSurjective π hπ).symm.toLinearMap
  have hsplit : π.comp t = LinearMap.id := by
    apply LinearMap.ext; intro m
    obtain ⟨v, rfl⟩ := hπ m
    have hq : (LinearMap.quotKerEquivOfSurjective π hπ).symm (π v) = Submodule.Quotient.mk v :=
      (LinearMap.quotKerEquivOfSurjective π hπ).injective (by simp)
    change π (K.liftQ u hker_u ((LinearMap.quotKerEquivOfSurjective π hπ).symm (π v))) = π v
    rw [hq]
    change π (v - (s v).1) = π v
    rw [map_sub, (s v).2, sub_zero]
  exact Module.Projective.of_split t π hsplit

private lemma ringKrullDim_eq_nat_of_local_noetherian
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    ∃ d : ℕ, ringKrullDim A = (d : WithBot ℕ∞) := by
  have hnbot : ringKrullDim A ≠ ⊥ := ringKrullDim_ne_bot
  have hntop : ringKrullDim A ≠ ⊤ := ringKrullDim_ne_top
  cases h : ringKrullDim A with
  | bot => exact absurd h hnbot
  | coe x =>
    cases x with
    | top => exact absurd h hntop
    | coe d => exact ⟨d, rfl⟩

private lemma ringKrullDim_localization_lt
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (Q : Ideal A) [Q.IsPrime] (hQne : Q ≠ maximalIdeal A) :
    ringKrullDim (Localization.AtPrime Q) < ringKrullDim A := by
  obtain ⟨d, hd⟩ := ringKrullDim_eq_nat_of_local_noetherian A
  obtain ⟨dQ, hdQ⟩ := ringKrullDim_eq_nat_of_local_noetherian (Localization.AtPrime Q)
  rw [hd, hdQ]
  suffices hlt : dQ < d by
    exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_natCast.mpr hlt)
  have hQ_lt : Q < maximalIdeal A :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top') hQne
  have hex : ∃ l : LTSeries (PrimeSpectrum (Localization.AtPrime Q)), l.length = dQ := by
    have hne : Nonempty (PrimeSpectrum (Localization.AtPrime Q)) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance
    rw [ringKrullDim, Order.krullDim_eq_iSup_length] at hdQ
    have hdQ' : (⨆ l : LTSeries (PrimeSpectrum (Localization.AtPrime Q)), (l.length : ℕ∞)) = (dQ : ℕ∞) :=
      WithBot.coe_injective hdQ
    by_contra hno
    have hle : ∀ l : LTSeries (PrimeSpectrum (Localization.AtPrime Q)), l.length < dQ := by
      intro l
      have h1 : (l.length : ℕ∞) ≤ (dQ : ℕ∞) :=
        hdQ' ▸ le_iSup (fun p : LTSeries (PrimeSpectrum (Localization.AtPrime Q)) => (p.length : ℕ∞)) l
      exact lt_of_le_of_ne (Nat.cast_le.mp h1) (fun heq => hno ⟨l, heq⟩)
    cases dQ with
    | zero =>
      obtain ⟨p⟩ := hne
      exact Nat.not_lt_zero _ (hle (RelSeries.singleton _ p))
    | succ m =>
      have hsup : (⨆ l : LTSeries (PrimeSpectrum (Localization.AtPrime Q)), (l.length : ℕ∞)) ≤ (m : ℕ∞) :=
        iSup_le fun l => Nat.cast_le.mpr (Nat.lt_succ_iff.mp (hle l))
      rw [hdQ'] at hsup
      have : m + 1 ≤ m := Nat.cast_le.mp hsup
      omega
  obtain ⟨l, hl⟩ := hex
  let f := algebraMap A (Localization.AtPrime Q)
  have hstrict : StrictMono (PrimeSpectrum.comap f) := by
    intro p₁ p₂ hp
    have hle : p₁.asIdeal.comap f ≤ p₂.asIdeal.comap f := Ideal.comap_mono (le_of_lt hp)
    refine lt_of_le_of_ne hle fun heq => ne_of_lt hp ?_
    have h1 := IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q) p₁.asIdeal
    have h2 := IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q) p₂.asIdeal
    have heq' : Ideal.under A p₁.asIdeal = Ideal.under A p₂.asIdeal :=
      congrArg PrimeSpectrum.asIdeal heq
    exact PrimeSpectrum.ext (by rw [← h1, ← h2, heq'])
  let l' : LTSeries (PrimeSpectrum A) := l.map (PrimeSpectrum.comap f) hstrict
  have hlast_le : l'.last.asIdeal ≤ Q := by
    change l.last.asIdeal.comap f ≤ Q
    exact (IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime Q) Q ⟨l.last.asIdeal, l.last.isPrime⟩).2.2
  have hlast_lt : l'.last < ⟨maximalIdeal A, inferInstance⟩ :=
    show l'.last.asIdeal < maximalIdeal A from lt_of_le_of_lt hlast_le hQ_lt
  let L : LTSeries (PrimeSpectrum A) := l'.snoc ⟨maximalIdeal A, inferInstance⟩ hlast_lt
  have hL_le : (L.length : ℕ∞) ≤ (d : ℕ∞) := by
    rw [ringKrullDim, Order.krullDim_eq_iSup_length] at hd
    have hd' : (⨆ p : LTSeries (PrimeSpectrum A), (p.length : ℕ∞)) = (d : ℕ∞) :=
      WithBot.coe_injective hd
    exact hd' ▸ le_iSup (fun p : LTSeries (PrimeSpectrum A) => (p.length : ℕ∞)) L
  have hL_len : L.length = dQ + 1 := by
    simp [L, l', hl]
  rw [hL_len] at hL_le
  have : dQ + 1 ≤ d := Nat.cast_le.mp hL_le
  omega

private lemma exists_regular_in_maximalIdeal_of_one_le_dim
    (A : Type) [CommRing A] [IsLocalRing A] [IsDomain A]
    (hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim A) :
    ∃ x ∈ maximalIdeal A, IsSMulRegular A x := by
  have hne : maximalIdeal A ≠ ⊥ := by
    intro hbot
    have hle0 : ringKrullDim A ≤ 0 := by
      rw [ringKrullDim, Order.krullDim_eq_iSup_length]
      apply WithBot.coe_le_coe.mpr
      apply iSup_le
      intro l
      cases hlen : l.length with
      | zero => exact le_rfl
      | succ m =>
        exfalso
        have hlt : (l ⟨0, by omega⟩).asIdeal < (l ⟨1, by omega⟩).asIdeal :=
          l.strictMono (by show (⟨0, _⟩ : Fin (l.length + 1)) < ⟨1, _⟩; exact Nat.zero_lt_one)
        have h1 : (l ⟨1, by omega⟩).asIdeal ≤ ⊥ :=
          hbot ▸ IsLocalRing.le_maximalIdeal (l ⟨1, by omega⟩).isPrime.ne_top
        exact not_lt_of_ge (h1.trans bot_le) (lt_of_le_of_lt bot_le hlt)
    have hbad : (1 : WithBot ℕ∞) ≤ 0 := hdim.trans hle0
    have hbad' : ((1 : ℕ) : ℕ∞) ≤ ((0 : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp hbad
    exact absurd (ENat.natCast_le_natCast.mp hbad') (by omega)
  obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨x, hxmem, fun a b hab => mul_left_cancel₀ hxne hab⟩

private lemma type0_local_normal_projective
    (h1 : H1) (h2 : H2)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A]
    (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hMR : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of A M) (ModuleCat.of A A) i))
    (hMM : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of A M) (ModuleCat.of A M) i)) :
    Module.Projective A M := by
  have aux : ∀ (d : ℕ)
      (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [IsDomain B] [IsIntegrallyClosed B],
      ringKrullDim B = (d : WithBot ℕ∞) →
      ∀ (N : Type) [AddCommGroup N] [Module B N] [Module.Finite B N],
        (∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of B N) (ModuleCat.of B B) i)) →
        (∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of B N) (ModuleCat.of B N) i)) →
        Module.Projective B N := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro B _ _ _ _ _ hdim N _ _ _ hNR hNN
      by_cases hd1 : d ≤ 1
      · have hdim1 : ringKrullDim B ≤ 1 := by
          rw [hdim]
          exact WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hd1)
        exact projective_of_dim_le_one B hdim1 N hNR
      · have hd2 : (2 : WithBot ℕ∞) ≤ ringKrullDim B := by
          rw [hdim]
          have h2le : 2 ≤ d := by omega
          exact WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr h2le)
        have hS1 : ∀ (Q : Ideal B) [Q.IsPrime],
            (1 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime Q) →
            ∃ x ∈ maximalIdeal (Localization.AtPrime Q),
              IsSMulRegular (Localization.AtPrime Q) x := by
          intro Q hQ hdimQ
          have _ : IsDomain (Localization.AtPrime Q) :=
            IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime Q)
              (Ideal.primeCompl_le_nonZeroDivisors (P := Q))
          exact exists_regular_in_maximalIdeal_of_one_le_dim (Localization.AtPrime Q) hdimQ
        have hS2 : ∀ (Q : Ideal B) [Q.IsPrime],
            (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime Q) →
            ∃ x ∈ maximalIdeal (Localization.AtPrime Q),
              IsSMulRegular (Localization.AtPrime Q) x ∧
              ∃ y ∈ maximalIdeal (Localization.AtPrime Q),
                IsSMulRegular ((Localization.AtPrime Q) ⧸ Ideal.span {x}) y := by
          intro Q hQ hdimQ
          have _ : IsDomain (Localization.AtPrime Q) :=
            IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime Q)
              (Ideal.primeCompl_le_nonZeroDivisors (P := Q))
          have _ : IsIntegrallyClosed (Localization.AtPrime Q) :=
            isIntegrallyClosed_of_isLocalization (Localization.AtPrime Q) Q.primeCompl
              (Ideal.primeCompl_le_nonZeroDivisors (P := Q))
          exact h1 (Localization.AtPrime Q) hdimQ
        have hpunct : ∀ (Q : Ideal B) [Q.IsPrime], Q ≠ maximalIdeal B →
            Module.Projective (Localization.AtPrime Q) (LocalizedModule Q.primeCompl N) := by
          intro Q hQ hQne
          have _ : IsDomain (Localization.AtPrime Q) :=
            IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime Q)
              (Ideal.primeCompl_le_nonZeroDivisors (P := Q))
          have _ : IsIntegrallyClosed (Localization.AtPrime Q) :=
            isIntegrallyClosed_of_isLocalization (Localization.AtPrime Q) Q.primeCompl
              (Ideal.primeCompl_le_nonZeroDivisors (P := Q))
          let eNQ : (Localization.AtPrime Q ⊗[B] N) ≃ₗ[Localization.AtPrime Q]
              LocalizedModule Q.primeCompl N :=
            (IsLocalizedModule.isBaseChange Q.primeCompl (Localization.AtPrime Q)
              (LocalizedModule.mkLinearMap Q.primeCompl N)).equiv
          have _ : Module.Finite (Localization.AtPrime Q) (LocalizedModule Q.primeCompl N) :=
            Module.Finite.equiv eNQ
          obtain ⟨dQ, hdQ⟩ := ringKrullDim_eq_nat_of_local_noetherian (Localization.AtPrime Q)
          have hlt : ringKrullDim (Localization.AtPrime Q) < ringKrullDim B :=
            ringKrullDim_localization_lt B Q hQne
          rw [hdim, hdQ] at hlt
          have hdQ_lt : dQ < d := ENat.natCast_lt_natCast.mp (WithBot.coe_lt_coe.mp hlt)
          exact ih dQ hdQ_lt (Localization.AtPrime Q) hdQ (LocalizedModule Q.primeCompl N)
            (localizedModule_ext_ring_subsingleton Q hNR)
            (localizedModule_ext_subsingleton Q hNN)
        exact h2 B hd2 hS1 hS2 N hpunct hNR hNN
  obtain ⟨d, hd⟩ := ringKrullDim_eq_nat_of_local_noetherian A
  exact aux d A hd M hMR hMM

end

theorem main : H1 → H2 → type_of% @AuslanderReiten.auslander_reiten.variants.normal := by
  intro h1 h2 R _ _ M _ _ _ _ _ hMR hMM
  have _ : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  refine Module.projective_of_localization_maximal fun P hP => ?_
  have _ : P.IsPrime := hP.isPrime
  have _ : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime P)
      (Ideal.primeCompl_le_nonZeroDivisors (P := P))
  have _ : IsIntegrallyClosed (Localization.AtPrime P) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime P) P.primeCompl
      (Ideal.primeCompl_le_nonZeroDivisors (P := P))
  let eMP : (Localization.AtPrime P ⊗[R] M) ≃ₗ[Localization.AtPrime P]
      LocalizedModule P.primeCompl M :=
    (IsLocalizedModule.isBaseChange P.primeCompl (Localization.AtPrime P)
      (LocalizedModule.mkLinearMap P.primeCompl M)).equiv
  have _ : Module.Finite (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    Module.Finite.equiv eMP
  exact local_normal_projective_of_type0
    (fun A _ _ _ _ _ M₀ _ _ _ hMR₀ hMM₀ => type0_local_normal_projective h1 h2 A M₀ hMR₀ hMM₀)
    (Localization.AtPrime P)
    (LocalizedModule P.primeCompl M)
    (localizedModule_ext_ring_subsingleton P hMR)
    (localizedModule_ext_subsingleton P hMM)

end OMA.R_AuslanderReiten_auslander_reiten_variants_normal_R1
