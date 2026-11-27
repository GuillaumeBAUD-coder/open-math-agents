import FormalConjectures.Wikipedia.NoetherProblem

/-!
Proof of NoetherProblem.noether_problem.variants.four:
For any field K and any subgroup H of K-automorphisms of K(X_0, X_1, X_2, X_3) permuting the 4
indeterminates, the fixed field L^H is purely transcendental over K (in every characteristic).
We reduce to a subgroup G ≤ Perm (Fin 4) and handle all 11 conjugacy classes of subgroups of S_4
(|G| ∈ {1, 2, 3, 4, 6, 8, 12, 24}) via explicit rational generators and 1-, 2-, or 3-step
algebraic towers of degree ≤ |G|, combined with Artin's theorem and transcendence degree.
-/

namespace OMA.Noether4

open MvPolynomial NoetherProblem Equiv

private abbrev A4 (K : Type) [Field K] := MvPolynomial (Fin 4) K
private abbrev FR4 (K : Type) [Field K] := FractionRing (A4 K)

private noncomputable def permAut (K : Type) [Field K] (σ : Perm (Fin 4)) :
    FR4 K ≃ₐ[K] FR4 K :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K σ)

private lemma permAut_algebraMap {K : Type} [Field K] (σ : Perm (Fin 4)) (a : A4 K) :
    permAut K σ (algebraMap (A4 K) (FR4 K) a) = algebraMap (A4 K) (FR4 K) (rename σ a) := by
  rw [permAut, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

private lemma permAut_X {K : Type} [Field K] (σ : Perm (Fin 4)) (i : Fin 4) :
    permAut K σ (algebraMap (A4 K) (FR4 K) (X i)) = algebraMap (A4 K) (FR4 K) (X (σ i)) := by
  rw [permAut_algebraMap, rename_X]

private lemma permAut_one {K : Type} [Field K] : permAut K (1 : Perm (Fin 4)) = 1 := by
  ext y
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A4 K) y
  rw [map_div₀, permAut_algebraMap, permAut_algebraMap]
  simp [Perm.coe_one, rename_id]

private lemma permAut_mul {K : Type} [Field K] (σ τ : Perm (Fin 4)) :
    permAut K (σ * τ) = permAut K σ * permAut K τ := by
  ext y
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A4 K) y
  rw [AlgEquiv.mul_apply, map_div₀, map_div₀, map_div₀]
  simp only [permAut_algebraMap, rename_rename]
  rfl

private noncomputable def permAutHom (K : Type) [Field K] :
    Perm (Fin 4) →* (FR4 K ≃ₐ[K] FR4 K) where
  toFun := permAut K
  map_one' := permAut_one
  map_mul' := permAut_mul

private lemma permAutHom_injective (K : Type) [Field K] :
    Function.Injective (permAutHom K) := by
  intro σ τ h
  ext i
  have h1 : permAut K σ (algebraMap (A4 K) (FR4 K) (X i)) =
      permAut K τ (algebraMap (A4 K) (FR4 K) (X i)) :=
    congrArg (fun f : FR4 K ≃ₐ[K] FR4 K => f (algebraMap (A4 K) (FR4 K) (X i))) h
  rw [permAut_X, permAut_X] at h1
  have h2 : (X (σ i) : A4 K) = X (τ i) := IsFractionRing.injective (A4 K) (FR4 K) h1
  have h3 := congrArg (MvPolynomial.eval (Pi.single (σ i) (1 : K))) h2
  simp only [eval_X, Pi.single_eq_same] at h3
  by_contra hne
  have hne' : σ i ≠ τ i := fun he => hne (congrArg Fin.val he)
  rw [Pi.single_eq_of_ne (Ne.symm hne')] at h3
  exact one_ne_zero h3

private lemma mem_intermediateField_of_mem_X {K : Type} [Field K]
    (E : IntermediateField K (FR4 K))
    (hX : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈ E) :
    E = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A4 K) y
  have hpoly : ∀ p : A4 K, algebraMap (A4 K) (FR4 K) p ∈ E := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C k =>
      change algebraMap (A4 K) (FR4 K) (algebraMap K (A4 K) k) ∈ E
      rw [← IsScalarTower.algebraMap_apply K (A4 K) (FR4 K)]
      exact E.algebraMap_mem k
    | add p q hp hq => rw [map_add]; exact E.add_mem hp hq
    | mul_X p i hp => rw [map_mul]; exact E.mul_mem hp (hX i)
  exact E.div_mem (hpoly a) (hpoly b)

private lemma xFun_isTranscendenceBasis (K : Type) [Field K] :
    IsTranscendenceBasis K (fun i : Fin 4 => algebraMap (A4 K) (FR4 K) (X i)) := by
  set xFun : Fin 4 → FR4 K := fun i => algebraMap (A4 K) (FR4 K) (X i)
  have hind : AlgebraicIndependent K xFun := by
    rw [algebraicIndependent_iff_injective_aeval]
    have hcomp : MvPolynomial.aeval xFun = IsScalarTower.toAlgHom K (A4 K) (FR4 K) := by
      ext i; simp [xFun]
    rw [hcomp]
    exact IsFractionRing.injective (A4 K) (FR4 K)
  rw [hind.isTranscendenceBasis_iff_isAlgebraic]
  constructor
  intro y
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A4 K) y
  have hmem : ∀ p : A4 K, algebraMap (A4 K) (FR4 K) p ∈ Algebra.adjoin K (Set.range xFun) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C k =>
      change algebraMap (A4 K) (FR4 K) (algebraMap K (A4 K) k) ∈ _
      rw [← IsScalarTower.algebraMap_apply K (A4 K) (FR4 K)]
      exact Subalgebra.algebraMap_mem _ k
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp => rw [map_mul]; exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hb0 : algebraMap (A4 K) (FR4 K) b ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hb (IsFractionRing.injective (A4 K) (FR4 K) (h.trans (map_zero _).symm))
  refine ⟨Polynomial.C ⟨algebraMap (A4 K) (FR4 K) b, hmem b⟩ * Polynomial.X -
    Polynomial.C ⟨algebraMap (A4 K) (FR4 K) a, hmem a⟩, ?_, ?_⟩
  · intro h0
    have hc := congrArg (fun q => Polynomial.coeff q 1) h0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
      one_ne_zero, ↓reduceIte, sub_zero, Polynomial.coeff_zero] at hc
    exact hb0 (congrArg Subtype.val hc)
  · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    change algebraMap (A4 K) (FR4 K) b * (algebraMap (A4 K) (FR4 K) a / algebraMap (A4 K) (FR4 K) b) -
      algebraMap (A4 K) (FR4 K) a = 0
    rw [mul_div_cancel₀ _ hb0, sub_self]

private lemma algebraicIndependent_of_isAlgebraic_adjoin {K : Type} [Field K]
    (f : Fin 4 → FR4 K)
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range f)) (FR4 K)) :
    AlgebraicIndependent K f := by
  classical
  set S := Algebra.adjoin K (Set.range f)
  set E := IntermediateField.adjoin K (Set.range f)
  have hS_le_E : S ≤ E.toSubalgebra := by
    rw [Algebra.adjoin_le_iff]
    exact IntermediateField.subset_adjoin K (Set.range f)
  have hE_sub : ∀ y ∈ E, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ y = a / b := by
    let E' : IntermediateField K (FR4 K) :=
      { carrier := {y : FR4 K | ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ y = a / b}
        mul_mem' := by
          rintro _ _ ⟨a1, ha1, b1, hb1, hb10, rfl⟩ ⟨a2, ha2, b2, hb2, hb20, rfl⟩
          exact ⟨a1 * a2, S.mul_mem ha1 ha2, b1 * b2, S.mul_mem hb1 hb2, mul_ne_zero hb10 hb20,
            by ring⟩
        one_mem' := ⟨1, S.one_mem, 1, S.one_mem, one_ne_zero, by simp⟩
        add_mem' := by
          rintro _ _ ⟨a1, ha1, b1, hb1, hb10, rfl⟩ ⟨a2, ha2, b2, hb2, hb20, rfl⟩
          exact ⟨a1 * b2 + a2 * b1, S.add_mem (S.mul_mem ha1 hb2) (S.mul_mem ha2 hb1),
            b1 * b2, S.mul_mem hb1 hb2, mul_ne_zero hb10 hb20, by field_simp⟩
        zero_mem' := ⟨0, S.zero_mem, 1, S.one_mem, one_ne_zero, by simp⟩
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, hb0, rfl⟩
          by_cases ha0 : a = 0
          · subst ha0; exact ⟨0, S.zero_mem, 1, S.one_mem, one_ne_zero, by simp⟩
          · exact ⟨b, hb, a, ha, ha0, by rw [inv_div]⟩
        algebraMap_mem' := fun k => ⟨algebraMap K (FR4 K) k, S.algebraMap_mem k, 1, S.one_mem,
          one_ne_zero, by simp⟩ }
    have hle : E ≤ E' := by
      rw [IntermediateField.adjoin_le_iff]
      rintro y ⟨i, rfl⟩
      exact ⟨f i, Algebra.subset_adjoin ⟨i, rfl⟩, 1, S.one_mem, one_ne_zero, by simp⟩
    exact fun y hy => hle hy
  letI : Algebra S E := (Subalgebra.inclusion hS_le_E).toRingHom.toAlgebra
  haveI : IsScalarTower S E (FR4 K) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hS_alg_E : Algebra.IsAlgebraic S E := by
    constructor
    intro y
    obtain ⟨a, ha, b, hb, hb0, hy⟩ := hE_sub y.1 y.2
    refine ⟨Polynomial.C ⟨b, hb⟩ * Polynomial.X - Polynomial.C ⟨a, ha⟩, ?_, ?_⟩
    · intro h0
      have hc := congrArg (fun q => Polynomial.coeff q 1) h0
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
        one_ne_zero, ↓reduceIte, sub_zero, Polynomial.coeff_zero] at hc
      exact hb0 (congrArg Subtype.val hc)
    · apply Subtype.ext
      simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      change b * y.1 - a = 0
      rw [hy, mul_div_cancel₀ _ hb0, sub_self]
  have hSE : Algebra.IsAlgebraic S (FR4 K) := Algebra.IsAlgebraic.trans S E (FR4 K)
  obtain ⟨t, ht_sub, ht_basis⟩ := exists_isTranscendenceBasis_subset (R := K) (Set.range f)
  have hcard_t : Cardinal.mk t = 4 := by
    have h1 := ht_basis.lift_cardinalMk_eq_trdeg
    have h2 := (xFun_isTranscendenceBasis K).lift_cardinalMk_eq_trdeg
    simp only [Cardinal.lift_id] at h1 h2
    rw [h1, ← h2]
    simp
  have hfin_range : (Set.range f).Finite := Set.finite_range f
  have hfin_t : t.Finite := hfin_range.subset ht_sub
  letI : Fintype t := hfin_t.fintype
  have ht_card_nat : Fintype.card t = 4 := by
    have : (Fintype.card t : Cardinal) = 4 := by
      rw [← Cardinal.mk_fintype]; exact hcard_t
    exact_mod_cast this
  have hcard_le : Fintype.card t ≤ (Finset.univ.image f).card := by
    have : t.toFinset ⊆ Finset.univ.image f := by
      intro x hx
      rw [Set.mem_toFinset] at hx
      obtain ⟨i, rfl⟩ := ht_sub hx
      exact Finset.mem_image_of_mem f (Finset.mem_univ i)
    calc Fintype.card t = t.toFinset.card := (Set.toFinset_card t).symm
      _ ≤ (Finset.univ.image f).card := Finset.card_le_card this
  have himg_card : (Finset.univ.image f).card = 4 := by
    have hle4 : (Finset.univ.image f).card ≤ 4 := by
      calc (Finset.univ.image f).card ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
        _ = 4 := by simp
    omega
  have hfinj : Function.Injective f := by
    have : (Finset.univ.image f).card = (Finset.univ : Finset (Fin 4)).card := by
      rw [himg_card]; simp
    have hinjOn := Finset.injOn_of_card_image_eq this
    intro i j hij
    exact hinjOn (Finset.mem_univ i) (Finset.mem_univ j) hij
  have ht_eq : t = Set.range f := by
    have hsub_fin : t.toFinset ⊆ Finset.univ.image f := by
      intro x hx
      rw [Set.mem_toFinset] at hx
      obtain ⟨i, rfl⟩ := ht_sub hx
      exact Finset.mem_image_of_mem f (Finset.mem_univ i)
    have hcard_eq : t.toFinset.card = (Finset.univ.image f).card := by
      rw [Set.toFinset_card, ht_card_nat, himg_card]
    have heq_fin := Finset.eq_of_subset_of_card_le hsub_fin (le_of_eq hcard_eq.symm)
    ext x
    constructor
    · exact fun hx => ht_sub hx
    · intro hx
      have : x ∈ Finset.univ.image f := by
        obtain ⟨i, rfl⟩ := hx; exact Finset.mem_image_of_mem f (Finset.mem_univ i)
      rw [← heq_fin, Set.mem_toFinset] at this
      exact this
  let e_t : Fin 4 ≃ t :=
    Equiv.ofBijective (fun i => ⟨f i, ht_eq ▸ ⟨i, rfl⟩⟩)
      ⟨fun i j h => hfinj (congrArg Subtype.val h),
       fun ⟨x, hx⟩ => by
         rw [ht_eq] at hx
         obtain ⟨i, rfl⟩ := hx
         exact ⟨i, rfl⟩⟩
  rw [algebraicIndependent_iff_injective_aeval]
  have hcomp : MvPolynomial.aeval f =
      (MvPolynomial.aeval ((↑) : t → FR4 K)).comp (MvPolynomial.renameEquiv K e_t).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    change MvPolynomial.aeval f (X i) = MvPolynomial.aeval ((↑) : t → FR4 K) (rename e_t (X i))
    rw [MvPolynomial.aeval_X, MvPolynomial.rename_X, MvPolynomial.aeval_X]
    rfl
  rw [hcomp]
  intro p q hpq
  exact (MvPolynomial.renameEquiv K e_t).injective (ht_basis.1 (by simpa [AlgHom.comp_apply] using hpq))

private lemma isRational_of_adjoin_fin4 {K : Type} [Field K]
    (f : Fin 4 → FR4 K)
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range f)) (FR4 K)) :
    IsRationalExtension K (IntermediateField.adjoin K (Set.range f)) (Fin 4) := by
  classical
  set E := IntermediateField.adjoin K (Set.range f)
  have hind : AlgebraicIndependent K f := algebraicIndependent_of_isAlgebraic_adjoin f halg
  have hind_inj : Function.Injective (MvPolynomial.aeval f) := hind
  let g : A4 K →ₐ[K] E := MvPolynomial.aeval (fun i => (⟨f i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩ : E))
  have hg_comp : E.val.comp g = MvPolynomial.aeval f := by
    ext i; simp [g]
  have hg_val : ∀ p : A4 K, (g p : FR4 K) = MvPolynomial.aeval f p := fun p =>
    congrArg (fun h : A4 K →ₐ[K] FR4 K => h p) hg_comp
  have ginj : Function.Injective g := by
    intro p q hpq
    have h1 : (g p : FR4 K) = g q := congrArg Subtype.val hpq
    rw [hg_val, hg_val] at h1
    exact hind_inj h1
  letI : Algebra (A4 K) E := g.toRingHom.toAlgebra
  have hgalg : ∀ p : A4 K, algebraMap (A4 K) E p = g p := fun _ => rfl
  have : FaithfulSMul (A4 K) E := (faithfulSMul_iff_algebraMap_injective (A4 K) E).mpr ginj
  have hsurj : ∀ z : E, ∃ x y : A4 K, z = algebraMap (A4 K) E x / algebraMap (A4 K) E y := by
    let E' : IntermediateField K (FR4 K) :=
      { carrier := {y : FR4 K | ∃ p q : A4 K, q ≠ 0 ∧ y = MvPolynomial.aeval f p / MvPolynomial.aeval f q}
        mul_mem' := by
          rintro _ _ ⟨p1, q1, hq1, rfl⟩ ⟨p2, q2, hq2, rfl⟩
          exact ⟨p1 * p2, q1 * q2, mul_ne_zero hq1 hq2, by simp [map_mul]; ring⟩
        one_mem' := ⟨1, 1, one_ne_zero, by simp⟩
        add_mem' := by
          rintro _ _ ⟨p1, q1, hq1, rfl⟩ ⟨p2, q2, hq2, rfl⟩
          have hq1' : MvPolynomial.aeval f q1 ≠ 0 := by
            intro h; exact hq1 (hind_inj (h.trans (map_zero _).symm))
          have hq2' : MvPolynomial.aeval f q2 ≠ 0 := by
            intro h; exact hq2 (hind_inj (h.trans (map_zero _).symm))
          exact ⟨p1 * q2 + p2 * q1, q1 * q2, mul_ne_zero hq1 hq2, by
            simp only [map_add, map_mul]; field_simp⟩
        zero_mem' := ⟨0, 1, one_ne_zero, by simp⟩
        inv_mem' := by
          rintro _ ⟨p, q, hq, rfl⟩
          by_cases hp : p = 0
          · subst hp; exact ⟨0, 1, one_ne_zero, by simp⟩
          · exact ⟨q, p, hp, by rw [inv_div]⟩
        algebraMap_mem' := fun k => ⟨C k, 1, one_ne_zero, by simp⟩ }
    have hle : E ≤ E' := by
      rw [IntermediateField.adjoin_le_iff]
      rintro y ⟨i, rfl⟩
      exact ⟨X i, 1, one_ne_zero, by simp⟩
    intro z
    obtain ⟨p, q, hq, hz⟩ := hle z.2
    refine ⟨p, q, ?_⟩
    apply Subtype.ext
    rw [IntermediateField.coe_div, hgalg, hgalg, hg_val, hg_val, hz]
  have : IsFractionRing (A4 K) E := IsFractionRing.of_field (A4 K) E hsurj
  let eqv : FR4 K ≃ₐ[A4 K] E := IsLocalization.algEquiv (nonZeroDivisors (A4 K)) (FR4 K) E
  have hcomm : ∀ k : K, eqv.toRingEquiv (algebraMap K (FR4 K) k) = algebraMap K E k := by
    intro k
    rw [IsScalarTower.algebraMap_apply K (A4 K) (FR4 K) k]
    change eqv (algebraMap (A4 K) (FR4 K) (algebraMap K (A4 K) k)) = _
    rw [AlgEquiv.commutes, hgalg]
    exact g.commutes k
  exact ⟨⟨(AlgEquiv.ofRingEquiv (f := eqv.toRingEquiv) hcomm).symm⟩⟩

private lemma intermediateField_eq_of_finrank_le {K L : Type*} [Field K] [Field L] [Algebra K L]
    {E F : IntermediateField K L} (hEF : E ≤ F) [FiniteDimensional E L]
    {n : ℕ} (hn : 0 < n) (hE : Module.finrank E L ≤ n) (hF : Module.finrank F L = n) :
    E = F := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  haveI : IsScalarTower E F L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional E F := FiniteDimensional.left E F L
  haveI : FiniteDimensional F L := FiniteDimensional.right E F L
  have hmul := Module.finrank_mul_finrank E F L
  rw [hF] at hmul
  have hpos_EF : 0 < Module.finrank E F := Module.finrank_pos
  have hfin_EF_eq_one : Module.finrank E F = 1 := by nlinarith
  apply le_antisymm hEF
  intro y hy
  have hrange : LinearMap.range (Algebra.linearMap E F) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hinj : Function.Injective (Algebra.linearMap E F) :=
      RingHom.injective (algebraMap E F)
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_self, hfin_EF_eq_one]
  have hmem : (⟨y, hy⟩ : F) ∈ LinearMap.range (Algebra.linearMap E F) := by
    rw [hrange]; trivial
  obtain ⟨z, hz⟩ := hmem
  have : (z : L) = y := congrArg Subtype.val hz
  rw [← this]
  exact z.2

/-- General engine: if E = K(f) ≤ fixedField H and [FR4 K : E] ≤ |H| (with FiniteDimensional E (FR4 K)),
then fixedField H is purely transcendental over K. -/
private lemma fixedField_isRational_of_finrank_le {K : Type} [Field K]
    (H : Subgroup (FR4 K ≃ₐ[K] FR4 K)) [Fintype H]
    (f : Fin 4 → FR4 K)
    (hf : ∀ i, f i ∈ IntermediateField.fixedField H)
    [FiniteDimensional (IntermediateField.adjoin K (Set.range f)) (FR4 K)]
    (hfin : Module.finrank (IntermediateField.adjoin K (Set.range f)) (FR4 K) ≤ Fintype.card H) :
    IsRationalExtension K (IntermediateField.fixedField H) (Fin 4) := by
  let E := IntermediateField.adjoin K (Set.range f)
  let F := IntermediateField.fixedField H
  have hEF : E ≤ F := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    exact hf i
  have hfin_F : Module.finrank F (FR4 K) = Fintype.card H :=
    FixedPoints.finrank_eq_card H (FR4 K)
  have hEF_eq : E = F :=
    intermediateField_eq_of_finrank_le hEF (Fintype.card_pos_iff.mpr ⟨1⟩) hfin hfin_F
  have halg_E : Algebra.IsAlgebraic E (FR4 K) := Algebra.IsAlgebraic.of_finite E (FR4 K)
  have hrat_E : IsRationalExtension K E (Fin 4) := isRational_of_adjoin_fin4 f halg_E
  obtain ⟨eE⟩ := hrat_E.pure_transcendental
  exact ⟨⟨(IntermediateField.equivOfEq hEF_eq.symm).trans eE⟩⟩

/-- Abstract tower step: adjoining a single element α over E satisfying a nonzero polynomial of
degree ≤ d gives FiniteDimensional E E(α) and finrank E E(α) ≤ d. -/
private lemma adjoin_finrank_le_of_poly {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (α : L) {d : ℕ}
    (P : Polynomial E) (hP0 : P ≠ 0) (hPdeg : P.natDegree ≤ d) (hPα : Polynomial.aeval α P = 0) :
    FiniteDimensional E (IntermediateField.adjoin E ({α} : Set L)) ∧
      Module.finrank E (IntermediateField.adjoin E ({α} : Set L)) ≤ d := by
  have hint : IsIntegral E α := isAlgebraic_iff_isIntegral.mp ⟨P, hP0, hPα⟩
  refine ⟨IntermediateField.adjoin.finiteDimensional hint, ?_⟩
  rw [IntermediateField.adjoin.finrank hint]
  exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd E α hPα) hP0).trans hPdeg

/-- Helper for 1-step tower E(α) = ⊤. -/
private lemma finrank_le_of_single_gen {K : Type} [Field K]
    (E : IntermediateField K (FR4 K)) (α : FR4 K) {d : ℕ}
    (P : Polynomial E) (hP0 : P ≠ 0) (hPdeg : P.natDegree ≤ d) (hPα : Polynomial.aeval α P = 0)
    (hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
      IntermediateField.adjoin E ({α} : Set (FR4 K))) :
    FiniteDimensional E (FR4 K) ∧ Module.finrank E (FR4 K) ≤ d := by
  have htop : IntermediateField.adjoin E ({α} : Set (FR4 K)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hKtop : (IntermediateField.adjoin E ({α} : Set (FR4 K))).restrictScalars K = ⊤ :=
      mem_intermediateField_of_mem_X _ hgen
    have : y ∈ (IntermediateField.adjoin E ({α} : Set (FR4 K))).restrictScalars K := by
      rw [hKtop]; trivial
    exact this
  obtain ⟨hfd, hle⟩ := adjoin_finrank_le_of_poly E α P hP0 hPdeg hPα
  have hEqvTop : IntermediateField.adjoin E ({α} : Set (FR4 K)) ≃ₗ[E] FR4 K :=
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).toLinearEquiv
  exact ⟨hEqvTop.finiteDimensional, by rw [← hEqvTop.finrank_eq]; exact hle⟩

/-- Helper for 2-step tower E(α)(β) = ⊤. -/
private lemma finrank_le_of_two_gen {K : Type} [Field K]
    (E : IntermediateField K (FR4 K)) (α β : FR4 K) {d1 d2 : ℕ}
    (P1 : Polynomial E) (hP10 : P1 ≠ 0) (hP1deg : P1.natDegree ≤ d1) (hP1α : Polynomial.aeval α P1 = 0)
    (P2 : Polynomial ((IntermediateField.adjoin E ({α} : Set (FR4 K))).restrictScalars K))
    (hP20 : P2 ≠ 0) (hP2deg : P2.natDegree ≤ d2) (hP2β : Polynomial.aeval β P2 = 0)
    (hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
      IntermediateField.adjoin ((IntermediateField.adjoin E ({α} : Set (FR4 K))).restrictScalars K)
        ({β} : Set (FR4 K))) :
    FiniteDimensional E (FR4 K) ∧ Module.finrank E (FR4 K) ≤ d1 * d2 := by
  let M1 : IntermediateField K (FR4 K) := (IntermediateField.adjoin E ({α} : Set (FR4 K))).restrictScalars K
  have hEM1 : E ≤ M1 := fun y hy => (IntermediateField.adjoin E ({α} : Set (FR4 K))).algebraMap_mem ⟨y, hy⟩
  obtain ⟨hfd1, hle1⟩ := adjoin_finrank_le_of_poly E α P1 hP10 hP1deg hP1α
  obtain ⟨hfd2, hle2⟩ := finrank_le_of_single_gen M1 β P2 hP20 hP2deg hP2β hgen
  letI : Algebra E M1 := (IntermediateField.inclusion hEM1).toRingHom.toAlgebra
  have hEqv1 : IntermediateField.adjoin E ({α} : Set (FR4 K)) ≃ₗ[E] M1 :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : FiniteDimensional E M1 := hEqv1.finiteDimensional
  have hle1' : Module.finrank E M1 ≤ d1 := by rw [← hEqv1.finrank_eq]; exact hle1
  haveI : IsScalarTower E M1 (FR4 K) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Free E M1 := Module.Free.of_divisionRing E M1
  haveI : Module.Free M1 (FR4 K) := Module.Free.of_divisionRing M1 (FR4 K)
  refine ⟨FiniteDimensional.trans E M1 (FR4 K), ?_⟩
  rw [← Module.finrank_mul_finrank E M1 (FR4 K)]
  exact Nat.mul_le_mul hle1' hle2

/-- Helper for 3-step tower E(α)(β)(γ) = ⊤. -/
private lemma finrank_le_of_three_gen {K : Type} [Field K]
    (E : IntermediateField K (FR4 K)) (α β γ : FR4 K) {d1 d2 d3 : ℕ}
    (P1 : Polynomial E) (hP10 : P1 ≠ 0) (hP1deg : P1.natDegree ≤ d1) (hP1α : Polynomial.aeval α P1 = 0)
    (P2 : Polynomial ((IntermediateField.adjoin E ({α} : Set (FR4 K))).restrictScalars K))
    (hP20 : P2 ≠ 0) (hP2deg : P2.natDegree ≤ d2) (hP2β : Polynomial.aeval β P2 = 0)
    (P3 : Polynomial ((IntermediateField.adjoin
      ((IntermediateField.adjoin E ({α} : Set (FR4 K))).restrictScalars K)
      ({β} : Set (FR4 K))).restrictScalars K))
    (hP30 : P3 ≠ 0) (hP3deg : P3.natDegree ≤ d3) (hP3γ : Polynomial.aeval γ P3 = 0)
    (hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
      IntermediateField.adjoin ((IntermediateField.adjoin
        ((IntermediateField.adjoin E ({α} : Set (FR4 K))).restrictScalars K)
        ({β} : Set (FR4 K))).restrictScalars K) ({γ} : Set (FR4 K))) :
    FiniteDimensional E (FR4 K) ∧ Module.finrank E (FR4 K) ≤ d1 * (d2 * d3) := by
  let M1 : IntermediateField K (FR4 K) := (IntermediateField.adjoin E ({α} : Set (FR4 K))).restrictScalars K
  have hEM1 : E ≤ M1 := fun y hy => (IntermediateField.adjoin E ({α} : Set (FR4 K))).algebraMap_mem ⟨y, hy⟩
  obtain ⟨hfd1, hle1⟩ := adjoin_finrank_le_of_poly E α P1 hP10 hP1deg hP1α
  obtain ⟨hfd23, hle23⟩ := finrank_le_of_two_gen M1 β γ P2 hP20 hP2deg hP2β P3 hP30 hP3deg hP3γ hgen
  letI : Algebra E M1 := (IntermediateField.inclusion hEM1).toRingHom.toAlgebra
  have hEqv1 : IntermediateField.adjoin E ({α} : Set (FR4 K)) ≃ₗ[E] M1 :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : FiniteDimensional E M1 := hEqv1.finiteDimensional
  have hle1' : Module.finrank E M1 ≤ d1 := by rw [← hEqv1.finrank_eq]; exact hle1
  haveI : IsScalarTower E M1 (FR4 K) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Free E M1 := Module.Free.of_divisionRing E M1
  haveI : Module.Free M1 (FR4 K) := Module.Free.of_divisionRing M1 (FR4 K)
  refine ⟨FiniteDimensional.trans E M1 (FR4 K), ?_⟩
  rw [← Module.finrank_mul_finrank E M1 (FR4 K)]
  exact Nat.mul_le_mul hle1' hle23

/-- Polynomial evaluation and degree helpers (abstract over IntermediateField to avoid unfolding). -/
private lemma natDegree_C_mul_X_le' {E : Type*} [Field E] (a : E) :
    (Polynomial.C a * Polynomial.X : Polynomial E).natDegree ≤ 1 :=
  (Polynomial.natDegree_C_mul_le a Polynomial.X).trans (by simp)

private lemma natDegree_quad_le {E : Type*} [Field E] (a b : E) :
    (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial E).natDegree ≤ 2 := by
  calc (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree
      ≤ max (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X).natDegree (Polynomial.C b).natDegree :=
        Polynomial.natDegree_add_le _ _
    _ ≤ 2 := by
      rw [max_le_iff]; refine ⟨?_, by simp⟩
      calc (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X).natDegree
          ≤ max (Polynomial.X ^ 2 : Polynomial E).natDegree (Polynomial.C a * Polynomial.X).natDegree :=
            Polynomial.natDegree_add_le _ _
        _ ≤ 2 := by
          rw [max_le_iff]; exact ⟨by simp, (natDegree_C_mul_X_le' a).trans (by norm_num)⟩

private lemma quad_ne_zero {E : Type*} [Field E] (a b : E) :
    (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial E) ≠ 0 := by
  intro h
  have hc := congrArg (fun q => Polynomial.coeff q 2) h
  simp [Polynomial.coeff_X_pow] at hc

private lemma aeval_quad_apply {K L : Type*} [Field K] [Field L] [Algebra K L]
    {E : IntermediateField K L} (a b : E) (z : L) :
    Polynomial.aeval z (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b) =
      z ^ 2 + (a : L) * z + (b : L) := by
  rw [map_add, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_C]
  rfl

private lemma natDegree_cubic_le {E : Type*} [Field E] (a b c : E) :
    (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
      Polynomial.C c : Polynomial E).natDegree ≤ 3 := by
  calc (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
        Polynomial.C c).natDegree
      ≤ max (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X).natDegree
          (Polynomial.C c).natDegree := Polynomial.natDegree_add_le _ _
    _ ≤ 3 := by
      rw [max_le_iff]; refine ⟨?_, by simp⟩
      calc (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X).natDegree
          ≤ max (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2).natDegree
              (Polynomial.C b * Polynomial.X).natDegree := Polynomial.natDegree_add_le _ _
        _ ≤ 3 := by
          rw [max_le_iff]; refine ⟨?_, (natDegree_C_mul_X_le' b).trans (by norm_num)⟩
          calc (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2).natDegree
              ≤ max (Polynomial.X ^ 3 : Polynomial E).natDegree (Polynomial.C a * Polynomial.X ^ 2).natDegree :=
                Polynomial.natDegree_add_le _ _
            _ ≤ 3 := by
              rw [max_le_iff]; refine ⟨by simp, ?_⟩
              exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)

private lemma cubic_ne_zero {E : Type*} [Field E] (a b c : E) :
    (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
      Polynomial.C c : Polynomial E) ≠ 0 := by
  intro h
  have hc := congrArg (fun q => Polynomial.coeff q 3) h
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hc

private lemma aeval_cubic_apply {K L : Type*} [Field K] [Field L] [Algebra K L]
    {E : IntermediateField K L} (a b c : E) (z : L) :
    Polynomial.aeval z (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 +
      Polynomial.C b * Polynomial.X + Polynomial.C c) =
      z ^ 3 + (a : L) * z ^ 2 + (b : L) * z + (c : L) := by
  rw [map_add, map_add, map_add, map_mul, map_mul, map_pow, map_pow,
    Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_C]
  rfl

/-- Non-vanishing helper: if a polynomial p : A4 K evaluates to a nonzero value at some v : Fin 4 → K,
then algebraMap (A4 K) (FR4 K) p ≠ 0. -/
private lemma algebraMap_ne_zero_of_eval {K : Type} [Field K] (p : A4 K) (v : Fin 4 → K)
    (hv : MvPolynomial.eval v p ≠ 0) :
    algebraMap (A4 K) (FR4 K) p ≠ 0 := by
  intro h
  have hp0 : p = 0 := IsFractionRing.injective (A4 K) (FR4 K) (h.trans (map_zero _).symm)
  rw [hp0, map_zero] at hv
  exact hv rfl

/-- Case |G| = 24: full symmetric group S_4 via esymmAlgEquiv. -/
private lemma prod_rename_symm {K : Type} [Field K] (q : A4 K) (τ : Perm (Fin 4)) :
    rename τ (∏ σ : Perm (Fin 4), rename σ q) = ∏ σ : Perm (Fin 4), rename σ q := by
  rw [map_prod]
  simp_rw [rename_rename]
  exact Fintype.prod_equiv (Equiv.mulLeft τ) (fun σ => rename (⇑τ ∘ ⇑σ) q)
    (fun σ => rename ⇑σ q) (fun σ => by simp [Perm.coe_mul])

private lemma fixedField_full_symm {K : Type} [Field K]
    (H : Subgroup (FR4 K ≃ₐ[K] FR4 K))
    (hH : ∀ σ : Perm (Fin 4), permAut K σ ∈ H)
    (hHsub : ∀ h ∈ H, ∃ σ : Perm (Fin 4), h = permAut K σ) :
    IsRationalExtension K (IntermediateField.fixedField H) (Fin 4) := by
  classical
  set E := IntermediateField.fixedField H
  let s := esymmAlgEquiv (Fin 4) K (Fintype.card_fin 4)
  let f : A4 K →+* FR4 K := (algebraMap (A4 K) (FR4 K)).comp
    ((symmetricSubalgebra (Fin 4) K).val.toRingHom.comp (s : A4 K →+* symmetricSubalgebra (Fin 4) K))
  have hf : ∀ p, f p = algebraMap (A4 K) (FR4 K) (s p : A4 K) := fun _ => rfl
  have fmem : ∀ p, f p ∈ E := by
    intro p
    rw [IntermediateField.mem_fixedField_iff]
    intro h hh
    obtain ⟨σ, rfl⟩ := hHsub h hh
    rw [hf, permAut_algebraMap, (s p).2 σ]
  let g : A4 K →+* E := f.codRestrict E fmem
  have hg : ∀ p, (g p : FR4 K) = algebraMap (A4 K) (FR4 K) (s p : A4 K) := fun _ => rfl
  have ginj : Function.Injective g := by
    intro p q hpq
    have h1 : (g p : FR4 K) = g q := congrArg Subtype.val hpq
    rw [hg, hg] at h1
    exact s.injective (Subtype.ext (IsFractionRing.injective (A4 K) (FR4 K) h1))
  letI : Algebra (A4 K) E := g.toAlgebra
  have hgalg : ∀ p, algebraMap (A4 K) E p = g p := fun _ => rfl
  have : FaithfulSMul (A4 K) E := (faithfulSMul_iff_algebraMap_injective (A4 K) E).mpr ginj
  have hsurj : ∀ z : E, ∃ x y : A4 K, z = algebraMap (A4 K) E x / algebraMap (A4 K) E y := by
    intro z
    have hz : ∀ σ : Perm (Fin 4), permAut K σ (z : FR4 K) = z := fun σ =>
      (IntermediateField.mem_fixedField_iff H (z : FR4 K)).mp z.2 (permAut K σ) (hH σ)
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := A4 K) (z : FR4 K)
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have haq : algebraMap (A4 K) (FR4 K) q ≠ 0 := by
      intro h; exact hq0 (IsFractionRing.injective (A4 K) (FR4 K) (h.trans (map_zero _).symm))
    set R := ∏ σ ∈ Finset.univ.erase (1 : Perm (Fin 4)), rename σ q with hRd
    set Q := ∏ σ : Perm (Fin 4), rename σ q with hQd
    have hQ : Q = q * R := by
      rw [hQd, hRd, ← Finset.mul_prod_erase Finset.univ (fun σ : Perm (Fin 4) => rename σ q)
        (Finset.mem_univ 1)]
      simp [Perm.coe_one, rename_id]
    have hQsym : Q.IsSymmetric := fun τ => prod_rename_symm q τ
    have hQ0 : Q ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro σ _
      exact (rename_injective _ σ.injective).ne_iff' (map_zero _) |>.mpr hq0
    have hkey : algebraMap (A4 K) (FR4 K) (p * R) = (z : FR4 K) * algebraMap (A4 K) (FR4 K) Q := by
      rw [← hpq, hQ, map_mul, map_mul, div_mul_eq_mul_div, eq_div_iff haq]
      ring
    have hPsym : (p * R).IsSymmetric := by
      intro τ
      apply IsFractionRing.injective (A4 K) (FR4 K)
      rw [← permAut_algebraMap, hkey, map_mul, hz τ, permAut_algebraMap, hQsym τ]
    refine ⟨s.symm ⟨p * R, hPsym⟩, s.symm ⟨Q, hQsym⟩, ?_⟩
    have hgy : g (s.symm ⟨Q, hQsym⟩) ≠ 0 := by
      rw [Ne, ← map_zero g]
      intro h
      have := ginj h
      rw [← map_zero s.symm] at this
      exact hQ0 (congrArg Subtype.val (s.symm.injective this))
    rw [hgalg, hgalg, eq_div_iff hgy]
    apply Subtype.ext
    rw [IntermediateField.coe_mul, hg, hg]
    simp only [AlgEquiv.apply_symm_apply, hkey]
  have : IsFractionRing (A4 K) E := IsFractionRing.of_field (A4 K) E hsurj
  let eqv : FR4 K ≃ₐ[A4 K] E := IsLocalization.algEquiv (nonZeroDivisors (A4 K)) (FR4 K) E
  have hcomm : ∀ k : K, eqv.toRingEquiv (algebraMap K (FR4 K) k) = algebraMap K E k := by
    intro k
    rw [IsScalarTower.algebraMap_apply K (A4 K) (FR4 K) k]
    change eqv (algebraMap (A4 K) (FR4 K) (algebraMap K (A4 K) k)) = _
    rw [AlgEquiv.commutes, hgalg]
    apply Subtype.ext
    rw [hg, AlgEquiv.commutes]
    change algebraMap (A4 K) (FR4 K) (algebraMap K (A4 K) k) = _
    rw [← IsScalarTower.algebraMap_apply K (A4 K) (FR4 K)]
    rfl
  exact ⟨⟨(AlgEquiv.ofRingEquiv (f := eqv.toRingEquiv) hcomm).symm⟩⟩

/-- Case 1 (|G| = 2): G = ⟨swap 0 1⟩. -/
private lemma fixedField_swap01 {K : Type} [Field K]
    (H : Subgroup (FR4 K ≃ₐ[K] FR4 K)) [Fintype H]
    (hcard : Fintype.card H = 2)
    (hHsub : ∀ h ∈ H, h = 1 ∨ h = permAut K (Equiv.swap 0 1)) :
    IsRationalExtension K (IntermediateField.fixedField H) (Fin 4) := by
  classical
  set x0 : FR4 K := algebraMap (A4 K) (FR4 K) (X 0)
  set x1 : FR4 K := algebraMap (A4 K) (FR4 K) (X 1)
  set x2 : FR4 K := algebraMap (A4 K) (FR4 K) (X 2)
  set x3 : FR4 K := algebraMap (A4 K) (FR4 K) (X 3)
  have hτ0 : permAut K (Equiv.swap 0 1) x0 = x1 := by
    have : (Equiv.swap (0 : Fin 4) 1) 0 = 1 := by decide
    simp only [x0, x1, permAut_X, this]
  have hτ1 : permAut K (Equiv.swap 0 1) x1 = x0 := by
    have : (Equiv.swap (0 : Fin 4) 1) 1 = 0 := by decide
    simp only [x0, x1, permAut_X, this]
  have hτ2 : permAut K (Equiv.swap 0 1) x2 = x2 := by
    have : (Equiv.swap (0 : Fin 4) 1) 2 = 2 := by decide
    simp only [x2, permAut_X, this]
  have hτ3 : permAut K (Equiv.swap 0 1) x3 = x3 := by
    have : (Equiv.swap (0 : Fin 4) 1) 3 = 3 := by decide
    simp only [x3, permAut_X, this]
  let f : Fin 4 → FR4 K := ![x0 + x1, x0 * x1, x2, x3]
  have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
    intro i
    rw [IntermediateField.mem_fixedField_iff]
    intro h hh
    rcases hHsub h hh with rfl | rfl
    · rfl
    · fin_cases i
      · change permAut K (Equiv.swap 0 1) (x0 + x1) = x0 + x1; rw [map_add, hτ0, hτ1]; ring
      · change permAut K (Equiv.swap 0 1) (x0 * x1) = x0 * x1; rw [map_mul, hτ0, hτ1]; ring
      · change permAut K (Equiv.swap 0 1) x2 = x2; exact hτ2
      · change permAut K (Equiv.swap 0 1) x3 = x3; exact hτ3
  set E := IntermediateField.adjoin K (Set.range f)
  let e0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
  let e1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
  let e2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
  let e3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
  let P : Polynomial E := Polynomial.X ^ 2 + Polynomial.C (-e0) * Polynomial.X + Polynomial.C e1
  have hPα : Polynomial.aeval x0 P = 0 := by
    rw [show P = _ from rfl, aeval_quad_apply]
    change x0 ^ 2 + -(x0 + x1) * x0 + x0 * x1 = 0; ring
  have hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
      IntermediateField.adjoin E ({x0} : Set (FR4 K)) := by
    intro i
    set M := IntermediateField.adjoin E ({x0} : Set (FR4 K))
    have hx0 : x0 ∈ M := IntermediateField.subset_adjoin E _ rfl
    have he0 : x0 + x1 ∈ M := M.algebraMap_mem e0
    fin_cases i
    · exact hx0
    · change x1 ∈ M; rw [show x1 = (x0 + x1) - x0 from by ring]; exact sub_mem he0 hx0
    · exact M.algebraMap_mem e2
    · exact M.algebraMap_mem e3
  obtain ⟨hfd, hle⟩ := finrank_le_of_single_gen E x0 P (quad_ne_zero _ _) (natDegree_quad_le _ _) hPα hgen
  exact fixedField_isRational_of_finrank_le H f hf (by rw [hcard]; exact hle)

/-- Case 2 (|G| = 2): G = ⟨(0 1)(2 3)⟩. -/
private lemma fixedField_swap01_23 {K : Type} [Field K]
    (H : Subgroup (FR4 K ≃ₐ[K] FR4 K)) [Fintype H]
    (hcard : Fintype.card H = 2)
    (hHsub : ∀ h ∈ H, h = 1 ∨ h = permAut K (Equiv.swap 0 1 * Equiv.swap 2 3)) :
    IsRationalExtension K (IntermediateField.fixedField H) (Fin 4) := by
  classical
  set σ : Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
  set x0 : FR4 K := algebraMap (A4 K) (FR4 K) (X 0)
  set x1 : FR4 K := algebraMap (A4 K) (FR4 K) (X 1)
  set x2 : FR4 K := algebraMap (A4 K) (FR4 K) (X 2)
  set x3 : FR4 K := algebraMap (A4 K) (FR4 K) (X 3)
  have hσ0 : permAut K σ x0 = x1 := by
    have : σ 0 = 1 := by decide
    simp only [x0, x1, permAut_X, this]
  have hσ1 : permAut K σ x1 = x0 := by
    have : σ 1 = 0 := by decide
    simp only [x0, x1, permAut_X, this]
  have hσ2 : permAut K σ x2 = x3 := by
    have : σ 2 = 3 := by decide
    simp only [x2, x3, permAut_X, this]
  have hσ3 : permAut K σ x3 = x2 := by
    have : σ 3 = 2 := by decide
    simp only [x2, x3, permAut_X, this]
  have hfix : ∀ y : FR4 K, permAut K σ y = y → y ∈ IntermediateField.fixedField H := by
    intro y hy
    rw [IntermediateField.mem_fixedField_iff]
    intro h hh
    rcases hHsub h hh with rfl | rfl
    · rfl
    · exact hy
  by_cases hchar2 : (2 : FR4 K) = 0
  · -- Characteristic 2: u = x0 + x1, v = x2 + x3, f = ![u, v, x0 * x1, x0 / u + x2 / v]
    set u : FR4 K := x0 + x1
    set v : FR4 K := x2 + x3
    have hu_ne : u ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 0 + X 1) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [u, x0, x1, map_add] using h
    have hv_ne : v ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 2 + X 3) (Pi.single (2 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [v, x2, x3, map_add] using h
    have hσu : permAut K σ u = u := by simp only [u, map_add, hσ0, hσ1]; ring
    have hσv : permAut K σ v = v := by simp only [v, map_add, hσ2, hσ3]; ring
    let f : Fin 4 → FR4 K := ![u, v, x0 * x1, x0 / u + x2 / v]
    have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
      intro i; apply hfix; fin_cases i
      · exact hσu
      · exact hσv
      · change permAut K σ (x0 * x1) = x0 * x1; rw [map_mul, hσ0, hσ1]; ring
      · change permAut K σ (x0 / u + x2 / v) = x0 / u + x2 / v
        rw [map_add, map_div₀, map_div₀, hσ0, hσ2, hσu, hσv]
        field_simp [hu_ne, hv_ne]; simp only [u, v]
        linear_combination (x1 * x3 - x0 * x2) * hchar2
    set E := IntermediateField.adjoin K (Set.range f)
    let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
    let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
    let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
    let g3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
    let P : Polynomial E := Polynomial.X ^ 2 + Polynomial.C (-g0) * Polynomial.X + Polynomial.C g2
    have hPα : Polynomial.aeval x0 P = 0 := by
      rw [show P = _ from rfl, aeval_quad_apply]
      change x0 ^ 2 + -(x0 + x1) * x0 + x0 * x1 = 0; ring
    have hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
        IntermediateField.adjoin E ({x0} : Set (FR4 K)) := by
      intro i
      set M := IntermediateField.adjoin E ({x0} : Set (FR4 K))
      have hx0 : x0 ∈ M := IntermediateField.subset_adjoin E _ rfl
      have huM : u ∈ M := M.algebraMap_mem g0
      have hvM : v ∈ M := M.algebraMap_mem g1
      have hqM : x0 / u + x2 / v ∈ M := M.algebraMap_mem g3
      have hx2 : x2 ∈ M := by
        have : x2 = v * ((x0 / u + x2 / v) - x0 / u) := by field_simp [hu_ne, hv_ne]; ring
        rw [this]; exact mul_mem hvM (sub_mem hqM (div_mem hx0 huM))
      fin_cases i
      · exact hx0
      · change x1 ∈ M; rw [show x1 = u - x0 from by simp only [u]; ring]; exact sub_mem huM hx0
      · exact hx2
      · change x3 ∈ M; rw [show x3 = v - x2 from by simp only [v]; ring]; exact sub_mem hvM hx2
    obtain ⟨hfd, hle⟩ := finrank_le_of_single_gen E x0 P (quad_ne_zero _ _) (natDegree_quad_le _ _) hPα hgen
    exact fixedField_isRational_of_finrank_le H f hf (by rw [hcard]; exact hle)
  · -- Characteristic ≠ 2: u = x0 + x1, v = x2 + x3, w = x0 - x1, z = x2 - x3, f = ![u, v, w^2, z / w]
    set u : FR4 K := x0 + x1
    set v : FR4 K := x2 + x3
    set w : FR4 K := x0 - x1
    set z : FR4 K := x2 - x3
    have hw_ne : w ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 0 - X 1) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [w, x0, x1, map_sub] using h
    have hσu : permAut K σ u = u := by simp only [u, map_add, hσ0, hσ1]; ring
    have hσv : permAut K σ v = v := by simp only [v, map_add, hσ2, hσ3]; ring
    have hσw : permAut K σ w = -w := by simp only [w, map_sub, hσ0, hσ1]; ring
    have hσz : permAut K σ z = -z := by simp only [z, map_sub, hσ2, hσ3]; ring
    let f : Fin 4 → FR4 K := ![u, v, w ^ 2, z / w]
    have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
      intro i; apply hfix; fin_cases i
      · exact hσu
      · exact hσv
      · change permAut K σ (w ^ 2) = w ^ 2; rw [map_pow, hσw]; ring
      · change permAut K σ (z / w) = z / w; rw [map_div₀, hσz, hσw, neg_div_neg_eq]
    set E := IntermediateField.adjoin K (Set.range f)
    let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
    let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
    let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
    let g3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
    let P : Polynomial E := Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X + Polynomial.C (-g2)
    have hPα : Polynomial.aeval w P = 0 := by
      rw [show P = _ from rfl, aeval_quad_apply]
      change w ^ 2 + 0 * w + -(w ^ 2) = 0; ring
    have hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
        IntermediateField.adjoin E ({w} : Set (FR4 K)) := by
      intro i
      set M := IntermediateField.adjoin E ({w} : Set (FR4 K))
      have hwM : w ∈ M := IntermediateField.subset_adjoin E _ rfl
      have huM : u ∈ M := M.algebraMap_mem g0
      have hvM : v ∈ M := M.algebraMap_mem g1
      have hzwM : z / w ∈ M := M.algebraMap_mem g3
      have hzM : z ∈ M := by
        have : z = (z / w) * w := (div_mul_cancel₀ z hw_ne).symm
        rw [this]; exact mul_mem hzwM hwM
      have h2M : (2 : FR4 K) ∈ M := M.algebraMap_mem (2 : E)
      fin_cases i
      · change x0 ∈ M
        have : x0 = (u + w) / 2 := by rw [eq_div_iff hchar2]; simp only [u, w]; ring
        rw [this]; exact div_mem (add_mem huM hwM) h2M
      · change x1 ∈ M
        have : x1 = (u - w) / 2 := by rw [eq_div_iff hchar2]; simp only [u, w]; ring
        rw [this]; exact div_mem (sub_mem huM hwM) h2M
      · change x2 ∈ M
        have : x2 = (v + z) / 2 := by rw [eq_div_iff hchar2]; simp only [v, z]; ring
        rw [this]; exact div_mem (add_mem hvM hzM) h2M
      · change x3 ∈ M
        have : x3 = (v - z) / 2 := by rw [eq_div_iff hchar2]; simp only [v, z]; ring
        rw [this]; exact div_mem (sub_mem hvM hzM) h2M
    obtain ⟨hfd, hle⟩ := finrank_le_of_single_gen E w P (quad_ne_zero _ _) (natDegree_quad_le _ _) hPα hgen
    exact fixedField_isRational_of_finrank_le H f hf (by rw [hcard]; exact hle)

set_option maxHeartbeats 800000 in
/-- Case 3 (|G| = 3): G = ⟨(0 1 2)⟩. Same generators as Noether3 plus x3. -/
private lemma fixedField_A3 {K : Type} [Field K]
    (H : Subgroup (FR4 K ≃ₐ[K] FR4 K)) [Fintype H]
    (hcard : Fintype.card H = 3)
    (hHsub : ∀ h ∈ H, h = 1 ∨ h = permAut K (Equiv.swap 0 1 * Equiv.swap 1 2) ∨
      h = permAut K ((Equiv.swap 0 1 * Equiv.swap 1 2) * (Equiv.swap 0 1 * Equiv.swap 1 2))) :
    IsRationalExtension K (IntermediateField.fixedField H) (Fin 4) := by
  classical
  set σ : Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
  set x0 : FR4 K := algebraMap (A4 K) (FR4 K) (X 0)
  set x1 : FR4 K := algebraMap (A4 K) (FR4 K) (X 1)
  set x2 : FR4 K := algebraMap (A4 K) (FR4 K) (X 2)
  set x3 : FR4 K := algebraMap (A4 K) (FR4 K) (X 3)
  have hσ0 : permAut K σ x0 = x1 := by have : σ 0 = 1 := (by decide); simp only [x0, x1, permAut_X, this]
  have hσ1 : permAut K σ x1 = x2 := by have : σ 1 = 2 := (by decide); simp only [x1, x2, permAut_X, this]
  have hσ2 : permAut K σ x2 = x0 := by have : σ 2 = 0 := (by decide); simp only [x2, x0, permAut_X, this]
  have hσ3 : permAut K σ x3 = x3 := by have : σ 3 = 3 := (by decide); simp only [x3, permAut_X, this]
  have hfix : ∀ y : FR4 K, permAut K σ y = y → y ∈ IntermediateField.fixedField H := by
    intro y hy
    rw [IntermediateField.mem_fixedField_iff]
    intro h hh
    rcases hHsub h hh with rfl | rfl | rfl
    · rfl
    · exact hy
    · rw [permAut_mul, AlgEquiv.mul_apply, hy, hy]
  by_cases hchar3 : (3 : FR4 K) = 0
  · set e1 : FR4 K := x0 + x1 + x2
    have he1_ne : e1 ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 0 + X 1 + X 2) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [e1, x0, x1, x2, map_add] using h
    set U : FR4 K := (x1 - x2) / e1
    have hσe1 : permAut K σ e1 = e1 := by simp only [e1, map_add, hσ0, hσ1, hσ2]; ring
    have hσU : permAut K σ U = U - 1 := by
      simp only [U, map_div₀, map_sub, hσ1, hσ2, hσe1]
      field_simp [he1_ne]; simp only [e1]; linear_combination x2 * hchar3
    let f : Fin 4 → FR4 K := ![e1, U ^ 3 - U, x0 + e1 * U ^ 2, x3]
    have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
      intro i; apply hfix; fin_cases i
      · exact hσe1
      · change permAut K σ (U ^ 3 - U) = U ^ 3 - U
        rw [map_sub, map_pow, hσU]; linear_combination (U - U ^ 2) * hchar3
      · change permAut K σ (x0 + e1 * U ^ 2) = x0 + e1 * U ^ 2
        rw [map_add, map_mul, map_pow, hσ0, hσe1, hσU]
        have hdiff : x1 - x0 + e1 * (1 - 2 * U) = 0 := by
          simp only [U]; field_simp [he1_ne]; simp only [e1]; linear_combination x2 * hchar3
        linear_combination hdiff
      · exact hσ3
    set E := IntermediateField.adjoin K (Set.range f)
    let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
    let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
    let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
    let g3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
    let P : Polynomial E :=
      Polynomial.X ^ 3 + Polynomial.C 0 * Polynomial.X ^ 2 + Polynomial.C (-1) * Polynomial.X + Polynomial.C (-g1)
    have hPα : Polynomial.aeval U P = 0 := by
      rw [show P = _ from rfl, aeval_cubic_apply]
      change U ^ 3 + 0 * U ^ 2 + -1 * U + -(U ^ 3 - U) = 0; ring
    have hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
        IntermediateField.adjoin E ({U} : Set (FR4 K)) := by
      intro i
      set M := IntermediateField.adjoin E ({U} : Set (FR4 K))
      have hU : U ∈ M := IntermediateField.subset_adjoin E _ rfl
      have hg0 : e1 ∈ M := M.algebraMap_mem g0
      have hg2 : x0 + e1 * U ^ 2 ∈ M := M.algebraMap_mem g2
      have hx0 : x0 ∈ M := by
        rw [show x0 = (x0 + e1 * U ^ 2) - e1 * U ^ 2 from by ring]
        exact sub_mem hg2 (mul_mem hg0 (pow_mem hU 2))
      have hx1 : x1 ∈ M := by
        have : x1 = -(e1 - x0 + e1 * U) := by
          simp only [U]; field_simp [he1_ne]; simp only [e1]; linear_combination x1 * hchar3
        rw [this]; exact neg_mem (add_mem (sub_mem hg0 hx0) (mul_mem hg0 hU))
      fin_cases i
      · exact hx0
      · exact hx1
      · change x2 ∈ M; rw [show x2 = e1 - x0 - x1 from by simp only [e1]; ring]
        exact sub_mem (sub_mem hg0 hx0) hx1
      · exact M.algebraMap_mem g3
    obtain ⟨hfd, hle⟩ := finrank_le_of_single_gen E U P (cubic_ne_zero _ _ _) (natDegree_cubic_le _ _ _) hPα hgen
    exact fixedField_isRational_of_finrank_le H f hf (by rw [hcard]; exact hle)
  · set w : FR4 K := x1 - x2
    have hw_ne : w ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 1 - X 2) (Pi.single (1 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [w, x1, x2, map_sub] using h
    set Z : FR4 K := (x0 - x1) / w
    have hZ_ne : Z ≠ 0 := div_ne_zero (by
      have h := algebraMap_ne_zero_of_eval (X 0 - X 1) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [x0, x1, map_sub] using h) hw_ne
    have hZ1_ne : Z + 1 ≠ 0 := by
      intro h
      have h2 : (x0 - x1) / w + 1 = 0 := h
      field_simp [hw_ne] at h2
      have h3 : x0 - x2 = 0 := by simp only [w] at h2; linear_combination h2
      have h4 := algebraMap_ne_zero_of_eval (X 0 - X 2) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      exact h4 (by simpa [x0, x2, map_sub] using h3)
    have hZ2_ne : Z ^ 2 + Z + 1 ≠ 0 := by
      intro h
      have h2 : ((x0 - x1) / w) ^ 2 + (x0 - x1) / w + 1 = 0 := h
      field_simp [hw_ne] at h2
      have hpoly : (x0 - x1) ^ 2 + (x0 - x1) * (x1 - x2) + (x1 - x2) ^ 2 = 0 := by
        simp only [w] at h2; linear_combination h2
      have h4 := algebraMap_ne_zero_of_eval
        ((X 0 - X 1) ^ 2 + (X 0 - X 1) * (X 1 - X 2) + (X 1 - X 2) ^ 2)
        (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      exact h4 (by simpa [x0, x1, x2, map_add, map_sub, map_mul, map_pow] using hpoly)
    have hσw : permAut K σ w = -(Z + 1) * w := by
      rw [show w = x1 - x2 from rfl, map_sub, hσ1, hσ2]
      have hZw : Z * w = x0 - x1 := div_mul_cancel₀ _ hw_ne
      rw [show -(Z + 1) * w = -(Z * w) - w from by ring, hZw]; simp only [w]; ring
    have hσZ : permAut K σ Z = -1 / (Z + 1) := by
      rw [show Z = (x0 - x1) / w from rfl, map_div₀, map_sub, hσ0, hσ1, hσw]
      change w / (-(Z + 1) * w) = -1 / (Z + 1); field_simp [hw_ne, hZ1_ne]
    let f : Fin 4 → FR4 K :=
      ![x0 + x1 + x2, (Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1)), w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1)), x3]
    have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
      intro i; apply hfix; fin_cases i
      · change permAut K σ (x0 + x1 + x2) = x0 + x1 + x2; rw [map_add, map_add, hσ0, hσ1, hσ2]; ring
      · change permAut K σ ((Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))) = (Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))
        simp only [map_div₀, map_sub, map_mul, map_pow, map_add, map_one, map_ofNat, hσZ]
        field_simp [hZ_ne, hZ1_ne]; ring
      · change permAut K σ (w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))) =
          w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))
        simp only [map_div₀, map_mul, map_pow, map_add, map_one, hσw, hσZ]
        field_simp [hZ_ne, hZ1_ne]; ring
      · exact hσ3
    set E := IntermediateField.adjoin K (Set.range f)
    let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
    let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
    let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
    let g3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
    let P : Polynomial E :=
      Polynomial.X ^ 3 + Polynomial.C (-g1) * Polynomial.X ^ 2 +
        Polynomial.C (-(g1 + 3)) * Polynomial.X + Polynomial.C (-1)
    have hPα : Polynomial.aeval Z P = 0 := by
      rw [show P = _ from rfl, aeval_cubic_apply]
      change Z ^ 3 + -((Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))) * Z ^ 2 +
        -(((Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))) + 3) * Z + -1 = 0
      field_simp [hZ_ne, hZ1_ne]; ring
    have hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
        IntermediateField.adjoin E ({Z} : Set (FR4 K)) := by
      intro i
      set M := IntermediateField.adjoin E ({Z} : Set (FR4 K))
      have hZ : Z ∈ M := IntermediateField.subset_adjoin E _ rfl
      have hg0 : x0 + x1 + x2 ∈ M := M.algebraMap_mem g0
      have hg2 : w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1)) ∈ M := M.algebraMap_mem g2
      have hw : w ∈ M := by
        have hZ2' : Z * (Z + 1) + 1 ≠ 0 := by convert hZ2_ne using 1; ring
        have : w = (w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))) * (Z * (Z + 1)) / (Z ^ 2 + Z + 1) ^ 2 := by
          field_simp [hZ_ne, hZ1_ne, hZ2_ne, hZ2']
        rw [this]
        exact div_mem (mul_mem hg2 (mul_mem hZ (add_mem hZ M.one_mem)))
          (pow_mem (add_mem (add_mem (pow_mem hZ 2) hZ) M.one_mem) 2)
      have hx0 : x0 ∈ M := by
        have hZw : Z * w = x0 - x1 := div_mul_cancel₀ _ hw_ne
        have : x0 = ((x0 + x1 + x2) + (2 * Z + 1) * w) / 3 := by
          rw [eq_div_iff hchar3, show (2 * Z + 1) * w = 2 * (Z * w) + w from by ring, hZw]
          simp only [w]; ring
        rw [this]
        exact div_mem (add_mem hg0 (mul_mem (add_mem (mul_mem (M.algebraMap_mem (2 : E)) hZ) M.one_mem) hw))
          (M.algebraMap_mem (3 : E))
      have hx1 : x1 ∈ M := by
        have hZw : Z * w = x0 - x1 := div_mul_cancel₀ _ hw_ne
        have : x1 = x0 - Z * w := by rw [hZw]; ring
        rw [this]; exact sub_mem hx0 (mul_mem hZ hw)
      fin_cases i
      · exact hx0
      · exact hx1
      · change x2 ∈ M; rw [show x2 = x1 - w from by simp only [w]; ring]; exact sub_mem hx1 hw
      · exact M.algebraMap_mem g3
    obtain ⟨hfd, hle⟩ := finrank_le_of_single_gen E Z P (cubic_ne_zero _ _ _) (natDegree_cubic_le _ _ _) hPα hgen
    exact fixedField_isRational_of_finrank_le H f hf (by rw [hcard]; exact hle)

/-- Case 4 (|G| = 4): non-normal Klein 4-group ⟨(0 1), (2 3)⟩. -/
private lemma fixedField_K4_nonnormal {K : Type} [Field K]
    (H : Subgroup (FR4 K ≃ₐ[K] FR4 K)) [Fintype H]
    (hcard : Fintype.card H = 4)
    (hHsub : ∀ h ∈ H, h = 1 ∨ h = permAut K (Equiv.swap 0 1) ∨
      h = permAut K (Equiv.swap 2 3) ∨ h = permAut K (Equiv.swap 0 1 * Equiv.swap 2 3)) :
    IsRationalExtension K (IntermediateField.fixedField H) (Fin 4) := by
  classical
  set x0 : FR4 K := algebraMap (A4 K) (FR4 K) (X 0)
  set x1 : FR4 K := algebraMap (A4 K) (FR4 K) (X 1)
  set x2 : FR4 K := algebraMap (A4 K) (FR4 K) (X 2)
  set x3 : FR4 K := algebraMap (A4 K) (FR4 K) (X 3)
  let f : Fin 4 → FR4 K := ![x0 + x1, x0 * x1, x2 + x3, x2 * x3]
  have hfix_s01 : ∀ i, permAut K (Equiv.swap 0 1) (f i) = f i := by
    intro i
    have h0 : permAut K (Equiv.swap 0 1) x0 = x1 := by have : (Equiv.swap (0 : Fin 4) 1) 0 = 1 := (by decide); simp only [x0, x1, permAut_X, this]
    have h1 : permAut K (Equiv.swap 0 1) x1 = x0 := by have : (Equiv.swap (0 : Fin 4) 1) 1 = 0 := (by decide); simp only [x0, x1, permAut_X, this]
    have h2 : permAut K (Equiv.swap 0 1) x2 = x2 := by have : (Equiv.swap (0 : Fin 4) 1) 2 = 2 := (by decide); simp only [x2, permAut_X, this]
    have h3 : permAut K (Equiv.swap 0 1) x3 = x3 := by have : (Equiv.swap (0 : Fin 4) 1) 3 = 3 := (by decide); simp only [x3, permAut_X, this]
    fin_cases i
    · change permAut K (Equiv.swap 0 1) (x0 + x1) = x0 + x1; rw [map_add, h0, h1]; ring
    · change permAut K (Equiv.swap 0 1) (x0 * x1) = x0 * x1; rw [map_mul, h0, h1]; ring
    · change permAut K (Equiv.swap 0 1) (x2 + x3) = x2 + x3; rw [map_add, h2, h3]
    · change permAut K (Equiv.swap 0 1) (x2 * x3) = x2 * x3; rw [map_mul, h2, h3]
  have hfix_s23 : ∀ i, permAut K (Equiv.swap 2 3) (f i) = f i := by
    intro i
    have h0 : permAut K (Equiv.swap 2 3) x0 = x0 := by have : (Equiv.swap (2 : Fin 4) 3) 0 = 0 := (by decide); simp only [x0, permAut_X, this]
    have h1 : permAut K (Equiv.swap 2 3) x1 = x1 := by have : (Equiv.swap (2 : Fin 4) 3) 1 = 1 := (by decide); simp only [x1, permAut_X, this]
    have h2 : permAut K (Equiv.swap 2 3) x2 = x3 := by have : (Equiv.swap (2 : Fin 4) 3) 2 = 3 := (by decide); simp only [x2, x3, permAut_X, this]
    have h3 : permAut K (Equiv.swap 2 3) x3 = x2 := by have : (Equiv.swap (2 : Fin 4) 3) 3 = 2 := (by decide); simp only [x2, x3, permAut_X, this]
    fin_cases i
    · change permAut K (Equiv.swap 2 3) (x0 + x1) = x0 + x1; rw [map_add, h0, h1]
    · change permAut K (Equiv.swap 2 3) (x0 * x1) = x0 * x1; rw [map_mul, h0, h1]
    · change permAut K (Equiv.swap 2 3) (x2 + x3) = x2 + x3; rw [map_add, h2, h3]; ring
    · change permAut K (Equiv.swap 2 3) (x2 * x3) = x2 * x3; rw [map_mul, h2, h3]; ring
  have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
    intro i
    rw [IntermediateField.mem_fixedField_iff]
    intro h hh
    rcases hHsub h hh with rfl | rfl | rfl | rfl
    · rfl
    · exact hfix_s01 i
    · exact hfix_s23 i
    · rw [permAut_mul, AlgEquiv.mul_apply, hfix_s23 i, hfix_s01 i]
  set E := IntermediateField.adjoin K (Set.range f)
  let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
  let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
  let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
  let g3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
  let P1 : Polynomial E := Polynomial.X ^ 2 + Polynomial.C (-g0) * Polynomial.X + Polynomial.C g1
  have hP1 : Polynomial.aeval x0 P1 = 0 := by
    rw [show P1 = _ from rfl, aeval_quad_apply]
    change x0 ^ 2 + -(x0 + x1) * x0 + x0 * x1 = 0; ring
  set M1 : IntermediateField K (FR4 K) := (IntermediateField.adjoin E ({x0} : Set (FR4 K))).restrictScalars K
  let g2' : M1 := ⟨f 2, (IntermediateField.adjoin E ({x0} : Set (FR4 K))).algebraMap_mem g2⟩
  let g3' : M1 := ⟨f 3, (IntermediateField.adjoin E ({x0} : Set (FR4 K))).algebraMap_mem g3⟩
  let P2 : Polynomial M1 := Polynomial.X ^ 2 + Polynomial.C (-g2') * Polynomial.X + Polynomial.C g3'
  have hP2 : Polynomial.aeval x2 P2 = 0 := by
    rw [show P2 = _ from rfl, aeval_quad_apply]
    change x2 ^ 2 + -(x2 + x3) * x2 + x2 * x3 = 0; ring
  have hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
      IntermediateField.adjoin M1 ({x2} : Set (FR4 K)) := by
    intro i
    set M2 := IntermediateField.adjoin M1 ({x2} : Set (FR4 K))
    have hx0 : x0 ∈ M2 := M2.algebraMap_mem ⟨x0, IntermediateField.subset_adjoin E _ rfl⟩
    have hx2 : x2 ∈ M2 := IntermediateField.subset_adjoin M1 _ rfl
    have hg0M : x0 + x1 ∈ M2 := M2.algebraMap_mem ⟨f 0, (IntermediateField.adjoin E ({x0} : Set (FR4 K))).algebraMap_mem g0⟩
    have hg2M : x2 + x3 ∈ M2 := M2.algebraMap_mem g2'
    fin_cases i
    · exact hx0
    · change x1 ∈ M2; rw [show x1 = (x0 + x1) - x0 from by ring]; exact sub_mem hg0M hx0
    · exact hx2
    · change x3 ∈ M2; rw [show x3 = (x2 + x3) - x2 from by ring]; exact sub_mem hg2M hx2
  obtain ⟨hfd, hle⟩ := finrank_le_of_two_gen E x0 x2 P1 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP1
    P2 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP2 hgen
  exact fixedField_isRational_of_finrank_le H f hf (by rw [hcard]; exact hle)

set_option maxHeartbeats 600000 in
/-- Case 5 (|G| = 4): normal Klein 4-group V_4 = {1, (0 1)(2 3), (0 2)(1 3), (0 3)(1 2)}. -/
private lemma fixedField_V4 {K : Type} [Field K]
    (H : Subgroup (FR4 K ≃ₐ[K] FR4 K)) [Fintype H]
    (hcard : Fintype.card H = 4)
    (hHsub : ∀ h ∈ H, h = 1 ∨ h = permAut K (Equiv.swap 0 1 * Equiv.swap 2 3) ∨
      h = permAut K (Equiv.swap 0 2 * Equiv.swap 1 3) ∨
      h = permAut K (Equiv.swap 0 3 * Equiv.swap 1 2)) :
    IsRationalExtension K (IntermediateField.fixedField H) (Fin 4) := by
  classical
  set σ1 : Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
  set σ2 : Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
  set σ3 : Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2
  have hσ3_eq : σ3 = σ1 * σ2 := by decide
  set x0 : FR4 K := algebraMap (A4 K) (FR4 K) (X 0)
  set x1 : FR4 K := algebraMap (A4 K) (FR4 K) (X 1)
  set x2 : FR4 K := algebraMap (A4 K) (FR4 K) (X 2)
  set x3 : FR4 K := algebraMap (A4 K) (FR4 K) (X 3)
  have h10 : permAut K σ1 x0 = x1 := by have : σ1 0 = 1 := (by decide); simp only [x0, x1, permAut_X, this]
  have h11 : permAut K σ1 x1 = x0 := by have : σ1 1 = 0 := (by decide); simp only [x0, x1, permAut_X, this]
  have h12 : permAut K σ1 x2 = x3 := by have : σ1 2 = 3 := (by decide); simp only [x2, x3, permAut_X, this]
  have h13 : permAut K σ1 x3 = x2 := by have : σ1 3 = 2 := (by decide); simp only [x2, x3, permAut_X, this]
  have h20 : permAut K σ2 x0 = x2 := by have : σ2 0 = 2 := (by decide); simp only [x0, x2, permAut_X, this]
  have h21 : permAut K σ2 x1 = x3 := by have : σ2 1 = 3 := (by decide); simp only [x1, x3, permAut_X, this]
  have h22 : permAut K σ2 x2 = x0 := by have : σ2 2 = 0 := (by decide); simp only [x0, x2, permAut_X, this]
  have h23 : permAut K σ2 x3 = x1 := by have : σ2 3 = 1 := (by decide); simp only [x1, x3, permAut_X, this]
  have hfix : ∀ y : FR4 K, permAut K σ1 y = y → permAut K σ2 y = y → y ∈ IntermediateField.fixedField H := by
    intro y hy1 hy2
    rw [IntermediateField.mem_fixedField_iff]
    intro h hh
    rcases hHsub h hh with rfl | rfl | rfl | rfl
    · rfl
    · exact hy1
    · exact hy2
    · change permAut K σ3 y = y; rw [hσ3_eq, permAut_mul, AlgEquiv.mul_apply, hy2, hy1]
  by_cases hchar2 : (2 : FR4 K) = 0
  · -- Characteristic 2: s = x0+x1+x2+x3, y1 = (x0+x1)/s, y2 = (x0+x2)/s, y3 = (x0+x3)/s
    set s : FR4 K := x0 + x1 + x2 + x3
    have hs_ne : s ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 0 + X 1 + X 2 + X 3) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [s, x0, x1, x2, x3, map_add] using h
    have hσ1s : permAut K σ1 s = s := by simp only [s, map_add, h10, h11, h12, h13]; ring
    have hσ2s : permAut K σ2 s = s := by simp only [s, map_add, h20, h21, h22, h23]; ring
    set y1 : FR4 K := (x0 + x1) / s
    set y2 : FR4 K := (x0 + x2) / s
    set y3 : FR4 K := (x0 + x3) / s
    have hy_sum : y1 + y2 + y3 = 1 := by
      simp only [y1, y2, y3]; field_simp [hs_ne]; simp only [s]; linear_combination x0 * hchar2
    have h1y1 : permAut K σ1 y1 = y1 := by simp only [y1, map_div₀, map_add, h10, h11, hσ1s]; ring
    have h1y2 : permAut K σ1 y2 = y2 + 1 := by
      simp only [y2, map_div₀, map_add, h10, h12, hσ1s]; field_simp [hs_ne]; simp only [s]; linear_combination (-x0 - x2) * hchar2
    have h1y3 : permAut K σ1 y3 = y3 + 1 := by
      simp only [y3, map_div₀, map_add, h10, h13, hσ1s]; field_simp [hs_ne]; simp only [s]; linear_combination (-x0 - x3) * hchar2
    have h2y1 : permAut K σ2 y1 = y1 + 1 := by
      simp only [y1, map_div₀, map_add, h20, h21, hσ2s]; field_simp [hs_ne]; simp only [s]; linear_combination (-x0 - x1) * hchar2
    have h2y2 : permAut K σ2 y2 = y2 := by simp only [y2, map_div₀, map_add, h20, h22, hσ2s]; ring
    have h2y3 : permAut K σ2 y3 = y3 + 1 := by
      simp only [y3, map_div₀, map_add, h20, h23, hσ2s]; field_simp [hs_ne]; simp only [s]; linear_combination (-x0 - x3) * hchar2
    set w : FR4 K := x0 / s + y1 * y2 + y2 * y3 + y3 * y1
    let f : Fin 4 → FR4 K := ![s, w, y1 ^ 2 + y1, y2 ^ 2 + y2]
    have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
      intro i; apply hfix <;> fin_cases i
      · exact hσ1s
      · change permAut K σ1 (x0 / s + y1 * y2 + y2 * y3 + y3 * y1) = x0 / s + y1 * y2 + y2 * y3 + y3 * y1
        rw [map_add, map_add, map_add, map_div₀, map_mul, map_mul, map_mul, h10, hσ1s, h1y1, h1y2, h1y3]
        have hx01 : x1 / s - x0 / s = y1 := by simp only [y1]; field_simp [hs_ne]; linear_combination (-x0) * hchar2
        linear_combination hx01 + hy_sum + (y1 + 1) * hchar2
      · change permAut K σ1 (y1 ^ 2 + y1) = y1 ^ 2 + y1; rw [map_add, map_pow, h1y1]
      · change permAut K σ1 (y2 ^ 2 + y2) = y2 ^ 2 + y2; rw [map_add, map_pow, h1y2]; linear_combination (y2 + 1) * hchar2
      · exact hσ2s
      · change permAut K σ2 (x0 / s + y1 * y2 + y2 * y3 + y3 * y1) = x0 / s + y1 * y2 + y2 * y3 + y3 * y1
        rw [map_add, map_add, map_add, map_div₀, map_mul, map_mul, map_mul, h20, hσ2s, h2y1, h2y2, h2y3]
        have hx02 : x2 / s - x0 / s = y2 := by simp only [y2]; field_simp [hs_ne]; linear_combination (-x0) * hchar2
        linear_combination hx02 + hy_sum + (y2 + 1) * hchar2
      · change permAut K σ2 (y1 ^ 2 + y1) = y1 ^ 2 + y1; rw [map_add, map_pow, h2y1]; linear_combination (y1 + 1) * hchar2
      · change permAut K σ2 (y2 ^ 2 + y2) = y2 ^ 2 + y2; rw [map_add, map_pow, h2y2]
    set E := IntermediateField.adjoin K (Set.range f)
    let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
    let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
    let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
    let g3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
    let P1 : Polynomial E := Polynomial.X ^ 2 + Polynomial.C 1 * Polynomial.X + Polynomial.C (-g2)
    have hP1 : Polynomial.aeval y1 P1 = 0 := by
      rw [show P1 = _ from rfl, aeval_quad_apply]
      change y1 ^ 2 + 1 * y1 + -(y1 ^ 2 + y1) = 0; ring
    set M1 : IntermediateField K (FR4 K) := (IntermediateField.adjoin E ({y1} : Set (FR4 K))).restrictScalars K
    let g3' : M1 := ⟨f 3, (IntermediateField.adjoin E ({y1} : Set (FR4 K))).algebraMap_mem g3⟩
    let P2 : Polynomial M1 := Polynomial.X ^ 2 + Polynomial.C 1 * Polynomial.X + Polynomial.C (-g3')
    have hP2 : Polynomial.aeval y2 P2 = 0 := by
      rw [show P2 = _ from rfl, aeval_quad_apply]
      change y2 ^ 2 + 1 * y2 + -(y2 ^ 2 + y2) = 0; ring
    have hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
        IntermediateField.adjoin M1 ({y2} : Set (FR4 K)) := by
      intro i
      set M2 := IntermediateField.adjoin M1 ({y2} : Set (FR4 K))
      have hsM : s ∈ M2 := M2.algebraMap_mem ⟨f 0, (IntermediateField.adjoin E ({y1} : Set (FR4 K))).algebraMap_mem g0⟩
      have hwM : w ∈ M2 := M2.algebraMap_mem ⟨f 1, (IntermediateField.adjoin E ({y1} : Set (FR4 K))).algebraMap_mem g1⟩
      have hy1M : y1 ∈ M2 := M2.algebraMap_mem ⟨y1, IntermediateField.subset_adjoin E _ rfl⟩
      have hy2M : y2 ∈ M2 := IntermediateField.subset_adjoin M1 _ rfl
      have hy3M : y3 ∈ M2 := by
        rw [show y3 = 1 - y1 - y2 from by linear_combination hy_sum]
        exact sub_mem (sub_mem M2.one_mem hy1M) hy2M
      have hx0M : x0 ∈ M2 := by
        have : x0 = s * (w - y1 * y2 - y2 * y3 - y3 * y1) := by
          simp only [w]; field_simp [hs_ne]; ring
        rw [this]
        exact mul_mem hsM (sub_mem (sub_mem (sub_mem hwM (mul_mem hy1M hy2M)) (mul_mem hy2M hy3M)) (mul_mem hy3M hy1M))
      fin_cases i
      · exact hx0M
      · change x1 ∈ M2
        rw [show x1 = s * y1 - x0 from by simp only [y1]; field_simp [hs_ne]; ring]
        exact sub_mem (mul_mem hsM hy1M) hx0M
      · change x2 ∈ M2
        rw [show x2 = s * y2 - x0 from by simp only [y2]; field_simp [hs_ne]; ring]
        exact sub_mem (mul_mem hsM hy2M) hx0M
      · change x3 ∈ M2
        rw [show x3 = s * y3 - x0 from by simp only [y3]; field_simp [hs_ne]; ring]
        exact sub_mem (mul_mem hsM hy3M) hx0M
    obtain ⟨hfd, hle⟩ := finrank_le_of_two_gen E y1 y2 P1 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP1
      P2 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP2 hgen
    exact fixedField_isRational_of_finrank_le H f hf (by rw [hcard]; exact hle)
  · -- Characteristic ≠ 2: s = x0+x1+x2+x3, y1 = x0+x1-x2-x3, y2 = x0-x1+x2-x3, y3 = x0-x1-x2+x3
    set s : FR4 K := x0 + x1 + x2 + x3
    set y1 : FR4 K := x0 + x1 - x2 - x3
    set y2 : FR4 K := x0 - x1 + x2 - x3
    set y3 : FR4 K := x0 - x1 - x2 + x3
    have hy1_ne : y1 ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 0 + X 1 - X 2 - X 3) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [y1, x0, x1, x2, x3, map_add, map_sub] using h
    have hy2_ne : y2 ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 0 - X 1 + X 2 - X 3) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [y2, x0, x1, x2, x3, map_add, map_sub] using h
    have h4_ne : (4 : FR4 K) ≠ 0 := by
      rw [show (4 : FR4 K) = 2 * 2 from by norm_num]; exact mul_ne_zero hchar2 hchar2
    have h1s : permAut K σ1 s = s := by simp only [s, map_add, h10, h11, h12, h13]; ring
    have h2s : permAut K σ2 s = s := by simp only [s, map_add, h20, h21, h22, h23]; ring
    have h1y1 : permAut K σ1 y1 = y1 := by simp only [y1, map_add, map_sub, h10, h11, h12, h13]; ring
    have h1y2 : permAut K σ1 y2 = -y2 := by simp only [y2, map_add, map_sub, h10, h11, h12, h13]; ring
    have h1y3 : permAut K σ1 y3 = -y3 := by simp only [y3, map_add, map_sub, h10, h11, h12, h13]; ring
    have h2y1 : permAut K σ2 y1 = -y1 := by simp only [y1, map_add, map_sub, h20, h21, h22, h23]; ring
    have h2y2 : permAut K σ2 y2 = y2 := by simp only [y2, map_add, map_sub, h20, h21, h22, h23]; ring
    have h2y3 : permAut K σ2 y3 = -y3 := by simp only [y3, map_add, map_sub, h20, h21, h22, h23]; ring
    let f : Fin 4 → FR4 K := ![s, y1 ^ 2, y2 ^ 2, y1 * y2 * y3]
    have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
      intro i; apply hfix <;> fin_cases i
      · exact h1s
      · change permAut K σ1 (y1 ^ 2) = y1 ^ 2; rw [map_pow, h1y1]
      · change permAut K σ1 (y2 ^ 2) = y2 ^ 2; rw [map_pow, h1y2]; ring
      · change permAut K σ1 (y1 * y2 * y3) = y1 * y2 * y3; rw [map_mul, map_mul, h1y1, h1y2, h1y3]; ring
      · exact h2s
      · change permAut K σ2 (y1 ^ 2) = y1 ^ 2; rw [map_pow, h2y1]; ring
      · change permAut K σ2 (y2 ^ 2) = y2 ^ 2; rw [map_pow, h2y2]
      · change permAut K σ2 (y1 * y2 * y3) = y1 * y2 * y3; rw [map_mul, map_mul, h2y1, h2y2, h2y3]; ring
    set E := IntermediateField.adjoin K (Set.range f)
    let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
    let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
    let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
    let g3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
    let P1 : Polynomial E := Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X + Polynomial.C (-g1)
    have hP1 : Polynomial.aeval y1 P1 = 0 := by
      rw [show P1 = _ from rfl, aeval_quad_apply]
      change y1 ^ 2 + 0 * y1 + -(y1 ^ 2) = 0; ring
    set M1 : IntermediateField K (FR4 K) := (IntermediateField.adjoin E ({y1} : Set (FR4 K))).restrictScalars K
    let g2' : M1 := ⟨f 2, (IntermediateField.adjoin E ({y1} : Set (FR4 K))).algebraMap_mem g2⟩
    let P2 : Polynomial M1 := Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X + Polynomial.C (-g2')
    have hP2 : Polynomial.aeval y2 P2 = 0 := by
      rw [show P2 = _ from rfl, aeval_quad_apply]
      change y2 ^ 2 + 0 * y2 + -(y2 ^ 2) = 0; ring
    have hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
        IntermediateField.adjoin M1 ({y2} : Set (FR4 K)) := by
      intro i
      set M2 := IntermediateField.adjoin M1 ({y2} : Set (FR4 K))
      have hsM : s ∈ M2 := M2.algebraMap_mem ⟨f 0, (IntermediateField.adjoin E ({y1} : Set (FR4 K))).algebraMap_mem g0⟩
      have hpM : y1 * y2 * y3 ∈ M2 := M2.algebraMap_mem ⟨f 3, (IntermediateField.adjoin E ({y1} : Set (FR4 K))).algebraMap_mem g3⟩
      have hy1M : y1 ∈ M2 := M2.algebraMap_mem ⟨y1, IntermediateField.subset_adjoin E _ rfl⟩
      have hy2M : y2 ∈ M2 := IntermediateField.subset_adjoin M1 _ rfl
      have hy3M : y3 ∈ M2 := by
        rw [show y3 = (y1 * y2 * y3) / (y1 * y2) from by field_simp [hy1_ne, hy2_ne]]
        exact div_mem hpM (mul_mem hy1M hy2M)
      have h4M : (4 : FR4 K) ∈ M2 := M2.algebraMap_mem (4 : M1)
      fin_cases i
      · change x0 ∈ M2
        rw [show x0 = (s + y1 + y2 + y3) / 4 from by rw [eq_div_iff h4_ne]; simp only [s, y1, y2, y3]; ring]
        exact div_mem (add_mem (add_mem (add_mem hsM hy1M) hy2M) hy3M) h4M
      · change x1 ∈ M2
        rw [show x1 = (s + y1 - y2 - y3) / 4 from by rw [eq_div_iff h4_ne]; simp only [s, y1, y2, y3]; ring]
        exact div_mem (sub_mem (sub_mem (add_mem hsM hy1M) hy2M) hy3M) h4M
      · change x2 ∈ M2
        rw [show x2 = (s - y1 + y2 - y3) / 4 from by rw [eq_div_iff h4_ne]; simp only [s, y1, y2, y3]; ring]
        exact div_mem (sub_mem (add_mem (sub_mem hsM hy1M) hy2M) hy3M) h4M
      · change x3 ∈ M2
        rw [show x3 = (s - y1 - y2 + y3) / 4 from by rw [eq_div_iff h4_ne]; simp only [s, y1, y2, y3]; ring]
        exact div_mem (add_mem (sub_mem (sub_mem hsM hy1M) hy2M) hy3M) h4M
    obtain ⟨hfd, hle⟩ := finrank_le_of_two_gen E y1 y2 P1 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP1
      P2 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP2 hgen
    exact fixedField_isRational_of_finrank_le H f hf (by rw [hcard]; exact hle)

set_option maxHeartbeats 600000 in
/-- Case 6 (|G| = 4): cyclic C_4 = ⟨(0 1 2 3)⟩. -/
private lemma fixedField_C4 {K : Type} [Field K]
    (H : Subgroup (FR4 K ≃ₐ[K] FR4 K)) [Fintype H]
    (hcard : Fintype.card H = 4)
    (hHsub : ∀ h ∈ H, h = 1 ∨
      h = permAut K (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3) ∨
      h = permAut K ((Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3) ^ 2) ∨
      h = permAut K ((Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3) ^ 3)) :
    IsRationalExtension K (IntermediateField.fixedField H) (Fin 4) := by
  classical
  set σ : Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3
  set x0 : FR4 K := algebraMap (A4 K) (FR4 K) (X 0)
  set x1 : FR4 K := algebraMap (A4 K) (FR4 K) (X 1)
  set x2 : FR4 K := algebraMap (A4 K) (FR4 K) (X 2)
  set x3 : FR4 K := algebraMap (A4 K) (FR4 K) (X 3)
  have hσ0 : permAut K σ x0 = x1 := by have : σ 0 = 1 := (by decide); simp only [x0, x1, permAut_X, this]
  have hσ1 : permAut K σ x1 = x2 := by have : σ 1 = 2 := (by decide); simp only [x1, x2, permAut_X, this]
  have hσ2 : permAut K σ x2 = x3 := by have : σ 2 = 3 := (by decide); simp only [x2, x3, permAut_X, this]
  have hσ3 : permAut K σ x3 = x0 := by have : σ 3 = 0 := (by decide); simp only [x3, x0, permAut_X, this]
  have hfix : ∀ y : FR4 K, permAut K σ y = y → y ∈ IntermediateField.fixedField H := by
    intro y hy
    rw [IntermediateField.mem_fixedField_iff]
    intro h hh
    rcases hHsub h hh with rfl | rfl | rfl | rfl
    · rfl
    · exact hy
    · rw [sq, permAut_mul, AlgEquiv.mul_apply, hy, hy]
    · rw [pow_succ, sq, permAut_mul, permAut_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hy, hy, hy]
  by_cases hchar2 : (2 : FR4 K) = 0
  · -- Characteristic 2: s = x0+x1+x2+x3, t = (x0+x2)/s, v = (x0+x1)/s
    set s : FR4 K := x0 + x1 + x2 + x3
    have hs_ne : s ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 0 + X 1 + X 2 + X 3) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [s, x0, x1, x2, x3, map_add] using h
    have hσs : permAut K σ s = s := by simp only [s, map_add, hσ0, hσ1, hσ2, hσ3]; ring
    set t : FR4 K := (x0 + x2) / s
    set v : FR4 K := (x0 + x1) / s
    have hσt : permAut K σ t = t + 1 := by
      simp only [t, map_div₀, map_add, hσ0, hσ2, hσs]; field_simp [hs_ne]; simp only [s]
      linear_combination (-x0 - x2) * hchar2
    have hσv : permAut K σ v = v + t := by
      simp only [v, t, map_div₀, map_add, hσ0, hσ1, hσs]; field_simp [hs_ne]
      linear_combination (-x0) * hchar2
    let f : Fin 4 → FR4 K := ![s, t ^ 2 + t, v ^ 2 + v + t * (t ^ 2 + t), x0 / s + t * v + t * (t ^ 2 + t)]
    have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
      intro i; apply hfix; fin_cases i
      · exact hσs
      · change permAut K σ (t ^ 2 + t) = t ^ 2 + t; rw [map_add, map_pow, hσt]; linear_combination (t + 1) * hchar2
      · change permAut K σ (v ^ 2 + v + t * (t ^ 2 + t)) = v ^ 2 + v + t * (t ^ 2 + t)
        simp only [map_add, map_mul, map_pow, hσv, hσt]
        linear_combination (v * t + 2 * t ^ 2 + 3 * t + 1) * hchar2
      · change permAut K σ (x0 / s + t * v + t * (t ^ 2 + t)) = x0 / s + t * v + t * (t ^ 2 + t)
        simp only [map_add, map_div₀, map_mul, map_pow, hσ0, hσs, hσt, hσv]
        have hx01 : x1 / s - x0 / s = v := by simp only [v]; field_simp [hs_ne]; linear_combination (-x0) * hchar2
        linear_combination hx01 + (v + 2 * t ^ 2 + 3 * t + 1) * hchar2
    set E := IntermediateField.adjoin K (Set.range f)
    let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
    let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
    let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
    let g3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
    let P1 : Polynomial E := Polynomial.X ^ 2 + Polynomial.C 1 * Polynomial.X + Polynomial.C (-g1)
    have hP1 : Polynomial.aeval t P1 = 0 := by
      rw [show P1 = _ from rfl, aeval_quad_apply]
      change t ^ 2 + 1 * t + -(t ^ 2 + t) = 0; ring
    set M1 : IntermediateField K (FR4 K) := (IntermediateField.adjoin E ({t} : Set (FR4 K))).restrictScalars K
    let tM1 : M1 := ⟨t, IntermediateField.subset_adjoin E _ rfl⟩
    let g1' : M1 := ⟨f 1, (IntermediateField.adjoin E ({t} : Set (FR4 K))).algebraMap_mem g1⟩
    let g2' : M1 := ⟨f 2, (IntermediateField.adjoin E ({t} : Set (FR4 K))).algebraMap_mem g2⟩
    let P2 : Polynomial M1 := Polynomial.X ^ 2 + Polynomial.C 1 * Polynomial.X + Polynomial.C (tM1 * g1' - g2')
    have hP2 : Polynomial.aeval v P2 = 0 := by
      rw [show P2 = _ from rfl, aeval_quad_apply]
      change v ^ 2 + 1 * v + (t * (t ^ 2 + t) - (v ^ 2 + v + t * (t ^ 2 + t))) = 0; ring
    have hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
        IntermediateField.adjoin M1 ({v} : Set (FR4 K)) := by
      intro i
      set M2 := IntermediateField.adjoin M1 ({v} : Set (FR4 K))
      have hsM : s ∈ M2 := M2.algebraMap_mem ⟨f 0, (IntermediateField.adjoin E ({t} : Set (FR4 K))).algebraMap_mem g0⟩
      have hg1M : t ^ 2 + t ∈ M2 := M2.algebraMap_mem g1'
      have hg3M : x0 / s + t * v + t * (t ^ 2 + t) ∈ M2 :=
        M2.algebraMap_mem ⟨f 3, (IntermediateField.adjoin E ({t} : Set (FR4 K))).algebraMap_mem g3⟩
      have htM : t ∈ M2 := M2.algebraMap_mem tM1
      have hvM : v ∈ M2 := IntermediateField.subset_adjoin M1 _ rfl
      have hx0M : x0 ∈ M2 := by
        have : x0 = s * ((x0 / s + t * v + t * (t ^ 2 + t)) - t * v - t * (t ^ 2 + t)) := by
          field_simp [hs_ne]; ring
        rw [this]
        exact mul_mem hsM (sub_mem (sub_mem hg3M (mul_mem htM hvM)) (mul_mem htM hg1M))
      have hx1M : x1 ∈ M2 := by
        rw [show x1 = s * v - x0 from by simp only [v]; field_simp [hs_ne]; ring]
        exact sub_mem (mul_mem hsM hvM) hx0M
      have hx2M : x2 ∈ M2 := by
        rw [show x2 = s * t - x0 from by simp only [t]; field_simp [hs_ne]; ring]
        exact sub_mem (mul_mem hsM htM) hx0M
      fin_cases i
      · exact hx0M
      · exact hx1M
      · exact hx2M
      · change x3 ∈ M2
        rw [show x3 = s - x0 - x1 - x2 from by simp only [s]; ring]
        exact sub_mem (sub_mem (sub_mem hsM hx0M) hx1M) hx2M
    obtain ⟨hfd, hle⟩ := finrank_le_of_two_gen E t v P1 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP1
      P2 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP2 hgen
    exact fixedField_isRational_of_finrank_le H f hf (by rw [hcard]; exact hle)
  · -- Characteristic ≠ 2: s = x0+x1+x2+x3, a = x0-x1+x2-x3, u = x0-x2, v = x1-x3, t = u/v
    set s : FR4 K := x0 + x1 + x2 + x3
    set a : FR4 K := x0 - x1 + x2 - x3
    set u : FR4 K := x0 - x2
    set v : FR4 K := x1 - x3
    have hv_ne : v ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 1 - X 3) (Pi.single (1 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [v, x1, x3, map_sub] using h
    have hu_ne : u ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 0 - X 2) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [u, x0, x2, map_sub] using h
    set t : FR4 K := u / v
    have ht_ne : t ≠ 0 := div_ne_zero hu_ne hv_ne
    have ht2_ne : t ^ 2 + 1 ≠ 0 := by
      intro h
      have h2 : (u / v) ^ 2 + 1 = 0 := h
      field_simp [hv_ne] at h2
      have h3 : (x0 - x2) ^ 2 + (x1 - x3) ^ 2 = 0 := by simpa [u, v] using h2
      have h4 := algebraMap_ne_zero_of_eval ((X 0 - X 2) ^ 2 + (X 1 - X 3) ^ 2)
        (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      exact h4 (by simpa [x0, x1, x2, x3, map_add, map_sub, map_pow] using h3)
    have h4_ne : (4 : FR4 K) ≠ 0 := by
      rw [show (4 : FR4 K) = 2 * 2 from by norm_num]; exact mul_ne_zero hchar2 hchar2
    have hσs : permAut K σ s = s := by simp only [s, map_add, hσ0, hσ1, hσ2, hσ3]; ring
    have hσa : permAut K σ a = -a := by simp only [a, map_add, map_sub, hσ0, hσ1, hσ2, hσ3]; ring
    have hσu : permAut K σ u = v := by simp only [u, v, map_sub, hσ0, hσ2]
    have hσv : permAut K σ v = -u := by simp only [u, v, map_sub, hσ1, hσ3]; ring
    have hσt : permAut K σ t = -1 / t := by
      simp only [t, map_div₀, hσu, hσv]; field_simp [hu_ne, hv_ne]
    let f : Fin 4 → FR4 K := ![s, t - 1 / t, a * (t + 1 / t), u ^ 2 + v ^ 2]
    have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
      intro i; apply hfix; fin_cases i
      · exact hσs
      · change permAut K σ (t - 1 / t) = t - 1 / t
        simp only [map_sub, map_div₀, map_one, hσt]; field_simp [ht_ne]; ring
      · change permAut K σ (a * (t + 1 / t)) = a * (t + 1 / t)
        simp only [map_mul, map_add, map_div₀, map_one, hσa, hσt]; field_simp [ht_ne]; ring
      · change permAut K σ (u ^ 2 + v ^ 2) = u ^ 2 + v ^ 2
        rw [map_add, map_pow, map_pow, hσu, hσv]; ring
    set E := IntermediateField.adjoin K (Set.range f)
    let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
    let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
    let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
    let g3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
    let P1 : Polynomial E := Polynomial.X ^ 2 + Polynomial.C (-g1) * Polynomial.X + Polynomial.C (-1)
    have hP1 : Polynomial.aeval t P1 = 0 := by
      rw [show P1 = _ from rfl, aeval_quad_apply]
      change t ^ 2 + -(t - 1 / t) * t + -1 = 0; field_simp [ht_ne]; ring
    set M1 : IntermediateField K (FR4 K) := (IntermediateField.adjoin E ({t} : Set (FR4 K))).restrictScalars K
    let tM1 : M1 := ⟨t, IntermediateField.subset_adjoin E _ rfl⟩
    let g3' : M1 := ⟨f 3, (IntermediateField.adjoin E ({t} : Set (FR4 K))).algebraMap_mem g3⟩
    let P2 : Polynomial M1 := Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X + Polynomial.C (-(g3' / (tM1 ^ 2 + 1)))
    have hP2 : Polynomial.aeval v P2 = 0 := by
      rw [show P2 = _ from rfl, aeval_quad_apply]
      change v ^ 2 + 0 * v + -((u ^ 2 + v ^ 2) / (t ^ 2 + 1)) = 0
      have huv : u = t * v := (div_mul_cancel₀ u hv_ne).symm
      rw [huv]; field_simp [ht2_ne]; ring
    have hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
        IntermediateField.adjoin M1 ({v} : Set (FR4 K)) := by
      intro i
      set M2 := IntermediateField.adjoin M1 ({v} : Set (FR4 K))
      have hsM : s ∈ M2 := M2.algebraMap_mem ⟨f 0, (IntermediateField.adjoin E ({t} : Set (FR4 K))).algebraMap_mem g0⟩
      have hg2M : a * (t + 1 / t) ∈ M2 := M2.algebraMap_mem ⟨f 2, (IntermediateField.adjoin E ({t} : Set (FR4 K))).algebraMap_mem g2⟩
      have htM : t ∈ M2 := M2.algebraMap_mem tM1
      have hvM : v ∈ M2 := IntermediateField.subset_adjoin M1 _ rfl
      have huM : u ∈ M2 := by
        rw [show u = t * v from (div_mul_cancel₀ u hv_ne).symm]
        exact mul_mem htM hvM
      have haM : a ∈ M2 := by
        have ht1 : t + 1 / t ≠ 0 := by
          intro h; apply ht2_ne; field_simp [ht_ne] at h; linear_combination h
        rw [show a = (a * (t + 1 / t)) / (t + 1 / t) from by field_simp [ht1]]
        exact div_mem hg2M (add_mem htM (div_mem M2.one_mem htM))
      have h4M : (4 : FR4 K) ∈ M2 := M2.algebraMap_mem (4 : M1)
      fin_cases i
      · change x0 ∈ M2
        rw [show x0 = (s + a + 2 * u) / 4 from by rw [eq_div_iff h4_ne]; simp only [s, a, u]; ring]
        exact div_mem (add_mem (add_mem hsM haM) (mul_mem (M2.algebraMap_mem (2 : M1)) huM)) h4M
      · change x1 ∈ M2
        rw [show x1 = (s - a + 2 * v) / 4 from by rw [eq_div_iff h4_ne]; simp only [s, a, v]; ring]
        exact div_mem (add_mem (sub_mem hsM haM) (mul_mem (M2.algebraMap_mem (2 : M1)) hvM)) h4M
      · change x2 ∈ M2
        rw [show x2 = (s + a - 2 * u) / 4 from by rw [eq_div_iff h4_ne]; simp only [s, a, u]; ring]
        exact div_mem (sub_mem (add_mem hsM haM) (mul_mem (M2.algebraMap_mem (2 : M1)) huM)) h4M
      · change x3 ∈ M2
        rw [show x3 = (s - a - 2 * v) / 4 from by rw [eq_div_iff h4_ne]; simp only [s, a, v]; ring]
        exact div_mem (sub_mem (sub_mem hsM haM) (mul_mem (M2.algebraMap_mem (2 : M1)) hvM)) h4M
    obtain ⟨hfd, hle⟩ := finrank_le_of_two_gen E t v P1 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP1
      P2 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP2 hgen
    exact fixedField_isRational_of_finrank_le H f hf (by rw [hcard]; exact hle)

/-- Case 7 (|G| = 6): S_3 on {0, 1, 2} fixing 3. -/
private lemma fixedField_S3_012 {K : Type} [Field K]
    (H : Subgroup (FR4 K ≃ₐ[K] FR4 K)) [Fintype H]
    (hcard : Fintype.card H = 6)
    (hHsub : ∀ h ∈ H, ∃ σ : Perm (Fin 4), σ 3 = 3 ∧ h = permAut K σ) :
    IsRationalExtension K (IntermediateField.fixedField H) (Fin 4) := by
  classical
  set x0 : FR4 K := algebraMap (A4 K) (FR4 K) (X 0)
  set x1 : FR4 K := algebraMap (A4 K) (FR4 K) (X 1)
  set x2 : FR4 K := algebraMap (A4 K) (FR4 K) (X 2)
  set x3 : FR4 K := algebraMap (A4 K) (FR4 K) (X 3)
  let f : Fin 4 → FR4 K := ![x0 + x1 + x2, x0 * x1 + x1 * x2 + x2 * x0, x0 * x1 * x2, x3]
  have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
    intro i
    rw [IntermediateField.mem_fixedField_iff]
    intro h hh
    obtain ⟨σ, hσ3, rfl⟩ := hHsub h hh
    have hfix_s01 : ∀ j, permAut K (Equiv.swap 0 1) (f j) = f j := by
      intro j
      have h0 : permAut K (Equiv.swap 0 1) x0 = x1 := by have : (Equiv.swap (0 : Fin 4) 1) 0 = 1 := (by decide); simp only [x0, x1, permAut_X, this]
      have h1 : permAut K (Equiv.swap 0 1) x1 = x0 := by have : (Equiv.swap (0 : Fin 4) 1) 1 = 0 := (by decide); simp only [x0, x1, permAut_X, this]
      have h2 : permAut K (Equiv.swap 0 1) x2 = x2 := by have : (Equiv.swap (0 : Fin 4) 1) 2 = 2 := (by decide); simp only [x2, permAut_X, this]
      have h3 : permAut K (Equiv.swap 0 1) x3 = x3 := by have : (Equiv.swap (0 : Fin 4) 1) 3 = 3 := (by decide); simp only [x3, permAut_X, this]
      fin_cases j
      · change permAut K (Equiv.swap 0 1) (x0 + x1 + x2) = x0 + x1 + x2; rw [map_add, map_add, h0, h1, h2]; ring
      · change permAut K (Equiv.swap 0 1) (x0 * x1 + x1 * x2 + x2 * x0) = x0 * x1 + x1 * x2 + x2 * x0; simp only [map_add, map_mul, h0, h1, h2]; ring
      · change permAut K (Equiv.swap 0 1) (x0 * x1 * x2) = x0 * x1 * x2; simp only [map_mul, h0, h1, h2]; ring
      · change permAut K (Equiv.swap 0 1) x3 = x3; exact h3
    have hfix_s12 : ∀ j, permAut K (Equiv.swap 1 2) (f j) = f j := by
      intro j
      have h0 : permAut K (Equiv.swap 1 2) x0 = x0 := by have : (Equiv.swap (1 : Fin 4) 2) 0 = 0 := (by decide); simp only [x0, permAut_X, this]
      have h1 : permAut K (Equiv.swap 1 2) x1 = x2 := by have : (Equiv.swap (1 : Fin 4) 2) 1 = 2 := (by decide); simp only [x1, x2, permAut_X, this]
      have h2 : permAut K (Equiv.swap 1 2) x2 = x1 := by have : (Equiv.swap (1 : Fin 4) 2) 2 = 1 := (by decide); simp only [x1, x2, permAut_X, this]
      have h3 : permAut K (Equiv.swap 1 2) x3 = x3 := by have : (Equiv.swap (1 : Fin 4) 2) 3 = 3 := (by decide); simp only [x3, permAut_X, this]
      fin_cases j
      · change permAut K (Equiv.swap 1 2) (x0 + x1 + x2) = x0 + x1 + x2; rw [map_add, map_add, h0, h1, h2]; ring
      · change permAut K (Equiv.swap 1 2) (x0 * x1 + x1 * x2 + x2 * x0) = x0 * x1 + x1 * x2 + x2 * x0; simp only [map_add, map_mul, h0, h1, h2]; ring
      · change permAut K (Equiv.swap 1 2) (x0 * x1 * x2) = x0 * x1 * x2; simp only [map_mul, h0, h1, h2]; ring
      · change permAut K (Equiv.swap 1 2) x3 = x3; exact h3
    have hσ_cases : σ = 1 ∨ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 1 2 ∨
        σ = Equiv.swap 0 1 * Equiv.swap 1 2 ∨ σ = Equiv.swap 1 2 * Equiv.swap 0 1 ∨
        σ = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1 := by
      have hall : ∀ τ : Perm (Fin 4), τ 3 = 3 →
          τ = 1 ∨ τ = Equiv.swap 0 1 ∨ τ = Equiv.swap 1 2 ∨
          τ = Equiv.swap 0 1 * Equiv.swap 1 2 ∨ τ = Equiv.swap 1 2 * Equiv.swap 0 1 ∨
          τ = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1 := by decide
      exact hall σ hσ3
    rcases hσ_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [permAut_one]
    · exact hfix_s01 i
    · exact hfix_s12 i
    · rw [permAut_mul, AlgEquiv.mul_apply, hfix_s12 i, hfix_s01 i]
    · rw [permAut_mul, AlgEquiv.mul_apply, hfix_s01 i, hfix_s12 i]
    · rw [permAut_mul, permAut_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hfix_s01 i, hfix_s12 i, hfix_s01 i]
  set E := IntermediateField.adjoin K (Set.range f)
  let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
  let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
  let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
  let g3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
  let P1 : Polynomial E :=
    Polynomial.X ^ 3 + Polynomial.C (-g0) * Polynomial.X ^ 2 + Polynomial.C g1 * Polynomial.X + Polynomial.C (-g2)
  have hP1 : Polynomial.aeval x0 P1 = 0 := by
    rw [show P1 = _ from rfl, aeval_cubic_apply]
    change x0 ^ 3 + -(x0 + x1 + x2) * x0 ^ 2 + (x0 * x1 + x1 * x2 + x2 * x0) * x0 + -(x0 * x1 * x2) = 0; ring
  set M1 : IntermediateField K (FR4 K) := (IntermediateField.adjoin E ({x0} : Set (FR4 K))).restrictScalars K
  let x0M1 : M1 := ⟨x0, IntermediateField.subset_adjoin E _ rfl⟩
  let g0' : M1 := ⟨f 0, (IntermediateField.adjoin E ({x0} : Set (FR4 K))).algebraMap_mem g0⟩
  let g1' : M1 := ⟨f 1, (IntermediateField.adjoin E ({x0} : Set (FR4 K))).algebraMap_mem g1⟩
  let P2 : Polynomial M1 :=
    Polynomial.X ^ 2 + Polynomial.C (x0M1 - g0') * Polynomial.X + Polynomial.C (g1' - x0M1 * (g0' - x0M1))
  have hP2 : Polynomial.aeval x1 P2 = 0 := by
    rw [show P2 = _ from rfl, aeval_quad_apply]
    change x1 ^ 2 + (x0 - (x0 + x1 + x2)) * x1 + ((x0 * x1 + x1 * x2 + x2 * x0) - x0 * ((x0 + x1 + x2) - x0)) = 0
    ring
  have hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
      IntermediateField.adjoin M1 ({x1} : Set (FR4 K)) := by
    intro i
    set M2 := IntermediateField.adjoin M1 ({x1} : Set (FR4 K))
    have hx0 : x0 ∈ M2 := M2.algebraMap_mem x0M1
    have hx1 : x1 ∈ M2 := IntermediateField.subset_adjoin M1 _ rfl
    have hg0M : x0 + x1 + x2 ∈ M2 := M2.algebraMap_mem g0'
    fin_cases i
    · exact hx0
    · exact hx1
    · change x2 ∈ M2; rw [show x2 = (x0 + x1 + x2) - x0 - x1 from by ring]; exact sub_mem (sub_mem hg0M hx0) hx1
    · exact M2.algebraMap_mem ⟨f 3, (IntermediateField.adjoin E ({x0} : Set (FR4 K))).algebraMap_mem g3⟩
  obtain ⟨hfd, hle⟩ := finrank_le_of_two_gen E x0 x1 P1 (cubic_ne_zero _ _ _) (natDegree_cubic_le _ _ _) hP1
    P2 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP2 hgen
  exact fixedField_isRational_of_finrank_le H f hf (by rw [hcard]; exact hle)

set_option maxHeartbeats 800000 in
/-- Case 8 (|G| = 8): D_4 = ⟨(0 2), (1 3), (0 1)(2 3)⟩ (stabilizer of {{0,2},{1,3}}). -/
private lemma fixedField_D4 {K : Type} [Field K]
    (H : Subgroup (FR4 K ≃ₐ[K] FR4 K)) [Fintype H]
    (hcard : Fintype.card H = 8)
    (hHsub : ∀ h ∈ H, ∃ σ : Perm (Fin 4),
      ((σ 0 = 0 ∨ σ 0 = 2) ∧ (σ 2 = 0 ∨ σ 2 = 2) ∨ (σ 0 = 1 ∨ σ 0 = 3) ∧ (σ 2 = 1 ∨ σ 2 = 3)) ∧
      h = permAut K σ) :
    IsRationalExtension K (IntermediateField.fixedField H) (Fin 4) := by
  classical
  set x0 : FR4 K := algebraMap (A4 K) (FR4 K) (X 0)
  set x1 : FR4 K := algebraMap (A4 K) (FR4 K) (X 1)
  set x2 : FR4 K := algebraMap (A4 K) (FR4 K) (X 2)
  set x3 : FR4 K := algebraMap (A4 K) (FR4 K) (X 3)
  set u : FR4 K := x0 + x2
  set v : FR4 K := x1 + x3
  set p : FR4 K := x0 * x2
  set q : FR4 K := x1 * x3
  set gA : Perm (Fin 4) := Equiv.swap 0 2
  set gB : Perm (Fin 4) := Equiv.swap 1 3
  set gC : Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
  have hA : permAut K gA u = u ∧ permAut K gA v = v ∧ permAut K gA p = p ∧ permAut K gA q = q := by
    have h0 : gA 0 = 2 := (by decide); have h1 : gA 1 = 1 := (by decide)
    have h2 : gA 2 = 0 := (by decide); have h3 : gA 3 = 3 := (by decide)
    simp only [u, v, p, q, x0, x1, x2, x3, map_add, map_mul, permAut_X, h0, h1, h2, h3]
    exact ⟨by ring, trivial, by ring, trivial⟩
  have hB : permAut K gB u = u ∧ permAut K gB v = v ∧ permAut K gB p = p ∧ permAut K gB q = q := by
    have h0 : gB 0 = 0 := (by decide); have h1 : gB 1 = 3 := (by decide)
    have h2 : gB 2 = 2 := (by decide); have h3 : gB 3 = 1 := (by decide)
    simp only [u, v, p, q, x0, x1, x2, x3, map_add, map_mul, permAut_X, h0, h1, h2, h3]
    exact ⟨trivial, by ring, trivial, by ring⟩
  have hC : permAut K gC u = v ∧ permAut K gC v = u ∧ permAut K gC p = q ∧ permAut K gC q = p := by
    have h0 : gC 0 = 1 := (by decide); have h1 : gC 1 = 0 := (by decide)
    have h2 : gC 2 = 3 := (by decide); have h3 : gC 3 = 2 := (by decide)
    simp only [u, v, p, q, x0, x1, x2, x3, map_add, map_mul, permAut_X, h0, h1, h2, h3]
    exact ⟨trivial, trivial, trivial, trivial⟩
  have hD4_gen : ∀ σ : Perm (Fin 4),
      ((σ 0 = 0 ∨ σ 0 = 2) ∧ (σ 2 = 0 ∨ σ 2 = 2) ∨ (σ 0 = 1 ∨ σ 0 = 3) ∧ (σ 2 = 1 ∨ σ 2 = 3)) →
      (permAut K σ u = u ∧ permAut K σ v = v ∧ permAut K σ p = p ∧ permAut K σ q = q) ∨
      (permAut K σ u = v ∧ permAut K σ v = u ∧ permAut K σ p = q ∧ permAut K σ q = p) := by
    intro σ hσ
    have hcases : σ = 1 ∨ σ = gA ∨ σ = gB ∨ σ = gA * gB ∨
        σ = gC ∨ σ = gA * gC ∨ σ = gB * gC ∨ σ = gA * gB * gC := by
      have hall : ∀ τ : Perm (Fin 4),
          ((τ 0 = 0 ∨ τ 0 = 2) ∧ (τ 2 = 0 ∨ τ 2 = 2) ∨ (τ 0 = 1 ∨ τ 0 = 3) ∧ (τ 2 = 1 ∨ τ 2 = 3)) →
          τ = 1 ∨ τ = gA ∨ τ = gB ∨ τ = gA * gB ∨
          τ = gC ∨ τ = gA * gC ∨ τ = gB * gC ∨ τ = gA * gB * gC := by decide
      exact hall σ hσ
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left; simp [permAut_one]
    · left; exact hA
    · left; exact hB
    · left; simp only [permAut_mul, AlgEquiv.mul_apply, hB.1, hB.2.1, hB.2.2.1, hB.2.2.2, hA.1, hA.2.1, hA.2.2.1, hA.2.2.2]; exact ⟨trivial, trivial, trivial, trivial⟩
    · right; exact hC
    · right; simp only [permAut_mul, AlgEquiv.mul_apply, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2, hA.1, hA.2.1, hA.2.2.1, hA.2.2.2]; exact ⟨trivial, trivial, trivial, trivial⟩
    · right; simp only [permAut_mul, AlgEquiv.mul_apply, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2, hB.1, hB.2.1, hB.2.2.1, hB.2.2.2]; exact ⟨trivial, trivial, trivial, trivial⟩
    · right; simp only [permAut_mul, AlgEquiv.mul_apply, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2, hB.1, hB.2.1, hB.2.2.1, hB.2.2.2, hA.1, hA.2.1, hA.2.2.1, hA.2.2.2]; exact ⟨trivial, trivial, trivial, trivial⟩
  by_cases hchar2 : (2 : FR4 K) = 0
  · -- Characteristic 2: f = ![u+v, u*v, p+q, u/(u+v)*(p+q) + p]
    have huv_ne : u + v ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 0 + X 2 + (X 1 + X 3)) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [u, v, x0, x1, x2, x3, map_add] using h
    let f : Fin 4 → FR4 K := ![u + v, u * v, p + q, u / (u + v) * (p + q) + p]
    have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
      intro i
      rw [IntermediateField.mem_fixedField_iff]
      intro h hh
      obtain ⟨σ, hσ, rfl⟩ := hHsub h hh
      rcases hD4_gen σ hσ with ⟨hu, hv, hp, hq⟩ | ⟨hu, hv, hp, hq⟩ <;> fin_cases i
      · change permAut K σ (u + v) = u + v; rw [map_add, hu, hv]
      · change permAut K σ (u * v) = u * v; rw [map_mul, hu, hv]
      · change permAut K σ (p + q) = p + q; rw [map_add, hp, hq]
      · change permAut K σ (u / (u + v) * (p + q) + p) = u / (u + v) * (p + q) + p
        simp only [map_add, map_mul, map_div₀, hu, hv, hp, hq]
      · change permAut K σ (u + v) = u + v; rw [map_add, hu, hv]; ring
      · change permAut K σ (u * v) = u * v; rw [map_mul, hu, hv]; ring
      · change permAut K σ (p + q) = p + q; rw [map_add, hp, hq]; ring
      · change permAut K σ (u / (u + v) * (p + q) + p) = u / (u + v) * (p + q) + p
        simp only [map_add, map_mul, map_div₀, hu, hv, hp, hq]
        rw [show v + u = u + v from add_comm v u]
        field_simp [huv_ne]
        linear_combination (v * q - u * p) * hchar2
    set E := IntermediateField.adjoin K (Set.range f)
    let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
    let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
    let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
    let g3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
    let P1 : Polynomial E := Polynomial.X ^ 2 + Polynomial.C (-g0) * Polynomial.X + Polynomial.C g1
    have hP1 : Polynomial.aeval u P1 = 0 := by
      rw [show P1 = _ from rfl, aeval_quad_apply]; change u ^ 2 + -(u + v) * u + u * v = 0; ring
    set M1 : IntermediateField K (FR4 K) := (IntermediateField.adjoin E ({u} : Set (FR4 K))).restrictScalars K
    have huM1 : u ∈ M1 := IntermediateField.subset_adjoin E _ rfl
    have hg0M1 : u + v ∈ M1 := (IntermediateField.adjoin E ({u} : Set (FR4 K))).algebraMap_mem g0
    have hg2M1 : p + q ∈ M1 := (IntermediateField.adjoin E ({u} : Set (FR4 K))).algebraMap_mem g2
    have hg3M1 : u / (u + v) * (p + q) + p ∈ M1 := (IntermediateField.adjoin E ({u} : Set (FR4 K))).algebraMap_mem g3
    have hvM1 : v ∈ M1 := by rw [show v = (u + v) - u from by ring]; exact sub_mem hg0M1 huM1
    have hpM1 : p ∈ M1 := by
      rw [show p = (u / (u + v) * (p + q) + p) - u / (u + v) * (p + q) from by ring]
      exact sub_mem hg3M1 (mul_mem (div_mem huM1 hg0M1) hg2M1)
    have hqM1 : q ∈ M1 := by rw [show q = (p + q) - p from by ring]; exact sub_mem hg2M1 hpM1
    let P2 : Polynomial M1 := Polynomial.X ^ 2 + Polynomial.C (-⟨u, huM1⟩) * Polynomial.X + Polynomial.C ⟨p, hpM1⟩
    have hP2 : Polynomial.aeval x0 P2 = 0 := by
      rw [show P2 = _ from rfl, aeval_quad_apply]; change x0 ^ 2 + -(x0 + x2) * x0 + x0 * x2 = 0; ring
    set M2 : IntermediateField K (FR4 K) := (IntermediateField.adjoin M1 ({x0} : Set (FR4 K))).restrictScalars K
    have hvM2 : v ∈ M2 := (IntermediateField.adjoin M1 ({x0} : Set (FR4 K))).algebraMap_mem ⟨v, hvM1⟩
    have hqM2 : q ∈ M2 := (IntermediateField.adjoin M1 ({x0} : Set (FR4 K))).algebraMap_mem ⟨q, hqM1⟩
    let P3 : Polynomial M2 := Polynomial.X ^ 2 + Polynomial.C (-⟨v, hvM2⟩) * Polynomial.X + Polynomial.C ⟨q, hqM2⟩
    have hP3 : Polynomial.aeval x1 P3 = 0 := by
      rw [show P3 = _ from rfl, aeval_quad_apply]; change x1 ^ 2 + -(x1 + x3) * x1 + x1 * x3 = 0; ring
    have hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
        IntermediateField.adjoin M2 ({x1} : Set (FR4 K)) := by
      intro i
      set M3 := IntermediateField.adjoin M2 ({x1} : Set (FR4 K))
      have hx0 : x0 ∈ M3 := M3.algebraMap_mem ⟨x0, IntermediateField.subset_adjoin M1 _ rfl⟩
      have hx1 : x1 ∈ M3 := IntermediateField.subset_adjoin M2 _ rfl
      have huM3 : u ∈ M3 := M3.algebraMap_mem ⟨u, (IntermediateField.adjoin M1 ({x0} : Set (FR4 K))).algebraMap_mem ⟨u, huM1⟩⟩
      have hvM3 : v ∈ M3 := M3.algebraMap_mem ⟨v, hvM2⟩
      fin_cases i
      · exact hx0
      · exact hx1
      · change x2 ∈ M3; rw [show x2 = u - x0 from by simp only [u]; ring]; exact sub_mem huM3 hx0
      · change x3 ∈ M3; rw [show x3 = v - x1 from by simp only [v]; ring]; exact sub_mem hvM3 hx1
    obtain ⟨hfd, hle⟩ := finrank_le_of_three_gen E u x0 x1 P1 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP1
      P2 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP2 P3 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP3 hgen
    exact fixedField_isRational_of_finrank_le H f hf (by rw [hcard]; exact hle)
  · -- Characteristic ≠ 2: f = ![u+v, (u-v)^2, p+q, (p-q)/(u-v)]
    have huv_ne : u - v ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 0 + X 2 - (X 1 + X 3)) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [u, v, x0, x1, x2, x3, map_add, map_sub] using h
    let f : Fin 4 → FR4 K := ![u + v, (u - v) ^ 2, p + q, (p - q) / (u - v)]
    have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
      intro i
      rw [IntermediateField.mem_fixedField_iff]
      intro h hh
      obtain ⟨σ, hσ, rfl⟩ := hHsub h hh
      rcases hD4_gen σ hσ with ⟨hu, hv, hp, hq⟩ | ⟨hu, hv, hp, hq⟩ <;> fin_cases i
      · change permAut K σ (u + v) = u + v; rw [map_add, hu, hv]
      · change permAut K σ ((u - v) ^ 2) = (u - v) ^ 2; rw [map_pow, map_sub, hu, hv]
      · change permAut K σ (p + q) = p + q; rw [map_add, hp, hq]
      · change permAut K σ ((p - q) / (u - v)) = (p - q) / (u - v); rw [map_div₀, map_sub, map_sub, hu, hv, hp, hq]
      · change permAut K σ (u + v) = u + v; rw [map_add, hu, hv]; ring
      · change permAut K σ ((u - v) ^ 2) = (u - v) ^ 2; rw [map_pow, map_sub, hu, hv]; ring
      · change permAut K σ (p + q) = p + q; rw [map_add, hp, hq]; ring
      · change permAut K σ ((p - q) / (u - v)) = (p - q) / (u - v)
        rw [map_div₀, map_sub, map_sub, hu, hv, hp, hq]
        have hvu : v - u ≠ 0 := by intro h; apply huv_ne; linear_combination -h
        field_simp [huv_ne, hvu]; ring
    set E := IntermediateField.adjoin K (Set.range f)
    let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
    let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
    let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
    let g3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
    let P1 : Polynomial E := Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X + Polynomial.C (-g1)
    have hP1 : Polynomial.aeval (u - v) P1 = 0 := by
      rw [show P1 = _ from rfl, aeval_quad_apply]; change (u - v) ^ 2 + 0 * (u - v) + -((u - v) ^ 2) = 0; ring
    set M1 : IntermediateField K (FR4 K) := (IntermediateField.adjoin E ({u - v} : Set (FR4 K))).restrictScalars K
    have huvM1 : u - v ∈ M1 := IntermediateField.subset_adjoin E _ rfl
    have hg0M1 : u + v ∈ M1 := (IntermediateField.adjoin E ({u - v} : Set (FR4 K))).algebraMap_mem g0
    have hg2M1 : p + q ∈ M1 := (IntermediateField.adjoin E ({u - v} : Set (FR4 K))).algebraMap_mem g2
    have hg3M1 : (p - q) / (u - v) ∈ M1 := (IntermediateField.adjoin E ({u - v} : Set (FR4 K))).algebraMap_mem g3
    have hpqM1 : p - q ∈ M1 := by
      rw [show p - q = ((p - q) / (u - v)) * (u - v) from (div_mul_cancel₀ _ huv_ne).symm]
      exact mul_mem hg3M1 huvM1
    have h2M1 : (2 : FR4 K) ∈ M1 := (IntermediateField.adjoin E ({u - v} : Set (FR4 K))).algebraMap_mem (2 : E)
    have huM1 : u ∈ M1 := by
      rw [show u = ((u + v) + (u - v)) / 2 from by rw [eq_div_iff hchar2]; ring]
      exact div_mem (add_mem hg0M1 huvM1) h2M1
    have hvM1 : v ∈ M1 := by
      rw [show v = ((u + v) - (u - v)) / 2 from by rw [eq_div_iff hchar2]; ring]
      exact div_mem (sub_mem hg0M1 huvM1) h2M1
    have hpM1 : p ∈ M1 := by
      rw [show p = ((p + q) + (p - q)) / 2 from by rw [eq_div_iff hchar2]; ring]
      exact div_mem (add_mem hg2M1 hpqM1) h2M1
    have hqM1 : q ∈ M1 := by
      rw [show q = ((p + q) - (p - q)) / 2 from by rw [eq_div_iff hchar2]; ring]
      exact div_mem (sub_mem hg2M1 hpqM1) h2M1
    let P2 : Polynomial M1 := Polynomial.X ^ 2 + Polynomial.C (-⟨u, huM1⟩) * Polynomial.X + Polynomial.C ⟨p, hpM1⟩
    have hP2 : Polynomial.aeval x0 P2 = 0 := by
      rw [show P2 = _ from rfl, aeval_quad_apply]; change x0 ^ 2 + -(x0 + x2) * x0 + x0 * x2 = 0; ring
    set M2 : IntermediateField K (FR4 K) := (IntermediateField.adjoin M1 ({x0} : Set (FR4 K))).restrictScalars K
    have hvM2 : v ∈ M2 := (IntermediateField.adjoin M1 ({x0} : Set (FR4 K))).algebraMap_mem ⟨v, hvM1⟩
    have hqM2 : q ∈ M2 := (IntermediateField.adjoin M1 ({x0} : Set (FR4 K))).algebraMap_mem ⟨q, hqM1⟩
    let P3 : Polynomial M2 := Polynomial.X ^ 2 + Polynomial.C (-⟨v, hvM2⟩) * Polynomial.X + Polynomial.C ⟨q, hqM2⟩
    have hP3 : Polynomial.aeval x1 P3 = 0 := by
      rw [show P3 = _ from rfl, aeval_quad_apply]; change x1 ^ 2 + -(x1 + x3) * x1 + x1 * x3 = 0; ring
    have hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
        IntermediateField.adjoin M2 ({x1} : Set (FR4 K)) := by
      intro i
      set M3 := IntermediateField.adjoin M2 ({x1} : Set (FR4 K))
      have hx0 : x0 ∈ M3 := M3.algebraMap_mem ⟨x0, IntermediateField.subset_adjoin M1 _ rfl⟩
      have hx1 : x1 ∈ M3 := IntermediateField.subset_adjoin M2 _ rfl
      have huM3 : u ∈ M3 := M3.algebraMap_mem ⟨u, (IntermediateField.adjoin M1 ({x0} : Set (FR4 K))).algebraMap_mem ⟨u, huM1⟩⟩
      have hvM3 : v ∈ M3 := M3.algebraMap_mem ⟨v, hvM2⟩
      fin_cases i
      · exact hx0
      · exact hx1
      · change x2 ∈ M3; rw [show x2 = u - x0 from by simp only [u]; ring]; exact sub_mem huM3 hx0
      · change x3 ∈ M3; rw [show x3 = v - x1 from by simp only [v]; ring]; exact sub_mem hvM3 hx1
    obtain ⟨hfd, hle⟩ := finrank_le_of_three_gen E (u - v) x0 x1 P1 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP1
      P2 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP2 P3 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP3 hgen
    exact fixedField_isRational_of_finrank_le H f hf (by rw [hcard]; exact hle)

set_option maxHeartbeats 2400000 in
/-- Case 9 (|G| = 12): A_4 = V_4 ⋊ ⟨(1 2 3)⟩. -/
private lemma fixedField_A4 {K : Type} [Field K]
    (H : Subgroup (FR4 K ≃ₐ[K] FR4 K)) [Fintype H]
    (hcard : Fintype.card H = 12)
    (hHsub : ∀ h ∈ H, ∃ σ : Perm (Fin 4), Equiv.Perm.sign σ = 1 ∧ h = permAut K σ) :
    IsRationalExtension K (IntermediateField.fixedField H) (Fin 4) := by
  classical
  set σ1 : Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
  set σ2 : Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
  set τ : Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3
  set x0 : FR4 K := algebraMap (A4 K) (FR4 K) (X 0)
  set x1 : FR4 K := algebraMap (A4 K) (FR4 K) (X 1)
  set x2 : FR4 K := algebraMap (A4 K) (FR4 K) (X 2)
  set x3 : FR4 K := algebraMap (A4 K) (FR4 K) (X 3)
  have h10 : permAut K σ1 x0 = x1 := by have : σ1 0 = 1 := (by decide); simp only [x0, x1, permAut_X, this]
  have h11 : permAut K σ1 x1 = x0 := by have : σ1 1 = 0 := (by decide); simp only [x0, x1, permAut_X, this]
  have h12 : permAut K σ1 x2 = x3 := by have : σ1 2 = 3 := (by decide); simp only [x2, x3, permAut_X, this]
  have h13 : permAut K σ1 x3 = x2 := by have : σ1 3 = 2 := (by decide); simp only [x2, x3, permAut_X, this]
  have h20 : permAut K σ2 x0 = x2 := by have : σ2 0 = 2 := (by decide); simp only [x0, x2, permAut_X, this]
  have h21 : permAut K σ2 x1 = x3 := by have : σ2 1 = 3 := (by decide); simp only [x1, x3, permAut_X, this]
  have h22 : permAut K σ2 x2 = x0 := by have : σ2 2 = 0 := (by decide); simp only [x0, x2, permAut_X, this]
  have h23 : permAut K σ2 x3 = x1 := by have : σ2 3 = 1 := (by decide); simp only [x1, x3, permAut_X, this]
  have ht0 : permAut K τ x0 = x0 := by have : τ 0 = 0 := (by decide); simp only [x0, permAut_X, this]
  have ht1 : permAut K τ x1 = x2 := by have : τ 1 = 2 := (by decide); simp only [x1, x2, permAut_X, this]
  have ht2 : permAut K τ x2 = x3 := by have : τ 2 = 3 := (by decide); simp only [x2, x3, permAut_X, this]
  have ht3 : permAut K τ x3 = x1 := by have : τ 3 = 1 := (by decide); simp only [x3, x1, permAut_X, this]
  -- Every even permutation in Perm (Fin 4) is a product of σ1, σ2, τ
  have hfix : ∀ y : FR4 K, permAut K σ1 y = y → permAut K σ2 y = y → permAut K τ y = y →
      y ∈ IntermediateField.fixedField H := by
    intro y hy1 hy2 hyt
    rw [IntermediateField.mem_fixedField_iff]
    intro h hh
    obtain ⟨σ, hsign, rfl⟩ := hHsub h hh
    have hgen_A4 : ∀ g : Perm (Fin 4), Equiv.Perm.sign g = 1 →
        g = 1 ∨ g = σ1 ∨ g = σ2 ∨ g = σ1 * σ2 ∨
        g = τ ∨ g = σ1 * τ ∨ g = σ2 * τ ∨ g = σ1 * σ2 * τ ∨
        g = τ * τ ∨ g = σ1 * (τ * τ) ∨ g = σ2 * (τ * τ) ∨ g = σ1 * σ2 * (τ * τ) := by decide
    have hyt2 : permAut K (τ * τ) y = y := by rw [permAut_mul, AlgEquiv.mul_apply, hyt, hyt]
    rcases hgen_A4 σ hsign with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [permAut_one]
    · exact hy1
    · exact hy2
    · rw [permAut_mul, AlgEquiv.mul_apply, hy2, hy1]
    · exact hyt
    · rw [permAut_mul, AlgEquiv.mul_apply, hyt, hy1]
    · rw [permAut_mul, AlgEquiv.mul_apply, hyt, hy2]
    · rw [permAut_mul, permAut_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hyt, hy2, hy1]
    · exact hyt2
    · rw [permAut_mul, AlgEquiv.mul_apply, hyt2, hy1]
    · rw [permAut_mul, AlgEquiv.mul_apply, hyt2, hy2]
    · rw [permAut_mul, AlgEquiv.mul_apply, hyt2, permAut_mul, AlgEquiv.mul_apply, hy2, hy1]
  by_cases hchar2 : (2 : FR4 K) = 0
  · -- Characteristic 2: u1 = y1^2+y1, u2 = y2^2+y2, Z = u1/u2, τ(Z) = 1/(Z+1)
    set s : FR4 K := x0 + x1 + x2 + x3
    have hs_ne : s ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 0 + X 1 + X 2 + X 3) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [s, x0, x1, x2, x3, map_add] using h
    have h1s : permAut K σ1 s = s := by simp only [s, map_add, h10, h11, h12, h13]; ring
    have h2s : permAut K σ2 s = s := by simp only [s, map_add, h20, h21, h22, h23]; ring
    have hts : permAut K τ s = s := by simp only [s, map_add, ht0, ht1, ht2, ht3]; ring
    set y1 : FR4 K := (x0 + x1) / s
    set y2 : FR4 K := (x0 + x2) / s
    set y3 : FR4 K := (x0 + x3) / s
    have hy_sum : y1 + y2 + y3 = 1 := by
      simp only [y1, y2, y3]; field_simp [hs_ne]; simp only [s]; linear_combination x0 * hchar2
    have h1y1 : permAut K σ1 y1 = y1 := by simp only [y1, map_div₀, map_add, h10, h11, h1s]; ring
    have h1y2 : permAut K σ1 y2 = y2 + 1 := by
      simp only [y2, map_div₀, map_add, h10, h12, h1s]; field_simp [hs_ne]; simp only [s]; linear_combination (-x0 - x2) * hchar2
    have h1y3 : permAut K σ1 y3 = y3 + 1 := by
      simp only [y3, map_div₀, map_add, h10, h13, h1s]; field_simp [hs_ne]; simp only [s]; linear_combination (-x0 - x3) * hchar2
    have h2y1 : permAut K σ2 y1 = y1 + 1 := by
      simp only [y1, map_div₀, map_add, h20, h21, h2s]; field_simp [hs_ne]; simp only [s]; linear_combination (-x0 - x1) * hchar2
    have h2y2 : permAut K σ2 y2 = y2 := by simp only [y2, map_div₀, map_add, h20, h22, h2s]; ring
    have h2y3 : permAut K σ2 y3 = y3 + 1 := by
      simp only [y3, map_div₀, map_add, h20, h23, h2s]; field_simp [hs_ne]; simp only [s]; linear_combination (-x0 - x3) * hchar2
    have hty1 : permAut K τ y1 = y2 := by simp only [y1, y2, map_div₀, map_add, ht0, ht1, hts]
    have hty2 : permAut K τ y2 = y3 := by simp only [y2, y3, map_div₀, map_add, ht0, ht2, hts]
    have hty3 : permAut K τ y3 = y1 := by simp only [y3, y1, map_div₀, map_add, ht0, ht3, hts]
    set w : FR4 K := x0 / s + y1 * y2 + y2 * y3 + y3 * y1
    set u1 : FR4 K := y1 ^ 2 + y1
    set u2 : FR4 K := y2 ^ 2 + y2
    set u3 : FR4 K := y3 ^ 2 + y3
    have hu1_eq : u1 = (x0 + x1) * (x2 + x3) / s ^ 2 := by
      simp only [u1, y1]; field_simp [hs_ne]; simp only [s]; linear_combination (x0 + x1) ^ 2 * hchar2
    have hu2_eq : u2 = (x0 + x2) * (x1 + x3) / s ^ 2 := by
      simp only [u2, y2]; field_simp [hs_ne]; simp only [s]; linear_combination (x0 + x2) ^ 2 * hchar2
    have hu3_eq : u3 = (x0 + x3) * (x1 + x2) / s ^ 2 := by
      simp only [u3, y3]; field_simp [hs_ne]; simp only [s]; linear_combination (x0 + x3) ^ 2 * hchar2
    have hu_sum : u3 = u1 + u2 := by
      have : y3 = 1 - y1 - y2 := by linear_combination hy_sum
      simp only [u1, u2, u3, this]
      linear_combination (y1 * y2 - 2 * y1 - 2 * y2 + 1) * hchar2
    have hu1_ne : u1 ≠ 0 := by
      rw [hu1_eq]; apply div_ne_zero _ (pow_ne_zero 2 hs_ne)
      have h := algebraMap_ne_zero_of_eval ((X 0 + X 1) * (X 2 + X 3)) ![(1 : K), 0, 1, 0] (by simp [eval_X])
      simpa [x0, x1, x2, x3, map_mul, map_add] using h
    have hu2_ne : u2 ≠ 0 := by
      rw [hu2_eq]; apply div_ne_zero _ (pow_ne_zero 2 hs_ne)
      have h := algebraMap_ne_zero_of_eval ((X 0 + X 2) * (X 1 + X 3)) ![(1 : K), 1, 0, 0] (by simp [eval_X])
      simpa [x0, x1, x2, x3, map_mul, map_add] using h
    have hu3_ne : u3 ≠ 0 := by
      rw [hu3_eq]; apply div_ne_zero _ (pow_ne_zero 2 hs_ne)
      have h := algebraMap_ne_zero_of_eval ((X 0 + X 3) * (X 1 + X 2)) ![(1 : K), 1, 0, 0] (by simp [eval_X])
      simpa [x0, x1, x2, x3, map_mul, map_add] using h
    set Z : FR4 K := u1 / u2
    have hZ_ne : Z ≠ 0 := div_ne_zero hu1_ne hu2_ne
    have hZ1_ne : Z + 1 ≠ 0 := by
      have : Z + 1 = u3 / u2 := by simp only [Z, hu_sum]; field_simp [hu2_ne]
      rw [this]; exact div_ne_zero hu3_ne hu2_ne
    have hZ2_ne : Z ^ 2 + Z + 1 ≠ 0 := by
      intro h
      have h1 : u1 ^ 2 + u1 * u2 + u2 ^ 2 = 0 := by
        have h2 : (u1 / u2) ^ 2 + u1 / u2 + 1 = 0 := h
        field_simp [hu2_ne] at h2; linear_combination h2
      rw [hu1_eq, hu2_eq] at h1
      have h3 : ((x0 + x1) * (x2 + x3)) ^ 2 + ((x0 + x1) * (x2 + x3)) * ((x0 + x2) * (x1 + x3)) +
          ((x0 + x2) * (x1 + x3)) ^ 2 = 0 := by
        field_simp [hs_ne] at h1; linear_combination h1
      have h4 := algebraMap_ne_zero_of_eval
        (((X 0 + X 1) * (X 2 + X 3)) ^ 2 + ((X 0 + X 1) * (X 2 + X 3)) * ((X 0 + X 2) * (X 1 + X 3)) +
          ((X 0 + X 2) * (X 1 + X 3)) ^ 2) ![(1 : K), 0, 1, 0] (by simp [eval_X])
      exact h4 (by simpa [x0, x1, x2, x3, map_add, map_mul, map_pow] using h3)
    have h1u1 : permAut K σ1 u1 = u1 := by simp only [u1, map_add, map_pow, h1y1]
    have h1u2 : permAut K σ1 u2 = u2 := by simp only [u2, map_add, map_pow, h1y2]; linear_combination (y2 + 1) * hchar2
    have h2u1 : permAut K σ2 u1 = u1 := by simp only [u1, map_add, map_pow, h2y1]; linear_combination (y1 + 1) * hchar2
    have h2u2 : permAut K σ2 u2 = u2 := by simp only [u2, map_add, map_pow, h2y2]
    have htu1 : permAut K τ u1 = u2 := by simp only [u1, u2, map_add, map_pow, hty1]
    have htu2 : permAut K τ u2 = u1 + u2 := by rw [← hu_sum]; simp only [u2, u3, map_add, map_pow, hty2]
    have htZ : permAut K τ Z = 1 / (Z + 1) := by
      simp only [Z, map_div₀, htu1, htu2]; field_simp [hu2_ne, hZ1_ne]
    have h1Z : permAut K σ1 Z = Z := by simp only [Z, map_div₀, h1u1, h1u2]
    have h2Z : permAut K σ2 Z = Z := by simp only [Z, map_div₀, h2u1, h2u2]
    let f : Fin 4 → FR4 K :=
      ![s, w, (Z ^ 3 + Z + 1) / (Z * (Z + 1)), u2 * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))]
    have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
      intro i; apply hfix
      · fin_cases i
        · exact h1s
        · change permAut K σ1 (x0 / s + y1 * y2 + y2 * y3 + y3 * y1) = x0 / s + y1 * y2 + y2 * y3 + y3 * y1
          rw [map_add, map_add, map_add, map_div₀, map_mul, map_mul, map_mul, h10, h1s, h1y1, h1y2, h1y3]
          have hx01 : x1 / s - x0 / s = y1 := by simp only [y1]; field_simp [hs_ne]; linear_combination (-x0) * hchar2
          linear_combination hx01 + hy_sum + (y1 + 1) * hchar2
        · change permAut K σ1 ((Z ^ 3 + Z + 1) / (Z * (Z + 1))) = (Z ^ 3 + Z + 1) / (Z * (Z + 1))
          simp only [map_div₀, map_add, map_mul, map_pow, map_one, h1Z]
        · change permAut K σ1 (u2 * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))) = u2 * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))
          simp only [map_div₀, map_add, map_mul, map_pow, map_one, h1u2, h1Z]
      · fin_cases i
        · exact h2s
        · change permAut K σ2 (x0 / s + y1 * y2 + y2 * y3 + y3 * y1) = x0 / s + y1 * y2 + y2 * y3 + y3 * y1
          rw [map_add, map_add, map_add, map_div₀, map_mul, map_mul, map_mul, h20, h2s, h2y1, h2y2, h2y3]
          have hx02 : x2 / s - x0 / s = y2 := by simp only [y2]; field_simp [hs_ne]; linear_combination (-x0) * hchar2
          linear_combination hx02 + hy_sum + (y2 + 1) * hchar2
        · change permAut K σ2 ((Z ^ 3 + Z + 1) / (Z * (Z + 1))) = (Z ^ 3 + Z + 1) / (Z * (Z + 1))
          simp only [map_div₀, map_add, map_mul, map_pow, map_one, h2Z]
        · change permAut K σ2 (u2 * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))) = u2 * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))
          simp only [map_div₀, map_add, map_mul, map_pow, map_one, h2u2, h2Z]
      · fin_cases i
        · exact hts
        · change permAut K τ (x0 / s + y1 * y2 + y2 * y3 + y3 * y1) = x0 / s + y1 * y2 + y2 * y3 + y3 * y1
          rw [map_add, map_add, map_add, map_div₀, map_mul, map_mul, map_mul, ht0, hts, hty1, hty2, hty3]; ring
        · change permAut K τ ((Z ^ 3 + Z + 1) / (Z * (Z + 1))) = (Z ^ 3 + Z + 1) / (Z * (Z + 1))
          rw [map_div₀, map_add, map_add, map_pow, map_one, map_mul, map_add, map_one, htZ]
          have hZ1'_eq : 1 / (Z + 1) + 1 = Z / (Z + 1) := by
            have : 1 / (Z + 1) + 1 = (Z + 2) / (Z + 1) := by field_simp [hZ1_ne]; ring
            rw [this, hchar2, add_zero]
          have hnum : (1 / (Z + 1)) ^ 3 + 1 / (Z + 1) + 1 = (Z ^ 3 + Z + 1) / (Z + 1) ^ 3 := by
            field_simp [hZ1_ne]; linear_combination (2 * Z ^ 2 + 2 * Z + 1) * hchar2
          rw [hnum, hZ1'_eq]
          field_simp [hZ_ne, hZ1_ne]
        · change permAut K τ (u2 * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))) = u2 * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))
          rw [map_div₀, map_mul, htu2, map_pow, map_add, map_add, map_pow, map_one, map_mul, map_add, map_one, htZ]
          have hZ1'_eq : 1 / (Z + 1) + 1 = Z / (Z + 1) := by
            have : 1 / (Z + 1) + 1 = (Z + 2) / (Z + 1) := by field_simp [hZ1_ne]; ring
            rw [this, hchar2, add_zero]
          have hnum2 : (1 / (Z + 1)) ^ 2 + 1 / (Z + 1) + 1 = (Z ^ 2 + Z + 1) / (Z + 1) ^ 2 := by
            field_simp [hZ1_ne]; linear_combination (Z + 1) * hchar2
          have hu12 : u1 + u2 = (Z + 1) * u2 := by simp only [Z]; field_simp [hu2_ne]
          rw [hnum2, hZ1'_eq, hu12]
          field_simp [hZ_ne, hZ1_ne]
    set E := IntermediateField.adjoin K (Set.range f)
    let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
    let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
    let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
    let g3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
    let P1 : Polynomial E :=
      Polynomial.X ^ 3 + Polynomial.C (-g2) * Polynomial.X ^ 2 + Polynomial.C (1 - g2) * Polynomial.X + Polynomial.C 1
    have hP1 : Polynomial.aeval Z P1 = 0 := by
      rw [show P1 = _ from rfl, aeval_cubic_apply]
      change Z ^ 3 + -((Z ^ 3 + Z + 1) / (Z * (Z + 1))) * Z ^ 2 +
        (1 - (Z ^ 3 + Z + 1) / (Z * (Z + 1))) * Z + 1 = 0
      field_simp [hZ_ne, hZ1_ne]; ring
    set M1 : IntermediateField K (FR4 K) := (IntermediateField.adjoin E ({Z} : Set (FR4 K))).restrictScalars K
    have hZM1 : Z ∈ M1 := IntermediateField.subset_adjoin E _ rfl
    have hg3M1 : u2 * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1)) ∈ M1 :=
      (IntermediateField.adjoin E ({Z} : Set (FR4 K))).algebraMap_mem g3
    have hu2M1 : u2 ∈ M1 := by
      have hZ2' : Z * (Z + 1) + 1 ≠ 0 := by convert hZ2_ne using 1; ring
      have : u2 = (u2 * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))) * (Z * (Z + 1)) / (Z ^ 2 + Z + 1) ^ 2 := by
        field_simp [hZ_ne, hZ1_ne, hZ2_ne, hZ2']
      rw [this]
      exact div_mem (mul_mem hg3M1 (mul_mem hZM1 (add_mem hZM1 M1.one_mem)))
        (pow_mem (add_mem (add_mem (pow_mem hZM1 2) hZM1) M1.one_mem) 2)
    have hu1M1 : u1 ∈ M1 := by
      rw [show u1 = Z * u2 from (div_mul_cancel₀ u1 hu2_ne).symm]
      exact mul_mem hZM1 hu2M1
    let P2 : Polynomial M1 := Polynomial.X ^ 2 + Polynomial.C 1 * Polynomial.X + Polynomial.C (-⟨u1, hu1M1⟩)
    have hP2 : Polynomial.aeval y1 P2 = 0 := by
      rw [show P2 = _ from rfl, aeval_quad_apply]; change y1 ^ 2 + 1 * y1 + -(y1 ^ 2 + y1) = 0; ring
    set M2 : IntermediateField K (FR4 K) := (IntermediateField.adjoin M1 ({y1} : Set (FR4 K))).restrictScalars K
    have hu2M2 : u2 ∈ M2 := (IntermediateField.adjoin M1 ({y1} : Set (FR4 K))).algebraMap_mem ⟨u2, hu2M1⟩
    let P3 : Polynomial M2 := Polynomial.X ^ 2 + Polynomial.C 1 * Polynomial.X + Polynomial.C (-⟨u2, hu2M2⟩)
    have hP3 : Polynomial.aeval y2 P3 = 0 := by
      rw [show P3 = _ from rfl, aeval_quad_apply]; change y2 ^ 2 + 1 * y2 + -(y2 ^ 2 + y2) = 0; ring
    have hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
        IntermediateField.adjoin M2 ({y2} : Set (FR4 K)) := by
      intro i
      set M3 := IntermediateField.adjoin M2 ({y2} : Set (FR4 K))
      have hsM : s ∈ M3 := M3.algebraMap_mem ⟨s, (IntermediateField.adjoin M1 ({y1} : Set (FR4 K))).algebraMap_mem
        ⟨s, (IntermediateField.adjoin E ({Z} : Set (FR4 K))).algebraMap_mem g0⟩⟩
      have hwM : w ∈ M3 := M3.algebraMap_mem ⟨w, (IntermediateField.adjoin M1 ({y1} : Set (FR4 K))).algebraMap_mem
        ⟨w, (IntermediateField.adjoin E ({Z} : Set (FR4 K))).algebraMap_mem g1⟩⟩
      have hy1M : y1 ∈ M3 := M3.algebraMap_mem ⟨y1, IntermediateField.subset_adjoin M1 _ rfl⟩
      have hy2M : y2 ∈ M3 := IntermediateField.subset_adjoin M2 _ rfl
      have hy3M : y3 ∈ M3 := by
        rw [show y3 = 1 - y1 - y2 from by linear_combination hy_sum]
        exact sub_mem (sub_mem M3.one_mem hy1M) hy2M
      have hx0M : x0 ∈ M3 := by
        rw [show x0 = s * (w - y1 * y2 - y2 * y3 - y3 * y1) from by simp only [w]; field_simp [hs_ne]; ring]
        exact mul_mem hsM (sub_mem (sub_mem (sub_mem hwM (mul_mem hy1M hy2M)) (mul_mem hy2M hy3M)) (mul_mem hy3M hy1M))
      fin_cases i
      · exact hx0M
      · change x1 ∈ M3; rw [show x1 = s * y1 - x0 from by simp only [y1]; field_simp [hs_ne]; ring]
        exact sub_mem (mul_mem hsM hy1M) hx0M
      · change x2 ∈ M3; rw [show x2 = s * y2 - x0 from by simp only [y2]; field_simp [hs_ne]; ring]
        exact sub_mem (mul_mem hsM hy2M) hx0M
      · change x3 ∈ M3; rw [show x3 = s * y3 - x0 from by simp only [y3]; field_simp [hs_ne]; ring]
        exact sub_mem (mul_mem hsM hy3M) hx0M
    obtain ⟨hfd, hle⟩ := finrank_le_of_three_gen E Z y1 y2 P1 (cubic_ne_zero _ _ _) (natDegree_cubic_le _ _ _) hP1
      P2 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP2 P3 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP3 hgen
    exact fixedField_isRational_of_finrank_le H f hf (by rw [hcard]; exact hle)
  · -- Characteristic ≠ 2: z1 = y2*y3/y1, z2 = y3*y1/y2, z3 = y1*y2/y3
    set s : FR4 K := x0 + x1 + x2 + x3
    set y1 : FR4 K := x0 + x1 - x2 - x3
    set y2 : FR4 K := x0 - x1 + x2 - x3
    set y3 : FR4 K := x0 - x1 - x2 + x3
    have hy1_ne : y1 ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 0 + X 1 - X 2 - X 3) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [y1, x0, x1, x2, x3, map_add, map_sub] using h
    have hy2_ne : y2 ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 0 - X 1 + X 2 - X 3) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [y2, x0, x1, x2, x3, map_add, map_sub] using h
    have hy3_ne : y3 ≠ 0 := by
      have h := algebraMap_ne_zero_of_eval (X 0 - X 1 - X 2 + X 3) (Pi.single (0 : Fin 4) (1 : K)) (by simp [eval_X])
      simpa [y3, x0, x1, x2, x3, map_add, map_sub] using h
    have h4_ne : (4 : FR4 K) ≠ 0 := by
      rw [show (4 : FR4 K) = 2 * 2 from by norm_num]; exact mul_ne_zero hchar2 hchar2
    have h4K_ne : (4 : K) ≠ 0 := by
      intro h; apply h4_ne; simpa [map_ofNat] using congrArg (algebraMap K (FR4 K)) h
    have h1s : permAut K σ1 s = s := by simp only [s, map_add, h10, h11, h12, h13]; ring
    have h2s : permAut K σ2 s = s := by simp only [s, map_add, h20, h21, h22, h23]; ring
    have hts : permAut K τ s = s := by simp only [s, map_add, ht0, ht1, ht2, ht3]; ring
    have h1y1 : permAut K σ1 y1 = y1 := by simp only [y1, map_add, map_sub, h10, h11, h12, h13]; ring
    have h1y2 : permAut K σ1 y2 = -y2 := by simp only [y2, map_add, map_sub, h10, h11, h12, h13]; ring
    have h1y3 : permAut K σ1 y3 = -y3 := by simp only [y3, map_add, map_sub, h10, h11, h12, h13]; ring
    have h2y1 : permAut K σ2 y1 = -y1 := by simp only [y1, map_add, map_sub, h20, h21, h22, h23]; ring
    have h2y2 : permAut K σ2 y2 = y2 := by simp only [y2, map_add, map_sub, h20, h21, h22, h23]; ring
    have h2y3 : permAut K σ2 y3 = -y3 := by simp only [y3, map_add, map_sub, h20, h21, h22, h23]; ring
    have hty1 : permAut K τ y1 = y2 := by simp only [y1, y2, map_add, map_sub, ht0, ht1, ht2, ht3]; ring
    have hty2 : permAut K τ y2 = y3 := by simp only [y2, y3, map_add, map_sub, ht0, ht1, ht2, ht3]; ring
    have hty3 : permAut K τ y3 = y1 := by simp only [y3, y1, map_add, map_sub, ht0, ht1, ht2, ht3]; ring
    set z1 : FR4 K := y2 * y3 / y1
    set z2 : FR4 K := y3 * y1 / y2
    set z3 : FR4 K := y1 * y2 / y3
    have h1z1 : permAut K σ1 z1 = z1 := by simp only [z1, map_div₀, map_mul, h1y1, h1y2, h1y3]; ring
    have h1z2 : permAut K σ1 z2 = z2 := by simp only [z2, map_div₀, map_mul, h1y1, h1y2, h1y3]; field_simp [hy2_ne]
    have h1z3 : permAut K σ1 z3 = z3 := by simp only [z3, map_div₀, map_mul, h1y1, h1y2, h1y3]; field_simp [hy3_ne]
    have h2z1 : permAut K σ2 z1 = z1 := by simp only [z1, map_div₀, map_mul, h2y1, h2y2, h2y3]; field_simp [hy1_ne]
    have h2z2 : permAut K σ2 z2 = z2 := by simp only [z2, map_div₀, map_mul, h2y1, h2y2, h2y3]; ring
    have h2z3 : permAut K σ2 z3 = z3 := by simp only [z3, map_div₀, map_mul, h2y1, h2y2, h2y3]; field_simp [hy3_ne]
    have htz1 : permAut K τ z1 = z2 := by simp only [z1, z2, map_div₀, map_mul, hty1, hty2, hty3]
    have htz2 : permAut K τ z2 = z3 := by simp only [z2, z3, map_div₀, map_mul, hty1, hty2, hty3]
    have htz3 : permAut K τ z3 = z1 := by simp only [z3, z1, map_div₀, map_mul, hty1, hty2, hty3]
    -- Shared helper: given E and α such that z1, z2, z3, s ∈ M1 = E(α), finish with y1, y2 of degree 2
    have hfinish : ∀ (f : Fin 4 → FR4 K) (hf : ∀ i, f i ∈ IntermediateField.fixedField H)
        (α : FR4 K) (P1 : Polynomial (IntermediateField.adjoin K (Set.range f)))
        (hP10 : P1 ≠ 0) (hP1deg : P1.natDegree ≤ 3) (hP1α : Polynomial.aeval α P1 = 0)
        (hsM : s ∈ (IntermediateField.adjoin (IntermediateField.adjoin K (Set.range f)) ({α} : Set (FR4 K))).restrictScalars K)
        (hz1M : z1 ∈ (IntermediateField.adjoin (IntermediateField.adjoin K (Set.range f)) ({α} : Set (FR4 K))).restrictScalars K)
        (hz2M : z2 ∈ (IntermediateField.adjoin (IntermediateField.adjoin K (Set.range f)) ({α} : Set (FR4 K))).restrictScalars K)
        (hz3M : z3 ∈ (IntermediateField.adjoin (IntermediateField.adjoin K (Set.range f)) ({α} : Set (FR4 K))).restrictScalars K),
        IsRationalExtension K (IntermediateField.fixedField H) (Fin 4) := by
      intro f hf α P1 hP10 hP1deg hP1α hsM hz1M hz2M hz3M
      let E := IntermediateField.adjoin K (Set.range f)
      let M1 : IntermediateField K (FR4 K) := (IntermediateField.adjoin E ({α} : Set (FR4 K))).restrictScalars K
      have hy1sqM1 : y1 ^ 2 ∈ M1 := by
        rw [show y1 ^ 2 = z2 * z3 from by simp only [z2, z3]; field_simp [hy2_ne, hy3_ne]]
        exact mul_mem hz2M hz3M
      have hy2sqM1 : y2 ^ 2 ∈ M1 := by
        rw [show y2 ^ 2 = z3 * z1 from by simp only [z3, z1]; field_simp [hy3_ne, hy1_ne]]
        exact mul_mem hz3M hz1M
      have hyprodM1 : y1 * y2 * y3 ∈ M1 := by
        rw [show y1 * y2 * y3 = z1 * z2 * z3 from by simp only [z1, z2, z3]; field_simp [hy1_ne, hy2_ne, hy3_ne]]
        exact mul_mem (mul_mem hz1M hz2M) hz3M
      let P2 : Polynomial M1 := Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X + Polynomial.C (-⟨y1 ^ 2, hy1sqM1⟩)
      have hP2 : Polynomial.aeval y1 P2 = 0 := by
        rw [show P2 = _ from rfl, aeval_quad_apply]; change y1 ^ 2 + 0 * y1 + -(y1 ^ 2) = 0; ring
      set M2 : IntermediateField K (FR4 K) := (IntermediateField.adjoin M1 ({y1} : Set (FR4 K))).restrictScalars K
      have hy2sqM2 : y2 ^ 2 ∈ M2 := (IntermediateField.adjoin M1 ({y1} : Set (FR4 K))).algebraMap_mem ⟨y2 ^ 2, hy2sqM1⟩
      let P3 : Polynomial M2 := Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X + Polynomial.C (-⟨y2 ^ 2, hy2sqM2⟩)
      have hP3 : Polynomial.aeval y2 P3 = 0 := by
        rw [show P3 = _ from rfl, aeval_quad_apply]; change y2 ^ 2 + 0 * y2 + -(y2 ^ 2) = 0; ring
      have hgen : ∀ i : Fin 4, algebraMap (A4 K) (FR4 K) (X i) ∈
          IntermediateField.adjoin M2 ({y2} : Set (FR4 K)) := by
        intro i
        set M3 := IntermediateField.adjoin M2 ({y2} : Set (FR4 K))
        have hsM3 : s ∈ M3 := M3.algebraMap_mem ⟨s, (IntermediateField.adjoin M1 ({y1} : Set (FR4 K))).algebraMap_mem ⟨s, hsM⟩⟩
        have hpM3 : y1 * y2 * y3 ∈ M3 := M3.algebraMap_mem ⟨y1 * y2 * y3,
          (IntermediateField.adjoin M1 ({y1} : Set (FR4 K))).algebraMap_mem ⟨y1 * y2 * y3, hyprodM1⟩⟩
        have hy1M3 : y1 ∈ M3 := M3.algebraMap_mem ⟨y1, IntermediateField.subset_adjoin M1 _ rfl⟩
        have hy2M3 : y2 ∈ M3 := IntermediateField.subset_adjoin M2 _ rfl
        have hy3M3 : y3 ∈ M3 := by
          rw [show y3 = (y1 * y2 * y3) / (y1 * y2) from by field_simp [hy1_ne, hy2_ne]]
          exact div_mem hpM3 (mul_mem hy1M3 hy2M3)
        have h4M3 : (4 : FR4 K) ∈ M3 := M3.algebraMap_mem (4 : M2)
        fin_cases i
        · change x0 ∈ M3
          rw [show x0 = (s + y1 + y2 + y3) / 4 from by rw [eq_div_iff h4_ne]; simp only [s, y1, y2, y3]; ring]
          exact div_mem (add_mem (add_mem (add_mem hsM3 hy1M3) hy2M3) hy3M3) h4M3
        · change x1 ∈ M3
          rw [show x1 = (s + y1 - y2 - y3) / 4 from by rw [eq_div_iff h4_ne]; simp only [s, y1, y2, y3]; ring]
          exact div_mem (sub_mem (sub_mem (add_mem hsM3 hy1M3) hy2M3) hy3M3) h4M3
        · change x2 ∈ M3
          rw [show x2 = (s - y1 + y2 - y3) / 4 from by rw [eq_div_iff h4_ne]; simp only [s, y1, y2, y3]; ring]
          exact div_mem (sub_mem (add_mem (sub_mem hsM3 hy1M3) hy2M3) hy3M3) h4M3
        · change x3 ∈ M3
          rw [show x3 = (s - y1 - y2 + y3) / 4 from by rw [eq_div_iff h4_ne]; simp only [s, y1, y2, y3]; ring]
          exact div_mem (add_mem (sub_mem (sub_mem hsM3 hy1M3) hy2M3) hy3M3) h4M3
      obtain ⟨hfd, hle⟩ := finrank_le_of_three_gen E α y1 y2 P1 hP10 hP1deg hP1α
        P2 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP2 P3 (quad_ne_zero _ _) (natDegree_quad_le _ _) hP3 hgen
      exact fixedField_isRational_of_finrank_le H f hf (by rw [hcard]; exact hle)
    by_cases hchar3 : (3 : FR4 K) = 0
    · -- Characteristic 3: e1 = z1 + z2 + z3, U = (z2 - z3)/e1
      set e1 : FR4 K := z1 + z2 + z3
      have he1_ne : e1 ≠ 0 := by
        intro h
        have h1 : y2 ^ 2 * y3 ^ 2 + y3 ^ 2 * y1 ^ 2 + y1 ^ 2 * y2 ^ 2 = 0 := by
          have h2 : y2 * y3 / y1 + y3 * y1 / y2 + y1 * y2 / y3 = 0 := h
          field_simp [hy1_ne, hy2_ne, hy3_ne] at h2; linear_combination h2
        -- Check polynomial is nonzero by mapping X_2 -> 0, X_3 -> 0 into K[T] (X_0 -> T, X_1 -> 1)
        let ev : A4 K →ₐ[K] Polynomial K := MvPolynomial.aeval ![Polynomial.X, 1, 0, 0]
        have hpA : algebraMap (A4 K) (FR4 K)
            ((X 0 - X 1 + X 2 - X 3) ^ 2 * (X 0 - X 1 - X 2 + X 3) ^ 2 +
             (X 0 - X 1 - X 2 + X 3) ^ 2 * (X 0 + X 1 - X 2 - X 3) ^ 2 +
             (X 0 + X 1 - X 2 - X 3) ^ 2 * (X 0 - X 1 + X 2 - X 3) ^ 2) = 0 := by
          simpa [y1, y2, y3, x0, x1, x2, x3, map_add, map_sub, map_mul, map_pow] using h1
        have hp0 := IsFractionRing.injective (A4 K) (FR4 K) (hpA.trans (map_zero _).symm)
        have hev0 := congrArg (fun q => Polynomial.coeff (ev q) 3) hp0
        simp only [ev, map_add, map_sub, map_mul, map_pow, map_zero, aeval_X, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, sub_zero, add_zero] at hev0
        have heq : (Polynomial.X - 1 : Polynomial K) ^ 2 * (Polynomial.X - 1) ^ 2 +
            (Polynomial.X - 1) ^ 2 * (Polynomial.X + 1) ^ 2 +
            (Polynomial.X + 1) ^ 2 * (Polynomial.X - 1) ^ 2 =
            3 * Polynomial.X ^ 4 - 4 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 2 - 4 * Polynomial.X + Polynomial.C 3 := by
          simp only [map_ofNat]; ring
        rw [heq] at hev0
        simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_ofNat_mul,
          Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at hev0
        norm_num at hev0
        exact h4K_ne hev0
      set U : FR4 K := (z2 - z3) / e1
      have h1e1 : permAut K σ1 e1 = e1 := by simp only [e1, map_add, h1z1, h1z2, h1z3]
      have h2e1 : permAut K σ2 e1 = e1 := by simp only [e1, map_add, h2z1, h2z2, h2z3]
      have hte1 : permAut K τ e1 = e1 := by simp only [e1, map_add, htz1, htz2, htz3]; ring
      have h1U : permAut K σ1 U = U := by simp only [U, map_div₀, map_sub, h1z2, h1z3, h1e1]
      have h2U : permAut K σ2 U = U := by simp only [U, map_div₀, map_sub, h2z2, h2z3, h2e1]
      have htU : permAut K τ U = U - 1 := by
        simp only [U, map_div₀, map_sub, htz2, htz3, hte1]
        field_simp [he1_ne]; simp only [e1]; linear_combination z3 * hchar3
      let f : Fin 4 → FR4 K := ![s, e1, U ^ 3 - U, z1 + e1 * U ^ 2]
      have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
        intro i; apply hfix
        · fin_cases i
          · exact h1s
          · exact h1e1
          · change permAut K σ1 (U ^ 3 - U) = U ^ 3 - U; rw [map_sub, map_pow, h1U]
          · change permAut K σ1 (z1 + e1 * U ^ 2) = z1 + e1 * U ^ 2; rw [map_add, map_mul, map_pow, h1z1, h1e1, h1U]
        · fin_cases i
          · exact h2s
          · exact h2e1
          · change permAut K σ2 (U ^ 3 - U) = U ^ 3 - U; rw [map_sub, map_pow, h2U]
          · change permAut K σ2 (z1 + e1 * U ^ 2) = z1 + e1 * U ^ 2; rw [map_add, map_mul, map_pow, h2z1, h2e1, h2U]
        · fin_cases i
          · exact hts
          · exact hte1
          · change permAut K τ (U ^ 3 - U) = U ^ 3 - U
            rw [map_sub, map_pow, htU]; linear_combination (U - U ^ 2) * hchar3
          · change permAut K τ (z1 + e1 * U ^ 2) = z1 + e1 * U ^ 2
            rw [map_add, map_mul, map_pow, htz1, hte1, htU]
            have hdiff : z2 - z1 + e1 * (1 - 2 * U) = 0 := by
              simp only [U]; field_simp [he1_ne]; simp only [e1]; linear_combination z3 * hchar3
            linear_combination hdiff
      set E := IntermediateField.adjoin K (Set.range f)
      let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
      let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
      let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
      let g3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
      let P1 : Polynomial E :=
        Polynomial.X ^ 3 + Polynomial.C 0 * Polynomial.X ^ 2 + Polynomial.C (-1) * Polynomial.X + Polynomial.C (-g2)
      have hP1 : Polynomial.aeval U P1 = 0 := by
        rw [show P1 = _ from rfl, aeval_cubic_apply]; change U ^ 3 + 0 * U ^ 2 + -1 * U + -(U ^ 3 - U) = 0; ring
      set M1 : IntermediateField K (FR4 K) := (IntermediateField.adjoin E ({U} : Set (FR4 K))).restrictScalars K
      have hUM1 : U ∈ M1 := IntermediateField.subset_adjoin E _ rfl
      have hsM1 : s ∈ M1 := (IntermediateField.adjoin E ({U} : Set (FR4 K))).algebraMap_mem g0
      have he1M1 : e1 ∈ M1 := (IntermediateField.adjoin E ({U} : Set (FR4 K))).algebraMap_mem g1
      have hg3M1 : z1 + e1 * U ^ 2 ∈ M1 := (IntermediateField.adjoin E ({U} : Set (FR4 K))).algebraMap_mem g3
      have hz1M1 : z1 ∈ M1 := by
        rw [show z1 = (z1 + e1 * U ^ 2) - e1 * U ^ 2 from by ring]
        exact sub_mem hg3M1 (mul_mem he1M1 (pow_mem hUM1 2))
      have hz2M1 : z2 ∈ M1 := by
        have : z2 = -(e1 - z1 + e1 * U) := by
          simp only [U]; field_simp [he1_ne]; simp only [e1]; linear_combination z2 * hchar3
        rw [this]; exact neg_mem (add_mem (sub_mem he1M1 hz1M1) (mul_mem he1M1 hUM1))
      have hz3M1 : z3 ∈ M1 := by
        rw [show z3 = e1 - z1 - z2 from by simp only [e1]; ring]
        exact sub_mem (sub_mem he1M1 hz1M1) hz2M1
      exact hfinish f hf U P1 (cubic_ne_zero _ _ _) (natDegree_cubic_le _ _ _) hP1 hsM1 hz1M1 hz2M1 hz3M1
    · -- Characteristic ≠ 2, 3: w = z2 - z3, Z = (z1 - z2) / w
      set w : FR4 K := z2 - z3
      have hw_ne : w ≠ 0 := by
        intro h
        have h1 : y3 ^ 2 - y2 ^ 2 = 0 := by
          have h2 : y3 * y1 / y2 - y1 * y2 / y3 = 0 := h
          field_simp [hy2_ne, hy3_ne] at h2
          exact (mul_eq_zero.mp (by linear_combination h2 : y1 * (y3 ^ 2 - y2 ^ 2) = 0)).resolve_left hy1_ne
        let ev : A4 K →ₐ[K] Polynomial K := MvPolynomial.aeval ![Polynomial.X, 0, 1, 0]
        have hpA : algebraMap (A4 K) (FR4 K) ((X 0 - X 1 - X 2 + X 3) ^ 2 - (X 0 - X 1 + X 2 - X 3) ^ 2) = 0 := by
          simpa [y2, y3, x0, x1, x2, x3, map_add, map_sub, map_pow] using h1
        have hp0 := IsFractionRing.injective (A4 K) (FR4 K) (hpA.trans (map_zero _).symm)
        have hev0 := congrArg (fun q => Polynomial.coeff (ev q) 1) hp0
        simp only [ev, map_add, map_sub, map_pow, map_zero, aeval_X, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, sub_zero, add_zero] at hev0
        rw [show (Polynomial.X - 1 : Polynomial K) ^ 2 - (Polynomial.X + 1) ^ 2 = Polynomial.C (-4 : K) * Polynomial.X from by simp only [map_neg, map_ofNat]; ring] at hev0
        rw [Polynomial.coeff_C_mul_X] at hev0
        exact h4K_ne (neg_eq_zero.mp hev0)
      have hz12_ne : z1 - z2 ≠ 0 := by
        intro h
        have h1 : y2 ^ 2 - y1 ^ 2 = 0 := by
          have h2 : y2 * y3 / y1 - y3 * y1 / y2 = 0 := h
          field_simp [hy1_ne, hy2_ne] at h2
          exact (mul_eq_zero.mp (by linear_combination h2 : y3 * (y2 ^ 2 - y1 ^ 2) = 0)).resolve_left hy3_ne
        let ev : A4 K →ₐ[K] Polynomial K := MvPolynomial.aeval ![Polynomial.X, 1, 0, 0]
        have hpA : algebraMap (A4 K) (FR4 K) ((X 0 - X 1 + X 2 - X 3) ^ 2 - (X 0 + X 1 - X 2 - X 3) ^ 2) = 0 := by
          simpa [y1, y2, x0, x1, x2, x3, map_add, map_sub, map_pow] using h1
        have hp0 := IsFractionRing.injective (A4 K) (FR4 K) (hpA.trans (map_zero _).symm)
        have hev0 := congrArg (fun q => Polynomial.coeff (ev q) 1) hp0
        simp only [ev, map_add, map_sub, map_pow, map_zero, aeval_X, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, sub_zero, add_zero] at hev0
        rw [show (Polynomial.X - 1 : Polynomial K) ^ 2 - (Polynomial.X + 1) ^ 2 = Polynomial.C (-4 : K) * Polynomial.X from by simp only [map_neg, map_ofNat]; ring] at hev0
        rw [Polynomial.coeff_C_mul_X] at hev0
        exact h4K_ne (neg_eq_zero.mp hev0)
      have hz13_ne : z1 - z3 ≠ 0 := by
        intro h
        have h1 : y3 ^ 2 - y1 ^ 2 = 0 := by
          have h2 : y2 * y3 / y1 - y1 * y2 / y3 = 0 := h
          field_simp [hy1_ne, hy3_ne] at h2
          exact (mul_eq_zero.mp (by linear_combination h2 : y2 * (y3 ^ 2 - y1 ^ 2) = 0)).resolve_left hy2_ne
        let ev : A4 K →ₐ[K] Polynomial K := MvPolynomial.aeval ![Polynomial.X, 1, 0, 0]
        have hpA : algebraMap (A4 K) (FR4 K) ((X 0 - X 1 - X 2 + X 3) ^ 2 - (X 0 + X 1 - X 2 - X 3) ^ 2) = 0 := by
          simpa [y1, y3, x0, x1, x2, x3, map_add, map_sub, map_pow] using h1
        have hp0 := IsFractionRing.injective (A4 K) (FR4 K) (hpA.trans (map_zero _).symm)
        have hev0 := congrArg (fun q => Polynomial.coeff (ev q) 1) hp0
        simp only [ev, map_add, map_sub, map_pow, map_zero, aeval_X, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, sub_zero, add_zero] at hev0
        rw [show (Polynomial.X - 1 : Polynomial K) ^ 2 - (Polynomial.X + 1) ^ 2 = Polynomial.C (-4 : K) * Polynomial.X from by simp only [map_neg, map_ofNat]; ring] at hev0
        rw [Polynomial.coeff_C_mul_X] at hev0
        exact h4K_ne (neg_eq_zero.mp hev0)
      set Z : FR4 K := (z1 - z2) / w
      have hZ_ne : Z ≠ 0 := div_ne_zero hz12_ne hw_ne
      have hZ1_ne : Z + 1 ≠ 0 := by
        intro h
        have h2 : (z1 - z2) / w + 1 = 0 := h
        field_simp [hw_ne] at h2
        apply hz13_ne; simp only [w] at h2; linear_combination h2
      have hZ2_ne : Z ^ 2 + Z + 1 ≠ 0 := by
        intro h
        have h2 : ((z1 - z2) / w) ^ 2 + (z1 - z2) / w + 1 = 0 := h
        field_simp [hw_ne] at h2
        have h3 : z1 ^ 2 + z2 ^ 2 + z3 ^ 2 - z1 * z2 - z2 * z3 - z3 * z1 = 0 := by
          simp only [w] at h2; linear_combination h2
        have h4 : y2 ^ 4 * y3 ^ 4 + y3 ^ 4 * y1 ^ 4 + y1 ^ 4 * y2 ^ 4 -
            y1 ^ 2 * y2 ^ 2 * y3 ^ 2 * (y1 ^ 2 + y2 ^ 2 + y3 ^ 2) = 0 := by
          simp only [z1, z2, z3] at h3; field_simp [hy1_ne, hy2_ne, hy3_ne] at h3; linear_combination h3
        let ev : A4 K →ₐ[K] Polynomial K := MvPolynomial.aeval ![Polynomial.X, 1, 0, 0]
        let pY1 : A4 K := X 0 + X 1 - X 2 - X 3
        let pY2 : A4 K := X 0 - X 1 + X 2 - X 3
        let pY3 : A4 K := X 0 - X 1 - X 2 + X 3
        have hpA : algebraMap (A4 K) (FR4 K) (pY2 ^ 4 * pY3 ^ 4 + pY3 ^ 4 * pY1 ^ 4 + pY1 ^ 4 * pY2 ^ 4 -
            pY1 ^ 2 * pY2 ^ 2 * pY3 ^ 2 * (pY1 ^ 2 + pY2 ^ 2 + pY3 ^ 2)) = 0 := by
          simpa [pY1, pY2, pY3, y1, y2, y3, x0, x1, x2, x3, map_add, map_sub, map_mul, map_pow] using h4
        have hp0 := IsFractionRing.injective (A4 K) (FR4 K) (hpA.trans (map_zero _).symm)
        have hev0 := congrArg (fun q => Polynomial.coeff (ev q) 6) hp0
        simp only [ev, pY1, pY2, pY3, map_add, map_sub, map_mul, map_pow, map_zero, aeval_X,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, sub_zero, add_zero] at hev0
        have heq : (Polynomial.X - 1 : Polynomial K) ^ 4 * (Polynomial.X - 1) ^ 4 +
            (Polynomial.X - 1) ^ 4 * (Polynomial.X + 1) ^ 4 +
            (Polynomial.X + 1) ^ 4 * (Polynomial.X - 1) ^ 4 -
            (Polynomial.X + 1) ^ 2 * (Polynomial.X - 1) ^ 2 * (Polynomial.X - 1) ^ 2 *
              ((Polynomial.X + 1) ^ 2 + (Polynomial.X - 1) ^ 2 + (Polynomial.X - 1) ^ 2) =
            16 * Polynomial.X ^ 6 - 64 * Polynomial.X ^ 5 + 96 * Polynomial.X ^ 4 -
              64 * Polynomial.X ^ 3 + 16 * Polynomial.X ^ 2 := by ring
        rw [heq] at hev0
        simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_ofNat_mul,
          Polynomial.coeff_X_pow] at hev0
        norm_num at hev0
        have : (16 : K) = 4 * 4 := by norm_num
        rw [this] at hev0
        exact mul_ne_zero h4K_ne h4K_ne hev0
      have h1w : permAut K σ1 w = w := by simp only [w, map_sub, h1z2, h1z3]
      have h2w : permAut K σ2 w = w := by simp only [w, map_sub, h2z2, h2z3]
      have htw : permAut K τ w = -(Z + 1) * w := by
        rw [show w = z2 - z3 from rfl, map_sub, htz2, htz3]
        have hZw : Z * w = z1 - z2 := div_mul_cancel₀ _ hw_ne
        rw [show -(Z + 1) * w = -(Z * w) - w from by ring, hZw]; simp only [w]; ring
      have h1Z : permAut K σ1 Z = Z := by simp only [Z, map_div₀, map_sub, h1z1, h1z2, h1w]
      have h2Z : permAut K σ2 Z = Z := by simp only [Z, map_div₀, map_sub, h2z1, h2z2, h2w]
      have htZ : permAut K τ Z = -1 / (Z + 1) := by
        rw [show Z = (z1 - z2) / w from rfl, map_div₀, map_sub, htz1, htz2, htw]
        change w / (-(Z + 1) * w) = -1 / (Z + 1); field_simp [hw_ne, hZ1_ne]
      let f : Fin 4 → FR4 K :=
        ![s, z1 + z2 + z3, (Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1)), w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))]
      have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
        intro i; apply hfix
        · fin_cases i
          · exact h1s
          · change permAut K σ1 (z1 + z2 + z3) = z1 + z2 + z3; rw [map_add, map_add, h1z1, h1z2, h1z3]
          · change permAut K σ1 ((Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))) = (Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))
            simp only [map_div₀, map_sub, map_mul, map_pow, map_add, map_one, map_ofNat, h1Z]
          · change permAut K σ1 (w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))) = w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))
            simp only [map_div₀, map_mul, map_pow, map_add, map_one, h1w, h1Z]
        · fin_cases i
          · exact h2s
          · change permAut K σ2 (z1 + z2 + z3) = z1 + z2 + z3; rw [map_add, map_add, h2z1, h2z2, h2z3]
          · change permAut K σ2 ((Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))) = (Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))
            simp only [map_div₀, map_sub, map_mul, map_pow, map_add, map_one, map_ofNat, h2Z]
          · change permAut K σ2 (w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))) = w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))
            simp only [map_div₀, map_mul, map_pow, map_add, map_one, h2w, h2Z]
        · fin_cases i
          · exact hts
          · change permAut K τ (z1 + z2 + z3) = z1 + z2 + z3; rw [map_add, map_add, htz1, htz2, htz3]; ring
          · change permAut K τ ((Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))) = (Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))
            rw [map_div₀, map_sub, map_sub, map_pow, map_mul, map_ofNat, map_one, map_mul, map_add, map_one, htZ]
            have hZ1'_eq : -1 / (Z + 1) + 1 = Z / (Z + 1) := by field_simp [hZ1_ne]; ring
            rw [hZ1'_eq]
            field_simp [hZ_ne, hZ1_ne]; ring
          · change permAut K τ (w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))) = w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))
            rw [map_div₀, map_mul, htw, map_pow, map_add, map_add, map_pow, map_one, map_mul, map_add, map_one, htZ]
            have hZ1'_eq : -1 / (Z + 1) + 1 = Z / (Z + 1) := by field_simp [hZ1_ne]; ring
            rw [hZ1'_eq]
            field_simp [hZ_ne, hZ1_ne]; ring
      set E := IntermediateField.adjoin K (Set.range f)
      let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
      let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
      let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
      let g3 : E := ⟨f 3, IntermediateField.subset_adjoin K _ ⟨3, rfl⟩⟩
      let P1 : Polynomial E :=
        Polynomial.X ^ 3 + Polynomial.C (-g2) * Polynomial.X ^ 2 +
          Polynomial.C (-(g2 + 3)) * Polynomial.X + Polynomial.C (-1)
      have hP1 : Polynomial.aeval Z P1 = 0 := by
        rw [show P1 = _ from rfl, aeval_cubic_apply]
        change Z ^ 3 + -((Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))) * Z ^ 2 +
          -(((Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))) + 3) * Z + -1 = 0
        field_simp [hZ_ne, hZ1_ne]; ring
      set M1 : IntermediateField K (FR4 K) := (IntermediateField.adjoin E ({Z} : Set (FR4 K))).restrictScalars K
      have hZM1 : Z ∈ M1 := IntermediateField.subset_adjoin E _ rfl
      have hsM1 : s ∈ M1 := (IntermediateField.adjoin E ({Z} : Set (FR4 K))).algebraMap_mem g0
      have hg1M1 : z1 + z2 + z3 ∈ M1 := (IntermediateField.adjoin E ({Z} : Set (FR4 K))).algebraMap_mem g1
      have hg3M1 : w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1)) ∈ M1 :=
        (IntermediateField.adjoin E ({Z} : Set (FR4 K))).algebraMap_mem g3
      have hwM1 : w ∈ M1 := by
        have hZ2' : Z * (Z + 1) + 1 ≠ 0 := by convert hZ2_ne using 1; ring
        have : w = (w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))) * (Z * (Z + 1)) / (Z ^ 2 + Z + 1) ^ 2 := by
          field_simp [hZ_ne, hZ1_ne, hZ2_ne, hZ2']
        rw [this]
        exact div_mem (mul_mem hg3M1 (mul_mem hZM1 (add_mem hZM1 M1.one_mem)))
          (pow_mem (add_mem (add_mem (pow_mem hZM1 2) hZM1) M1.one_mem) 2)
      have hz1M1 : z1 ∈ M1 := by
        have hZw : Z * w = z1 - z2 := div_mul_cancel₀ _ hw_ne
        have : z1 = ((z1 + z2 + z3) + (2 * Z + 1) * w) / 3 := by
          rw [eq_div_iff hchar3, show (2 * Z + 1) * w = 2 * (Z * w) + w from by ring, hZw]
          simp only [w]; ring
        rw [this]
        exact div_mem (add_mem hg1M1 (mul_mem (add_mem (mul_mem
          ((IntermediateField.adjoin E ({Z} : Set (FR4 K))).algebraMap_mem (2 : E)) hZM1) M1.one_mem) hwM1))
          ((IntermediateField.adjoin E ({Z} : Set (FR4 K))).algebraMap_mem (3 : E))
      have hz2M1 : z2 ∈ M1 := by
        have hZw : Z * w = z1 - z2 := div_mul_cancel₀ _ hw_ne
        rw [show z2 = z1 - Z * w from by rw [hZw]; ring]
        exact sub_mem hz1M1 (mul_mem hZM1 hwM1)
      have hz3M1 : z3 ∈ M1 := by
        rw [show z3 = z2 - w from by simp only [w]; ring]
        exact sub_mem hz2M1 hwM1
      exact hfinish f hf Z P1 (cubic_ne_zero _ _ _) (natDegree_cubic_le _ _ _) hP1 hsM1 hz1M1 hz2M1 hz3M1

/-- Helper: every subgroup of Perm (Fin 4) of order 6 fixes a point of Fin 4. -/
private lemma exists_fixed_of_card_six (G : Subgroup (Perm (Fin 4))) [Fintype G]
    (h6 : Fintype.card G = 6) : ∃ k : Fin 4, ∀ σ ∈ G, σ k = k := by
  classical
  -- Every orbit of G on Fin 4 has size dividing 6 and ≤ 4, so size ∈ {1, 2, 3}.
  by_contra hnofix
  push Not at hnofix
  -- For each i : Fin 4, let orb i = Finset.univ.image (fun g : G => g.1 i)
  let orb (i : Fin 4) : Finset (Fin 4) := Finset.univ.image (fun g : G => g.1 i)
  have horb_pos : ∀ i : Fin 4, 2 ≤ (orb i).card := by
    intro i
    obtain ⟨σ, hσG, hσne⟩ := hnofix i
    have hmem1 : i ∈ orb i := Finset.mem_image.mpr ⟨1, Finset.mem_univ 1, rfl⟩
    have hmem2 : σ i ∈ orb i := Finset.mem_image.mpr ⟨⟨σ, hσG⟩, Finset.mem_univ _, rfl⟩
    have hsub : ({i, σ i} : Finset (Fin 4)) ⊆ orb i := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have h2 : ({i, σ i} : Finset (Fin 4)).card = 2 := Finset.card_pair (Ne.symm hσne)
    exact h2 ▸ Finset.card_le_card hsub
  have horb_dvd : ∀ i : Fin 4, (orb i).card ∣ 6 := by
    intro i
    -- Fiber of (fun g : G => g.1 i) over any j ∈ orb i has the same size as the stabilizer of i
    let stab : Finset G := Finset.univ.filter (fun g : G => g.1 i = i)
    have hfiber : ∀ j ∈ orb i, (Finset.univ.filter (fun g : G => g.1 i = j)).card = stab.card := by
      intro j hj
      obtain ⟨g0, _, rfl⟩ := Finset.mem_image.mp hj
      apply Finset.card_bij (fun g _ => g0⁻¹ * g)
      · intro g hg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, stab] at hg ⊢
        change (g0.1⁻¹ * g.1) i = i
        rw [Perm.mul_apply, hg, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]
      · intro a _ b _ hab; exact mul_left_cancel hab
      · intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, stab] at hs
        refine ⟨g0 * s, ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change (g0.1 * s.1) i = g0.1 i
        rw [Perm.mul_apply, hs]
    have hsum := Finset.card_eq_sum_card_fiberwise (f := fun g : G => g.1 i) (s := Finset.univ) (t := orb i)
      (fun g _ => Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩)
    rw [Finset.card_univ, h6] at hsum
    have hsum' : ∑ j ∈ orb i, (Finset.univ.filter (fun g : G => g.1 i = j)).card = (orb i).card * stab.card := by
      rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]
    rw [hsum'] at hsum
    exact ⟨stab.card, hsum⟩
  -- So every orbit has size 2 or 3.
  have horb_le : ∀ i : Fin 4, (orb i).card ≤ 4 := fun i =>
    (Finset.card_le_univ (orb i)).trans (by simp)
  have horb_23 : ∀ i : Fin 4, (orb i).card = 2 ∨ (orb i).card = 3 := by
    intro i
    have h1 := horb_pos i
    have h2 := horb_dvd i
    have h3 := horb_le i
    interval_cases h : (orb i).card <;> simp_all
  -- Orbits are either equal or disjoint
  have horb_disj_or_eq : ∀ i j : Fin 4, orb i = orb j ∨ Disjoint (orb i) (orb j) := by
    intro i j
    by_cases h : ∃ x, x ∈ orb i ∧ x ∈ orb j
    · left
      obtain ⟨x, hi, hj⟩ := h
      obtain ⟨g1, _, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨g2, _, h2⟩ := Finset.mem_image.mp hj
      ext y; simp only [orb, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨g, rfl⟩
        refine ⟨g * g1⁻¹ * g2, ?_⟩
        change (g.1 * g1.1⁻¹ * g2.1) j = g.1 i
        rw [Perm.mul_apply, Perm.mul_apply, h2, show g1.1⁻¹ (g1.1 i) = i from by rw [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]]
      · rintro ⟨g, rfl⟩
        refine ⟨g * g2⁻¹ * g1, ?_⟩
        change (g.1 * g2.1⁻¹ * g1.1) i = g.1 j
        rw [Perm.mul_apply, Perm.mul_apply, ← h2, show g2.1⁻¹ (g2.1 j) = j from by rw [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]]
    · right
      rw [Finset.disjoint_left]
      intro x hx1 hx2; exact h ⟨x, hx1, hx2⟩
  -- If any orbit has size 3, the remaining 1 element has orbit size 1, contradiction!
  by_cases h3 : ∃ i : Fin 4, (orb i).card = 3
  · obtain ⟨i, hi3⟩ := h3
    have hne_univ : orb i ≠ Finset.univ := by intro h; rw [h, Finset.card_univ] at hi3; norm_num at hi3
    obtain ⟨j, hj⟩ : ∃ j : Fin 4, j ∉ orb i := by
      by_contra hall; push Not at hall
      exact hne_univ (Finset.eq_univ_iff_forall.mpr hall)
    have hdisj : Disjoint (orb i) (orb j) := by
      rcases horb_disj_or_eq i j with heq | hd
      · exfalso; apply hj; rw [heq]; exact Finset.mem_image.mpr ⟨1, Finset.mem_univ 1, rfl⟩
      · exact hd
    have hcard_union : (orb i ∪ orb j).card = (orb i).card + (orb j).card := Finset.card_union_of_disjoint hdisj
    have hle4 : (orb i ∪ orb j).card ≤ 4 := (Finset.card_le_univ _).trans (by simp)
    have := horb_pos j
    omega
  · -- All orbits have size 2! So every σ ∈ G preserves orb 0 (size 2) and (orb 0)ᶜ (size 2), hence |G| ≤ 4!
    push Not at h3
    have h02 : (orb 0).card = 2 := (horb_23 0).resolve_right (h3 0)
    have hG_pres : ∀ σ ∈ G, ∀ x ∈ orb 0, σ x ∈ orb 0 := by
      intro σ hσ x hx
      obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨⟨σ, hσ⟩ * g, Finset.mem_univ _, rfl⟩
    have hsub_le4 : (Finset.univ.filter (fun σ : Perm (Fin 4) => ∀ x ∈ orb 0, σ x ∈ orb 0)).card ≤ 4 := by
      have hall : ∀ S : Finset (Fin 4), S.card = 2 →
          (Finset.univ.filter (fun σ : Perm (Fin 4) => ∀ x ∈ S, σ x ∈ S)).card ≤ 4 := by decide
      exact hall (orb 0) h02
    have hG_sub : Finset.univ.image (fun g : G => g.1) ⊆
        Finset.univ.filter (fun σ : Perm (Fin 4) => ∀ x ∈ orb 0, σ x ∈ orb 0) := by
      intro σ hσ
      obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hσ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG_pres g.1 g.2⟩
    have hcard_img : (Finset.univ.image (fun g : G => g.1)).card = 6 := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ, h6]
    have := Finset.card_le_card hG_sub
    omega

/-- Helper: every subgroup of Perm (Fin 4) of order 8 stabilizes one of the 3 pair-partitions. -/
private lemma exists_partition_of_card_eight (G : Subgroup (Perm (Fin 4))) [Fintype G]
    (h8 : Fintype.card G = 8) :
    ∃ π : Perm (Fin 4), ∀ σ ∈ G,
      (((π * σ * π⁻¹) 0 = 0 ∨ (π * σ * π⁻¹) 0 = 2) ∧ ((π * σ * π⁻¹) 2 = 0 ∨ (π * σ * π⁻¹) 2 = 2)) ∨
      (((π * σ * π⁻¹) 0 = 1 ∨ (π * σ * π⁻¹) 0 = 3) ∧ ((π * σ * π⁻¹) 2 = 1 ∨ (π * σ * π⁻¹) 2 = 3)) := by
  classical
  -- Define the 3 pair-partitions as Fin 3, and action of Perm (Fin 4) on Fin 3:
  -- 0 = {{0,2},{1,3}}, 1 = {{0,1},{2,3}}, 2 = {{0,3},{1,2}}
  let partAct (σ : Perm (Fin 4)) (p : Fin 3) : Fin 3 :=
    match p with
    | 0 => if (σ 0 = 0 ∨ σ 0 = 2) ∧ (σ 2 = 0 ∨ σ 2 = 2) ∨ (σ 0 = 1 ∨ σ 0 = 3) ∧ (σ 2 = 1 ∨ σ 2 = 3) then 0
           else if (σ 0 = 0 ∨ σ 0 = 1) ∧ (σ 2 = 0 ∨ σ 2 = 1) ∨ (σ 0 = 2 ∨ σ 0 = 3) ∧ (σ 2 = 2 ∨ σ 2 = 3) then 1
           else 2
    | 1 => if (σ 0 = 0 ∨ σ 0 = 2) ∧ (σ 1 = 0 ∨ σ 1 = 2) ∨ (σ 0 = 1 ∨ σ 0 = 3) ∧ (σ 1 = 1 ∨ σ 1 = 3) then 0
           else if (σ 0 = 0 ∨ σ 0 = 1) ∧ (σ 1 = 0 ∨ σ 1 = 1) ∨ (σ 0 = 2 ∨ σ 0 = 3) ∧ (σ 1 = 2 ∨ σ 1 = 3) then 1
           else 2
    | 2 => if (σ 0 = 0 ∨ σ 0 = 2) ∧ (σ 3 = 0 ∨ σ 3 = 2) ∨ (σ 0 = 1 ∨ σ 0 = 3) ∧ (σ 3 = 1 ∨ σ 3 = 3) then 0
           else if (σ 0 = 0 ∨ σ 0 = 1) ∧ (σ 3 = 0 ∨ σ 3 = 1) ∨ (σ 0 = 2 ∨ σ 0 = 3) ∧ (σ 3 = 2 ∨ σ 3 = 3) then 1
           else 2
  have hact_one : ∀ p : Fin 3, partAct 1 p = p := by decide
  have hact_mul : ∀ σ τ : Perm (Fin 4), ∀ p : Fin 3, partAct (σ * τ) p = partAct σ (partAct τ p) := by decide
  -- Every orbit of G on Fin 3 has size dividing 8 and ≤ 3, so size 1 or 2; since |Fin 3| = 3 is odd, some p is fixed!
  have hex_fix : ∃ p : Fin 3, ∀ g : G, partAct g.1 p = p := by
    by_contra hno
    push Not at hno
    let orb (p : Fin 3) : Finset (Fin 3) := Finset.univ.image (fun g : G => partAct g.1 p)
    have horb_ge2 : ∀ p : Fin 3, 2 ≤ (orb p).card := by
      intro p
      obtain ⟨g, hg⟩ := hno p
      have h1 : p ∈ orb p := Finset.mem_image.mpr ⟨1, Finset.mem_univ 1, hact_one p⟩
      have h2 : partAct g.1 p ∈ orb p := Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩
      have hsub : ({p, partAct g.1 p} : Finset (Fin 3)) ⊆ orb p := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      exact (Finset.card_pair (Ne.symm hg)) ▸ Finset.card_le_card hsub
    have horb_dvd : ∀ p : Fin 3, (orb p).card ∣ 8 := by
      intro p
      let stab : Finset G := Finset.univ.filter (fun g : G => partAct g.1 p = p)
      have hfiber : ∀ q ∈ orb p, (Finset.univ.filter (fun g : G => partAct g.1 p = q)).card = stab.card := by
        intro q hq
        obtain ⟨g0, _, rfl⟩ := Finset.mem_image.mp hq
        apply Finset.card_bij (fun g _ => g0⁻¹ * g)
        · intro g hg
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, stab] at hg ⊢
          change partAct (g0.1⁻¹ * g.1) p = p
          rw [hact_mul, hg, ← hact_mul, inv_mul_cancel, hact_one]
        · intro a _ b _ hab; exact mul_left_cancel hab
        · intro s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, stab] at hs
          refine ⟨g0 * s, ?_, by simp⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          change partAct (g0.1 * s.1) p = partAct g0.1 p
          rw [hact_mul, hs]
      have hsum := Finset.card_eq_sum_card_fiberwise (f := fun g : G => partAct g.1 p) (s := Finset.univ) (t := orb p)
        (fun g _ => Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩)
      rw [Finset.card_univ, h8] at hsum
      have hsum' : ∑ q ∈ orb p, (Finset.univ.filter (fun g : G => partAct g.1 p = q)).card = (orb p).card * stab.card := by
        rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]
      rw [hsum'] at hsum
      exact ⟨stab.card, hsum⟩
    have horb_eq2 : ∀ p : Fin 3, (orb p).card = 2 := by
      intro p
      have h1 := horb_ge2 p
      have h2 := horb_dvd p
      have h3 : (orb p).card ≤ 3 := (Finset.card_le_univ _).trans (by simp)
      interval_cases h : (orb p).card <;> simp_all
    -- orb 0 has size 2, so there is q ∉ orb 0; orb q is disjoint from orb 0 and also has size 2, 2 + 2 > 3!
    have hne_u : orb 0 ≠ Finset.univ := by intro h; have := horb_eq2 0; rw [h, Finset.card_univ] at this; norm_num at this
    obtain ⟨q, hq⟩ : ∃ q : Fin 3, q ∉ orb 0 := by
      by_contra hall; push Not at hall; exact hne_u (Finset.eq_univ_iff_forall.mpr hall)
    have hdisj : Disjoint (orb 0) (orb q) := by
      rw [Finset.disjoint_left]
      intro x hx0 hxq
      obtain ⟨g1, _, rfl⟩ := Finset.mem_image.mp hx0
      obtain ⟨g2, _, h2⟩ := Finset.mem_image.mp hxq
      apply hq
      refine Finset.mem_image.mpr ⟨g2⁻¹ * g1, Finset.mem_univ _, ?_⟩
      change partAct ((g2⁻¹ * g1).1) 0 = q
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hact_mul (g2.1⁻¹) g1.1 0, ← h2, ← hact_mul (g2.1⁻¹) g2.1 q, inv_mul_cancel, hact_one]
    have hcard_u : (orb 0 ∪ orb q).card = (orb 0).card + (orb q).card := Finset.card_union_of_disjoint hdisj
    have hle3 : (orb 0 ∪ orb q).card ≤ 3 := (Finset.card_le_univ _).trans (by simp)
    rw [horb_eq2 0, horb_eq2 q] at hcard_u
    omega
  obtain ⟨p, hp⟩ := hex_fix
  fin_cases p
  · refine ⟨1, fun σ hσ => ?_⟩
    have h0 := hp ⟨σ, hσ⟩
    have hall : ∀ τ : Perm (Fin 4), partAct τ 0 = 0 →
        (((1 * τ * 1⁻¹) 0 = 0 ∨ (1 * τ * 1⁻¹) 0 = 2) ∧ ((1 * τ * 1⁻¹) 2 = 0 ∨ (1 * τ * 1⁻¹) 2 = 2)) ∨
        (((1 * τ * 1⁻¹) 0 = 1 ∨ (1 * τ * 1⁻¹) 0 = 3) ∧ ((1 * τ * 1⁻¹) 2 = 1 ∨ (1 * τ * 1⁻¹) 2 = 3)) := by decide
    exact hall σ h0
  · refine ⟨Equiv.swap (1 : Fin 4) 2, fun σ hσ => ?_⟩
    have h1 := hp ⟨σ, hσ⟩
    have hall : ∀ τ : Perm (Fin 4), partAct τ 1 = 1 →
        (((Equiv.swap (1 : Fin 4) 2 * τ * (Equiv.swap (1 : Fin 4) 2)⁻¹) 0 = 0 ∨ (Equiv.swap (1 : Fin 4) 2 * τ * (Equiv.swap (1 : Fin 4) 2)⁻¹) 0 = 2) ∧
         ((Equiv.swap (1 : Fin 4) 2 * τ * (Equiv.swap (1 : Fin 4) 2)⁻¹) 2 = 0 ∨ (Equiv.swap (1 : Fin 4) 2 * τ * (Equiv.swap (1 : Fin 4) 2)⁻¹) 2 = 2)) ∨
        (((Equiv.swap (1 : Fin 4) 2 * τ * (Equiv.swap (1 : Fin 4) 2)⁻¹) 0 = 1 ∨ (Equiv.swap (1 : Fin 4) 2 * τ * (Equiv.swap (1 : Fin 4) 2)⁻¹) 0 = 3) ∧
         ((Equiv.swap (1 : Fin 4) 2 * τ * (Equiv.swap (1 : Fin 4) 2)⁻¹) 2 = 1 ∨ (Equiv.swap (1 : Fin 4) 2 * τ * (Equiv.swap (1 : Fin 4) 2)⁻¹) 2 = 3)) := by decide
    exact hall σ h1
  · refine ⟨Equiv.swap (2 : Fin 4) 3, fun σ hσ => ?_⟩
    have h2 := hp ⟨σ, hσ⟩
    have hall : ∀ τ : Perm (Fin 4), partAct τ 2 = 2 →
        (((Equiv.swap (2 : Fin 4) 3 * τ * (Equiv.swap (2 : Fin 4) 3)⁻¹) 0 = 0 ∨ (Equiv.swap (2 : Fin 4) 3 * τ * (Equiv.swap (2 : Fin 4) 3)⁻¹) 0 = 2) ∧
         ((Equiv.swap (2 : Fin 4) 3 * τ * (Equiv.swap (2 : Fin 4) 3)⁻¹) 2 = 0 ∨ (Equiv.swap (2 : Fin 4) 3 * τ * (Equiv.swap (2 : Fin 4) 3)⁻¹) 2 = 2)) ∨
        (((Equiv.swap (2 : Fin 4) 3 * τ * (Equiv.swap (2 : Fin 4) 3)⁻¹) 0 = 1 ∨ (Equiv.swap (2 : Fin 4) 3 * τ * (Equiv.swap (2 : Fin 4) 3)⁻¹) 0 = 3) ∧
         ((Equiv.swap (2 : Fin 4) 3 * τ * (Equiv.swap (2 : Fin 4) 3)⁻¹) 2 = 1 ∨ (Equiv.swap (2 : Fin 4) 3 * τ * (Equiv.swap (2 : Fin 4) 3)⁻¹) 2 = 3)) := by decide
    exact hall σ h2

/-- Helper: every subgroup of Perm (Fin 4) of order 12 is A_4 (all permutations have sign 1). -/
private lemma sign_eq_one_of_card_twelve (G : Subgroup (Perm (Fin 4))) [Fintype G]
    (h12 : Fintype.card G = 12) : ∀ σ ∈ G, Equiv.Perm.sign σ = 1 := by
  classical
  by_contra hodd
  push Not at hodd
  obtain ⟨g0, hg0G, hg0sign⟩ := hodd
  -- G_even = {g ∈ G | sign g = 1} is a subgroup of G of index 2, hence cardinality 6
  let Geven : Subgroup (Perm (Fin 4)) := G ⊓ Equiv.Perm.sign.ker
  letI : Fintype Geven := Fintype.ofFinite Geven
  have hcard_even : Fintype.card Geven = 6 := by
    let S1 : Finset G := Finset.univ.filter (fun g : G => Equiv.Perm.sign g.1 = 1)
    let S2 : Finset G := Finset.univ.filter (fun g : G => Equiv.Perm.sign g.1 ≠ 1)
    have hdisj : Disjoint S1 S2 := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1)
    have hunion : S1 ∪ S2 = Finset.univ := by
      ext g; simp only [S1, S2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; exact iff_true_intro (em _)
    have hbij : S1.card = S2.card := by
      apply Finset.card_bij (fun g _ => ⟨g0, hg0G⟩ * g)
      · intro g hg
        simp only [S1, S2, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
        change Equiv.Perm.sign (g0 * g.1) ≠ 1
        rw [map_mul, hg, mul_one]; exact hg0sign
      · intro a _ b _ hab; exact mul_left_cancel hab
      · intro g hg
        simp only [S1, S2, Finset.mem_filter, Finset.mem_univ, true_and] at hg
        refine ⟨⟨g0, hg0G⟩⁻¹ * g, ?_, by simp⟩
        simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and]
        change Equiv.Perm.sign (g0⁻¹ * g.1) = 1
        rw [map_mul, map_inv]
        have hs1 : Equiv.Perm.sign g0 = -1 := (Int.units_eq_one_or (Equiv.Perm.sign g0)).resolve_left hg0sign
        have hs2 : Equiv.Perm.sign g.1 = -1 := (Int.units_eq_one_or (Equiv.Perm.sign g.1)).resolve_left hg
        rw [hs1, hs2]; decide
    have hsum : S1.card + S2.card = 12 := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, h12]
    have hS1_eq : Fintype.card Geven = S1.card := by
      rw [← Fintype.card_coe S1]
      apply Fintype.card_of_bijective (f := fun x : Geven => (⟨⟨x.1, x.2.1⟩, by
        simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and]; exact x.2.2⟩ : S1))
      constructor
      · intro a b hab; exact Subtype.ext (congrArg (fun z : S1 => z.1.1) hab)
      · rintro ⟨⟨σ, hσG⟩, hσS⟩
        simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hσS
        exact ⟨⟨σ, hσG, hσS⟩, rfl⟩
    omega
  -- By exists_fixed_of_card_six, Geven fixes some k : Fin 4
  obtain ⟨k, hk⟩ := exists_fixed_of_card_six Geven hcard_even
  -- But at most 3 even permutations in Perm (Fin 4) fix k!
  have hle3 : (Finset.univ.filter (fun σ : Perm (Fin 4) => Equiv.Perm.sign σ = 1 ∧ σ k = k)).card ≤ 3 := by
    have hall : ∀ j : Fin 4, (Finset.univ.filter (fun σ : Perm (Fin 4) => Equiv.Perm.sign σ = 1 ∧ σ j = j)).card ≤ 3 := by
      decide
    exact hall k
  have hsub : Finset.univ.image (fun g : Geven => g.1) ⊆
      Finset.univ.filter (fun σ : Perm (Fin 4) => Equiv.Perm.sign σ = 1 ∧ σ k = k) := by
    intro σ hσ
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hσ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, g.2.2, hk g.1 g.2⟩
  have hcard_img : (Finset.univ.image (fun g : Geven => g.1)).card = 6 := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ, hcard_even]
  have := Finset.card_le_card hsub
  omega

/-- Classification of all subgroups of Perm (Fin 4) up to conjugacy. -/
private inductive Sub4Class (G : Subgroup (Perm (Fin 4))) : Prop
  | bot (h : G = ⊥)
  | top (h : G = ⊤)
  | swap01 (π : Perm (Fin 4)) (hcard : Nat.card G = 2)
      (h : ∀ σ ∈ G, π * σ * π⁻¹ = 1 ∨ π * σ * π⁻¹ = Equiv.swap 0 1)
  | swap01_23 (π : Perm (Fin 4)) (hcard : Nat.card G = 2)
      (h : ∀ σ ∈ G, π * σ * π⁻¹ = 1 ∨ π * σ * π⁻¹ = Equiv.swap 0 1 * Equiv.swap 2 3)
  | A3 (π : Perm (Fin 4)) (hcard : Nat.card G = 3)
      (h : ∀ σ ∈ G, π * σ * π⁻¹ = 1 ∨ π * σ * π⁻¹ = Equiv.swap 0 1 * Equiv.swap 1 2 ∨
        π * σ * π⁻¹ = (Equiv.swap 0 1 * Equiv.swap 1 2) * (Equiv.swap 0 1 * Equiv.swap 1 2))
  | K4_nonnormal (π : Perm (Fin 4)) (hcard : Nat.card G = 4)
      (h : ∀ σ ∈ G, π * σ * π⁻¹ = 1 ∨ π * σ * π⁻¹ = Equiv.swap 0 1 ∨
        π * σ * π⁻¹ = Equiv.swap 2 3 ∨ π * σ * π⁻¹ = Equiv.swap 0 1 * Equiv.swap 2 3)
  | V4 (hcard : Nat.card G = 4)
      (h : ∀ σ ∈ G, σ = 1 ∨ σ = Equiv.swap 0 1 * Equiv.swap 2 3 ∨
        σ = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ σ = Equiv.swap 0 3 * Equiv.swap 1 2)
  | C4 (π : Perm (Fin 4)) (hcard : Nat.card G = 4)
      (h : ∀ σ ∈ G, π * σ * π⁻¹ = 1 ∨
        π * σ * π⁻¹ = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 ∨
        π * σ * π⁻¹ = (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3) ^ 2 ∨
        π * σ * π⁻¹ = (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3) ^ 3)
  | S3 (π : Perm (Fin 4)) (hcard : Nat.card G = 6) (h : ∀ σ ∈ G, (π * σ * π⁻¹) 3 = 3)
  | D4 (π : Perm (Fin 4)) (hcard : Nat.card G = 8)
      (h : ∀ σ ∈ G,
        (((π * σ * π⁻¹) 0 = 0 ∨ (π * σ * π⁻¹) 0 = 2) ∧ ((π * σ * π⁻¹) 2 = 0 ∨ (π * σ * π⁻¹) 2 = 2)) ∨
        (((π * σ * π⁻¹) 0 = 1 ∨ (π * σ * π⁻¹) 0 = 3) ∧ ((π * σ * π⁻¹) 2 = 1 ∨ (π * σ * π⁻¹) 2 = 3)))
  | A4 (hcard : Nat.card G = 12) (h : ∀ σ ∈ G, Equiv.Perm.sign σ = 1)

private lemma subgroup_perm_fin4_cases (G : Subgroup (Perm (Fin 4))) : Sub4Class G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hdvd : Fintype.card G ∣ Fintype.card (Perm (Fin 4)) := by
    simpa [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card G
  have h24 : Fintype.card (Perm (Fin 4)) = 24 := by decide
  rw [h24] at hdvd
  have hpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨1⟩
  have hle24 : Fintype.card G ≤ 24 := Nat.le_of_dvd (by decide) hdvd
  have hcases : Fintype.card G = 1 ∨ Fintype.card G = 2 ∨ Fintype.card G = 3 ∨ Fintype.card G = 4 ∨
      Fintype.card G = 6 ∨ Fintype.card G = 8 ∨ Fintype.card G = 12 ∨ Fintype.card G = 24 := by
    interval_cases h : Fintype.card G <;> simp_all
  rcases hcases with h1 | h2 | h3 | h4 | h6 | h8 | h12 | h24'
  · exact Sub4Class.bot (by
      rw [eq_bot_iff]; intro σ hσ
      have hsub : Subsingleton G := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h1)
      exact congrArg Subtype.val (Subsingleton.elim (⟨σ, hσ⟩ : G) 1))
  · have hne : ∃ τ ∈ G, τ ≠ 1 := by
      by_contra hall; push Not at hall
      have hsub : Subsingleton G := ⟨fun a b => Subtype.ext ((hall a.1 a.2).trans (hall b.1 b.2).symm)⟩
      have := Fintype.card_le_one_iff_subsingleton.mpr hsub; omega
    obtain ⟨τ, hτG, hτne⟩ := hne
    have hall : ∀ σ ∈ G, σ = 1 ∨ σ = τ := by
      intro σ hσ; by_contra h; push Not at h
      have h3 : ({(1 : G), ⟨τ, hτG⟩, ⟨σ, hσ⟩} : Finset G).card = 3 :=
        Finset.card_eq_three.mpr ⟨1, ⟨τ, hτG⟩, ⟨σ, hσ⟩, fun e => hτne (congrArg Subtype.val e).symm,
          fun e => h.1 (congrArg Subtype.val e).symm, fun e => h.2 (congrArg Subtype.val e).symm, rfl⟩
      have := Finset.card_le_univ ({(1 : G), ⟨τ, hτG⟩, ⟨σ, hσ⟩} : Finset G); omega
    have hτsq : τ * τ = 1 := by
      rcases hall (τ * τ) (G.mul_mem hτG hτG) with h | h
      · exact h
      · exfalso; exact hτne (mul_left_cancel (a := τ) (by simpa using h))
    have hinv_list : ∀ x : Perm (Fin 4), x ≠ 1 → x * x = 1 →
        x = Equiv.swap 0 1 ∨ x = Equiv.swap 0 2 ∨ x = Equiv.swap 0 3 ∨
        x = Equiv.swap 1 2 ∨ x = Equiv.swap 1 3 ∨ x = Equiv.swap 2 3 ∨
        x = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ x = Equiv.swap 0 2 * Equiv.swap 1 3 ∨
        x = Equiv.swap 0 3 * Equiv.swap 1 2 := by decide
    have hconj2 : ∀ x : Perm (Fin 4), x ≠ 1 → x * x = 1 →
        (∃ π : Perm (Fin 4), π * x * π⁻¹ = Equiv.swap 0 1) ∨
        (∃ π : Perm (Fin 4), π * x * π⁻¹ = Equiv.swap 0 1 * Equiv.swap 2 3) := by
      intro x hx1 hx2
      rcases hinv_list x hx1 hx2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨1, by decide⟩
      · exact Or.inl ⟨Equiv.swap 1 2, by decide⟩
      · exact Or.inl ⟨Equiv.swap 1 3, by decide⟩
      · exact Or.inl ⟨Equiv.swap 0 2, by decide⟩
      · exact Or.inl ⟨Equiv.swap 0 3, by decide⟩
      · exact Or.inl ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide⟩
      · exact Or.inr ⟨1, by decide⟩
      · exact Or.inr ⟨Equiv.swap 1 2, by decide⟩
      · exact Or.inr ⟨Equiv.swap 1 3, by decide⟩
    rcases hconj2 τ hτne hτsq with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · exact Sub4Class.swap01 π (by rw [Nat.card_eq_fintype_card, h2]) (fun σ hσ => by
        rcases hall σ hσ with rfl | rfl
        · left; simp
        · right; exact hπ)
    · exact Sub4Class.swap01_23 π (by rw [Nat.card_eq_fintype_card, h2]) (fun σ hσ => by
        rcases hall σ hσ with rfl | rfl
        · left; simp
        · right; exact hπ)
  · have hne : ∃ τ ∈ G, τ ≠ 1 := by
      by_contra hall; push Not at hall
      have hsub : Subsingleton G := ⟨fun a b => Subtype.ext ((hall a.1 a.2).trans (hall b.1 b.2).symm)⟩
      have := Fintype.card_le_one_iff_subsingleton.mpr hsub; omega
    obtain ⟨τ, hτG, hτne⟩ := hne
    have hτ3 : τ ^ 3 = 1 := by
      have : (⟨τ, hτG⟩ : G) ^ Fintype.card G = 1 := pow_card_eq_one
      rw [h3] at this; exact congrArg Subtype.val this
    have hτ2 : τ * τ ≠ 1 := by
      intro h; have h1' : τ ^ 3 = τ := by rw [pow_succ, sq, h, one_mul]
      rw [hτ3] at h1'; exact hτne h1'.symm
    have hτ2ne : τ * τ ≠ τ := fun h => hτne (mul_left_cancel (a := τ) (by simpa using h))
    have hall : ∀ σ ∈ G, σ = 1 ∨ σ = τ ∨ σ = τ * τ := by
      intro σ hσ; by_contra h; push Not at h
      have h4 : ({(1 : G), ⟨τ, hτG⟩, ⟨τ * τ, G.mul_mem hτG hτG⟩, ⟨σ, hσ⟩} : Finset G).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton, Subtype.ext_iff]; exact h.2.2.symm
        · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, not_or]
          exact ⟨hτ2ne.symm, h.2.1.symm⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, not_or]
          exact ⟨hτne.symm, hτ2.symm, h.1.symm⟩
      have := Finset.card_le_univ ({(1 : G), ⟨τ, hτG⟩, ⟨τ * τ, G.mul_mem hτG hτG⟩, ⟨σ, hσ⟩} : Finset G); omega
    have hconj3 : ∀ x : Perm (Fin 4), x ≠ 1 → x ^ 3 = 1 →
        ∃ π : Perm (Fin 4), π * x * π⁻¹ = Equiv.swap 0 1 * Equiv.swap 1 2 := by decide
    obtain ⟨π, hπ⟩ := hconj3 τ hτne hτ3
    exact Sub4Class.A3 π (by rw [Nat.card_eq_fintype_card, h3]) (fun σ hσ => by
      rcases hall σ hσ with rfl | rfl | rfl
      · left; simp
      · right; left; exact hπ
      · right; right; rw [← hπ]; group)
  · -- |G| = 4: either cyclic C_4 or Klein 4 (V_4 or non-normal)
    by_cases hcyc : ∃ τ ∈ G, τ * τ ≠ 1
    · obtain ⟨τ, hτG, hτ2⟩ := hcyc
      have hτ4 : τ ^ 4 = 1 := by
        have : (⟨τ, hτG⟩ : G) ^ Fintype.card G = 1 := pow_card_eq_one
        rw [h4] at this; exact congrArg Subtype.val this
      have hconj4 : ∀ x : Perm (Fin 4), x * x ≠ 1 → x ^ 4 = 1 →
          ∃ π : Perm (Fin 4), π * x * π⁻¹ = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 := by
        intro x hx2 hx4
        have hsq_sq : (x * x) * (x * x) = 1 := by
          have : x ^ 4 = (x * x) * (x * x) := by rw [pow_succ, pow_succ, pow_succ, pow_one]; group
          exact this.symm.trans hx4
        have hsq_sign : Equiv.Perm.sign (x * x) = 1 := by
          rw [map_mul]; exact Units.ext (by
            rcases Int.units_eq_one_or (Equiv.Perm.sign x) with h | h <;> simp [h])
        have hsq_list : ∀ y : Perm (Fin 4), y ≠ 1 → y * y = 1 → Equiv.Perm.sign y = 1 →
            y = Equiv.swap 0 1 * Equiv.swap 2 3 ∨
            y = Equiv.swap 0 2 * Equiv.swap 1 3 ∨
            y = Equiv.swap 0 3 * Equiv.swap 1 2 := by decide
        have hsq1 : ∀ z : Perm (Fin 4), z * z = Equiv.swap 0 1 * Equiv.swap 2 3 →
            z = Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 3 ∨
            z = Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 1 2 := by decide
        have hsq2 : ∀ z : Perm (Fin 4), z * z = Equiv.swap 0 2 * Equiv.swap 1 3 →
            z = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 ∨
            z = Equiv.swap 0 3 * Equiv.swap 3 2 * Equiv.swap 2 1 := by decide
        have hsq3 : ∀ z : Perm (Fin 4), z * z = Equiv.swap 0 3 * Equiv.swap 1 2 →
            z = Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 2 ∨
            z = Equiv.swap 0 2 * Equiv.swap 2 3 * Equiv.swap 3 1 := by decide
        rcases hsq_list (x * x) hx2 hsq_sq hsq_sign with hy | hy | hy
        · rcases hsq1 x hy with rfl | rfl
          · exact ⟨Equiv.swap 1 2, by decide⟩
          · exact ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by decide⟩
        · rcases hsq2 x hy with rfl | rfl
          · exact ⟨1, by decide⟩
          · exact ⟨Equiv.swap 1 3, by decide⟩
        · rcases hsq3 x hy with rfl | rfl
          · exact ⟨Equiv.swap 2 3, by decide⟩
          · exact ⟨Equiv.swap 2 3 * Equiv.swap 1 2, by decide⟩
      obtain ⟨π, hπ⟩ := hconj4 τ hτ2 hτ4
      have hτne1 : τ ≠ 1 := fun h => hτ2 (by simp [h])
      have hτ3ne1 : τ ^ 3 ≠ 1 := by
        intro h; have : τ ^ 4 = τ := by rw [pow_succ, h, one_mul]
        rw [hτ4] at this; exact hτne1 this.symm
      have hτ3neτ : τ ^ 3 ≠ τ := by
        intro h; apply hτ2; have : τ * (τ * τ) = τ * 1 := by simpa [pow_succ, sq, mul_assoc] using h
        exact mul_left_cancel this
      have hτ3neτ2 : τ ^ 3 ≠ τ ^ 2 := by
        intro h; apply hτne1; have : τ ^ 2 * τ = τ ^ 2 * 1 := by simpa [pow_succ] using h
        exact mul_left_cancel this
      have hτ2neτ : τ ^ 2 ≠ τ := fun h => hτne1 (mul_left_cancel (a := τ) (by simpa [sq] using h))
      have hall : ∀ σ ∈ G, σ = 1 ∨ σ = τ ∨ σ = τ ^ 2 ∨ σ = τ ^ 3 := by
        intro σ hσ
        let S : Finset G := {1, ⟨τ, hτG⟩, ⟨τ ^ 2, G.pow_mem hτG 2⟩, ⟨τ ^ 3, G.pow_mem hτG 3⟩}
        have hS4 : S.card = 4 := by
          simp only [S]
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp only [Finset.mem_singleton, Subtype.ext_iff]; exact hτ3neτ2.symm
          · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, not_or]
            exact ⟨hτ2neτ.symm, hτ3neτ.symm⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, not_or]
            exact ⟨hτne1.symm, by simpa [sq] using hτ2.symm, hτ3ne1.symm⟩
        have hSu : S = Finset.univ := Finset.eq_univ_of_card S (by rw [hS4, h4])
        have hmem : (⟨σ, hσ⟩ : G) ∈ S := by rw [hSu]; exact Finset.mem_univ _
        simp only [S, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] at hmem
        exact hmem
      exact Sub4Class.C4 π (by rw [Nat.card_eq_fintype_card, h4]) (fun σ hσ => by
        rcases hall σ hσ with rfl | rfl | rfl | rfl
        · left; simp
        · right; left; exact hπ
        · right; right; left; rw [← hπ, sq, sq]; group
        · right; right; right; rw [← hπ, pow_succ, pow_succ, pow_one, pow_succ, pow_succ, pow_one]; group)
    · push Not at hcyc
      -- Every element of G has order dividing 2; pick two distinct non-identity elements a, b ∈ G
      have ha_ex : ∃ a ∈ G, a ≠ 1 := by
        by_contra h; push Not at h
        have hsub : Subsingleton G := ⟨fun x y => Subtype.ext ((h x.1 x.2).trans (h y.1 y.2).symm)⟩
        have := Fintype.card_le_one_iff_subsingleton.mpr hsub; omega
      obtain ⟨a, haG, hane1⟩ := ha_ex
      have hb_ex : ∃ b ∈ G, b ≠ 1 ∧ b ≠ a := by
        by_contra h; push Not at h
        have hsub : (Finset.univ : Finset G) ⊆ {1, ⟨a, haG⟩} := by
          intro x _
          by_cases hx1 : x.1 = 1
          · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext hx1))
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext (h x.1 x.2 hx1))))
        have := (Finset.card_le_card hsub).trans (Finset.card_le_two)
        rw [Finset.card_univ, h4] at this; omega
      obtain ⟨b, hbG, hbne1, hbnea⟩ := hb_ex
      have ha2 : a * a = 1 := hcyc a haG
      have hb2 : b * b = 1 := hcyc b hbG
      have hab2 : (a * b) * (a * b) = 1 := hcyc (a * b) (G.mul_mem haG hbG)
      have hab_ne1 : a * b ≠ 1 := by
        intro h; apply hbnea
        have : a * b = a * a := h.trans ha2.symm
        exact mul_left_cancel this
      have hab_nea : a * b ≠ a := fun h => hbne1 (mul_left_cancel (a := a) (by simpa using h))
      have hab_neb : a * b ≠ b := fun h => hane1 (mul_right_cancel (b := b) (by simpa using h))
      have hall : ∀ σ ∈ G, σ = 1 ∨ σ = a ∨ σ = b ∨ σ = a * b := by
        intro σ hσ
        let S : Finset G := {1, ⟨a, haG⟩, ⟨b, hbG⟩, ⟨a * b, G.mul_mem haG hbG⟩}
        have hS4 : S.card = 4 := by
          simp only [S]
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp only [Finset.mem_singleton, Subtype.ext_iff]; exact hab_neb.symm
          · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, not_or]
            exact ⟨hbnea.symm, hab_nea.symm⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, not_or]
            exact ⟨hane1.symm, hbne1.symm, hab_ne1.symm⟩
        have hSu : S = Finset.univ := Finset.eq_univ_of_card S (by rw [hS4, h4])
        have hmem : (⟨σ, hσ⟩ : G) ∈ S := by rw [hSu]; exact Finset.mem_univ _
        simp only [S, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] at hmem
        exact hmem
      have hinv_list : ∀ x : Perm (Fin 4), x ≠ 1 → x * x = 1 →
          x = Equiv.swap 0 1 ∨ x = Equiv.swap 0 2 ∨ x = Equiv.swap 0 3 ∨
          x = Equiv.swap 1 2 ∨ x = Equiv.swap 1 3 ∨ x = Equiv.swap 2 3 ∨
          x = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ x = Equiv.swap 0 2 * Equiv.swap 1 3 ∨
          x = Equiv.swap 0 3 * Equiv.swap 1 2 := by decide
      have hK4_class : ∀ x y : Perm (Fin 4), x ≠ 1 → y ≠ 1 → x ≠ y → x * x = 1 → y * y = 1 → (x * y) * (x * y) = 1 →
          ((x = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ x = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ x = Equiv.swap 0 3 * Equiv.swap 1 2) ∧
           (y = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ y = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ y = Equiv.swap 0 3 * Equiv.swap 1 2) ∧
           (x * y = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ x * y = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ x * y = Equiv.swap 0 3 * Equiv.swap 1 2)) ∨
          (∃ π : Perm (Fin 4),
            (π * x * π⁻¹ = Equiv.swap 0 1 ∨ π * x * π⁻¹ = Equiv.swap 2 3 ∨ π * x * π⁻¹ = Equiv.swap 0 1 * Equiv.swap 2 3) ∧
            (π * y * π⁻¹ = Equiv.swap 0 1 ∨ π * y * π⁻¹ = Equiv.swap 2 3 ∨ π * y * π⁻¹ = Equiv.swap 0 1 * Equiv.swap 2 3) ∧
            (π * (x * y) * π⁻¹ = Equiv.swap 0 1 ∨ π * (x * y) * π⁻¹ = Equiv.swap 2 3 ∨ π * (x * y) * π⁻¹ = Equiv.swap 0 1 * Equiv.swap 2 3)) := by
        intro x y hx1 hy1 hxy hx2 hy2 hxy2
        have hstep1 : ∀ v : Perm (Fin 4),
            v ≠ 1 → Equiv.swap (0 : Fin 4) 1 ≠ v → v * v = 1 →
            (Equiv.swap 0 1 * v) * (Equiv.swap 0 1 * v) = 1 →
            (v = Equiv.swap 0 1 ∨ v = Equiv.swap 2 3 ∨ v = Equiv.swap 0 1 * Equiv.swap 2 3) ∧
            (Equiv.swap 0 1 * v = Equiv.swap 0 1 ∨ Equiv.swap 0 1 * v = Equiv.swap 2 3 ∨
              Equiv.swap 0 1 * v = Equiv.swap 0 1 * Equiv.swap 2 3) := by decide
        have hstep2 : ∀ v : Perm (Fin 4),
            v ≠ 1 → Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 ≠ v → v * v = 1 →
            ((Equiv.swap 0 1 * Equiv.swap 2 3) * v) * ((Equiv.swap 0 1 * Equiv.swap 2 3) * v) = 1 →
            (v = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ v = Equiv.swap 0 3 * Equiv.swap 1 2) ∨
            ((v = Equiv.swap 0 1 ∨ v = Equiv.swap 2 3 ∨ v = Equiv.swap 0 1 * Equiv.swap 2 3) ∧
             ((Equiv.swap 0 1 * Equiv.swap 2 3) * v = Equiv.swap 0 1 ∨
              (Equiv.swap 0 1 * Equiv.swap 2 3) * v = Equiv.swap 2 3 ∨
              (Equiv.swap 0 1 * Equiv.swap 2 3) * v = Equiv.swap 0 1 * Equiv.swap 2 3)) := by decide
        have hconj_x : ∃ π : Perm (Fin 4),
            π * x * π⁻¹ = Equiv.swap 0 1 ∨ π * x * π⁻¹ = Equiv.swap 0 1 * Equiv.swap 2 3 := by
          rcases hinv_list x hx1 hx2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact ⟨1, Or.inl (by decide)⟩
          · exact ⟨Equiv.swap 1 2, Or.inl (by decide)⟩
          · exact ⟨Equiv.swap 1 3, Or.inl (by decide)⟩
          · exact ⟨Equiv.swap 0 2, Or.inl (by decide)⟩
          · exact ⟨Equiv.swap 0 3, Or.inl (by decide)⟩
          · exact ⟨Equiv.swap 0 2 * Equiv.swap 1 3, Or.inl (by decide)⟩
          · exact ⟨1, Or.inr (by decide)⟩
          · exact ⟨Equiv.swap 1 2, Or.inr (by decide)⟩
          · exact ⟨Equiv.swap 1 3, Or.inr (by decide)⟩
        obtain ⟨π, hπx⟩ := hconj_x
        set u := π * x * π⁻¹
        set v := π * y * π⁻¹
        have hv1 : v ≠ 1 := by
          intro h; apply hy1
          have := congrArg (fun z => π⁻¹ * z * π) h
          simpa [v, mul_assoc] using this
        have huv : u ≠ v := by intro h; apply hxy; exact mul_right_cancel (b := π⁻¹) (mul_left_cancel (a := π) h)
        have hv2 : v * v = 1 := by simp only [v]; rw [show π * y * π⁻¹ * (π * y * π⁻¹) = π * (y * y) * π⁻¹ from by group, hy2]; simp
        have huv2 : (u * v) * (u * v) = 1 := by
          have hmul : u * v = π * (x * y) * π⁻¹ := by simp only [u, v]; group
          rw [hmul, show π * (x * y) * π⁻¹ * (π * (x * y) * π⁻¹) = π * ((x * y) * (x * y)) * π⁻¹ from by group, hxy2]; simp
        rcases hπx with hu01 | hu0123
        · right
          have ⟨hvK, huvK⟩ := hstep1 v hv1 (hu01 ▸ huv) hv2 (hu01 ▸ huv2)
          refine ⟨π, Or.inl hu01, hvK, ?_⟩
          have hmul : π * (x * y) * π⁻¹ = u * v := by simp only [u, v]; group
          rw [hmul, hu01]; exact huvK
        · rcases hstep2 v hv1 (hu0123 ▸ huv) hv2 (hu0123 ▸ huv2) with hvV | ⟨hvK, huvK⟩
          · left
            have hnorm : ∀ p q : Perm (Fin 4),
                (q = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ q = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ q = Equiv.swap 0 3 * Equiv.swap 1 2) →
                (p⁻¹ * q * p = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ p⁻¹ * q * p = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ p⁻¹ * q * p = Equiv.swap 0 3 * Equiv.swap 1 2) := by
              intro p q hq
              have h1 : ∀ r : Perm (Fin 4), r⁻¹ * (Equiv.swap 0 1 * Equiv.swap 2 3) * r = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ r⁻¹ * (Equiv.swap 0 1 * Equiv.swap 2 3) * r = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ r⁻¹ * (Equiv.swap 0 1 * Equiv.swap 2 3) * r = Equiv.swap 0 3 * Equiv.swap 1 2 := by decide
              have h2 : ∀ r : Perm (Fin 4), r⁻¹ * (Equiv.swap 0 2 * Equiv.swap 1 3) * r = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ r⁻¹ * (Equiv.swap 0 2 * Equiv.swap 1 3) * r = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ r⁻¹ * (Equiv.swap 0 2 * Equiv.swap 1 3) * r = Equiv.swap 0 3 * Equiv.swap 1 2 := by decide
              have h3 : ∀ r : Perm (Fin 4), r⁻¹ * (Equiv.swap 0 3 * Equiv.swap 1 2) * r = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ r⁻¹ * (Equiv.swap 0 3 * Equiv.swap 1 2) * r = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ r⁻¹ * (Equiv.swap 0 3 * Equiv.swap 1 2) * r = Equiv.swap 0 3 * Equiv.swap 1 2 := by decide
              rcases hq with rfl | rfl | rfl; exact h1 p; exact h2 p; exact h3 p
            have hxV : x = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ x = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ x = Equiv.swap 0 3 * Equiv.swap 1 2 := by
              have := hnorm π u (Or.inl hu0123); simpa [u, mul_assoc] using this
            have hyV : y = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ y = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ y = Equiv.swap 0 3 * Equiv.swap 1 2 := by
              have := hnorm π v (Or.inr hvV); simpa [v, mul_assoc] using this
            have hxyV : x * y = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ x * y = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ x * y = Equiv.swap 0 3 * Equiv.swap 1 2 := by
              rcases hxV with rfl | rfl | rfl <;> rcases hyV with rfl | rfl | rfl <;> first | exact absurd rfl hxy | decide
            exact ⟨hxV, hyV, hxyV⟩
          · right
            refine ⟨π, Or.inr (Or.inr hu0123), hvK, ?_⟩
            have hmul : π * (x * y) * π⁻¹ = u * v := by simp only [u, v]; group
            rw [hmul, hu0123]; exact huvK
      rcases hK4_class a b hane1 hbne1 hbnea.symm ha2 hb2 hab2 with ⟨hx, hy, hxy⟩ | ⟨π, hx, hy, hxy⟩
      · exact Sub4Class.V4 (by rw [Nat.card_eq_fintype_card, h4]) (fun σ hσ => by
          rcases hall σ hσ with rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr hx
          · exact Or.inr hy
          · exact Or.inr hxy)
      · exact Sub4Class.K4_nonnormal π (by rw [Nat.card_eq_fintype_card, h4]) (fun σ hσ => by
          rcases hall σ hσ with rfl | rfl | rfl | rfl
          · left; simp
          · exact Or.inr hx
          · exact Or.inr hy
          · exact Or.inr hxy)
  · -- |G| = 6
    obtain ⟨k, hk⟩ := exists_fixed_of_card_six G h6
    refine Sub4Class.S3 (Equiv.swap k 3) (by rw [Nat.card_eq_fintype_card, h6]) (fun σ hσ => ?_)
    rw [Perm.mul_apply, Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_swap, Equiv.swap_apply_right, hk σ hσ, Equiv.swap_apply_left]
  · -- |G| = 8
    obtain ⟨π, hπ⟩ := exists_partition_of_card_eight G h8
    exact Sub4Class.D4 π (by rw [Nat.card_eq_fintype_card, h8]) hπ
  · -- |G| = 12
    exact Sub4Class.A4 (by rw [Nat.card_eq_fintype_card, h12]) (sign_eq_one_of_card_twelve G h12)
  · -- |G| = 24
    exact Sub4Class.top (by
      rw [eq_top_iff]; intro σ _
      have huniv : (Finset.univ.filter (fun x : Perm (Fin 4) => x ∈ G)) = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [← Fintype.card_subtype, h24', Fintype.card_perm]; decide
      have : σ ∈ Finset.univ.filter (fun x : Perm (Fin 4) => x ∈ G) := by rw [huniv]; exact Finset.mem_univ σ
      exact (Finset.mem_filter.mp this).2)

end OMA.Noether4

open OMA.Noether4 MvPolynomial NoetherProblem Equiv in
theorem OMA.solution : type_of% @NoetherProblem.noether_problem.variants.four := by
  intro K L ι _ _ _ _ _ hι e H hH
  classical
  -- Transport e : L ≃ₐ[K] FractionRing (MvPolynomial ι K) to e4 : L ≃ₐ[K] FR4 K
  let eqι : ι ≃ Fin 4 := Fintype.equivFinOfCardEq hι
  let renameFR : FractionRing (MvPolynomial ι K) ≃ₐ[K] FR4 K :=
    IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K eqι)
  let e4 : L ≃ₐ[K] FR4 K := e.trans renameFR
  let H4 : Subgroup (FR4 K ≃ₐ[K] FR4 K) := H.map (AlgEquiv.autCongr e4).toMonoidHom
  have hH4_perm : ∀ h ∈ H4, ∃ σ : Perm (Fin 4), h = permAut K σ := by
    rintro h ⟨g, hg, rfl⟩
    obtain ⟨σ₀, rfl⟩ := hH g hg
    refine ⟨eqι.symm.trans (σ₀.trans eqι), ?_⟩
    ext y
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A4 K) y
    simp only [e4, MulEquiv.coe_toMonoidHom, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
      AlgEquiv.symm_trans_apply, map_div₀]
    have hconj : ∀ (g : FractionRing (MvPolynomial ι K) ≃ₐ[K] FractionRing (MvPolynomial ι K))
        (z : FractionRing (MvPolynomial ι K)), e ((e.autCongr.symm g) (e.symm z)) = g z := by
      intro g z; change e (e.symm (g (e (e.symm z)))) = g z; simp
    rw [hconj, hconj]
    have hsymm : ∀ p : A4 K, renameFR.symm (algebraMap (A4 K) (FR4 K) p) =
        algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) (rename eqι.symm p) := by
      intro p
      apply renameFR.injective
      rw [AlgEquiv.apply_symm_apply]
      have h1 : renameFR (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) (rename eqι.symm p)) =
          algebraMap (A4 K) (FR4 K) ((MvPolynomial.renameEquiv K eqι) (rename eqι.symm p)) :=
        IsFractionRing.algEquivOfAlgEquiv_algebraMap (MvPolynomial.renameEquiv K eqι) (rename eqι.symm p)
      rw [h1]; congr 1
      change p = rename eqι (rename eqι.symm p)
      rw [rename_rename]; simp
    rw [hsymm a, hsymm b]
    simp only [renameFR, IsFractionRing.algEquivOfAlgEquiv_algebraMap, permAut_algebraMap]
    change algebraMap (A4 K) (FR4 K) (rename eqι (rename σ₀ (rename eqι.symm a))) /
      algebraMap (A4 K) (FR4 K) (rename eqι (rename σ₀ (rename eqι.symm b))) =
      algebraMap (A4 K) (FR4 K) (rename (eqι.symm.trans (σ₀.trans eqι)) a) /
      algebraMap (A4 K) (FR4 K) (rename (eqι.symm.trans (σ₀.trans eqι)) b)
    simp only [rename_rename]; rfl
  let G : Subgroup (Perm (Fin 4)) := H4.comap (permAutHom K)
  letI : Fintype G := Fintype.ofFinite G
  have heqv_fixed : IntermediateField.fixedField H ≃ₐ[K] IntermediateField.fixedField H4 :=
    { toFun := fun x => ⟨e4 x.1, by
        rw [IntermediateField.mem_fixedField_iff]
        rintro h ⟨g, hg, rfl⟩
        change e4 (g (e4.symm (e4 x.1))) = e4 x.1
        rw [AlgEquiv.symm_apply_apply, (IntermediateField.mem_fixedField_iff H x.1).mp x.2 g hg]⟩
      invFun := fun y => ⟨e4.symm y.1, by
        rw [IntermediateField.mem_fixedField_iff]
        intro g hg
        have hy := (IntermediateField.mem_fixedField_iff H4 y.1).mp y.2 (AlgEquiv.autCongr e4 g) ⟨g, hg, rfl⟩
        have h2 := congrArg e4.symm hy; simpa using h2⟩
      left_inv := fun x => Subtype.ext (e4.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e4.apply_symm_apply y.1)
      map_mul' := fun x y => Subtype.ext (map_mul e4 x.1 y.1)
      map_add' := fun x y => Subtype.ext (map_add e4 x.1 y.1)
      commutes' := fun k => Subtype.ext (e4.commutes k) }
  suffices hrat4 : IsRationalExtension K (IntermediateField.fixedField H4) (Fin 4) by
    obtain ⟨eF⟩ := hrat4.pure_transcendental
    exact ⟨Fin 4, ⟨⟨heqv_fixed.trans eF⟩⟩⟩
  -- Helper to conjugate H4 by permAut K π
  have hconj_step : ∀ (π : Perm (Fin 4)),
      let H4' : Subgroup (FR4 K ≃ₐ[K] FR4 K) := H4.map (AlgEquiv.autCongr (permAut K π)).toMonoidHom
      IsRationalExtension K (IntermediateField.fixedField H4') (Fin 4) →
      IsRationalExtension K (IntermediateField.fixedField H4) (Fin 4) := by
    intro π H4' hrat'
    obtain ⟨eF⟩ := hrat'.pure_transcendental
    let φ := permAut K π
    let heqv' : IntermediateField.fixedField H4 ≃ₐ[K] IntermediateField.fixedField H4' :=
      { toFun := fun x => ⟨φ x.1, by
          rw [IntermediateField.mem_fixedField_iff]
          rintro h ⟨g, hg, rfl⟩
          change φ (g (φ.symm (φ x.1))) = φ x.1
          rw [AlgEquiv.symm_apply_apply, (IntermediateField.mem_fixedField_iff H4 x.1).mp x.2 g hg]⟩
        invFun := fun y => ⟨φ.symm y.1, by
          rw [IntermediateField.mem_fixedField_iff]
          intro g hg
          have hy := (IntermediateField.mem_fixedField_iff H4' y.1).mp y.2 (AlgEquiv.autCongr φ g) ⟨g, hg, rfl⟩
          have h2 := congrArg φ.symm hy; simpa using h2⟩
        left_inv := fun x => Subtype.ext (φ.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (φ.apply_symm_apply y.1)
        map_mul' := fun x y => Subtype.ext (map_mul φ x.1 y.1)
        map_add' := fun x y => Subtype.ext (map_add φ x.1 y.1)
        commutes' := fun k => Subtype.ext (φ.commutes k) }
    exact ⟨⟨heqv'.trans eF⟩⟩
  have hconj_mem : ∀ (π : Perm (Fin 4)) (h : FR4 K ≃ₐ[K] FR4 K),
      h ∈ H4.map (AlgEquiv.autCongr (permAut K π)).toMonoidHom →
      ∃ σ ∈ G, h = permAut K (π * σ * π⁻¹) := by
    rintro π h ⟨g, hg, rfl⟩
    obtain ⟨σ, rfl⟩ := hH4_perm g hg
    refine ⟨σ, hg, ?_⟩
    change permAut K π * permAut K σ * (permAut K π)⁻¹ = permAut K (π * σ * π⁻¹)
    rw [show (permAut K π)⁻¹ = permAut K π⁻¹ from (map_inv (permAutHom K) π).symm, ← permAut_mul, ← permAut_mul]
  have hbij_conj : ∀ (π : Perm (Fin 4)),
      let H4' : Subgroup (FR4 K ≃ₐ[K] FR4 K) := H4.map (AlgEquiv.autCongr (permAut K π)).toMonoidHom
      Function.Bijective (fun x : G =>
        (⟨AlgEquiv.autCongr (permAut K π) (permAutHom K x.1), ⟨permAutHom K x.1, x.2, rfl⟩⟩ : H4')) := by
    intro π H4'
    constructor
    · intro a b hab
      exact Subtype.ext (permAutHom_injective K ((AlgEquiv.autCongr (permAut K π)).injective (congrArg Subtype.val hab)))
    · rintro ⟨h, g, hg, rfl⟩
      obtain ⟨σ, rfl⟩ := hH4_perm g hg
      exact ⟨⟨σ, hg⟩, rfl⟩
  have hbij_id : Function.Bijective (fun x : G => (⟨permAutHom K x.1, x.2⟩ : H4)) := by
    constructor
    · intro a b hab; exact Subtype.ext (permAutHom_injective K (congrArg Subtype.val hab))
    · rintro ⟨h, hh⟩; obtain ⟨σ, rfl⟩ := hH4_perm h hh; exact ⟨⟨σ, hh⟩, rfl⟩
  rcases subgroup_perm_fin4_cases G with hbot | htop | ⟨π, hcard, hsub⟩ | ⟨π, hcard, hsub⟩ |
    ⟨π, hcard, hsub⟩ | ⟨π, hcard, hsub⟩ | ⟨hcard, hsub⟩ | ⟨π, hcard, hsub⟩ |
    ⟨π, hcard, hsub⟩ | ⟨π, hcard, hsub⟩ | ⟨hcard, hsub⟩
  · -- |G| = 1
    have hH4_top : IntermediateField.fixedField H4 = ⊤ := by
      rw [eq_top_iff]; intro y _; rw [IntermediateField.mem_fixedField_iff]; intro h hh
      obtain ⟨σ, rfl⟩ := hH4_perm h hh
      have hσ1 : σ = 1 := by have : σ ∈ G := hh; rw [hbot] at this; exact this
      rw [hσ1, permAut_one]; rfl
    exact ⟨⟨(IntermediateField.equivOfEq hH4_top).trans IntermediateField.topEquiv⟩⟩
  · -- |G| = 24
    exact fixedField_full_symm H4 (fun σ => by change σ ∈ G; rw [htop]; trivial) hH4_perm
  · -- |G| = 2, swap 0 1
    apply hconj_step π
    let H4' := H4.map (AlgEquiv.autCongr (permAut K π)).toMonoidHom
    letI : Fintype H4' := Fintype.ofEquiv G (Equiv.ofBijective _ (hbij_conj π))
    refine fixedField_swap01 H4' (by rw [← Fintype.card_of_bijective (hbij_conj π), ← Nat.card_eq_fintype_card, hcard]) ?_
    intro h hh; obtain ⟨σ, hσG, rfl⟩ := hconj_mem π h hh
    rcases hsub σ hσG with h1 | h2
    · exact Or.inl (by rw [h1, permAut_one])
    · exact Or.inr (by rw [h2])
  · -- |G| = 2, (0 1)(2 3)
    apply hconj_step π
    let H4' := H4.map (AlgEquiv.autCongr (permAut K π)).toMonoidHom
    letI : Fintype H4' := Fintype.ofEquiv G (Equiv.ofBijective _ (hbij_conj π))
    refine fixedField_swap01_23 H4' (by rw [← Fintype.card_of_bijective (hbij_conj π), ← Nat.card_eq_fintype_card, hcard]) ?_
    intro h hh; obtain ⟨σ, hσG, rfl⟩ := hconj_mem π h hh
    rcases hsub σ hσG with h1 | h2
    · exact Or.inl (by rw [h1, permAut_one])
    · exact Or.inr (by rw [h2])
  · -- |G| = 3, A_3
    apply hconj_step π
    let H4' := H4.map (AlgEquiv.autCongr (permAut K π)).toMonoidHom
    letI : Fintype H4' := Fintype.ofEquiv G (Equiv.ofBijective _ (hbij_conj π))
    refine fixedField_A3 H4' (by rw [← Fintype.card_of_bijective (hbij_conj π), ← Nat.card_eq_fintype_card, hcard]) ?_
    intro h hh; obtain ⟨σ, hσG, rfl⟩ := hconj_mem π h hh
    rcases hsub σ hσG with h1 | h2 | h3
    · exact Or.inl (by rw [h1, permAut_one])
    · exact Or.inr (Or.inl (by rw [h2]))
    · exact Or.inr (Or.inr (by rw [h3]))
  · -- |G| = 4, K4 non-normal
    apply hconj_step π
    let H4' := H4.map (AlgEquiv.autCongr (permAut K π)).toMonoidHom
    letI : Fintype H4' := Fintype.ofEquiv G (Equiv.ofBijective _ (hbij_conj π))
    refine fixedField_K4_nonnormal H4' (by rw [← Fintype.card_of_bijective (hbij_conj π), ← Nat.card_eq_fintype_card, hcard]) ?_
    intro h hh; obtain ⟨σ, hσG, rfl⟩ := hconj_mem π h hh
    rcases hsub σ hσG with h1 | h2 | h3 | h4
    · exact Or.inl (by rw [h1, permAut_one])
    · exact Or.inr (Or.inl (by rw [h2]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h3])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h4])))
  · -- |G| = 4, V_4
    letI : Fintype H4 := Fintype.ofEquiv G (Equiv.ofBijective _ hbij_id)
    refine fixedField_V4 H4 (by rw [← Fintype.card_of_bijective hbij_id, ← Nat.card_eq_fintype_card, hcard]) ?_
    intro h hh; obtain ⟨σ, rfl⟩ := hH4_perm h hh
    rcases hsub σ hh with rfl | rfl | rfl | rfl
    · exact Or.inl permAut_one
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · -- |G| = 4, C_4
    apply hconj_step π
    let H4' := H4.map (AlgEquiv.autCongr (permAut K π)).toMonoidHom
    letI : Fintype H4' := Fintype.ofEquiv G (Equiv.ofBijective _ (hbij_conj π))
    refine fixedField_C4 H4' (by rw [← Fintype.card_of_bijective (hbij_conj π), ← Nat.card_eq_fintype_card, hcard]) ?_
    intro h hh; obtain ⟨σ, hσG, rfl⟩ := hconj_mem π h hh
    rcases hsub σ hσG with h1 | h2 | h3 | h4
    · exact Or.inl (by rw [h1, permAut_one])
    · exact Or.inr (Or.inl (by rw [h2]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h3])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h4])))
  · -- |G| = 6, S_3
    apply hconj_step π
    let H4' := H4.map (AlgEquiv.autCongr (permAut K π)).toMonoidHom
    letI : Fintype H4' := Fintype.ofEquiv G (Equiv.ofBijective _ (hbij_conj π))
    refine fixedField_S3_012 H4' (by rw [← Fintype.card_of_bijective (hbij_conj π), ← Nat.card_eq_fintype_card, hcard]) ?_
    intro h hh; obtain ⟨σ, hσG, rfl⟩ := hconj_mem π h hh
    exact ⟨π * σ * π⁻¹, hsub σ hσG, rfl⟩
  · -- |G| = 8, D_4
    apply hconj_step π
    let H4' := H4.map (AlgEquiv.autCongr (permAut K π)).toMonoidHom
    letI : Fintype H4' := Fintype.ofEquiv G (Equiv.ofBijective _ (hbij_conj π))
    refine fixedField_D4 H4' (by rw [← Fintype.card_of_bijective (hbij_conj π), ← Nat.card_eq_fintype_card, hcard]) ?_
    intro h hh; obtain ⟨σ, hσG, rfl⟩ := hconj_mem π h hh
    exact ⟨π * σ * π⁻¹, hsub σ hσG, rfl⟩
  · -- |G| = 12, A_4
    letI : Fintype H4 := Fintype.ofEquiv G (Equiv.ofBijective _ hbij_id)
    refine fixedField_A4 H4 (by rw [← Fintype.card_of_bijective hbij_id, ← Nat.card_eq_fintype_card, hcard]) ?_
    intro h hh; obtain ⟨σ, rfl⟩ := hH4_perm h hh
    exact ⟨σ, hsub σ hh, rfl⟩

