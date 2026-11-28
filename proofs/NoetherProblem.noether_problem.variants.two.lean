import FormalConjectures.Wikipedia.NoetherProblem

namespace OMA.Noether2

open MvPolynomial NoetherProblem Equiv

noncomputable abbrev ph (K : Type) {ι : Type} [Field K] (σ : Perm ι) :
    FractionRing (MvPolynomial ι K) ≃ₐ[K] FractionRing (MvPolynomial ι K) :=
  IsFractionRing.algEquivOfAlgEquiv (renameEquiv K σ)

variable {K L ι : Type} [Field K] [Field L] [Fintype ι] [Algebra K L]

lemma pa (σ : Perm ι) (a : MvPolynomial ι K) :
    ph K σ (algebraMap _ _ a) = algebraMap _ _ (rename σ a) := by
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

lemma p1 (y : FractionRing (MvPolynomial ι K)) : ph K (1 : Perm ι) y = y := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial ι K) y
  simp [rename_id]

lemma m (e : L ≃ₐ[K] FractionRing (MvPolynomial ι K)) (E : IntermediateField K L)
    (hE : ∀ x : L, x ∈ E ↔ ∀ σ : Perm ι, e.symm (ph K σ (e x)) = x) :
    IsRationalExtension K E (Fin (Fintype.card ι)) := by
  classical
  set P := MvPolynomial (Fin (Fintype.card ι)) K
  set A := MvPolynomial ι K
  set FR := FractionRing A
  let s := esymmAlgEquiv ι K rfl
  let f : P →+* L := (e.symm : FR →+* L).comp ((algebraMap A FR).comp
    ((symmetricSubalgebra ι K).val.toRingHom.comp (s : P →+* symmetricSubalgebra ι K)))
  have hf : ∀ p, f p = e.symm (algebraMap A FR (s p : A)) := fun _ => rfl
  have fmem : ∀ p, f p ∈ E := fun p => (hE _).2 fun σ => by
    rw [hf, AlgEquiv.apply_symm_apply, pa, (s p).2 σ]
  let g : P →+* E := f.codRestrict E fmem
  have ginj : Function.Injective g := fun p q h => s.injective (Subtype.ext
    (IsFractionRing.injective A FR (e.symm.injective (congrArg Subtype.val h))))
  letI : Algebra P E := g.toAlgebra
  have hg : ∀ p, (algebraMap P E p : L) = e.symm (algebraMap A FR (s p : A)) := fun _ => rfl
  haveI : FaithfulSMul P E := (faithfulSMul_iff_algebraMap_injective P E).2 ginj
  have hsurj : ∀ z : E, ∃ x y, z = algebraMap P E x / algebraMap P E y := fun z => by
    have hz : ∀ σ : Perm ι, ph K σ (e z) = e z := fun σ => e.symm_apply_eq.1 ((hE z).1 z.2 σ)
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := A) (e z)
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have haq : algebraMap A FR q ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A FR)).2 hq0
    set Q := ∏ σ : Perm ι, rename σ q with hQd
    obtain ⟨R, hR⟩ : q ∣ Q := by
      simpa [hQd, rename_id] using Finset.dvd_prod_of_mem (fun σ : Perm ι => rename σ q)
        (Finset.mem_univ (1 : Perm ι))
    have hQsym : Q.IsSymmetric := fun τ => by
      simp only [hQd, map_prod, rename_rename]
      exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => rfl
    have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ =>
      (map_ne_zero_iff _ (rename_injective _ σ.injective)).2 hq0
    have hkey : algebraMap A FR (p * R) = e z * algebraMap A FR Q := by
      rw [← hpq, hR, map_mul, map_mul, div_mul_eq_mul_div, eq_div_iff haq]
      ring
    have hPsym : (p * R).IsSymmetric := fun τ => IsFractionRing.injective A FR (by
      rw [← pa, hkey, map_mul, hz, pa, hQsym τ])
    refine ⟨s.symm ⟨p * R, hPsym⟩, s.symm ⟨Q, hQsym⟩, ?_⟩
    have hgy : algebraMap P E (s.symm ⟨Q, hQsym⟩) ≠ 0 :=
      (map_ne_zero_iff _ ginj).2 ((map_ne_zero_iff _ s.symm.injective).2 fun h =>
        hQ0 (congrArg Subtype.val h))
    rw [eq_div_iff hgy]
    exact Subtype.ext (e.injective (by simpa [hg] using hkey.symm))
  haveI : IsFractionRing P E := IsFractionRing.of_field P E hsurj
  haveI : IsScalarTower K P E := .of_algebraMap_eq fun k => Subtype.ext (by
    rw [hg, AlgEquiv.commutes]
    exact (e.symm.commutes k).symm.trans (congrArg e.symm (IsScalarTower.algebraMap_apply K A FR k)))
  exact ⟨⟨((IsLocalization.algEquiv (nonZeroDivisors P) (FractionRing P) E).restrictScalars K).symm⟩⟩

end OMA.Noether2

open OMA.Noether2 Equiv IntermediateField in
theorem OMA.solution : type_of% @NoetherProblem.noether_problem.variants.two := by
  intro K L ι _ _ _ _ _ hι e H hH
  classical
  by_cases htriv : ∀ h ∈ H, h = 1
  · obtain rfl : H = ⊥ := (Subgroup.eq_bot_iff_forall H).2 htriv
    exact ⟨ι, ⟨⟨((equivOfEq fixedField_bot).trans topEquiv).trans e⟩⟩⟩
  · push Not at htriv
    obtain ⟨h, hh, hne⟩ := htriv
    obtain ⟨σ, rfl⟩ := hH h hh
    have hσ : σ ≠ 1 := by
      rintro rfl
      exact hne (AlgEquiv.ext fun x => (congrArg e.symm (p1 _)).trans (e.symm_apply_apply x))
    have hall : ∀ τ : Perm ι, τ = 1 ∨ τ = σ := fun τ => by
      by_contra hc
      push Not at hc
      have := Fintype.two_lt_card_iff.2 ⟨1, σ, τ, hσ.symm, hc.1.symm, fun h => hc.2 h.symm⟩
      simp [Fintype.card_perm, hι] at this
    refine ⟨_, m e _ fun x => ?_⟩
    rw [mem_fixedField_iff]
    refine ⟨fun hx τ => ?_, fun hx h' hh' => ?_⟩
    · rcases hall τ with rfl | rfl
      · rw [p1, e.symm_apply_apply]
      · exact hx _ hh
    · obtain ⟨τ, rfl⟩ := hH h' hh'
      exact hx τ
