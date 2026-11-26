import FormalConjectures.Wikipedia.InverseGalois

-- Problem: Inverse Galois problem — abelian
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/InverseGalois.lean:70 (declaration InverseGalois.inverse_galois_problem.variants.abelian)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

universe u

/-- Any quotient of the Galois group of a finite Galois extension of `ℚ` is realizable. -/
lemma realization_of_surjective {G : Type u} [Group G]
    (K : Type) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (f : (K ≃ₐ[ℚ] K) →* G) (hf : Function.Surjective f) :
    Nonempty (InverseGalois.GaloisRealization ℚ G) := by
  have e1 : (K ≃ₐ[ℚ] K) ⧸ f.ker ≃* G := QuotientGroup.quotientKerEquivOfSurjective f hf
  have e2 := IsGalois.normalAutEquivQuotient f.ker
  exact ⟨⟨IntermediateField.fixedField f.ker, inferInstance,
    (IntermediateField.fixedField f.ker).algebra', inferInstance, e1.symm.trans e2⟩⟩

/-- A finite cyclic group surjects onto any cyclic group whose order divides its order. -/
lemma exists_surjective_of_cyclic (Γ : Type) [Group Γ] [Finite Γ] [IsCyclic Γ]
    (C : Type) [Group C] [IsCyclic C] (h : Nat.card C ∣ Nat.card Γ) :
    ∃ f : Γ →* C, Function.Surjective f := by
  let _ : CommGroup Γ := IsCyclic.commGroup
  let H : Subgroup Γ := (powMonoidHom (Nat.card C) : Γ →* Γ).range
  have hidx : H.index = Nat.card C := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right h]
  have : IsCyclic (Γ ⧸ H) :=
    isCyclic_of_surjective (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  have e1 : Γ ⧸ H ≃* C :=
    mulEquivOfCyclicCardEq (by rw [← Subgroup.index_eq_card, hidx])
  exact ⟨e1.toMonoidHom.comp (QuotientGroup.mk' H),
    e1.surjective.comp (QuotientGroup.mk'_surjective H)⟩

/-- Distinct primes in prescribed residue classes `1` mod `n i`. -/
lemma exists_primes {ι : Type} [DecidableEq ι] (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
    (s : Finset ι) :
    ∃ p : ι → ℕ, (∀ i, (p i).Prime ∧ p i ≡ 1 [MOD n i]) ∧ Set.InjOn p s := by
  induction s using Finset.induction_on with
  | empty =>
    choose p hp using fun i => Nat.exists_prime_gt_modEq_one 0 (hn i)
    exact ⟨p, fun i => ⟨(hp i).1, (hp i).2.2⟩, by simp⟩
  | insert a s ha ih =>
    obtain ⟨p, hp, hinj⟩ := ih
    obtain ⟨q, hq, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (∑ i ∈ s, p i) (hn a)
    refine ⟨Function.update p a q, fun i => ?_, ?_⟩
    · by_cases hi : i = a
      · subst hi
        simpa using ⟨hq, hmod⟩
      · simpa [Function.update_of_ne hi] using hp i
    · have hlt : ∀ i ∈ s, p i < q := fun i hi =>
        lt_of_le_of_lt (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi) hgt
      have hne : ∀ i ∈ s, i ≠ a := fun i hi h => ha (h ▸ hi)
      intro i hi j hj hij
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hi hj
      rcases hi with rfl | hi <;> rcases hj with rfl | hj
      · rfl
      · rw [Function.update_self, Function.update_of_ne (hne j hj)] at hij
        exact absurd hij (hlt j hj).ne'
      · rw [Function.update_self, Function.update_of_ne (hne i hi)] at hij
        exact absurd hij (hlt i hi).ne
      · rw [Function.update_of_ne (hne i hi), Function.update_of_ne (hne j hj)] at hij
        exact hinj hi hj hij

/-- A product of cyclic groups `ZMod (n i)` is a quotient of some `(ZMod N)ˣ` with `N ≠ 0`. -/
lemma exists_surjective_units {ι : Type} [Fintype ι] (n : ι → ℕ) (hn : ∀ i, n i ≠ 0) :
    ∃ (N : ℕ) (_ : N ≠ 0) (f : (ZMod N)ˣ →* ((i : ι) → Multiplicative (ZMod (n i)))),
      Function.Surjective f := by
  classical
  obtain ⟨p, hp, hinj⟩ := exists_primes n hn Finset.univ
  have hinj' : Function.Injective p := fun i j h => hinj (by simp) (by simp) h
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := fun i j hij =>
    (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hinj' h))
  have key : ∀ i, ∃ g : (ZMod (p i))ˣ →* Multiplicative (ZMod (n i)), Function.Surjective g := by
    intro i
    have : Fact (p i).Prime := ⟨(hp i).1⟩
    have : NeZero (n i) := ⟨hn i⟩
    have hcard : Nat.card (Multiplicative (ZMod (n i))) = n i := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    apply exists_surjective_of_cyclic
    rw [hcard, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (hp i).1]
    exact (Nat.modEq_iff_dvd' (hp i).1.one_le).mp (hp i).2.symm
  choose g hg using key
  let E : (ZMod (∏ i, p i))ˣ ≃* ((i : ι) → (ZMod (p i))ˣ) :=
    (Units.mapEquiv (ZMod.prodEquivPi p hcop).toMulEquiv).trans MulEquiv.piUnits
  refine ⟨∏ i, p i, Finset.prod_ne_zero_iff.mpr fun i _ => (hp i).1.ne_zero,
    (MonoidHom.piMap g).comp E.toMonoidHom, ?_⟩
  intro y
  choose x hx using fun i => hg i (y i)
  refine ⟨E.symm x, ?_⟩
  show MonoidHom.piMap g (E (E.symm x)) = y
  rw [E.apply_symm_apply]
  exact funext hx

end OMA

theorem OMA.solution : type_of% @InverseGalois.inverse_galois_problem.variants.abelian := by
  intro G _ _
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  obtain ⟨N, hN, f, hf⟩ := OMA.exists_surjective_units n (fun i => (hn i).ne_bot)
  have : NeZero N := ⟨hN⟩
  have : NeZero ((N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hN⟩
  have inst : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  have e0 : (CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) ≃* (ZMod N)ˣ :=
    IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ)
      (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hN))
  have : IsGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isGalois {N} ℚ _
  have : FiniteDimensional ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.finiteDimensional {N} ℚ _
  exact ⟨OMA.realization_of_surjective (CyclotomicField N ℚ)
    (e.symm.toMonoidHom.comp (f.comp e0.toMonoidHom))
    (e.symm.surjective.comp (hf.comp e0.surjective))⟩

