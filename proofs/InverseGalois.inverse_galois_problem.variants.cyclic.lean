import FormalConjectures.Wikipedia.InverseGalois

-- Problem: Inverse Galois problem — cyclic
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/InverseGalois.lean:61 (declaration InverseGalois.inverse_galois_problem.variants.cyclic)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

universe u

/-- A finite cyclic group has a normal subgroup of every index dividing its order. -/
lemma exists_normal_index (Γ : Type) [Group Γ] [Finite Γ] [IsCyclic Γ] (n : ℕ)
    (h : n ∣ Nat.card Γ) : ∃ H : Subgroup Γ, H.Normal ∧ H.index = n := by
  let _ : CommGroup Γ := IsCyclic.commGroup
  refine ⟨(powMonoidHom n : Γ →* Γ).range, inferInstance, ?_⟩
  rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right h]

/-- If `p` is a prime congruent to `1` modulo `|G|`, then the `p`-th cyclotomic extension `K` of
`ℚ` has cyclic Galois group of order `p - 1`, and the fixed field of its subgroup of index `|G|`
realizes the cyclic group `G`. -/
lemma realization_of_cyclotomic {G : Type u} [Finite G] [Group G] [IsCyclic G]
    (p : ℕ) (hp : p.Prime) (hmod : p ≡ 1 [MOD Nat.card G])
    (K : Type) [Field K] [Algebra ℚ K] [IsCyclotomicExtension {p} ℚ K] :
    Nonempty (InverseGalois.GaloisRealization ℚ G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have e : (K ≃ₐ[ℚ] K) ≃* (ZMod p)ˣ :=
    IsCyclotomicExtension.autEquivPow K (Polynomial.cyclotomic.irreducible_rat hp.pos)
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  have : FiniteDimensional ℚ K := IsCyclotomicExtension.finiteDimensional {p} ℚ K
  have : IsCyclic (K ≃ₐ[ℚ] K) := isCyclic_of_surjective e.symm e.symm.surjective
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = p - 1 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hp]
  have hdvd : Nat.card G ∣ Nat.card (K ≃ₐ[ℚ] K) := by
    rw [hcard]
    exact (Nat.modEq_iff_dvd' hp.one_le).mp hmod.symm
  obtain ⟨H, hH, hidx⟩ := exists_normal_index _ _ hdvd
  have : H.Normal := hH
  have e2 := IsGalois.normalAutEquivQuotient H
  have : IsCyclic ((K ≃ₐ[ℚ] K) ⧸ H) :=
    isCyclic_of_surjective (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  have e1 : G ≃* (K ≃ₐ[ℚ] K) ⧸ H :=
    mulEquivOfCyclicCardEq (by rw [← Subgroup.index_eq_card, hidx])
  exact ⟨⟨IntermediateField.fixedField H, inferInstance,
    (IntermediateField.fixedField H).algebra', inferInstance, e1.trans e2⟩⟩

end OMA

theorem OMA.solution : type_of% @InverseGalois.inverse_galois_problem.variants.cyclic := by
  intro G _ _ _
  have hn : Nat.card G ≠ 0 := Nat.card_pos.ne'
  obtain ⟨p, hp, -, hmod⟩ := Nat.exists_prime_gt_modEq_one 0 hn
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  have inst : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  exact ⟨OMA.realization_of_cyclotomic p hp hmod (CyclotomicField p ℚ)⟩
