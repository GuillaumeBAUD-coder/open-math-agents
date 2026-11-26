import FormalConjectures.Wikipedia.InverseGalois

-- Problem: Inverse Galois problem — cyclic
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/InverseGalois.lean (declaration InverseGalois.inverse_galois_problem.variants.cyclic)
-- Credit: @niclorusso (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Every finite cyclic group `G` of order `n` is a Galois group over `ℚ`.

Take a prime `p ≡ 1 [MOD n]`. The Galois group of the `p`-th cyclotomic field is
`(ZMod p)ˣ`, cyclic of order `p - 1`, so it surjects onto `G` (both are `ZMod` of their order,
and `n ∣ p - 1`). The fixed field of the kernel is Galois over `ℚ` with Galois group `G`.
-/

namespace OMA.InverseGaloisCyclic

open Polynomial IntermediateField

/-- If the Galois group of a finite Galois extension of `ℚ` surjects onto `G`, then `G` is
realizable over `ℚ`: take the fixed field of the kernel. -/
lemma realizable_of_surjective {L : Type} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] {G : Type*} [Group G] (f : Gal(L/ℚ) →* G) (hf : Function.Surjective f) :
    InverseGalois.IsRealizable ℚ G :=
  ⟨⟨{ L := fixedField f.ker
      to_field := (fixedField f.ker).toField
      to_algebra := (fixedField f.ker).algebra'
      to_isGalois := IsGalois.of_fixedField_normal_subgroup f.ker
      iso := (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
        (IsGalois.normalAutEquivQuotient f.ker) }⟩⟩

/-- A cyclic group surjects onto any cyclic group whose order divides its order. -/
lemma exists_surjective_of_dvd {H G : Type*} [Group H] [Group G] (hH : IsCyclic H)
    (hG : IsCyclic G) (h : Nat.card G ∣ Nat.card H) :
    ∃ f : H →* G, Function.Surjective f := by
  let eH := zmodCyclicMulEquiv hH
  let eG := zmodCyclicMulEquiv hG
  let c : Multiplicative (ZMod (Nat.card H)) →* Multiplicative (ZMod (Nat.card G)) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom h (ZMod (Nat.card G))).toAddMonoidHom
  have hc : Function.Surjective c := by
    intro y
    obtain ⟨x, hx⟩ := ZMod.castHom_surjective h (Multiplicative.toAdd y)
    exact ⟨Multiplicative.ofAdd x, by simp [c, hx]⟩
  refine ⟨eG.toMonoidHom.comp (c.comp eH.symm.toMonoidHom), ?_⟩
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact eG.surjective.comp (hc.comp eH.symm.surjective)

end OMA.InverseGaloisCyclic

open Polynomial OMA.InverseGaloisCyclic in
theorem OMA.solution : type_of% @InverseGalois.inverse_galois_problem.variants.cyclic := by
  intro G _ _ hG
  obtain ⟨p, hp, -, hpn⟩ := Nat.exists_prime_gt_modEq_one 0 (Nat.card_pos (α := G)).ne'
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p : ℚ) := ⟨Nat.cast_ne_zero.2 hp.ne_zero⟩
  have : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  have : FiniteDimensional ℚ (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.finiteDimensional {p} ℚ (CyclotomicField p ℚ)
  have : IsGalois ℚ (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.isGalois {p} ℚ (CyclotomicField p ℚ)
  let e : Gal(CyclotomicField p ℚ/ℚ) ≃* (ZMod p)ˣ :=
    IsCyclotomicExtension.autEquivPow (CyclotomicField p ℚ) (cyclotomic.irreducible_rat hp.pos)
  have hU : IsCyclic (ZMod p)ˣ := inferInstance
  have hcard : Nat.card G ∣ Nat.card (ZMod p)ˣ := by
    rw [Nat.card_eq_fintype_card (α := (ZMod p)ˣ), ZMod.card_units p]
    exact (Nat.modEq_iff_dvd' hp.one_le).1 hpn.symm
  obtain ⟨f, hf⟩ := exists_surjective_of_dvd hU hG hcard
  exact realizable_of_surjective (f.comp e.toMonoidHom) (by
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact hf.comp e.surjective)
