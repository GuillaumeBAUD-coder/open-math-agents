import FormalConjectures.Wikipedia.GromovPolynomialGrowth

-- Reduction GromovPolynomialGrowth.GromovPolynomialGrowthTheorem.R1 of Gromov's theorem on groups of polynomial growth
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Gromov's polynomial growth theorem: the two directions and a transfer lemma

The classical theorem is split along its standard proof; no new result is claimed.

* `H1` is Gromov's theorem proper (M. Gromov, *Groups of polynomial growth and expanding maps*,
  Publ. Math. IHES 53 (1981)): a finitely generated group of polynomial growth is virtually
  nilpotent.
* `H2` is the nilpotent case of the converse (J. A. Wolf, *Growth of finitely generated solvable
  groups and curvature of Riemannian manifolds*, J. Differential Geom. 2 (1968); the exact degree
  is the Bass–Guivarc'h formula): a finitely generated nilpotent group has polynomial growth.
* `H3` is the elementary transfer lemma: polynomial growth passes from a finite-index subgroup to
  the whole group (a finite-index subgroup is quasi-isometric to the group).

The hypotheses quantify over groups in `Type`. The assembly moves a finitely generated group
`G` of any universe to the isomorphic group `FreeGroup α ⧸ ker φ` in `Type`, where `φ` is a
surjection from a free group on a finite type, and transports polynomial growth and virtual
nilpotency along the isomorphism. Schreier's lemma (`Subgroup.fg_of_index_ne_zero` in Mathlib)
makes the finite-index nilpotent subgroup finitely generated.
-/

namespace OMA.R_GromovPolynomialGrowth_GromovPolynomialGrowthTheorem_R1

open GromovPolynomialGrowth

/-- Gromov (1981): a finitely generated group of polynomial growth is virtually nilpotent. -/
def H1 : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → HasPolynomialGrowth G → Group.IsVirtuallyNilpotent G

/-- Wolf (1968): a finitely generated nilpotent group has polynomial growth. -/
def H2 : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → Group.IsNilpotent G → HasPolynomialGrowth G

/-- Polynomial growth of a finite-index subgroup implies polynomial growth of the group. -/
def H3 : Prop :=
  ∀ (G : Type) [Group G] (H : Subgroup G), H.FiniteIndex → HasPolynomialGrowth H →
    HasPolynomialGrowth G

section transport

variable {G G' : Type*} [Group G] [Group G']

theorem mem_cayleyBall_map (e : G ≃* G') {S : Set G} {n : ℕ} {g : G}
    (hg : g ∈ CayleyBall S n) : e g ∈ CayleyBall (e '' S) n := by
  obtain ⟨l, hl, hS, rfl⟩ := hg
  refine ⟨l.map e, by simpa using hl, ?_, (map_list_prod e l).symm⟩
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
  rcases hS t ht with h | h
  · exact Or.inl ⟨t, h, rfl⟩
  · exact Or.inr ⟨t⁻¹, h, map_inv e t⟩

theorem cayleyBall_map (e : G ≃* G') (S : Set G) (n : ℕ) :
    CayleyBall (e '' S) n = e '' CayleyBall S n := by
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    have h := mem_cayleyBall_map e.symm hx
    have hS : (e.symm : G' → G) '' ((e : G → G') '' S) = S := by
      rw [Set.image_image]
      simp
    rwa [hS] at h
  · rintro ⟨g, hg, rfl⟩
    exact mem_cayleyBall_map e hg

theorem growthFunction_map (e : G ≃* G') (S : Set G) (n : ℕ) :
    GrowthFunction (e '' S) n = GrowthFunction S n := by
  unfold GrowthFunction
  rw [cayleyBall_map e S n]
  exact Set.ncard_image_of_injective _ e.injective

theorem hasPolynomialGrowth_map (e : G ≃* G') (h : HasPolynomialGrowth G) :
    HasPolynomialGrowth G' := by
  obtain ⟨S, hSf, hSc, C, d, hC, hbound⟩ := h
  refine ⟨e '' S, hSf.image _, ?_, C, d, hC, fun n hn => ?_⟩
  · have := MonoidHom.map_closure (e : G →* G') S
    rw [hSc, Subgroup.map_top_of_surjective _ e.surjective] at this
    exact this.symm
  · rw [growthFunction_map e S n]
    exact hbound n hn

theorem isVirtuallyNilpotent_map (e : G ≃* G') (h : Group.IsVirtuallyNilpotent G) :
    Group.IsVirtuallyNilpotent G' := by
  obtain ⟨N, hN, hNf⟩ := h
  refine ⟨N.map (e : G →* G'), ?_, ⟨?_⟩⟩
  · exact Group.nilpotent_of_mulEquiv
      (N.equivMapOfInjective (e : G →* G') e.injective)
  · rw [Subgroup.index_map_equiv]
    exact hNf.index_ne_zero

end transport

theorem main : H1 → H2 → H3 → type_of% @GromovPolynomialGrowth.GromovPolynomialGrowthTheorem := by
  intro h1 h2 h3 G _ hfg
  obtain ⟨α, _, φ, hφ⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.1 hfg
  let e : FreeGroup α ⧸ φ.ker ≃* G := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  haveI hQ : Group.FG (FreeGroup α ⧸ φ.ker) :=
    Group.fg_of_surjective (f := (e.symm : G →* FreeGroup α ⧸ φ.ker)) e.symm.surjective
  constructor
  · intro hG
    exact isVirtuallyNilpotent_map e (h1 _ hQ (hasPolynomialGrowth_map e.symm hG))
  · intro hG
    obtain ⟨N, hN, hNf⟩ := isVirtuallyNilpotent_map e.symm hG
    haveI := hNf
    have hNfg : Group.FG N := inferInstance
    exact hasPolynomialGrowth_map e (h3 _ N hNf (h2 _ hNfg hN))

end OMA.R_GromovPolynomialGrowth_GromovPolynomialGrowthTheorem_R1
