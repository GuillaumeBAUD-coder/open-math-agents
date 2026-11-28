import OMAStatements.S_mo_98927

-- Problem mo-98927: the statement claims that in a finite group G, if the normal closures of x and y meet
-- trivially, then |<x>^G : <x>| * |<y>^G : <y>| = |<xy>^G : <xy>|.
-- Upstream: statements/mo-98927.lean (declaration OMA.S_mo_98927.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: let G = D3 x D3 (D3 the dihedral group of order 6, r a rotation of order 3, s a reflection),
-- x = (r, 1) and y = (1, r). Every conjugate of x is x or its inverse, so <x> is normal and equals its normal
-- closure; the same holds for y. The two closures lie in different factors, so they meet trivially, and the left
-- side is 1 * 1 = 1. But xy = (r, r), and its conjugate by (s, 1) is (r^-1, r), which is not a power of (r, r)
-- because its two coordinates differ. So <xy> is a proper subgroup of its normal closure and the right side is
-- not 1.

open Subgroup

private lemma normal_of_conj {G : Type} [Group G] (x : G)
    (hx : ∀ g : G, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹) : (Subgroup.zpowers x).Normal := by
  constructor
  intro n hn g
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  rw [← conj_zpow]
  rcases hx g with e | e
  · rw [e]
    exact zpow_mem (Subgroup.mem_zpowers x) k
  · rw [e]
    exact zpow_mem (inv_mem (Subgroup.mem_zpowers x)) k

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_98927.main) := by
  intro h
  obtain ⟨x, hx⟩ : ∃ x : DihedralGroup 3 × DihedralGroup 3, x = (DihedralGroup.r 1, 1) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : DihedralGroup 3 × DihedralGroup 3, y = (1, DihedralGroup.r 1) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : DihedralGroup 3 × DihedralGroup 3, t = (DihedralGroup.sr 0, 1) := ⟨_, rfl⟩
  have hxc : ∀ g, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹ := by
    subst hx
    decide
  have hyc : ∀ g, g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y⁻¹ := by
    subst hy
    decide
  have hx2 : x.2 = 1 := by
    subst hx
    rfl
  have hy1 : y.1 = 1 := by
    subst hy
    rfl
  have hxy : (x * y).1 = (x * y).2 := by
    subst hx hy
    decide
  have hbad : (t * (x * y) * t⁻¹).1 ≠ (t * (x * y) * t⁻¹).2 := by
    subst hx hy ht
    decide
  have hnx : (zpowers x).Normal := normal_of_conj x hxc
  have hny : (zpowers y).Normal := normal_of_conj y hyc
  have hcx : normalClosure {x} ≤ zpowers x :=
    normalClosure_le_normal (Set.singleton_subset_iff.mpr (mem_zpowers x))
  have hcy : normalClosure {y} ≤ zpowers y :=
    normalClosure_le_normal (Set.singleton_subset_iff.mpr (mem_zpowers y))
  have hkx : zpowers x ≤ (MonoidHom.snd (DihedralGroup 3) (DihedralGroup 3)).ker :=
    zpowers_le.mpr (MonoidHom.mem_ker.mpr hx2)
  have hky : zpowers y ≤ (MonoidHom.fst (DihedralGroup 3) (DihedralGroup 3)).ker :=
    zpowers_le.mpr (MonoidHom.mem_ker.mpr hy1)
  have hcond : normalClosure {x} ⊓ normalClosure {y} = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have e2 : g.2 = 1 := MonoidHom.mem_ker.mp (hkx (hcx hg.1))
    have e1 : g.1 = 1 := MonoidHom.mem_ker.mp (hky (hcy hg.2))
    rw [mem_bot]
    exact Prod.ext e1 e2
  have key := h _ x y hcond
  rw [relIndex_eq_one.mpr hcx, relIndex_eq_one.mpr hcy] at key
  have h3 : normalClosure {x * y} ≤ zpowers (x * y) := relIndex_eq_one.mp (by rw [← key])
  have hmem : t * (x * y) * t⁻¹ ∈ normalClosure {x * y} :=
    normalClosure_normal.conj_mem _ (subset_normalClosure (Set.mem_singleton _)) t
  have hle : zpowers (x * y) ≤
      (MonoidHom.fst (DihedralGroup 3) (DihedralGroup 3)).eqLocus (MonoidHom.snd _ _) :=
    zpowers_le.mpr hxy
  exact hbad (hle (h3 hmem))
