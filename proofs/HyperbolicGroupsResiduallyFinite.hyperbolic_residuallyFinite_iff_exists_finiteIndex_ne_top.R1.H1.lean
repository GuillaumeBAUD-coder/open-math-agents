import OMAReductions.R_HyperbolicGroupsResiduallyFinite_hyperbolic_residuallyFinite_iff_exists_finiteIndex_ne_top_R1

/-! The easy implication: a nontrivial residually finite group has a proper subgroup of
finite index. A nontrivial element lies outside some normal subgroup of finite index, and
that subgroup is proper. -/

theorem OMA.solution :
    OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_residuallyFinite_iff_exists_finiteIndex_ne_top_R1.H1 := by
  intro hall G _ _ _
  have hrf : Group.ResiduallyFinite G := hall G
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have h := (Group.residuallyFinite_iff_forall_finiteIndexNormalSubgroup (G := G)).1 hrf g
  by_contra hcon
  apply hg
  apply h
  intro H
  have htop : H.toSubgroup = ⊤ := by
    by_contra hne
    exact hcon ⟨H.toSubgroup, hne, H.isFiniteIndex'⟩
  have hmem : g ∈ H.toSubgroup := by
    rw [htop]
    exact Subgroup.mem_top g
  exact hmem
