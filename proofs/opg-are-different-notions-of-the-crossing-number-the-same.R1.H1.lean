import OMAReductions.R_opg_are_different_notions_of_the_crossing_number_the_same_R1

/-!
# Proof of `opg-are-different-notions-of-the-crossing-number-the-same.R1.H1`

Proves the classical inequality `pcr G ≤ cr G` and the planar equivalence `pcr G = 0 → cr G = 0`
for every finite simple graph `G`.

For any drawing `D : Drawing G`, the projection `(e₁, e₂, x) ↦ (e₁, e₂)` maps `D.crossings`
onto `D.crossingPairs`. Hence for every admissible drawing (`D.crossings.Finite`),
`D.crossingPairs.ncard ≤ D.crossings.ncard`, yielding `pcr G ≤ cr G`. Moreover, `D.crossingPairs`
is symmetric with no diagonal elements (`e₁ ≠ e₂`), so any nonempty `D.crossingPairs` has
cardinality at least `2`. Thus `D.crossingPairs.ncard / 2 = 0` forces `D.crossingPairs = ∅`,
which forces `D.crossings = ∅`, giving `cr G = 0`.
-/

namespace OpgCrossingNumberR1H1Proof

open OMA.S_opg_are_different_notions_of_the_crossing_number_the_same

private lemma crossingPairs_eq_image {V : Type} [Fintype V] {G : SimpleGraph V}
    (D : Drawing G) :
    D.crossingPairs = (fun p : Sym2 V × Sym2 V × P => (p.1, p.2.1)) '' D.crossings := by
  ext ⟨e₁, e₂⟩
  simp only [Drawing.crossingPairs, Drawing.crossings, Set.mem_ofPred_eq, Set.mem_image,
    Set.Nonempty, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, hne, x, hx⟩
    exact ⟨e₁, e₂, x, ⟨h1, h2, hne, hx⟩, rfl, rfl⟩
  · rintro ⟨a, b, x, ⟨h1, h2, hne, hx⟩, rfl, rfl⟩
    exact ⟨h1, h2, hne, x, hx⟩

private lemma crossingPairs_ncard_le {V : Type} [Fintype V] {G : SimpleGraph V}
    {D : Drawing G} (hgood : D.Good) :
    D.crossingPairs.ncard ≤ D.crossings.ncard := by
  rw [crossingPairs_eq_image]
  exact Set.ncard_image_le hgood

private lemma crossings_empty_of_div_two_eq_zero {V : Type} [Fintype V] {G : SimpleGraph V}
    {D : Drawing G} (hgood : D.Good) (hzero : D.crossingPairs.ncard / 2 = 0) :
    D.crossings = ∅ := by
  have hfin : D.crossingPairs.Finite := by
    rw [crossingPairs_eq_image]
    exact hgood.image _
  have hpair_empty : D.crossingPairs = ∅ := by
    by_contra hne
    obtain ⟨⟨e₁, e₂⟩, hmem⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hsym : (e₂, e₁) ∈ D.crossingPairs := by
      rcases hmem with ⟨h1, h2, hneq, hnon⟩
      refine ⟨h2, h1, hneq.symm, ?_⟩
      rwa [Set.inter_comm]
    have hdistinct : (e₁, e₂) ≠ (e₂, e₁) := by
      intro heq
      have h12 : e₁ = e₂ := (Prod.mk.inj heq).1
      exact hmem.2.2.1 h12
    have hsub : ({(e₁, e₂), (e₂, e₁)} : Set (Sym2 V × Sym2 V)) ⊆ D.crossingPairs := by
      intro p hp
      rcases hp with rfl | rfl
      · exact hmem
      · exact hsym
    have hcard_pair : ({(e₁, e₂), (e₂, e₁)} : Set (Sym2 V × Sym2 V)).ncard = 2 :=
      Set.ncard_pair hdistinct
    have hle : 2 ≤ D.crossingPairs.ncard := by
      rw [← hcard_pair]
      exact Set.ncard_le_ncard hsub hfin
    omega
  by_contra hc_ne
  obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hc_ne
  have hmem : (p.1, p.2.1) ∈ D.crossingPairs := by
    rw [crossingPairs_eq_image]
    exact ⟨p, hp, rfl⟩
  rw [hpair_empty] at hmem
  exact hmem

end OpgCrossingNumberR1H1Proof

theorem OMA.solution : OMA.R_opg_are_different_notions_of_the_crossing_number_the_same_R1.H1 := by
  intro V _ G
  open OMA.S_opg_are_different_notions_of_the_crossing_number_the_same in
  let Scr : Set ℕ := {n | ∃ D : Drawing G, D.Good ∧ n = D.crossings.ncard / 2}
  let Spcr : Set ℕ := {n | ∃ D : Drawing G, D.Good ∧ n = D.crossingPairs.ncard / 2}
  constructor
  · by_cases hne : Scr.Nonempty
    · have hmem : cr G ∈ Scr := Nat.sInf_mem hne
      obtain ⟨D, hgood, hcr⟩ := hmem
      have hpcr_le : pcr G ≤ D.crossingPairs.ncard / 2 :=
        Nat.sInf_le ⟨D, hgood, rfl⟩
      have hdiv : D.crossingPairs.ncard / 2 ≤ D.crossings.ncard / 2 :=
        Nat.div_le_div_right (OpgCrossingNumberR1H1Proof.crossingPairs_ncard_le hgood)
      omega
    · have hcr0 : cr G = 0 := by
        change sInf Scr = 0
        rw [Set.not_nonempty_iff_eq_empty.mp hne]
        exact Nat.sInf_empty
      have hpcr_empty : Spcr = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨_, D, hgood, _⟩
        exact hne ⟨D.crossings.ncard / 2, D, hgood, rfl⟩
      have hpcr0 : pcr G = 0 := by
        change sInf Spcr = 0
        rw [hpcr_empty]
        exact Nat.sInf_empty
      omega
  · intro hpcr0
    by_cases hne : Spcr.Nonempty
    · have hmem : pcr G ∈ Spcr := Nat.sInf_mem hne
      rw [hpcr0] at hmem
      obtain ⟨D, hgood, hzero⟩ := hmem
      have hempty : D.crossings = ∅ :=
        OpgCrossingNumberR1H1Proof.crossings_empty_of_div_two_eq_zero hgood hzero.symm
      have h0mem : 0 ∈ Scr := ⟨D, hgood, by simp [hempty]⟩
      have hle : cr G ≤ 0 := Nat.sInf_le h0mem
      omega
    · change sInf Scr = 0
      have hcr_empty : Scr = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨_, D, hgood, _⟩
        exact hne ⟨D.crossingPairs.ncard / 2, D, hgood, rfl⟩
      rw [hcr_empty]
      exact Nat.sInf_empty
