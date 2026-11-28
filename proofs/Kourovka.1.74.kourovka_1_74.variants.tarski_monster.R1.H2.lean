import OMAReductions.R_Kourovka_1_74_kourovka_1_74_variants_tarski_monster_R1

-- Step Kourovka.1.74.kourovka_1_74.variants.tarski_monster.R1.H2: hypothesis H2 of reduction Kourovka.1.74.kourovka_1_74.variants.tarski_monster.R1
-- Credit: @harshb16

open scoped Pointwise

theorem OMA.solution : OMA.R_Kourovka_1_74_kourovka_1_74_variants_tarski_monster_R1.H2 := by
  intro G _ 𝓕 h1 hmul hinv hconj hpure hne
  let B : GroupFilterBasis G :=
    { sets := 𝓕.sets
      nonempty := ⟨Set.univ, Filter.univ_mem⟩
      inter_sets := fun {U V} hU hV => ⟨U ∩ V, Filter.inter_mem hU hV, subset_rfl⟩
      one' := fun {U} hU => h1 U hU
      mul' := fun {U} hU => by
        obtain ⟨V, hV, hVU⟩ := hmul U hU
        refine ⟨V, hV, ?_⟩
        rintro _ ⟨x, hx, y, hy, rfl⟩
        exact hVU x hx y hy
      inv' := fun {U} hU => ⟨_, hinv U hU, fun x hx => hx⟩
      conj' := fun g {U} hU => ⟨_, hconj g U hU, fun x hx => hx⟩ }
  let _t : TopologicalSpace G := B.topology
  have hTG : IsTopologicalGroup G := B.isTopologicalGroup
  have hn : nhds (1 : G) = 𝓕 := by
    rw [B.nhds_one_eq]
    ext U
    rw [FilterBasis.mem_filter_iff]
    exact ⟨fun ⟨V, hV, hVU⟩ => Filter.mem_of_superset hV hVU, fun h => ⟨U, h, subset_rfl⟩⟩
  refine ⟨B.topology, hTG, ?_, ?_⟩
  · intro hd
    apply hpure
    rw [← hn, nhds_discrete]
  · obtain ⟨U, hU, hUne⟩ := hne
    have hUn : U ∈ nhds (1 : G) := hn ▸ hU
    refine ⟨interior U, isOpen_interior, ⟨1, mem_interior_iff_mem_nhds.mpr hUn⟩, ?_⟩
    intro h
    apply hUne
    exact Set.eq_univ_of_univ_subset (h ▸ interior_subset)
