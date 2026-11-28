import OMAStatements.S_mo_361305

-- Problem: Does the compact-open topology retain topological groups?
-- Upstream: formal-conjectures statements/mo-361305.lean:0 (declaration OMA.S_mo_361305.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Topology Set

theorem OMA.solution : type_of% @OMA.S_mo_361305.main := by
  intro X Y _ _ _ _
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · rw [continuous_iff_continuousAt]
    rintro ⟨f, g⟩
    rw [ContinuousAt, ContinuousMap.tendsto_nhds_compactOpen]
    intro K hK U hU hKU
    refine hK.induction_on
      (p := fun S => ∀ᶠ q : C(X, Y) × C(X, Y) in 𝓝 (f, g), MapsTo (⇑(q.1 * q.2)) S U)
      ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun q => mapsTo_empty _ _
    · intro s t hst ht
      exact ht.mono fun q hq => hq.mono_left hst
    · intro s t hs ht
      exact (hs.and ht).mono fun q hq x hx => hx.elim (fun h => hq.1 h) (fun h => hq.2 h)
    · intro x hx
      have hxU : (f x, g x) ∈ (fun p : Y × Y => p.1 * p.2) ⁻¹' U := by
        have := hKU hx
        simpa using this
      obtain ⟨V, W, hVo, hWo, hxV, hxW, hVW⟩ :=
        isOpen_prod_iff.1 (hU.preimage continuous_mul) (f x) (g x) hxU
      obtain ⟨V', hV'n, hV'c, hV'V⟩ := exists_mem_nhds_isClosed_subset (hVo.mem_nhds hxV)
      obtain ⟨W', hW'n, hW'c, hW'W⟩ := exists_mem_nhds_isClosed_subset (hWo.mem_nhds hxW)
      refine ⟨K ∩ (f ⁻¹' V' ∩ g ⁻¹' W'), inter_mem_nhdsWithin K (inter_mem
        (f.continuous.continuousAt.preimage_mem_nhds hV'n)
        (g.continuous.continuousAt.preimage_mem_nhds hW'n)), ?_⟩
      have htc : IsCompact (K ∩ (f ⁻¹' V' ∩ g ⁻¹' W')) :=
        hK.inter_right ((hV'c.preimage f.continuous).inter (hW'c.preimage g.continuous))
      have hf : MapsTo f (K ∩ (f ⁻¹' V' ∩ g ⁻¹' W')) V := fun y hy => hV'V hy.2.1
      have hg : MapsTo g (K ∩ (f ⁻¹' V' ∩ g ⁻¹' W')) W := fun y hy => hW'W hy.2.2
      exact ((ContinuousMap.eventually_mapsTo htc hVo hf).prod_nhds
        (ContinuousMap.eventually_mapsTo htc hWo hg)).mono fun q hq y hy => by
          have := hVW (Set.mk_mem_prod (hq.1 hy) (hq.2 hy))
          simpa using this
  · have h := ContinuousMap.continuous_postcomp (X := X)
      (⟨fun y : Y => y⁻¹, continuous_inv⟩ : C(Y, Y))
    exact h.congr fun f => by ext x; rfl
