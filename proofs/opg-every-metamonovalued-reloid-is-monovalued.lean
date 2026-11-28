import OMAStatements.S_opg_every_metamonovalued_reloid_is_monovalued

-- Credit: @YlliBala
open Filter OMA.S_opg_every_metamonovalued_reloid_is_monovalued

private theorem rel_mono {A B C : Type} {F F' : Set (A × B)} {G G' : Set (B × C)}
    (hF : F ⊆ F') (hG : G ⊆ G') : relComp F G ⊆ relComp F' G' := by
  rintro p ⟨b, hb, hb'⟩
  exact ⟨b, hF hb, hG hb'⟩

private theorem comp_basis {A B C : Type} (f : Filter (A × B)) (g : Filter (B × C))
    (T : Set (A × C)) : T ∈ comp g f ↔ ∃ F ∈ f, ∃ G ∈ g, relComp F G ⊆ T := by
  change T ∈ f.lift (fun F => g.lift fun G => 𝓟 (relComp F G)) ↔ _
  have mG (F : Set (A × B)) : Monotone (fun G : Set (B × C) => 𝓟 (relComp F G)) := by
    intro _ _ h
    exact principal_mono.mpr (rel_mono (fun _ hx => hx) h)
  have mF : Monotone (fun F : Set (A × B) => g.lift fun G => 𝓟 (relComp F G)) := by
    intro _ _ h
    exact lift_mono le_rfl fun G => principal_mono.mpr (rel_mono h (fun _ hx => hx))
  rw [mem_lift_sets mF]
  simp only [mem_lift_sets (mG _), mem_principal]

theorem OMA.solution : type_of% @OMA.S_opg_every_metamonovalued_reloid_is_monovalued.main := by
  intro A B f hf
  let D : Set (B × B) := {p | p.1 = p.2}
  have he := hf B {𝓟 D, 𝓟 Dᶜ}
  have hb : comp (⊥ : Filter (B × B)) f = ⊥ := by
    apply empty_mem_iff_bot.mp
    apply (comp_basis _ _ _).2
    exact ⟨Set.univ, univ_mem, ∅, by simp, by simp [relComp]⟩
  have hd : Disjoint (comp (𝓟 D) f) (comp (𝓟 Dᶜ) f) := by
    apply disjoint_iff.mpr
    apply bot_unique
    calc
      _ ≤ ⨅ g ∈ ({𝓟 D, 𝓟 Dᶜ} : Set (Filter (B × B))), comp g f := by
        apply le_iInf₂
        intro g hg
        rcases Set.mem_insert_iff.mp hg with rfl | hg
        · exact inf_le_left
        · rw [Set.mem_singleton_iff.mp hg]
          exact inf_le_right
      _ = _ := he.symm
      _ = ⊥ := by simp [inf_principal, hb]
  obtain ⟨U, hU, V, hV, hdUV⟩ := Filter.disjoint_iff.mp hd
  obtain ⟨F, hF, R, hR, hFU⟩ := (comp_basis _ _ _).mp hU
  obtain ⟨G, hG, S, hS, hGV⟩ := (comp_basis _ _ _).mp hV
  let H := F ∩ G
  have hH : H ∈ f := inter_mem hF hG
  apply le_principal_iff.mpr
  apply (comp_basis _ _ _).2
  refine ⟨Prod.swap ⁻¹' H, ?_, H, hH, ?_⟩
  · change Prod.swap ⁻¹' (Prod.swap ⁻¹' H) ∈ f
    exact hH
  · rintro ⟨b,c⟩ ⟨a, hab, hac⟩
    change b = c
    by_contra hbc
    apply (Set.disjoint_left.mp hdUV) (a := (a,c))
    · exact hFU ⟨c, hac.1, hR (show (c,c) ∈ D from rfl)⟩
    · exact hGV ⟨b, hab.2, hS (show (b,c) ∈ Dᶜ from hbc)⟩
