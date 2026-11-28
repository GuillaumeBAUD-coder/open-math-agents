import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1_H2_R1

-- Step Erdos1162.erdos_1162.variants.roney_dougal_tracey.R1.H2.R2.H2.R1.H2.R1.H2: hypothesis H2 of reduction Erdos1162.erdos_1162.variants.roney_dougal_tracey.R1.H2.R2.H2.R1.H2.R1
-- Credit: @yhay81
-- H2 := ∀ (G : Type) [Group G] [Finite G], ∀ M : Subgroup G,     Minimal (fun N : Subgroup G => N.Normal ∧ N ≠ ⊥) M →     ¬ Group.IsSolvable M →     ∃ (S : Type) (_ : Group S) (_ : Finite S) (_ : IsSimpleGroup S) (n : ℕ),       ¬ IsMulCommutative S ∧ Nonempty (M ≃* (Fin n → S))

/-!
Classification of nonsolvable minimal normal subgroups of a finite group as finite direct powers
of a nonabelian finite simple group.
-/

namespace OMA.Step_Erdos1162_H2

private lemma map_minimal_normal {M : Type} [Group M] {S : Subgroup M}
    (hS : Minimal (fun N : Subgroup M => N.Normal ∧ N ≠ ⊥) S) (φ : MulAut M) :
    Minimal (fun N : Subgroup M => N.Normal ∧ N ≠ ⊥) (S.map φ.toMonoidHom) := by
  have hnorm : (S.map φ.toMonoidHom).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rcases hx with ⟨a, ha, rfl⟩
    refine ⟨φ.symm y * a * (φ.symm y)⁻¹, hS.1.1.conj_mem a ha (φ.symm y), ?_⟩
    simp
  have hne : S.map φ.toMonoidHom ≠ ⊥ := by
    intro h
    apply hS.1.2
    rw [eq_bot_iff]
    intro a ha
    have h1 : φ a = 1 := Subgroup.mem_bot.mp (h ▸ ⟨a, ha, rfl⟩)
    exact Subgroup.mem_bot.mpr (φ.injective (by simpa using h1))
  refine ⟨⟨hnorm, hne⟩, fun N hN hNle => ?_⟩
  let N' : Subgroup M := N.comap φ.toMonoidHom
  have hN'norm : N'.Normal := hN.1.comap φ.toMonoidHom
  have hN'ne : N' ≠ ⊥ := by
    intro h
    apply hN.2
    rw [eq_bot_iff]
    intro x hx
    have h1 : φ.symm x ∈ N' := by
      change φ (φ.symm x) ∈ N
      simpa using hx
    have h2 : φ.symm x = 1 := Subgroup.mem_bot.mp (h ▸ h1)
    have h3 : x = 1 := by
      simpa using congrArg φ h2
    exact Subgroup.mem_bot.mpr h3
  have hN'le : N' ≤ S := by
    intro a ha
    have hfa : φ a ∈ S.map φ.toMonoidHom := hNle ha
    rcases hfa with ⟨b, hb, hba⟩
    exact (φ.injective hba) ▸ hb
  have hSle : S ≤ N' := hS.2 ⟨hN'norm, hN'ne⟩ hN'le
  rintro _ ⟨a, ha, rfl⟩
  exact hSle ha

private lemma normal_map_subtype_of_characteristic {G : Type} [Group G] {M : Subgroup G}
    [hMn : M.Normal] {K : Subgroup M} (hK : K.Characteristic) :
    (K.map M.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rcases hx with ⟨a, ha, rfl⟩
  let ψ : MulAut M :=
    { toFun := fun m => ⟨g * m.1 * g⁻¹, hMn.conj_mem m.1 m.2 g⟩
      invFun := fun m => ⟨g⁻¹ * m.1 * g, by simpa using hMn.conj_mem m.1 m.2 g⁻¹⟩
      left_inv := fun m => by ext; simp [mul_assoc]
      right_inv := fun m => by ext; simp [mul_assoc]
      map_mul' := fun m₁ m₂ => by ext; simp [mul_assoc] }
  have hmap : K.map ψ.toMonoidHom = K := (Subgroup.characteristic_iff_map_eq.mp hK) ψ
  have hmem : ψ a ∈ K := hmap ▸ ⟨a, ha, rfl⟩
  exact ⟨ψ a, hmem, rfl⟩

private lemma sSup_orbit_eq_top {G : Type} [Group G] {M : Subgroup G}
    (hM : Minimal (fun N : Subgroup G => N.Normal ∧ N ≠ ⊥) M)
    {S : Subgroup M} (hS : Minimal (fun N : Subgroup M => N.Normal ∧ N ≠ ⊥) S) :
    sSup (Set.range (fun φ : MulAut M => S.map φ.toMonoidHom)) = ⊤ := by
  let T : Set (Subgroup M) := Set.range (fun φ : MulAut M => S.map φ.toMonoidHom)
  have hchar : (sSup T).Characteristic := by
    rw [Subgroup.characteristic_iff_map_le]
    intro ψ
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le ?_
    rintro K ⟨φ, rfl⟩
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_map]
    refine le_sSup ⟨φ.trans ψ, ?_⟩
    rfl
  have hSmem : S ∈ T := ⟨MulEquiv.refl M, by simp⟩
  have hne : sSup T ≠ ⊥ := by
    intro h
    exact hS.1.2 (le_bot_iff.mp (h ▸ le_sSup hSmem))
  have : M.Normal := hM.1.1
  have hnormG : ((sSup T).map M.subtype).Normal := normal_map_subtype_of_characteristic hchar
  have hneG : (sSup T).map M.subtype ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro a ha
    have h1 : (a : G) = 1 := Subgroup.mem_bot.mp (h ▸ ⟨a, ha, rfl⟩)
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have hleM : (sSup T).map M.subtype ≤ M := Subgroup.map_subtype_le _
  have hMle : M ≤ (sSup T).map M.subtype := hM.2 ⟨hnormG, hneG⟩ hleM
  rw [eq_top_iff]
  intro a _
  rcases hMle a.2 with ⟨b, hb, hba⟩
  exact (Subtype.ext hba) ▸ hb

private lemma disjoint_of_ne_minimal {M : Type} [Group M] {K₁ K₂ : Subgroup M}
    (h₁ : Minimal (fun N : Subgroup M => N.Normal ∧ N ≠ ⊥) K₁)
    (h₂ : Minimal (fun N : Subgroup M => N.Normal ∧ N ≠ ⊥) K₂)
    (hne : K₁ ≠ K₂) : Disjoint K₁ K₂ := by
  rw [disjoint_iff]
  by_contra hbot
  have : K₁.Normal := h₁.1.1
  have : K₂.Normal := h₂.1.1
  have h12 : K₁ ≤ K₁ ⊓ K₂ := h₁.2 ⟨inferInstance, hbot⟩ inf_le_left
  have hle : K₁ ≤ K₂ := h12.trans inf_le_right
  have hge : K₂ ≤ K₁ := h₂.2 h₁.1 hle
  exact hne (le_antisymm hle hge)

private lemma commute_of_ne_minimal {M : Type} [Group M] {K₁ K₂ : Subgroup M}
    (h₁ : Minimal (fun N : Subgroup M => N.Normal ∧ N ≠ ⊥) K₁)
    (h₂ : Minimal (fun N : Subgroup M => N.Normal ∧ N ≠ ⊥) K₂)
    (hne : K₁ ≠ K₂) {x y : M} (hx : x ∈ K₁) (hy : y ∈ K₂) : Commute x y :=
  Subgroup.commute_of_normal_of_disjoint K₁ K₂ h₁.1.1 h₂.1.1
    (disjoint_of_ne_minimal h₁ h₂ hne) x y hx hy

private lemma isSimpleGroup_of_orbit_top {M : Type} [Group M] {S : Subgroup M}
    (hS : Minimal (fun N : Subgroup M => N.Normal ∧ N ≠ ⊥) S)
    (hT : sSup (Set.range (fun φ : MulAut M => S.map φ.toMonoidHom)) = ⊤) :
    IsSimpleGroup S := by
  have hnt : Nontrivial S := by
    have hex : ∃ x ∈ S, x ≠ 1 := by
      by_contra hall
      push Not at hall
      apply hS.1.2
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.mpr (hall x hx)
    rcases hex with ⟨x, hx, hx1⟩
    exact ⟨⟨⟨x, hx⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  refine ⟨fun N hN => ?_⟩
  let N' : Subgroup M := N.map S.subtype
  have hN'norm : N'.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hT]
    refine sSup_le ?_
    rintro K ⟨φ, rfl⟩ k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    by_cases hKS : S.map φ.toMonoidHom = S
    · have hkS : k ∈ S := hKS ▸ hk
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨⟨k, hkS⟩ * a * ⟨k, hkS⟩⁻¹, hN.conj_mem a ha ⟨k, hkS⟩, rfl⟩
      · rintro ⟨a, ha, hka⟩
        have h1 : x = (⟨k, hkS⟩⁻¹ * a * ⟨k, hkS⟩ : S).1 := by
          have h2 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
          rw [← hka] at h2
          simpa [mul_assoc] using h2.symm
        have hmem : ⟨k, hkS⟩⁻¹ * a * ⟨k, hkS⟩ ∈ N := by
          simpa using hN.conj_mem a ha (⟨k, hkS⟩⁻¹)
        exact ⟨⟨k, hkS⟩⁻¹ * a * ⟨k, hkS⟩, hmem, h1.symm⟩
    · have hKmin := map_minimal_normal hS φ
      have hcomm : ∀ y ∈ S, Commute k y := fun y hy =>
        commute_of_ne_minimal hKmin hS hKS hk hy
      constructor
      · rintro ⟨a, ha, rfl⟩
        simp only [Subgroup.coe_subtype]
        have hkx : k * a.1 * k⁻¹ = a.1 := by
          rw [(hcomm a.1 a.2).eq, mul_assoc, mul_inv_cancel, mul_one]
        rw [hkx]
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, hka⟩
        have hkx : x = a.1 := by
          have h1 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
          rw [← hka, Subgroup.coe_subtype] at h1
          have h2 : k⁻¹ * a.1 * k = a.1 := by
            have hc := (hcomm a.1 a.2).inv_left.eq
            rw [hc, mul_assoc, inv_mul_cancel, mul_one]
          rw [h2] at h1
          exact h1.symm
        rw [hkx]
        exact ⟨a, ha, rfl⟩
  by_cases hbot : N' = ⊥
  · left
    rw [eq_bot_iff]
    intro a ha
    have h1 : (a : M) = 1 := Subgroup.mem_bot.mp (hbot ▸ ⟨a, ha, rfl⟩)
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  · right
    have hSle : S ≤ N' := hS.2 ⟨hN'norm, hbot⟩ (Subgroup.map_subtype_le N)
    rw [eq_top_iff]
    intro a _
    rcases hSle a.2 with ⟨b, hb, hba⟩
    exact (Subtype.ext hba) ▸ hb

private lemma not_isMulCommutative_of_orbit_top {M : Type} [Group M] {S : Subgroup M}
    (hS : Minimal (fun N : Subgroup M => N.Normal ∧ N ≠ ⊥) S)
    (hT : sSup (Set.range (fun φ : MulAut M => S.map φ.toMonoidHom)) = ⊤)
    (hMs : ¬ Group.IsSolvable M) : ¬ IsMulCommutative S := by
  intro hcommS
  have hcenter : Subgroup.center M = ⊤ := by
    rw [eq_top_iff, ← hT]
    refine sSup_le ?_
    rintro K ⟨φ, rfl⟩ x hx
    rw [Subgroup.mem_center_iff]
    have hcent : Subgroup.centralizer ({x} : Set M) = ⊤ := by
      rw [eq_top_iff, ← hT]
      refine sSup_le ?_
      rintro K' ⟨ψ, rfl⟩ y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      by_cases hEq : S.map ψ.toMonoidHom = S.map φ.toMonoidHom
      · have hy' : y ∈ S.map φ.toMonoidHom := hEq ▸ hy
        have : IsMulCommutative (S.map φ.toMonoidHom) :=
          S.map_isMulCommutative φ.toMonoidHom
        exact setLike_mul_comm hx hy'
      · exact (commute_of_ne_minimal (map_minimal_normal hS φ)
          (map_minimal_normal hS ψ) (Ne.symm hEq) hx hy).eq
    intro g
    have hg : g ∈ Subgroup.centralizer ({x} : Set M) := hcent ▸ Subgroup.mem_top g
    exact ((Subgroup.mem_centralizer_iff.mp hg) x rfl).symm
  let _ : CommGroup M :=
    { ‹Group M› with
      mul_comm := fun a b =>
        (Subgroup.mem_center_iff.mp (hcenter ▸ Subgroup.mem_top b)) a }
  exact hMs inferInstance

private lemma center_eq_bot_of_simple_not_comm {S : Type} [Group S] [IsSimpleGroup S]
    (hnc : ¬ IsMulCommutative S) : Subgroup.center S = ⊥ := by
  rcases (inferInstance : (Subgroup.center S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a

end OMA.Step_Erdos1162_H2

theorem OMA.solution : OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1_H2_R1.H2 := by
  classical
  intro G _ _ M hM hMs
  have htopM : (⊤ : Subgroup M) ≠ ⊥ := by
    intro h
    exact hMs (Group.isSolvable_of_top_eq_bot M h)
  obtain ⟨S, hS⟩ := exists_minimal_of_wellFoundedLT
    (fun N : Subgroup M => N.Normal ∧ N ≠ ⊥) ⟨⊤, inferInstance, htopM⟩
  let T : Set (Subgroup M) := Set.range (fun φ : MulAut M => S.map φ.toMonoidHom)
  have hTtop : sSup T = ⊤ := OMA.Step_Erdos1162_H2.sSup_orbit_eq_top hM hS
  have hSimple : IsSimpleGroup S := OMA.Step_Erdos1162_H2.isSimpleGroup_of_orbit_top hS hTtop
  have hnc : ¬ IsMulCommutative S :=
    OMA.Step_Erdos1162_H2.not_isMulCommutative_of_orbit_top hS hTtop hMs
  let _ : Fintype T := Fintype.ofFinite T
  let n : ℕ := Fintype.card T
  let eIdx : Fin n ≃ T := (Fintype.equivFin T).symm
  let H : Fin n → Subgroup M := fun k => (eIdx k).1
  have hHinj : Function.Injective H := Subtype.val_injective.comp eIdx.injective
  let φ : Fin n → MulAut M := fun k => Classical.choose (eIdx k).2
  have hφ : ∀ k, S.map (φ k).toMonoidHom = H k := fun k => Classical.choose_spec (eIdx k).2
  have hHmin : ∀ k, Minimal (fun N : Subgroup M => N.Normal ∧ N ≠ ⊥) (H k) := fun k =>
    hφ k ▸ OMA.Step_Erdos1162_H2.map_minimal_normal hS (φ k)
  let f : Fin n → S →* M := fun k => (φ k).toMonoidHom.comp S.subtype
  have hrange : ∀ k, (f k).range = H k := by
    intro k
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hφ k]
  have hcomm : Pairwise fun i j : Fin n => ∀ x y : S, Commute (f i x) (f j y) := by
    intro i j hij x y
    have hxi : f i x ∈ H i := hrange i ▸ ⟨x, rfl⟩
    have hyj : f j y ∈ H j := hrange j ▸ ⟨y, rfl⟩
    exact OMA.Step_Erdos1162_H2.commute_of_ne_minimal (hHmin i) (hHmin j)
      (fun h => hij (hHinj h)) hxi hyj
  have hind : iSupIndep fun k => (f k).range := by
    intro i
    rw [disjoint_iff_inf_le]
    rintro x ⟨hxi, hxrest⟩
    have hxi' : x ∈ H i := (hrange i) ▸ hxi
    have hrest_le : (⨆ j ≠ i, (f j).range) ≤ Subgroup.centralizer (H i : Set M) := by
      refine iSup₂_le ?_
      intro j hji y hy
      have hy' : y ∈ H j := (hrange j) ▸ hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (OMA.Step_Erdos1162_H2.commute_of_ne_minimal (hHmin i) (hHmin j)
        (fun h => hji (hHinj h.symm)) hz hy').eq
    have hxcent : x ∈ Subgroup.centralizer (H i : Set M) := hrest_le hxrest
    let eHi : S ≃* H i :=
      ((φ i).subgroupMap S).trans (MulEquiv.subgroupCongr (hφ i))
    have : IsSimpleGroup (H i) := eHi.symm.isSimpleGroup
    have hncHi : ¬ IsMulCommutative (H i) := by
      intro hci
      apply hnc
      refine ⟨⟨fun a b => ?_⟩⟩
      apply eHi.injective
      rw [map_mul, map_mul]
      exact mul_comm' (eHi a) (eHi b)
    have hmemC : (⟨x, hxi'⟩ : H i) ∈ Subgroup.center (H i) := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxcent) z.1 z.2)
    have hbotC : Subgroup.center (H i) = ⊥ :=
      OMA.Step_Erdos1162_H2.center_eq_bot_of_simple_not_comm hncHi
    have h1 : (⟨x, hxi'⟩ : H i) = 1 := Subgroup.mem_bot.mp (hbotC ▸ hmemC)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  have hinj_f : ∀ k, Function.Injective (f k) := fun k =>
    (φ k).injective.comp S.subtype_injective
  let Φ : (Fin n → S) →* M := MonoidHom.noncommPiCoprod f hcomm
  have hΦinj : Function.Injective Φ :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep f hind hinj_f
  have hΦsurj : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top, MonoidHom.noncommPiCoprod_range]
    rw [eq_top_iff, ← hTtop]
    refine sSup_le ?_
    intro K hK
    have hk : H (eIdx.symm ⟨K, hK⟩) = K := by simp [H]
    rw [← hk, ← hrange (eIdx.symm ⟨K, hK⟩)]
    exact le_iSup (fun k => (f k).range) (eIdx.symm ⟨K, hK⟩)
  let e : M ≃* (Fin n → S) := (MulEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩).symm
  exact ⟨S, inferInstance, inferInstance, hSimple, n, hnc, ⟨e⟩⟩
