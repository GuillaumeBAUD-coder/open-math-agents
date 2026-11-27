import FormalConjectures.Mathoverflow.«235893»

/-!
Gro-Tsen's MathOverflow 260589 theorem on connected bijections.
We choose one matched pair for each interval and each possible open separation.
-/

open Set Function Cardinal TopologicalSpace
open scoped Cardinal EuclideanGeometry

namespace OMA

private theorem fresh {α β : Type} (s : Set β) (g : α → β)
    (h : #α < #s) : ∃ x ∈ s, x ∉ range g := by
  by_contra! hn
  exact h.not_ge ((mk_le_mk_of_subset hn).trans mk_range_le)

private theorem representatives {ι β : Type} (S : ι → Set β) (h : ∀ i, #ι ≤ #(S i)) :
    ∃ f : ι → β, Injective f ∧ ∀ i, f i ∈ S i := by
  classical
  obtain ⟨ord, wf, ho⟩ := exists_ord_eq_type_lt ι
  have step (i : ι) (g : ∀ j : ι, j < i → β) :
      ∃ x ∈ S i, x ∉ range (fun j : Iio i => g j.1 j.2) :=
    fresh _ _ ((mk_Iio_lt i ho).trans_le (h i))
  let choosePoint (i : ι) (g : ∀ j : ι, j < i → β) := (step i g).choose
  let f := wellFounded_lt.fix choosePoint
  have spec (i : ι) : f i ∈ S i ∧ f i ∉ range (fun j : Iio i => f j.1) := by
    have eqn : f i = choosePoint i (fun j _ => f j) := WellFounded.fix_eq _ _ _
    exact eqn ▸ (step i (fun j _ => f j)).choose_spec
  have ne_of_before {i j : ι} (hij : i < j) : f i ≠ f j := fun he =>
    (spec j).2 ⟨⟨i, hij⟩, he⟩
  refine ⟨f, ?_, fun i => (spec i).1⟩
  intro i j he
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (ne_of_before hij he).elim
  · exact hij
  · exact (ne_of_before hij he.symm).elim

private theorem reserved {ι β : Type} (S : ι → Set β) (hi : #ι ≤ 𝔠)
    (hb : #β = 𝔠) (h : ∀ i, 𝔠 ≤ #(S i)) :
    ∃ f : ι → β, Injective f ∧ (∀ i, f i ∈ S i) ∧ #((range f)ᶜ : Set β) = 𝔠 := by
  classical
  -- The right summand reserves points for extending the matching to a bijection.
  let T : ι ⊕ ℝ → Set β := Sum.elim S (fun _ => univ)
  have hc : #(ι ⊕ ℝ) ≤ 𝔠 := by
    simpa only [mk_sum, lift_id, mk_real, continuum_add_self] using
      (add_le_add hi (le_refl 𝔠))
  obtain ⟨g, hg, hgT⟩ := representatives T (fun i => hc.trans (by
    cases i with
    | inl i => exact h i
    | inr r => simp [T, hb]))
  let f (i : ι) := g (Sum.inl i)
  have hr (r : ℝ) : g (Sum.inr r) ∉ range f := by
    rintro ⟨i, he⟩
    cases hg he
  let k (r : ℝ) : ((range f)ᶜ : Set β) := ⟨g (Sum.inr r), hr r⟩
  have hk : Injective k := fun _ _ he => Sum.inr.inj (hg (congrArg Subtype.val he))
  exact ⟨f, hg.comp Sum.inl_injective, fun i => hgT (.inl i),
    (mk_set_le _ |>.trans_eq hb).antisymm (mk_real ▸ mk_le_of_injective hk)⟩

private theorem matching {ι α β : Type} (A : ι → Set α) (B : ι → Set β)
    (hi : #ι ≤ 𝔠) (ha : #α = 𝔠) (hb : #β = 𝔠)
    (hA : ∀ i, 𝔠 ≤ #(A i)) (hB : ∀ i, 𝔠 ≤ #(B i)) :
    ∃ e : α ≃ β, ∀ i, ∃ x ∈ A i, e x ∈ B i := by
  classical
  obtain ⟨a, hai, ham, hac⟩ := reserved A hi ha hA
  obtain ⟨b, hbi, hbm, hbc⟩ := reserved B hi hb hB
  let ea := Equiv.ofInjective a hai
  let eb := Equiv.ofInjective b hbi
  let ec := (Cardinal.eq.mp (hac.trans hbc.symm)).some
  let e := (Equiv.Set.sumCompl (range a)).symm.trans
    ((Equiv.sumCongr (ea.symm.trans eb) ec).trans (Equiv.Set.sumCompl (range b)))
  refine ⟨e, fun i => ⟨a i, ham i, ?_⟩⟩
  have he : e (a i) = b i := by
    have hsplit : (Equiv.Set.sumCompl (range a)).symm (a i) = Sum.inl (ea i) :=
      Equiv.Set.sumCompl_symm_apply_of_mem (mem_range_self i)
    simp only [e, Equiv.trans_apply, hsplit, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.symm_apply_apply, Equiv.Set.sumCompl_apply_inl]
    rfl
  rw [he]
  exact hbm i

private abbrev Plane := ℝ × ℝ

private def obstruction (U V : Set Plane) := (U ∪ V)ᶜ ∪ (U ∩ V)

private theorem open_card {s : Set ℝ} (ho : IsOpen s) (hn : s.Nonempty) : 𝔠 ≤ #s := by
  obtain ⟨a, b, hab, hs⟩ := ho.exists_Ioo_subset hn
  exact (mk_Ioo_real hab).symm.le.trans (mk_le_mk_of_subset hs)

private theorem obstruction_card {U V : Set Plane} (hU : IsOpen U) (hV : IsOpen V)
    (hnU : U.Nonempty) (hnV : V.Nonempty) : 𝔠 ≤ #(obstruction U V) := by
  classical
  by_contra! small
  let S := obstruction U V
  have outside {p : Plane → ℝ} {W : Set Plane} (hw : 𝔠 ≤ #(p '' W)) :
      ∃ w ∈ W, p w ∉ p '' S := by
    by_contra! H
    have hsub : p '' W ⊆ p '' S := image_subset_iff.mpr H
    exact small.not_ge (hw.trans ((mk_le_mk_of_subset hsub).trans mk_image_le))
  obtain ⟨u, hu, hy⟩ := outside (p := Prod.snd)
    (open_card (isOpenMap_snd U hU) (hnU.image _))
  obtain ⟨v, hv, hx⟩ := outside (p := Prod.fst)
    (open_card (isOpenMap_fst V hV) (hnV.image _))
  -- These two lines avoid S, meet each other, and meet U and V respectively.
  let H := range (fun x : ℝ => (x, u.2))
  let L := range (fun y : ℝ => (v.1, y))
  have hHL : IsPreconnected (H ∪ L) := by
    apply IsPreconnected.union (s := H) (t := L) (v.1, u.2) ⟨v.1, rfl⟩ ⟨u.2, rfl⟩
    · exact isPreconnected_range (continuous_id.prodMk continuous_const)
    · exact isPreconnected_range (continuous_const.prodMk continuous_id)
  have avoid : ∀ z ∈ H ∪ L, z ∉ S := by
    rintro z (⟨x, rfl⟩ | ⟨y, rfl⟩) hz
    · exact hy ⟨_, hz, rfl⟩
    · exact hx ⟨_, hz, rfl⟩
  have cover : H ∪ L ⊆ U ∪ V := by
    intro z hz
    by_contra hn
    exact avoid z hz (Or.inl hn)
  obtain ⟨z, hz, hboth⟩ := hHL U V hU hV cover
    ⟨u, Or.inl ⟨u.1, rfl⟩, hu⟩ ⟨v, Or.inr ⟨v.2, rfl⟩, hv⟩
  exact avoid z hz (Or.inr hboth)

private theorem opens_card : #(Opens Plane) ≤ 𝔠 := by
  classical
  obtain ⟨B, hc, _, hB⟩ := exists_countable_basis Plane
  let code (u : Opens Plane) : Set B := {b | b.val ⊆ u}
  have hi : Injective code := by
    intro u v he
    apply SetLike.coe_injective
    apply hB.eq_of_forall_subset_iff u.isOpen v.isOpen
    intro b hb
    exact Set.ext_iff.mp he ⟨b, hb⟩
  calc
    _ ≤ #(Set B) := mk_le_of_injective hi
    _ = 2 ^ #B := mk_set
    _ ≤ 2 ^ ℵ₀ := power_le_power_left (by norm_num) (le_aleph0_iff_set_countable.mpr hc)
    _ = 𝔠 := two_power_aleph0

private theorem connected_bijection : ∃ f : ℝ ≃ Plane, Mathoverflow235893.IsConnectedMap f := by
  classical
  let R := {t : (ℝ × ℝ) × Opens Plane × Opens Plane //
    t.1.1 < t.1.2 ∧ (t.2.1 : Set Plane).Nonempty ∧ (t.2.2 : Set Plane).Nonempty}
  let A (i : R) := Ioo i.1.1.1 i.1.1.2
  let B (i : R) := obstruction i.1.2.1 i.1.2.2
  have hp : #Plane = 𝔠 := by simp [Plane, mk_prod, mk_real]
  have hoo : #(Opens Plane × Opens Plane) ≤ 𝔠 := by
    simpa only [mk_prod, lift_id, continuum_mul_self] using
      (mul_le_mul' opens_card opens_card)
  have hr : #R ≤ 𝔠 := by
    apply (mk_subtype_le _).trans
    simpa only [mk_prod, lift_id, mk_real, continuum_mul_self] using
      (mul_le_mul' hp.le hoo)
  obtain ⟨f, h⟩ := matching A B hr mk_real hp
    (fun i => (mk_Ioo_real i.2.1).ge)
    (fun i => obstruction_card i.1.2.1.isOpen i.1.2.2.isOpen i.2.2.1 i.2.2.2)
  refine ⟨f, ?_⟩
  intro s hs
  refine ⟨hs.nonempty.image _, ?_⟩
  rcases s.subsingleton_or_nontrivial with hsmall | hmany
  · exact (hsmall.image f).isPreconnected
  obtain ⟨a, ha, b, hb, hab⟩ := hmany.exists_lt
  intro U V hU hV cover hu hv
  let i : R := ⟨((a, b), ⟨U, hU⟩, ⟨V, hV⟩), hab, hu.mono inter_subset_right,
    hv.mono inter_subset_right⟩
  obtain ⟨x, hx, hfx⟩ := h i
  have hx' : x ∈ s := hs.isPreconnected.ordConnected.out ha hb (Ioo_subset_Icc_self hx)
  have hmem := mem_image_of_mem f hx'
  rcases hfx with hout | hboth
  · exact (hout (cover hmem)).elim
  · exact ⟨_, hmem, hboth⟩

end OMA

open OMA Mathoverflow235893

-- Credit: @MrSeizy
theorem OMA.solution : type_of% @Mathoverflow235893.mathoverflow_260589 := by
  obtain ⟨g, hg⟩ := connected_bijection
  let h : (ℝ^2) ≃ₜ Plane :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans (Homeomorph.finTwoArrow)
  let f := g.trans h.symm.toEquiv
  refine ⟨f, isConnectedMap_comp (f := (g : ℝ → Plane)) (g := (h.symm : Plane → ℝ^2)) hg
    (isConnectedMap_homeomorph h.symm), ?_⟩
  intro hf
  have hr : 1 < Module.rank ℝ (ℝ^2) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  have hc := hf (isConnected_compl_singleton_of_one_lt_rank hr (f 0))
  rw [Equiv.image_symm_eq_preimage] at hc
  have hord := hc.isPreconnected.ordConnected
  have hm : (-1 : ℝ) ∈ f ⁻¹' ({f 0}ᶜ) := by simp
  have hp : (1 : ℝ) ∈ f ⁻¹' ({f 0}ᶜ) := by simp
  have hz := hord.out hm hp (show (0 : ℝ) ∈ Icc (-1) 1 by constructor <;> norm_num)
  simp at hz
