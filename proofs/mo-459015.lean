import OMAStatements.S_mo_459015
import Mathlib
open OMA.S_mo_459015

theorem OMA.solution : type_of% @OMA.S_mo_459015.main := by
  intro X Y _ _ _ _ E _ n k hX hY hkn
  constructor
  · rintro ⟨S0, hS0, f, hinj, hE⟩ S
    have h1 : (S ∩ S0).card ≤ (Finset.univ.filter fun y => ∃ x ∈ S, E x y).card := by
      apply Finset.card_le_card_of_injOn f
      · intro x hx
        rw [Finset.mem_coe, Finset.mem_inter] at hx
        rw [Finset.mem_coe, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, x, hx.1, hE x hx.2⟩
      · exact hinj.mono (by intro x hx; exact (Finset.mem_inter.mp hx).2)
    have h2 : (S \ S0).card ≤ n - k := by
      have : (S \ S0).card ≤ (Finset.univ \ S0).card :=
        Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl)
      rw [Finset.card_univ_sdiff, hX, hS0] at this
      exact this
    have h3 := Finset.card_inter_add_card_sdiff S S0
    omega
  · intro hH
    set m := n - k with hm
    let t : X → Finset (Y ⊕ Fin m) := fun x =>
      (Finset.univ.filter (E x)).image Sum.inl ∪ Finset.univ.image Sum.inr
    have hall : ∀ s : Finset X, s.card ≤ (s.biUnion t).card := by
      intro s
      rcases s.eq_empty_or_nonempty with hs | ⟨x0, hx0⟩
      · rw [hs]; simp
      have hsub : (Finset.univ.filter fun y => ∃ x ∈ s, E x y).image Sum.inl ∪
          (Finset.univ.image (Sum.inr : Fin m → Y ⊕ Fin m)) ⊆ s.biUnion t := by
        intro z hz
        rw [Finset.mem_union] at hz
        rw [Finset.mem_biUnion]
        rcases hz with hz | hz
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
          obtain ⟨_, x, hx, hxy⟩ := Finset.mem_filter.mp hy
          refine ⟨x, hx, ?_⟩
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hxy⟩, rfl⟩)
        · exact ⟨x0, hx0, Finset.mem_union_right _ hz⟩
      have hdisj : Disjoint ((Finset.univ.filter fun y => ∃ x ∈ s, E x y).image Sum.inl)
          (Finset.univ.image (Sum.inr : Fin m → Y ⊕ Fin m)) := by
        rw [Finset.disjoint_left]
        intro z hz1 hz2
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz2
        exact Sum.inr_ne_inl hi
      have hc := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ Sum.inl_injective,
        Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ, Fintype.card_fin]
        at hc
      have := hH s
      omega
    obtain ⟨g, ginj, hg⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
    set S1 := Finset.univ.filter fun x => (g x).isLeft = true with hS1
    set C := Finset.univ.filter fun x => ¬ (g x).isLeft = true with hC
    have hCc : C.card ≤ m := by
      have : C.card ≤ (Finset.univ.image (Sum.inr : Fin m → Y ⊕ Fin m)).card := by
        apply Finset.card_le_card_of_injOn g
        · intro x hx
          rw [Finset.mem_coe, hC, Finset.mem_filter] at hx
          have hgx := hg x
          rw [Finset.mem_union] at hgx
          rcases hgx with h | h
          · obtain ⟨y, _, hy⟩ := Finset.mem_image.mp h
            exact absurd (by rw [← hy]; rfl) hx.2
          · exact h
        · exact ginj.injOn
      rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ,
        Fintype.card_fin] at this
      exact this
    have hsum : S1.card + C.card = n := by
      rw [hS1, hC, Finset.card_filter_add_card_filter_not, Finset.card_univ, hX]
    obtain ⟨S, hSS1, hScard⟩ := Finset.exists_subset_card_eq (show k ≤ S1.card by omega)
    refine ⟨S, hScard, ?_⟩
    by_cases hYne : Nonempty Y
    · obtain ⟨y0⟩ := hYne
      let f : X → Y := fun x => Sum.elim id (fun _ => y0) (g x)
      have hleft : ∀ x ∈ S, g x = Sum.inl (f x) := by
        intro x hx
        have h1 := (Finset.mem_filter.mp (hSS1 hx)).2
        obtain ⟨y, hy⟩ := Sum.isLeft_iff.mp h1
        simp only [f, hy, Sum.elim_inl, id]
      refine ⟨f, ?_, ?_⟩
      · intro x1 hx1 x2 hx2 h
        apply ginj
        rw [hleft x1 hx1, hleft x2 hx2, h]
      · intro x hx
        have hgx := hg x
        rw [hleft x hx, Finset.mem_union] at hgx
        rcases hgx with h | h
        · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp h
          rw [Sum.inl_injective hyx] at hy
          exact (Finset.mem_filter.mp hy).2
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
          exact absurd hi Sum.inr_ne_inl
    · have hY0 : n = 0 := by
        rw [← hY]
        exact Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hYne)
      have hXe : IsEmpty X := Fintype.card_eq_zero_iff.mp (hX.trans hY0)
      refine ⟨fun x => (hXe.false x).elim, ?_, ?_⟩
      · intro x1 _ _ _ _
        exact (hXe.false x1).elim
      · intro x _
        exact (hXe.false x).elim
