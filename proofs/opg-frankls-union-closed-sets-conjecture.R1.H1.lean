import OMAReductions.R_opg_frankls_union_closed_sets_conjecture_R1

-- Step opg-frankls-union-closed-sets-conjecture.R1.H1: hypothesis H1 of reduction opg-frankls-union-closed-sets-conjecture.R1
-- Credit: @nnkostov

/-!
# Sarvate-Renaud Case of Frankl's Union-Closed Sets Conjecture

If a finite union-closed family `F` of finite sets contains a member `S` of
cardinality 1 or 2, then some element of `S` belongs to at least half the
members of `F`:

* When `S = {x}`, `A ↦ A ∪ {x}` maps `{A ∈ F | x ∉ A}` injectively into
  `{A ∈ F | x ∈ A}`.
* When `S = {x, y}`, `A ↦ A ∪ {x, y}` maps `{A ∈ F | x ∉ A ∧ y ∉ A}`
  injectively into `{A ∈ F | x ∈ A ∧ y ∈ A}`, giving `|F| ≤ |F_x| + |F_y|`,
  so at least one of `x` or `y` appears in at least `|F| / 2` members.
-/

theorem OMA.solution : OMA.R_opg_frankls_union_closed_sets_conjecture_R1.H1 := by
  intro α _ F huc ⟨S, hSF, hcard⟩
  rcases hcard with h1 | h2
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1
    let Fx := F.filter (fun A => x ∈ A)
    let Fnx := F.filter (fun A => x ∉ A)
    have hsplit : Fx.card + Fnx.card = F.card :=
      Finset.card_filter_add_card_filter_not (s := F) (fun A => x ∈ A)
    have hinj : Fnx.card ≤ Fx.card := by
      refine Finset.card_le_card_of_injOn (fun A => A ∪ {x}) ?_ ?_
      · intro A hA
        simp only [Fnx, Fx, Finset.mem_coe, Finset.mem_filter] at hA ⊢
        exact ⟨huc A hA.1 {x} hSF, Finset.mem_union_right A (Finset.mem_singleton_self x)⟩
      · intro A hA B hB hAB
        simp only [Fnx, Finset.mem_coe, Finset.mem_filter] at hA hB
        ext z
        by_cases hzx : z = x
        · subst hzx
          exact iff_of_false hA.2 hB.2
        · have hz := Finset.ext_iff.mp hAB z
          simpa only [Finset.mem_union, Finset.mem_singleton, hzx, or_false] using hz
    have hfx : F.card ≤ 2 * Fx.card := by omega
    exact ⟨x, hfx⟩
  · obtain ⟨x, y, _, rfl⟩ := Finset.card_eq_two.mp h2
    let Fx := F.filter (fun A => x ∈ A)
    let Fnx := F.filter (fun A => x ∉ A)
    let Fy := F.filter (fun A => y ∈ A)
    let F11 := Fx.filter (fun A => y ∈ A)
    let F10 := Fx.filter (fun A => y ∉ A)
    let F01 := Fnx.filter (fun A => y ∈ A)
    let F00 := Fnx.filter (fun A => y ∉ A)
    have hsplit : Fx.card + Fnx.card = F.card :=
      Finset.card_filter_add_card_filter_not (s := F) (fun A => x ∈ A)
    have hsplitx : F11.card + F10.card = Fx.card :=
      Finset.card_filter_add_card_filter_not (s := Fx) (fun A => y ∈ A)
    have hsplitnx : F01.card + F00.card = Fnx.card :=
      Finset.card_filter_add_card_filter_not (s := Fnx) (fun A => y ∈ A)
    have hsplity : F11.card + F01.card = Fy.card := by
      have h := Finset.card_filter_add_card_filter_not (s := Fy) (fun A => x ∈ A)
      have h1 : Fy.filter (fun A => x ∈ A) = F11 := by
        ext A
        simp only [Fy, F11, Fx, Finset.mem_filter]
        tauto
      have h2' : Fy.filter (fun A => x ∉ A) = F01 := by
        ext A
        simp only [Fy, F01, Fnx, Finset.mem_filter]
        tauto
      rw [h1, h2'] at h
      exact h
    have hinj : F00.card ≤ F11.card := by
      refine Finset.card_le_card_of_injOn (fun A => A ∪ {x, y}) ?_ ?_
      · intro A hA
        simp only [F00, F11, Fnx, Fx, Finset.mem_coe, Finset.mem_filter] at hA ⊢
        refine ⟨⟨huc A hA.1.1 {x, y} hSF, ?_⟩, ?_⟩
        · exact Finset.mem_union_right A (Finset.mem_insert_self x {y})
        · exact Finset.mem_union_right A (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
      · intro A hA B hB hAB
        simp only [F00, Fnx, Finset.mem_coe, Finset.mem_filter] at hA hB
        ext z
        by_cases hzx : z = x
        · subst hzx
          exact iff_of_false hA.1.2 hB.1.2
        · by_cases hzy : z = y
          · subst hzy
            exact iff_of_false hA.2 hB.2
          · have hz := Finset.ext_iff.mp hAB z
            simpa only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hzx, hzy,
              or_self, or_false] using hz
    by_cases hx : F.card ≤ 2 * Fx.card
    · exact ⟨x, hx⟩
    · have hfy : F.card ≤ 2 * Fy.card := by omega
      exact ⟨y, hfy⟩
