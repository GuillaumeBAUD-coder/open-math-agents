import OMAReductions.R_UnionClosed_union_closed_R1

-- Step UnionClosed.union_closed.R1.H2: hypothesis H2 of reduction UnionClosed.union_closed.R1
-- Credit: @JamesSlash. Split A by membership of x and y into N (neither), Ax, Ay, Axy. Since {x, y} is a member,
-- X -> X ∪ {x, y} maps N injectively into Axy, so |N| <= |Axy|. If x and y were both in fewer than half of the
-- members, then |Ax| + |Axy| < |N| + |Ay| and |Ay| + |Axy| < |N| + |Ax|, so |Axy| < |N|, a contradiction.

theorem OMA.solution : OMA.R_UnionClosed_union_closed_R1.H2 := by
  intro m A x y hxy hU hpair
  set a := (A.filter (fun X => x ∈ X)).filter (fun X => y ∈ X) with ha
  set b := (A.filter (fun X => x ∈ X)).filter (fun X => y ∉ X) with hb
  set c := (A.filter (fun X => x ∉ X)).filter (fun X => y ∈ X) with hc
  set d := (A.filter (fun X => x ∉ X)).filter (fun X => y ∉ X) with hd
  have h1 : (A.filter (fun X => x ∈ X)).card = a.card + b.card :=
    (Finset.card_filter_add_card_filter_not (s := A.filter (fun X => x ∈ X)) (fun X => y ∈ X)).symm
  have h2 : (A.filter (fun X => x ∉ X)).card = c.card + d.card :=
    (Finset.card_filter_add_card_filter_not (s := A.filter (fun X => x ∉ X)) (fun X => y ∈ X)).symm
  have h3 : A.card = (A.filter (fun X => x ∈ X)).card + (A.filter (fun X => x ∉ X)).card :=
    (Finset.card_filter_add_card_filter_not (s := A) (fun X => x ∈ X)).symm
  have h4 : (A.filter (fun X => y ∈ X)).card = a.card + c.card := by
    have e := (Finset.card_filter_add_card_filter_not (s := A.filter (fun X => y ∈ X)) (fun X => x ∈ X)).symm
    have ea : (A.filter (fun X => y ∈ X)).filter (fun X => x ∈ X) = a := by
      ext X; simp only [ha, Finset.mem_filter]; tauto
    have ec : (A.filter (fun X => y ∈ X)).filter (fun X => x ∉ X) = c := by
      ext X; simp only [hc, Finset.mem_filter]; tauto
    rw [ea, ec] at e
    exact e
  have hinj : d.card ≤ a.card := by
    refine Finset.card_le_card_of_injOn (fun X => X ∪ {x, y}) ?_ ?_
    · intro X hX
      simp only [hd, Finset.mem_coe, Finset.mem_filter] at hX
      simp only [ha, Finset.mem_coe, Finset.mem_filter]
      refine ⟨⟨hU X hX.1.1 {x, y} hpair, by simp⟩, by simp⟩
    · intro X hX Y hY hXY
      simp only [hd, Finset.mem_coe, Finset.mem_filter] at hX hY
      have dX : Disjoint X {x, y} := by
        rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]; exact ⟨hX.1.2, hX.2⟩
      have dY : Disjoint Y {x, y} := by
        rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]; exact ⟨hY.1.2, hY.2⟩
      have hXY' : X ∪ {x, y} = Y ∪ {x, y} := hXY
      rw [← Finset.union_sdiff_cancel_right dX, ← Finset.union_sdiff_cancel_right dY, hXY']
  have hnat : A.card ≤ 2 * (A.filter (fun X => x ∈ X)).card ∨
      A.card ≤ 2 * (A.filter (fun X => y ∈ X)).card := by
    by_contra hcon
    rw [not_or, not_le, not_le] at hcon
    omega
  rcases hnat with h | h
  · left
    have : (A.card : ℚ) ≤ 2 * (A.filter (fun X => x ∈ X)).card := by exact_mod_cast h
    linarith
  · right
    have : (A.card : ℚ) ≤ 2 * (A.filter (fun X => y ∈ X)).card := by exact_mod_cast h
    linarith
