import FormalConjectures.ErdosProblems.«23»

/-!
Structural proof that every triangle-free graph on 5 vertices becomes bipartite after
removing at most one edge.
-/

open SimpleGraph

theorem OMA.solution : type_of% @Erdos23.erdos_23.variants.n1 := by
  classical
  intro G hG
  by_cases hdeg : ∃ v : Fin 5, 2 ≤ G.degree v
  · obtain ⟨v, hv⟩ := hdeg
    let B : Finset (Fin 5) := G.neighborFinset v
    let A : Finset (Fin 5) := (Finset.univ \ B).erase v
    have hB : 2 ≤ B.card := hv
    have hvB : v ∉ B := G.notMem_neighborFinset_self v
    have hA : A.card ≤ 2 := by
      have hvU : v ∈ Finset.univ \ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvB⟩
      have h1 : A.card + 1 = (Finset.univ \ B).card := Finset.card_erase_add_one hvU
      have h2 : (Finset.univ \ B).card = 5 - B.card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      omega
    let H : SimpleGraph (Fin 5) :=
      { Adj := fun x y => G.Adj x y ∧ (x ∈ B ↔ y ∉ B)
        symm := ⟨fun _ _ h => ⟨h.1.symm, by tauto⟩⟩
        loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩ }
    refine ⟨H, fun _ _ h => h.1, ?_, ?_⟩
    · refine ⟨SimpleGraph.Coloring.mk (fun x => if x ∈ B then (0 : Fin 2) else 1) ?_⟩
      intro x y ⟨_, hiff⟩
      by_cases hx : x ∈ B
      · have hy : y ∉ B := hiff.mp hx
        simp [hx, hy]
      · have hy : y ∈ B := not_not.mp fun hy => hx (hiff.mpr hy)
        simp [hx, hy]
    · rw [Finset.card_le_one]
      have hmemA : ∀ {x y : Fin 5}, G.Adj x y → ¬ H.Adj x y →
          x ∈ A ∧ y ∈ A ∧ x ≠ y := by
        intro x y hxy hnH
        have hne : x ≠ y := hxy.ne
        have hnotB : ¬ (x ∈ B ∧ y ∈ B) := by
          rintro ⟨hx, hy⟩
          have hvx : G.Adj v x := (mem_neighborFinset G v x).mp hx
          have hvy : G.Adj v y := (mem_neighborFinset G v y).mp hy
          have hcl : G.IsNClique 3 {v, x, y} := by
            refine ⟨?_, ?_⟩
            · intro a ha b hb hab
              simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
                Set.mem_singleton_iff] at ha hb
              rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
              · exact (hab rfl).elim
              · exact hvx
              · exact hvy
              · exact hvx.symm
              · exact (hab rfl).elim
              · exact hxy
              · exact hvy.symm
              · exact hxy.symm
              · exact (hab rfl).elim
            · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp [hne]
              · simp [hvx.ne, hvy.ne]
          exact hG {v, x, y} hcl
        have hsame : x ∉ B ∧ y ∉ B := by
          have : ¬ (x ∈ B ↔ y ∉ B) := fun h => hnH ⟨hxy, h⟩
          tauto
        have hxv : x ≠ v := by
          rintro rfl
          exact hsame.2 ((mem_neighborFinset G x y).mpr hxy)
        have hyv : y ≠ v := by
          rintro rfl
          exact hsame.1 ((mem_neighborFinset G y x).mpr hxy.symm)
        exact ⟨Finset.mem_erase.mpr ⟨hxv, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hsame.1⟩⟩,
          Finset.mem_erase.mpr ⟨hyv, Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hsame.2⟩⟩, hne⟩
      have hpair : ∀ {x y : Fin 5}, x ∈ A → y ∈ A → x ≠ y → ({x, y} : Finset (Fin 5)) = A := by
        intro x y hx hy hne
        exact Finset.eq_of_subset_of_card_le
          (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
          (by rw [Finset.card_pair hne]; exact hA)
      intro e₁ he₁ e₂ he₂
      have ⟨hG₁, hH₁⟩ : e₁ ∈ G.edgeSet ∧ e₁ ∉ H.edgeSet := by simpa [mem_edgeFinset] using he₁
      have ⟨hG₂, hH₂⟩ : e₂ ∈ G.edgeSet ∧ e₂ ∉ H.edgeSet := by simpa [mem_edgeFinset] using he₂
      induction e₁ using Sym2.ind with
      | _ x₁ y₁ =>
        induction e₂ using Sym2.ind with
        | _ x₂ y₂ =>
          obtain ⟨hx₁, hy₁, hne₁⟩ := hmemA hG₁ hH₁
          obtain ⟨hx₂, hy₂, hne₂⟩ := hmemA hG₂ hH₂
          have heq : ({x₁, y₁} : Finset (Fin 5)) = {x₂, y₂} :=
            (hpair hx₁ hy₁ hne₁).trans (hpair hx₂ hy₂ hne₂).symm
          have hx₁m : x₁ ∈ ({x₂, y₂} : Finset (Fin 5)) := by
            rw [← heq]; exact Finset.mem_insert_self x₁ {y₁}
          have hy₁m : y₁ ∈ ({x₂, y₂} : Finset (Fin 5)) := by
            rw [← heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y₁)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁m hy₁m
          rcases hx₁m with rfl | rfl <;> rcases hy₁m with rfl | rfl
          · exact (hne₁ rfl).elim
          · rfl
          · exact Sym2.eq_swap
          · exact (hne₁ rfl).elim
  · push Not at hdeg
    refine ⟨G, le_rfl, ?_, by simp⟩
    refine ⟨SimpleGraph.Coloring.mk (fun x => if ∃ y, G.Adj x y ∧ x < y then (0 : Fin 2) else 1) ?_⟩
    intro x y hxy
    have hle : ∀ u a b : Fin 5, G.Adj u a → G.Adj u b → a = b := by
      intro u a b ha hb
      by_contra hab
      have hcard : 2 ≤ (G.neighborFinset u).card := by
        rw [← Finset.card_pair hab]
        apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact (mem_neighborFinset G u z).mpr ha
        · exact (mem_neighborFinset G u z).mpr hb
      have hu : (G.neighborFinset u).card < 2 := by
        simpa [G.card_neighborFinset_eq_degree] using hdeg u
      omega
    rcases lt_or_gt_of_ne hxy.ne with hlt | hgt
    · have hx : ∃ z, G.Adj x z ∧ x < z := ⟨y, hxy, hlt⟩
      have hy : ¬ ∃ z, G.Adj y z ∧ y < z := by
        rintro ⟨z, hyz, hltz⟩
        have := hle y x z hxy.symm hyz
        omega
      simp [hx, hy]
    · have hy : ∃ z, G.Adj y z ∧ y < z := ⟨x, hxy.symm, hgt⟩
      have hx : ¬ ∃ z, G.Adj x z ∧ x < z := by
        rintro ⟨z, hxz, hltz⟩
        have := hle x y z hxy hxz
        omega
      simp [hx, hy]
