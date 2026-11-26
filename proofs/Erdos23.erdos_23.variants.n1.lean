import FormalConjectures.ErdosProblems.«23»

/-!
Proof of Erdos23.erdos_23.variants.n1: every triangle-free graph on 5 vertices
can be made bipartite by removing at most 1 edge.
-/

open SimpleGraph

theorem OMA.solution : type_of% @Erdos23.erdos_23.variants.n1 := by
  classical
  intro G hG
  by_cases hdeg : ∃ v a b : Fin 5, a ≠ b ∧ G.Adj v a ∧ G.Adj v b
  · rcases hdeg with ⟨v, a, b, hab, hva, hvb⟩
    let c : Fin 5 → Fin 2 := fun u => if G.Adj v u then 1 else 0
    let H : SimpleGraph (Fin 5) :=
      { Adj := fun x y => G.Adj x y ∧ c x ≠ c y
        symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
        loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩ }
    refine ⟨H, fun _ _ h => h.1, ?_, ?_⟩
    · refine ⟨SimpleGraph.Coloring.mk c (fun {x y} h => h.2)⟩
    · rw [Finset.card_le_one]
      intro e₁ he₁ e₂ he₂
      have hmem : ∀ x y, G.Adj x y → ¬ H.Adj x y →
          x ≠ y ∧ x ∉ ({v, a, b} : Finset (Fin 5)) ∧ y ∉ ({v, a, b} : Finset (Fin 5)) := by
        intro x y hadj hnotH
        have hc : c x = c y := by
          by_contra hne
          exact hnotH ⟨hadj, hne⟩
        have hnvx : ¬ G.Adj v x := by
          intro hvx
          have hvy : G.Adj v y := by
            by_contra hnvy
            simp [c, hvx, hnvy] at hc
          have hcl : G.IsNClique 3 {v, x, y} := by
            refine ⟨?_, ?_⟩
            · intro p hp q hq hpq
              simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
                Set.mem_singleton_iff] at hp hq
              rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
              · exact absurd rfl hpq
              · exact hvx
              · exact hvy
              · exact hvx.symm
              · exact absurd rfl hpq
              · exact hadj
              · exact hvy.symm
              · exact hadj.symm
              · exact absurd rfl hpq
            · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp [hadj.ne]
              · simp [hvx.ne, hvy.ne]
          exact hG {v, x, y} hcl
        have hnvy : ¬ G.Adj v y := by
          intro hvy
          simp [c, hnvx, hvy] at hc
        refine ⟨hadj.ne, ?_, ?_⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          refine ⟨?_, ?_, ?_⟩
          · rintro rfl; exact hnvy hadj
          · rintro rfl; exact hnvx hva
          · rintro rfl; exact hnvx hvb
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          refine ⟨?_, ?_, ?_⟩
          · rintro rfl; exact hnvx hadj.symm
          · rintro rfl; exact hnvy hva
          · rintro rfl; exact hnvy hvb
      let S : Finset (Fin 5) := Finset.univ \ {v, a, b}
      have hScard : S.card = 2 := by
        have h3 : ({v, a, b} : Finset (Fin 5)).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp [hab]
          · simp [hva.ne, hvb.ne]
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, h3]
      induction e₁ using Sym2.ind with
      | _ x₁ y₁ =>
        induction e₂ using Sym2.ind with
        | _ x₂ y₂ =>
          simp only [Finset.mem_sdiff, mem_edgeFinset] at he₁ he₂
          rcases hmem x₁ y₁ he₁.1 he₁.2 with ⟨hxy₁, hx₁, hy₁⟩
          rcases hmem x₂ y₂ he₂.1 he₂.2 with ⟨hxy₂, hx₂, hy₂⟩
          have hsub₁ : ({x₁, y₁} : Finset (Fin 5)) = S := by
            apply Finset.eq_of_subset_of_card_le
            · intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl <;> simp [S, hx₁, hy₁]
            · rw [hScard, Finset.card_pair hxy₁]
          have hsub₂ : ({x₂, y₂} : Finset (Fin 5)) = S := by
            apply Finset.eq_of_subset_of_card_le
            · intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl <;> simp [S, hx₂, hy₂]
            · rw [hScard, Finset.card_pair hxy₂]
          have heq : ({x₁, y₁} : Finset (Fin 5)) = {x₂, y₂} := hsub₁.trans hsub₂.symm
          have h1 : x₁ ∈ ({x₂, y₂} : Finset (Fin 5)) := heq ▸ Finset.mem_insert_self x₁ {y₁}
          have h2 : y₁ ∈ ({x₂, y₂} : Finset (Fin 5)) :=
            heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y₁)
          simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
          rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
          · exact absurd rfl hxy₁
          · rfl
          · exact Sym2.eq_swap
          · exact absurd rfl hxy₁
  · push Not at hdeg
    refine ⟨G, le_rfl, ?_, ?_⟩
    · let c : Fin 5 → Fin 2 := fun u => if ∃ w : Fin 5, w < u ∧ G.Adj u w then 1 else 0
      refine ⟨SimpleGraph.Coloring.mk c ?_⟩
      intro x y hxy
      rcases lt_or_gt_of_ne hxy.ne with hlt | hgt
      · have hy : ∃ w : Fin 5, w < y ∧ G.Adj y w := ⟨x, hlt, hxy.symm⟩
        have hx : ¬ ∃ w : Fin 5, w < x ∧ G.Adj x w := by
          rintro ⟨w, hwx, hxw⟩
          have hwy : w ≠ y := ne_of_lt (lt_trans hwx hlt)
          exact hdeg x w y hwy hxw hxy
        simp [c, hx, hy]
      · have hx : ∃ w : Fin 5, w < x ∧ G.Adj x w := ⟨y, hgt, hxy⟩
        have hy : ¬ ∃ w : Fin 5, w < y ∧ G.Adj y w := by
          rintro ⟨w, hwy, hyw⟩
          have hwx : w ≠ x := ne_of_lt (lt_trans hwy hgt)
          exact hdeg y w x hwx hyw hxy.symm
        simp [c, hx, hy]
    · simp
