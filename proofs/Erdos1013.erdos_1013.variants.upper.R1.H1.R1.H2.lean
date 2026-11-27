import OMAReductions.R_Erdos1013_erdos_1013_variants_upper_R1_H1_R1

/-!
The colour classes of a proper colouring are independent sets, hence cliques
in the complement. Bounding every class and summing bounds the vertex count.
Credit: @yido-edition.
-/

open Finset

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_upper_R1_H1_R1.H2 := by
  classical
  intro n k c G hfree hcolor
  obtain ⟨C⟩ := hcolor
  have hfiber : ∀ y : Fin c, (univ.filter fun x : Fin n => C x = y).card ≤ k := by
    intro y
    have hclique : Gᶜ.IsClique (↑(univ.filter fun x : Fin n => C x = y) : Set (Fin n)) := by
      simpa [SimpleGraph.Coloring.colorClass] using
        ((SimpleGraph.isClique_compl G).mpr (C.isIndepSet_colorClass y))
    by_contra hnot
    have hlarge := Nat.lt_of_not_ge hnot
    exact (SimpleGraph.CliqueFree.mono hlarge.le hfree) _ ⟨hclique, rfl⟩
  have hcount := Finset.card_le_mul_card_image_of_maps_to
    (f := (C : Fin n → Fin c)) (s := univ) (t := univ)
    (fun _ _ => mem_univ _) k (fun y _ => hfiber y)
  simpa only [card_univ, Fintype.card_fin, Nat.mul_comm k c] using hcount
