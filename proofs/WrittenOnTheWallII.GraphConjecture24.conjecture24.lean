import FormalConjectures.WrittenOnTheWallII.GraphConjecture24
import Mathlib.Combinatorics.SimpleGraph.Prod

open SimpleGraph Finset

universe u in
theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture24.conjecture24.{u} := by
  intro h
  let A := ULift.{u} (Fin 8)
  let G : SimpleGraph (A × Fin 8) := ⊤ □ ⊤
  let d := (univ.image (distEven G)).min' (univ_nonempty.image _)
  let L := (univ.image (indepNeighborsCard G)).max' (univ_nonempty.image _)
  have hh : (L : ℝ) + ⌈(d : ℝ) / 3⌉ ≤ (b G : ℝ) :=
    h G (connected_top.boxProd connected_top)
  have hd : 49 ≤ d := by
    apply le_min'
    intro n hn
    obtain ⟨x, _, rfl⟩ := mem_image.mp hn
    let U := (univ.erase x.1) ×ˢ (univ.erase x.2)
    have hU : U.card = 49 := by
      simp [U, card_erase_of_mem, A]
    apply hU.ge.trans
    apply card_le_card
    intro y hy
    have hxy := mem_product.mp hy
    have h₁ := (ne_of_mem_erase hxy.1).symm
    have h₂ := (ne_of_mem_erase hxy.2).symm
    have he : G.edist x y = 2 := by simp [G, edist_top, h₁, h₂, one_add_one_eq_two]
    exact mem_filter.mpr ⟨mem_univ _, by norm_num [SimpleGraph.dist, he]; decide⟩
  have hB : largestInducedBipartiteSubgraphSize G ≤ 16 := by
    apply csSup_le'
    rintro _ ⟨s, ⟨c⟩, rfl⟩
    let f : (↑s : Set (A × Fin 8)) → A × Fin 2 := fun x => (x.1.1, c x)
    have hf : Function.Injective f := by
      intro x y he
      have h₁ : x.1.1 = y.1.1 := congrArg (Prod.fst : A × Fin 2 → A) he
      apply Subtype.ext
      apply Prod.ext h₁
      by_contra h₂
      apply c.valid _ (congrArg (Prod.snd : A × Fin 2 → Fin 2) he)
      change G.Adj x.1 y.1
      simp [G, h₁, h₂]
    simpa [A] using Fintype.card_le_of_injective f hf
  have hBR : (b G : ℝ) ≤ 16 := by unfold b; exact_mod_cast hB
  have hdR : (49 : ℝ) ≤ d := by exact_mod_cast hd
  have hLR : (0 : ℝ) ≤ L := by positivity
  linarith [Int.le_ceil ((d : ℝ) / 3)]
