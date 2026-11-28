import FormalConjectures.WrittenOnTheWallII.GraphConjecture25
import Mathlib.Combinatorics.SimpleGraph.Prod

open SimpleGraph Finset

universe u in
theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture25.conjecture25.{u} := by
  intro h
  let A := ULift.{u} (Fin 2)
  let G : SimpleGraph (A × Fin 7) := ⊤ □ ⊤
  let d := (univ.image (distEven G)).min' (univ_nonempty.image _)
  have hh : 2 * (⌈(1 + (d : ℝ)) / 3⌉ : ℝ) ≤ (b G : ℝ) :=
    h G (connected_top.boxProd connected_top)
  have hd : 6 ≤ d := by
    apply le_min'
    intro n hn
    obtain ⟨x, _, rfl⟩ := mem_image.mp hn
    let z : A := if x.1 = ⟨0⟩ then ⟨1⟩ else ⟨0⟩
    have hz : x.1 ≠ z := by
      by_cases hx : x.1 = ⟨0⟩ <;> simp [z, hx] <;> decide
    let U := (univ.erase x.2).image (fun j => (z, j))
    have hU : U.card = 6 := by
      rw [card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h),
        card_erase_of_mem (mem_univ _)]
      decide
    rw [← hU]
    apply card_le_card
    intro y hy
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hy
    have hj' := (ne_of_mem_erase hj).symm
    have he : G.edist x (z, j) = 2 := by simp [G, edist_top, hz, hj', one_add_one_eq_two]
    exact mem_filter.mpr ⟨mem_univ _, by norm_num [SimpleGraph.dist, he]; decide⟩
  have hB : largestInducedBipartiteSubgraphSize G ≤ 4 := by
    apply csSup_le'
    rintro _ ⟨s, ⟨c⟩, rfl⟩
    let f : (↑s : Set (A × Fin 7)) → A × Fin 2 := fun x => (x.1.1, c x)
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
  have hBR : (b G : ℝ) ≤ 4 := by unfold b; exact_mod_cast hB
  have hdR : (6 : ℝ) ≤ d := by exact_mod_cast hd
  linarith [Int.le_ceil ((1 + (d : ℝ)) / 3)]
