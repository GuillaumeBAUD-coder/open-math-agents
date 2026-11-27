import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R3
import Mathlib

-- Step Erdos151.erdos_151.variants.cliqueFree_four.R3.H1: hypothesis H1 of reduction Erdos151.erdos_151.variants.cliqueFree_four.R3
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Colour each vertex by its side in the chosen near-bipartition of its component, flipped by a
per-component bit chosen so that the exceptional same-side edge {a, b} avoids the colour c a b.
Edges between the two sides receive different colours; the only same-side edge is {a, b}. -/

theorem OMA.solution : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R3.H1 := by
  intro V L hL c hc
  choose side a b hside using hL
  let t : L.ConnectedComponent → Bool := fun C => decide (side C (a C) = c (a C) (b C))
  refine ⟨fun x => xor (side (L.connectedComponentMk x) x) (t (L.connectedComponentMk x)), ?_⟩
  intro x y hxy
  have hC : L.connectedComponentMk y = L.connectedComponentMk x :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
  simp only [hC]
  set C := L.connectedComponentMk x with hCdef
  by_cases hs : side C x = side C y
  · have hab := hside C x y hxy rfl hs
    have hcab : c x y = c (a C) (b C) := by
      rcases hab with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rw [hx, hy]
      · rw [hx, hy]; exact hc _ _
    have hxa : side C x = side C (a C) := by
      rcases hab with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rw [hx]
      · rw [hs, hy]
    rw [hcab, ← hs, hxa]
    simp only [t]
    cases side C (a C) <;> cases c (a C) (b C) <;> simp
  · cases h1 : side C x <;> cases h2 : side C y <;> cases h3 : t C <;> cases h4 : c x y <;>
      simp_all
