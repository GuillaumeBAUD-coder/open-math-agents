import FormalConjectures.ErdosProblems.«934»

-- Reduction Erdos934.erdos_934.variants.h_two.R1 of Erdős Problem 934 — h two
-- Credit: @luciusacarr
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `h₂(d) ≤ 5d²/4 + 1`, with equality for even `d`

* `H1` is the extremal construction: for even `d`, the blow-up of the `5`-cycle with `d / 2`
  vertices per class has maximum degree `d`, `5d²/4` edges, and no two edges at distance `≥ 2`
  (no induced `2K₂`).
* `H2` is the theorem of Chung, Gyárfás, Tuza and Trotter: every graph with maximum degree at most
  `d` and at least `⌊5d²/4⌋ + 1` edges has two edges at distance at least `2`.
-/

namespace OMA.R_Erdos934_erdos_934_variants_h_two_R1

open Erdos934

/-- The blow-up of `C₅`: for even `d`, a graph of maximum degree at most `d` with at least
`5d²/4` edges and no two edges at distance at least `2`. -/
def H1 : Prop :=
  ∀ d : ℕ, Even d → ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ v, (G.neighborSet v).ncard ≤ d) ∧ 5 * d ^ 2 / 4 ≤ G.edgeSet.ncard ∧ ¬ HasFarEdges G 2

/-- Chung–Gyárfás–Tuza–Trotter: maximum degree at most `d` and at least `⌊(5d² + 4)/4⌋` edges
force two edges at distance at least `2`. -/
def H2 : Prop :=
  ∀ (d n : ℕ) (G : SimpleGraph (Fin n)), (∀ v, (G.neighborSet v).ncard ≤ d) →
    (5 * d ^ 2 + 4) / 4 ≤ G.edgeSet.ncard → HasFarEdges G 2

theorem main : H1 → H2 → type_of% @Erdos934.erdos_934.variants.h_two := by
  intro h1 h2
  have hup : ∀ d : ℕ, h 2 d ≤ (5 * d ^ 2 + 4) / 4 := fun d => h_le (h2 d)
  refine ⟨fun d => by have := hup d; omega, fun d hd => ?_⟩
  apply le_antisymm (by have := hup d; omega)
  have hne : {m : ℕ | ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ v, (G.neighborSet v).ncard ≤ d) → m ≤ G.edgeSet.ncard → HasFarEdges G 2}.Nonempty :=
    ⟨_, h2 d⟩
  have hmem := Nat.sInf_mem hne
  obtain ⟨n, G, hdeg, hedge, hfar⟩ := h1 d hd
  have hlt : 5 * d ^ 2 / 4 < h 2 d := by
    by_contra hle
    exact hfar (hmem n G hdeg (le_trans (not_lt.mp hle) hedge))
  obtain ⟨k, rfl⟩ := hd
  have : 5 * (k + k) ^ 2 / 4 = 5 * k ^ 2 := by ring_nf; omega
  rw [this] at hlt
  nlinarith

end OMA.R_Erdos934_erdos_934_variants_h_two_R1
