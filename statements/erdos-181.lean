import Mathlib

/-!
# Erdős Problem 181

Source: https://www.erdosproblems.com/181
Credit: @mattdorman

The source asks (Burr and Erdős): let `Qₙ` be the `n`-dimensional hypercube graph (`2ⁿ` vertices,
`n 2ⁿ⁻¹` edges). Prove that `R(Qₙ) ≪ 2ⁿ`.

Reading used here: `R(H)` is the diagonal two-colour Ramsey number, the least `N` such that every
red/blue colouring of the edges of `K_N` has a monochromatic copy of `H`. A colouring is a graph
`G` on `Fin N` (red edges) and its complement (blue edges); a copy is a subgraph embedding (`SimpleGraph.IsContained`).
`R(Qₙ) ≪ 2ⁿ` means there is a constant `C` with `R(Qₙ) ≤ C 2ⁿ` for all `n`, which is stated as the
existence, for each `n`, of a good `N ≤ C 2ⁿ`. `Qₙ` has vertex set `Fin n → Bool`, two vertices
adjacent when they differ in exactly one coordinate.
-/

namespace OMA.S_erdos_181

/-- The `n`-dimensional hypercube graph. -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj x y := (Finset.univ.filter fun i => x i ≠ y i).card = 1
  symm := ⟨fun x y h => by simpa only [ne_comm] using h⟩
  loopless := ⟨fun x h => by simp at h⟩

theorem main :
    ∃ C : ℝ, ∀ n : ℕ, ∃ N : ℕ, (N : ℝ) ≤ C * 2 ^ n ∧
      ∀ G : SimpleGraph (Fin N), (hypercube n).IsContained G ∨ (hypercube n).IsContained Gᶜ := by
  sorry

end OMA.S_erdos_181
