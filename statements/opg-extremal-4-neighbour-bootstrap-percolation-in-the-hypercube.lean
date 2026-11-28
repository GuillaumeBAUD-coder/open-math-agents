import Mathlib

namespace OMA.S_opg_extremal_4_neighbour_bootstrap_percolation_in_the_hypercube

abbrev Vertex (d : ℕ) := Fin d → Bool

/-- Retain every infected vertex and add the vertices with four or more
infected Hamming-distance-one neighbors at the start of the round. -/
noncomputable def step {d : ℕ} (infected : Finset (Vertex d)) : Finset (Vertex d) := by
  classical
  exact infected ∪ Finset.univ.filter (fun v =>
    4 ≤ (infected.filter (fun w => hammingDist v w = 1)).card)

def Percolates {d : ℕ} (seed : Finset (Vertex d)) : Prop :=
  ∃ rounds : ℕ, (step^[rounds]) seed = Finset.univ

/-- The minimum exists because the full vertex set percolates at round zero. -/
noncomputable def minimumSeed (d : ℕ) : ℕ :=
  sInf {size : ℕ | ∃ seed : Finset (Vertex d), seed.card = size ∧ Percolates seed}

/-- Noel's conjectured exact minimum for four-neighbor bootstrap percolation
on the hypercube. Integer division of the numerator plus 23 by 24 gives its ceiling. -/
theorem main :
    ∀ d : ℕ, 4 ≤ d → d ≠ 5 →
      minimumSeed d = (d * (d ^ 2 + 3 * d + 14) + 23) / 24 + 1 := by
  sorry

end OMA.S_opg_extremal_4_neighbour_bootstrap_percolation_in_the_hypercube
