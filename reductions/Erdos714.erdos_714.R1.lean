import FormalConjectures.ErdosProblems.«714»

-- Reduction Erdos714.erdos_714.R1 of Erdős Problem 714
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 714: the known cases `r = 2, 3` and the open part `r ≥ 4`

The claim is `ex(n; K_{r,r}) ≫ n^{2 - 1/r}` for every `r ≥ 2`. No implication runs between
different `r`, so the cases split cleanly:

* `H1` (`r = 2`): `ex(n; C₄) ≫ n^{3/2}`. Known (Erdős–Rényi–Sós 1966, Brown 1966): the polarity
  graph of the projective plane over `𝔽_q` has `q² + q + 1` vertices, about `q³/2` edges and no
  `C₄`; Bertrand-type prime gaps give all `n`. A known theorem not yet in Mathlib.
* `H2` (`r = 3`): `ex(n; K_{3,3}) ≫ n^{5/3}`. Known (Brown 1966): points of `𝔽_p³`, adjacent when
  their distance is a fixed quadratic non-residue (unit spheres meet in at most two points).
  A known theorem not yet in Mathlib.
* `H3` (`r ≥ 4`): the open part (norm graphs give `K_{r,s}` only for `s > (r-1)!`).
-/

namespace OMA.R_Erdos714_erdos_714_R1

open Filter SimpleGraph

/-- `r = 2`: Erdős–Rényi–Sós / Brown (polarity graphs). -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    c * (n : ℝ) ^ ((2 : ℝ) - 1 / (2 : ℝ)) ≤
      (extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) : ℝ)

/-- `r = 3`: Brown's construction. -/
def H2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    c * (n : ℝ) ^ ((2 : ℝ) - 1 / (3 : ℝ)) ≤
      (extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3)) : ℝ)

/-- `r ≥ 4`: open. -/
def H3 : Prop :=
  ∀ r : ℕ, 4 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
      (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ)

theorem main : H1 → H2 → H3 → type_of% @Erdos714.erdos_714 := by
  intro h1 h2 h3 r hr
  by_cases hr2 : r = 2
  · subst hr2
    simpa [H1] using h1
  by_cases hr3 : r = 3
  · subst hr3
    simpa [H2] using h2
  exact h3 r (by omega)

end OMA.R_Erdos714_erdos_714_R1
