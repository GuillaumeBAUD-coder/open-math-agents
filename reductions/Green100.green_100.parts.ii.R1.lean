import FormalConjectures.GreensOpenProblems.«100»

/-! A finite-relator reduction of Green 100, part II. -/

-- Problem: Green100.green_100.parts.ii
-- Credit: @sobrien032
-- A finite-presentation criterion using Green's normalized Hilbert–Schmidt distance.
-- Gao–Yu–Zhi, arXiv:2610.10248v2, Proposition 4.2, gives a candidate for the second step.

namespace OMA.R_Green100_green_100_parts_ii_R1

/-- A hyperlinear group admits arbitrarily accurate unitary models of any finite
list of relators, with a chosen nonidentity word still separated from the identity. -/
def H1 : Prop :=
  ∀ (k : ℕ) (R : Finset (List (Fin k × Bool))) (w : List (Fin k × Bool))
    (G : Type) [Group G] (s : Fin k → G), Green100.IsHyperlinear G →
    (∀ r ∈ R, FreeGroup.lift s (FreeGroup.mk r) = 1) →
    FreeGroup.lift s (FreeGroup.mk w) ≠ 1 →
    ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (u : Fin k → Matrix.unitaryGroup (Fin n) ℂ),
      (∀ r ∈ R, Green100.hsDist (FreeGroup.lift u (FreeGroup.mk r)) 1 < δ) ∧
      1 / 8 < Green100.hsDist (FreeGroup.lift u (FreeGroup.mk w)) 1

/-- Finite relators and a word that survives in an exact group model but
collapses in every sufficiently accurate unitary model, uniformly in dimension. -/
def H2 : Prop :=
  ∃ (k : ℕ) (R : Finset (List (Fin k × Bool))) (w : List (Fin k × Bool)),
    (∃ (G : Type) (_ : Group G) (s : Fin k → G),
      (∀ r ∈ R, FreeGroup.lift s (FreeGroup.mk r) = 1) ∧
      FreeGroup.lift s (FreeGroup.mk w) ≠ 1) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (u : Fin k → Matrix.unitaryGroup (Fin n) ℂ),
      (∀ r ∈ R, Green100.hsDist (FreeGroup.lift u (FreeGroup.mk r)) 1 < δ) →
      Green100.hsDist (FreeGroup.lift u (FreeGroup.mk w)) 1 ≤ 1 / 8

theorem main : H1 → H2 → type_of% @Green100.green_100.parts.ii := by
  intro models obstruction allGroups
  obtain ⟨k, R, w, ⟨G, inst, s, rel, nontrivial⟩, δ, positive, collapse⟩ := obstruction
  obtain ⟨n, u, approx, separated⟩ :=
    models k R w G s (allGroups G) rel nontrivial δ positive
  exact (not_lt_of_ge (collapse n u approx)) separated

end OMA.R_Green100_green_100_parts_ii_R1
