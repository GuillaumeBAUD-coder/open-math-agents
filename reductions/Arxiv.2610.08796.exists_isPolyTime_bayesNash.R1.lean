import FormalConjectures.Arxiv.«2610.08796».BayesianSecurityGames

-- Reduction Arxiv.2610.08796.exists_isPolyTime_bayesNash.R1 of Computing Bayes–Nash equilibria in Bayesian simple security games
-- Credit: @tatashbar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
The split separates the open combinatorial core from two pieces that are true but not formalized.

A *pattern* `S : List Bool × List Bool × List (List Bool)` records, for an output `e`,
which targets have positive coverage (`S.1`), which have coverage below one (`S.2.1`), and,
for each attacker type, which targets it attacks with positive probability (`S.2.2`).
`e` *has pattern* `S` when each of these bits is exactly the truth value of the
corresponding strict inequality.

* `H1` (closure of polynomial time): `x ↦ h (x, f x)` is polynomial time when `f` and `h` are.
* `H2` (from a pattern to an equilibrium): the outputs with a fixed exact pattern that are
  Bayes–Nash equilibria form a polyhedron cut out by linear constraints (fix the zero and full
  coverages and the zero attack probabilities, impose the best-response inequalities on the
  supports and the exchange inequalities between the positive and the non-full targets; every
  point of that polyhedron is an equilibrium, and an equilibrium with the pattern lies in it).
  So exact rational linear programming finds an equilibrium from a pattern that some equilibrium has.
* `H3` (the open core): an equilibrium pattern can be found in polynomial time.
-/

namespace OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1

open ComplexityTheory Arxiv.«2610.08796»

/-- Polynomial time is closed under `x ↦ h (x, f x)`. -/
def H1 : Prop :=
  ∀ {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
    (f : α → β) (h : α × β → γ),
    IsPolyTime f → IsPolyTime h → IsPolyTime (fun x => h (x, f x))

/-- From an exact equilibrium pattern, an equilibrium can be computed in polynomial time. -/
def H2 : Prop :=
  ∃ F : GameInput × (List Bool × List Bool × List (List Bool)) → EquilibriumOutput,
    IsPolyTime F ∧
    ∀ (g : GameInput) (S : List Bool × List Bool × List (List Bool)), g.Valid →
      (∃ e : EquilibriumOutput, g.IsBayesNash e ∧
        ∀ t : Fin g.numTargets,
          (S.1[t.val]?.getD false = true ↔ 0 < e.1[t.val]?.getD 0) ∧
          (S.2.1[t.val]?.getD false = true ↔ e.1[t.val]?.getD 0 < 1) ∧
          ∀ θ : Fin g.numTypes,
            ((S.2.2[θ.val]?.getD [])[t.val]?.getD false = true ↔
              0 < (e.2[θ.val]?.getD [])[t.val]?.getD 0)) →
      g.IsBayesNash (F (g, S))

/-- The open core: some polynomial-time map returns the exact pattern of an equilibrium. -/
def H3 : Prop :=
  ∃ σ : GameInput → List Bool × List Bool × List (List Bool),
    IsPolyTime σ ∧
    ∀ g : GameInput, g.Valid →
      ∃ e : EquilibriumOutput, g.IsBayesNash e ∧
        ∀ t : Fin g.numTargets,
          ((σ g).1[t.val]?.getD false = true ↔ 0 < e.1[t.val]?.getD 0) ∧
          ((σ g).2.1[t.val]?.getD false = true ↔ e.1[t.val]?.getD 0 < 1) ∧
          ∀ θ : Fin g.numTypes,
            (((σ g).2.2[θ.val]?.getD [])[t.val]?.getD false = true ↔
              0 < (e.2[θ.val]?.getD [])[t.val]?.getD 0)

theorem main : H1 → H2 → H3 → type_of% @Arxiv.«2610.08796».exists_isPolyTime_bayesNash := by
  intro h1 h2 h3
  obtain ⟨F, hF, hFeq⟩ := h2
  obtain ⟨σ, hσ, hσeq⟩ := h3
  refine ⟨fun g => F (g, σ g), h1 σ F hσ hF, fun g hg => ?_⟩
  obtain ⟨e, he, hpat⟩ := hσeq g hg
  exact hFeq g (σ g) hg ⟨e, he, hpat⟩

end OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1
