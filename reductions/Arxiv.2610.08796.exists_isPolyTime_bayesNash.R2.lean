import FormalConjectures.Arxiv.«2610.08796».BayesianSecurityGames

-- Reduction Arxiv.2610.08796.exists_isPolyTime_bayesNash.R2 of Computing Bayes–Nash equilibria in Bayesian simple security games
-- Credit: @paynebrowning
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Fixed-threshold (LTU matching) decomposition of Bayesian simple security games.

In a Bayes–Nash equilibrium, the defender's best-response condition
`∀ t s, 0 < coverage t → coverage s < 1 → coverageGain s ≤ coverageGain t`
is equivalent to the existence of a single rational threshold `lam : ℚ` such that
`0 < coverage t → lam ≤ coverageGain t` and `coverage s < 1 → coverageGain s ≤ lam`.
For a fixed threshold `lam`, the remaining conditions are a Linearly Transferable Utility (LTU)
matching problem with price caps `c_t ∈ [0, 1]` and target supplies `lam / (covered - uncovered)`.

* `H1`: Closure of `IsPolyTime` under `g ↦ F (g, Λ g)` for `Λ : GameInput → ℚ` and
  `F : GameInput × ℚ → EquilibriumOutput`.
* `H2`: Given a valid game `g` and a valid equilibrium defender threshold `lam : ℚ`,
  compute a fixed-threshold equilibrium of `g` with total coverage `g.1` in polynomial time.
* `H3`: Compute a valid rational equilibrium defender threshold `Λ g : ℚ` for every valid game `g`
  in polynomial time.
-/

namespace OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2

open ComplexityTheory Arxiv.«2610.08796»

/-- Polynomial time is closed under pairing with a rational threshold `g ↦ F (g, Λ g)`. -/
def H1 : Prop :=
  ∀ (Λ : GameInput → ℚ) (F : GameInput × ℚ → EquilibriumOutput),
    IsPolyTime Λ → IsPolyTime F → IsPolyTime (fun g => F (g, Λ g))

/-- Fixed-threshold (LTU matching) equilibrium solver: from a valid game and an achievable
defender marginal-gain threshold, compute an equilibrium at that threshold in polynomial time. -/
def H2 : Prop :=
  ∃ F : GameInput × ℚ → EquilibriumOutput,
    IsPolyTime F ∧
    ∀ (g : GameInput) (lam : ℚ), g.Valid →
      (∃ e : EquilibriumOutput,
        let cov (t : Fin g.numTargets) := e.1[t.val]?.getD 0
        let row (θ : Fin g.numTypes) := e.2[θ.val]?.getD []
        let atk (θ : Fin g.numTypes) (t : Fin g.numTargets) := (row θ)[t.val]?.getD 0
        let uA (θ : Fin g.numTypes) (t : Fin g.numTargets) :=
          (1 - cov t) * (g.attackerPayoff θ t).1 + cov t * (g.attackerPayoff θ t).2
        let gain (t : Fin g.numTargets) :=
          (∑ θ : Fin g.numTypes, g.prior θ * atk θ t) *
            ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)
        e.1.length = g.numTargets ∧ e.2.length = g.numTypes ∧
        (∑ t, cov t) = (g.1 : ℚ) ∧ (∀ t, 0 ≤ cov t ∧ cov t ≤ 1) ∧
        (∀ θ, (row θ).length = g.numTargets ∧ (∑ t, atk θ t) = 1 ∧ ∀ t, 0 ≤ atk θ t) ∧
        (∀ θ t s, 0 < atk θ t → uA θ s ≤ uA θ t) ∧
        (∀ t, 0 < cov t → lam ≤ gain t) ∧ (∀ t, cov t < 1 → gain t ≤ lam)) →
      let e := F (g, lam)
      let cov (t : Fin g.numTargets) := e.1[t.val]?.getD 0
      let row (θ : Fin g.numTypes) := e.2[θ.val]?.getD []
      let atk (θ : Fin g.numTypes) (t : Fin g.numTargets) := (row θ)[t.val]?.getD 0
      let uA (θ : Fin g.numTypes) (t : Fin g.numTargets) :=
        (1 - cov t) * (g.attackerPayoff θ t).1 + cov t * (g.attackerPayoff θ t).2
      let gain (t : Fin g.numTargets) :=
        (∑ θ : Fin g.numTypes, g.prior θ * atk θ t) *
          ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)
      e.1.length = g.numTargets ∧ e.2.length = g.numTypes ∧
      (∑ t, cov t) = (g.1 : ℚ) ∧ (∀ t, 0 ≤ cov t ∧ cov t ≤ 1) ∧
      (∀ θ, (row θ).length = g.numTargets ∧ (∑ t, atk θ t) = 1 ∧ ∀ t, 0 ≤ atk θ t) ∧
      (∀ θ t s, 0 < atk θ t → uA θ s ≤ uA θ t) ∧
      (∀ t, 0 < cov t → lam ≤ gain t) ∧ (∀ t, cov t < 1 → gain t ≤ lam)

/-- Rational defender threshold computation: a polynomial-time map returns an achievable
equilibrium defender marginal-gain threshold for every valid game. -/
def H3 : Prop :=
  ∃ Λ : GameInput → ℚ,
    IsPolyTime Λ ∧
    ∀ g : GameInput, g.Valid →
      ∃ e : EquilibriumOutput,
        let cov (t : Fin g.numTargets) := e.1[t.val]?.getD 0
        let row (θ : Fin g.numTypes) := e.2[θ.val]?.getD []
        let atk (θ : Fin g.numTypes) (t : Fin g.numTargets) := (row θ)[t.val]?.getD 0
        let uA (θ : Fin g.numTypes) (t : Fin g.numTargets) :=
          (1 - cov t) * (g.attackerPayoff θ t).1 + cov t * (g.attackerPayoff θ t).2
        let gain (t : Fin g.numTargets) :=
          (∑ θ : Fin g.numTypes, g.prior θ * atk θ t) *
            ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)
        e.1.length = g.numTargets ∧ e.2.length = g.numTypes ∧
        (∑ t, cov t) = (g.1 : ℚ) ∧ (∀ t, 0 ≤ cov t ∧ cov t ≤ 1) ∧
        (∀ θ, (row θ).length = g.numTargets ∧ (∑ t, atk θ t) = 1 ∧ ∀ t, 0 ≤ atk θ t) ∧
        (∀ θ t s, 0 < atk θ t → uA θ s ≤ uA θ t) ∧
        (∀ t, 0 < cov t → Λ g ≤ gain t) ∧ (∀ t, cov t < 1 → gain t ≤ Λ g)

theorem main : H1 → H2 → H3 → type_of% @Arxiv.«2610.08796».exists_isPolyTime_bayesNash := by
  intro h1 h2 h3
  obtain ⟨F, hF, hFeq⟩ := h2
  obtain ⟨Λ, hΛ, hΛeq⟩ := h3
  refine ⟨fun g => F (g, Λ g), h1 Λ F hΛ hF, fun g hg => ?_⟩
  have hres := hFeq g (Λ g) hg (hΛeq g hg)
  rcases hres with ⟨hl1, hl2, hsum, hcov, hatk, hbrA, hge, hle⟩
  refine ⟨hl1, hl2, hsum, hcov, hatk, hbrA, fun t s ht hs => ?_⟩
  exact le_trans (hle s hs) (hge t ht)

end OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2
