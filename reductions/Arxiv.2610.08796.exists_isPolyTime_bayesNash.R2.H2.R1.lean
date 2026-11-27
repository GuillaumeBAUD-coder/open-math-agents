import OMAReductions.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2

-- Reduction Arxiv.2610.08796.exists_isPolyTime_bayesNash.R2.H2.R1 of step R2.H2
-- Credit: @paynebrowning
-- Each H becomes its own step once this file is accepted. Proving all of them closes R2.H2.

/-!
Separation of the fixed-threshold (`lam`) equilibrium solver `R2.H2` into:
- `H1`: Computing a valid fixed-threshold equilibrium coverage vector `c` (with `∑ c_t = g.1`)
  in polynomial time — isolating the pure coverage-finding LTU matching core.
- `H2`: Given `(g, lam, c)`, computing a matching attacker strategy profile `p` in polynomial
  time. Once `c` is fixed, every attacker type's best-response set is fixed, so finding `p`
  reduces to a single rational linear feasibility / bipartite transportation problem.
- `H3`: Closure of `IsPolyTime` under `x ↦ (C x, P (x, C x))`.
-/

namespace OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H2_R1

open ComplexityTheory Arxiv.«2610.08796»

/-- Fixed-threshold coverage solver: given a valid game and an achievable defender threshold
`lam`, compute in polynomial time a coverage vector `c` that extends to a fixed-`lam`
equilibrium with total coverage `g.1`. -/
def H1 : Prop :=
  ∃ C : GameInput × ℚ → List ℚ,
    IsPolyTime C ∧
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
      ∃ p : List (List ℚ),
        let cov (t : Fin g.numTargets) := (C (g, lam))[t.val]?.getD 0
        let row (θ : Fin g.numTypes) := p[θ.val]?.getD []
        let atk (θ : Fin g.numTypes) (t : Fin g.numTargets) := (row θ)[t.val]?.getD 0
        let uA (θ : Fin g.numTypes) (t : Fin g.numTargets) :=
          (1 - cov t) * (g.attackerPayoff θ t).1 + cov t * (g.attackerPayoff θ t).2
        let gain (t : Fin g.numTargets) :=
          (∑ θ : Fin g.numTypes, g.prior θ * atk θ t) *
            ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)
        (C (g, lam)).length = g.numTargets ∧ p.length = g.numTypes ∧
        (∑ t, cov t) = (g.1 : ℚ) ∧ (∀ t, 0 ≤ cov t ∧ cov t ≤ 1) ∧
        (∀ θ, (row θ).length = g.numTargets ∧ (∑ t, atk θ t) = 1 ∧ ∀ t, 0 ≤ atk θ t) ∧
        (∀ θ t s, 0 < atk θ t → uA θ s ≤ uA θ t) ∧
        (∀ t, 0 < cov t → lam ≤ gain t) ∧ (∀ t, cov t < 1 → gain t ≤ lam)

/-- Fixed-coverage attack-flow solver: given `(g, lam, x)` where `x` extends to a fixed-`lam`
equilibrium, compute such an attacker strategy profile `p` in polynomial time. -/
def H2 : Prop :=
  ∃ P : (GameInput × ℚ) × List ℚ → List (List ℚ),
    IsPolyTime P ∧
    ∀ (g : GameInput) (lam : ℚ) (x : List ℚ), g.Valid →
      (∃ p : List (List ℚ),
        let cov (t : Fin g.numTargets) := x[t.val]?.getD 0
        let row (θ : Fin g.numTypes) := p[θ.val]?.getD []
        let atk (θ : Fin g.numTypes) (t : Fin g.numTargets) := (row θ)[t.val]?.getD 0
        let uA (θ : Fin g.numTypes) (t : Fin g.numTargets) :=
          (1 - cov t) * (g.attackerPayoff θ t).1 + cov t * (g.attackerPayoff θ t).2
        let gain (t : Fin g.numTargets) :=
          (∑ θ : Fin g.numTypes, g.prior θ * atk θ t) *
            ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)
        x.length = g.numTargets ∧ p.length = g.numTypes ∧
        (∑ t, cov t) = (g.1 : ℚ) ∧ (∀ t, 0 ≤ cov t ∧ cov t ≤ 1) ∧
        (∀ θ, (row θ).length = g.numTargets ∧ (∑ t, atk θ t) = 1 ∧ ∀ t, 0 ≤ atk θ t) ∧
        (∀ θ t s, 0 < atk θ t → uA θ s ≤ uA θ t) ∧
        (∀ t, 0 < cov t → lam ≤ gain t) ∧ (∀ t, cov t < 1 → gain t ≤ lam)) →
      let p := P ((g, lam), x)
      let cov (t : Fin g.numTargets) := x[t.val]?.getD 0
      let row (θ : Fin g.numTypes) := p[θ.val]?.getD []
      let atk (θ : Fin g.numTypes) (t : Fin g.numTargets) := (row θ)[t.val]?.getD 0
      let uA (θ : Fin g.numTypes) (t : Fin g.numTargets) :=
        (1 - cov t) * (g.attackerPayoff θ t).1 + cov t * (g.attackerPayoff θ t).2
      let gain (t : Fin g.numTargets) :=
        (∑ θ : Fin g.numTypes, g.prior θ * atk θ t) *
          ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)
      x.length = g.numTargets ∧ p.length = g.numTypes ∧
      (∑ t, cov t) = (g.1 : ℚ) ∧ (∀ t, 0 ≤ cov t ∧ cov t ≤ 1) ∧
      (∀ θ, (row θ).length = g.numTargets ∧ (∑ t, atk θ t) = 1 ∧ ∀ t, 0 ≤ atk θ t) ∧
      (∀ θ t s, 0 < atk θ t → uA θ s ≤ uA θ t) ∧
      (∀ t, 0 < cov t → lam ≤ gain t) ∧ (∀ t, cov t < 1 → gain t ≤ lam)

/-- Polynomial-time closure under dependent pairing `x ↦ (C x, P (x, C x))`. -/
def H3 : Prop :=
  ∀ (C : GameInput × ℚ → List ℚ) (P : (GameInput × ℚ) × List ℚ → List (List ℚ)),
    IsPolyTime C → IsPolyTime P → IsPolyTime (fun x => (C x, P (x, C x)))

theorem main : H1 → H2 → H3 → OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2.H2 := by
  intro h1 h2 h3
  obtain ⟨C, hC_pt, hC_spec⟩ := h1
  obtain ⟨P, hP_pt, hP_spec⟩ := h2
  refine ⟨fun x => (C x, P (x, C x)), h3 C P hC_pt hP_pt, ?_⟩
  intro g lam hg hex
  exact hP_spec g lam (C (g, lam)) hg (hC_spec g lam hg hex)

end OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H2_R1
