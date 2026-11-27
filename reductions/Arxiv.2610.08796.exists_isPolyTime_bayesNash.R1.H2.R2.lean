import OMAReductions.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1

-- Reduction Arxiv.2610.08796.exists_isPolyTime_bayesNash.R1.H2.R2 of step R1.H2
-- Credit: @paynebrowning
-- Each H becomes its own step once this file is accepted. Proving all of them closes R1.H2.

/-!
Decoupled rational LP reduction of `R1.H2` (computing a Bayes–Nash equilibrium from an exact
equilibrium pattern `S = (posCov, ltOneCov, posAtk)`), correcting the binary-`ℕ` dimension
encoding bug in `R1.H2.R1.H1`.

Because `BitstringEncoding ℕ` is binary (`O(log n)` bits), an unconstrained solver taking
`(n, []) : ℕ × List (List ℚ × ℚ)` would be required to output a length-`n` list in
`poly(log n)` time, which is impossible. Requiring every constraint row to have length `n`
together with `n = 0 ∨ cons ≠ []` bounds `n` linearly by the bit-length of `cons`, restoring
Khachiyan's exact rational LP feasibility theorem in `IsPolyTime`.

For a fixed pattern `S`, the equilibrium constraints decouple completely into two independent
well-formed rational linear inequality systems `A x ≤ b`:
- a coverage LP in `m = g.numTargets` variables `c_t` enforcing `0 ≤ c_t ≤ 1`, boundary pins
  `c_t = 0` (`¬posCov[t]`) and `c_t = 1` (`¬ltOneCov[t]`), `∑ c_t = g.1`, and attacker
  best-response inequalities `uA(θ, s, c) ≤ uA(θ, t, c)` for `posAtk[θ][t]`;
- an attack LP in `n * m` variables `p_{θ,t}` enforcing `p_{θ,t} ≥ 0`, `p_{θ,t} = 0`
  (`¬posAtk[θ][t]`), `∑_t p_{θ,t} = 1`, and defender exchange inequalities
  `gain(s, p) ≤ gain(t, p)` for `posCov[t] ∧ ltOneCov[s]`.

* `H1`: General exact rational LP feasibility in `IsPolyTime` (Khachiyan's theorem) for
  well-formed systems `(n, cons)` whose constraint rows have length `n` (with `n = 0 ∨ cons ≠ []`).
* `H2`: Polynomial-time construction of the two decoupled rational LPs from `(g, S)`, together
  with row-length well-formedness, completeness, and soundness relative to `g.IsBayesNash`.
* `H3`: Polynomial-time composition, pairing, and reshaping of the flat `n * m` attack solution
  vector into `n` rows of length `m` (identical to `R1.H2.R1.H3`).
-/

namespace OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1_H2_R2

open ComplexityTheory Arxiv.«2610.08796»

/-- Exact rational linear programming feasibility is computable in polynomial time:
given `(n, cons)` representing `∑_j a_j x_j ≤ b` for `(a, b) ∈ cons`, where every row has
length `n` and `n = 0 ∨ cons ≠ []` (so `n` is bounded by the bit-length of the input), if a
feasible `x ∈ ℚ^n` exists, `lpSolve (n, cons)` returns one. -/
def H1 : Prop :=
  ∃ lpSolve : (ℕ × List (List ℚ × ℚ)) → List ℚ,
    IsPolyTime lpSolve ∧
    ∀ (n : ℕ) (cons : List (List ℚ × ℚ)),
      (∀ r ∈ cons, r.1.length = n) → (n = 0 ∨ cons ≠ []) →
      (∃ x : List ℚ, x.length = n ∧
        ∀ r ∈ cons, (∑ j : Fin n, r.1[j.val]?.getD 0 * x[j.val]?.getD 0) ≤ r.2) →
      (lpSolve (n, cons)).length = n ∧
      ∀ r ∈ cons, (∑ j : Fin n, r.1[j.val]?.getD 0 * (lpSolve (n, cons))[j.val]?.getD 0) ≤ r.2

/-- Polynomial-time construction of the decoupled defender-coverage LP and attacker-strategy LP
from `(g, S)`, with row-length well-formedness, completeness from any exact-pattern equilibrium,
and soundness to `g.IsBayesNash`. -/
def H2 : Prop :=
  ∃ bC bP : GameInput × (List Bool × List Bool × List (List Bool)) → ℕ × List (List ℚ × ℚ),
    IsPolyTime bC ∧ IsPolyTime bP ∧
    ∀ (g : GameInput) (S : List Bool × List Bool × List (List Bool)), g.Valid →
      let lpC := bC (g, S)
      let lpP := bP (g, S)
      (∀ r ∈ lpC.2, r.1.length = lpC.1) ∧ (lpC.1 = 0 ∨ lpC.2 ≠ []) ∧
      (∀ r ∈ lpP.2, r.1.length = lpP.1) ∧ (lpP.1 = 0 ∨ lpP.2 ≠ []) ∧
      ((∃ e : EquilibriumOutput, g.IsBayesNash e ∧
        ∀ t : Fin g.numTargets,
          (S.1[t.val]?.getD false = true ↔ 0 < e.1[t.val]?.getD 0) ∧
          (S.2.1[t.val]?.getD false = true ↔ e.1[t.val]?.getD 0 < 1) ∧
          ∀ θ : Fin g.numTypes,
            ((S.2.2[θ.val]?.getD [])[t.val]?.getD false = true ↔
              0 < (e.2[θ.val]?.getD [])[t.val]?.getD 0)) →
        (∃ x : List ℚ, x.length = lpC.1 ∧
          ∀ r ∈ lpC.2, (∑ j : Fin lpC.1, r.1[j.val]?.getD 0 * x[j.val]?.getD 0) ≤ r.2) ∧
        (∃ y : List ℚ, y.length = lpP.1 ∧
          ∀ r ∈ lpP.2, (∑ j : Fin lpP.1, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2)) ∧
      (∀ x y : List ℚ,
        x.length = lpC.1 →
        (∀ r ∈ lpC.2, (∑ j : Fin lpC.1, r.1[j.val]?.getD 0 * x[j.val]?.getD 0) ≤ r.2) →
        y.length = lpP.1 →
        (∀ r ∈ lpP.2, (∑ j : Fin lpP.1, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) →
        g.IsBayesNash (x, List.ofFn fun θ : Fin g.numTypes =>
          List.ofFn fun t : Fin g.numTargets => y[θ.val * g.numTargets + t.val]?.getD 0))

/-- Polynomial-time composition, pairing, and flat-to-2D list reshaping for the two LP calls. -/
def H3 : Prop :=
  ∀ (bC bP : GameInput × (List Bool × List Bool × List (List Bool)) → ℕ × List (List ℚ × ℚ))
    (lpSolve : ℕ × List (List ℚ × ℚ) → List ℚ),
    IsPolyTime bC → IsPolyTime bP → IsPolyTime lpSolve →
    IsPolyTime (fun x : GameInput × (List Bool × List Bool × List (List Bool)) =>
      (lpSolve (bC x), List.ofFn fun θ : Fin x.1.numTypes =>
        List.ofFn fun t : Fin x.1.numTargets =>
          (lpSolve (bP x))[θ.val * x.1.numTargets + t.val]?.getD 0))

theorem main : H1 → H2 → H3 → OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1.H2 := by
  intro h1 h2 h3
  obtain ⟨lpSolve, hlp_pt, hlp_spec⟩ := h1
  obtain ⟨bC, bP, hbC_pt, hbP_pt, hspec⟩ := h2
  refine ⟨fun x =>
    (lpSolve (bC x), List.ofFn fun θ : Fin x.1.numTypes =>
      List.ofFn fun t : Fin x.1.numTargets =>
        (lpSolve (bP x))[θ.val * x.1.numTargets + t.val]?.getD 0),
    h3 bC bP lpSolve hbC_pt hbP_pt hlp_pt, ?_⟩
  intro g S hg hpat
  obtain ⟨hCrows, hCne, hProws, hPne, hcomp, hsound⟩ := hspec g S hg
  obtain ⟨hCfeas, hPfeas⟩ := hcomp hpat
  obtain ⟨hClen, hCsat⟩ := hlp_spec (bC (g, S)).1 (bC (g, S)).2 hCrows hCne hCfeas
  obtain ⟨hPlen, hPsat⟩ := hlp_spec (bP (g, S)).1 (bP (g, S)).2 hProws hPne hPfeas
  exact hsound (lpSolve (bC (g, S))) (lpSolve (bP (g, S))) hClen hCsat hPlen hPsat

end OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1_H2_R2
