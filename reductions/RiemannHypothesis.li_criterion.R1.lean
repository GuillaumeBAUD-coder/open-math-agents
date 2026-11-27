import FormalConjectures.Paper.RiemannHypothesisEquivalents

-- Reduction RiemannHypothesis.li_criterion.R1 of Li's Criterion
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Li's criterion, split into its two implications

Li's criterion identifies the Riemann Hypothesis with the positivity of the sequence

$$\lambda_n = \sum_\rho \left(1 - \left(1 - \frac{1}{\rho}\right)^n\right),$$

summed over the nontrivial zeros of the Riemann zeta function.

The two implications are proved by completely different means, and it is worth separating them.

* `H1` (the Riemann Hypothesis forces every `λₙ` to be positive) is the direction that goes through
  the explicit formula: under RH one controls the zeros directly and each summand has positive real
  part.
* `H2` (positivity of every `λₙ` forces the Riemann Hypothesis) is the converse, which needs the
  asymptotic analysis of `λₙ` for large `n`: the exponential growth rate of `λₙ` detects whether
  zeros off the critical line exist.

Neither direction is in Mathlib, and neither is a formal consequence of the other. Together they are
the statement, and the assembly is formal.
-/

namespace OMA.R_RiemannHypothesis_li_criterion_R1

/-- The forward direction of Li's criterion: the Riemann Hypothesis implies that every `λₙ` with
`n > 0` is positive. -/
def H1 : Prop :=
  RiemannHypothesis → ∀ n > 0, 0 < RiemannHypothesis.lambda n

/-- The converse direction of Li's criterion: if every `λₙ` with `n > 0` is positive, then the
Riemann Hypothesis holds. -/
def H2 : Prop :=
  (∀ n > 0, 0 < RiemannHypothesis.lambda n) → RiemannHypothesis

theorem main : H1 → H2 → type_of% @RiemannHypothesis.li_criterion := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_RiemannHypothesis_li_criterion_R1
