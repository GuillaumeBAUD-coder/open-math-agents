import FormalConjectures.Paper.RiemannHypothesisEquivalents

-- Reduction RiemannHypothesis.lagarias_criterion.R1 of Lagarias' Criterion
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Lagarias' criterion, split into its two implications

Lagarias' criterion states that the Riemann Hypothesis is equivalent to Robin's inequality holding
in the sharpened form

$$ \sigma(n) < H_n + e^{H_n} \log H_n \qquad (n > 1), $$

where `H_n` is the `n`-th harmonic number and `σ 1 n` is the sum of the divisors of `n`.

The two implications are proved by different means and it is worth separating them.

* `H1` (the Riemann Hypothesis implies the inequality) is the direction proved from the explicit
  formula together with the known bounds for the error term in the prime number theorem; it is the
  direction that yields Robin's inequality under RH.
* `H2` (the inequality implies the Riemann Hypothesis) is the converse, which needs the analysis of
  hypothetical zeros off the critical line: a zero with real part greater than `1/2` produces
  values of `n` for which the inequality fails.

Neither direction is in Mathlib, and neither follows formally from the other. Together they are the
statement, and the assembly is formal.
-/

namespace OMA.R_RiemannHypothesis_lagarias_criterion_R1

open Real MeasureTheory
open scoped ArithmeticFunction.sigma

/-- The forward direction of Lagarias' criterion: the Riemann Hypothesis implies Robin's inequality
in Lagarias' sharpened form, for every `n > 1`. -/
def H1 : Prop :=
  RiemannHypothesis →
    ∀ n > 1, σ 1 n < harmonic n + exp (harmonic n) * log (harmonic n)

/-- The converse direction of Lagarias' criterion: Lagarias' inequality for every `n > 1` implies
the Riemann Hypothesis. -/
def H2 : Prop :=
  (∀ n > 1, σ 1 n < harmonic n + exp (harmonic n) * log (harmonic n)) → RiemannHypothesis

theorem main : H1 → H2 → type_of% @RiemannHypothesis.lagarias_criterion := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_RiemannHypothesis_lagarias_criterion_R1
