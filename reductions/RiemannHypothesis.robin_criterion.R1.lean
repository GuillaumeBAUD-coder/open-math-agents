import FormalConjectures.Paper.RiemannHypothesisEquivalents

-- Reduction RiemannHypothesis.robin_criterion.R1 of Robin's criterion
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Robin's criterion, split into its two implications

Robin's criterion identifies the Riemann Hypothesis with an explicit inequality involving the sum of
divisors:

$$\mathrm{RH} \iff \forall n > 5040,\ \sigma_1(n) < e^{\gamma}\, n \log\log n .$$

The two implications are proved by completely different means, and it is worth separating them.

* `H1` is the direction from the Riemann Hypothesis to the inequality.  It is the one that follows
  from an explicit bound for `|ψ(x) - x|` (equivalently from the error term in the prime number
  theorem), transferred to `σ₁` through the hyperbola identity; it needs the zero-free region that RH
  provides, but no asymptotic analysis of `σ₁` itself.
* `H2` is the converse: the inequality for all `n > 5040` forces the Riemann Hypothesis.  Any zero
  off the critical line produces infinitely many `n` for which `σ₁(n)` exceeds the right-hand side
  (Robin's and Lagarias' argument via highly composite `n`), so this direction is a statement about
  the growth of `σ₁` along extremal integers.

Neither direction is in Mathlib, and neither is a formal consequence of the other. Together they are
the statement, and the assembly is formal.
-/

namespace OMA.R_RiemannHypothesis_robin_criterion_R1

open Real
open scoped ArithmeticFunction.sigma

/-- The forward direction of Robin's criterion: the Riemann Hypothesis implies the inequality for
every `n > 5040`. -/
def H1 : Prop :=
  RiemannHypothesis →
    ∀ n > 5040, σ 1 n < (exp eulerMascheroniConstant) * n * log (log n)

/-- The converse direction of Robin's criterion: the inequality for every `n > 5040` implies the
Riemann Hypothesis. -/
def H2 : Prop :=
  (∀ n > 5040, σ 1 n < (exp eulerMascheroniConstant) * n * log (log n)) →
    RiemannHypothesis

theorem main : H1 → H2 → type_of% @RiemannHypothesis.robin_criterion := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_RiemannHypothesis_robin_criterion_R1
