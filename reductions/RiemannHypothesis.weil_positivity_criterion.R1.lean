import FormalConjectures.Paper.RiemannHypothesisEquivalents

-- Reduction RiemannHypothesis.weil_positivity_criterion.R1 of the Weil positivity criterion
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The Weil positivity criterion, split into its two implications

Weil's criterion identifies the Riemann Hypothesis with the positivity of the Weil functional on
test functions: for every `g` in `C_c(ℝ, ℝ)` with `ContDiff ℝ ∞ g` and `IsTestFunction g`,

$$W(g) = W_\infty\bigl(g \star \tilde g\bigr) + \sum_p W_p\bigl(g \star \tilde g\bigr) \le 0 .$$

The two implications are proved by completely different means, and it is worth separating them.

* `H1` (the Riemann Hypothesis implies the inequality) goes through the explicit formula: when RH
  holds, the Weil functional is a sum of positive terms indexed by the zeros on the critical line,
  which gives the sign directly.
* `H2` (the inequality for every test function implies the Riemann Hypothesis) is the converse and
  is the hard direction of Weil's criterion: a zero off the critical line produces a test function
  for which the functional becomes positive, by a careful choice of `g` concentrated on that zero
  (Weil's positivity argument, in the form of the Bombieri–Weil explicit formula).

Neither direction is in Mathlib, and neither is a formal consequence of the other. Together they are
the statement, and the assembly is formal.
-/

open Real MeasureTheory
open scoped ArithmeticFunction.sigma CompactlySupported Convolution ContDiff
open RiemannHypothesis

namespace OMA.R_RiemannHypothesis_weil_positivity_criterion_R1

/-- The forward direction of Weil's criterion: the Riemann Hypothesis implies the positivity
inequality for every test function. -/
def H1 : Prop :=
  RiemannHypothesis →
    ∀ g : C_c(ℝ, ℝ), ContDiff ℝ ∞ g → IsTestFunction g →
      weilArchimedean (g ⋆ fun x ↦ g (-x)) +
        ∑' p : Nat.Primes, weilNonArchimedean p (g ⋆ fun x ↦ g (-x)) ≤ 0

/-- The converse direction of Weil's criterion: the positivity inequality for every test function
implies the Riemann Hypothesis. -/
def H2 : Prop :=
  (∀ g : C_c(ℝ, ℝ), ContDiff ℝ ∞ g → IsTestFunction g →
      weilArchimedean (g ⋆ fun x ↦ g (-x)) +
        ∑' p : Nat.Primes, weilNonArchimedean p (g ⋆ fun x ↦ g (-x)) ≤ 0) →
    RiemannHypothesis

theorem main : H1 → H2 → type_of% @RiemannHypothesis.weil_positivity_criterion := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_RiemannHypothesis_weil_positivity_criterion_R1
