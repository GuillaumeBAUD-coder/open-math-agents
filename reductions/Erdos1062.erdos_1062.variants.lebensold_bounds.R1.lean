import FormalConjectures.ErdosProblems.«1062»

-- Reduction Erdos1062.erdos_1062.variants.lebensold_bounds.R1 of Erdős Problem 1062 — lebensold bounds
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Lebensold's bounds on `f n`, split into the lower and the upper estimate

`f n` is the largest size of a fork-free subset of `{1, …, n}`.  Lebensold proved that for large `n`
the proportion `f n / n` is trapped in `[0.6725, 0.6736]`.

The two sides of that interval are produced by genuinely different arguments — a lower bound by
exhibiting a large fork-free set, an upper bound by bounding every such set — so the conjunction

`∀ᶠ n, 0.6725 * n ≤ f n ∧ f n ≤ 0.6736 * n`

is split into the two halves:

* `H1` is the lower estimate `0.6725 * n ≤ f n`,
* `H2` is the upper estimate `f n ≤ 0.6736 * n`.

Each is an eventual statement on its own, and together they give exactly the original conjunction.
-/

namespace OMA.R_Erdos1062_erdos_1062_variants_lebensold_bounds_R1

open Filter Erdos1062

/-- The lower estimate: eventually `0.6725 * n ≤ f n`. -/
def H1 : Prop :=
  ∀ᶠ n in atTop, (0.6725 : ℝ) * n ≤ f n

/-- The upper estimate: eventually `f n ≤ 0.6736 * n`. -/
def H2 : Prop :=
  ∀ᶠ n in atTop, f n ≤ (0.6736 : ℝ) * n

theorem main : H1 → H2 → type_of% @Erdos1062.erdos_1062.variants.lebensold_bounds := by
  intro h1 h2
  filter_upwards [h1, h2] with n hn1 hn2
  exact ⟨hn1, hn2⟩

end OMA.R_Erdos1062_erdos_1062_variants_lebensold_bounds_R1
