import FormalConjectures.ErdosProblems.«813»

-- Reduction Erdos813.erdos_813.variants.bucic_sudakov.R1 of Erdős Problem 813 — bucic sudakov
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Bucić–Sudakov, split at the exponent `5/12`

`h n` is the least clique number of a graph on `n` vertices in which every `7` vertices contain a
triangle (equivalently, in the complement, every `7` vertices contain an independent set of size
`3`).  Bucić and Sudakov prove `h n ≫ n^{5/12 - o(1)}`, stated here as
`∀ ε > 0, ∀ᶠ n, n^{5/12 - ε} ≤ h n`.

The quantifier over `ε` splits into two ranges in which the two sides of the inequality behave very
differently:

* `H1` is the range `ε ≥ 5/12`, where the exponent `5/12 - ε` is non-positive, so `n^{5/12 - ε}` is
  bounded by `1` for `n ≥ 1` and it suffices to know that `h n` is at least `1` — the trivial
  counting bound coming from the graph itself.  No probabilistic construction is needed.
* `H2` is the range `0 < ε < 5/12`, where the exponent is positive and the whole strength of the
  Bucić–Sudakov argument (their `n^{5/12 - o(1)}` lower bound) is required.

Splitting the exponent range isolates the regime where the estimate is essentially free from the
regime where the construction has to be used.
-/

namespace OMA.R_Erdos813_erdos_813_variants_bucic_sudakov_R1

open Filter Erdos813

/-- The regime `ε ≥ 5/12`: the exponent `5/12 - ε` is non-positive. -/
def H1 : Prop :=
  ∀ ε : ℝ, 5 / 12 ≤ ε → ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (5 / 12 - ε : ℝ) ≤ (h n : ℝ)

/-- The regime `0 < ε < 5/12`: the exponent is positive, so this is the real content. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 5 / 12 → ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (5 / 12 - ε : ℝ) ≤ (h n : ℝ)

theorem main : H1 → H2 → type_of% @Erdos813.erdos_813.variants.bucic_sudakov := by
  intro h1 h2 ε hε
  by_cases hlt : ε < 5 / 12
  · exact h2 ε hε hlt
  · exact h1 ε (le_of_not_gt hlt)

end OMA.R_Erdos813_erdos_813_variants_bucic_sudakov_R1
