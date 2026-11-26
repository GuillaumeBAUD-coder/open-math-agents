import FormalConjectures.ErdosProblems.«142»

/-!
# Splitting the asymptotic formula for r_3(N)

The answer function is an opaque placeholder in the upstream file, so no
property of it is known.  The asymptotic equivalence is reduced to two
independent analytic statements: eventual non-vanishing of the answer, and
convergence of the ratio to one.
-/

namespace OMA.R_Erdos142_erdos_142_variants_three_R1

open Asymptotics Erdos142 Filter
open scoped Topology

/-- The unknown answer function is eventually nonzero. -/
def H1 : Prop := ∀ᶠ N : ℕ in atTop, erdos_142.variants.three.answer N ≠ 0

/-- The ratio of the maximal progression-free size to the answer tends to one. -/
def H2 : Prop :=
  Tendsto ((fun N : ℕ ↦ (r 3 N : ℝ)) / erdos_142.variants.three.answer) atTop (𝓝 1)

theorem main : H1 → H2 → type_of% @Erdos142.erdos_142.variants.three := by
  intro h1 h2
  exact (isEquivalent_iff_tendsto_one h1).2 h2

end OMA.R_Erdos142_erdos_142_variants_three_R1
