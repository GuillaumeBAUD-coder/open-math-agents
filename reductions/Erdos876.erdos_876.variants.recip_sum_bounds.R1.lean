import FormalConjectures.ErdosProblems.«876»

/-!
# Reduction `Erdos876.erdos_876.variants.recip_sum_bounds`

`R = maxRecipSum` is the supremum of `sum over a in A of 1 / a` over infinite sum-free sets
`A` (Erdős's sense: no element is a sum of distinct smaller elements of `A`). The target is the
pair of numerical bounds on `R` proved by Levine and O'Sullivan [LeOS77] and Abbott [Ab87].

The target is a conjunction of two independent bounds, and the split below is exactly those two
bounds. The lower bound is a construction (an explicit infinite sum-free set whose reciprocal sum
exceeds `2.064`); the upper bound is an argument of Levine and O'Sullivan that no sum-free set
does better than `4`. Neither follows from the other, so each is a genuine separate obligation.
-/

-- Reduction Erdos876.erdos_876.variants.recip_sum_bounds.R1
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos876_erdos_876_variants_recip_sum_bounds_R1

/-- The lower bound of Abbott [Ab87]: `R` is bigger than `2.064`. -/
def H1 : Prop := (2.064 : ℝ) < Erdos876.maxRecipSum

/-- The upper bound of Levine and O'Sullivan [LeOS77]: `R` is smaller than `4`. -/
def H2 : Prop := Erdos876.maxRecipSum < 4

theorem main : H1 → H2 →
    type_of% @Erdos876.erdos_876.variants.recip_sum_bounds := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_Erdos876_erdos_876_variants_recip_sum_bounds_R1
