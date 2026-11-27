import FormalConjectures.ErdosProblems.«813»

/-!
# Reduction of the Erdős–Hajnal bounds on `h(n)`

The target is a conjunction of two independent asymptotic bounds, `n^{1/3} ≪ h(n)` and
`h(n) ≪ n^{1/2}`. Erdős and Hajnal prove them by different arguments, so each bound is a
separate step.
-/

-- Reduction Erdos813.erdos_813.variants.erdos_hajnal.R1 of Erdős Problem 813
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos813_erdos_813_variants_erdos_hajnal_R1

/-- The lower bound `n^{1/3} ≪ h(n)`. -/
def H1 : Prop :=
  Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ))
    (fun n => (Erdos813.h n : ℝ))

/-- The upper bound `h(n) ≪ n^{1/2}`. -/
def H2 : Prop :=
  Asymptotics.IsBigO Filter.atTop (fun n => (Erdos813.h n : ℝ))
    (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ))

theorem main : H1 → H2 → type_of% @Erdos813.erdos_813.variants.erdos_hajnal := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_Erdos813_erdos_813_variants_erdos_hajnal_R1
