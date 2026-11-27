import FormalConjectures.Paper.DisjointNPPairs

/-! The Cook-Levin theorem gives a complete disjoint NP pair when NP equals coNP.
The CNF encoding follows Dominic Breuker. The pair construction follows Glaßer, Selman,
Sengupta and Zhang and the account of Pudlák cited by the upstream problem.
Credit: @TheWaler -/

open ComplexityTheory DisjointNPPairs

namespace OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1

-- The bit format follows Dominic Breuker, CookLevin/SAT/EvalCnfCmd.lean.
-- Each literal carries a sign bit and a unary index, and false terminates a clause.
-- The two obligations are the membership and hardness halves of Cook-Levin.
def H1 : Prop :=
  ∃ C : DecisionProblem, C ∈ NP ∧ ∀ input, C input = true ↔
      ∃ (formula : List (List (Bool × ℕ))) (assignment : ℕ → Bool),
        input = formula.flatMap (fun clause =>
          clause.flatMap (fun lit => [true, lit.1] ++ List.replicate lit.2 true ++ [false]) ++ [false]) ∧
        ∀ clause ∈ formula, ∃ lit ∈ clause, assignment lit.2 = lit.1

def H2 : Prop :=
  ∀ A ∈ NP, ∃ f : List Bool → List Bool, IsPolyTime f ∧ ∀ x, A x = true ↔
      ∃ (formula : List (List (Bool × ℕ))) (assignment : ℕ → Bool),
        (f x) = formula.flatMap (fun clause =>
          clause.flatMap (fun lit => [true, lit.1] ++ List.replicate lit.2 true ++ [false]) ++ [false]) ∧
        ∀ clause ∈ formula, ∃ lit ∈ clause, assignment lit.2 = lit.1

theorem main : H1 → H2 → type_of% @DisjointNPPairs.no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP := by
  intro membership hardness eqClasses
  obtain ⟨C, memC, sat⟩ := membership
  have memCompl : Cᶜ ∈ NP := by
    have h : C ∈ coNP := eqClasses ▸ memC
    exact h
  refine ⟨C, Cᶜ, ⟨memC, memCompl, ?_⟩, ?_⟩
  · intro x hx
    have hneg := hx.2
    change (!(C x)) = true at hneg
    simp [hx.1] at hneg
  · intro A B pair
    obtain ⟨f, poly, correct⟩ := hardness A pair.memA
    refine ⟨f, poly, fun x hx => (sat (f x)).mpr ((correct x).mp hx), ?_⟩
    intro x hx
    change (!(C (f x))) = true
    cases hc : C (f x) with
    | false => rfl
    | true => exact False.elim (pair.disjoint x ⟨(correct x).mpr ((sat (f x)).mp hc), hx⟩)

end OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1
