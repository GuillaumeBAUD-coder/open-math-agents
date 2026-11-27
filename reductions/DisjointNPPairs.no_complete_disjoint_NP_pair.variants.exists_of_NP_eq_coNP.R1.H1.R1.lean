import OMAReductions.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1
import Mathlib

/-! NP membership of unary CNF satisfiability splits into verification of a
given finite bit assignment and the bound on the amount of assignment needed. -/
-- Credit: @marcusbuffett

open ComplexityTheory
namespace OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1_H1_R1

/-- The deterministic verifier checks the syntax and tests every clause against
the supplied finite assignment. Positions past the end default to false. -/
def H1 : Prop :=
  ∃ R : (List Bool × List Bool) → Bool, IsPolyTime R ∧ ∀ x w, R (x,w) = true ↔
    ∃ F : List (List (Bool × ℕ)),
      x = F.flatMap (fun c => c.flatMap (fun t => [true,t.1] ++ List.replicate t.2 true ++ [false]) ++ [false]) ∧
      ∀ c ∈ F, ∃ t ∈ c, (w[t.2]?).getD false = t.1

/-- Every assignment can be truncated to an input-length witness without
changing the value of any literal in the formula. -/
def H2 : Prop :=
  ∀ (F : List (List (Bool × ℕ))) (a : ℕ → Bool), ∃ w : List Bool,
    w.length ≤ (F.flatMap (fun c => c.flatMap (fun t => [true,t.1] ++ List.replicate t.2 true ++ [false]) ++ [false])).length ∧
    ∀ c ∈ F, ∀ t ∈ c, (w[t.2]?).getD false = a t.2

theorem main : H1 → H2 → OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1.H1 := by
  classical
  rintro ⟨R,poly,verify⟩ restrict
  let C : DecisionProblem := fun x => decide (∃ w : List Bool, w.length ≤ x.length ∧ R (x,w) = true)
  refine ⟨C,⟨Polynomial.X,R,poly,fun x => by simp [C]⟩,?_⟩
  intro x
  simp only [C,decide_eq_true_iff]
  constructor
  · rintro ⟨w,_,hw⟩
    obtain ⟨F,hx,hF⟩ := (verify x w).mp hw
    exact ⟨F,fun i => (w[i]?).getD false,hx,hF⟩
  · rintro ⟨F,a,rfl,hF⟩
    obtain ⟨w,hw,matchLit⟩ := restrict F a
    refine ⟨w,hw,(verify _ w).mpr ⟨F,rfl,?_⟩⟩
    intro c hc
    obtain ⟨t,ht,ha⟩ := hF c hc
    exact ⟨t,ht,(matchLit c hc t ht).trans ha⟩

end OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1_H1_R1
