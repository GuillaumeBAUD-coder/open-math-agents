/-
Four cuts for the three-agent demand multiset (1,2,4)/7.
Source: Erel Segal-Halevi, Cake-Cutting with Different Entitlements,
arXiv:1803.05470v3, final Conjecture of Section 4.
https://arxiv.org/abs/1803.05470

The agent order below is B:2/7, C:1/7, H:4/7. Relabeling agents gives the
source's order (1/7,2/7,4/7). This is the specifically identified three-agent
case, not the conjecture for arbitrary numbers of agents and entitlements.
The division model is copied exactly from the approved arXiv:1909.07141 model.
-/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Data.Fin.Tuple.Basic

namespace OMA.S_arxiv_1803_05470_demands_124

open MeasureTheory

/-- A division of [0,1] with at most k cuts; shared endpoints have zero mass
under the hypotheses of main. Each agent may own multiple intervals. -/
def DivisionWithCuts {n : ℕ} (μ : Fin n → Measure ℝ) (α : Fin n → ℝ) (k : ℕ) : Prop :=
  ∃ (c : Fin (k + 2) → ℝ) (owner : Fin (k + 1) → Fin n),
    Monotone c ∧ c 0 = 0 ∧ c (Fin.last (k + 1)) = 1 ∧
      ∀ i : Fin n, ENNReal.ofReal (α i) ≤
        μ i (⋃ j ∈ {j : Fin (k + 1) | owner j = i}, Set.Icc (c j.castSucc) (c j.succ))

/-- The fixed three-agent (1,2,4)/7 case of Segal-Halevi's conjecture. -/
theorem main : ∀ μ : Fin 3 → Measure ℝ,
    (∀ i, IsProbabilityMeasure (μ i)) →
    (∀ i, NullSingletonClass (μ i)) →
    (∀ i, μ i (Set.Icc 0 1) = 1) →
    DivisionWithCuts μ ![(2/7:ℝ),1/7,4/7] 4 := by
  sorry

end OMA.S_arxiv_1803_05470_demands_124
