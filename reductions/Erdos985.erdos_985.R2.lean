import FormalConjectures.ErdosProblems.«985»
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Real.Sqrt

/-!
The finite range through 2791 is separated from Theorem 1 of
McGown, Treviño and Trudgian, arXiv:1508.05182. That theorem bounds
the least prime primitive root under the Dirichlet GRH.
-/

-- Credit: @dk8827

namespace OMA.R_Erdos985_erdos_985_R2

/-- The finite range, including the prime at the threshold. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ 2791 →
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1

/-- Dirichlet GRH for primitive characters in the open critical strip. -/
def H2 : Prop :=
  ∀ (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re = 1 / 2

/-- The prime primitive root bound of McGown, Treviño and Trudgian. -/
def H3 : Prop :=
  (∀ (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re = 1 / 2) →
    ∀ p : ℕ, p.Prime → 2791 < p →
      ∃ q : ℕ, q.Prime ∧ (q : ℝ) < Real.sqrt (p : ℝ) - 2 ∧
        orderOf (q : ZMod p) = p - 1

theorem main : H1 → H2 → H3 → type_of% @Erdos985.erdos_985 := by
  intro small grh large p hp h₂
  by_cases hp₀ : p ≤ 2791
  · exact small p hp h₂ hp₀
  · obtain ⟨q, hq, hqp, horder⟩ := large grh p hp (lt_of_not_ge hp₀)
    have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hs : Real.sqrt (p : ℝ) ≤ p := Real.sqrt_le_self_iff.2 (Or.inr hp₁)
    exact ⟨q, hq, by exact_mod_cast (show (q : ℝ) < p by linarith), horder⟩

end OMA.R_Erdos985_erdos_985_R2
