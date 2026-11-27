import Mathlib

/-!
# Ideal solutions of the Prouhet–Tarry–Escott problem

Source: https://en.wikipedia.org/wiki/Prouhet%E2%80%93Tarry%E2%80%93Escott_problem
Credit: @Ciphore

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wpc_prouhet_tarry_escott

/-- Two disjoint integer multisets of size `n + 1` form an ideal solution of degree `n` when
their sums of `k`th powers agree for every `k = 1, …, n`. -/
def IsIdealSolution (n : ℕ) (A B : Multiset ℤ) : Prop :=
  A.card = n + 1 ∧ B.card = n + 1 ∧ (∀ x, x ∈ A → x ∉ B) ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n → (A.map fun x => x ^ k).sum = (B.map fun x => x ^ k).sum

/-- The ideal Prouhet–Tarry–Escott problem: ideal solutions exist in every degree. -/
theorem main : ∀ n : ℕ, ∃ A B : Multiset ℤ, IsIdealSolution n A B := by
  sorry

end OMA.S_wpc_prouhet_tarry_escott
