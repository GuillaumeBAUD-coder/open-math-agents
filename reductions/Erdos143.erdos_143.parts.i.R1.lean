import FormalConjectures.ErdosProblems.«143»
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Erdos143_erdos_143_parts_i_R1
open Filter Finset Erdos143
open scoped Classical

/-- Koukoulopoulos–Lamzouri–Lichtman's logarithmic sparsity estimate, with
one reciprocal per occupied unit interval. A point x in bin k satisfies
1/(k+1) ≤ 1/x. -/
def H1 : Prop := ∀ A : Set ℝ, WellSeparatedSet A → ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop,
  (∑ k ∈ (range N).filter (fun j ↦ j ∈ (fun x : ℝ ↦ ⌊x⌋₊) '' A), ((k:ℝ)+1)⁻¹) ≤ δ * Real.log N

/-- Partial summation: a unit-separated real set with logarithmically sparse
occupied bins has lower density zero. -/
def H2 : Prop := ∀ A : Set ℝ, A ⊆ Set.Ioi 1 →
  (∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ |x-y|) →
  (∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop,
    (∑ k ∈ (range N).filter (fun j ↦ j ∈ (fun x : ℝ ↦ ⌊x⌋₊) '' A), ((k:ℝ)+1)⁻¹) ≤ δ * Real.log N) →
  liminf (fun x : ℝ ↦ ((A ∩ Set.Icc 1 x).ncard : ℝ) / x) atTop = 0

theorem main : H1 → H2 → type_of% @Erdos143.erdos_143.parts.i := by
  intro sparse partialSum A hA
  apply partialSum A hA.1 _ (sparse A hA)
  intro x hx y hy hxy
  simpa using hA.2.2.2 x hx y hy hxy 1 le_rfl

end OMA.R_Erdos143_erdos_143_parts_i_R1
