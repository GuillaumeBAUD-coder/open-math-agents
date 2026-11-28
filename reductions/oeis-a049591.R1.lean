import OMAStatements.S_oeis_a049591

-- Reduction oeis-a049591.R1 of oeis-a049591: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a049591_R1

open OMA.S_oeis_a049591
open Asymptotics Filter

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ s : ℕ, 2 ≤ s → ∀ f : ℕ → ℕ, IsCloitre s f →
      (fun n : ℕ => (f n : ℝ) - (n : ℝ) / 2) =O[atTop] (fun n : ℕ => Real.log n))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ s : ℕ, 2 ≤ s → ∀ f : ℕ → ℕ, IsCloitre s f →
      {p : ℕ | p.Prime ∧ f (2 * p) = p}.Infinite)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ f : ℕ → ℕ, IsCloitre 3 f →
      ∀ p : ℕ, p.Prime → (f (2 * p) = p ↔ p ≠ 2 ∧ ¬ (p + 2).Prime))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a049591.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a049591_R1
