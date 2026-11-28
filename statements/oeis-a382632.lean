import Mathlib.Data.Nat.Basic

/-! The polygon-folding conjecture of OEIS A382632. The rods occur in cyclic
order with lengths 1 through n and fill the perimeter exactly once. The joint
after rod j is at arc coordinate j*(j+1)/2; the closing joint equals joint 0.
Starting with the smallest corner coordinate lets a side cross the closing joint.
Source: https://oeis.org/A382632 -/

namespace OMA.S_oeis_a382632

def joint (j : ℕ) : ℕ := j * (j+1) / 2

def canFold (n sides : ℕ) : Prop :=
  ∃ first step : ℕ, 0 < step ∧ first < step ∧ joint n = sides * step ∧
    ∀ i : ℕ, i < sides → ∃ j : ℕ, j < n ∧ joint j = first + i * step

theorem main : ∀ sides : ℕ, 2 ≤ sides →
    ((∃ n : ℕ, 0 < n ∧ canFold n sides) ↔ sides = 2 ∨ sides = 3) := by
  sorry

end OMA.S_oeis_a382632
