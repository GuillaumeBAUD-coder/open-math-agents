import Mathlib

namespace OMA.S_mo_102456

open Polynomial Function

/-- The copy of the closed unit interval on the real axis. -/
def segment : Set ℂ := Complex.ofReal '' Set.Icc (0 : ℝ) 1

def Confined (p : ℂ[X]) : Prop := p.rootSet ℂ ⊆ segment

/-- The constant-coefficient operator with the given derivative coefficients. -/
noncomputable def applyDiff {N : ℕ} (c : Fin (N+1) → ℂ) (p : ℂ[X]) : ℂ[X] :=
  ∑ j, C (c j) * derivative^[j.val] p

/-- A constant-coefficient differential operator preserves the unit-interval
root condition exactly when at most one derivative coefficient is nonzero. -/
theorem main :
    ∀ (N : ℕ) (c : Fin (N+1) → ℂ),
      (∀ p : ℂ[X], Confined p → Confined (applyDiff c p)) ↔
        ∃ i : Fin (N+1), ∀ j : Fin (N+1), j ≠ i → c j = 0 := by
  sorry

end OMA.S_mo_102456
